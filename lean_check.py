"""Fast single-target Lean check on Modal.

Architecture (v2 — fixes the slow-volume failure mode):
  * The image BAKES the pinned Lean toolchain, the mathlib dependency tree
    (exact revisions from the repo's committed lake-manifest.json), and the
    full Mathlib olean cache.  All of it lands on the container's local disk,
    which is where small-file I/O is fast.
  * At runtime we shallow-clone the repo, overlay local working-copy files
    (so iterations need no git push), symlink the warm packages into
    .lake/packages, and `lake build` the target directly.
  * Project-module cache (opt-out: LEAN_CHECK_NO_CACHE=1): every run (even a
    failed one) saves .lake/build as ONE rolling tarball on the existing
    lean-cache volume; later runs restore it onto local disk and lake only
    rebuilds modules whose sources (or overlays) actually changed.  A single
    sequential volume read/write per run — the thousands-of-tiny-writes stall
    never happens.

Usage:
    /home/doz/dozenv/bin/modal run lean_check.py \\
        [--target MathProof.Tau.CongruenceSmall] [--file MathProof/Tau/CongruenceSmall.lean]

`--file` overlays that one file and (unless `--target` is also given) builds
the module it defines.  Every run prints `[telemetry]` resource milestones, a
final peak-RSS/CPU summary for the `lake` process tree and a per-module peak
table (`[memory]`); a run reaching LEAN_CHECK_MEM_ALERT_GIB (default 64) prints
`[memory-alert]` lines that must be investigated.  LEAN_CHECK_PROFILE=<Module>
attributes a module's memory to its individual declarations (`[profile]`).
"""

import modal
import os

app = modal.App("mathproof-check")

# ── Build telemetry ─────────────────────────────────────────────────────────
# Watches the `lake` process tree while it runs: milestone lines on every >=10%
# peak-RSS growth (streamed live, so they survive a container OOM kill), plus a
# final summary with peak tree RSS, CPU seconds, and a decimated RSS curve.
# Std-lib only — no image change, no new Modal resources.

import os as _os
import resource as _resource
import subprocess as _subprocess
import sys as _sys
import threading as _threading
import time as _time

_PAGE = _os.sysconf("SC_PAGE_SIZE")
_CLK_TCK = _os.sysconf("SC_CLK_TCK")


def _stat(pid):
    """(ppid, cpu_ticks) for pid, or None if it vanished."""
    try:
        with open(f"/proc/{pid}/stat", "rb") as f:
            data = f.read().decode()
        fields = data[data.rfind(")") + 2:].split()  # from state (3rd field) on
        return int(fields[1]), int(fields[11]) + int(fields[12])  # ppid, utime+stime
    except Exception:
        return None


def _lean_file(pid):
    """The `.lean` source a `lean` process is elaborating (from its cmdline), or None."""
    try:
        with open(f"/proc/{pid}/cmdline", "rb") as f:
            args = f.read().decode(errors="replace").split("\0")
    except Exception:
        return None
    if not args or not _os.path.basename(args[0]).startswith("lean"):
        return None
    return next((a for a in args[1:] if a.endswith(".lean")), None)


def _tree_snapshot(root_pid, per_file=None):
    """(total_rss_bytes, total_cpu_seconds, n_procs) over the tree rooted at root_pid.
    If `per_file` is a dict, it receives {lean_source: rss_bytes} for every
    `lean` process in the tree (lake runs one per module)."""
    infos = {}
    for name in _os.listdir("/proc"):
        if name.isdigit():
            s = _stat(name)
            if s is not None:
                infos[int(name)] = s
    kids = {}
    for pid, (ppid, _) in infos.items():
        kids.setdefault(ppid, []).append(pid)
    rss = cpu = n = 0
    stack, seen = [root_pid], set()
    while stack:
        pid = stack.pop()
        if pid in seen:
            continue
        seen.add(pid)
        stack.extend(kids.get(pid, ()))
        try:
            with open(f"/proc/{pid}/statm") as f:
                prss = int(f.read().split()[1]) * _PAGE
            rss += prss
            if per_file is not None:
                src = _lean_file(pid)
                if src is not None:
                    per_file[src] = per_file.get(src, 0) + prss
        except Exception:
            pass
        cpu += infos.get(pid, (0, 0))[1]
        n += 1
    return rss, cpu / _CLK_TCK, n


def run_monitored(cmd, interval=1.0, marks=None):
    """`subprocess.run(cmd)` (stdout inherited) plus resource telemetry.

    Also tracks the peak RSS of every `lean` process by source file (one per
    module) and prints a per-module table.  Returns (rc, samples, module_peaks)
    with samples = [(monotonic_s, rss_bytes)].  If `marks` is a list, stdout
    is streamed through and every `@@MARK <id> <monoMs>` line (emitted by an
    instrumented source, see `_instrument`; `#eval` routes its IO to the
    message log, i.e. stdout) is appended to it as (id, seconds).
    """
    t0 = _time.monotonic()
    proc = _subprocess.Popen(cmd, stdout=_subprocess.PIPE if marks is not None else None)
    if marks is not None:
        def pump():
            for raw in proc.stdout:
                line = raw.decode(errors="replace")
                if line.startswith("@@MARK "):
                    _, mid, ms = line.split()
                    marks.append((int(mid), int(ms) / 1000.0))
                else:
                    _sys.stdout.write(line)
        _threading.Thread(target=pump, daemon=True).start()
    samples = []
    module_peaks = {}
    last_milestone = 0
    while proc.poll() is None:
        per_file = {}
        rss, cpu, n = _tree_snapshot(proc.pid, per_file)
        now = _time.monotonic()
        samples.append((now, rss))
        for src, r in per_file.items():
            if r > module_peaks.get(src, (0, 0))[0]:
                module_peaks[src] = (r, now - t0)
        if rss >= last_milestone * 1.10:  # milestone on >=10% growth
            last_milestone = max(last_milestone, rss)
            top = max(per_file.items(), key=lambda kv: kv[1], default=None)
            where = f"  top={top[0]}" if top else ""
            print(f"[telemetry] t={now - t0:7.1f}s  rss={rss / 2**30:6.2f} GiB  "
                  f"cpu={cpu:6.0f}s  procs={n}{where}", flush=True)
        _time.sleep(interval)
    rc = proc.returncode
    wall = _time.monotonic() - t0
    peak = max((s[1] for s in samples), default=0)
    try:
        child_peak = _resource.getrusage(_resource.RUSAGE_CHILDREN).ru_maxrss / 2**20
    except Exception:
        child_peak = float("nan")
    print("─" * 66, flush=True)
    print(f"[telemetry] wall={wall:.0f}s  peak_tree_rss={peak / 2**30:.2f} GiB  "
          f"samples={len(samples)}  rc={rc}", flush=True)
    print(f"[telemetry] children ru_maxrss={child_peak:.2f} GiB", flush=True)
    if len(samples) > 2:
        step = max(1, len(samples) // 24)
        print("[telemetry] rss curve (decimated, t:GiB): "
              + "  ".join(f"{s[0] - t0:.0f}:{s[1] / 2**30:.2f}" for s in samples[::step]),
              flush=True)
    if module_peaks:
        print("[memory] per-module peak RSS (GiB, t of peak):", flush=True)
        for src, (r, t) in sorted(module_peaks.items(), key=lambda kv: -kv[1][0])[:15]:
            print(f"[memory]   {r / 2**30:7.2f}  t={t:7.0f}s  {src}", flush=True)
    _memory_alert(peak, module_peaks)
    print("─" * 66, flush=True)
    return rc, samples, module_peaks


# Investigation policy (AGENTS.md "Memory alerts"): any build whose lake tree
# reaches this RSS must be investigated.  The alert names the modules and the
# command that attributes the memory to individual declarations.
_MEM_ALERT_GIB = float(os.environ.get("LEAN_CHECK_MEM_ALERT_GIB", "64"))


def _memory_alert(peak, module_peaks):
    if peak < _MEM_ALERT_GIB * 2**30:
        return
    hot = [(src, r) for src, (r, _) in module_peaks.items() if r >= _MEM_ALERT_GIB * 2**30 / 2]
    hot.sort(key=lambda kv: -kv[1])
    print(f"[memory-alert] peak tree RSS {peak / 2**30:.1f} GiB >= {_MEM_ALERT_GIB:.0f} GiB "
          "— investigation required (AGENTS.md, Memory alerts)", flush=True)
    for src, r in hot:
        mod = src.removesuffix(".lean").replace("/", ".")
        print(f"[memory-alert]   {mod}: {r / 2**30:.1f} GiB  →  per-declaration profile: "
              f"LEAN_CHECK_PROFILE={mod} tools/modal_run.sh", flush=True)


# ── Per-declaration memory profile ──────────────────────────────────────────
# LEAN_CHECK_PROFILE=<Module>: build only the module's imports with lake (and
# cache them), then elaborate an instrumented copy of the module directly with
# `lean` (synchronous elaboration, `Elab.async=false`): before every top-level
# command a `#eval` prints `@@MARK <id> <monotonic ms>` (on stdout).  RSS
# samples taken by the monitor (same CLOCK_MONOTONIC) are bucketed between
# consecutive marks, giving peak / growth per declaration.  The instrumented
# copy lives in /tmp, so the project's build tree and cache are untouched.

_CMD_START = ("theorem", "lemma", "def", "abbrev", "instance", "example", "structure",
              "class", "inductive", "noncomputable", "private", "protected", "@[", "/--",
              "set_option", "attribute", "open", "namespace", "section", "end", "variable",
              "#", "local", "scoped", "macro", "syntax", "elab", "partial", "unsafe",
              "irreducible_def", "alias", "notation", "infix", "universe", "omit", "include")


def _instrument(src: str):
    """Insert a mark before each top-level command that follows a blank line.
    Returns (instrumented_text, {mark_id: (line_no, description)})."""
    lines = src.split("\n")
    out, labels, depth, prev_blank, past_imports = [], {}, 0, True, False
    for i, line in enumerate(lines, 1):
        s = line.lstrip()
        top = line == s and s != ""
        if top and not s.startswith("import"):
            past_imports = True
        if (past_imports and depth == 0 and prev_blank and top
                and s.startswith(_CMD_START)):
            mid = len(labels)
            # describe the command by its first declaration-looking line
            desc = s
            for nxt in lines[i - 1:i + 25]:
                t = nxt.strip()
                if t.split(" ", 1)[0] in ("theorem", "lemma", "def", "abbrev", "instance",
                                          "example", "noncomputable", "private",
                                          "protected", "structure", "inductive", "class"):
                    desc = t
                    break
            labels[mid] = (i, desc[:110])
            out.append(f'#eval (do IO.eprintln s!"@@MARK {mid} {{← IO.monoMsNow}}" : IO Unit)')
        out.append(line)
        depth += line.count("/-") - line.count("-/")
        depth = max(depth, 0)
        prev_blank = s == ""
    end = len(labels)
    labels[end] = (len(lines), "<end of file>")
    out.append(f'#eval (do IO.eprintln s!"@@MARK {end} {{← IO.monoMsNow}}" : IO Unit)')
    return "\n".join(out) + "\n", labels


def _lean_options(lakefile):
    """`-Dkey=value` flags for the lakefile's [leanOptions] (lake applies them;
    a bare `lean` invocation would not)."""
    import tomllib
    try:
        with open(lakefile, "rb") as f:
            opts = tomllib.load(f).get("leanOptions", {})
    except Exception:
        return []
    flags = []

    def walk(prefix, d):  # TOML dotted keys arrive as nested tables
        for k, v in d.items():
            key = f"{prefix}{k}"
            if isinstance(v, dict):
                walk(key + ".", v)
            else:
                v = str(v).lower() if isinstance(v, bool) else str(v)
                flags.append(f"-D{key}={v}")
    walk("", opts)
    return flags


def profile_module(module: str, repo):
    import pathlib
    path = repo / (module.replace(".", "/") + ".lean")
    src = path.read_text()
    imports = [l.split()[1] for l in src.split("\n") if l.startswith("import ")]
    print(f"[profile] building imports of {module}: {imports}", flush=True)
    rc, _, _ = run_monitored(["lake", "build", *imports])
    if rc != 0:
        return rc
    text, labels = _instrument(src)
    prof = pathlib.Path("/tmp/profile") / path.name
    prof.parent.mkdir(parents=True, exist_ok=True)
    prof.write_text(text)
    marks = []
    cmd = ["lake", "env", "lean", "-DElab.async=false", *_lean_options(repo / "lakefile.toml"),
           str(prof)]
    print(f"[profile] $ {' '.join(cmd)}", flush=True)
    rc, samples, _ = run_monitored(cmd, interval=0.25, marks=marks)
    marks.sort(key=lambda m: m[1])
    rows = []
    for (mid, t_a), (_, t_b) in zip(marks, marks[1:]):
        window = [r for (t, r) in samples if t_a <= t <= t_b]
        before = [r for (t, r) in samples if t <= t_a]
        start = before[-1] if before else (window[0] if window else 0)
        peak = max(window, default=start)
        line, desc = labels.get(mid, (0, "?"))
        rows.append((peak, peak - start, t_b - t_a, line, desc))
    print("[profile] top commands by RSS growth (GiB peak, GiB growth, s, line, command):",
          flush=True)
    for peak, grow, dur, line, desc in sorted(rows, key=lambda r: -r[1])[:15]:
        print(f"[profile] {peak / 2**30:7.2f} {grow / 2**30:+7.2f} {dur:8.1f}s  "
              f"L{line:<6} {desc}", flush=True)
    print("[profile] top commands by duration:", flush=True)
    for peak, grow, dur, line, desc in sorted(rows, key=lambda r: -r[2])[:10]:
        print(f"[profile] {peak / 2**30:7.2f} {grow / 2**30:+7.2f} {dur:8.1f}s  "
              f"L{line:<6} {desc}", flush=True)
    if len(marks) < len(labels):
        print(f"[profile] note: {len(marks)}/{len(labels)} marks seen "
              "(elaboration stopped early or a mark sat inside a multi-line command)",
              flush=True)
    return rc

# ────────────────────────────────────────────────────────────────────────────

# Same image definition as lean_build.py (layer cache is shared across apps).
image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install(
        "curl", "git", "ca-certificates",
        "build-essential", "xz-utils",
    )
    .run_commands(
        "curl -sSfL https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz -C /tmp",
        "mkdir -p /opt/elan",
        "ELAN_HOME=/opt/elan /tmp/elan-init -y --default-toolchain none",
        # Bake the pinned toolchain: without this every cold container
        # re-downloads ~400 MB from releases.lean-lang.org (very slow).
        "ELAN_HOME=/opt/elan /opt/elan/bin/elan toolchain install leanprover/lean4:v4.36.0-rc1",
    )
    .run_commands(
        # Warm dependency tree: clone the repo itself (small) and materialize
        # .lake/packages at exactly the committed manifest's revisions, then
        # fetch the Mathlib olean cache INTO THE IMAGE (local disk at build
        # time; downloads go to /tmp so they don't double the image size).
        "git clone --depth 1 https://github.com/picodozbotdoz/math-proof1.git /opt/warmrepo",
        "cd /opt/warmrepo && ELAN_HOME=/opt/elan /opt/elan/bin/lake update",
        "cd /opt/warmrepo && ELAN_HOME=/opt/elan XDG_CACHE_HOME=/tmp/dl /opt/elan/bin/lake exe cache get",
        # Drop MathProof's own build dir from the image (it belongs to the
        # evolving repo), but KEEP .lake/packages with each package's .git:
        # lake validates package revisions through git at build time, and a
        # package without git metadata triggers a full re-fetch.
        "rm -rf /opt/warmrepo/.lake/build",
    )
    .env({
        "ELAN_HOME": "/opt/elan",
        "PATH": "/opt/elan/bin:/usr/local/bin:/usr/bin:/bin",
    })
)


# Memory request (MiB) is overridable per run via env var, e.g. big kernel
# decides need more than the 32 GiB default:
#   LEAN_CHECK_MEMORY_MIB=98304 modal run lean_check.py --file ...
# (Modal's memory= is a soft request; see research/lehmer-mod-scaling-study.md.)
_CHECK_MEMORY_MIB = int(os.environ.get("LEAN_CHECK_MEMORY_MIB", "32768"))


@app.function(
    image=image,
    cpu=2.0,
    memory=_CHECK_MEMORY_MIB,
    timeout=2 * 60 * 60,
    volumes={"/cache": modal.Volume.from_name("lean-cache")},
)
def check(files: dict, target: str, profile: str = "",
          repo_url: str = "https://github.com/picodozbotdoz/math-proof1.git"):
    import os
    import pathlib
    import shutil
    import subprocess
    import time

    t0 = time.time()

    repo = pathlib.Path("/tmp/repo")
    if repo.exists():
        shutil.rmtree(repo)
    subprocess.run(
        ["git", "clone", "--depth", "1", repo_url, str(repo)],
        check=True,
    )

    for rel, content in files.items():
        p = repo / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content)
        print(f"overlay: {rel} ({len(content)} bytes)")

    # Warm-start: symlink the baked dependency tree into this clone.  The
    # container's overlay filesystem makes writes through these symlinks
    # private to this container, so the pristine image stays intact.
    warm = pathlib.Path("/opt/warmrepo/.lake/packages")
    pkgs = repo / ".lake" / "packages"
    pkgs.mkdir(parents=True, exist_ok=True)
    for d in warm.iterdir():
        if d.is_dir():
            link = pkgs / d.name
            if link.exists() or link.is_symlink():
                link.unlink()
            link.symlink_to(d)
    print(f"warm packages: {sorted(d.name for d in warm.iterdir() if d.is_dir())}")

    # Project-module cache: ONE rolling tarball of .lake/build on the existing
    # lean-cache volume.  Lake re-validates every restored module against its
    # hash trace (source + imports), so a restore is always safe: modules
    # whose sources (or overlays) changed rebuild, everything else is
    # skipped.  A single sequential volume read/write per run — the
    # thousands-of-tiny-writes stall never happens.
    cache_dir = pathlib.Path("/cache/buildcache")
    latest = cache_dir / "latest.tar.gz"
    use_cache = os.environ.get("LEAN_CHECK_NO_CACHE", "") != "1"
    if use_cache:
        try:
            if latest.exists():
                t1 = time.time()
                r = subprocess.run(["tar", "xzf", str(latest), "-C", str(repo)])
                print(f"[cache] restored {latest.name} ({latest.stat().st_size // 2**20} MiB) "
                      f"in {time.time() - t1:.0f}s rc={r.returncode}")
            else:
                print("[cache] empty")
        except Exception as e:
            print(f"[cache] restore failed (non-fatal): {e}")

    os.chdir(repo)
    if profile:
        rc = profile_module(profile, repo)
    else:
        cmd = ["lake", "build"]
        if target:
            cmd.append(target)
        print(f"$ {' '.join(cmd)}")
        rc, _, _ = run_monitored(cmd)

    # Save the build tree even when the build FAILED: lake only writes a
    # module's trace after it elaborates successfully, so every artifact in
    # the tree is valid, and an hour-long heavy module that built before a
    # later failure must not be paid for again.  Written under a temp name
    # and renamed, so a concurrent run never restores a partial tarball (last
    # writer wins; a run that loses only rebuilds what it is missing).
    if use_cache:
        try:
            cache_dir.mkdir(parents=True, exist_ok=True)
            tmp = cache_dir / f".latest.{os.getpid()}.{int(time.time())}.tmp"
            t1 = time.time()
            subprocess.run(
                ["tar", "-I", "gzip -1", "-cf", str(tmp), "-C", str(repo), ".lake/build"],
                check=True)
            os.replace(tmp, latest)
            for old in cache_dir.glob("*.tar.gz"):  # per-HEAD tarballs (v1 scheme)
                if old != latest:
                    old.unlink()
            modal.Volume.from_name("lean-cache").commit()
            print(f"[cache] saved {latest.name} ({latest.stat().st_size // 2**20} MiB) "
                  f"in {time.time() - t1:.0f}s")
        except Exception as e:
            print(f"[cache] save failed (non-fatal): {e}")

    print(f"elapsed: {time.time() - t0:.0f}s")
    if rc != 0:
        raise SystemExit(f"BUILD FAILED for target: {target or 'full project'}")
    print(f"OK: target {target or 'full project'}")


@app.local_entrypoint()
def main(
    target: str = "",
    file: str = "",
):
    from pathlib import Path
    import subprocess as sp

    # Overlay every locally-modified / untracked file that affects the build:
    # any .lean file in the repo, plus lakefile.toml (so config changes are
    # testable without pushing).  lean_build.py covers the pushed state.
    files = {}
    out = sp.run(
        ["git", "status", "--porcelain", "--untracked-files=all"],
        capture_output=True, text=True, check=True,
    ).stdout
    paths = [line[3:].strip() for line in out.splitlines()]
    # Also overlay files committed locally but not yet pushed: the remote
    # side clones origin's default branch, so local commits are otherwise
    # invisible to it.
    diff = sp.run(
        ["git", "diff", "--name-only", "origin/master"],
        capture_output=True, text=True,
    )
    if diff.returncode == 0:
        paths += [p.strip() for p in diff.stdout.splitlines() if p.strip()]
    for path in dict.fromkeys(paths):
        if path.endswith(".lean") or path == "lakefile.toml":
            # Deleted files (status D) carry no content to overlay; the fresh
            # clone keeps its stale copy, but it is only elaborated if still
            # imported, which the overlaid tree decides.
            if not Path(path).exists():
                continue
            files[path] = Path(path).read_text()

    # Per-declaration memory profile of one module (see profile_module).
    profile = os.environ.get("LEAN_CHECK_PROFILE", "")
    if profile:
        target = target or profile

    if file:
        files[file] = Path(file).read_text()
        if not target:
            # --file implies building that module (MathProof/Tau/Foo.lean ->
            # MathProof.Tau.Foo; Bench/Packed/Bar.lean -> Bench.Packed.Bar).
            target = file.removesuffix(".lean").replace("/", ".")

    if not target:
        if not files:
            raise SystemExit("no local changes found; pass --file or --target")
        target = "MathProof.Tau.CongruenceSmall"
    check.remote(files=files, target=target, profile=profile)
