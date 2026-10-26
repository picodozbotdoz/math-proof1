"""Fast single-target Lean check on Modal.

Architecture (v2 — fixes the slow-volume failure mode):
  * The image BAKES the pinned Lean toolchain, the mathlib dependency tree
    (exact revisions from the repo's committed lake-manifest.json), and the
    full Mathlib olean cache.  All of it lands on the container's local disk,
    which is where small-file I/O is fast.
  * At runtime we shallow-clone the repo, overlay local working-copy files
    (so iterations need no git push), symlink the warm packages into
    .lake/packages, and `lake build` the target directly.
  * No Modal volume in the hot path: writing thousands of tiny .olean files
    to a network volume stalls at ~40 MB / 11 min (measured); local disk does
    the same in seconds.  MathProof's own modules recompile from scratch each
    run (~1 min) — cheap next to any volume-based caching.

Usage:
    /home/doz/dozenv/bin/modal run lean_check.py \\
        [--target MathProof.Tau.CongruenceSmall] [--file MathProof/Tau/CongruenceSmall.lean]

`--file` overlays that one file and (unless `--target` is also given) builds
the module it defines.  Every run prints `[telemetry]` resource milestones and
a final peak-RSS/CPU summary for the `lake` process tree.
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


def _tree_snapshot(root_pid):
    """(total_rss_bytes, total_cpu_seconds, n_procs) over the tree rooted at root_pid."""
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
                rss += int(f.read().split()[1]) * _PAGE
        except Exception:
            pass
        cpu += infos[pid][1]
        n += 1
    return rss, cpu / _CLK_TCK, n


def run_monitored(cmd):
    """`subprocess.run(cmd)` (stdout inherited) plus resource telemetry."""
    t0 = _time.monotonic()
    proc = _subprocess.Popen(cmd)
    samples = []
    last_milestone = 0
    while proc.poll() is None:
        rss, cpu, n = _tree_snapshot(proc.pid)
        samples.append((_time.monotonic() - t0, rss, cpu, n))
        if rss >= last_milestone * 1.10:  # milestone on >=10% growth
            last_milestone = max(last_milestone, rss)
            print(f"[telemetry] t={samples[-1][0]:7.1f}s  rss={rss / 2**30:6.2f} GiB  "
                  f"cpu={cpu:6.0f}s  procs={n}", flush=True)
        _time.sleep(1.0)
    rc = proc.returncode
    wall = _time.monotonic() - t0
    peak = max((s[1] for s in samples), default=0)
    last = samples[-1] if samples else (0, 0, 0, 0)
    try:
        child_peak = _resource.getrusage(_resource.RUSAGE_CHILDREN).ru_maxrss / 2**20
    except Exception:
        child_peak = float("nan")
    print("─" * 66, flush=True)
    print(f"[telemetry] wall={wall:.0f}s  peak_tree_rss={peak / 2**30:.2f} GiB  "
          f"final_cpu={last[2]:.0f}s  samples={len(samples)}  rc={rc}", flush=True)
    print(f"[telemetry] children ru_maxrss={child_peak:.2f} GiB", flush=True)
    if len(samples) > 2:
        step = max(1, len(samples) // 24)
        print("[telemetry] rss curve (decimated, t:GiB): "
              + "  ".join(f"{s[0]:.0f}:{s[1] / 2**30:.2f}" for s in samples[::step]), flush=True)
    print("─" * 66, flush=True)
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
)
def check(files: dict, target: str, repo_url: str = "https://github.com/picodozbotdoz/math-proof1.git"):
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

    os.chdir(repo)
    cmd = ["lake", "build"]
    if target:
        cmd.append(target)
    print(f"$ {' '.join(cmd)}")
    rc = run_monitored(cmd)

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
    for line in out.splitlines():
        path = line[3:].strip()
        if path.endswith(".lean") or path == "lakefile.toml":
            # Deleted files (status D) carry no content to overlay; the fresh
            # clone keeps its stale copy, but it is only elaborated if still
            # imported, which the overlaid tree decides.
            if not Path(path).exists():
                continue
            files[path] = Path(path).read_text()

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
    check.remote(files=files, target=target)
