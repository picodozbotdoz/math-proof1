import modal

app = modal.App("math-proof1-build")

# ── Build telemetry ─────────────────────────────────────────────────────────
# Watches the `lake` process tree while it runs: milestone lines on every >=10%
# peak-RSS growth (streamed live, so they survive a container OOM kill), plus a
# final summary with peak tree RSS, CPU seconds, and a decimated RSS curve.
# Std-lib only — no image change, no new Modal resources.
# NOTE: keep this block byte-identical with lean_check.py.

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

# Persistent volume kept mounted for ad-hoc `modal shell` use; nothing in the
# build hot path writes to it (thousands of tiny .olean writes to a network
# volume stall at ~40 MB / 11 min — everything heavy lives in the image).
# Create once with: modal volume create lean-cache
VOL = modal.Volume.from_name("lean-cache", create_if_missing=True)

# Same image definition as lean_check.py (layer cache is shared across apps).
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
        # Keep each package's .git: lake validates package revisions through
        # git at build time, and a package without git metadata triggers a
        # full re-fetch.
        "git clone --depth 1 https://github.com/picodozbotdoz/math-proof1.git /opt/warmrepo",
        "cd /opt/warmrepo && ELAN_HOME=/opt/elan /opt/elan/bin/lake update",
        "cd /opt/warmrepo && ELAN_HOME=/opt/elan XDG_CACHE_HOME=/tmp/dl /opt/elan/bin/lake exe cache get",
        "rm -rf /opt/warmrepo/.lake/build",
    )
    .env({
        "ELAN_HOME": "/opt/elan",
        "PATH": "/opt/elan/bin:/usr/local/bin:/usr/bin:/bin",
    })
)


@app.function(
    image=image,
    cpu=2.0,                 # 4 physical cores = 8 vCPU --> reduce to 2 due to idle cpu
    memory=32768,            # 32 GiB RAM: kernel-heavy `decide`s need headroom
    timeout=4 * 60 * 60,     # 4-hour ceiling for the build
    startup_timeout=600,
    volumes={"/cache": VOL},
)
def build(
    repo_url: str = "https://github.com/picodozbotdoz/math-proof1.git",
    target: str = "",  # "" (or None) for the full `lake build`
):

    import os
    import pathlib
    import shutil
    import subprocess
    import time

    t0 = time.time()

    # Always fresh-clone (never reuse a stale /tmp/repo).
    repo = pathlib.Path("/tmp/repo")
    if repo.exists():
        shutil.rmtree(repo)
    subprocess.run(
        ["git", "clone", "--depth", "1", repo_url, str(repo)],
        check=True,
    )

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

    os.chdir(repo)
    cmd = ["lake", "build"]
    if target:
        cmd.append(target)
    print(f"$ {' '.join(cmd)}")
    rc = run_monitored(cmd)

    print(f"elapsed: {time.time() - t0:.0f}s")
    if rc != 0:
        raise SystemExit(f"BUILD FAILED for target: {target or 'full project'}")
    print(f"Build completed for target: {target or 'full project'}")


@app.local_entrypoint()
def main(
    repo_url: str = "https://github.com/picodozbotdoz/math-proof1.git",
    target: str = "",
):
    build.remote(repo_url=repo_url, target=target)
