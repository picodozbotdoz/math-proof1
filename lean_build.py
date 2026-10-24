import modal

app = modal.App("math-proof1-build")

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
    r = subprocess.run(cmd)

    print(f"elapsed: {time.time() - t0:.0f}s")
    if r.returncode != 0:
        raise SystemExit(f"BUILD FAILED for target: {target or 'full project'}")
    print(f"Build completed for target: {target or 'full project'}")


@app.local_entrypoint()
def main(
    repo_url: str = "https://github.com/picodozbotdoz/math-proof1.git",
    target: str = "",
):
    build.remote(repo_url=repo_url, target=target)
