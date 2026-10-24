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
"""

import modal

app = modal.App("mathproof-check")

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


@app.function(
    image=image,
    cpu=2.0,
    memory=32768,
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
    r = subprocess.run(cmd)

    print(f"elapsed: {time.time() - t0:.0f}s")
    if r.returncode != 0:
        raise SystemExit(f"BUILD FAILED for target: {target or 'full project'}")
    print(f"OK: target {target or 'full project'}")


@app.local_entrypoint()
def main(
    target: str = "MathProof.Tau.CongruenceSmall",
    file: str = "",
):
    from pathlib import Path
    files = {}
    if file:
        files[file] = Path(file).read_text()
    else:
        # default: overlay every locally-modified MathProof file
        import subprocess as sp
        out = sp.run(
            ["git", "status", "--porcelain"],
            capture_output=True, text=True, check=True,
        ).stdout
        for line in out.splitlines():
            path = line[3:].strip()
            if path.endswith(".lean"):
                files[path] = Path(path).read_text()
        if not files:
            raise SystemExit("no local MathProof changes found; pass --file")
    check.remote(files=files, target=target)
