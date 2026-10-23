import modal

app = modal.App("math-proof1-build")

# Persistent volume for Lean toolchain, Mathlib, and .lake artifacts.
# Create once with: modal volume create lean-cache
VOL = modal.Volume.from_name("lean-cache", create_if_missing=True)

image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install(
        "curl", "git", "ca-certificates",
        "build-essential", "xz-utils",
    )
    .run_commands(
        # Install elan into a global location so lean/lake are on PATH.
        "curl -sSfL https://github.com/leanprover/elan/releases/download/v4.35.0/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz -C /tmp",
        "mkdir -p /opt/elan",
        "ELAN_HOME=/opt/elan /tmp/elan-init -y --default-toolchain none",
    )
    .env({
        "ELAN_HOME": "/opt/elan",
        "PATH": "/opt/elan/bin:/usr/local/bin:/usr/bin:/bin",
        # Redirect Mathlib cache into the persistent volume.
        "MATHLIB_CACHE_DIR": "/cache/mathlib",
    })
)


@app.function(
    image=image,
    cpu=4.0,                 # 4 physical cores = 8 vCPU
    memory=32768,            # 32 GiB RAM
    timeout=4 * 60 * 60,     # 4-hour ceiling for the build
    volumes={"/cache": VOL},
)
def build(
    repo_url: str = "https://github.com/picodozbotdoz/math-proof1.git",
    target: str = "MathProof.Tau.Lehmer",  # Set to None for full `lake build`
):

    import os
    import pathlib
    import shutil
    import subprocess

    repo = pathlib.Path("/tmp/repo")
    if not repo.exists():
        subprocess.run(
            ["git", "clone", "--depth", "1", repo_url, str(repo)],
            check=True,
        )

    # ------------------------------------------------------------
    # Ensure the persistent cache directory exists.
    # ------------------------------------------------------------
    cache_lake = pathlib.Path("/cache/lake")
    cache_lake.mkdir(parents=True, exist_ok=True)

    # ------------------------------------------------------------
    # Remove any existing .lake (directory, file, or symlink)
    # so we can replace it with a clean symlink to the cache.
    # ------------------------------------------------------------
    lake_path = repo / ".lake"
    if lake_path.exists() or lake_path.is_symlink():
        if lake_path.is_dir() and not lake_path.is_symlink():
            shutil.rmtree(lake_path)
        else:
            lake_path.unlink()

    # ------------------------------------------------------------
    # Create the symlink.
    # ------------------------------------------------------------
    lake_path.symlink_to(cache_lake)

    os.chdir(repo)
    subprocess.run(["lake", "exe", "cache", "get"], check=True)

    # Run the dense verification pass.
    cmd = ["lake", "build"]
    if target:
        cmd.append(target)
    subprocess.run(cmd, check=True)

    # Persist new artifacts and Mathlib cache to the volume.
    VOL.commit()
    print(f"Build completed for target: {target or 'full project'}")


@app.local_entrypoint()
def main(
    repo_url: str = "https://github.com/picodozbotdoz/math-proof1.git",
    target: str = "MathProof.Tau.Lehmer",
):
    build.remote(repo_url=repo_url, target=target)
