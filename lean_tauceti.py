"""TauCeti port checks on Modal (app `tauceti-check`).

Created on the user's explicit authorization (2026-10-30) as the one exception to
the "no new Modal resources" rule in AGENTS.md: a separate *image* for TauCeti's
pinned toolchain/Mathlib (no volume, no secret, no `modal deploy`; ephemeral
`modal run` only).  It is for TauCeti-related checks only; math-proof1's own
modules still go through lean_check.py / lean_build.py.

The image bakes: elan + the TauCeti-pinned Lean toolchain, a clone of
TauCetiProject/TauCeti at a pinned commit, Mathlib's olean cache, and a build of
the TauCeti modules our ports import.  At run time the staged files (the
`.lean` files of one port branch, see tools/modal_tauceti.sh) are overlaid on
that clone and, per file: `lake build` (full linter set), TauCeti's
`scripts/HeaderStyle.lean`, forbidden-construct greps, and an axiom audit.

Usage (via tools/modal_tauceti.sh, which stages the files):
    modal run lean_tauceti.py --dir /tmp/tauceti-stage/<branch>
"""

import modal
import os

app = modal.App("tauceti-check")

TAUCETI_REV = os.environ.get("TAUCETI_REV", "821b72398ec7f09aa9569e851c8a5482d23983cf")
TOOLCHAIN = "leanprover/lean4:v4.36.0-rc1"

# Modules that our ports import; built into the image so runs only compile the
# overlaid files.
_BAKE = " ".join([
    "TauCeti.NumberTheory.ModularForms.LevelOne.DiscriminantEigenform",
    "TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion",
    "TauCeti.NumberTheory.ModularForms.Newforms.Eigenform",
    "TauCeti.NumberTheory.ModularForms.Order.AtCusp",
    "TauCeti.NumberTheory.ModularForms.TrivialNebentypus",
])

image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install("curl", "git", "ca-certificates", "build-essential", "xz-utils")
    .run_commands(
        "curl -sSfL https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz -C /tmp",
        "mkdir -p /opt/elan",
        "ELAN_HOME=/opt/elan /tmp/elan-init -y --default-toolchain none",
        f"ELAN_HOME=/opt/elan /opt/elan/bin/elan toolchain install {TOOLCHAIN}",
    )
    .run_commands(
        "git init /opt/tauceti",
        "cd /opt/tauceti && git remote add origin https://github.com/TauCetiProject/TauCeti.git",
        f"cd /opt/tauceti && git fetch --depth 1 origin {TAUCETI_REV} && git checkout -q FETCH_HEAD",
        "cd /opt/tauceti && ELAN_HOME=/opt/elan /opt/elan/bin/lake exe cache get",
        f"cd /opt/tauceti && ELAN_HOME=/opt/elan /opt/elan/bin/lake build {_BAKE}",
    )
    .env({"ELAN_HOME": "/opt/elan", "PATH": "/opt/elan/bin:/usr/local/bin:/usr/bin:/bin"})
)

_AXIOMS_TMPL = """import Lean
import {mod}
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `{mod} | throwError "module not found"
  let ok : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut bad : Array Name := #[]
  for c in env.header.moduleData[idx.toNat]!.constNames do
    let axs : Array Name ← collectAxioms c
    for a in axs do
      if !ok.contains a && !bad.contains a then
        bad := bad.push a
  logInfo m!"AXIOMS {mod} non-standard axioms: {{bad}}"
"""


@app.function(image=image, cpu=4.0, memory=16384, timeout=2 * 60 * 60)
def check(files: dict, order: list):
    """files: {relative path: text}; order: relative paths to check, in order."""
    import pathlib
    import re
    import subprocess

    repo = pathlib.Path("/opt/tauceti")
    for rel, content in files.items():
        p = repo / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content)
    print(f"[tauceti] rev {TAUCETI_REV[:10]}; overlaid {len(files)} file(s)", flush=True)

    def sh(cmd):
        r = subprocess.run(cmd, cwd=repo, shell=True, capture_output=True, text=True)
        return r.returncode, (r.stdout + r.stderr)

    results = {}
    for rel in order:
        mod = rel[:-5].replace("/", ".")
        print(f"\n=== {rel}", flush=True)
        src = files[rel]
        res = {}
        rc, out = sh(f"lake build {mod}")
        print(out[-3000:], flush=True)
        res["build"] = rc == 0
        rc, out = sh(f"lake env lean --run scripts/HeaderStyle.lean {rel}")
        print(out.strip(), flush=True)
        res["header"] = rc == 0
        bad = [m for m in re.findall(r"(?m)^\s*(set_option\b|#eval\b|native_decide|sorry\b|admit\b)", src)]
        bad += re.findall(r"(?m)^(?:public )?import (Lean|Lake|Std)\b.*$", src)
        res["forbidden"] = not bad
        print("forbidden constructs:", bad or "none", flush=True)
        n_lines = src.count("\n") + 1
        res["lines<=1000"] = n_lines <= 1000
        long_lines = sum(1 for l in src.split("\n") if len(l) > 100)
        print(f"lines: {n_lines}, lines >100 chars: {long_lines}", flush=True)
        tmp = repo / "AuditTmp.lean"
        tmp.write_text(_AXIOMS_TMPL.format(mod=mod))
        rc, out = sh("lake env lean AuditTmp.lean")
        print(out.strip(), flush=True)
        res["axioms"] = rc == 0 and "non-standard axioms: []" in out
        tmp.unlink()
        results[rel] = res

    print("\n[tauceti] SUMMARY", flush=True)
    allok = True
    for rel, res in results.items():
        ok = all(res.values())
        allok &= ok
        print(f"[tauceti] {'OK  ' if ok else 'FAIL'} {rel} {res}", flush=True)
    print("[tauceti] ALLOK" if allok else "[tauceti] SOMEFAIL", flush=True)
    return allok


@app.local_entrypoint()
def main(dir: str):
    import pathlib

    root = pathlib.Path(dir)
    order = [l.strip() for l in (root / "ORDER").read_text().splitlines() if l.strip()]
    allf = root / "ORDER.all"  # every file up to this branch (imports of the checked ones)
    names = allf.read_text().split() if allf.exists() else order
    files = {rel: (root / rel).read_text() for rel in dict.fromkeys(names + order)}
    ok = check.remote(files, order)
    raise SystemExit(0 if ok else 1)
