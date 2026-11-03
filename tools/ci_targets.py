#!/usr/bin/env python3
"""Select the CI build targets (selective targets, iteration 23 review).

`defaultTargets` in lakefile.toml is the single source of the light target
list.  CI builds it in one of two tiers:

* ``full``  -- every default target (weekly schedule, workflow_dispatch);
* ``push``  -- the default targets minus the *full-only* families: the
  roots listed in ``.github/ci-full-only.txt`` and every default target
  whose import closure reaches one of them (computed here, so a new module
  importing an expensive certificate file is excluded automatically).

The full-only roots are the generated per-weight certificate files whose
cold build dominates CI (an edit to one of their ancestors rebuilds them
all: ~70 min).  They are still built by the full tier, on Modal at every
wave merge, and audited by AxCheckDecide.

Usage:
  tools/ci_targets.py push|full        # print space-separated targets
  tools/ci_targets.py --report         # tiers, exclusions, sanity checks
Exit status 1 when a sanity check fails (a full-only root that is not a
default target, a default target missing from MathProof.lean, or a
default target with no source file).
"""

import functools
import pathlib
import re
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
FULL_ONLY = ROOT / ".github" / "ci-full-only.txt"


def default_targets():
    with open(ROOT / "lakefile.toml", "rb") as f:
        return list(tomllib.load(f)["defaultTargets"])


def full_only_roots():
    roots = []
    for line in FULL_ONLY.read_text().splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            roots.append(line)
    return roots


def source(mod):
    return ROOT / (mod.replace(".", "/") + ".lean")


@functools.lru_cache(maxsize=None)
def imports(mod):
    path = source(mod)
    if not path.exists():
        return ()
    out = []
    for line in path.read_text().splitlines():
        m = re.match(r"\s*import\s+(.*)", line)
        if m:
            out += [t for t in m.group(1).split() if t.startswith("MathProof")]
    return tuple(out)


@functools.lru_cache(maxsize=None)
def closure(mod):
    seen = set()
    for i in imports(mod):
        seen |= {i} | closure(i)
    return frozenset(seen)


def tiers():
    targets = default_targets()
    roots = set(full_only_roots())
    excluded = [t for t in targets if t in roots or closure(t) & roots]
    push = [t for t in targets if t not in excluded]
    return targets, push, excluded


def problems():
    targets = default_targets()
    out = []
    for r in full_only_roots():
        if r not in targets:
            out.append(f"full-only root {r} is not a default target")
    root_imports = closure("MathProof")
    for t in targets:
        if not source(t).exists():
            out.append(f"default target {t} has no source file")
        if t not in root_imports:
            out.append(f"default target {t} is not reachable from MathProof.lean")
    return out


def main(argv):
    if len(argv) != 2 or argv[1] not in ("push", "full", "--report"):
        print(__doc__, file=sys.stderr)
        return 2
    bad = problems()
    for p in bad:
        print(f"[ci_targets] ERROR: {p}", file=sys.stderr)
    targets, push, excluded = tiers()
    if argv[1] == "--report":
        print(f"default targets: {len(targets)}")
        print(f"push tier:       {len(push)}")
        print(f"full-only:       {len(excluded)}")
        for t in excluded:
            print(f"  - {t}")
    else:
        print(" ".join(targets if argv[1] == "full" else push))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
