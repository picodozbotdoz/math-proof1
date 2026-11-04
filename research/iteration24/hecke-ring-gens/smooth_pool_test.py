#!/usr/bin/env python3 -I
"""Ad hoc G1 measurement: unimodular n-subsets of the SMOOTH T_m pool
(m ≤ 3n, prime factors of m in {2,3,5}) at the 22 '{3,5}'-weights, plus the
T₇-coefficient solve.  Rows are pure (a_m(g_j)) — q-lemma data in Lean."""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "research" / "iteration23" / "hecke-index"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import g1_audit as G  # noqa: E402
from g1_ring_gens import search_unimodular, solve_int  # noqa: E402

ref = json.load(open(ROOT / "research/iteration23/hecke-index/index_data.json"))
pgens = json.load(open(ROOT / "research/iteration24/probe_gens.json"))
W35 = sorted(int(k) for k, v in pgens.items()
             if [int(x) for x in v["greedy"][-1][0]] == [3, 5])


def smooth(m):
    for p in (2, 3, 5):
        while m % p == 0:
            m //= p
    return m == 1


out = {}
for k in W35:
    n = ref[str(k)]["dim"]
    mrows = G.basis_miller(k, n)
    pool = [m for m in range(1, 3 * n + 1) if smooth(m)]
    rows = [[mrows[j][m] for j in range(n)] for m in pool]
    labels = [(m,) for m in pool]
    rowT7 = [mrows[j][7] for j in range(n)]
    found, sub, nodes = search_unimodular(rows, labels, n, budget=5_000_000)
    ent = {"pool": pool, "nodes": nodes}
    if found:
        sel = [rows[labels.index(s)] for s in sub]
        c = solve_int(sel, rowT7)
        ent["ms"] = [s[0] for s in sub]
        ent["c"] = c
        ent["c_digits"] = max(len(str(abs(x))) for x in c) if c else -1
        ent["R_digits"] = max(len(str(abs(x))) for r in sel for x in r)
        print(f"w{k} dim {n}: FOUND ms={ent['ms']} c_digits={ent['c_digits']}"
              f" R_digits={ent['R_digits']}", flush=True)
    else:
        print(f"w{k} dim {n}: NOT FOUND ({len(pool)}-pool, nodes={nodes})",
              flush=True)
    out[k] = ent
    Path(__file__).resolve().parent.joinpath("smooth_pool.json").write_text(
        json.dumps(out, indent=1))
print("done")
