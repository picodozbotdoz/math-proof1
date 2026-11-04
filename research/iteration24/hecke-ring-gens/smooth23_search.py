#!/usr/bin/env python3 -I
"""G1 measurement: is there an n-subset of the smooth {2,3} T_m pool
(m = 2^a 3^b ≤ 3n) with |det| = idx3 (i.e. a small-entry basis of the ring
lattice ℤ[T₂,T₃])?  All 36 dims-5-10 weights.  Rows are (a_m(g_j)) —
q-lemma data in Lean; `idx3` cross-checked against the greedy-chain value."""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "research" / "iteration23" / "hecke-index"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import g1_audit as G  # noqa: E402

ref = json.load(open(ROOT / "research/iteration23/hecke-index/index_data.json"))
pgens = json.load(open(ROOT / "research/iteration24/probe_gens.json"))
WALL = sorted(int(k) for k in pgens)


def smooth23(m):
    while m % 2 == 0:
        m //= 2
    while m % 3 == 0:
        m //= 3
    return m == 1


out = {}
for k in WALL:
    n = ref[str(k)]["dim"]
    mrows = G.basis_miller(k, n)
    idx3 = next(ix for s, ix in pgens[str(k)]["greedy"]
                if [int(x) for x in s] == [3])
    pool = [m for m in range(1, 3 * n + 1) if smooth23(m)]
    rows = {m: [mrows[j][m] for j in range(n)] for m in pool}
    # DFS over n-subsets in pool order, rank-tracking; target |det| = idx3
    order = sorted(pool)
    st = {"found": None}
    nodes = [0]
    from math import comb
    if comb(len(order), n) <= 3_000_000:

        def det_of(sel):
            return abs(G.det([rows[m] for m in sel]))

        def dfs(start, sel):
            if st["found"]:
                return
            if len(sel) == n:
                nodes[0] += 1
                if det_of(sel) == idx3:
                    st["found"] = list(sel)
                return
            for pos in range(start, len(order) - (n - len(sel)) + 1):
                nodes[0] += 1
                if nodes[0] > 3_000_000:
                    return
                m = order[pos]
                sel.append(m)
                dfs(pos + 1, sel)
                if st["found"]:
                    return
                sel.pop()
        dfs(0, [])
    found = st["found"]
    ent = {"pool": pool, "found": found, "nodes": nodes[0], "idx3": idx3}
    if found:
        d = det_of(found)
        ent["det"] = d
        ent["digits"] = max(len(str(abs(x))) for m in found for x in rows[m])
        print(f"w{k} dim {n}: idx3={idx3} FOUND ms={found} "
              f"entries {ent['digits']}d", flush=True)
    else:
        print(f"w{k} dim {n}: idx3={idx3} not found (nodes={nodes}, "
              f"pool={len(pool)})", flush=True)
    out[k] = ent
    Path(__file__).resolve().parent.joinpath("smooth23.json").write_text(
        json.dumps(out, indent=1))
print("done")
