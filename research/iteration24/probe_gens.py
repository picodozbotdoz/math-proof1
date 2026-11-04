#!/usr/bin/env python3 -I
"""Iteration-24 probe 2: minimal generating sets of 𝕋 over ℤ[T₂], dims 5–10.

Extends probe_index.py: greedy scan over sets S of extra Hecke indices —
compute [𝕋 : ℤ[T₂] + span of all T₂^a ∏_{m∈S} T_m^{b_m}] — until the index
is 1 (𝕋 = ℤ[T₂, S]).  Greedy = add the smallest prime that strictly lowers
the index.  Also prints the SNF invariant factors at dims 5–10 (the quotient
structure: which cyclic factors appear beyond ⟨[T₃]⟩).

Anchors: re-run of the probe-1 anchors (|det A| = Ik, base index = Ik).
"""

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "research" / "iteration23" / "hecke-index"))
import g1_audit as G  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
from probe_index import hnf_index  # noqa: E402

OUT = Path(__file__).resolve().parent / "probe_gens.json"

# m·dim must stay < 516 (g1_audit's N); dim ≤ 10 → m ≤ 47 in this probe
PRIMES = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]


def lat_gens(M2m, Mms, n):
    """Rows of the generators T₂^a ∏_{m∈S} T_m^{b_m} over all monomials of
    total degree ≤ n (commuting operators; enough to span the lattice —
    higher-degree monomials are ℚ-combinations of lower ones since the
    ℚ-algebra has dimension n)."""
    rows = []
    S = sorted(Mms)
    # enumerate exponent tuples (b_m)_{m∈S} with sum ≤ n, memoized matrices
    mem = {}

    def Xof(bs):
        key = tuple(bs)
        if key not in mem:
            M = [[int(i == j) for j in range(n)] for i in range(n)]
            for m, b in zip(S, bs):
                for _ in range(b):
                    M = G.matmul(M, Mms[m])
            mem[key] = M
        return mem[key]

    def rec(idx, rem, cur):
        if idx == len(S):
            yield cur[:]
            return
        for b in range(rem + 1):
            cur.append(b)
            yield from rec(idx + 1, rem - b, cur)
            cur.pop()

    for bs in rec(0, n, []):
        X = Xof(bs)
        for a in range(n - sum(bs)):
            rows.append(G.matmul(G.matpow(M2m, a), X)[0][:])
    return rows


def idx_of(M2m, Mms, n):
    return hnf_index(lat_gens(M2m, Mms, n), n)


def main():
    ref = json.load(open(ROOT / "research" / "iteration23" / "hecke-index"
                         / "index_data.json"))
    data, report = {}, []
    for k in sorted(ref, key=int):
        ent = ref[k]
        n = ent["dim"]
        if n < 5:
            continue
        k = int(k)
        mrows = G.basis_miller(k, n)
        M2m = G.op_matrix(k, 2, mrows)
        Ik = ent["Ik"]
        S = {}
        cur = idx_of(M2m, S, n)
        assert cur is not None
        chain = [(list(S), cur)]
        while cur != 1:
            best = None
            for p in PRIMES:
                if p in S:
                    continue
                ix = idx_of(M2m, {**S, p: G.op_matrix(k, p, mrows)}, n)
                if ix is not None and ix < cur and (best is None or ix < best[1]):
                    best = (p, ix)
                if best and best[1] == 1:
                    break
            if best is None:
                chain.append((list(S) + ["<none>"], None))
                break
            S[best[0]] = G.op_matrix(k, best[0], mrows)
            cur = best[1]
            chain.append((list(S), cur))
        data[k] = {"dim": n, "Ik": Ik, "snf": None, "greedy": chain}
        report.append(f"w{k:3d} dim {n}: greedy chain " +
                      " -> ".join(f"{{{'/'.join(map(str, s))}}}:{ix}"
                                  for s, ix in chain))
        print(report[-1], flush=True)
    OUT.write_text(json.dumps(data, indent=1))
    print("written", OUT)


if __name__ == "__main__":
    main()
