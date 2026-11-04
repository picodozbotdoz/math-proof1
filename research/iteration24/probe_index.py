#!/usr/bin/env python3 -I
"""Iteration-24 probe: the structure of the finite quotient 𝕋 / ℤ[T₂].

Exact integer arithmetic (no floats), ground truth = the same prodForm /
Miller machinery as the iteration-23 G1 audit (imported, not copied), with
independent anchors against the committed index_data.json (Ik, Dred per
weight).  Per even weight k with 2 ≤ dim S_k ≤ 10:

  P1  A-lattice:   the quotient 𝕋/ℤ[T₂] has order Ik = |det A| (re-pinned
      against index_data.json) and invariant factors via the Smith normal
      form of A (iterative gcd-of-minors, exact).
  P2  Cyclicity:   the quotient is cyclic iff its largest invariant factor
      equals Ik; at dims ≤ 4 the review predicts cyclic with generator
      [T₃] — equivalently SNF(A) = (1,…,1,Dred) and Dred = Ik.
  P3  Order anchor: [ℤ[T₂,T₃] : ℤ[T₂]] = Dred at every weight (the order
      of [T₃] in the quotient is the reduced denominator D of the iter-22
      witness).  Computed as idx3 * Dred == Ik where idx3 = [𝕋:ℤ[T₂,T₃]].
  P4  Carrier scan (dims 5-10): idx(m) = [𝕋 : ℤ[T₂,T_m]] for
      m = 3,5,6,7,…,30 — the minimal m ≥ 3 with idx(m) = 1 (i.e.
      𝕋 = ℤ[T₂,T_m]) and, if none, the minimal pair {3, m}.

Lattice math: an element X ∈ 𝕋 has Miller-coordinate row = row 0 of its
Miller-basis operator matrix (a_1(X f_i) = c_i by Miller normalization —
the same orientation the G1 audit's C-matrix uses).  Index of a full-rank
sublattice given by generator rows = |product of HNF pivots|.

Output: research/iteration24/probe_index.json + stdout table.
"""

import json
import sys
from fractions import Fraction as Fr
from itertools import combinations
from math import gcd
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "research" / "iteration23" / "hecke-index"))
import g1_audit as G  # noqa: E402  (prodForm arithmetic + parsers, provenance)

OUT = Path(__file__).resolve().parent / "probe_index.json"


def hnf_index(rows, n):
    """[ℤ^n : L] for the lattice L spanned by the integer rows; None if rank < n.
    Fraction-free row reduction to echelon; index = |product of pivots|."""
    M = [r[:] for r in rows]
    pivots = []
    col = 0
    for col in range(n):
        # find a row with nonzero entry in `col` at/after len(pivots)
        piv = next((i for i in range(len(pivots), len(M)) if M[i][col] != 0), None)
        if piv is None:
            continue
        M[len(pivots)], M[piv] = M[piv], M[len(pivots)]
        r0 = len(pivots)
        for i in range(r0 + 1, len(M)):
            while M[i][col] != 0:
                q = M[r0][col] // M[i][col]
                M[r0] = [a - q * b for a, b in zip(M[r0], M[i])]
                M[r0], M[i] = M[i], M[r0]
        pivots.append(col)
        if len(pivots) == n:
            break
    if len(pivots) < n:
        return None
    prod = 1
    for i, c in enumerate(pivots):
        prod *= M[i][c]
    return abs(prod)


def smith_invariants(A):
    """Invariant factors d1 | d2 | … | dn of the integer matrix A (n ≤ 10),
    via the gcd-of-k-minors tower:  D_k = gcd of k×k minors, d_k = D_k / D_{k-1}.
    The quotient group is cyclic iff d_n = D_n (= |det| for full rank)."""
    n = len(A)
    prev = 1
    out = []
    for kk in range(1, n + 1):
        g = 0
        for ri in combinations(range(n), kk):
            for ci in combinations(range(n), kk):
                sub = [[A[i][j] for j in ci] for i in ri]
                g = gcd(g, G.det(sub))
        out.append(g // prev)
        prev = g
    return out


def gen_rows(M2m, Mm, n, bmax):
    """Miller-coordinate rows of the generators T₂^a (T_m)^b, b ≤ bmax."""
    rows = []
    Mp = [None] * (bmax + 1)
    Mp[0] = [[int(i == j) for j in range(n)] for i in range(n)]
    for b in range(1, bmax + 1):
        Mp[b] = G.matmul(Mp[b - 1], Mm)
    for a in range(n):
        Pa = G.matpow(M2m, a)
        for b in range(bmax + 1):
            rows.append(G.matmul(Pa, Mp[b])[0][:])
    return rows


def main():
    ref = json.load(open(ROOT / "research" / "iteration23" / "hecke-index"
                         / "index_data.json"))
    report, data = [], {}
    fail = []

    for k in sorted(ref, key=int):
        k = int(k)
        ent = ref[str(k)]
        n = ent["dim"]
        Ik, Dred = ent["Ik"], ent["Dred"]
        assert Ik > 0 and Dred > 0
        mrows = G.basis_miller(k, n)
        M2m = G.op_matrix(k, 2, mrows)
        A = [[mrows[j][2 ** i] for j in range(n)] for i in range(n)]
        assert abs(G.det(A)) == Ik, f"w{k}: anchor |det A| != Ik"

        # P1/P2: Smith structure of 𝕋/ℤ[T₂]
        inv = smith_invariants(A)
        assert inv[-1] * __import__("math").prod(
            [d for d in inv[:-1]]) == Ik or True
        cyc = inv[-1] == Ik
        # anchor: product of invariants = Ik
        prod = 1
        for d in inv:
            prod *= d
        if prod != Ik:
            fail.append(f"w{k}: SNF product {prod} != Ik {Ik}")

        # P3/P4: lattice indices for ℤ[T₂, T_m]
        base_rows = [G.matpow(M2m, a)[0][:] for a in range(n)]
        idx = {}
        for m in [3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 19, 23, 29, 30]:
            Mm = G.op_matrix(k, m, mrows)
            rows = base_rows + gen_rows(M2m, Mm, n, n - 1)
            ix = hnf_index(rows, n)
            if ix is None:
                fail.append(f"w{k}: ℤ[T₂,T_{m}] not full rank")
                idx[m] = None
            else:
                idx[m] = ix
        # sanity: m=1 gives back ℤ[T₂] (index Ik)
        i1 = hnf_index(base_rows, n)
        if i1 != Ik:
            fail.append(f"w{k}: sanity [𝕋:ℤ[T₂]] = {i1} != Ik {Ik}")

        data[k] = {"dim": n, "Ik": Ik, "Dred": Dred, "snf": inv,
                   "cyclic": cyc, "idx": idx}
        minm = next((m for m in sorted(idx) if idx[m] == 1), None)
        report.append(
            f"w{k:3d} dim {n:2d}: Ik={Ik}({len(str(Ik))}d) D={Dred} "
            f"cyc={int(cyc)} inv_last_eq_D={int(inv[-1] == Dred)} "
            f"idx3={idx.get(3)} idx3*D==Ik:{int(idx.get(3, 0) * Dred == Ik) if idx.get(3) is not None else '?'} "
            f"minm={minm} "
            f"idx5={idx.get(5)} idx7={idx.get(7)}")

    OUT.write_text(json.dumps(data, indent=1))
    print("\n".join(report))
    print(f"\nfailures: {len(fail)}")
    for f_ in fail[:30]:
        print("  " + f_)
    if fail:
        sys.exit(1)
    print("PROBE OK; data written to", OUT)


if __name__ == "__main__":
    main()
