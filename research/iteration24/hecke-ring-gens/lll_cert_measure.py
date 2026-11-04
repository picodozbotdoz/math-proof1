#!/usr/bin/env python3 -I
"""G1 measurement (cont.): LLL-reduced-basis T₇ representations at the 10
dims-7-9 '{3,5}'-weights, + the greedy minimality table (all 36).

At dims 7-9 no unimodular subset of the smooth T_m pool exists (exhaustive,
smooth_pool.json), so the candidate certificate is: reduce the {T₂,T₃,T₅}
box-monomial lattice (det ± 1 at '{3,5}'-weights) by LLL, solve T₇ over the
reduced basis, and report the digit sizes of (a) the T₇ coefficients over
the reduced basis, (b) the reduced-basis rows, (c) the transform
U with B_red = U · (box monomial rows) — the membership certificates.
"""
import json
import sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "research" / "iteration23" / "hecke-index"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import g1_audit as G  # noqa: E402
from g1_ring_gens import lattice_index  # noqa: E402

ref = json.load(open(ROOT / "research/iteration23/hecke-index/index_data.json"))
pgens = json.load(open(ROOT / "research/iteration24/probe_gens.json"))
W35 = sorted(int(k) for k, v in pgens.items()
             if [int(x) for x in v["greedy"][-1][0]] == [3, 5])
WALL = sorted(int(k) for k in pgens)


def lll(basis):
    """LLL (Lovász, δ = 3/4) on the integer row lattice `basis` (full rank).
    Exact arithmetic (Fractions for GS; rows ≤ 10 so GS is recomputed fresh
    each step — simple and safe).  Returns (B_red, U), B_red = U · basis."""
    B = [r[:] for r in basis]
    m = len(B)
    U = [[int(i == j) for j in range(m)] for i in range(m)]

    def gs():
        Bs, mus = [], []
        for i in range(m):
            v = [Fr(x) for x in B[i]]
            mu = [Fr(0)] * m
            for t in range(i):
                nt = sum(x * x for x in Bs[t])
                if nt != 0:
                    mu[t] = sum(Fr(x) * Fr(y) for x, y in zip(B[i], Bs[t])) / nt
                    v = [x - mu[t] * y for x, y in zip(v, Bs[t])]
            Bs.append(v)
            mus.append(mu)
        return Bs, mus

    k = 1
    while k < m:
        Bs, mus = gs()
        # size-reduce B[k] against B[k-1..0]
        for t in range(k - 1, -1, -1):
            q = round(mus[k][t])
            if q:
                B[k] = [x - q * y for x, y in zip(B[k], B[t])]
                U[k] = [x - q * y for x, y in zip(U[k], U[t])]
                Bs, mus = gs()
        lhs = sum(x * x for x in Bs[k])
        rhs = (Fr(3, 4) - mus[k][k - 1] ** 2) * sum(x * x for x in Bs[k - 1])
        if lhs >= rhs:
            k += 1
        else:
            B[k], B[k - 1] = B[k - 1], B[k]
            U[k], U[k - 1] = U[k - 1], U[k]
            k = max(k - 1, 1)
    return B, U


def box_rows(Mpows, gens, n):
    S = sorted(gens)
    rows, labels = [], []
    mem = {}

    def Xof(bs):
        key = tuple(bs)
        if key not in mem:
            M = [[int(i == j) for j in range(n)] for i in range(n)]
            for m, b in zip(S, bs):
                for _ in range(b):
                    M = G.matmul(M, gens[m])
            mem[key] = M
        return mem[key]

    def rec(idx, cur):
        if idx == len(S):
            yield cur[:]
            return
        for b in range(n):
            cur.append(b)
            yield from rec(idx + 1, cur)
            cur.pop()

    for bs in rec(0, []):
        X = Xof(bs)
        for a in range(n):
            rows.append(G.matmul(Mpows[a], X)[0][:])
            labels.append((a, tuple(bs)))
    return rows, labels


def solve_over_basis(Bred, b):
    """Integer c with ∑ c_i Bred[i] = b (Cramer; Bred square invertible)."""
    n = len(Bred)
    d = G.det(Bred)
    assert d != 0
    c = []
    for l in range(n):
        B2 = [r[:] for r in Bred]
        B2[l] = b[:]
        c.append(G.det(B2) // d)
    acc = [sum(c[i] * Bred[i][j] for i in range(n)) for j in range(n)]
    assert acc == b
    return c


def digits(v):
    return max(len(str(abs(x))) for x in v)


out = {}
for k in W35:
    n = ref[str(k)]["dim"]
    if n < 7:
        continue
    mrows = G.basis_miller(k, n)
    M2m = G.op_matrix(k, 2, mrows)
    Mpows = [G.matpow(M2m, a) for a in range(n)]
    gens = {3: G.op_matrix(k, 3, mrows), 5: G.op_matrix(k, 5, mrows)}
    rows, labels = box_rows(Mpows, gens, n)
    assert lattice_index(rows, n) == 1
    # a first echelon basis (n independent rows) then LLL on it
    from g1_ring_gens import transform
    piv, Bech, Uech = transform(rows, n)
    Bred, U2 = lll(Bech)
    # full transform: Bred = U2 · Bech = U2 · Uech · rows
    Ufull = [[sum(U2[i][t] * Uech[t][j] for t in range(n))
              for j in range(len(rows))] for i in range(n)]
    rowT7 = [mrows[j][7] for j in range(n)]
    c = solve_over_basis(Bred, rowT7)
    ent = {
        "dim": n,
        "Bred_digits": max(digits(r) for r in Bred),
        "U_digits": max(digits(r) for r in Ufull),
        "U_nz_per_row": [sum(1 for x in r if x) for r in Ufull],
        "c_digits": digits(c),
        "Bred": Bred, "Ufull": Ufull, "c": c,
        "labels": [list(l) for l in labels],
    }
    out[k] = ent
    print(f"w{k} dim {n}: Bred {ent['Bred_digits']}d U {ent['U_digits']}d "
          f"U_nz {ent['U_nz_per_row']} c {ent['c_digits']}d", flush=True)
    Path(__file__).resolve().parent.joinpath("lll_certs.json").write_text(
        json.dumps(out, indent=1))

# greedy minimality table: [𝕋 : ℤ[T₂, S]] for all S ⊆ {3,5,7}, all 36
print("\nminimality table [𝕋 : ℤ[T₂,S]]:", flush=True)
tab = {}
for k in WALL:
    n = ref[str(k)]["dim"]
    mrows = G.basis_miller(k, n)
    M2m = G.op_matrix(k, 2, mrows)
    Mpows = [G.matpow(M2m, a) for a in range(n)]
    from itertools import combinations as comb
    row = {}
    for r in range(1, 4):
        for S in comb((3, 5, 7), r):
            gens = {m: G.op_matrix(k, m, mrows) for m in S}
            rows, _ = box_rows(Mpows, gens, n)
            row["/".join(map(str, S))] = lattice_index(rows, n)
    tab[k] = {"dim": n, "idx": row}
    print(f"w{k} dim {n}: " + " ".join(f"{S}={v}" for S, v in row.items()),
          flush=True)
Path(__file__).resolve().parent.joinpath("minimality_table.json").write_text(
    json.dumps(tab, indent=1))
print("done")
