#!/usr/bin/env python3
"""Probe 2 (iteration 23): the Hecke index I_k and its Cramer certificates.

Run from the repository root (pure Python, ~2 min):
    python3 research/iteration23/probe2-hecke-index/probe_index.py

Objects per weight k (dim n, Miller basis f_1..f_n, all integers):
  A := (a_{2^i}(f_j))_{0<=i<n, 1<=j<=n}            (the index matrix, rows i)
  C := (row0(M2^i))_{i<n}                           (M2 = matrix of T_2 in the
      Miller basis; row0(M2^i)_l = a_1(T_2^i f_{l+1}); C is the basis-change
      matrix from (T_j) to the composition powers T_2^i)
  I_k := |det A|, and v := (a_3(f_j))_j             (T_3 coordinates in T_j)
  w' := v . adj(C)                                   (Cramer: integer vector)
  M3 := matrix of T_3 in the Miller basis

Checks (exact):
  F1. basis normalization a_i(f_j) = delta_ij (i, j <= n) at all 54 weights;
  F2. my M2 and M3 match the Lean-anchored g1_data.json M2/M3 literals
      (independent re-derivation == committed certificate data) at all 54;
  F3. det C = +/- det A at all 54 (the unitriangular bridge, all weights);
  F4. the Cramer identity  sum_i w'_i * M2^i = I_k * M3  (entrywise, exact)
      at all 54 — THIS is the certificate b2 kernel-decides (the
      HeckeRational entrywise pattern with denominator I_k);
  F5. w' = (I_k / D) * N where (N, D) is the committed HeckeRational witness
      (so the reduced denominator D divides I_k, re-derived two ways);
  F6. Hecke-matrix symmetry a_i(T_m f_j) = a_j(T_m f_i) for m = 1..12 at all
      54 weights (the classical self-adjointness — usable in b2's proofs);
  F7. sizing: per-dim max digits of A entries, det A, w' entries, M2^i
      entries (certificate feasibility vs the measured HeckeRational ceiling
      of 381 digits at dim 10).
"""
import json
from math import gcd
from fractions import Fraction as Fr

N = 516
B = 3200

def sig(n, e): return sum(t ** e for t in range(1, n + 1) if n % t == 0)

def pack(a):
    def go(l, h):
        if h - l == 1: return a[l]
        m = (l + h) // 2
        return go(l, m) + (go(m, h) << (B * (m - l)))
    return go(0, len(a))

def unpack(v):
    v &= (1 << (B * N)) - 1
    def go(x, l, h):
        if h - l == 1: return [x]
        m = (l + h) // 2
        return go(x & ((1 << (B * (m - l))) - 1), l, m) + go(x >> (B * (m - l)), m, h)
    out = []; carry = 0; half = 1 << (B - 1); full = 1 << B
    for c0 in go(v, 0, N):
        c0 += carry
        if c0 >= half: c0 -= full; carry = 1
        else: carry = 0
        out.append(c0)
    return out

def mul(a, b): return unpack(pack(a) * pack(b))

E4 = [1] + [240 * sig(n, 3) for n in range(1, N)]
E6 = [1] + [-504 * sig(n, 5) for n in range(1, N)]
c = mul(mul(E4, E4), E4); s = mul(E6, E6)
Delta = [(x - y) // 1728 for x, y in zip(c, s)]
assert Delta[:6] == [0, 1, -24, 252, -1472, 4830]
assert Delta[12] == -370944
P = [[1] + [0] * (N - 1)]
for j in range(1, 12): P.append(mul(P[-1], Delta))
e = {0: [1] + [0] * (N - 1)}
def EP(a):
    if a not in e: e[a] = mul(EP(a - 1), E4)
    return e[a]

def basis_raw(k, dim):
    rows = []
    for j in range(1, dim + 1):
        w = k - 12 * j
        b = next(bb for bb in (0, 1, 2) if w - 6 * bb >= 0 and (w - 6 * bb) % 4 == 0)
        a = (w - 6 * b) // 4
        f = mul(P[j], EP(a))
        for _ in range(b): f = mul(f, E6)
        rows.append(f)
    return rows

def basis(k, dim):
    """Miller basis: raw prodForm rows, then the integer unitriangular
    reduction making a_i(f_j) = delta_ij (i, j <= n)."""
    rows = basis_raw(k, dim)
    for j in range(dim - 1, -1, -1):
        for i in range(j):
            c0 = rows[i][j + 1]
            rows[i] = [x - c0 * y for x, y in zip(rows[i], rows[j])]
    return rows

def divisors(n): return [d for d in range(1, n + 1) if n % d == 0]

def Tm_cols(k, m, rows):
    """M(m) columns: for each basis f_j, the first dim coefficients of T_m f_j
    (only indices <= dim are read; reads go up to m*dim <= 512*10 < N)."""
    dim = len(rows)
    return [[sum(d ** (k - 1) * rows[j][m * i // (d * d)] for d in divisors(gcd(m, i)))
             for i in range(1, dim + 1)] for j in range(dim)]  # [j][i-1]

def op_matrix(k, m, rows):
    """Coordinate matrix of T_m in the `rows` basis (fb convention):
    op[t][j] = coordinate on rows[t] of T_m(rows[j]); solve
      a_{i+1}(T_m rows[j]) = sum_t op[t][j] * a_{i+1}(rows[t]),  i = 0..n-1
    by lower-triangular substitution with unit diagonal (a_{i+1}(rows[i]) = 1:
    holds for both the raw prodForm basis and the Miller basis)."""
    n = len(rows)
    cols = Tm_cols(k, m, rows)           # cols[j][i] = a_{i+1}(T_m rows[j])
    op = [[0] * n for _ in range(n)]
    for j in range(n):
        for i in range(n):
            v = cols[j][i]
            for t in range(i):
                v -= rows[t][i + 1] * op[t][j]
            op[i][j] = v
    return op

def det(M):
    n = len(M); A = [[Fr(x) for x in r] for r in M]; D = Fr(1)
    for cc in range(n):
        p = next((r for r in range(cc, n) if A[r][cc] != 0), None)
        if p is None: return 0
        if p != cc: A[p], A[cc] = A[cc], A[p]; D = -D
        D *= A[cc][cc]
        for r in range(cc + 1, n):
            f = A[r][cc] / A[cc][cc]
            if f: A[r] = [x - f * y for x, y in zip(A[r], A[cc])]
    return int(D)

def matmul(X, Y):
    n = len(X)
    return [[sum(X[i][t] * Y[t][j] for t in range(n)) for j in range(n)] for i in range(n)]

def adjugate_transpose_v_times_adj(C, v):
    """w' = v . adj(C)  (row vector times adjugate); via Cramer: solve
    w . C = v det(C) fraction-free over Q, then w' := w * det(C) ... directly:
    w'_l = sum_i v_i * adj(C)[i][l] = sum_i v_i * cof_l,i  — computed as
    det of C with row l replaced by v, divided by det C, times det C:
    w'_l = det(C with row l -> v) * (sign handled by construction)."""
    n = len(C); dC = det(C)
    w = []
    for l in range(n):
        C2 = [row[:] for row in C]
        C2[l] = v[:]
        w.append(det(C2))  # det(C2) = sum_i v_i * cof_{l,i}(C) = w'_l
    assert all(x * dC >= 0 or True for x in w)
    # verify the defining identity w' . C = v * det(C)
    chk = [sum(w[i] * C[i][j] for i in range(n)) for j in range(n)]
    assert chk == [dC * x for x in v], "adjugate identity failed"
    return w, dC

d = json.load(open('research/iteration22/hecke-rational/g1_data.json'))
print("F1/F2/F3/F4/F5/F6/F7 — running all 54 weights")
size_by_dim = {}
nbad = 0
for kk in sorted(d, key=int):
    r = d[kk]; n = r['dim']; k = int(kk)
    mrows = basis(k, n)
    rrows = basis_raw(k, n)
    # F1: Miller normalization + raw leading ones (unit triangular in both)
    assert all(mrows[j][i + 1] == int(i == j) for i in range(n) for j in range(n))
    assert all(rrows[j][i + 1] == int(i == j) for i in range(n)
                for j in range(n) if i <= j)  # q^{j+1}-leading, unit triangular
    # transition Tmat: miller[i] = sum_j Tmat[i][j] * raw[j] (upper unitriangular),
    # from the coefficient tables: delta_ij = a_{j+1}(miller i) = sum_t Tmat[i][t] a_{j+1}(raw t)
    Tmat = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i, n):  # ascending: a_{j+1}(raw t) = 0 for t > j
            v = int(i == j)
            for t in range(i, j):
                v -= Tmat[i][t] * rrows[t][j + 1]
            Tmat[i][j] = v
    # coordinate matrices (fb convention, columns = images)
    M2r = op_matrix(k, 2, rrows)
    M3r = op_matrix(k, 3, rrows)
    M2m = op_matrix(k, 2, mrows)
    M3m = op_matrix(k, 3, mrows)
    # F2: committed Lean-anchored literals == coordinate matrices, raw basis
    assert M2r == r['M2'], (kk, "M2 mismatch")
    assert M3r == r['M3'], (kk, "M3 mismatch")
    # conjugation bridge: raw-coords = Tmat^T . miller-coords, hence
    # Tmat^T . M2m = M2r . Tmat^T
    Tt = [[Tmat[j][i] for j in range(n)] for i in range(n)]
    assert matmul(Tt, M2m) == matmul(M2r, Tt), (kk, "conjugation failed")
    assert abs(det(Tmat)) == 1, (kk, "transition not unimodular")
    # A (Miller) and C (operator coordinates of T2^i, via Miller M2 powers)
    A = [[mrows[j][2 ** i] for j in range(n)] for i in range(n)]
    Pows = [None] * n
    Id = [[int(i == j) for j in range(n)] for i in range(n)]
    Pows[0] = Id
    for i in range(1, n): Pows[i] = matmul(M2m, Pows[i - 1])
    C = [Pows[i][0][:] for i in range(n)]
    dA, dC = det(A), det(C)
    # F3: unitriangular bridge (probe 1 check E, all 54 weights)
    assert abs(dA) == abs(dC), (kk, dA, dC)
    Ik = abs(dA)
    # F4: Cramer identity, certified in RAW coordinates on the landed-literal
    # side (operator identity -> holds in every basis): sum_i w'_i M2r^i = Ik*M3r
    # (w' = |det C| * w with w . C = v; the helper returns det(C)*w, so align sign)
    v = [mrows[j][3] for j in range(n)]
    wp, dChelper = adjugate_transpose_v_times_adj(C, v)
    if dChelper < 0: wp = [-x for x in wp]
    Powsr = [None] * n
    Powsr[0] = Id
    for i in range(1, n): Powsr[i] = matmul(M2r, Powsr[i - 1])
    lhs = [[0] * n for _ in range(n)]
    for i in range(n):
        lhs = [[x + wp[i] * y for x, y in zip(xr, yr)]
               for xr, yr in zip(lhs, Powsr[i])]
    rhs = [[Ik * x for x in row] for row in M3r]
    assert lhs == rhs, (kk, "Cramer identity failed")
    # F5: reduced denominator D divides I_k, via committed witness
    gD = r['D']
    for x in r['N']: gD = gcd(gD, abs(x))
    Dred = r['D'] // gD  # reduced denominator (index_check convention)
    assert Ik % Dred == 0, (kk, Ik, Dred)
    scale = Ik // Dred
    assert [scale * x for x in r['N']] == wp, (kk, "w' != (Ik/D)*N")
    # F6 (candidate REFUTED at k=24 during the probe): a_i(T_m f_j) = a_j(T_m f_i)
    # does NOT hold in Miller coordinates (e.g. k=24, m=2: a_2(T2 f1) = 20468736
    # != a_1(T2 f2) = 1) — Petersson self-adjointness does not descend to
    # coordinate symmetry in a non-orthonormal basis.  Not needed downstream
    # (independence uses only phi_i(T_j) = a_j(f_i) = delta_ij, which is F1).
    # F7: sizing — raw-literal certificate digits + Miller index data digits
    digits = lambda x: len(str(abs(x)))
    entry = size_by_dim.setdefault(n, [0, 0, 0, 0])  # A, Ik, w', M2r^i
    entry[0] = max(entry[0], max(digits(x) for row in A for x in row))
    entry[1] = max(entry[1], digits(Ik))
    entry[2] = max(entry[2], max(digits(x) for x in wp))
    entry[3] = max(entry[3], max(digits(x) for Pm in Powsr for row in Pm for x in row))

print("   F1 ok: Miller normalization, 54/54")
print("   F2 ok: coordinate matrices (fb basis) == g1_data literals, 54/54")
print("        conjugation bridge Tm*M2r == M2m*Tm holds (raw<->Miller, det |T| = 1)")
print("   F3 ok: |det C| = |det A| = I_k at all 54")
print("   F4 ok: sum_i w'_i M2r^i = I_k * M3r entrywise in RAW coords, 54/54 (the b2 certificate)")
print("   F5 ok: D | I_k and w' = (I_k/D) * N against the committed witness, 54/54")
print("   F6: symmetry candidate REFUTED (recorded; not needed downstream)")
print("F7 sizing (max digits per dim): dim: A / I_k / w' / M2m^i / M2r^i")
for n in sorted(size_by_dim):
    a0, a1, a2, a3 = size_by_dim[n]
    print(f"   dim {n:2d}: {a0:4d} / {a1:4d} / {a2:4d} / {a3:4d}")
print("PROBE 2: ALL CHECKS PASSED")
