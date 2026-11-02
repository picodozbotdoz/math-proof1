#!/usr/bin/env python3
"""Probe 3 (iteration 23): Hecke-field corollaries and dim-2 integrality.

Run from the repository root (pure Python, ~1 min):
    python3 research/iteration23/probe3-hecke-field/probe_field.py

Checks:
  G1. dim-2 integrality, GENERIC m: at every dim-2 weight (24,28,30,32,34,38),
      for m = 1..60, the operator identity
          T_m = a_m(f_1) * Id + a_m(f_2) * T_2
      holds as matrices in the Miller basis (this is b3's dim-2 theorem —
      every T_m is an INTEGER polynomial in T_2 with coefficients read off
      the Miller q-expansions; here verified numerically, generic in m).
  G2. eigenvalue sanity (numerical, 1e-6): at k = 36 (dim 3), for every
      eigenvalue lambda_2 of the T_2 matrix, Q(lambda_2) is an eigenvalue of
      the T_3 matrix, where Q is the committed witness (N/D) — the
      matrix-level shape of 'lambda_3 = Q(lambda_2) in Q(lambda_2)'.
  G3. dim-2 weight inventory: for each dim-2 weight, print the charpoly
      (from g1_data-independent re-derivation here) — the Gal = S_2 wiring
      input (MaedaGaloisQuad.bijective_of_quadratic needs: monic quadratic,
      irreducible over Q — the landed `maeda` theorems at these weights).
"""
import math
import json
from math import gcd

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
P = [[1] + [0] * (N - 1)]
for j in range(1, 12): P.append(mul(P[-1], Delta))
e = {0: [1] + [0] * (N - 1)}
def EP(a):
    if a not in e: e[a] = mul(EP(a - 1), E4)
    return e[a]

def basis(k, dim):
    rows = []
    for j in range(1, dim + 1):
        w = k - 12 * j
        b = next(bb for bb in (0, 1, 2) if w - 6 * bb >= 0 and (w - 6 * bb) % 4 == 0)
        a = (w - 6 * b) // 4
        f = mul(P[j], EP(a))
        for _ in range(b): f = mul(f, E6)
        rows.append(f)
    for j in range(dim - 1, -1, -1):
        for i in range(j):
            c0 = rows[i][j + 1]
            rows[i] = [x - c0 * y for x, y in zip(rows[i], rows[j])]
    return rows

def divisors(n): return [d for d in range(1, n + 1) if n % d == 0]

def Tm_cols(k, m, rows):
    dim = len(rows)
    return [[sum(d ** (k - 1) * rows[j][m * i // (d * d)] for d in divisors(gcd(m, i)))
             for i in range(1, dim + 1)] for j in range(dim)]

def charpoly2(M):
    # det(xI - M) for 2x2: x^2 - tr x + det
    return (1, -(M[0][0] + M[1][1]), M[0][0] * M[1][1] - M[0][1] * M[1][0])

print("G1. dim-2 integrality, generic m (m = 1..60, six weights)")
for k in (24, 28, 30, 32, 34, 38):
    rows = basis(k, 2)
    assert all(rows[j][i + 1] == int(i == j) for i in range(2) for j in range(2))
    # T_2 matrix in the Miller basis
    T2c = Tm_cols(k, 2, rows)
    M2 = [[T2c[j][i] for j in range(2)] for i in range(2)]
    for m in range(1, 61):
        McM = Tm_cols(k, m, rows)  # McM[j][i] = a_{i+1}(T_m f_{j+1})
        # claim: M(m) = a_m(f_1) * I + a_m(f_2) * M2
        lhs = [[McM[j][i] for j in range(2)] for i in range(2)]
        rhs = [[int(i == j) * rows[0][m] + M2[i][j] * rows[1][m] for j in range(2)]
               for i in range(2)]
        assert lhs == rhs, (k, m)
print("   ok: T_m = a_m(f1) * 1 + a_m(f2) * T_2 for all m <= 60 at all six dim-2 weights")

print("G2. eigenvalue sanity at k=36 (dim 3): lambda_3 = Q(lambda_2)")
d = json.load(open('research/iteration22/hecke-rational/g1_data.json'))
r = d['36']
M2, M3 = r['M2'], r['M3']
Nw, Dw = r['N'], r['D']
assert Dw == 72
# The exact integer identity N(M2) = D*M3 (the committed certificate) is the
# matrix form of lambda_3 = Q(lambda_2):
def matmul3(X, Y):
    return [[sum(X[i][t] * Y[t][j] for t in range(3)) for j in range(3)] for i in range(3)]
from fractions import Fraction as Fr
acc = [[Fr(0)] * 3 for _ in range(3)]
Id3 = [[int(i == j) for j in range(3)] for i in range(3)]
Pw = [Id3]
for _ in range(2): Pw.append(matmul3(M2, Pw[-1]))
for i in range(3):
    acc = [[x + Fr(Nw[i]) * y for x, y in zip(xr, yr)] for xr, yr in zip(acc, Pw[i])]
assert acc == [[Dw * x for x in row] for row in M3], "Q(M2) = M3 identity failed"
print("   ok: N(M2) = D * M3 exactly (the committed certificate); eigenvalue")
print("       containment lambda_3 = Q(lambda_2) follows spectrally in Lean")

print("G3. dim-2 T_2 charpolys (Gal = S_2 wiring input):")
for k in (24, 28, 30, 32, 34, 38):
    rows = basis(k, 2)
    T2c = Tm_cols(k, 2, rows)
    M2 = [[T2c[j][i] for j in range(2)] for i in range(2)]
    a, b, c0 = charpoly2(M2)
    # discriminant non-square check (integer sqrt test) for irreducibility sanity
    disc = b * b - 4 * c0
    s = math.isqrt(disc) if disc >= 0 else -1
    sq = (s * s == disc) if disc >= 0 else False
    print(f"   k={k}: charpoly T2 = X^2 {'+' if b >= 0 else '-'} {abs(b)} X "
          f"{'+' if c0 >= 0 else '-'} {abs(c0)}; disc = {disc} "
          f"({'square' if sq else 'NON-square -> irreducible -> Gal = S2'})")
print("PROBE 3: ALL CHECKS PASSED")
