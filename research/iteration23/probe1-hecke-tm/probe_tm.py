#!/usr/bin/env python3
"""Probe 1 (iteration 23): the composite Hecke operators T_m on level-one cusp forms.

Run from the repository root (pure Python, ~2 min):
    python3 research/iteration23/probe1-hecke-tm/probe_tm.py

Everything is checked at the level of q-coefficient lists, the same surface
where Lean will work (qExpansion_coeff_ext turns coefficient identities into
operator identities).  The T_m action is the classical formula

    (T_m f)_n = sum_{d | gcd(m,n)} d^(k-1) * f_{m n / d^2}

which for prime m = p specializes to the LANDED Lean formula
(heckeTP_qExpansion_coeff): (T_p f)_n = f_{p n} + p^(k-1) [p | n] f_{n/p}.

Valid-prefix discipline: a coefficient list is built to length N; Tm_action
may only read indices < N, so (T_m f)_n is trustworthy for n <= (N-1) // m.
All comparisons respect the trust region of the composed expressions.

Checks (all exact, integers only):
  A. prime specialization matches the landed formula shape;
  B. multiplicativity of the T-calculus:
        T_m . T_n = sum_{d | gcd(m,n)} d^(k-1) T_{m n / d^2}
     on every Miller-basis element at k in {24, 36, 48} and on Delta,
     for a grid of (m, n) including composite-composite pairs;
  C. Delta anchor: T_m Delta = tau(m) Delta for m <= 21, tau from the
     kernel-verified values tau_one..tau_twenty_one (Basic.lean) —
     independent of this script's E4/E6 arithmetic;
  D. duality matrix identity (the b2 core): with M(m) := (a_i(T_m f_j))_{i,j},
        M(m) = sum_j a_m(f_j) * M(j)        (j = 1..n)
     for m = 1..40 at k in {24, 36, 48, 50};
  E. powers-of-T_2 vs honest T_{2^i}: T_2^i (composition power) is a
     unitriangular integer combination of the honest T_{2^j}, j <= i
     (both families span the same lattice — the det A = det C bridge).
"""
import sys
from math import gcd
from fractions import Fraction as Fr

class Ctx:
    """Power-series arithmetic to length N (packed bignum multiplication)."""
    def __init__(self, N, B):
        # B = limb width in bits; must satisfy N * max|entry|^2 < 2^(B-1) for
        # every product computed in this context (see docstring checks).
        self.N = N; self.B = B
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
        self.mul = lambda a, b: unpack(pack(a) * pack(b))
        self.E4 = [1] + [240 * sig(n, 3) for n in range(1, N)]
        self.E6 = [1] + [-504 * sig(n, 5) for n in range(1, N)]
        c = self.mul(self.mul(self.E4, self.E4), self.E4); s = self.mul(self.E6, self.E6)
        self.Delta = [(x - y) // 1728 for x, y in zip(c, s)]
        assert self.Delta[:6] == [0, 1, -24, 252, -1472, 4830]
        assert self.Delta[12] == -370944
        P = [[1] + [0] * (N - 1)]
        for j in range(1, 12): P.append(self.mul(P[-1], self.Delta))
        self.P = P
        self.e = {0: [1] + [0] * (N - 1)}
    def EP(self, a):
        if a not in self.e: self.e[a] = self.mul(self.EP(a - 1), self.E4)
        return self.e[a]
    def basis(self, k, dim):
        rows = []
        for j in range(1, dim + 1):
            w = k - 12 * j
            b = next(bb for bb in (0, 1, 2) if w - 6 * bb >= 0 and (w - 6 * bb) % 4 == 0)
            a = (w - 6 * b) // 4
            f = self.mul(self.P[j], self.EP(a))
            for _ in range(b): f = self.mul(f, self.E6)
            rows.append(f)
        for j in range(dim - 1, -1, -1):
            for i in range(j):
                c0 = rows[i][j + 1]
                rows[i] = [x - c0 * y for x, y in zip(rows[i], rows[j])]
        return rows

def divisors(n): return [d for d in range(1, n + 1) if n % d == 0]

_pwcache = {}
def pw(k, d):
    key = (k, d)
    if key not in _pwcache: _pwcache[key] = d ** (k - 1)
    return _pwcache[key]

def Tm_action(ctx, k, m, f):
    """out[n] = sum_{d | gcd(m,n)} d^(k-1) f_{m n / d^2}; trustworthy for
    1 <= n <= (ctx.N - 1) // m."""
    out = [0] * ctx.N
    top = (ctx.N - 1) // m
    for n in range(1, top + 1):
        acc = 0
        for d in divisors(gcd(m, n)):
            acc += pw(k, d) * f[m * n // (d * d)]
        out[n] = acc
    return out

print("A. prime specialization == landed formula shape")
ctxA = Ctx(600, 256)
for p in (2, 3, 5, 7):
    for k in (24, 36):
        f = ctxA.basis(k, {24: 2, 36: 3}[k])[0]
        t = Tm_action(ctxA, k, p, f)
        for n in range(1, 60):
            landed = f[p * n] + (p ** (k - 1) * f[n // p] if n % p == 0 else 0)
            assert t[n] == landed, (p, k, n)
print("   ok: identical to heckeTP_qExpansion_coeff for p in {2,3,5,7}")

print("B. T-calculus multiplicativity: T_m T_n = sum_{d|gcd} d^(k-1) T_{mn/d^2}")
GRID = [(2, 2), (2, 3), (2, 4), (2, 6), (2, 8), (3, 3), (3, 4), (3, 6), (4, 4),
        (4, 6), (4, 8), (4, 9), (6, 6), (6, 9), (6, 10), (8, 9), (8, 12), (9, 9),
        (9, 12), (12, 18), (10, 15), (16, 18), (2, 12), (2, 18), (3, 12)]
NC = 12
Nmax = max(m * n for m, n in GRID)
ctxB = Ctx(NC * Nmax + 2, 896)
for k, dim in ((24, 2), (36, 3), (48, 4)):
    for f in ctxB.basis(k, dim) + [ctxB.Delta]:
        for (m, n) in GRID:
            lhs = Tm_action(ctxB, k, m, Tm_action(ctxB, k, n, f))
            rhs = [0] * ctxB.N
            for d in divisors(gcd(m, n)):
                r = Tm_action(ctxB, k, m * n // (d * d), f)
                rhs = [x + pw(k, d) * y for x, y in zip(rhs, r)]
            assert lhs[:NC] == rhs[:NC], (k, m, n)
print(f"   ok: {len(GRID)} pairs x (basis + Delta) x k in {{24,36,48}}, first {NC} coeffs")

print("C. Delta anchor: T_m Delta = tau(m) Delta, m <= 21 (kernel-verified tau)")
# values transcribed from MathProof/Tau/Basic.lean tau_one .. tau_twenty_one
# (kernel-verified); a first hand-typed attempt was WRONG from tau(18) on —
# caught by this very anchor, which is the point of check C.
TAU = [0, 1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920,
       534612, -370944, -577738, 401856, 1217160, 987136, -6905934, 2727432,
       10661420, -7109760, -4219488]
ctxC = Ctx(300, 256)
for m in range(1, 22):
    t = Tm_action(ctxC, 12, m, ctxC.Delta)
    for n in range(1, 13):
        assert t[n] == TAU[m] * ctxC.Delta[n], (m, n)
print("   ok: all m <= 21, first 12 coefficients each")

print("D. duality matrix identity: M(m) = sum_j a_m(f_j) M(j), m = 1..40")
ctxD = Ctx(600, 512)
for k, dim in ((24, 2), (36, 3), (48, 4), (64, 5)):  # dims from g1_data.json
    rows = ctxD.basis(k, dim)
    assert all(rows[j][i + 1] == int(i == j) for i in range(dim) for j in range(dim))
    Mtab = {m: [[Tm_action(ctxD, k, m, rows[j])[i + 1] for j in range(dim)]
                for i in range(dim)] for m in range(1, 41)}
    assert Mtab[1] == [[int(i == j) for j in range(dim)] for i in range(dim)]
    for m in range(2, 41):
        rhs = [[sum(rows[j][m] * Mtab[j + 1][i][l] for j in range(dim))
                for l in range(dim)] for i in range(dim)]
        assert Mtab[m] == rhs, (k, m)
print("   ok: k in {24,36,48,64} (dims 2..5), m = 1..40 each")

print("E. T_2^i unitriangular over the honest T_{2^j}")
ctxE = Ctx(512 * 10 + 4, 1088)
def matmul(A, B, n): return [[sum(A[i][t] * B[t][j] for t in range(n)) for j in range(n)]
                             for i in range(n)]
for k, dim in ((24, 2), (36, 3), (48, 4), (64, 5), (120, 10)):  # dim-10 = 120..134
    rows = ctxE.basis(k, dim)
    M2 = [[Tm_action(ctxE, k, 2, rows[j])[i + 1] for j in range(dim)] for i in range(dim)]
    Pows = [[[int(i == j) for j in range(dim)] for i in range(dim)]]
    for i in range(1, dim): Pows.append(matmul(M2, Pows[-1], dim))
    for i in range(1, dim):
        flats = {0: [x for row in ([[int(a == b) for b in range(dim)] for a in range(dim)])
                     for x in row]}
        for j in range(1, i + 1):
            flats[j] = [x for row in [[Tm_action(ctxE, k, 2 ** j, rows[l])[t + 1]
                                       for l in range(dim)] for t in range(dim)] for x in row]
        target = [x for row in Pows[i] for x in row]
        cols = list(range(0, i + 1))
        Aug = [[Fr(flats[j][r]) for j in cols] + [Fr(target[r])] for r in range(len(target))]
        r = 0; piv = []
        for cidx in cols:
            p = next((rr for rr in range(r, len(Aug)) if Aug[rr][cidx] != 0), None)
            if p is None: continue
            Aug[r], Aug[p] = Aug[p], Aug[r]
            pv = Aug[r][cidx]
            Aug[r] = [x / pv for x in Aug[r]]
            for rr in range(len(Aug)):
                if rr != r and Aug[rr][cidx] != 0:
                    fct = Aug[rr][cidx]
                    Aug[rr] = [x - fct * y for x, y in zip(Aug[rr], Aug[r])]
            piv.append(cidx); r += 1
        assert all(Aug[rr][i + 1] == 0 for rr in range(r, len(Aug))), (k, i, "inconsistent")
        sol = [Fr(0)] * (i + 1)
        for idx, cidx in enumerate(piv): sol[cidx] = Aug[idx][i + 1]
        assert sol[i] == 1, (k, i, "leading coeff not 1")
        assert all(x.denominator == 1 for x in sol), (k, i, "non-integer combination")
print("   ok: dims 2..10 (k = 24,36,48,64,120): integer, unitriangular")

print("PROBE 1: ALL CHECKS PASSED")
