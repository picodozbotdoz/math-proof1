#!/usr/bin/env python3
"""Scaling probe for the Maeda machinery (research only; Lean re-checks everything).

Question: the formalized Maeda results stop at dim S_k = 4 (weights 48-62).
What would it take to push to dim 5 (weights 60, 64, 66, 68, 70, 74) and on to
dim 25 (weights 300-314)?  This probe computes, per weight:

  * the triangular basis Delta^i E4^a E6^b and the exact integer matrix of T_2
    (same echelon/q-coefficient algorithm as tools/gen_maeda.py and
    charpoly_dim2/3/4.lean);
  * the exact characteristic polynomial (Bareiss det + interpolation);
  * an irreducibility certificate: for dim 5 the smallest prime ell with no
    root and no quadratic factor mod ell (the quintic analogue of the committed
    quartic certificate); for dim >= 6 a Rabin certificate
    (f | X^(ell^n) - X  and  gcd(f, X^(ell^(n/q)) - X) = 1);
  * for dim 5 also the S_5 data: discriminant non-residue mod small primes and
    factorization types containing a cubic (a 3-cycle certificate, pending a
    future Dedekind/Frobenius lemma);
  * size/timing data (digits of matrix entries and charpoly coefficients,
    seconds of Python time) to extrapolate kernel cost.

Cross-checks: the tau values used agree with tools/gen_maeda.py, and the
computed charpolys at weights 24 / 48 reproduce the ones proved in
MaedaWeight24.lean / MaedaDim4Weights.lean.
"""
import time
from fractions import Fraction as F

L = 51  # series truncation: covers index 50 = 2*dim for dim <= 25

# ---------------------------------------------------------------- series data

def sigma(k, n):
    return sum(d ** k for d in range(1, n + 1) if n % d == 0)

def series_mul(a, b):
    r = [0] * L
    for i in range(L):
        if a[i]:
            for j in range(L - i):
                if b[j]:
                    r[i + j] += a[i] * b[j]
    return r

def pw(a, e):
    r = [1] + [0] * (L - 1)
    for _ in range(e):
        r = series_mul(r, a)
    return r

# prod_{m>=1} (1 - q^m)^24 truncated at index L-1  (Euler)
eta24 = [1] + [0] * (L - 1)
from math import comb
for m in range(1, L):
    fac = [0] * L
    top = min(24, (L - 1) // m)
    for c in range(top + 1):
        fac[c * m] = comb(24, c) * (-1) ** c
    eta24 = series_mul(eta24, fac)

# Delta as a 0-indexed series: D[n] = tau(n) for n >= 1, D[0] = 0
D = [0] + eta24[:L - 1]
TAU_GEN = [0, 1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643,
           -115920, 534612]
assert D[:12] == TAU_GEN, f"tau regression failed: {D[:12]}"

E4 = [1] + [240 * sigma(3, n) for n in range(1, L)]
E6 = [1] + [-504 * sigma(5, n) for n in range(1, L)]

def G(w):  # E4^a E6^b of weight w, minimal b (same as gen_maeda.py)
    for b in (0, 1):
        if w - 6 * b >= 0 and (w - 6 * b) % 4 == 0:
            return ((w - 6 * b) // 4, b)
    raise ValueError(w)

def dim(k):
    m = k - 12
    return m // 12 if m % 12 == 2 else m // 12 + 1

# ------------------------------------------------------- exact linear algebra

def bareiss_det(M):
    M = [row[:] for row in M]
    n = len(M)
    sign, prev = 1, 1
    for k in range(n - 1):
        if M[k][k] == 0:
            for i in range(k + 1, n):
                if M[i][k] != 0:
                    M[k], M[i] = M[i], M[k]
                    sign = -sign
                    break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
            M[i][k] = 0
        prev = M[k][k]
    return sign * M[n - 1][n - 1]

def charpoly(M):
    """charpoly of an integer matrix, by evaluation + interpolation."""
    n = len(M)
    ts = [0] + [s for v in range(1, 60) for s in (v, -v)][:n]
    vals = [bareiss_det([[(t if i == j else 0) - M[i][j] for j in range(n)]
                         for i in range(n)]) for t in ts]
    # Lagrange interpolation, exact
    poly = [F(0)] * (n + 1)  # poly[i] = coeff of x^i
    for i, t in enumerate(ts):
        basis = [F(1)]
        denom = F(1)
        for j, u in enumerate(ts):
            if j == i:
                continue
            new = [F(0)] * min(len(basis) + 1, n + 1)
            for kk, c in enumerate(basis):
                new[kk + 1] += c
                new[kk] -= u * c
            basis = new  # multiply by (x - u)
            denom *= (t - u)
        c = F(vals[i]) / denom
        for kk in range(n + 1):
            poly[kk] += c * basis[kk]
    assert all(x.denominator == 1 for x in poly), "non-integral charpoly"
    # to monic descending [1, c1, ..., cn] like gen_maeda.py
    asc = [int(x) for x in poly]
    return asc[::-1]

def maeda_data(k):
    """(dim, matrix of T2 in the echelon basis, charpoly list descending)."""
    d = dim(k)
    fs = []
    for i in range(1, d + 1):
        a, b = G(k - 12 * i)
        fs.append(series_mul(pw(D, i), series_mul(pw(E4, a), pw(E6, b))))
    def coords(x):
        c = []
        for m in range(1, d + 1):
            c.append(x[m] - sum(c[i] * fs[i][m] for i in range(len(c))))
        return c
    rows = []
    for f in fs:
        t2 = [0] * (2 * d + 1)
        for m in range(1, d + 1):
            t2[m] = f[2 * m] + (2 ** (k - 1) * f[m // 2] if m % 2 == 0 else 0)
        rows.append(coords(t2))
    Mat = [[rows[j][i] for j in range(d)] for i in range(d)]
    return d, Mat, charpoly(Mat)

# ------------------------------------------------- arithmetic mod a prime ell
# polynomials over Z/ell as little-endian lists

def pnorm(a):
    while a and a[-1] == 0:
        a.pop()
    return a

def pmul(a, b, l):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % l
    return pnorm(r)

def pdivmod(a, f, l):
    """(quotient, remainder) of a by monic-up-to-unit f over Z/l, little-endian."""
    a = a[:]
    q = [0] * max(0, len(a) - len(f) + 1)
    df = len(f) - 1
    inv = pow(f[-1], -1, l)
    while len(a) - 1 >= df and pnorm(a):
        c = a[-1] * inv % l
        sh = len(a) - 1 - df
        q[sh] = c
        for i, fc in enumerate(f):
            a[sh + i] = (a[sh + i] - c * fc) % l
        pnorm(a)
    return pnorm(q), a

def pmod(a, f, l):
    return pdivmod(a, f, l)[1]

def psub_x(h, l):
    """h - X over Z/l, little-endian."""
    h = h[:] + [0] * max(0, 2 - len(h))
    h[1] = (h[1] - 1) % l
    return pnorm(h)

def powx(e, f, l):
    """X^e mod f over Z/l, by square-and-multiply."""
    res = [1]
    base = pmod([0, 1], f, l)
    while e:
        if e & 1:
            res = pmod(pmul(res, base, l), f, l)
        base = pmod(pmul(base, base, l), f, l)
        e >>= 1
    return res

def pgcd(a, b, l):
    a, b = a[:], b[:]
    while b:
        a, b = b, pmod(a, b, l)
    return a

def poly_eval(cp, x, l):
    # cp descending monic
    r = 0
    for c in cp:
        r = (r * x + c) % l
    return r

def red(cp, l):
    return [c % l for c in cp]

def fmod(cp, l):
    """cp (descending, monic) as a little-endian list over Z/l."""
    return [c % l for c in cp][::-1]

def rabin_irreducible(cp, l, n):
    """cp monic degree n over Z: irreducible mod l? (Rabin)"""
    f = fmod(cp, l)
    assert len(f) == n + 1 and f[-1] == 1 % l
    if n == 1:
        return True
    if pmod(psub_x(powx(l ** n, f, l), l), f, l) != []:  # f | X^(l^n) - X
        return False
    for q in prime_divisors(n):
        h = psub_x(powx(l ** (n // q), f, l), l)
        if len(pnorm(pgcd(f, h, l))) != 1:  # any nonzero constant = coprime
            return False
    return True

def prime_divisors(n):
    out, q = [], 2
    while q * q <= n:
        if n % q == 0:
            out.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        out.append(n)
    return out

def isp(n):
    return n > 1 and all(n % i for i in range(2, int(n ** .5) + 1))

def irr_quintic_scan(cp, l):
    """No root and no monic quadratic factor mod l (Lean-style certificate).

    A reducible monic quintic has a factor of degree <= 2 (deg-2 factor times a
    cubic cofactor): f = (X^2 + uX + v)(X^3 + rX^2 + sX + t), with
    a1 = u+r, a2 = v+ur+s, a3 = vr+us+t, a4 = vs+ut, a5 = vt for
    f = X^5 + a1 X^4 + ... + a5.  r, s, t are forced by u, v; the last two
    equations are then a pure check."""
    f = red(cp, l)
    a1, a2, a3, a4, a5 = f[1:]
    if any(poly_eval(cp, x, l) == 0 for x in range(l)):
        return False
    for u in range(l):
        for v in range(l):
            r = (a1 - u) % l
            s = (a2 - v - u * r) % l
            t = (a3 - v * r - u * s) % l
            if (v * s + u * t - a4) % l == 0 and (v * t - a5) % l == 0:
                return False
    return True

def disc_mod(cp, l):
    """disc(f) mod l via the Sylvester determinant of (f, f')."""
    n = len(cp) - 1
    f = red(cp, l)
    fp = [((n - i) * f[i]) % l for i in range(n)]  # descending derivative
    m = 2 * n - 1
    Syl = [[0] * m for _ in range(m)]
    for r in range(n - 1):
        for i, c in enumerate(f):
            if c:
                Syl[r][r + i] = c
    for r in range(n):
        for i, c in enumerate(fp):
            if c:
                Syl[n - 1 + r][r + i] = c
    det, sgn = 1, 1
    for c in range(m):
        piv = next((r for r in range(c, m) if Syl[r][c]), None)
        if piv is None:
            return 0
        if piv != c:
            Syl[c], Syl[piv] = Syl[piv], Syl[c]
            sgn = -sgn
        inv = pow(Syl[c][c], -1, l)
        for r in range(c + 1, m):
            if Syl[r][c]:
                fac = Syl[r][c] * inv % l
                for cc in range(c, m):
                    Syl[r][cc] = (Syl[r][cc] - fac * Syl[c][cc]) % l
    for c in range(m):
        det = det * Syl[c][c] % l
    return sgn * det % l

def factor_degrees(cp, l):
    """multiset of degrees of irreducible factors mod l (distinct-degree only)."""
    remaining = fmod(cp, l)
    degs = []
    d = 1
    while len(pnorm(remaining[:])) - 1 >= 2 * d:
        hh = psub_x(powx(l ** d, remaining, l), l)
        g = pnorm(pgcd(remaining, pnorm(hh), l))
        gd = len(g) - 1
        if gd > 0:
            degs.extend([d] * (gd // d))
            remaining = pdivmod(remaining, g, l)[0]
            if len(pnorm(remaining)) <= 1:
                break
        d += 1
    if len(pnorm(remaining)) - 1 >= 1:
        degs.append(len(pnorm(remaining)) - 1)
    return sorted(degs)

# ------------------------------------------------------------------- the probe

def digits(x):
    return len(str(abs(x)))

def probe(k, verbose=True):
    t0 = time.time()
    d, Mat, cp = maeda_data(k)
    t1 = time.time()
    maxentry = max(max(abs(x) for x in row) for row in Mat)
    maxcp = max(abs(c) for c in cp[1:])
    out = {"k": k, "dim": d, "time_s": t1 - t0,
           "entry_digits": digits(maxentry), "cp_digits": digits(maxcp),
           "cp": cp, "Mat": Mat}
    # smallest irreducibility-certificate prime
    l = 3
    while True:
        if isp(l):
            if rabin_irreducible(cp, l, d):
                out["cert_ell"] = l
                break
        l += 2
        if l > 1200:
            out["cert_ell"] = None
            break
    # sanity: Rabin at a second prime too
    out["rabin_second"] = next((l2 for l2 in range(out["cert_ell"] + 2, 2000, 2)
                                if isp(l2) and rabin_irreducible(cp, l2, d)), None)
    if verbose:
        print(f"k={k} dim={d}  T2 entries ≤ {out['entry_digits']} digits, "
              f"charpoly coeffs ≤ {out['cp_digits']} digits, "
              f"Python {t1 - t0:.2f}s, cert ℓ={out['cert_ell']} "
              f"(2nd {out['rabin_second']})")
    return out

def quintic_details(k):
    """Extra data for the dim-5 S_5 certificate (future work)."""
    d, Mat, cp = maeda_data(k)
    assert d == 5
    l = 3
    while not (isp(l) and irr_quintic_scan(cp, l)):
        l += 2
    print(f"  k={k}: quintic scan certificate ℓ={l} (no root + no quadratic)")
    # discriminant: first prime where disc is a non-residue (and f squarefree)
    for l2 in range(3, 200):
        if not isp(l2):
            continue
        dd = disc_mod(cp, l2)
        if dd == 0:
            continue
        if pow(dd, (l2 - 1) // 2, l2) == l2 - 1:
            print(f"    disc is a non-residue mod {l2}")
            break
    # a prime with factorization type (3,1,1): a 3-cycle certificate
    for l2 in range(3, 200):
        if not isp(l2):
            continue
        f = red(cp, l2)
        if disc_mod(cp, l2) == 0:
            continue
        degs = factor_degrees(cp, l2)
        if sorted(degs) == [1, 1, 3]:
            print(f"    factor type (1,1,3) mod {l2}  [3-cycle, needs Dedekind]")
            break
    return cp

if __name__ == "__main__":
    print("== regressions against proved results ==")
    r24 = probe(24, verbose=False)
    assert r24["cp"] == [1, -1080, -20468736], r24["cp"]
    print("k=24 charpoly matches MaedaWeight24 ✓")
    r48 = probe(48, verbose=False)
    assert r48["cp"] == [1, -5785560, -467142374034432, 1426830562183253852160,
                         3297913828840214320807673856], r48["cp"]
    print("k=48 charpoly matches MaedaDim4Weights ✓")

    print("\n== dim 5 (the six weights) ==")
    for k in (60, 64, 66, 68, 70, 74):
        r = probe(k)
        quintic_details(k)

    print("\n== scaling probe (k = 12*dim) ==")
    for d in (6, 8, 10, 12, 16, 20):
        probe(12 * d)

    print("\n== dim 25 (the six weights) ==")
    for k in (300, 304, 306, 308, 310, 314):
        probe(k)
