#!/usr/bin/env python3
"""T₃ census probe for Iteration 21: Maeda's conjecture for the T₃ Hecke operator.

Emits `research/iteration20/data/maeda_t3_dim6_10.json` (dims 6–10, the same
30 weights as the T₂ census) and, for the stretch pass,
`research/iteration20/data/maeda_t3_small.json` (dims 2–5, k ≤ 74).  Research
only: every number is a certificate candidate; Lean re-checks everything at
build time.

The T₃ q-coefficient formula (`heckeTP_qExpansion_coeff`, p-generic in Lean):
`(T₃ f)_m = f_{3m} + 3^(k−1) [3 ∣ m] f_{m/3}`.

ANCHORS (the census hangs on these — the blueprint's own G1 anchor is WRONG
and is corrected here; see blueprint/iteration21-maeda-t3/WORKLOG.md):

  * k=12: S₁₂ = span(Δ) and T₃ Δ = τ(3)·Δ with τ(3) = 252 the kernel-verified
    `Ramanujan.tau 3` — charpoly(T₃ | S₁₂) = X − 252.  (The blueprint claimed
    charpoly(T₃ | S₂₄) = X² − 252·X + 3²³ "because S₂₄ is spanned by Δ"; Δ
    lives in S₁₂, the claim is false: the true k=24 charpoly is
    X² − 339480·X − 19020146544, verified here by two independent routes.)
  * k=16/18/20/22 (dim 1): T₃ = a₃·id with a₃ hand-derived from τ and the
    Eisenstein series (−3348, −4284, 50652, −128844).  k=14 has dim S₁₄ = 0.
  * k=24 (dim 2): pipeline (echelon basis + integer back-substitution) vs an
    independent route (non-echelon basis ΔE₄³, ΔE₆² + Cramer solve + trace /
    det), with the T₃-image linearity checked on the coefficients q³..q⁵.
  * τ(22..30) (needed for the seqPLc3 cap extension, dim ≥ 8): the Euler
    product values agree with the Mordell relations τ(mn) = τ(m)τ(n) (m⊥n) and
    τ(p²) = τ(p)² − p¹¹ — both Lean-proved — for every derivable index
    (22, 24, 25, 26, 27, 28, 30); 23 and 29 are prime indices and are
    certified by the Lean `decide` at build time.
  * Consistency with the T₂ census: same 30 weights, and the T₃ matrix
    commutes with the T₂ matrix of `maeda_dim6_10.json` (whose charpolys are
    Lean-proved in MaedaDim{6..10}Weights.lean) in every weight.

No Frobenius census this time (that served the future Gal = Sₙ route; the
generator does not read it and it dominated the T₂ probe's runtime).
"""
import importlib.util
import json
import sys
import time
from fractions import Fraction as Fr
from pathlib import Path

RESEARCH = Path(__file__).resolve().parents[2] / "research"
_spec = importlib.util.spec_from_file_location(
    "maeda_scaling_probe", RESEARCH / "maeda-scaling-probe.py")
msp = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(msp)  # runs the k=24/48 T₂ regression asserts

DATA_DIR = Path(__file__).resolve().parents[1] / "iteration20" / "data"
OUT = DATA_DIR / "maeda_t3_dim6_10.json"
OUT_SMALL = DATA_DIR / "maeda_t3_small.json"


# ------------------------------------------------------------- the T₃ engine

def t3_image(f, k, n):
    """Coefficients 1..n of T₃ f given the series f (0-indexed list)."""
    return [f[3 * m] + (3 ** (k - 1) * f[m // 3] if m % 3 == 0 else 0)
            for m in range(1, n + 1)]


def maeda_data_p(k, p):
    """(dim, matrix of T_p in the echelon basis, charpoly descending) — the
    prime-generic twin of msp.maeda_data (which stays untouched, T₂)."""
    d = msp.dim(k)
    fs = []
    for i in range(1, d + 1):
        a, b = msp.G(k - 12 * i)
        fs.append(msp.series_mul(msp.pw(msp.D, i),
                                 msp.series_mul(msp.pw(msp.E4, a), msp.pw(msp.E6, b))))
    def coords(x):
        c = []
        for m in range(1, d + 1):
            c.append(x[m] - sum(c[i] * fs[i][m] for i in range(len(c))))
        return c
    rows = []
    for f in fs:
        rows.append(coords([0] + t3_image(f, k, d)))
    Mat = [[rows[j][i] for j in range(d)] for i in range(d)]
    return d, Mat, msp.charpoly(Mat)


def matmul(A, B):
    n = len(A)
    return [[sum(A[i][t] * B[t][j] for t in range(n)) for j in range(n)]
            for i in range(n)]


def rabin_cost(ell, n):
    """ZMod-ell multiplications in a reflected Rabin certificate (iteration-20
    model, reused unchanged for cost comparability)."""
    def powmod_ops(e):
        return (e.bit_length() + bin(e).count("1")) * n * n
    total = powmod_cost = powmod_ops(ell ** n)
    for q in msp.prime_divisors(n):
        powmod_cost += powmod_ops(ell ** (n // q))
    return int(powmod_cost * 1.3)


# ------------------------------------------------------------------- anchors

def anchors():
    print("== anchors ==")
    # k=12: T₃ = τ(3) = 252 (kernel-verified Ramanujan.tau 3)
    d, M, cp = maeda_data_p(12, 3)
    assert d == 1 and M == [[252]] and cp == [1, -252], (d, M, cp)
    print("k=12: charpoly(T3|S12) = X - 252 = X - tau(3)  ✓")
    # dim-1 scalars k=16..22 (a₃ from τ × Eisenstein convolutions)
    for kk, expect in [(16, -3348), (18, -4284), (20, 50652), (22, -128844)]:
        d, M, cp = maeda_data_p(kk, 3)
        assert d == 1 and M == [[expect]] and cp == [1, -expect], (kk, M, cp)
    assert msp.dim(14) == 0  # no cusp forms of weight 14
    print("k=16/18/20/22 (dim 1): a₃ = -3348, -4284, 50652, -128844  ✓")
    # k=24: independent non-echelon route
    k = 24
    b1 = msp.series_mul(msp.pw(msp.D, 1), msp.pw(msp.E4, 3))
    b2 = msp.series_mul(msp.pw(msp.D, 1), msp.pw(msp.E6, 2))
    def solve2(w):
        A = [[Fr(b1[1]), Fr(b2[1])], [Fr(b1[2]), Fr(b2[2])]]
        det0 = A[0][0] * A[1][1] - A[0][1] * A[1][0]
        al = (Fr(w[1]) * A[1][1] - A[0][1] * Fr(w[2])) / det0
        be = (A[0][0] * Fr(w[2]) - Fr(w[1]) * A[1][0]) / det0
        assert al.denominator == 1 and be.denominator == 1
        for mm in (3, 4, 5):  # T₃-image linearity on further coefficients
            assert al * b1[mm] + be * b2[mm] == w[mm], mm
        return al, be
    c1 = solve2([0] + t3_image(b1, k, 5))
    c2 = solve2([0] + t3_image(b2, k, 5))
    tr = c1[0] + c2[1]
    det = c1[0] * c2[1] - c2[0] * c1[1]
    cp_ind = [1, -tr, det]
    d, M, cp = maeda_data_p(24, 3)
    assert d == 2 and cp == cp_ind == [1, -339480, -19020146544], (cp, cp_ind)
    print("k=24: charpoly(T3|S24) = X² - 339480·X - 19020146544, dual route  ✓")
    # τ(22..30) Mordell cross-checks (Lean-proved relations)
    tau = {n: msp.D[n] for n in range(31)}
    checks = {22: tau[2] * tau[11], 24: tau[8] * tau[3], 25: tau[5] ** 2 - 5 ** 11,
              26: tau[2] * tau[13], 27: tau[3] * tau[9] - 3 ** 11 * tau[3],
              28: tau[4] * tau[7], 30: tau[2] * tau[15]}
    assert all(tau[n] == v for n, v in checks.items())
    print("tau(22..30) Mordell cross-checks (7 of 9 derivable)  ✓:",
          [tau[n] for n in range(22, 31)])


# -------------------------------------------------------------------- census

def cert_primes(cp, d):
    cert = second = None
    ell = 3
    while ell < 2000:
        if msp.isp(ell) and msp.rabin_irreducible(cp, ell, d):
            cert = ell
            break
        ell += 2
    assert cert is not None
    ell = cert + 2
    while ell < 2000:
        if msp.isp(ell) and msp.rabin_irreducible(cp, ell, d):
            second = ell
            break
        ell += 2
    assert second is not None
    return cert, second


def reflected_checks(cp, ell, n):
    """Reflected-engine sanity (the same asserts the generator re-runs)."""
    fle = [c % ell for c in cp[::-1]]
    assert len(fle) == n + 1 and fle[-1] == 1
    top = msp.powx(ell ** n, fle, ell)
    assert msp.pnorm(list(top)) == [0, 1]
    for q in msp.prime_divisors(n):
        hq = msp.psub_x(msp.powx(ell ** (n // q), fle, ell), ell)
        g = msp.pnorm(list(msp.pgcd(list(fle), list(hq), ell)))
        assert len(g) == 1, (q, g)


def census(dmin, dmax, kmax, t2data=None, verbose=True):
    rows = []
    for k in range(12, kmax + 1):
        if k % 2 or not (dmin <= msp.dim(k) <= dmax):
            continue
        t0 = time.time()
        d, mat, cp = maeda_data_p(k, 3)
        dt = time.time() - t0
        if t2data is not None:
            w = next(w for w in t2data if w["k"] == k)
            assert d == w["dim"], k
            assert matmul(w["matrix"], mat) == matmul(mat, w["matrix"]), k
        cert, second = cert_primes(cp, d)
        reflected_checks(cp, cert, d)
        rows.append(dict(k=k, dim=d,
                         entry_digits=msp.digits(max(max(abs(x) for x in r) for r in mat)),
                         cp_digits=msp.digits(max(abs(c) for c in cp[1:])),
                         python_s=round(dt, 2), cert_ell=cert, cert2_ell=second,
                         rabin_zmuls=rabin_cost(cert, d),
                         F_bits=(cert ** d).bit_length(),
                         charpoly=cp, matrix=mat))
        if verbose:
            print(f"k={k} dim={d}: entries ≤{rows[-1]['entry_digits']}d, "
                  f"cp ≤{rows[-1]['cp_digits']}d, Rabin ℓ={cert} (+{second}), "
                  f"F={rows[-1]['F_bits']} bits, ~{rows[-1]['rabin_zmuls']} ZMod-muls")
            sys.stdout.flush()
    return rows


def main():
    anchors()
    t2data = json.load(open(DATA_DIR / "maeda_dim6_10.json"))
    t2ks = sorted(w["k"] for w in t2data)
    print(f"\n== dims 6-10: {len(t2ks)} weights (same list as the T₂ census) ==")
    t_all = time.time()
    rows = census(6, 10, 400, t2data=t2data)
    assert sorted(r["k"] for r in rows) == t2ks
    OUT.write_text(json.dumps(rows, indent=1))
    print(f"wrote {OUT} ({time.time() - t_all:.1f}s)")

    print("\n== per-dim summary ==")
    for d in range(6, 11):
        rs = [r for r in rows if r["dim"] == d]
        print(f"dim {d}: {len(rs)} weights, cp ≤ {max(r['cp_digits'] for r in rs)} digits, "
              f"Rabin ℓ ≤ {max(r['cert_ell'] for r in rs)}, "
              f"zmuls ≤ {max(r['rabin_zmuls'] for r in rs)}")

    print("\n== stretch: dims 2-5 (k ≤ 74) ==")
    small = census(2, 5, 74, verbose=False)
    for r in small:
        print(f"k={r['k']} dim={r['dim']}: Rabin ℓ={r['cert_ell']} (+{r['cert2_ell']})")
    OUT_SMALL.write_text(json.dumps(small, indent=1))
    print(f"wrote {OUT_SMALL}")


if __name__ == "__main__":
    main()
