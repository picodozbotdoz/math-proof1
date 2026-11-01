#!/usr/bin/env python3
"""Exact Lehmer-coverage counting for math-proof1, iteration 22 (BP lehmer-coverage).

Repo version of the probe-2 script (`research/iteration22/probe2-lehmer-coverage/
FINDINGS.md`): path-independent (all outputs land next to this file) plus the
anchor assertions and the Miller-Rabin audit folded in as committed tests.

Bad prime: p > 65536, p prime, p % 691 == 690  (the sole escape class of the
mod-691 sieve above the dense kernel-verified bound 65536).

Covered predicate (Lean: Ramanujan.tau_ne_zero_of_prime_factors_le_65536_or_mod):
  n >= 1 with every prime factor p of n satisfying (p <= 65536 or p % 691 != 690).

KEY EXACTNESS FACT (asserted below): the smallest bad prime is 70481
(kernel-consistent: it is exactly the bound of the Lean gap theorem
`Ramanujan.tau_ne_zero_of_lt_70481`), and 70481^2 = 4,967,571,361 > 2^32, so
every n < 2^32 has at most one bad prime factor, to the first power.  Hence
for any B <= 2^32:

    uncovered(B) := #{1 <= n < B : n divisible by some bad prime}
                  = sum over bad primes p < B of floor((B-1)/p)   -- EXACT.

Cross-checked by direct multiple-marking at 2^24, 2^25, 2^26, and against the
70481 anchor, and by a deterministic Miller-Rabin audit.

Usage:  python3 bad_prime_sieve.py [xcheck|full|all]     (default: all)
Output: stdout tables + bad_primes_2p32.npy + bad_primes_2p32.txt.gz here.
Runtime ~1 s, < 300 MB RSS (numpy 2.2, single thread).
"""
import gzip
import math
import sys
import time
from pathlib import Path

import numpy as np

Q, RES, DENSE = 691, 690, 65536
HERE = Path(__file__).resolve().parent
t0 = time.time()


def small_primes(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.flatnonzero(s).astype(np.int64)


SP = small_primes(65536)                      # all primes <= 65536 (sqrt(2^32))
SP_NOQ = SP[SP != Q]                          # 691 never divides 691k+690
print(f"[setup] {len(SP)} primes <= 65536 ; setup {time.time()-t0:.1f}s")


def bad_primes_below(B, seg_vals=1 << 29):
    """Segmented sieve of the AP {v = 691k+690 < B}, primality by SP_NOQ.
    Returns array of bad primes in (65536, B)."""
    out = []
    kmax = (B - 1 - RES) // Q                  # largest k with 691k+690 <= B-1
    k0 = (DENSE - RES) // Q + 1                # first k with v > 65536  (v=691k+690>65536)
    assert 0 <= k0 <= kmax + 1
    inv = [pow(int(Q), -1, int(q)) for q in SP_NOQ]
    t = time.time()
    swept = 0
    lo_k = k0
    while lo_k <= kmax:
        hi_k = min(kmax + 1, lo_k + max(1, seg_vals // Q))
        m = hi_k - lo_k
        comp = np.zeros(m, dtype=bool)
        for idx, q in enumerate(SP_NOQ):
            c = ((-RES) * inv[idx]) % int(q)   # k ≡ c (mod q)  <=>  q | 691k+690
            start = lo_k + ((c - lo_k) % int(q))
            # guard the classic negative-slice wraparound (probe-2 bug, caught
            # by the marking cross-check): the start offset must be in-range
            assert 0 <= start - lo_k < m + int(q)
            if start < hi_k:
                comp[start - lo_k::int(q)] = True
        ks = lo_k + np.flatnonzero(~comp)
        out.append(Q * ks + RES)
        swept += m
        dt = time.time() - t
        if swept >= 1 << 26 and (swept >> 26) > ((swept - m) >> 26):
            print(f"  [seg] k swept {swept:>10,} ({Q*swept:.2e} v-range) "
                  f"{dt:6.1f}s  ({Q*swept/dt/1e6:.2f} Mvals/s)", flush=True)
        lo_k = hi_k
    bp = np.concatenate(out) if out else np.array([], dtype=np.int64)
    return bp


def uncovered_exact(bp, B):
    """Exact uncovered count below B (valid for B <= 70481^2)."""
    p = bp[bp < B]
    return int(np.sum((B - 1) // p))


def uncovered_mark(B):
    """Independent cross-check: mark multiples of every bad prime < B."""
    # bad means > 65536; sieve the AP up to B directly, then mark.
    bp = bad_primes_below(B, seg_vals=1 << 28) if B > 1 << 22 else bad_primes_below(B)
    mark = np.zeros(B, dtype=bool)
    for p in bp:
        mark[int(p)::int(p)] = True
    return int(mark[:B].sum()), len(bp)


def miller_rabin(n, bases=(2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)):
    """Deterministic for n < 3.3e24 with these 12 bases."""
    if n < 2:
        return False
    for p in bases:                            # trial division first
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in bases:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def candidate_census(B):
    """The AP candidates in (65536, B): v = 691k+690 (for the Lean filter)."""
    kmax = (B - 1 - RES) // Q
    k0 = (DENSE - RES) // Q + 1
    return k0, kmax, kmax - k0 + 1


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"

    if what in ("all", "xcheck"):
        # --- cross-check the no-overlap identity at 2^24, 2^25, 2^26 ---
        for B in (1 << 24, 1 << 25, 1 << 26):
            bp = bad_primes_below(B)
            f = uncovered_exact(bp, B)
            mk, nbp = uncovered_mark(B)
            print(f"[xcheck] B=2^{int(math.log2(B))}: formula={f:,}  marking={mk:,}  "
                  f"badprimes={nbp:,}  match={f == mk}")
            print(f"         covered = {B-1-f:,} / {B-1:,} = {1-f/(B-1):.6%} "
                  f"uncovered density {f/(B-1):.6%}")
            assert f == mk

    if what in ("all", "full"):
        # --- full exact run to 2^32 ---
        t = time.time()
        bp = bad_primes_below(1 << 32, seg_vals=1 << 29)
        dt = time.time() - t
        print(f"\n[2^32] bad primes in (65536, 2^32): {len(bp):,}  sieve wall {dt:.1f}s "
              f"({(1<<32)/dt/1e6:.2f} Mvals/s effective)")

        # anchor assertions (independent of the sieve internals)
        assert int(bp[0]) == 70481, f"first bad prime {bp[0]} != 70481 (Lean anchor)"
        assert 70481 ** 2 > 1 << 32, "no-overlap identity hypothesis failed"
        print(f"[2^32] first bad prime: {int(bp[0])}  (== Lean gap bound 70481: OK)")
        print(f"[2^32] first 10 bad primes: {bp[:10].tolist()}")
        print(f"[2^32] last bad prime <= 2^32: {int(bp[-1]):,}")
        np.save(HERE / "bad_primes_2p32.npy", bp)
        with gzip.open(HERE / "bad_primes_2p32.txt.gz", "wt") as fh:
            fh.write("\n".join(str(int(p)) for p in bp) + "\n")
        print(f"[2^32] saved bad_primes_2p32.npy + bad_primes_2p32.txt.gz "
              f"({len(bp):,} entries)")

        print("\n[counts] exact uncovered / covered per bound (B <= 2^32, "
              "no-overlap identity):")
        print("  B      bad primes in (65536,B]  uncovered U(B)     covered")
        for e in (18, 20, 21, 24, 25, 26, 27, 28, 29, 30, 31, 32):
            B = 1 << e
            u = uncovered_exact(bp, B)
            nb = int((bp < B).sum())
            print(f"  2^{e:<2}   {nb:>13,}        {u:>13,}   {B-1-u:>13,}"
                  f"   ({1-u/(B-1):.6%} covered)")

        # --- small anchors: candidate census + prime lists for the Lean module
        print("\n[anchors] small-bound data for MathProof/Tau/LehmerCoverageCount.lean:")
        for e in (18, 20):
            B = 1 << e
            sel = bp[bp < B]
            k0, kmax, ncand = candidate_census(B)
            print(f"  2^{e}: candidates 691k+690, k={k0}..{kmax} ({ncand:,} values) "
                  f"-> {len(sel)} bad primes, U(2^{e}) = {uncovered_exact(bp, B):,}")
            if e == 18:
                print(f"        primes: {sel.tolist()}")

        # --- Miller-Rabin audit (deterministic 12-base) ---
        rng = np.random.default_rng(22)
        sample = np.concatenate([bp[bp < (1 << 20)],
                                 rng.choice(bp, size=3000, replace=False),
                                 bp[-1:]])
        bad = [int(p) for p in sample if not miller_rabin(int(p))]
        assert not bad, f"MR audit failures: {bad[:5]}"
        assert all(int(p) % 691 == 690 and int(p) > 65536 for p in bp[::37])
        print(f"\n[audit] Miller-Rabin (12-base deterministic): {len(sample):,} checked"
              f" (all 98 < 2^20 + 3000 random + last), 0 false primes; "
              f"residue/size spot-check OK")

        # sum of reciprocals (for Mertens-style accounting)
        for B in (1 << 28, 1 << 32):
            p = bp[bp < B]
            s = float(np.sum(1.0 / p.astype(np.float64)))
            print(f"[mertens] sum 1/p over bad p in (65536, 2^{int(math.log2(B))}): {s:.8f}")
        # analytic pi(x; q, a) ~ li(x)/phi(q)
        for B in (1 << 28, 1 << 32):
            nb = int((bp < B).sum())
            print(f"[piAP] bad primes in (65536, 2^{int(math.log2(B))}): {nb:,}")
        print(f"\n[done] wall {time.time()-t0:.1f}s")
