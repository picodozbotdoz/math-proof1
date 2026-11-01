#!/usr/bin/env python3
"""Iteration 21, stage G1: re-derive the Frobenius certificates for the 30
weights 72 <= k <= 134 with 6 <= dim S_k <= 10 (blueprint risk R1: never
trust the Iteration-20 census, re-derive).

For each weight this script recomputes, from the charpoly `P_k` of T_2:

* the `(n-1)`-cycle certificate: a prime `ell1` with
  `P mod ell1 = (X - r) * gbar`, `gbar` monic irreducible of degree `n-1`,
  `gbar(r) != 0` (so the reduction is squarefree and `ell1 ∤ disc`);
* the transposition certificate: a prime `ell2` with
  `P mod ell2 = (X - r1) * (X - r2) * hbar`, `hbar` monic irreducible of
  degree `n-2`, `r1 != r2`, `hbar(r1) != 0 != hbar(r2)`;
* squarefreeness is cross-checked by an explicit `gcd(P, P') = 1` over Z/ell;
* `ell ∤ n` (needed because the Lean side transports the resultant through
  the derivative, whose degree must not drop).

The census primes are only *hints*; every assertion is re-derived here.
Output: research/iteration21/data/galoisfull_certs.json

`--prime 3` (Iteration 22, T1 T3-Galois): the T₃ twin — input census
`maeda_t3_dim6_10.json`, output
`research/iteration22-t3-galois/data/t3_galoisfull_certs.json`.  The T₃
census carries no Frobenius hints (hints list stays empty) and every weight's
charpoly is additionally pinned to the *kernel-verified* `P` literal of the
committed `MaedaT3Dim{6..10}Weights.lean` (same parser as
`research/iteration22-t3-galois/g1_anchor.py`) before any scanning happens.
The prime-2 path is untouched.
"""

import json
import os
import random
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from galoisfull_data import make, is_prime, factor_full, factor_degrees  # noqa: E402


# --- Lean-literal parser (iteration-22 T3 mode only) -------------------------
# Minimal twin of g1_anchor.parse_P: evaluates the chunked `C (a * 10 ^ e + b)`
# literals of `noncomputable def P` in MaedaT3Dim{d}Weights.lean.
_TERM = re.compile(
    r"([+-])?\s*C\s*\(\s*([^()+]+(?:\([^()]*\))?[^()]*)\)\s*(?:\*\s*\(X : ℤ\[X\]\)\s*\^\s*(\d+))?",
    re.M)
_NUMOK = re.compile(r"^[\d\s+*^]+$")


def _eval_coeff(txt):
    txt = " ".join(txt.split())
    assert _NUMOK.match(txt), f"unexpected coefficient text: {txt!r}"
    total = 0
    for part in txt.split("+"):
        part = part.strip()
        if "*" in part:
            num, exp = part.split("*")
            assert exp.strip().startswith("10 ^"), part
            total += int(num) * 10 ** int(exp.strip()[4:])
        else:
            total += int(part)
    return total


def lean_t3_charpolys(here):
    """{k: big-endian int list} from the committed MaedaT3Dim files."""
    mf = os.path.join(here, "MathProof", "ModularForms")
    out = {}
    for d in range(6, 11):
        text = open(os.path.join(mf, f"MaedaT3Dim{d}Weights.lean")).read()
        for k in sorted(int(m) for m in re.findall(r"namespace MaedaT3Weight(\d+)\b", text)):
            block = re.search(
                rf"namespace MaedaT3Weight{k}\b(.*?)\nend MaedaT3Weight{k}\b", text, re.S).group(1)
            body = re.search(
                r"noncomputable def P : ℤ\[X\] :=(.*?)\n\ntheorem P_natDegree", block, re.S).group(1)
            coeffs, deg = {}, 0
            for sign, ctext, exp in _TERM.findall(body):
                val = _eval_coeff(ctext)
                if sign == "-":
                    val = -val
                e = int(exp) if exp else 0
                assert e not in coeffs
                coeffs[e] = val
                deg = max(deg, e)
            assert coeffs.get(deg) == 1, (k, "not monic")
            out[k] = [coeffs.get(i, 0) for i in range(deg, -1, -1)]
    return out


def check_squarefree(cp, ell):
    """gcd(cp mod ell, cp' mod ell) must be 1 (unit)."""
    trim, pmul, pmod, pdiv, pgcd, ppowx, psub = make(ell)
    f = trim([c % ell for c in cp[::-1]])
    fp = trim([(i * f[i]) % ell for i in range(1, len(f))])
    return len(pgcd(list(f), fp)) <= 1


def fast_transp(cp, ell, n):
    """Root-counting check that cp mod ell has type (2, 1^(n-2)) (squarefree,
    one irreducible quadratic, n-2 distinct roots) — for the large ell the
    exhaustive root scan is too slow."""
    trim, pmul, pmod, pdiv, pgcd, ppowx, psub = make(ell)
    f = trim([c % ell for c in cp[::-1]])
    fp = trim([(i * f[i]) % ell for i in range(1, len(f))])
    if len(pgcd(list(f), fp)) > 1:
        return False
    xl = ppowx(ell, f)
    lin = pgcd(list(f), psub(xl, [0, 1]))
    nlin = len(lin) - 1
    if nlin != n - 2:
        return False
    rem = pdiv(list(f), lin)
    xl2 = ppowx(ell * ell, rem)
    # irreducible quadratic (no F_ell roots, roots in F_{ell^2}):
    # X^{ell^2} == X (mod rem)
    return pmod(psub(xl2, [0, 1]), rem) == []


def try_pattern(cp, ell, want):
    """want in {'nm1', 'transp'}: check the factorization pattern at `ell`
    and, when it matches, return the certificate pieces."""
    n = len(cp) - 1
    trim, pmul, pmod, pdiv, pgcd, ppowx, psub = make(ell)
    r = factor_full(cp, ell)
    if r is None:
        return None
    degs, factors, roots = r
    if want == 'nm1':
        if sorted(degs, reverse=True) != [n - 1, 1]:
            return None
        gbar = next(f for f in factors if len(f) - 1 == n - 1)
        root = roots[0]
        assert pmod([(-root) % ell, 1], gbar) != [] or gbar != [(-root) % ell, 1]
        # gbar(root) != 0:
        gr = sum(c * pow(root, i, ell) for i, c in enumerate(gbar)) % ell
        assert gr != 0, (ell, root, gbar)
        assert check_squarefree(cp, ell)
        return {'ell': ell, 'root': root, 'gbar': gbar}
    else:
        if sorted(degs, reverse=True) != [2] + [1] * (n - 2):
            return None
        hbar = next(f for f in factors if len(f) - 1 == 2)
        assert len(roots) == n - 2 and len(set(roots)) == n - 2
        for rt in roots:
            hr = sum(c * pow(rt, i, ell) for i, c in enumerate(hbar)) % ell
            assert hr != 0, (ell, rt, hbar)
        assert check_squarefree(cp, ell)
        return {'ell': ell, 'roots': roots, 'hbar': hbar}


def main():
    prime = int(sys.argv[sys.argv.index('--prime') + 1]) if '--prime' in sys.argv else 2
    assert prime in (2, 3), prime
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    if prime == 2:
        src = os.path.join(here, 'research', 'iteration20', 'data',
                           'maeda_dim6_10.json')
        dst = os.path.join(here, 'research', 'iteration21', 'data')
        dst_name = 'galoisfull_certs.json'
    else:
        src = os.path.join(here, 'research', 'iteration20', 'data',
                           'maeda_t3_dim6_10.json')
        dst = os.path.join(here, 'research', 'iteration22-t3-galois', 'data')
        dst_name = 't3_galoisfull_certs.json'
    census = json.load(open(src))
    anchors = lean_t3_charpolys(here) if prime == 3 else None
    if anchors is not None:
        assert len(anchors) == len(census) == 30, (len(anchors), len(census))
    out = []
    for w in census:
        k, dim = w['k'], w['dim']
        n = dim
        cp = w['charpoly']  # descending coefficients, monic
        assert cp[0] == 1 and len(cp) == n + 1, (k, len(cp))
        if anchors is not None:
            # pin the census charpoly to the kernel-verified Lean literal
            assert cp == anchors[k], (k, 'census charpoly != Lean P literal')
        rec = {'k': k, 'dim': dim, 'charpoly': cp}
        # candidate primes: census hints first, then a fresh scan (the T₃
        # census has no hints — empty dict, straight to the scan)
        frob = w.get('frobenius', {})
        hints_nm1 = [frob['n_minus_1_cycle']] \
            if 'n_minus_1_cycle' in frob else []
        hints_tr = [frob['transposition']] \
            if 'transposition' in frob else []
        nm1 = None
        for ell in hints_nm1 + [p for p in range(max(2 * n, n + 3), 4000)
                                if is_prime(p)]:
            if n % ell == 0:
                continue
            try:
                nm1 = try_pattern(cp, ell, 'nm1')
            except AssertionError:
                nm1 = None
            if nm1:
                break
        tr = None
        for ell in hints_tr + [p for p in range(max(2 * n, n + 3), 4000)
                               if is_prime(p)]:
            if n % ell == 0:
                continue
            try:
                tr = try_pattern(cp, ell, 'transp')
            except AssertionError:
                tr = None
            if tr:
                break
        if tr is None:
            # transposition primes have Chebotarev density 1/(2 (n-2)!); scan
            # random primes with the root-counting check
            random.seed((20261031 if prime == 2 else 20261102) + k)
            tries = 0
            while tr is None and tries < 5000000:
                tries += 1
                ell = random.randrange(max(2 * n, n + 3), 20000000)
                if not is_prime(ell) or n % ell == 0:
                    continue
                if fast_transp(cp, ell, n):
                    r = factor_full(cp, ell)
                    degs, factors, roots = r
                    hbar = next(f for f in factors if len(f) - 1 == 2)
                    tr = {'ell': ell, 'roots': roots, 'hbar': hbar}
        assert nm1 is not None, (k, 'nm1')
        assert tr is not None, (k, 'transp')
        # cross-check the census n_minus_1_cycle prime really has type [1, n-1]
        cens = dict(w.get('frobenius_census', {}))
        if nm1['ell'] in cens:
            assert sorted(cens[nm1['ell']], reverse=True) == [n - 1, 1], \
                (k, nm1['ell'], cens[nm1['ell']])
        if tr['ell'] in cens:
            assert sorted(cens[tr['ell']], reverse=True) == [2] + [1] * (n - 2), \
                (k, tr['ell'], cens[tr['ell']])
        # ell must not divide n (derivative degree must not drop) and the
        # extracted data must re-multiply to the charpoly
        assert (n % tr['ell']) != 0 and (n % nm1['ell']) != 0
        rec['nm1'] = nm1
        rec['transp'] = tr
        out.append(rec)
        print(f"k={k}: nm1 ell={nm1['ell']} deg gbar={len(nm1['gbar'])-1}; "
              f"transp ell={tr['ell']} roots={tr['roots']}", flush=True)

    os.makedirs(dst, exist_ok=True)
    with open(os.path.join(dst, dst_name), 'w') as f:
        json.dump(out, f, indent=1)
    print(f"wrote {len(out)} weight certificates to {dst_name}")


if __name__ == '__main__':
    main()
