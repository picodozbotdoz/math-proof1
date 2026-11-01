#!/usr/bin/env python3
"""Exploration probe for Iteration 19: Maeda generic engine, dims 6-10 (blueprint stage).

Extends research/maeda-scaling-probe.py (imported, not duplicated — that probe
regresses against the charpolys *proved* in MaedaWeight24 / MaedaDim4Weights)
with everything the Iteration 19 blueprint needs:

  * the full weight list for dims 6-10 (k even, dim S_k in [6,10]);
  * exact T2 charpolys, entry/coefficient digit counts;
  * Rabin irreducibility certificate primes (first + second) and a Lean-side
    kernel-cost model (count of ZMod-l multiplications in the reflected
    square-and-multiply + gcds);
  * a Frobenius census: for every squarefree prime l <= 400 the factorization
    type of charpoly mod l, and the smallest prime of each class that a future
    Dedekind/Frobenius bridge would turn into a cycle-type certificate
    (transposition / (n-1)-cycle / p-cycle with p <= n-3 (Jordan) / n-cycle);
  * JSON dump (charpolys, certificates, census) for the future generator.

Research only: every number here is a certificate candidate; Lean re-checks
everything at build time.
"""
import importlib.util
import json
import sys
import time
from pathlib import Path

RESEARCH = Path(__file__).resolve().parents[2] / "research"
_spec = importlib.util.spec_from_file_location(
    "maeda_scaling_probe", RESEARCH / "maeda-scaling-probe.py")
msp = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(msp)  # runs its regressions-checked series setup

OUT = Path(__file__).resolve().parent / "data" / "maeda_dim6_10.json"
FROB_MAX = 400


def dim_weights(dmin, dmax):
    """Even weights k with dmin <= dim S_k <= dmax (dim formula of the probe)."""
    return [k for k in range(12, 400) if k % 2 == 0 and dmin <= msp.dim(k) <= dmax]


def rabin_cost(ell, n):
    """ZMod-ell multiplications in a reflected Rabin certificate of a degree-n poly.

    Square-and-multiply for X^(ell^n) mod f: floor(log2(ell^n)) squarings plus
    one multiply per set bit; each product of degree-<n polys costs < n^2
    scalar mults (dense, naive).  Then one run of the same length for each
    prime q | n (exponent ell^(n/q)), and gcds of degree-<n polys
    (O(log ell^n) division steps, each O(n^2) mults, cheaper than the powmods
    they follow — folded in as a 30% overhead).
    """
    def powmod_ops(e):
        steps = e.bit_length()
        muls = bin(e).count("1")
        return (steps + muls) * n * n

    total = powmod_cost = powmod_ops(ell ** n)
    for q in msp.prime_divisors(n):
        powmod_cost += powmod_ops(ell ** (n // q))
    total = powmod_cost * 1.3  # gcds + psub_x overhead (modelled)
    return int(total)


def frobenius_census(cp, n):
    """Smallest squarefree prime per cycle-type class + full census table."""
    classes = {
        "transposition": lambda t: sorted(t) == sorted([2] + [1] * (n - 2)),
        "n_minus_1_cycle": lambda t: sorted(t) == sorted([n - 1, 1]),
        "jordan_p_cycle": lambda t: (
            len(t) >= 2 and max(t) <= n - 3 and msp_isprime(max(t))
            and sorted(t) == sorted([max(t)] + [1] * (n - max(t)))
            and max(t) >= 2
        ),
        "n_cycle": lambda t: t == [n],
    }
    found = {}
    census = []
    for ell in range(3, FROB_MAX):
        if not msp.isp(ell):
            continue
        dd = msp.disc_mod(cp, ell)
        if dd == 0:  # ramified / not squarefree: no Frobenius
            continue
        if ("disc_nonres" not in found
                and pow(dd, (ell - 1) // 2, ell) == ell - 1):
            found["disc_nonres"] = ell
        types = msp.factor_degrees(cp, ell)
        census.append((ell, types))
        for name, test in classes.items():
            if name not in found and test(types):
                found[name] = ell
        if len(found) == len(classes):
            break
    return found, census


def msp_isprime(p):
    return msp.isp(p)


def main():
    print("== regressions (from the parent probe) ==")
    r24 = msp.probe(24, verbose=False)
    assert r24["cp"] == [1, -1080, -20468736]
    r48 = msp.probe(48, verbose=False)
    assert r48["cp"] == [1, -5785560, -467142374034432, 1426830562183253852160,
                         3297913828840214320807673856]
    print("k=24 / k=48 charpolys match the proved ones ✓")

    weights = dim_weights(6, 10)
    print(f"\n== dims 6-10: {len(weights)} weights ==")
    rows, js = [], []
    t_all = time.time()
    for k in weights:
        t0 = time.time()
        d, mat, cp = msp.maeda_data(k)
        dt = time.time() - t0
        entry_dg = msp.digits(max(max(abs(x) for x in r) for r in mat))
        cp_dg = msp.digits(max(abs(c) for c in cp[1:]))
        # Rabin certificate primes
        cert, second = None, None
        ell = 3
        while ell < 2000:
            if msp.isp(ell) and msp.rabin_irreducible(cp, ell, d):
                cert = ell
                break
            ell += 2
        assert cert is not None, f"no Rabin prime < 2000 for k={k}"
        ell = cert + 2
        while ell < 2000:
            if msp.isp(ell) and msp.rabin_irreducible(cp, ell, d):
                second = ell
                break
            ell += 2
        cost = rabin_cost(cert, d)
        frob, census = frobenius_census(cp, d)
        row = dict(k=k, dim=d, entry_digits=entry_dg, cp_digits=cp_dg,
                   python_s=round(dt, 2), cert_ell=cert, cert2_ell=second,
                   rabin_zmuls=cost, frob=frob)
        rows.append(row)
        js.append(dict(k=k, dim=d, charpoly=cp, matrix=mat, cert_ell=cert,
                       cert2_ell=second, rabin_zmuls=cost, frobenius=frob,
                       frobenius_census=census))
        print(f"k={k} dim={d}: entries ≤{entry_dg}d, cp ≤{cp_dg}d, "
              f"Rabin ℓ={cert} (+{second}), ~{cost} ZMod-muls, "
              f"Frob: " + ", ".join(f"{n}→{ell}" for n, ell in sorted(frob.items())))
        sys.stdout.flush()
    print(f"\ntotal {time.time() - t_all:.1f}s")

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(js, indent=1))
    print(f"wrote {OUT}")

    # summary by dim: maxima for the blueprint's cost model
    print("\n== per-dim summary ==")
    for d in range(6, 11):
        rs = [r for r in rows if r["dim"] == d]
        print(f"dim {d}: {len(rs)} weights, cp coeffs ≤ {max(r['cp_digits'] for r in rs)} digits, "
              f"Rabin ℓ ≤ {max(r['cert_ell'] for r in rs)}, "
              f"zmuls ≤ {max(r['rabin_zmuls'] for r in rs)}, "
              f"all classes found: {all(r['frob'] for r in rs)}")


if __name__ == "__main__":
    main()
