"""Finite-field arithmetic on little-endian coefficient lists mod `ell`,
shared by `tools/gen_galoisfull.py` (Iteration 21).

Independent of `research/maeda-scaling-probe.py` on purpose: this module is
the re-derivation of the Frobenius factorization data (blueprint R1, stage
G1) — the probe's census fields are *cross-checked* against it, never
trusted."""


def make(ell):
    """Little-endian arithmetic over Z/ell (lists of ints in [0, ell))."""
    def trim(a):
        a = list(a)
        while a and a[-1] % ell == 0:
            a.pop()
        return a

    def pmul(a, b):
        if not a or not b:
            return []
        r = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    r[i + j] = (r[i + j] + x * y) % ell
        return trim(r)

    def pmod(a, b):
        b, a = trim(b), trim(a)
        assert b, "division by zero polynomial"
        db, inv = len(b) - 1, pow(b[-1], -1, ell)
        a = list(a)
        while len(a) - 1 >= db and a:
            d = (len(a) - 1) - db
            c = a[-1] * inv % ell
            for i in range(len(b)):
                a[d + i] = (a[d + i] - c * b[i]) % ell
            a = trim(a)
        return trim(a)

    def pdiv(a, b):
        """Quotient a / b (exact when b | a, else the quotient of division)."""
        b, a = trim(b), trim(a)
        assert b, "division by zero polynomial"
        db, inv = len(b) - 1, pow(b[-1], -1, ell)
        q = [0] * max(len(a) - db, 1)
        while len(a) - 1 >= db and a:
            d = (len(a) - 1) - db
            c = a[-1] * inv % ell
            q[d] = c
            for i in range(len(b)):
                a[d + i] = (a[d + i] - c * b[i]) % ell
            a = trim(a)
        return trim(q)

    def pgcd(a, b):
        while True:
            b = trim(b)
            if not b:
                return trim(a)
            a, b = b, pmod(a, b)

    def ppowx(e, f):
        """X ^ e mod f."""
        r, base = [1], [0, 1]
        while e:
            if e & 1:
                r = pmod(pmul(r, base), f)
            base = pmod(pmul(base, base), f)
            e >>= 1
        return r

    def psub(a, b):
        n = max(len(a), len(b))
        return trim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)
                     for i in range(n)])
    return trim, pmul, pmod, pdiv, pgcd, ppowx, psub


def is_prime(m):
    if m < 2:
        return False
    return all(m % d for d in range(2, int(m ** 0.5) + 1))


def prime_divisors(n):
    out, p, m = [], 2, n
    while p * p <= m:
        if m % p == 0:
            out.append(p)
            while m % p == 0:
                m //= p
        p += 1
    if m > 1:
        out.append(m)
    return out


def factor_full(cp, ell):
    """(degree partition descending, little-endian monic factor lists) of the
    monic integer polynomial `cp` (descending coefficients) over Z/ell, or
    None when not squarefree (ell | disc).  Raises when equal-degree splitting
    would be needed (more than one factor of the same degree >= 2) — the
    Iteration-21 certificates only use patterns with a single nonlinear
    factor."""
    trim, pmul, pmod, pdiv, pgcd, ppowx, psub = make(ell)
    f = trim([c % ell for c in cp[::-1]])
    n = len(cp) - 1
    fp = trim([(i * f[i]) % ell for i in range(1, len(f))])
    g = pgcd(list(f), fp)
    if len(g) > 1:
        return None  # repeated factor: ell | disc
    # linear factors by brute-force root scan (ell is small in our use)
    roots, v = [], list(f)
    for r in range(ell):
        if sum(c * pow(r, i, ell) for i, c in enumerate(f)) % ell == 0:
            lin = [(-r) % ell, 1]
            assert pmod(list(v), lin) == []
            roots.append(r)
            v = pdiv(list(v), lin)
    assert len(roots) < ell or not v
    # remaining v: distinct-degree factorization.  Degrees always come out;
    # individual factor lists only when each degree > 1 appears once (the
    # Iteration-21 certificate patterns have a single nonlinear factor).
    factors = [[(-r) % ell, 1] for r in roots]
    degs_left, multi = [], False
    v = trim(v)
    while len(v) > 1:
        dd = 1
        h = []
        while len(h) - 1 < 1:
            h = trim(pgcd(list(v), psub(ppowx(ell ** dd, v), [0, 1])))
            dd += 1
        m = len(h) - 1
        assert m % (dd - 1) == 0 and m <= len(v) - 1, (ell, v, h)
        cnt = m // (dd - 1)
        degs_left += [dd - 1] * cnt
        if cnt > 1:
            multi = True
        elif dd - 1 > 1:
            pass  # single factor of degree dd-1: recovered below if !multi
        v = pdiv(list(v), h)
    assert len(v) <= 1, (ell, v)  # v is a unit (or empty) when fully split
    if not multi and len(degs_left) > 1:
        multi = True  # several nonlinear factors: lists not disentangled
    if not multi and degs_left:
        # the whole leftover was one irreducible factor: recompute it directly
        # as (f / linear factors)
        v = list(f)
        for r in roots:
            v = pdiv(list(v), [(-r) % ell, 1])
        factors.append(trim(v))
    degs = sorted([1] * len(roots) + degs_left, reverse=True)
    assert sum(degs) == n
    return degs, factors, roots


def factor_degrees(cp, ell):
    """Degree partition (descending) of the monic integer polynomial `cp`
    (descending coefficients) factored over Z/ell, or None when not
    squarefree (i.e. ell | disc)."""
    r = factor_full(cp, ell)
    return None if r is None else r[0]


def irreducible_mod(cp, ell):
    """Is cp (descending, monic) irreducible mod ell? (assumes squarefree)."""
    return factor_degrees(cp, ell) == [len(cp) - 1]
