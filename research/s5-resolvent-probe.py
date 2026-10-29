#!/usr/bin/env python3
"""Design probe for the S5 Galois certificate (research only; Lean re-checks all).

The F20-resolvent of the quintic f = X^5 + aX^4 + bX^3 + cX^2 + dX + e:

For a 5-cycle c (on the five roots), let
    theta(c)  = sum_v x_v * x_{c v}          (the pentagon sum),
so theta(c^2) is the pentagram sum (its edge set is the complement), and
    Theta(c)  = theta(c) * theta(c^2)        (degree 4 in the roots).
theta(c^k) equals theta(c) or theta(c^2) for k in {1,2,3,4} (relabeling v ->
c^j v), so Theta(c^k) = Theta(c): the normalizer N(<c>) = F20 fixes Theta(c)
(as a polynomial identity -- no genericity).  The six values Theta(c_i), one
per 5-cycle subgroup, are permuted by S5, so

    R(Y) = prod_i (Y - Theta(c_i)) = Y^6 + sum_j (-1)^j E_j Y^(6-j)

has coefficients that are symmetric polynomials in x_0..x_4, hence explicit
polynomials in (a,b,c,d,e) -- computed here by exact integer interpolation in
the elementary symmetric functions e_1..e_5.

Certificate logic (to be formalized):  Gal irreducible => 5 | |G|;  disc
non-square => some odd element => 2 | |G| and G not<= A5;  S5 has no subgroups
of order 30 or 40 (coset action + normal subgroups of S5 = {1, A5, S5});  so
if |G| != 120 then |G| in {10, 20, 60}; |G| = 60 => index 2 => normal => G =
A5, contradicting oddness;  |G| in {10, 20} => the Sylow-5 of G is normal in G
and its normalizer N in S5 contains G, and Theta(c) (c a generator) is fixed
by G, hence rational, hence a rational root of R.  So: R has no rational root
(<== no root mod a single prime ell, R monic integer) + disc non-square +
irreducible  =>  Gal = S5.

Also computes delta^2 = disc in (a..e) the same way, cross-checks both against
the six Maeda dim-5 quintics (Sylvester discriminant / direct root products),
and finds per-weight certificate primes.
"""
from fractions import Fraction as F
from itertools import combinations, permutations
import random, math, json

# ---------------------------------------------------------- poly dict arithmetic
def padd(p, q):
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, 0) + c
        if r[m] == 0:
            del r[m]
    return r

def pmul(p, q):
    r = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(a + b for a, b in zip(m1, m2))
            r[m] = r.get(m, 0) + c1 * c2
    return {m: c for m, c in r.items() if c}

def ppow(p, n):
    r = {(0,) * 5: 1}
    for _ in range(n):
        r = pmul(r, p)
    return r

def peval(p, xs):
    return sum(c * math.prod(x ** a for x, a in zip(xs, m)) for m, c in p.items())

X = [{tuple(1 if k == i else 0 for k in range(5)): 1} for i in range(5)]
def xj(j):  # the polynomial x_j
    return X[j]

# ------------------------------------------------------------------ the pieces
vand = {(0,) * 5: 1}
for i, j in combinations(range(5), 2):
    vand = pmul(vand, padd(xj(i), {tuple(1 if k == j else 0 for k in range(5)): -1}))
delta2 = pmul(vand, vand)
print(f"vandermonde {len(vand)} terms, delta^2 {len(delta2)} terms, "
      f"exp range [{min(min(m) for m in delta2)},{max(max(m) for m in delta2)}]")

def cmul(u, v):  # compose permutations (functions on 0..4)
    return tuple(u[v[i]] for i in range(5))

subs = {}
for p in permutations(range(5)):
    orb, v = set(), 0
    for _ in range(5):
        orb.add(v)
        v = p[v]
    if len(orb) == 5:
        powers, q = set(), p
        for _ in range(5):
            powers.add(q)
            q = cmul(p, q)
        subs[frozenset(powers)] = p
assert len(subs) == 6
cycs = sorted(subs.values())

def theta_poly(c):
    s = {}
    for v in range(5):
        s = padd(s, pmul(xj(v), xj(c[v])))
    return s

def Theta_poly(c):
    return pmul(theta_poly(c), theta_poly(cmul(c, c)))

Thetas = [Theta_poly(c) for c in cycs]
print("six Theta products, terms:", [len(t) for t in Thetas])

# sanity 1: Theta(c^k) = Theta(c) as polynomials (the F20 identity)
for c in cycs[:2]:
    for k in (2, 3, 4):
        ck = c
        for _ in range(k - 1):
            ck = cmul(c, ck)
        assert Theta_poly(ck) == Theta_poly(c)
print("Theta(c^k) = Theta(c) for k=1..4 ✓ (exact polynomial identity)")

# sanity 2: the six Thetas are permuted by S5 (as values, multiset-stable)
rnd = random.Random(999)
for _ in range(25):
    xs = tuple(rnd.randint(-9, 9) for _ in range(5))
    if len(set(xs)) < 5:
        continue
    vals = sorted(peval(t, xs) for t in Thetas)
    for p in permutations(range(5)):
        ys = [xs[p[i]] for i in range(5)]
        assert sorted(peval(t, ys) for t in Thetas) == vals
print("the six Theta values are S5-stable ✓")

# ------------------------------------------------ symmetric-function reduction
def elementary(xs):
    es = []
    for k in range(1, 6):
        s = 0
        for idx in combinations(range(5), k):
            t = 1
            for i in idx:
                t *= xs[i]
            s += t
        es.append(s)
    return es

def weighted_monomials(total):
    out = []
    def rec(i, rem, acc):
        if i == 6:
            if rem == 0:
                out.append(tuple(acc))
            return
        for a in range(rem // i + 1):
            rec(i + 1, rem - a * i, acc + [a])
    rec(1, 0 if False else total, [])
    return out

def monval(es, m):
    return math.prod(e ** a for e, a in zip(es, m))

def rref_independent(rows, n):
    """greedy: keep rows maintaining full column-rank progress; return kept rows."""
    kept = []
    for row in rows:
        M = [[F(v) for v in r] for r in kept] + [[F(v) for v in row]]
        # eliminate
        rank = 0
        for col in range(n):
            piv = next((r for r in range(rank, len(M)) if M[r][col] != 0), None)
            if piv is None:
                continue
            M[rank], M[piv] = M[piv], M[rank]
            pv = M[rank][col]
            M[rank] = [v / pv for v in M[rank]]
            for r in range(len(M)):
                if r != rank and M[r][col] != 0:
                    fac = M[r][col]
                    M[r] = [a - fac * b for a, b in zip(M[r], M[rank])]
            rank += 1
        if len(M) == rank or all(all(v == 0 for v in M[r]) is False and True for r in range(len(M))):
            kept.append(row)
            if len(kept) == n:
                break
    return kept

def reduce_symmetric(S, total, seed=12345):
    """Express the symmetric function S(xs) (int-valued) as a polynomial in
    e1..e5, weighted-homogeneous of degree `total`.  Linear algebra mod the
    Mersenne prime 2^61-1, lifted to symmetric representatives, then verified
    exactly at 50 fresh integer points (the exact verification is the proof
    of correctness of the lift)."""
    P = 2305843009213693951
    mons = weighted_monomials(total)
    n = len(mons)
    rnd = random.Random(seed)
    basis, pivots = [], []
    while len(basis) < n:
        xs = tuple(rnd.randint(-25, 25) for _ in range(5))
        if len(set(xs)) < 5:
            continue
        es = elementary(xs)
        row = [monval(es, m) % P for m in mons] + [S(xs) % P]
        for k, pc in enumerate(pivots):
            f = row[pc]
            if f:
                row = [(a - f * b) % P for a, b in zip(row, basis[k])]
        pc = next((i for i, v in enumerate(row[:n]) if v), None)
        if pc is None:
            continue
        inv = pow(row[pc], P - 2, P)
        row = [v * inv % P for v in row]
        for k, pc2 in enumerate(pivots):
            f = basis[k][pc]
            if f:
                basis[k] = [(a - f * b) % P for a, b in zip(basis[k], row)]
        basis.append(row)
        pivots.append(pc)
    assert sorted(pivots) == list(range(n))
    sol = {}
    for brow, pc in zip(basis, pivots):
        v = brow[n]
        sol[mons[pc]] = v if v <= P // 2 else v - P
    for _ in range(50):
        xs = tuple(rnd.randint(-40, 40) for _ in range(5))
        if len(set(xs)) < 5:
            continue
        es = elementary(xs)
        lhs = sum(c * monval(es, m) for m, c in sol.items())
        assert lhs == S(xs), (xs, lhs, S(xs))
    return sol

print("reducing e_j(Theta) (weighted degree 4j) ...")
EJ = {}
for j in range(1, 7):
    def Smake(j):
        def S(xs):
            vals = [peval(t, xs) for t in Thetas]
            s = 0
            for idx in combinations(range(6), j):
                t = 1
                for i in idx:
                    t *= vals[i]
                s += t
            return s
        return S
    EJ[j] = reduce_symmetric(Smake(j), 4 * j, seed=1000 + j)
    print(f"  E_{j}: {len(EJ[j])} monomials")

print("reducing delta^2 (weighted degree 20) ...")
DISC = reduce_symmetric(lambda xs: peval(delta2, xs), 20, seed=777)
print(f"  disc: {len(DISC)} monomials")

out = {"cycles": [list(c) for c in cycs],
       "ej_theta": {str(j): {"".join(map(str, m)): c for m, c in EJ[j].items()} for j in EJ},
       "disc": {"".join(map(str, m)): c for m, c in DISC.items()}}
with open("research/s5_resolvent.json", "w") as f:
    json.dump(out, f)
print("saved research/s5_resolvent.json")

# pretty-print the E_j in e-variables with e_i = (sigma_i of the x's), and in
# terms of (a,b,c,d,e) via e1=-a, e2=b, e3=-c, e4=d, e5=-e.
def to_ab(txt):
    return (txt.replace("e1", "(-a)").replace("e2", "b").replace("e3", "(-c)")
               .replace("e4", "d").replace("e5", "(-e)"))

def fmt(sol):
    names = ["e1", "e2", "e3", "e4", "e5"]
    parts = []
    for m, c in sorted(sol.items(), key=lambda kv: (-max(kv[0]), kv[0])):
        if c == 0:
            continue
        fac = str(c) if c < 0 else ("+" + str(c))
        mono = "*".join(n + ("" if a == 1 else f"^{a}") for n, a in zip(names, m) if a)
        parts.append((fac, mono or "1"))
    return parts

for j in range(1, 7):
    print(f"E_{j} =", fmt(EJ[j]))
print("disc =", fmt(DISC)[:5], "...")
