#!/usr/bin/env python3 -I
"""G1 audit for BLUEPRINT hecke-ring-gens (iteration 24, b3).

Re-derived from prodForm arithmetic (g1_audit machinery: the coefficient
rings, `basis_miller`/`basis_raw`/`op_matrix`/`matpow`/`det`/parsers); every
lattice/index/search computation below is this file's own implementation and
cross-checked against the committed probe jsons (double derivation).
Scope: the 36 weights with 5 ≤ dim S_k ≤ 10.

  A  Machinery validation + M5/M7 derivation (all 36):
      A1  M2/M3 re-derived == the LANDED Lean `M`/`M2` literals.
      A2  M5/M7 derived; row-0 anchor = (a_m(g_j))_j off the Miller rows.
      A3  Conjugation bridge Tt·Mm == Mr·Tt (m = 2,3,5,7, raw vs Miller).
      A4  |det A| == Ik (index_data.json anchor chain).
  B  Greedy table re-derivation with own index machinery; finals cross-checked
      against probe_gens.json.
  C  Certificate route measurement:
      C1 (route a) rank-tracking DFS over n-subsets of the {T₂,T₃,T₅}
         monomial rows (total degree < n, probe_gens' family), looking for
         |det| = 1; found subsets re-verified by an exact determinant.
      C2 (route b) echelon basis B + unimodular transform U of
         (i)  the {T₂,T₃} box family (a<n, b<n — the Cayley–Hamilton span,
              provably the ring ℤ[T₂,T₃]), |det| = idx3;
         (ii) the {T₂,T₃,T₅} box family at the 22 '{3,5}'-weights,
              |det| = 1 — entry digits of B and U (the certificate content).
      C3 ring-vs-lattice: [𝕋 : span(triangle a+b<n)] vs [𝕋 : span(box)]
         for {T₂,T₃} (triangle index == box index certifies the probe's
         triangle values are genuine ring indices) and the same for
         {T₂,T₃,T₅} at the '{3,5}'-weights.

Output: research/iteration24/hecke-ring-gens/g1_data.json + stdout report.
"""

import json
import sys
from pathlib import Path

sys.set_int_max_str_digits(2_000_000)  # transform coefficients can be huge

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "research" / "iteration23" / "hecke-index"))
import g1_audit as G  # noqa: E402  (prodForm arithmetic + Lean parsers)

MF = ROOT / "MathProof" / "ModularForms"
OUT = Path(__file__).resolve().parent / "g1_data.json"

T3_SMALL = MF / "MaedaT3SmallWeights.lean"
T3_DIM = {d: MF / f"MaedaT3Dim{d}Weights.lean" for d in range(6, 11)}
T2_DIM = {d: MF / f"MaedaDim{d}Weights.lean" for d in range(6, 11)}
HR_SMALL = MF / "HeckeRationalSmallWeights.lean"

PRIMES = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]  # dim·m < 516
NODE_BUDGET = 4_000_000


# --- this file's own lattice machinery -------------------------------------

def echelon(rows, n):
    """Unimodular row reduction of integer `rows`.
    (pivots, basis): basis[i] generates column pivots[i] and is frozen with
    zeros strictly left of its pivot; the basis spans the lattice of `rows`
    (only swaps and `r -= q·r'` are used).  rank = len(pivots); for rank n,
    |det basis| = ∏ basis[i][pivots[i]]."""
    M = [r[:] for r in rows]
    pivots, basis = [], []
    for col in range(n):
        piv = next((i for i in range(len(pivots), len(M)) if M[i][col] != 0),
                   None)
        if piv is None:
            continue
        M[len(pivots)], M[piv] = M[piv], M[len(pivots)]
        r0 = len(pivots)
        for i in range(r0 + 1, len(M)):
            while M[i][col] != 0:
                q = M[r0][col] // M[i][col]
                M[r0] = [a - q * b for a, b in zip(M[r0], M[i])]
                M[r0], M[i] = M[i], M[r0]
        pivots.append(col)
        basis.append(M[r0][:])
        if len(pivots) == n:
            break
    return pivots, basis


def lattice_index(rows, n):
    """[ℤ^n : L], L = lattice of `rows`; None if rank < n."""
    pivots, basis = echelon(rows, n)
    if len(pivots) < n:
        return None
    prod = 1
    for i, c in enumerate(pivots):
        prod *= basis[i][c]
    return abs(prod)


def transform(rows, n):
    """Echelon basis of L = ⟨rows⟩ with the integer transform: basis = U·rows
    (each basis row's coefficients over the ORIGINAL generators)."""
    m = len(rows)
    M = [r[:] for r in rows]
    U = [[int(i == j) for j in range(m)] for i in range(m)]
    pivots, basis, Ub = [], [], []
    for col in range(n):
        piv = next((i for i in range(len(pivots), len(M)) if M[i][col] != 0),
                   None)
        if piv is None:
            continue
        M[len(pivots)], M[piv] = M[piv], M[len(pivots)]
        U[len(pivots)], U[piv] = U[piv], U[len(pivots)]
        r0 = len(pivots)
        for i in range(r0 + 1, len(M)):
            while M[i][col] != 0:
                q = M[r0][col] // M[i][col]
                M[r0] = [a - q * b for a, b in zip(M[r0], M[i])]
                U[r0] = [a - q * b for a, b in zip(U[r0], U[i])]
                M[r0], M[i] = M[i], M[r0]
                U[r0], U[i] = U[i], U[r0]
        pivots.append(col)
        basis.append(M[r0][:])
        Ub.append(U[r0][:])
        if len(pivots) == n:
            break
    return pivots, basis, Ub


def monomial_rows(Mpows, n, gens, mode):
    """Miller rows of the monomials T₂^a ∏_m T_m^{b_m}:
    mode 'triangle': a + Σb < n (probe_gens' family, degree-0 = 1 included);
    mode 'box':      a < n, b_m < n (the Cayley–Hamilton span of the ring).
    Returns (rows, labels); labels are (a, (b_m...)) with gens sorted."""
    S = sorted(gens)
    rows, labels = [], []
    mem = {}

    def Xof(bs):
        key = tuple(bs)
        if key not in mem:
            M = [[int(i == j) for j in range(n)] for i in range(n)]
            for m, b in zip(S, bs):
                for _ in range(b):
                    M = G.matmul(M, gens[m])
            mem[key] = M
        return mem[key]

    if mode == "triangle":
        def rec(idx, rem, cur):
            if idx == len(S):
                yield cur[:]
                return
            for b in range(rem + 1):
                cur.append(b)
                yield from rec(idx + 1, rem - b, cur)
                cur.pop()
        for bs in rec(0, n - 1, []):  # Σb ≤ n-1
            X = Xof(bs)
            for a in range(n - sum(bs)):  # a + Σb < n
                rows.append(G.matmul(Mpows[a], X)[0][:])
                labels.append((a, tuple(bs)))
    elif mode == "box":
        def rec(idx, cur):
            if idx == len(S):
                yield cur[:]
                return
            for b in range(n):
                cur.append(b)
                yield from rec(idx + 1, cur)
                cur.pop()
        for bs in rec(0, []):  # each b_m < n
            X = Xof(bs)
            for a in range(n):
                rows.append(G.matmul(Mpows[a], X)[0][:])
                labels.append((a, tuple(bs)))
    else:
        raise ValueError(mode)
    return rows, labels


# --- route (a): rank-tracking subset search --------------------------------

def add_row_inc(basis, r):
    """Add row r to an echelon basis [(pc, row)...] (rows frozen, zeros left
    of pivots).  Returns the new basis iff the rank grows, else None.
    Unimodular 2×2 ops only, so the spanned lattice is preserved."""
    r = r[:]
    out = []
    for pc, br in basis:
        if r[pc] == 0:
            out.append((pc, br))
            continue
        a, b = br[:], r
        # Euclid on the pc-entries: (a[pc], b[pc]) → (b[pc], a[pc] mod b[pc]);
        # exits with a[pc] = gcd ≠ 0, b[pc] = 0 (b = the reduced remainder)
        while b[pc] != 0:
            q = a[pc] // b[pc]
            a, b = b, [x - q * y for x, y in zip(a, b)]
        out.append((pc, a))
        r = b
    pc = next((c for c in range(len(r)) if r[c] != 0), None)
    if pc is None:
        return None
    out.append((pc, r))
    out.sort(key=lambda t: t[0])
    return out


def search_unimodular(rows, labels, n, budget=NODE_BUDGET, key=None):
    """DFS over n-subsets of `rows` (rank-tracking echelon, prune when the
    rank does not grow).  `key` overrides the visit order (default: label
    order = exhaustive claim within budget; `key='entry'` orders by max
    |entry| — a heuristic that finds promising subsets fast but makes
    `found=False` weaker).  Returns (found, labels_subset, nodes).  Found
    subsets re-verified by an exact determinant at the end."""
    if key == "entry":
        order = sorted(range(len(rows)),
                       key=lambda i: (max(abs(x) for x in rows[i]), labels[i]))
    else:
        order = sorted(range(len(rows)), key=lambda i: labels[i])
    state = {"nodes": 0}

    def dfs(start, basis, cur):
        if len(basis) == n:
            prod = 1
            for pc, br in basis:
                prod *= br[pc]
            if abs(prod) == 1:
                return [labels[i] for i in cur]
            return None
        for pos in range(start, len(order) - (n - len(basis)) + 1):
            state["nodes"] += 1
            if state["nodes"] > budget:
                return None
            i = order[pos]
            nb = add_row_inc(basis, rows[i])
            if nb is None:
                continue
            cur.append(i)
            got = dfs(pos + 1, nb, cur)
            if got is not None:
                return got
            cur.pop()
        return None

    cur = []
    got = dfs(0, [], cur)
    if got is not None:
        sel = [rows[labels.index(l)] for l in got]
        assert abs(G.det(sel)) == 1, "search subset failed exact det check"
        assert lattice_index(sel, n) == 1
    return got is not None, got, state["nodes"]


def _selftest():
    """Positive controls for `add_row_inc` / `search_unimodular`."""
    # Euclid on a concrete column: reduce (1,0) against pivot (2,1)
    b = add_row_inc([(0, [2, 1])], [1, 0])
    assert b is not None
    assert sorted(pc for pc, _ in b) == [0, 1]
    for pc, br in b:
        assert all(x == 0 for x in br[:pc]), "pivot row not echelon"
    # identity rows are a unimodular subset
    found, _, _ = search_unimodular([[1, 0], [0, 1], [5, 3]],
                                     [(0,), (1,), (2,)], 2, budget=1000)
    assert found, "selftest: unimodular subset not found"
    # det-1 pair with non-obvious entries: {(2,1),(1,1)}
    found, _, _ = search_unimodular([[2, 1], [1, 1]], [(0,), (1,)], 2,
                                     budget=1000)
    assert found, "selftest: det-1 pair not found"
    # non-unimodular: {(2,0),(0,2)} — exhaustive, must not find
    found, _, nodes = search_unimodular([[2, 0], [0, 2]], [(0,), (1,)], 2,
                                         budget=1000)
    assert not found, "selftest: false positive"
    # the two 3x3 families {I + junk} vs {2I}
    found, _, _ = search_unimodular([[1, 0, 0], [0, 1, 0], [0, 0, 1],
                                     [3, 5, 7]], [(0,), (1,), (2,), (3,)], 3,
                                    budget=10000)
    assert found, "selftest: 3x3 identity subset not found"
    found, _, _ = search_unimodular([[2, 0, 0], [0, 2, 0], [0, 0, 2]],
                                    [(0,), (1,), (2,)], 3, budget=10000)
    assert not found, "selftest: 2I false positive"
    return True


# ---------------------------------------------------------------------------

def solve_int(R, b):
    """Integer solution c of R·c = b (R n×n integer, det ≠ 0), via Cramer
    (exact; caller verifies).  Returns None if not integral."""
    n = len(R)
    dR = G.det(R)
    if dR == 0:
        return None
    c = []
    for l in range(n):
        R2 = [row[:] for row in R]
        R2[l] = b[:]
        c.append(G.det(R2) // dR)
    # verify
    acc = [sum(c[i] * R[i][j] for i in range(n)) for j in range(n)]
    if acc != b:
        return None
    return c


def cert_measure(k, ref, report):
    """Route (a) certificate measurement at one '{3,5}'-weight: search
    degree-capped monomial pools for a unimodular n-subset, then solve
    T₇ = ∑ c·monomial exactly and report digit sizes."""
    n = ref[str(k)]["dim"]
    mrows = G.basis_miller(k, n)
    M2m = G.op_matrix(k, 2, mrows)
    M3m = G.op_matrix(k, 3, mrows)
    M5m = G.op_matrix(k, 5, mrows)
    Mpows = [G.matpow(M2m, a) for a in range(n)]
    gens = {3: M3m, 5: M5m}
    rowT7 = [mrows[j][7] for j in range(n)]
    res = {"dim": n}
    for D in range(2, min(6, n)):
        rows, labels = monomial_rows_degree(Mpows, n, gens, D)
        # phase 1: entry-ordered quick search (finds promising subsets fast)
        found, sub, nodes = search_unimodular(rows, labels, n, budget=2_000_000,
                                              key="entry")
        how = "quick"
        if not found:
            # phase 2: label-ordered exhaustive within the pool (the
            # found=False claim is pool-exhaustive iff nodes < budget)
            found, sub, nodes = search_unimodular(rows, labels, n,
                                                  budget=20_000_000)
            how = "exhaustive"
        res[f"pool_D{D}"] = {"nmon": len(rows), "found": found,
                             "nodes": nodes, "how": how,
                             "subset": [list(s) for s in sub] if sub else None}
        if found:
            sel = [rows[labels.index(tuple(s))] for s in sub]
            c = solve_int(sel, rowT7)
            assert c is not None, f"w{k}: T₇ row not in subset lattice?!"
            digits = [len(str(abs(x))) for x in c]
            rdigits = max(len(str(abs(x))) for r in sel for x in r)
            res["cert"] = {"family": [list(s) for s in sub], "c": c,
                           "c_digits": max(digits), "R_digits": rdigits,
                           "pool_D": D, "how": how}
            report.append(
                f"w{k:3d} dim {n}: D={D} ({len(rows)} mon, {how}, "
                f"nodes={nodes}) c_digits={max(digits)} R_digits={rdigits} "
                f"family={[s for s in sub]}")
            return res
        report.append(f"w{k:3d} dim {n}: D={D} ({len(rows)} mon) "
                      f"not found ({how}, nodes={nodes})")
    res["cert"] = None
    return res


def monomial_rows_degree(Mpows, n, gens, D):
    """Miller rows of the monomials T₂^a ∏ T_m^{b_m} of total degree ≤ D
    (including degree 0 = 1)."""
    S = sorted(gens)
    rows, labels = [], []
    mem = {}

    def Xof(bs):
        key = tuple(bs)
        if key not in mem:
            M = [[int(i == j) for j in range(n)] for i in range(n)]
            for m, b in zip(S, bs):
                for _ in range(b):
                    M = G.matmul(M, gens[m])
            mem[key] = M
        return mem[key]

    def rec(idx, rem, cur):
        if idx == len(S):
            yield cur[:]
            return
        for b in range(rem + 1):
            cur.append(b)
            yield from rec(idx + 1, rem - b, cur)
            cur.pop()

    for bs in rec(0, D, []):
        X = Xof(bs)
        for a in range(D - sum(bs) + 1):
            rows.append(G.matmul(Mpows[a], X)[0][:])
            labels.append((a, tuple(bs)))
    return rows, labels


def main():
    _selftest()
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    ref = json.load(open(ROOT / "research" / "iteration23" / "hecke-index"
                         / "index_data.json"))
    pgens = json.load(open(ROOT / "research" / "iteration24" / "probe_gens.json"))

    t3, small = {}, set()
    for f in [T3_SMALL] + list(T3_DIM.values()):
        for ns, sec in G.namespaces(f).items():
            t3[G.weight_of(ns)] = sec
            if f is T3_SMALL:
                small.add(G.weight_of(ns))
    t2dim, hr_small = {}, {}
    for d, f in T2_DIM.items():
        for ns, sec in G.namespaces(f).items():
            t2dim[G.weight_of(ns)] = sec
    for ns, sec in G.namespaces(HR_SMALL).items():
        hr_small[G.hr_weight_of(ns)] = sec

    fail, report, data = [], [], {}
    W35 = []

    def check(cond, msg):
        if not cond:
            fail.append(msg)
        return cond

    def digs(mat):
        return max(len(str(abs(x))) for r in mat for x in r)

    weights = sorted(int(k) for k in pgens)
    assert len(weights) == 36
    for k in weights:
        if which not in ("all", f"w{k}"):
            continue
        n = ref[str(k)]["dim"]
        Ik, Dred = ref[str(k)]["Ik"], ref[str(k)]["Dred"]
        mrows = G.basis_miller(k, n)
        rrows = G.basis_raw(k, n)
        M2m = G.op_matrix(k, 2, mrows)
        M3m = G.op_matrix(k, 3, mrows)
        M5m = G.op_matrix(k, 5, mrows)
        M7m = G.op_matrix(k, 7, mrows)

        # A1  (the Lean M/M2 literals are the RAW-basis coordinate matrices —
        # g1_audit check C2)
        M3lean = G.parse_M(t3[k])
        M2lean = G.parse_M2(hr_small[k]) if k in small else G.parse_M(t2dim[k])
        M2r, M3r = G.op_matrix(k, 2, rrows), G.op_matrix(k, 3, rrows)
        check(M2r == M2lean, f"w{k}: A1 M2 != Lean literal")
        check(M3r == M3lean, f"w{k}: A1 M3 != Lean literal")

        # A2
        for m, Mm in ((2, M2m), (3, M3m), (5, M5m), (7, M7m)):
            check(Mm[0] == [mrows[j][m] for j in range(n)],
                  f"w{k}: A2 row0 of M{m} != (a_{m}(g_j))_j")

        # A3
        Tmat = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(i, n):
                v = int(i == j)
                for t in range(i, j):
                    v -= Tmat[i][t] * rrows[t][j + 1]
                Tmat[i][j] = v
        Tt = [[Tmat[j][i] for j in range(n)] for i in range(n)]
        for m in (2, 3, 5, 7):
            Mmm = G.op_matrix(k, m, mrows)
            Mmr = G.op_matrix(k, m, rrows)
            check(G.matmul(Tt, Mmm) == G.matmul(Mmr, Tt),
                  f"w{k}: A3 conjugation bridge M{m}")

        # A4
        A = [[mrows[j][2 ** i] for j in range(n)] for i in range(n)]
        check(abs(G.det(A)) == Ik, f"w{k}: A4 |det A| != Ik")

        # B: greedy re-derivation (probe rule: smallest prime lowering most)
        Mpows = [G.matpow(M2m, a) for a in range(n)]
        base_rows = [Mpows[a][0][:] for a in range(n)]
        i2 = lattice_index(base_rows, n)
        check(i2 == Ik, f"w{k}: B [𝕋:ℤ[T₂]] = {i2} != Ik")

        def idx_tri(S):
            gens = {m: G.op_matrix(k, m, mrows) for m in S}
            rows, _ = monomial_rows(Mpows, n, gens, "triangle")
            return lattice_index(rows, n)

        S, cur = [], i2
        chain = []
        while cur != 1:
            best = None
            for p in PRIMES:
                if p in S:
                    continue
                ix = idx_tri(S + [p])
                if ix is not None and ix < cur and (best is None or ix < best[1]):
                    best = (p, ix)
            if best is None:
                chain.append((S + ["<none>"], None))
                break
            S = S + [best[0]]
            cur = best[1]
            chain.append((list(S), cur))
        final = S if cur == 1 else None
        check(final is not None, f"w{k}: B greedy stuck at {S}")
        probe_final = [int(x) for x in pgens[str(k)]["greedy"][-1][0]]
        if final is not None:
            check(final == probe_final,
                  f"w{k}: B greedy final {final} != probe {probe_final}")

        # C2 (i): {2,3} box family — basis + transform
        gens23 = {3: M3m}
        rows23b, labels23b = monomial_rows(Mpows, n, gens23, "box")
        piv23, B23, U23 = transform(rows23b, n)
        idx3_box = lattice_index(rows23b, n)
        tri3 = next((ix for s, ix in pgens[str(k)]["greedy"]
                     if [int(x) for x in s] == [3]), None)
        check(idx3_box == tri3,
              f"w{k}: C2 idx3(box) {idx3_box} != probe triangle {tri3}")

        # C3: triangle vs box, {2,3}
        rows23t, _ = monomial_rows(Mpows, n, gens23, "triangle")
        idx3_tri = lattice_index(rows23t, n)
        check(idx3_tri == idx3_box,
              f"w{k}: C3 idx3 triangle {idx3_tri} != box {idx3_box}")

        ent = {"idx3": idx3_box, "B23_digits": digs(B23), "U23_digits": digs(U23),
               "U23_nz": sum(1 for r in U23 for x in r if x),
               "greedy_final": final}
        if k == 60:
            ent["B23"] = B23
            ent["U23"] = U23
            ent["labels23_box"] = [list(l) for l in labels23b]

        # C2 (ii) + C3 at the '{3,5}'-weights
        if final == [3, 5]:
            W35.append(k)
            gens235 = {3: M3m, 5: M5m}
            rows235b, labels235b = monomial_rows(Mpows, n, gens235, "box")
            piv235, B235, U235 = transform(rows235b, n)
            idx235_box = lattice_index(rows235b, n)
            check(idx235_box == 1, f"w{k}: C2 idx(2,3,5 box) {idx235_box} != 1")
            rows235t, _ = monomial_rows(Mpows, n, gens235, "triangle")
            idx235_tri = lattice_index(rows235t, n)
            check(idx235_tri == 1, f"w{k}: C3 idx(2,3,5 tri) {idx235_tri} != 1")
            ent.update({"B235_digits": digs(B235), "U235_digits": digs(U235),
                        "U235_nz": sum(1 for r in U235 for x in r if x)})
            if k == 60:
                ent["B235"] = B235
                ent["U235"] = U235
                ent["labels235_box"] = [list(l) for l in labels235b]
                ent["rows235_box"] = rows235b
                ent["rows23_box"] = rows23b
            if k == 60:
                ent["labels235_box"] = [list(l) for l in labels235b]
                ent["rows235_box"] = rows235b
                ent["rows23_box"] = rows23b

        data[k] = {"dim": n, "Ik": Ik, "Dred": Dred, "entries": ent}
        report.append(
            f"w{k:3d} dim {n:2d}: greedy={final} idx3={idx3_box} "
            f"B23 {ent['B23_digits']:3d}d U23 {ent['U23_digits']:3d}d "
            + (f"B235 {ent['B235_digits']:3d}d U235 {ent['U235_digits']:3d}d"
               if final == [3, 5] else ""))
        print(report[-1], flush=True)

    print("\n".join(report))
    print(f"\n{{3,5}}-weights: {len(W35)}  (expect 22)")

    # C1 route (a) is superseded by `cert` mode (degree-capped pools +
    # T₇-coefficient solve — see cert_measure); keep the legacy single-weight
    # search only for explicit `wKK` runs.
    if which.startswith("w") and which[1:].isdigit():
        k = int(which[1:])
        n = ref[str(k)]["dim"]
        mrows = G.basis_miller(k, n)
        M2m = G.op_matrix(k, 2, mrows)
        Mpows = [G.matpow(M2m, a) for a in range(n)]
        gens = {3: G.op_matrix(k, 3, mrows), 5: G.op_matrix(k, 5, mrows)}
        rows, labels = monomial_rows(Mpows, n, gens, "triangle")
        found, sub, nodes = search_unimodular(rows, labels, n)
        print(f"C1 w{k} triangle (dim {n}, {len(rows)} monomials): "
              f"found={found} nodes={nodes} subset={sub}", flush=True)
        data[k]["entries"]["routeA"] = {
            "found": found, "subset": [list(s) for s in sub] if sub else None,
            "nodes": nodes, "nmon": len(rows)}

    if which == "cert":
        W35 = sorted(int(k) for k, v in pgens.items()
                     if [int(x) for x in v["greedy"][-1][0]] == [3, 5])
        certs = {}
        for k in W35:
            certs[k] = cert_measure(k, ref, report)
            print(report[-1], flush=True)
            OUT2 = Path(__file__).resolve().parent / "t7_certs.json"
            OUT2.write_text(json.dumps(certs, indent=1))
        nfound = sum(1 for v in certs.values() if v.get("cert"))
        print(f"\ncert route found at {nfound}/{len(certs)} '{{3,5}}'-weights")

    OUT.write_text(json.dumps(data, indent=1))
    print(f"\nfailures: {len(fail)}")
    for f_ in fail[:30]:
        print("  " + f_)
    if fail:
        sys.exit(1)
    print("G1 AUDIT OK; data written to", OUT)


if __name__ == "__main__":
    main()
