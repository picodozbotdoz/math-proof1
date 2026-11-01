#!/usr/bin/env python3 -I
"""G1 data audit for BLUEPRINT hecke-rational (iteration 22).

Ground truth = the Lean literals in the generated weight files.  This script:

  1. enumerates the 54 weights (2 <= dim S_k <= 10) with their T2/T3 sources;
  2. parses M3 (T3 matrix) for all 54 weights from the Lean files and
     cross-checks against the iteration-20/22 census JSONs;
  3. parses M2 (T2 matrix) for dims 6-10 from the Lean files, cross-checks
     against the census, and verifies the T2/T3 sections are syntactically
     aligned (f-defs / fb / Atab) so the defeq bridge in the generated file
     is sound;
  4. RE-DERIVES M2 for the 24 small weights from coefficient data: the T3
     file's basis q-lemma values + the heckeT2_coeff formula
        (T2 f)_m = f_{2m} + 2^(k-1) [2|m] f_{m/2}
     followed by the coordN triangular back-substitution under the T3 file's
     Atab; cross-checks against the T2 files' t-lemma values (dims 2-5), the
     T2 files' charpoly literals `P` (all 24), and the weight-24 literal
     toMatrix_heckeT2 = [[696,1],[20736000,384]];
  5. asserts [M2, M3] = 0 and charpoly(M3) = P3- literal per weight;
  6. solves  sum_j q_j M2^j = M3  exactly over Q (Gaussian elimination on
     the n^2 x n system), asserts exactness + uniqueness, and reports the
     certificate magnitudes (N_j = D q_j, common denominator D).

Output: research/iteration22/hecke-rational/g1_data.json + stdout report.
"""

import json
import re
import sys
from fractions import Fraction
from math import gcd, lcm
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
MF = ROOT / "MathProof" / "ModularForms"
OUT = Path(__file__).resolve().parent / "g1_data.json"

# --------------------------------------------------------------------------
# census of the 54 weights: (weight, dim, T2 source, T3 namespace)


def namespaces(path):
    """Split a Lean file into {namespace: section text}."""
    text = path.read_text()
    parts = re.split(r"^namespace (\w+)$", text, flags=re.M)
    out = {}
    for i in range(1, len(parts), 2):
        out[parts[i]] = parts[i + 1]
    return out


T3_FILES = [MF / "MaedaT3SmallWeights.lean"] + [
    MF / f"MaedaT3Dim{d}Weights.lean" for d in range(6, 11)
]
T2_DIM_FILES = {d: MF / f"MaedaDim{d}Weights.lean" for d in range(6, 11)}
T2_SMALL_FILES = [
    MF / "MaedaSmallWeights.lean",
    MF / "MaedaDim4Weights.lean",
    MF / "MaedaDim5Weights.lean",
]


def weight_of(ns):
    m = re.fullmatch(r"Maeda(?:T3)?Weight(\d+)", ns)
    assert m, ns
    return int(m.group(1))


# --------------------------------------------------------------------------
# Lean literal parsers


def parse_M(section):
    """`def M : Matrix (Fin n) (Fin n) ℤ := !![a, b; c, d]` -> list of rows."""
    m = re.search(r"def M : Matrix \(Fin (\d+)\) \(Fin (\d+)\) ℤ :=\s*!!\[", section)
    assert m, "no M literal"
    n = int(m.group(1))
    start = m.end()
    depth, i = 1, start
    while depth:
        c = section[i]
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
        i += 1
    body = section[start : i - 1]
    rows = [r.strip() for r in body.split(";")]
    assert len(rows) == n, (len(rows), n)
    mat = []
    for r in rows:
        entries = [int(t.strip()) for t in r.split(",")]
        assert len(entries) == n
        mat.append(entries)
    return mat


def parse_Atab(section):
    """`def Atab ... | i, j => (V : ℂ) ... | _, _ => 0` -> {(i,j): V}."""
    m = re.search(r"def Atab : ℕ → ℕ → ℂ(.*?)\n\n", section, flags=re.S)
    assert m, "no Atab"
    out = {}
    for i, j, v in re.findall(r"\| (\d+), (\d+) => \((-?\d+) : ℂ\)", m.group(1)):
        out[(int(i), int(j))] = int(v)
    assert "| _, _ => 0" in m.group(1)
    return out


def parse_value_lemmas(section, kind):
    """t/q coefficient lemmas: name -> value.

    t: `lemma t{i}_{m} : (qExpansion 1 (T2 f{i})).coeff {m} = (V : ℂ)`
    q: `lemma q{i}_{m} : (qExpansion 1 f{i}).coeff {m} = (V : ℂ)`
    """
    out = {}
    if kind == "t":
        pat = re.compile(
            r"lemma t(\d+)_(\d+) : \(qExpansion 1 \((?:T2|T3) f\1\)\)\.coeff \2 "
            r"= \((-?\d+) : ℂ\)"
        )
    else:
        pat = re.compile(
            r"lemma q(\d+)_(\d+) : \(qExpansion 1 f\1\)\.coeff \2 = \((-?\d+) : ℂ\)"
        )
    for i, m_, v in pat.findall(section):
        key = (int(i), int(m_))
        assert key not in out, key
        out[key] = int(v)
    return out


def parse_P(section):
    """`noncomputable def P : ℤ[X] := ...` -> ascending coefficient list.

    Handles both emitted shapes: `C (v) * (X : ℤ[X]) ^ d`, bare `X ^ d`,
    `* X` (degree 1), trailing `C (v)`, unary `-` before `C`, and chunked
    C-contents `a * 10 ^ e + b` (no parens inside the C group).
    """

    def numexpr(txt):
        tot = 0
        for tok in re.finditer(r"(-?\d+)(?: \* 10 \^ (\d+))?", txt):
            v = int(tok.group(1))
            if tok.group(2):
                v *= 10 ** int(tok.group(2))
            tot += v
        return tot

    m = re.search(r"noncomputable def P : ℤ\[X\] :=\s*(.*?)\n\n", section, flags=re.S)
    assert m, "no P literal"
    expr = re.sub(r"\s+", " ", m.group(1)).strip()
    vals = []

    def repl(mm):
        vals.append(mm.group(1))
        return f"C<{len(vals) - 1}>"

    expr = re.sub(r"C \(([^()]*)\)", repl, expr)
    coeffs = {}
    for piece in expr.split(" + "):
        piece = piece.strip()
        neg = piece.startswith("-")
        piece = piece[1:].strip() if neg else piece
        sgn = -1 if neg else 1
        mC = re.fullmatch(r"C<(\d+)>(?: \* \(?X(?: : ℤ\[X\])?\)?(?: \^ (\d+))?)?", piece)
        if mC:
            v = numexpr(vals[int(mC.group(1))])
            if " * " in piece:
                d = int(mC.group(2)) if mC.group(2) else 1
            else:
                d = 0
        else:
            mX = re.fullmatch(r"\(?X(?:: ℤ\[X\])?\)?(?: \^ (\d+))?", piece)
            assert mX, f"unparseable P term: {piece!r}"
            v, d = 1, (int(mX.group(1)) if mX.group(1) else 1)
        coeffs[d] = coeffs.get(d, 0) + sgn * v
    deg = max(coeffs)
    return [coeffs.get(i, 0) for i in range(deg + 1)]


def def_bodies(section):
    """`name -> body text` for noncomputable def/def declarations."""
    out = {}
    for m in re.finditer(
        r"(?:noncomputable )?def (\w+)[^\n]*?:=\s*(.*?)(?=\n\n|\n(?:lemma|theorem|def|noncomputable))",
        section,
        flags=re.S,
    ):
        out[m.group(1)] = re.sub(r"\s+", " ", m.group(2)).strip()
    return out


# --------------------------------------------------------------------------
# exact linear algebra over Z / Q


def mat_mul(A, B):
    n = len(A)
    return [
        [sum(A[i][t] * B[t][j] for t in range(n)) for j in range(n)] for i in range(n)
    ]


def mat_pow(A, e):
    n = len(A)
    R = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    while e:
        if e & 1:
            R = mat_mul(R, A)
        A = mat_mul(A, A)
        e >>= 1
    return R


def charpoly(A):
    """Exact charpoly (ascending coeffs of det(xI - A)) via Faddeev-LeVerrier."""
    n = len(A)
    Af = [[Fraction(x) for x in row] for row in A]
    M = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    coeff = [Fraction(1)]
    for k in range(1, n + 1):
        AM = mat_mul(Af, M)
        c = -sum(AM[i][i] for i in range(n)) / k
        coeff.append(c)
        M = [[AM[i][j] + (c if i == j else 0) for j in range(n)] for i in range(n)]
    ints = []
    for c in coeff:
        assert c.denominator == 1, c
        ints.append(int(c))
    return ints[::-1]  # FL yields descending; flip to ascending


def solve_Q(M2, M3):
    """Unique rational q with sum_j q_j M2^j = M3 (n^2 x n exact elimination)."""
    n = len(M2)
    powers = [mat_pow(M2, j) for j in range(n)]
    rows = []
    for r in range(n):
        for c in range(n):
            rows.append([Fraction(powers[j][r][c]) for j in range(n)]
                        + [Fraction(M3[r][c])])
    # Gaussian elimination
    rank = 0
    piv_cols = []
    for col in range(n):
        piv = next((i for i in range(rank, len(rows)) if rows[i][col] != 0), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        pv = rows[rank][col]
        rows[rank] = [x / pv for x in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[rank])]
        piv_cols.append(col)
        rank += 1
        if rank == n:
            break
    assert rank == n, "system not of full rank (I, M2, .. not independent)"
    for row in rows[n:]:
        assert all(x == 0 for x in row[:n]) and row[n] == 0, "inconsistent system"
    q = [Fraction(0)] * n
    for i, col in enumerate(piv_cols):
        q[col] = rows[i][n]
    # exact verification
    for r in range(n):
        for c in range(n):
            assert sum(q[j] * powers[j][r][c] for j in range(n)) == M3[r][c]
    return q


def norm_certificate(q):
    n = len(q)
    D = 1
    for x in q:
        D = lcm(D, x.denominator)
    N = [int(x * D) for x in q]
    g = 0
    for x in N:
        g = gcd(g, abs(x))
    g = gcd(g, D)
    if g > 1:
        N = [x // g for x in N]
        D //= g
    return N, D


# --------------------------------------------------------------------------
# main

def main():
    t3_secs = {}
    small = set()
    for f in T3_FILES:
        for ns, sec in namespaces(f).items():
            t3_secs[weight_of(ns)] = (ns, sec)
            if f.name == "MaedaT3SmallWeights.lean":
                small.add(weight_of(ns))
    assert len(small) == 24, len(small)
    t2_secs = {}
    for d, f in T2_DIM_FILES.items():
        for ns, sec in namespaces(f).items():
            t2_secs[weight_of(ns)] = (ns, sec)
    for f in T2_SMALL_FILES:
        for ns, sec in namespaces(f).items():
            t2_secs[weight_of(ns)] = (ns, sec)

    weights = sorted(t3_secs)
    assert len(weights) == 54, len(weights)

    census = {}
    for name in ["maeda_dim6_10", "maeda_t3_dim6_10", "maeda_t3_small"]:
        with open(ROOT / "research/iteration20/data" / f"{name}.json") as fh:
            for e in json.load(fh):
                census[(name, e["k"])] = e

    report = []
    data = {}
    fail = []

    def check(cond, msg):
        if not cond:
            fail.append(msg)
            report.append(f"  FAIL: {msg}")

    for k in weights:
        ns3, sec3 = t3_secs[k]
        n = len(parse_M(sec3))
        M3 = parse_M(sec3)
        q3 = parse_value_lemmas(sec3, "q")
        atab = parse_Atab(sec3)
        P3 = parse_P(sec3)

        # census cross-check (M3)
        cen = census.get(("maeda_t3_small", k)) or census.get(("maeda_t3_dim6_10", k))
        check(cen is not None, f"w{k}: no T3 census entry")
        check(cen["dim"] == n and cen["matrix"] == M3, f"w{k}: M3 != census")
        check(charpoly(M3) == P3, f"w{k}: charpoly(M3) != P3 literal")

        # echelon sanity on Atab vs q-lemmas
        for (i, j), v in atab.items():
            check(q3.get((i + 1, j + 1)) == v, f"w{k}: Atab {i},{j} != q{i+1}_{j+1}")

        entry = {"k": k, "dim": n, "ns3": ns3,
                 "Atab": {f"{a},{b}": v for (a, b), v in atab.items()},
                 "M3": M3, "q": {f"{a}_{b}": v for (a, b), v in q3.items()}}

        if k not in small:
            # dims 6-10: parse M2 from the T2 dim file + alignment audit
            ns2, sec2 = t2_secs[k]
            M2 = parse_M(sec2)
            entry["ns2"] = ns2
            entry["M2"] = M2
            cen2 = census.get(("maeda_dim6_10", k))
            check(cen2 is not None and cen2["matrix"] == M2, f"w{k}: M2 != census")

            # alignment: f-defs, fb, Atab bodies must coincide textually
            b2, b3 = def_bodies(sec2), def_bodies(sec3)
            for nm in ["fb", "Atab"]:
                check(b2.get(nm) == b3.get(nm), f"w{k}: {nm} body differs T2/T3")
            fdefs2 = {n_: b for n_, b in b2.items() if re.fullmatch(r"f\d+", n_)}
            fdefs3 = {n_: b for n_, b in b3.items() if re.fullmatch(r"f\d+", n_)}
            check(set(fdefs2) == set(fdefs3), f"w{k}: f-def names differ")
            for n_ in fdefs2:
                check(fdefs2[n_] == fdefs3[n_], f"w{k}: {n_} body differs T2/T3")
            t2v = parse_value_lemmas(sec2, "t")
            entry["t2"] = {f"{a}_{b}": v for (a, b), v in t2v.items()}
        else:
            # small weight: RE-DERIVE M2 from q-lemma values + heckeT2_coeff
            # (T2 f)_m = f_{2m} + 2^{k-1} [2|m] f_{m/2};  Xtab2 i m = value at
            # m+1;  coordN back-substitution under atab.
            def fcoeff(i, m):  # coeff q^m of f_{i+1} (0-indexed i)
                return q3.get((i + 1, m), 0)

            X2 = {}
            for i in range(n):
                for m in range(n):  # Xtab2 i m = coeff (m+1)
                    mm = m + 1
                    v = fcoeff(i, 2 * mm)
                    if mm % 2 == 0:
                        v += (1 << (k - 1)) * fcoeff(i, mm // 2)
                    X2[(i, m)] = v
            # coordN: gamma_j solves gamma_j + sum_{i<j} Atab[i][j] gamma_i =
            # X2[i-th image][j]
            M2 = [[0] * n for _ in range(n)]
            for i in range(n):
                gamma = [0] * n
                for j in range(n):
                    v = X2[(i, j)]
                    for t in range(j):
                        v -= atab.get((t, j), 0) * gamma[t]
                    gamma[j] = v
                for j in range(n):
                    M2[j][i] = gamma[j]
            entry["M2"] = M2
            entry["ns2"] = t2_secs[k][0] if k in t2_secs else "MaedaWeight24"

            # cross-check 1: T2 file t-lemma values (dims 2-5)
            if k in t2_secs:
                t2v = parse_value_lemmas(t2_secs[k][1], "t")
                for (ti, tm), v in t2v.items():
                    check(X2.get((ti - 1, tm - 1)) == v,
                          f"w{k}: derived X2[{ti-1},{tm-1}]={X2.get((ti-1,tm-1))} "
                          f"!= t{ti}_{tm}={v}")
                P2 = parse_P(t2_secs[k][1])
                check(charpoly(M2) == P2, f"w{k}: charpoly(M2) != T2-file P")
            else:
                check(k == 24 and M2 == [[696, 1], [20736000, 384]],
                      f"w{k}: M2 != weight-24 toMatrix literal: {M2}")

        # commutation + Q-solve
        C = [[sum(M2[i][t] * M3[t][j] - M3[i][t] * M2[t][j] for t in range(n))
              for j in range(n)] for i in range(n)]
        check(all(x == 0 for r in C for x in r), f"w{k}: [M2,M3] != 0")
        q = solve_Q(M2, M3)
        N, D = norm_certificate(q)
        check(D != 0, f"w{k}: D = 0")
        lhs = [[0] * n for _ in range(n)]
        for j, Nj in enumerate(N):
            Pj = mat_pow(M2, j)
            for r in range(n):
                for c in range(n):
                    lhs[r][c] += Nj * Pj[r][c]
        for r in range(n):
            for c in range(n):
                check(lhs[r][c] == D * M3[r][c], f"w{k}: scaled identity cell {r},{c}")
        maxN = max(abs(x) for x in N)
        maxL = max(abs(x) for r in lhs for x in r)
        entry["N"] = N
        entry["D"] = D
        entry["stats"] = {
            "maxN_digits": len(str(maxN)),
            "D_digits": len(str(abs(D))),
            "max_idcell_digits": len(str(maxL)),
            "M2_max_digits": max(len(str(abs(x))) for r in M2 for x in r),
            "M3_max_digits": max(len(str(abs(x))) for r in M3 for x in r),
        }
        data[k] = entry
        s = entry["stats"]
        report.append(
            f"w{k:3d} dim {n:2d}: M2max {s['M2_max_digits']:3d}d  M3max "
            f"{s['M3_max_digits']:3d}d  Nmax {s['maxN_digits']:3d}d  D "
            f"{s['D_digits']:3d}d  idcell {s['max_idcell_digits']:3d}d"
        )

    OUT.write_text(json.dumps(data, indent=1))
    print("\n".join(report))
    print(f"\n{len(weights)} weights, failures: {len(fail)}")
    for f_ in fail[:30]:
        print("  " + f_)
    if fail:
        sys.exit(1)
    print("ALL CHECKS PASSED; data written to", OUT)


if __name__ == "__main__":
    main()
