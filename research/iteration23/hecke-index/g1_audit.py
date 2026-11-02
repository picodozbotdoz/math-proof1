#!/usr/bin/env python3 -I
"""G1 data audit for BLUEPRINT hecke-index (iteration 23, b2).

Ground truth = the Lean literals in the generated weight files.  This script
re-pins the Hecke-index data (Tmat, A, C, I_k, w') to those literals directly
(no g1_data.json intermediary) and re-derives everything from prodForm
arithmetic.  Per weight k (dim n):

  C1  fb re-pin: the Lean `Atab`/`q{i}_{m}` literals of the T3 dim file equal
      the coefficients of the raw prodForm basis rows (fb = raw basis).
  C2  M2/M3 re-pin: the coordinate matrices of T2/T3 in the fb basis
      (unit-diagonal lower-triangular solve) equal the Lean `M` literals:
      dims 6-10 from MaedaDim{d}/MaedaT3Dim{d}Weights, dims 2-5 with M3 from
      MaedaT3SmallWeights and M2 from HeckeRationalSmallWeights (itself
      kernel-pinned by entryT2 lemmas in Lean).
  C3  Miller: normalization a_i(f_j) = delta_ij; the raw->Miller transition
      Tmat is integer upper-unitriangular with |det| = 1; conjugation bridge
      Tmat^T * M2m = M2r * Tmat^T.
  C4  A (Miller a_{2^i}(f_j)) integer; |det A| = |det C| = I_k != 0, where
      C = row-0s of the Miller M2 powers.
  C5  the b2 Cramer certificate, on the LEAN-parsed literals:
      sum_i w'_i * M2^i = I_k * M3 entrywise (w' = |det C| * w, w * C = v,
      v = (a_3(f_j)); the operator identity is basis-independent, so it holds
      in fb coordinates on the landed matrices).
  C6  the committed HeckeRational witness, parsed from the Lean cert/scaled_id
      literals (plain/chunked/Horner bodies): reduced denominator
      Dred = D/gcd(D, N) divides I_k, and w' = (I_k/Dred) * N.

Output: research/iteration23/hecke-index/index_data.json + stdout report.
"""

import json
import re
import sys
from fractions import Fraction as Fr
from math import gcd
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
MF = ROOT / "MathProof" / "ModularForms"
OUT = Path(__file__).resolve().parent / "index_data.json"

T3_SMALL = MF / "MaedaT3SmallWeights.lean"
T3_DIM = {d: MF / f"MaedaT3Dim{d}Weights.lean" for d in range(6, 11)}
T2_DIM = {d: MF / f"MaedaDim{d}Weights.lean" for d in range(6, 11)}
HR_BIG = MF / "HeckeRationalWeights.lean"
HR_SMALL = MF / "HeckeRationalSmallWeights.lean"


# ---------------------------------------------------------------------------
# Lean literal parsing (same rules as gen_hecke_rat.py / g1_audit.py)


def namespaces(path):
    text = path.read_text()
    parts = re.split(r"^namespace (\w+)$", text, flags=re.M)
    return {parts[i]: parts[i + 1] for i in range(1, len(parts), 2)}


def weight_of(ns):
    m = re.fullmatch(r"Maeda(?:T3)?Weight(\d+)", ns)
    assert m, ns
    return int(m.group(1))


def hr_weight_of(ns):
    m = re.fullmatch(r"HeckeRatWeight(\d+)", ns)
    assert m, ns
    return int(m.group(1))


def parse_M(section):
    m = re.search(r"def M : Matrix \(Fin (\d+)\) \(Fin (\d+)\) ℤ :=\s*!!\[", section)
    assert m, "no M literal"
    n = int(m.group(1))
    start, depth, i = m.end(), 1, m.end()
    while depth:
        c = section[i]
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
        i += 1
    rows = [r.strip() for r in section[start:i - 1].split(";")]
    assert len(rows) == n
    mat = [[int(t.strip()) for t in r.split(",")] for r in rows]
    assert all(len(r) == n for r in mat)
    return mat


def parse_M2(section):
    m = re.search(r"def M2 : Matrix \(Fin (\d+)\) \(Fin (\d+)\) ℤ :=\s*!!\[",
                  section)
    assert m, "no M2 literal"
    n = int(m.group(1))
    start, depth, i = m.end(), 1, m.end()
    while depth:
        c = section[i]
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
        i += 1
    rows = [r.strip() for r in section[start:i - 1].split(";")]
    assert len(rows) == n
    mat = [[int(t.strip()) for t in r.split(",")] for r in rows]
    assert all(len(r) == n for r in mat)
    return mat


def parse_Atab(section):
    m = re.search(r"def Atab : ℕ → ℕ → ℂ(.*?)\n\n", section, flags=re.S)
    assert m, "no Atab"
    out = {}
    for i, j, v in re.findall(r"\| (\d+), (\d+) => \((-?\d+) : ℂ\)", m.group(1)):
        out[(int(i), int(j))] = int(v)
    assert "| _, _ => 0" in m.group(1)
    return out


def parse_value_lemmas(section, kind):
    if kind == "t":
        pat = re.compile(r"lemma t(\d+)_(\d+) : \(qExpansion 1 \((?:T2|T3) f\1\)\)\.coeff \2"
                         r" = \((-?\d+) : ℂ\)")
    else:
        pat = re.compile(r"lemma q(\d+)_(\d+) : \(qExpansion 1 f\1\)\.coeff \2 = \((-?\d+) : ℂ\)")
    out = {}
    for i, m_, v in pat.findall(section):
        out[(int(i), int(m_))] = int(v)
    return out


# --- integer-expression parsing (plain / flat chunks / Horner chunks) ------

TOKEN = re.compile(r"\s*(\d+|\+|-|\*|\^|\(|\))")


def int_expr_eval(text):
    """Evaluate the integer literal expressions emitted by int_expr_lines:
    `123`, `c0 * 10 ^ e0 + c1 * 10 ^ e1 ± …` (flat chunks), or
    `((((c0 * 10 ^ 74 + c1) * 10 ^ 74 + c2) … + ck)` (Horner), with optional
    leading unary minus / extra parens.  Precedence climbing with `^` right
    binding tighter than `*`, then `+`/`-` (left)."""
    toks = []
    pos = 0
    while pos < len(text):
        m = TOKEN.match(text, pos)
        if not m:
            assert text[pos:].strip() == "", f"trailing {text[pos:]!r}"
            break
        toks.append(m.group(1))
        pos = m.end()
    assert all(t != "" for t in toks)
    idx = 0

    def peek():
        return toks[idx] if idx < len(toks) else None

    def eat(t=None):
        nonlocal idx
        cur = peek()
        assert cur is not None and (t is None or cur == t), (cur, t, toks)
        idx += 1
        return cur

    def atom():
        if peek() == "(":
            eat("(")
            v = expr()
            eat(")")
            return v
        if peek() == "-":
            eat("-")
            return -atom()
        return int(eat())

    def power():
        v = atom()
        if peek() == "^":
            eat("^")
            return v ** atom()   # exponents are literals; right binding
        return v

    def term():
        v = power()
        while peek() == "*":
            eat("*")
            v *= power()
        return v

    def expr():
        v = term()
        while peek() in ("+", "-"):
            if eat() == "+":
                v += term()
            else:
                v -= term()
        return v

    v = expr()
    assert peek() is None, toks[idx:]
    return v


def parse_cert_N(section):
    """The landed `cert : ℕ → ℤ` arms of a HeckeRatWeight namespace."""
    block = re.search(r"def cert : ℕ → ℤ\n(.*?)\n  \| _ => 0", section, flags=re.S)
    assert block, "no cert def"
    out = {}
    cur = None
    for line in block.group(1).splitlines():
        am = re.match(r"  \| (\d+) =>(.*)", line)
        if am:
            cur = int(am.group(1))
            out[cur] = am.group(2).strip()
        elif cur is not None and line.startswith("      "):
            out[cur] += " " + line.strip()
    vals = {}
    for j, body in out.items():
        body = re.sub(r"\s+", " ", body).strip()
        vals[j] = int_expr_eval(body)
    return vals


def parse_scaled_id_D(section):
    m = re.search(r"theorem scaled_id :[^\n]*\n(.*?):= by", section, flags=re.S)
    assert m, "no scaled_id"
    body = m.group(1)
    d = re.search(r"=\s*\((.*?)\s*:\s*ℤ\)", body, flags=re.S)
    assert d, "no D literal in scaled_id"
    return int_expr_eval(re.sub(r"\s+", " ", d.group(1)).strip())


# ---------------------------------------------------------------------------
# prodForm arithmetic (probe_index.py machinery, unchanged)


N = 516
B = 3200


def sig(n, e):
    return sum(t ** e for t in range(1, n + 1) if n % t == 0)


def pack(a):
    def go(l, h):
        if h - l == 1:
            return a[l]
        m = (l + h) // 2
        return go(l, m) + (go(m, h) << (B * (m - l)))
    return go(0, len(a))


def unpack(v):
    v &= (1 << (B * N)) - 1

    def go(x, l, h):
        if h - l == 1:
            return [x]
        m = (l + h) // 2
        return go(x & ((1 << (B * (m - l))) - 1), l, m) + go(x >> (B * (m - l)), m, h)
    out, carry, half, full = [], 0, 1 << (B - 1), 1 << B
    for c0 in go(v, 0, N):
        c0 += carry
        if c0 >= half:
            c0 -= full
            carry = 1
        else:
            carry = 0
        out.append(c0)
    return out


def mul(a, b):
    return unpack(pack(a) * pack(b))


E4 = [1] + [240 * sig(n, 3) for n in range(1, N)]
E6 = [1] + [-504 * sig(n, 5) for n in range(1, N)]
c = mul(mul(E4, E4), E4)
s = mul(E6, E6)
Delta = [(x - y) // 1728 for x, y in zip(c, s)]
assert Delta[:6] == [0, 1, -24, 252, -1472, 4830]
assert Delta[12] == -370944
P = [[1] + [0] * (N - 1)]
for j in range(1, 12):
    P.append(mul(P[-1], Delta))
e = {0: [1] + [0] * (N - 1)}


def EP(a):
    if a not in e:
        e[a] = mul(EP(a - 1), E4)
    return e[a]


def basis_raw(k, dim):
    rows = []
    for j in range(1, dim + 1):
        w = k - 12 * j
        b = next(bb for bb in (0, 1, 2) if w - 6 * bb >= 0 and (w - 6 * bb) % 4 == 0)
        a = (w - 6 * b) // 4
        f = mul(P[j], EP(a))
        for _ in range(b):
            f = mul(f, E6)
        rows.append(f)
    return rows


def basis_miller(k, dim):
    rows = basis_raw(k, dim)
    for j in range(dim - 1, -1, -1):
        for i in range(j):
            c0 = rows[i][j + 1]
            rows[i] = [x - c0 * y for x, y in zip(rows[i], rows[j])]
    return rows


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def Tm_cols(k, m, rows):
    dim = len(rows)
    return [[sum(d ** (k - 1) * rows[j][m * i // (d * d)] for d in divisors(gcd(m, i)))
             for i in range(1, dim + 1)] for j in range(dim)]


def op_matrix(k, m, rows):
    n = len(rows)
    cols = Tm_cols(k, m, rows)
    op = [[0] * n for _ in range(n)]
    for j in range(n):
        for i in range(n):
            v = cols[j][i]
            for t in range(i):
                v -= rows[t][i + 1] * op[t][j]
            op[i][j] = v
    return op


def det(M):
    n = len(M)
    A = [[Fr(x) for x in r] for r in M]
    D = Fr(1)
    for cc in range(n):
        p = next((r for r in range(cc, n) if A[r][cc] != 0), None)
        if p is None:
            return 0
        if p != cc:
            A[p], A[cc] = A[cc], A[p]
            D = -D
        D *= A[cc][cc]
        for r in range(cc + 1, n):
            f = A[r][cc] / A[cc][cc]
            if f:
                A[r] = [x - f * y for x, y in zip(A[r], A[cc])]
    return int(D)


def matmul(X, Y):
    n = len(X)
    return [[sum(X[i][t] * Y[t][j] for t in range(n)) for j in range(n)] for i in range(n)]


def matpow(X, e_):
    n = len(X)
    R = [[int(i == j) for j in range(n)] for i in range(n)]
    while e_:
        if e_ & 1:
            R = matmul(R, X)
        X = matmul(X, X)
        e_ >>= 1
    return R


def cramer_wp(C, v):
    """w' = v . adj(C)  as the row-l-replaced determinant; asserts the
    defining identity w' . C = det(C) . v."""
    n = len(C)
    dC = det(C)
    w = []
    for l in range(n):
        C2 = [row[:] for row in C]
        C2[l] = v[:]
        w.append(det(C2))
    chk = [sum(w[i] * C[i][j] for i in range(n)) for j in range(n)]
    assert chk == [dC * x for x in v], "adjugate identity failed"
    return w, dC


# ---------------------------------------------------------------------------
# main


def main():
    t3 = {}
    small = set()
    for f in [T3_SMALL] + list(T3_DIM.values()):
        for ns, sec in namespaces(f).items():
            t3[weight_of(ns)] = (ns, sec)
            if f is T3_SMALL:
                small.add(weight_of(ns))
    t2dim = {}
    for d, f in T2_DIM.items():
        for ns, sec in namespaces(f).items():
            t2dim[weight_of(ns)] = (ns, sec)
    hr = {}
    for f in [HR_BIG, HR_SMALL]:
        for ns, sec in namespaces(f).items():
            hr[hr_weight_of(ns)] = sec

    weights = sorted(t3)
    assert len(weights) == 54 and len(hr) == 54, (len(weights), len(hr))

    fail = []
    report = []
    data = {}

    def check(cond, msg):
        if not cond:
            fail.append(msg)
        return cond

    for k in weights:
        ns3, sec3 = t3[k]
        n = len(parse_M(sec3))
        M3lean = parse_M(sec3)
        atab = parse_Atab(sec3)
        q3 = parse_value_lemmas(sec3, "q")
        if k in small:
            M2lean = parse_M2(hr[k])
        else:
            M2lean = parse_M(t2dim[k][1])

        # prodForm ground truth
        rrows = basis_raw(k, n)
        mrows = basis_miller(k, n)

        # C1: fb re-pin — Lean Atab/q-lemmas == raw prodForm coefficients
        ok_c1 = all(atab.get((i, j)) == rrows[i][j + 1]
                    for i in range(n) for j in range(n) if i < j)
        ok_c1 &= all(rrows[i][i + 1] == 1 for i in range(n))
        ok_c1 &= all(rrows[i][m] == 0 for i in range(n) for m in range(1, i + 1))
        ok_c1 &= all(q3.get((i + 1, m)) == rrows[i][m]
                     for (i, m) in q3 if i < n)
        check(ok_c1, f"w{k}: C1 fb literals != raw prodForm rows")

        # C2: Lean M2/M3 == op_matrix on the raw basis
        M2r = op_matrix(k, 2, rrows)
        M3r = op_matrix(k, 3, rrows)
        check(M2r == M2lean, f"w{k}: C2 M2 literal != re-derived coordinate matrix")
        check(M3r == M3lean, f"w{k}: C2 M3 literal != re-derived coordinate matrix")

        # C3: Miller + transition
        ok_m = all(mrows[j][i + 1] == int(i == j)
                   for i in range(n) for j in range(n))
        check(ok_m, f"w{k}: C3 Miller normalization failed")
        Tmat = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(i, n):
                v = int(i == j)
                for t in range(i, j):
                    v -= Tmat[i][t] * rrows[t][j + 1]
                Tmat[i][j] = v
        check(all(Tmat[i][j] == 0 for i in range(n) for j in range(n) if i > j)
              and all(Tmat[i][i] == 1 for i in range(n)),
              f"w{k}: C3 Tmat not upper-unitriangular")
        check(abs(det(Tmat)) == 1, f"w{k}: C3 |det Tmat| != 1")
        M2m = op_matrix(k, 2, mrows)
        Tt = [[Tmat[j][i] for j in range(n)] for i in range(n)]
        check(matmul(Tt, M2m) == matmul(M2r, Tt), f"w{k}: C3 conjugation bridge")

        # C4: A, C, I_k
        A = [[mrows[j][2 ** i] for j in range(n)] for i in range(n)]
        Pows = [matpow(M2m, i) for i in range(n)]
        C = [Pows[i][0][:] for i in range(n)]
        dA, dC = det(A), det(C)
        check(abs(dA) == abs(dC), f"w{k}: C4 |det A| != |det C| ({dA} vs {dC})")
        Ik = abs(dA)
        check(Ik != 0, f"w{k}: C4 I_k = 0")

        # C5: Cramer certificate on the LEAN-parsed literals
        v = [mrows[j][3] for j in range(n)]
        wp, dCh = cramer_wp(C, v)
        if dCh < 0:
            wp = [-x for x in wp]
        PowsLean = [matpow(M2lean, i) for i in range(n)]
        lhs = [[0] * n for _ in range(n)]
        for i in range(n):
            lhs = [[x + wp[i] * y for x, y in zip(xr, yr)]
                   for xr, yr in zip(lhs, PowsLean[i])]
        rhs = [[Ik * x for x in row] for row in M3lean]
        check(lhs == rhs, f"w{k}: C5 Cramer identity failed on Lean literals")

        # C6: committed (N, D) from the Lean HeckeRational literals
        Nv = parse_cert_N(hr[k])
        Dv = parse_scaled_id_D(hr[k])
        check(len(Nv) == n and all(Nv.get(j, 0) == 0 or True for j in range(n)),
              f"w{k}: C6 cert arms {len(Nv)} != {n}")
        g = Dv
        for j in range(n):
            g = gcd(g, abs(Nv[j]))
        Dred = Dv // g
        check(Ik % Dred == 0, f"w{k}: C6 D_red={Dred} !| I_k={Ik}")
        scale = Ik // Dred
        check([scale * Nv[j] for j in range(n)] == wp,
              f"w{k}: C6 w' != (I_k/D)*N")

        data[k] = {
            "dim": n, "Ik": Ik, "A": A, "wp": wp, "Tmat": Tmat,
            "N": [Nv[j] for j in range(n)], "D": Dv, "Dred": Dred,
            "sign_detC": 1 if dC > 0 else -1,
            "stats": {
                "A_digits": max(len(str(abs(x))) for r in A for x in r),
                "Ik_digits": len(str(Ik)),
                "wp_digits": max(len(str(abs(x))) for x in wp),
                "M2pow_digits": max(len(str(abs(x))) for Pm in PowsLean
                                    for r in Pm for x in r),
                "Dred_digits": len(str(Dred)),
            },
        }
        st = data[k]["stats"]
        report.append(f"w{k:3d} dim {n:2d}: Ik {st['Ik_digits']:3d}d  "
                      f"wp {st['wp_digits']:3d}d  A {st['A_digits']:3d}d  "
                      f"Dred {st['Dred_digits']:3d}d  Ik/D {scale}")

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
