#!/usr/bin/env python3 -I
"""Generate the rational Hecke witnesses for T₃ on S_k(SL(2, ℤ)).

For every level-one weight 24 ≤ k ≤ 134 with 2 ≤ dim S_k ≤ 10 (54 weights)
this emits a light kernel-certified theorem

    theorem heckeT3_eq_aeval_rat_weightKK :
        ∃ Q : ℚ[X], heckeTPₗ ((KK : ℕ) : ℤ) Nat.prime_three
          = Polynomial.aeval T₂ (Q.map (algebraMap ℚ ℂ))

via `MaedaLevelOne.exists_aeval_rat_dimN` (HeckeRational.lean):

* dims 6–10 (30 weights, `MathProof/ModularForms/HeckeRationalWeights.lean`):
  T₂-side data reused from `MaedaDim{6..10}Weights` (fb/Atab defeq-bridged to
  the T₃ file's, verified below by the alignment assert); per weight only the
  integer certificate (`cert`, `scaled_id` by `decide +kernel`) and the two
  entry bridges are emitted.
* dims 2–5 (24 weights, `MathProof/ModularForms/HeckeRationalSmallWeights.lean`):
  the T₂ coefficient table is re-derived from the T₃ file's kernel-decided
  q-lemma values through the `heckeT2_coeff` formula
  `(T₂ f)_m = f_{2m} + 2^{k-1} [2|m] f_{m/2}`, and the T₂ matrix is pinned by
  freshly emitted LvT2/entryT2 staged lemmas (the `charpoly_dimN` recipe).

Ground truth = the Lean literals in the T₂/T₃ weight files.  The generator
re-derives everything and asserts:

- the T₂/T₃ dim-file sections are syntactically aligned (fb/Atab/f-defs),
  so the cross-namespace defeq bridge is sound;
- every derived Xtab2 value equals the T₂ files' own t-lemma values
  (dims 2–5), charpoly(M₂) equals the T₂ files' `P` literals, and the
  weight-24 matrix equals `MaedaWeight24.toMatrix_heckeT2`;
- [M₂, M₃] = 0 and the ℚ-solve of `∑ q_j M₂^j = M₃` is unique and exact;
  the scaled identity `∑ N_j M₂^j = D • M₃` is verified cellwise.

Run:  python3 -I tools/gen_hecke_rat.py            (write both files)
      python3 -I tools/gen_hecke_rat.py --check    (byte-identity check)
"""

import json
import re
import sys
from fractions import Fraction
from math import gcd, lcm
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MF = ROOT / "MathProof" / "ModularForms"
sys.path.insert(0, str(ROOT / "tools"))
import gen_hecke_index as HI   # noqa: E402  (pow-free table renderers, shared)

WIDTH = 98          # linter.style.longLine limit is 100; keep a margin
CHUNK = 60          # digits per chunk in decomposed big literals
PLAIN_DIGITS = 80   # a plain (undecomposed) literal renders fine up to this
MAX_POW = 256       # Lean's default `exponentiation.threshold`
MAX_FIRST = 85      # gen_maedan's bound; OUR sites are tighter (78 below)
FLAT_FIRST_MAX = 78  # longest first chunk fitting `  | j => c0 * 10 ^ e` (98)
HORNER_CHUNK = 74   # Horner chunk width: first line `(((((c0 * 10 ^ 74` fits

T3_SMALL = MF / "MaedaT3SmallWeights.lean"
T3_DIM = {d: MF / f"MaedaT3Dim{d}Weights.lean" for d in range(6, 11)}
T2_DIM = {d: MF / f"MaedaDim{d}Weights.lean" for d in range(6, 11)}
T2_SMALL_FILES = [MF / "MaedaSmallWeights.lean", MF / "MaedaDim4Weights.lean",
                  MF / "MaedaDim5Weights.lean"]
SMALL_OUT = MF / "HeckeRationalSmallWeights.lean"
BIG_OUT = MF / "HeckeRationalWeights.lean"
G1_DATA = ROOT / "research/iteration22/hecke-rational/g1_data.json"


# ---------------------------------------------------------------------------
# Lean literal parsing (same rules as research/iteration22/hecke-rational/
# g1_audit.py — the G1 gate; keep in sync)


def namespaces(path):
    text = path.read_text()
    parts = re.split(r"^namespace (\w+)$", text, flags=re.M)
    return {parts[i]: parts[i + 1] for i in range(1, len(parts), 2)}


def weight_of(ns):
    m = re.fullmatch(r"Maeda(?:T3)?Weight(\d+)", ns)
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


def parse_P(section):
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
        mC = re.fullmatch(r"C<(\d+)>(?: \* \(?X(?: : ℤ\[X\])?\)?(?: \^ (\d+))?)?", piece)
        if mC:
            v = numexpr(vals[int(mC.group(1))])
            d = int(mC.group(2)) if mC.group(2) else (1 if " * " in piece else 0)
        else:
            mX = re.fullmatch(r"\(?X(?:: ℤ\[X\])?\)?(?: \^ (\d+))?", piece)
            assert mX, f"unparseable P term: {piece!r}"
            v, d = 1, (int(mX.group(1)) if mX.group(1) else 1)
        coeffs[d] = coeffs.get(d, 0) + (-v if neg else v)
    return [coeffs.get(i, 0) for i in range(max(coeffs) + 1)]


def def_bodies(section):
    """`name -> normalized body text` for defs (both `:=`-style and
    pattern-match style; the body is the whole block up to the blank line,
    including any docstring)."""
    out = {}
    for block in re.split(r"\n\n", section):
        stripped = re.sub(r"^/--.*?-\s*/\s*", "", block.strip(), flags=re.S)
        m = re.match(r"(?:noncomputable )?def (\w+)\b", stripped)
        if m:
            out[m.group(1)] = re.sub(r"\s+", " ", stripped).strip()
    return out


# ---------------------------------------------------------------------------
# exact linear algebra


def mat_mul(A, B):
    n = len(A)
    return [[sum(A[i][t] * B[t][j] for t in range(n)) for j in range(n)] for i in range(n)]


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
    return ints[::-1]


def solve_Q(M2, M3):
    n = len(M2)
    powers = [mat_pow(M2, j) for j in range(n)]
    rows = [[Fraction(powers[j][r][c]) for j in range(n)] + [Fraction(M3[r][c])]
            for r in range(n) for c in range(n)]
    rank, piv_cols = 0, []
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
    assert rank == n, "I, M2, .. not independent"
    for row in rows[n:]:
        assert all(x == 0 for x in row[:n]) and row[n] == 0
    q = [Fraction(0)] * n
    for i, col in enumerate(piv_cols):
        q[col] = rows[i][n]
    for r in range(n):
        for c in range(n):
            assert sum(q[j] * powers[j][r][c] for j in range(n)) == M3[r][c]
    return q


def norm_certificate(q):
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


# ---------------------------------------------------------------------------
# chunked literal emission (same rules as tools/gen_maedan.py)


def digit_sizes(d):
    if d - CHUNK <= MAX_POW:
        return None
    first = d - MAX_POW
    assert first <= MAX_FIRST, f"{d}-digit first chunk {first} > {MAX_FIRST}"
    sizes = [first]
    rem = MAX_POW
    while rem:
        take = min(CHUNK, rem)
        sizes.append(take)
        rem -= take
    return sizes


def slice_chunks(s):
    sizes = digit_sizes(len(s))
    if sizes is None:
        return [s[i:i + CHUNK] for i in range(0, len(s), CHUNK)]
    out, i = [], 0
    for w in sizes:
        out.append(s[i:i + w])
        i += w
    assert i == len(s) and all(out)
    return out


def int_expr_lines(v):
    """Un-indented physical lines of the ℤ expression for `v`.

    Plain when ≤ PLAIN_DIGITS; flat gen_maedan-style chunks
    (`c0 * 10 ^ e0 + c1 …`, every exponent ≤ MAX_POW and the first chunk
    ≤ MAX_FIRST so its token fits a WIDTH line) up to
    MAX_POW + MAX_FIRST digits; beyond that a Horner form in base `10 ^ 80`
    (`(((c0 * 10 ^ 80 + c1) * 10 ^ 80 … + ck)`) — every numeral ≤ 80 digits
    and every explicit power ≤ MAX_POW, so `norm_num` and the kernel
    evaluate the pieces (the T₃ certificates reach 381 digits, past the flat
    scheme's budget)."""
    d = len(str(abs(v)))
    if d <= PLAIN_DIGITS:
        return [str(v)]
    sign = "" if v >= 0 else "-"
    if d <= MAX_POW + FLAT_FIRST_MAX:
        chs = slice_chunks(str(abs(v)))
        toks = []
        for j, ch in enumerate(chs):
            e = sum(len(c) for c in chs[j + 1:])
            core = ch if e == 0 else f"{ch} * 10 ^ {e}"
            if j == 0:
                toks.append(sign + core)
            else:
                toks.append(f"{'+' if v >= 0 else '-'} {core}")
        return toks
    # Horner in base 10 ^ HORNER_CHUNK (leading zeros of a chunk stripped:
    # the place value is carried by the `* 10 ^` factors, not the digits)
    s = str(abs(v))
    chunks = []
    while s:
        chunks.insert(0, str(int(s[-HORNER_CHUNK:])))
        s = s[:-HORNER_CHUNK]
    lines = ["(" * (len(chunks) - 1) + chunks[0] + f" * 10 ^ {HORNER_CHUNK}"]
    for j, ch in enumerate(chunks[1:], 1):
        tail = "" if j == len(chunks) - 1 else f" * 10 ^ {HORNER_CHUNK}"
        lines.append(f"+ {ch}){tail}")
    if v < 0:
        lines[0] = "-(" + lines[0]
        lines[-1] = lines[-1] + ")"
    return lines


def wrap_tokens(tokens, first_prefix, cont_prefix):
    """Greedily wrap token lines to WIDTH; `tokens` are pre-split lines."""
    out, cur = [], first_prefix
    for tok in tokens:
        cand = cur + tok
        if len(cand) > WIDTH:
            out.append(cur)
            cur = cont_prefix + tok
        else:
            cur = cand
    out.append(cur)
    return out


# ---------------------------------------------------------------------------
# per-weight data


def gather_weights():
    t3 = {}
    small = set()
    for f in [T3_SMALL] + list(T3_DIM.values()):
        for ns, sec in namespaces(f).items():
            t3[weight_of(ns)] = (ns, sec)
            if f is T3_SMALL:
                small.add(weight_of(ns))
    t2 = {}
    for f in list(T2_DIM.values()) + T2_SMALL_FILES:
        for ns, sec in namespaces(f).items():
            t2[weight_of(ns)] = (ns, sec)
    return t3, t2, small


def derive_X2_M2(k, n, q3, atab):
    """Xtab2 (i, m) → coeff m+1 of T₂ f_{i+1}; M₂ = coordN back-substitution."""
    def fc(i, m):
        return q3.get((i + 1, m), 0)

    X2 = {}
    for i in range(n):
        for m in range(n):
            mm = m + 1
            v = fc(i, 2 * mm)
            if mm % 2 == 0:
                v += (1 << (k - 1)) * fc(i, mm // 2)
            X2[(i, m)] = v
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
    return X2, M2


def coordN_table(atab, X2, n):
    """coordN Atab (Xtab2 i) j for all (i, j) — equals M₂, re-derived."""
    out = {}
    for i in range(n):
        gamma = []
        for j in range(n):
            v = X2[(i, j)]
            for t in range(j):
                v -= atab.get((t, j), 0) * gamma[t]
            gamma.append(v)
        for j in range(n):
            out[(i, j)] = gamma[j]
    return out


def audit_and_certify(t3, t2, small):
    """Full re-derivation + asserts; returns per-weight generation data."""
    with open(G1_DATA) as fh:
        g1 = json.load(fh)
    out = {}
    for k in sorted(t3):
        ns3, sec3 = t3[k]
        n = len(parse_M(sec3))
        M3 = parse_M(sec3)
        q3 = parse_value_lemmas(sec3, "q")
        atab = parse_Atab(sec3)
        assert g1[str(k)]["M3"] == M3 and g1[str(k)]["M2"] is not None

        if k not in small:
            ns2, sec2 = t2[k]
            M2 = parse_M(sec2)
            b2, b3 = def_bodies(sec2), def_bodies(sec3)
            for nm in ["fb", "Atab"]:
                assert b2[nm] == b3[nm], f"w{k}: {nm} body differs T2/T3"
            f2 = {nm: b for nm, b in b2.items() if re.fullmatch(r"f\d+", nm)}
            f3 = {nm: b for nm, b in b3.items() if re.fullmatch(r"f\d+", nm)}
            assert set(f2) == set(f3) and all(f2[x] == f3[x] for x in f2), f"w{k}: f-defs differ"
            t2v = parse_value_lemmas(sec2, "t")
        else:
            X2, M2 = derive_X2_M2(k, n, q3, atab)
            t2v = {}
            if k in t2:
                t2v = parse_value_lemmas(t2[k][1], "t")
                for (ti, tm), v in t2v.items():
                    assert X2.get((ti - 1, tm - 1)) == v, f"w{k}: X2 != t{ti}_{tm}"
                assert charpoly(M2) == parse_P(t2[k][1]), f"w{k}: charpoly(M2) != P"
            else:
                assert k == 24 and M2 == [[696, 1], [20736000, 384]], f"w{k}: M2 re-derive"
        assert M2 == g1[str(k)]["M2"], f"w{k}: M2 != g1"
        assert g1[str(k)]["Atab"] == {kk: v for kk, v in
                                      ((f"{a},{b}", v) for (a, b), v in atab.items())}

        C = [[sum(M2[i][t] * M3[t][j] - M3[i][t] * M2[t][j] for t in range(n))
              for j in range(n)] for i in range(n)]
        assert all(x == 0 for r in C for x in r), f"w{k}: [M2,M3] != 0"
        q = solve_Q(M2, M3)
        N, D = norm_certificate(q)
        lhs = [[0] * n for _ in range(n)]
        for j, Nj in enumerate(N):
            Pj = mat_pow(M2, j)
            for r in range(n):
                for c in range(n):
                    lhs[r][c] += Nj * Pj[r][c]
        assert lhs == [[D * x for x in row] for row in M3], f"w{k}: scaled identity"
        assert D != 0

        out[k] = {
            "k": k, "n": n, "small": k in small, "ns3": ns3, "ns2": t2.get(k, ("", ""))[0],
            "M2": M2, "M3": M3, "atab": atab, "X2": X2 if k in small else None,
            "t2vals": t2v, "N": N, "D": D, "q3": q3,
        }
    assert len(out) == 54
    return out


# ---------------------------------------------------------------------------
# emission


def cert_def(N, n):
    lines = [f"/-- The integer certificate `c`: `∑ c j • M₂^j = D • M₃`. -/",
             "def cert : ℕ → ℤ"]
    for j, v in enumerate(N):
        toks = int_expr_lines(v)
        if len(toks) == 1:
            lines.append(f"  | {j} => {toks[0]}")
        else:
            lines.append(f"  | {j} =>")
            lines.extend("      " + t for t in toks)
    lines.append("  | _ => 0")
    return lines


def matrix_def(M, name, doc):
    """`def NAME : Matrix (Fin n) (Fin n) ℤ := !![..; ..]` with WIDTH wrap."""
    n = len(M)
    out = [doc, f"def {name} : Matrix (Fin {n}) (Fin {n}) ℤ :="]
    cur = "      !!["
    for i, row in enumerate(M):
        for j, x in enumerate(row):
            last = i == len(M) - 1 and j == n - 1
            sep = "]" if last else (";" if j == n - 1 else ",")
            piece = f"{x}{sep}"
            if cur.endswith("["):
                cur += piece
            elif len(cur) + 1 + len(piece) > WIDTH:
                out.append(cur)
                cur = "      " + piece
            else:
                cur += " " + piece
    out.append(cur)
    return out


def scaled_id(n, D, m2name, m3name, docname, N=None, M2=None, M3=None):
    """`scaled_id` lines + the D-argument lines for the application.

    Iteration 25 (scaled-certs): the identity is no longer decided cell by
    cell (each cell dragged the `Finset` sum, the `!![…]` literals and the
    chunked `10 ^ e` numerals into its certificate); instead the matrices are
    re-stated as pow-free integer tables (`t2tab`/`t3tab`, bridged by
    `fin_cases <;> rfl`) and the whole identity is ONE `List`-sum boolean
    `ScaledCert.scaledCheck … = true` (`propext`-only), bridged back by
    `ScaledCert.scaled_of_check`.  The tables are reused by the HeckeIndex
    files."""
    Dtoks = int_expr_lines(D)
    if len(Dtoks) == 1:
        oneline = f"    = ({Dtoks[0]} : ℤ) • {m3name} :="
        if len(oneline) <= WIDTH:
            dlines = [oneline]
        else:
            dlines = [f"    = ({Dtoks[0]} : ℤ)", f"    • {m3name} :="]
        arg = [f"({Dtoks[0]} : ℤ)"]
    else:
        dlines = [f"    = ({Dtoks[0]}"]
        dlines.extend("    " + t for t in Dtoks[1:])
        tail = f"    : ℤ) • {m3name} :="
        dlines.append(tail)
        arg = ["(" + Dtoks[0]] + ["  " + t for t in Dtoks[1:]] + ["  : ℤ)"]
    pre = scaled_tables(n, M2, M3, m2name, m3name)
    # pow-free weights / scalar (only where the landed literal has `^`)
    if any(len(int_expr_lines(v)) > 1 for v in N):
        pre.extend(HI.seq_def("certv", N, "The certificate `cert`, pow-free (for the `List` "
                              "certificate).", HI.int_lines_nopow))
        pre.append("")
        pre.append(f"theorem hcertv : ∀ j : Fin {n}, cert j = certv j := by")
        pre.append("  intro j")
        pre.append("  fin_cases j <;> rfl")
        pre.append("")
        wv, hw = "certv", "hcertv"
    else:
        wv, hw = "cert", "(fun _ => rfl)"
    if len(Dtoks) > 1:
        pre.extend(HI.chunked_def("Dv", D, "The scalar `D`, pow-free.", lines_of=HI.int_lines_nopow))
        pre.append("")
        sv = "Dv"
    else:
        sv = f"({Dtoks[0]} : ℤ)"
    pre.append("/-- The kernel certificate over `List` sums and integer tables (`propext`-only). -/")
    pre.extend(wrap_words(f"theorem hscaled : ScaledCert.scaledCheck {wv} t2tab {sv} t3tab "
                          f"{n} {n} = true := by", "", "    "))
    pre.append("  decide +kernel")
    pre.append("")
    lines = pre + [f"theorem {docname} : (∑ j ∈ Finset.range {n}, cert j • {m2name} ^ j)"] + dlines
    lines.extend(wrap_words(f"ScaledCert.scaled_of_check {n} cert {wv} {m2name} {m3name} _ "
                            f"{sv} t2tab t3tab {hw} rfl ht2tab ht3tab hscaled", "  ", "    "))
    return lines, arg


def wrap_words(text, first_prefix, cont_prefix):
    """Greedily wrap the space-separated words of `text` to WIDTH."""
    out, cur = [], first_prefix
    for tok in text.split(" "):
        if cur.strip() and len(cur) + 1 + len(tok) > WIDTH:
            out.append(cur)
            cur = cont_prefix + tok
        else:
            cur = cur + (" " if cur.strip() else "") + tok
    out.append(cur)
    return out


def scaled_tables(n, M2, M3, m2name, m3name):
    """`t2tab`/`t3tab` + their `fin_cases <;> rfl` bridges."""
    out = []
    for t, M, nm in [("t2tab", M2, m2name), ("t3tab", M3, m3name)]:
        out.extend(HI.table_def(t, M, f"`{nm}` as a pow-free integer table (for the `List` "
                                "certificate)."))
        out.append("")
        out.append(f"theorem h{t} : ∀ i j : Fin {n}, {nm} i j = {t} i.val j.val := by")
        out.append("  intro i j")
        out.append("  fin_cases i <;> fin_cases j <;> rfl")
        out.append("")
    return out


def emit_small_section(w):
    k, n = w["k"], w["n"]
    q3 = w["q3"]
    X2 = w["X2"]
    L = []
    L.append(f"/-! ### Weight {k} (dim {n}) -/")
    L.append(f"namespace HeckeRatWeight{k}")
    L.append("")
    L.append(f"open MaedaT3Weight{k}")
    L.append("")
    L.append("/-- `T₂` on this weight. -/")
    L.append(f"noncomputable def T2 := heckeTPₗ (({k} : ℕ) : ℤ) Nat.prime_two")
    L.append("")
    L.append("/-- `Xtab2 i m` = coefficient of `q^(m+1)` in `T₂ (f i)`. -/")
    L.append("def Xtab2 : ℕ → ℕ → ℂ")
    for i in range(n):
        for m in range(n):
            L.append(f"  | {i}, {m} => ({X2[(i, m)]} : ℂ)")
    L.append("  | _, _ => 0")
    L.append("")
    # t-lemmas
    for i in range(n):
        for m in range(n):
            mm = m + 1
            refs = [f"q{i + 1}_{2 * mm}"]
            if mm % 2 == 0:
                refs.append(f"q{i + 1}_{mm // 2}")
            L.append(f"lemma t2_{i + 1}_{mm} : (qExpansion 1 (T2 f{i + 1})).coeff {mm}"
                     f" = ({X2[(i, m)]} : ℂ) := by")
            L.append("  rw [T2, heckeT2_coeff (by norm_num)]")
            L.append(f"  norm_num [{', '.join(refs)}]")
            L.append("")
    # hX2
    L.append("/-- `charpoly_dimN`-style hypothesis: the `T₂`-image coefficients. -/")
    L.append(f"lemma hX2 : ∀ (i m : ℕ), i < {n} → m < {n} →")
    L.append("    (qExpansion 1 (T2 (fb i))).coeff (m + 1) = Xtab2 i m := by")
    L.append("  intro i m hi hm")
    L.append("  interval_cases i")
    for i in range(n):
        L.append("  · simp only [fb]")
        L.append("    interval_cases m")
        for m in range(n):
            L.append("    · rw [t2_%d_%d]" % (i + 1, m + 1))
            L.append("      rfl")
    L.append("")
    # LvT2 staged lemmas: coordsAux Atab (fun m => Xtab2 i m) j
    def lv_target(i, j):
        vals = []
        v = []
        for jj in range(j):
            t = X2[(i, jj)]
            for tt in range(jj):
                t -= w["atab"].get((tt, jj), 0) * v[tt]
            v.append(t)
        vals = v
        return "[{}]" .format(", ".join(f"(({x} : ℤ) : ℂ)" for x in vals))
    def tgt_lines(i, j, indent=4):
        vals = lv_target(i, j)[1:-1].split(", ")
        pad = " " * indent
        budget = WIDTH - (2 if indent == 6 else 0)
        out, cur = [], pad + "["
        for t_i, tv in enumerate(vals):
            piece = tv + ("]" if t_i == len(vals) - 1 else ",")
            if len(cur) + 1 + len(piece) > budget and not cur.endswith("["):
                out.append(cur)
                cur = pad + piece
            else:
                cur = cur + piece if cur.endswith("[") else cur + " " + piece
        out.append(cur)
        return out

    for i in range(n):
        for j in range(1, n + 1):
            tgtl = tgt_lines(i, j)
            L.append(f"theorem LvT2_{i}_{j} : coordsAux Atab (fun m => Xtab2 {i} m) {j} =")
            for ln in tgtl[:-1]:
                L.append(ln)
            if j == 1:
                L.append(tgtl[-1] + " := by")
                L.append("  simp only [coordsAux, Xtab2, Finset.sum_range_zero, List.nil_append]")
                L.append("  norm_num")
            else:
                last = tgtl[-1]
                if len(last) + len(" := by") <= WIDTH:
                    L.append(last + " := by")
                else:
                    L.append(last)
                    L.append("    := by")
                L.append(f"  change coordsAux Atab (fun m => Xtab2 {i} m) {j - 1}")
                L.append(f"      ++ [Xtab2 {i} {j - 1} - ∑ i ∈ Finset.range {j - 1},")
                L.append(f"      Atab i {j - 1} * (coordsAux Atab (fun m => Xtab2 {i} m) {j - 1}).getD i 0] =")
                for ln in tgt_lines(i, j, 6):
                    L.append(ln)
                L.append(f"  rw [LvT2_{i}_{j - 1}]")
                succ = "List.getD_cons_succ, " if j >= 3 else ""
                L.append(f"  simp only [Atab, Xtab2, Finset.sum_range_succ, Finset.sum_range_zero,")
                L.append(f"      {succ}List.getD_cons_zero, List.nil_append, List.cons_append]")
                L.append("  norm_num")
            L.append("")
    # entryT2 lemmas
    ct = coordN_table(w["atab"], X2, n)
    for j in range(n):
        for i in range(n):
            L.append(f"theorem entryT2_{j}_{i} : coordN Atab (fun m => Xtab2 {i} m) {j}")
            L.append(f"      = (({ct[(i, j)]} : ℤ) : ℂ) := by")
            L.append("  simp only [coordN]")
            L.append(f"  rw [LvT2_{i}_{j + 1}]")
            L.append("  rfl")
            L.append("")
    # M2 literal
    L.extend(matrix_def(w["M2"], "M2",
                        "/-- The matrix of `T₂` in the echelon basis (re-derived, "
                        "regression-checked). -/"))
    L.append("")
    # hM2 (local Xtab2 / M2), hM3 (T₃ file's Xtab / M, opened)
    L.append(f"lemma hM2 : ∀ (i l : Fin {n}), coordN Atab (fun m => Xtab2 i.val m) l.val")
    L.append("    = ((M2 l i : ℤ) : ℂ) := by")
    L.append("  intro i l")
    L.append("  fin_cases i <;> fin_cases l")
    for i in range(n):
        for l in range(n):
            L.append(f"  · exact entryT2_{l}_{i}")
    L.append("")
    L.append(f"lemma hM3 : ∀ (i l : Fin {n}), coordN Atab (fun m => Xtab i.val m) l.val")
    L.append("    = ((M l i : ℤ) : ℂ) := by")
    L.append("  intro i l")
    L.append("  fin_cases i <;> fin_cases l")
    for i in range(n):
        for l in range(n):
            L.append(f"  · exact entry_{l}_{i}")
    L.append("")
    # certificate + identity
    L.extend(cert_def(w["N"], n))
    L.append("")
    sid, Darg = scaled_id(n, w["D"], "M2", "M", "scaled_id", w["N"], w["M2"], w["M3"])
    L.extend(sid)
    L.append("")
    # final theorem
    L.append(f"/-- **`T₃ ∈ ℚ[T₂]` at weight {k}.** -/")
    L.append(f"theorem heckeT3_eq_aeval_rat_weight{k} :")
    L.append(f"    ∃ Q : ℚ[X], heckeTPₗ (({k} : ℕ) : ℤ) Nat.prime_three")
    L.append("      = Polynomial.aeval T2 (Q.map (algebraMap ℚ ℂ)) :=")
    L.append(f"  exists_aeval_rat_dimN (by norm_num) finrank_eq fb Atab Xtab2 Xtab")
    L.append(f"    hzero hone hA T2 T3 hX2 hX M2 M hM2 hM3")
    oneline = f"    cert {Darg[0]} (by norm_num) scaled_id"
    if len(Darg) == 1 and len(oneline) <= WIDTH:
        L.append(oneline)
    elif len(Darg) == 1:
        L.append(f"    cert {Darg[0]}")
        L.append("      (by norm_num) scaled_id")
    else:
        L.append("    cert")
        L.extend("      " + t for t in Darg)
        L.append("      (by norm_num) scaled_id")
    L.append("")
    L.append(f"end HeckeRatWeight{k}")
    L.append("")
    return "\n".join(L)


def emit_big_section(w):
    k, n = w["k"], w["n"]
    ns2, ns3 = w["ns2"], w["ns3"]
    L = []
    L.append(f"/-! ### Weight {k} (dim {n}) -/")
    L.append(f"namespace HeckeRatWeight{k}")
    L.append("")
    L.extend(cert_def(w["N"], n))
    L.append("")
    sid, Darg = scaled_id(n, w["D"], f"{ns2}.M", f"{ns3}.M", "scaled_id", w["N"], w["M2"],
                           w["M3"])
    L.extend(sid)
    L.append("")
    for name, xname, mname, pfx in [
        ("hM2", f"{ns2}.Xtab", f"{ns2}.M", f"{ns2}.entry"),
        ("hM3", f"{ns3}.Xtab", f"{ns3}.M", f"{ns3}.entry"),
    ]:
        L.append(f"lemma {name} : ∀ (i l : Fin {n}), coordN {ns3}.Atab")
        L.append(f"      (fun m => {xname} i.val m) l.val")
        L.append(f"    = (({mname} l i : ℤ) : ℂ) := by")
        L.append("  intro i l")
        L.append("  fin_cases i <;> fin_cases l")
        for i in range(n):
            for l in range(n):
                L.append(f"  · exact {pfx}_{l}_{i}")
        L.append("")
    L.append(f"/-- **`T₃ ∈ ℚ[T₂]` at weight {k}.** -/")
    L.append(f"theorem heckeT3_eq_aeval_rat_weight{k} :")
    L.append(f"    ∃ Q : ℚ[X], heckeTPₗ (({k} : ℕ) : ℤ) Nat.prime_three")
    L.append(f"      = Polynomial.aeval {ns2}.T2 (Q.map (algebraMap ℚ ℂ)) :=")
    L.append(f"  exists_aeval_rat_dimN (by norm_num) {ns3}.finrank_eq {ns3}.fb")
    L.append(f"    {ns3}.Atab {ns2}.Xtab {ns3}.Xtab")
    L.append(f"    {ns3}.hzero {ns3}.hone {ns3}.hA")
    app = f"    {ns2}.T2 {ns3}.T3 {ns2}.hX {ns3}.hX {ns2}.M {ns3}.M hM2 hM3"
    if len(app) <= WIDTH:
        L.append(app)
    else:
        L.append(f"    {ns2}.T2 {ns3}.T3 {ns2}.hX {ns3}.hX")
        L.append(f"    {ns2}.M {ns3}.M hM2 hM3")
    oneline = f"    cert {Darg[0]} (by norm_num) scaled_id"
    if len(Darg) == 1 and len(oneline) <= WIDTH:
        L.append(oneline)
    elif len(Darg) == 1:
        L.append(f"    cert {Darg[0]}")
        L.append("      (by norm_num) scaled_id")
    else:
        L.append("    cert")
        L.extend("      " + t for t in Darg)
        L.append("      (by norm_num) scaled_id")
    L.append("")
    L.append(f"end HeckeRatWeight{k}")
    L.append("")
    return "\n".join(L)


def finalize(text):
    # collapse accidental triple newlines
    text = re.sub(r"\n\n\n+", "\n\n", text)
    return text.rstrip("\n") + "\n"


def main():
    check = "--check" in sys.argv
    t3, t2, small = gather_weights()
    data = audit_and_certify(t3, t2, small)

    small_header = f"""import MathProof.ModularForms.HeckeRational
import MathProof.ModularForms.ScaledCert
import MathProof.ModularForms.MaedaT3SmallWeights

/-!
# `T₃ ∈ ℚ[T₂]` for the level-one weights with `dim S_k ∈ {{2, …, 5}}`

For each of the 24 weights `k ≤ 74` with `2 ≤ dim S_k ≤ 5`: a light
kernel-certified rational polynomial witness

    ∃ Q : ℚ[X], heckeTPₗ ((k : ℕ) : ℤ) Nat.prime_three
      = Polynomial.aeval T₂ (Q.map (algebraMap ℚ ℂ)),

where `T₂ = heckeTPₗ k Nat.prime_two` and the witness comes from
`MaedaLevelOne.exists_aeval_rat_dimN` applied to the T₃ file's echelon data
(`fb`, `Atab`, `hzero/hone/hA/hX`) plus a freshly re-derived T₂ coefficient
table (`Xtab2` via `heckeT2_coeff` and the T₃ file's kernel-decided
q-lemma values), pinned to the literal matrix `M2` by staged `LvT2`/`entryT2`
lemmas (`charpoly_dimN`'s recipe), and the integer certificate
`∑_{{j<n}} cert j • M2^j = D • M3` checked by `decide +kernel`
(regression-checked against the T₂ files' `charpoly_T2` literals).

This file is generated by `tools/gen_hecke_rat.py` — regenerate, never
hand-edit (`python3 -I tools/gen_hecke_rat.py --check` verifies
byte-identity).  Like its parent `MaedaT3SmallWeights`, it is registered in
the root `MathProof.lean` only and is NOT a `defaultTargets`/CI item.
-/

open UpperHalfPlane ModularForm CuspForm Polynomial MaedaLevelOne
open scoped MatrixGroups

"""
    big_header = f"""import MathProof.ModularForms.HeckeRational
import MathProof.ModularForms.ScaledCert
import MathProof.ModularForms.MaedaT3Dim6Weights
import MathProof.ModularForms.MaedaT3Dim7Weights
import MathProof.ModularForms.MaedaT3Dim8Weights
import MathProof.ModularForms.MaedaT3Dim9Weights
import MathProof.ModularForms.MaedaT3Dim10Weights
import MathProof.ModularForms.MaedaDim6Weights
import MathProof.ModularForms.MaedaDim7Weights
import MathProof.ModularForms.MaedaDim8Weights
import MathProof.ModularForms.MaedaDim9Weights
import MathProof.ModularForms.MaedaDim10Weights

/-!
# `T₃ ∈ ℚ[T₂]` for the level-one weights `72 ≤ k ≤ 134` (dims 6–10)

For each of the 30 weights with `6 ≤ dim S_k ≤ 10`: a light kernel-certified
rational polynomial witness

    ∃ Q : ℚ[X], heckeTPₗ ((k : ℕ) : ℤ) Nat.prime_three
      = Polynomial.aeval T₂ (Q.map (algebraMap ℚ ℂ)),

via `MaedaLevelOne.exists_aeval_rat_dimN`.  The T₂-side data (`Xtab`, `hX`,
`M`, `entry_*`) is reused verbatim from `MaedaDim{{6..10}}Weights` — its
`fb`/`Atab` are syntactically identical to the T₃ file's (asserted by the
generator), so the cross-namespace defeq bridge is sound.  Each weight adds
only its integer certificate (`cert`, `scaled_id` by `decide +kernel`) and
the two `coordN` entry bridges.

This file is generated by `tools/gen_hecke_rat.py` — regenerate, never
hand-edit (`python3 -I tools/gen_hecke_rat.py --check` verifies
byte-identity).
-/

open UpperHalfPlane ModularForm CuspForm Polynomial MaedaLevelOne
open scoped MatrixGroups

"""
    small_body = "".join(emit_small_section(data[k]) for k in sorted(data) if data[k]["small"])
    big_body = "".join(emit_big_section(data[k]) for k in sorted(data) if not data[k]["small"])
    small_text = finalize(small_header + small_body)
    big_text = finalize(big_header + big_body)

    for path, text in [(SMALL_OUT, small_text), (BIG_OUT, big_text)]:
        if check:
            disk = path.read_text()
            if disk != text:
                print(f"CHECK FAILED: {path.name} differs from regeneration")
                sys.exit(1)
            print(f"check ok: {path.name} ({len(text.splitlines())} lines)")
        else:
            path.write_text(text)
            print(f"wrote {path.name} ({len(text.splitlines())} lines)")
    if not check:
        print("regeneration asserts all passed (alignment, t-lemma cross-checks, "
              "charpoly, commutation, exact ℚ-solve)")


if __name__ == "__main__":
    main()
