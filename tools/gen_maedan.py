#!/usr/bin/env python3
"""Generate MathProof/ModularForms/MaedaDim{6..10}Weights.lean (Iteration 20).

Per weight k with dim S_k = n in [6, 10] the generator emits one namespace
containing:
  * the echelon basis f_i = Delta^(i+1) E4^a E6^b (prodForm) and its
    coefficient machinery (seqPLc lists, q-coefficient lemmas up to 2n,
    T2-image lemmas up to n);
  * the A/X coefficient tables (matches on concrete indices, `rfl`-reducible);
  * the four charpoly_dimN hypothesis discharges (fin_cases + interval_cases
    over emitted per-case lemmas);
  * the literal integer matrix M_k (from the census JSON), its charpoly P
    (literal), n+1 certified `eval_det` determinants and `norm_num`
    evaluations, and the charpoly_T2 bridge through
    CharpolyEngine.charpoly_of_eval_eq + Matrix.charpoly_map;
  * Rabin certificates at the census prime ell (kernel decides) and
    `maeda : Irreducible (P.map (Int.castRingHom Q))` via
    RabinCert.irreducible_of_rabin_int, plus the second-prime sanity decide.

Every numeral comes from research/iteration20/data/maeda_dim6_10.json or is
recomputed from research/maeda-scaling-probe.py; the generator asserts the
recomputed T2 matrices and charpolys agree with the JSON (which regresses
against the charpolys proved in MaedaWeight24 / MaedaDim4Weights).

Re-runs are byte-identical (chain-cache rule): `tools/gen_maedan.py --check`.
"""
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

_spec = importlib.util.spec_from_file_location(
    "maeda_scaling_probe", ROOT / "research" / "maeda-scaling-probe.py")
msp = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(msp)  # runs its k=24/k=48 regression asserts

DATA = json.load(open(ROOT / "research/iteration20/data/maeda_dim6_10.json"))
BY_K = {w["k"]: w for w in DATA}

EVAL_LEMMAS = ("Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, "
               "Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, "
               "Polynomial.eval_neg")


def G(w):
    """E4^a E6^b of weight w, minimal b (identical to the probe / gen_maeda.py)."""
    for b in (0, 1):
        if w - 6 * b >= 0 and (w - 6 * b) % 4 == 0:
            return ((w - 6 * b) // 4, b)
    raise ValueError(w)


def prime_divisors(n):
    return msp.prime_divisors(n)


def is_prime(m):
    if m < 2:
        return False
    return all(m % d for d in range(2, int(m ** 0.5) + 1))


def series(i0, a, b, N):
    """Coefficients 0..N of Delta^(i0+1) E4^a E6^b (probe series data)."""
    s = msp.series_mul(msp.pw(msp.D, i0 + 1),
                       msp.series_mul(msp.pw(msp.E4, a), msp.pw(msp.E6, b)))
    return s[:N + 1]


def t2_coeffs(k, n, i0, a, b, N):
    """(coefficients 0..N-1 of f_i, dict of T2-image coefficients 1..n).

    seqPLc i a b N has length N (coefficients 0..N-1); with N = 2n+1 the
    q-lemmas cover every coefficient the extraction reads (m <= 2n = N-1)."""
    f = series(i0, a, b, max(N, 2 * n))
    t = {}
    for m in range(1, n + 1):
        t[m] = f[2 * m] + (2 ** (k - 1) * f[m // 2] if m % 2 == 0 else 0)
    return f[:N], t


def reflected_powmod(ell, f, e):
    """Model of RabinCert.zpxw: X^e mod f over Z/ell, little-endian lists."""
    return msp.powx(e, f, ell)


def reflected_gcd_steps(ell, a, b):
    """Number of pmod-steps the reflected Euclid needs (fuel lower bound)."""
    steps = 0
    while b and msp.pnorm(list(b)):
        _, r = msp.pdivmod(list(a), list(b), ell)
        a, b = b, r
        steps += 1
    return steps


def lean_int(x):
    return str(x)


WIDTH = 98  # Modal's linter.style.longLine limit is 100; keep a margin


def wrap_terms(terms, cont_indent, sep=" + "):
    """Join terms with sep, breaking lines so every rendered line stays within
    WIDTH.  The separator trails on continued lines (`a +\nb`), which parses
    for + and ,; continuation lines are indented by cont_indent spaces."""
    pad = " " * cont_indent
    out, cur = [], ""
    for t in terms:
        piece = t + sep if t is not terms[-1] else t
        budget = WIDTH if not out else WIDTH - cont_indent
        if cur and len(cur) + len(piece.rstrip()) > budget:
            out.append(cur.rstrip())
            cur = ""
        cur += piece
    out.append(cur.rstrip())
    return ("\n" + pad).join(out)


def lean_list(xs, indent=0):
    body = ", ".join(lean_int(x) for x in xs)
    if len(body) <= 100 - 2 * indent:
        return f"[{body}]"
    # wrap at ~90 columns
    lines, cur = [], ""
    for x in xs:
        piece = lean_int(x)
        if cur and len(cur) + len(piece) + 2 > 88:
            lines.append(cur)
            cur = ""
        cur += piece + ", "
    lines.append(cur[:-2])
    pad = " " * (2 + indent)
    return "[" + ("\n" + pad).join(lines) + "]"


def coeff_stmt(head, val):
    """Physical lines of a `lemma … = (val : ℂ) := by` statement: one line
    when it fits WIDTH, else the RHS carried to a continuation line (a
    newline inside the statement is insignificant to Lean)."""
    one = f"{head} = ({val} : ℂ) := by"
    if len(one) <= WIDTH:
        return [one]
    return [f"{head} =", f"    ({val} : ℂ) := by"]


def matrix_literal(M, indent=6, diag=None):
    """`!![…]` literal, rows separated by `;`, entries wrapped so every line
    stays within WIDTH (continuation lines aligned at `indent`).  With `diag`
    a function of (i, j) the cell text is customized (`t - x` on the diagonal
    for the symbolic `t·1 − M` matrices)."""
    pad = " " * indent
    lines, cur = [], ""
    for ri, r in enumerate(M):
        for j, x in enumerate(r):
            cell = lean_int(x) if diag is None else diag(ri, j, x)
            piece = cell + ("" if j == len(r) - 1 else ",")
            if cur and len(pad) + len(cur) + len(piece.rstrip()) + 1 > WIDTH:
                lines.append(cur.rstrip())
                cur = ""
            cur += piece + ("" if j == len(r) - 1 else " ")
        cur += ";" if ri < len(M) - 1 else ""
        lines.append(cur.rstrip())
        cur = ""
    return "!![" + ("\n" + pad).join(lines) + "]"


def sym_matrix_literal(M, indent=6):
    return matrix_literal(M, indent, diag=lambda i, j, x: f"t - {x}" if i == j else f"({-x})")


CHUNK = 60         # digits per chunk in decomposed big literals
PLAIN_DIGITS = 80  # a plain (undecomposed) literal renders fine up to this


def pos_chunks(x):
    """Decimal string chunks of |x| (first CHUNK digits, last maybe shorter),
    or None when the plain literal is short enough for every emission site."""
    s = str(abs(x))
    if len(s) <= PLAIN_DIGITS:
        return None
    return [s[i:i + CHUNK] for i in range(0, len(s), CHUNK)]


def term_chunks(c, suffix):
    """Chunking decision for a P coefficient `c` carrying `suffix`
    (` * (X : ℤ[X]) ^ e`, or "" for the constant term): None when the plain
    `- C (c){suffix}` term fits a continuation line, else the chunk list.
    p_literal and the hmap rw MUST decide identically (the rw rewrites the
    exact expression P contains)."""
    body = f"C ({c})" if c >= 0 else f"- C ({-c})"
    if 6 + len(body) + len(suffix) + 2 <= WIDTH:
        return None
    s = str(abs(c))
    return [s[i:i + CHUNK] for i in range(0, len(s), CHUNK)]


def chunk_expr_tokens(chs):
    """Token lines of the positive expression `c0 * 10 ^ E0 + c1 * 10 ^ E1 …`.
    The SAME token sequence is used inside `C (…)` in P and inside the hmap
    `show ((… : ℤ) : ZMod ℓ)` rewrite (rw matches syntactically)."""
    toks = []
    for j, ch in enumerate(chs):
        e = sum(len(c) for c in chs[j + 1:])
        core = ch if e == 0 else f"{ch} * 10 ^ {e}"
        toks.append(core if j == 0 else f"+ {core}")
    return toks


def flat_expr_lines(v, lead, cont):
    """Physical lines of a (possibly negative) integer rendered as
    `-c0 * 10 ^ E0 - c1 …` (flat; no unit parentheses), `lead` before the
    first line and `cont` before the rest; plain literal when it fits."""
    chs = pos_chunks(v)
    if chs is None:
        return [f"{lead}{v}"]
    toks = chunk_expr_tokens(chs)
    if v < 0:
        toks = [toks[0]] + [t.replace("+ ", "- ", 1) for t in toks[1:]]
        toks[0] = "-" + toks[0]
    return [lead + toks[0]] + [cont + t for t in toks[1:]]


def p_literal(cp, n):
    # term units: plain strings (packed like the dim-6 output) or pre-rendered
    # multi-line blocks for coefficients whose literal does not fit on a line
    units = []
    for i, c in enumerate(cp):
        if i == 0:
            # leading term as C 1 * X^n: after mapping, both sides of hmap carry
            # the identical atom C ((1 : ℤ) : ZMod ℓ) (ring_nf cannot equate
            # `C ↑1` with the bare numeral 1)
            units.append(("plain", f"C (1) * (X : ℤ[X]) ^ {n}"))
            continue
        suffix = f" * (X : ℤ[X]) ^ {n - i}" if i < n else ""
        chs = term_chunks(c, suffix)
        if chs is None:
            units.append(("plain", (f"C ({c})" if c >= 0 else f"- C ({-c})") + suffix))
        else:
            toks = chunk_expr_tokens(chs)
            block = [("- C (" if c < 0 else "C (")] + \
                [f"  {t}" for t in toks[:-1]] + [f"{toks[-1]}){suffix}"]
            units.append(("block", block))
    # greedy assembly: plain terms pack exactly like the earlier wrap_terms
    # (byte-identical when every coefficient is plain, i.e. dim 6); a block
    # flushes the current line and stands on its own physical lines
    pad = " " * 6
    out, cur = [], ""
    for idx, (kind, payload) in enumerate(units):
        sep = "" if idx == len(units) - 1 else " + "
        if kind == "plain":
            budget = WIDTH if not out else WIDTH - 6
            if cur and len(cur) + len(payload) + len(sep) > budget:
                out.append(cur.rstrip())
                cur = ""
            cur += payload + sep
        else:
            if cur:
                out.append(cur.rstrip())
                cur = ""
            out.extend([pad + payload[0]] + [pad + l for l in payload[1:-1]])
            cur = pad + payload[-1] + sep
    out.append(cur.rstrip())
    return ("\n" + pad).join(out)


def wrap_name(k):
    return f"MaedaWeight{k}"


def emit_weight(w):
    k, n = w["k"], w["dim"]
    M, cp = w["matrix"], w["charpoly"]
    ell, ell2 = w["cert_ell"], w["cert2_ell"]
    N = 2 * n + 1

    # --- regression: recompute the matrix and charpoly from the probe engine ---
    d2, Mat2, cp2 = msp.maeda_data(k)
    assert d2 == n and Mat2 == M and cp2 == cp, f"regression failed at k={k}"

    basis = []
    coeffs = []
    tdata = []
    for i0 in range(n):
        a, b = G(k - 12 * (i0 + 1))
        f, t = t2_coeffs(k, n, i0, a, b, N)
        basis.append((i0, a, b))
        coeffs.append(f)
        tdata.append(t)
        # the leading coefficient of f_{i0} sits at index i0+1 and is 1
        assert f[i0 + 1] == 1 and all(f[m] == 0 for m in range(0, i0 + 1)), (k, i0)

    out = []
    P = out.append
    wname = wrap_name(k)
    kq = f"(({k} : ℕ) : ℤ)"

    P(f"/-! ### Weight {k} (dim {n}) -/")
    P(f"namespace {wname}")
    P("")

    # --- basis and coefficient machinery ---
    for (i0, a, b), f in zip(basis, coeffs):
        j = i0 + 1
        P(f"/-- `Δ^{j} E₄^{a} E₆^{b}`. -/")
        P(f"noncomputable def f{j} : CuspForm 𝒮ℒ {kq} :=")
        P(f"  prodForm _ {i0} {a} {b} (by norm_num)")
        P("")
        P(f"lemma c{j} (m : ℕ) : (qExpansion 1 f{j}).coeff m = seqP {i0} {a} {b} m :=")
        P(f"  prodForm_coeff _ _ _ _ _ m")
        P("")
        P(f"lemma L{j}c : seqPLc {i0} {a} {b} {N} =")
        P(f"    {lean_list(f, 4)} := by")
        P("  decide +kernel")
        P("")
        P(f"lemma L{j} : seqPL {i0} {a} {b} {N} =")
        P(f"    {lean_list(f, 4)} := by")
        P(f"  rw [← seqPLc_eq (by norm_num)]")
        P(f"  exact L{j}c")
        P("")
        for m in range(1, 2 * n + 1):
            for _s in coeff_stmt(f"lemma q{j}_{m} : (qExpansion 1 f{j}).coeff {m}", f[m]):
                P(_s)
            P(f"  rw [c{j}, seqP_getD (N := {N}) (by norm_num), L{j}]")
            P("  norm_num [List.getD_cons_succ, List.getD_cons_zero]")
            P("")

    # --- T2 and its image coefficients ---
    P("/-- `T₂` on this weight. -/")
    P(f"noncomputable def T2 := heckeTPₗ {kq} Nat.prime_two")
    P("")
    for (i0, a, b), t in zip(basis, tdata):
        j = i0 + 1
        for m in range(1, n + 1):
            extra = f", q{j}_{m // 2}" if m % 2 == 0 else ""
            for _s in coeff_stmt(f"lemma t{j}_{m} : (qExpansion 1 (T2 f{j})).coeff {m}", t[m]):
                P(_s)
            P(f"  rw [T2, heckeT2_coeff (by norm_num)]")
            P(f"  norm_num [q{j}_{2 * m}{extra}]")
            P("")

    # --- A/X tables ---
    fb_args = ", ".join(f"f{j}" for j in range(1, n + 1))
    P("/-- The basis as an ℕ-indexed function (concrete indices reduce by `rfl`; the")
    P("catch-all is never used: `charpoly_dimN` only reads `fb i` for `i < n`). -/")
    P(f"noncomputable def fb : ℕ → CuspForm 𝒮ℒ {kq}")
    for i0 in range(n):
        P(f"  | {i0} => f{i0 + 1}")
    P("  | _ => 0")
    P("")
    P("/-- `Atab i j` = coefficient of `q^(j+1)` in `f i` for `i < j` (0 elsewhere). -/")
    P(f"def Atab : ℕ → ℕ → ℂ")
    for (i0, a, b), f in zip(basis, coeffs):
        for jj in range(i0 + 1, n):
            P(f"  | {i0}, {jj} => ({f[jj + 1]} : ℂ)")
    P("  | _, _ => 0")
    P("")
    P("/-- `Xtab i m` = coefficient of `q^(m+1)` in `T₂ (f i)`. -/")
    P(f"def Xtab : ℕ → ℕ → ℂ")
    for i0, t in enumerate(tdata):
        for m in range(n):
            P(f"  | {i0}, {m} => ({t[m + 1]} : ℂ)")
    P("  | _, _ => 0")
    P("")

    # --- finrank ---
    P("lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ %s) = %d := by" % (kq, n))
    P("  apply Module.finrank_eq_of_rank_eq")
    P("  rw [CuspForm.discriminantEquiv.rank_eq]")
    P(f"  have h := ModularForm.dimension_level_one {k - 12} (by decide)")
    P("  norm_num [Nat.ModEq] at h")
    P("  exact_mod_cast h")
    P("")

    # --- hypothesis discharges ---
    for i0 in range(n):
        pass  # per-case bullets are emitted inside the four lemmas below

    P("/-- `charpoly_dimN` hypothesis: the basis is in echelon form (zeros). -/")
    P("lemma hzero : ∀ (i m : ℕ), i < %d → 1 ≤ m → m ≤ i →" % n)
    P(f"    (qExpansion 1 (fb i)).coeff m = (0 : ℂ) := by")
    P("  intro i m hi h1 h2")
    P("  interval_cases i")
    for i0 in range(n):
        P(f"  · simp only [fb]")
        if i0 == 0:
            P("    exact (by omega : False).elim")
        else:
            P(f"    interval_cases m")
            for m in range(1, i0 + 1):
                j = i0 + 1
                P(f"    · rw [c{j}, seqP_getD (N := {N}) (by norm_num), L{j}]")
                P("      norm_num [List.getD_cons_succ, List.getD_cons_zero]")
    P("")
    P("/-- `charpoly_dimN` hypothesis: the diagonal is `1`. -/")
    P("lemma hone : ∀ i : ℕ, i < %d → (qExpansion 1 (fb i)).coeff (i + 1) = (1 : ℂ) := by" % n)
    P("  intro i hi")
    P("  interval_cases i")
    for i0 in range(n):
        j = i0 + 1
        P(f"  · simp only [fb]")
        P(f"    exact q{j}_{j}")
    P("")
    P("/-- `charpoly_dimN` hypothesis: the strict upper coefficients. -/")
    P("lemma hA : ∀ (i j : ℕ), i < j → j < %d →" % n)
    P("    (qExpansion 1 (fb i)).coeff (j + 1) = Atab i j := by")
    P("  intro i j hij hjn")
    P(f"  have hib : i < {n} := by omega")
    P("  interval_cases i")
    for i0 in range(n):
        j = i0 + 1
        P(f"  · simp only [fb]")
        P(f"    interval_cases j")
        for jj in range(i0 + 1, n):
            P(f"    · rw [c{j}, seqP_getD (N := {N}) (by norm_num), L{j}]")
            P("      norm_num [List.getD_cons_succ, List.getD_cons_zero]")
            P("      rfl")
    P("")
    P("/-- `charpoly_dimN` hypothesis: the T₂-image coefficients. -/")
    P("lemma hX : ∀ (i m : ℕ), i < %d → m < %d →" % (n, n))
    P("    (qExpansion 1 (T2 (fb i))).coeff (m + 1) = Xtab i m := by")
    P("  intro i m hi hm")
    P("  interval_cases i")
    for i0 in range(n):
        j = i0 + 1
        P(f"  · simp only [fb]")
        P(f"    interval_cases m")
        for m in range(n):
            P(f"    · rw [t{j}_{m + 1}]")
            P("      rfl")
    P("")

    # --- the literal matrix, P, determinants, evaluations ---
    P("/-- The matrix of `T₂` in the echelon basis (census data, regression-checked). -/")
    P(f"def M : Matrix (Fin {n}) (Fin {n}) ℤ :=")
    P("      " + matrix_literal(M))
    P("")
    P("/-- The translated matrices `t·1 − M`, as an explicit literal (symbolic in `t`). -/")
    P(f"def MT (t : ℤ) : Matrix (Fin {n}) (Fin {n}) ℤ :=")
    P("      " + sym_matrix_literal(M))
    P("")
    P("/-- One-time symbolic bridge, reused by all determinant lemmas. -/")
    P("theorem scalar_sub_M (t : ℤ) : Matrix.scalar (Fin %d) t - M = MT t := by" % n)
    P("  ext a b")
    P("  simp only [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.sub_apply, M, MT]")
    P("  fin_cases a <;> fin_cases b <;> simp")
    P("")
    P("/-- The characteristic polynomial of `T₂` (descending literal). -/")
    P("noncomputable def P : ℤ[X] :=")
    P(f"  {p_literal(cp, n)}")
    P("")
    P(f"theorem P_natDegree : P.natDegree = {n} := by unfold P; compute_degree!")
    P("")
    P("theorem P_monic : P.Monic := by unfold P; monicity!")
    P("")
    vals = []
    for t in range(n + 1):
        m2 = [[(t if i == j2 else 0) - M[i][j2] for j2 in range(n)] for i in range(n)]
        v = msp.bareiss_det(m2)
        ev = 0
        for c in cp:
            ev = ev * t + c
        assert v == ev, (k, t, v, ev)
        vals.append(v)
    for t, v in enumerate(vals):
        P(f"/-- `det (t·1 − M)` at `t = {t}`, by the certified Bareiss echelon decomposition. -/")
        head = f"theorem det_{t} : (Matrix.scalar (Fin {n}) ({t} : ℤ) - M).det"
        if len(head) + 3 + len(str(abs(v))) + 7 <= WIDTH:
            P(f"{head} = {v} := by")
        else:
            P(head)
            ls = flat_expr_lines(v, "     = ", "      ")
            ls[-1] += " := by"
            for l in ls:
                P(l)
        P(f"  rw [scalar_sub_M]")
        P(f"  simp only [MT]")
        P(f"  eval_det")
        if pos_chunks(v) is not None:
            # the RHS is a chunked `c0 * 10 ^ e0 + c1 …` literal; `eval_det`
            # reduces the det side to the flat numeral and leaves the pure
            # arithmetic identity for `norm_num` (both sides fully numeric)
            P(f"  norm_num")
        P("")
    for t, v in enumerate(vals):
        head = f"theorem ev_{t} : P.eval ({t} : ℤ)"
        if len(head) + 3 + len(str(abs(v))) + 7 <= WIDTH:
            P(f"{head} = {v} := by")
        else:
            P(head)
            ls = flat_expr_lines(v, "     = ", "      ")
            ls[-1] += " := by"
            for l in ls:
                P(l)
        P("  norm_num [P, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,")
        P("      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_neg]")
        P("")
    P("/-- Assembly: the n+1 evaluation points, discharged per case. -/")
    P("theorem hevals : ∀ i : Fin %d, P.eval ((i : ℕ) : ℤ)" % (n + 1))
    P("      = (Matrix.scalar (Fin %d) ((i : ℕ) : ℤ) - M).det := by" % n)
    P("  intro i")
    P("  fin_cases i")
    for t in range(n + 1):
        P(f"  · change P.eval ({t} : ℤ)")
        P(f"      = (Matrix.scalar (Fin {n}) ({t} : ℤ) - M).det")
        P(f"    rw [ev_{t}, det_{t}]")
    P("")
    # per-entry helper theorems: the back-substitution is STAGED — one lemma
    # per (column, row-count) holding the first j coordinates as a literal
    # list, each proved from the previous stage by a ONE-step `coordsAux`
    # unfold.  Letting `simp only [coordsAux]` unfold the whole cascade
    # exhausts the 200k heartbeat budget at the deepest rows from dim 9 on
    # (entry_8_{4..8}); splitting the declaration is the sanctioned fix
    # (TauCeti forbids raising any option)
    def clist_lines(vals, indent):
        """A `[((v : ℤ) : ℂ), …]` literal wrapped to WIDTH (elements are
        ~20–50 chars each; dim-10 lists need multi-line)."""
        pad = " " * indent
        items = [f"(({v} : ℤ) : ℂ)" for v in vals]
        lines, cur = [], "["
        for it in items:
            sep = "" if cur == "[" else ", "
            if len(pad + cur + sep + it) > WIDTH - 1 and cur != "[":
                lines.append(cur + ",")
                cur = it
            else:
                cur += sep + it
        lines.append(cur + "]")
        return [pad + lines[0]] + [pad + l for l in lines[1:]]

    for a in range(n):
        col = [M[c][a] for c in range(n)]
        for j in range(1, n + 1):
            ls = clist_lines(col[:j], 4)
            P(f"theorem Lv{a}_{j} : coordsAux Atab (fun m => Xtab {a} m) {j} =")
            for l in ls[:-1]:
                P(l)
            if len(ls[-1]) + 7 > WIDTH:
                P(ls[-1])
                P("      := by")
            else:
                P(ls[-1] + " := by")
            if j == 1:
                # range 0: the sum vanishes, so Atab never fires
                P("  simp only [coordsAux, Xtab, Finset.sum_range_zero, List.nil_append]")
                P("  norm_num")
            else:
                # `change` (not `show`): the unfold changes the goal, and
                # linter.style.show rejects goal-changing `show`s
                P(f"  change coordsAux Atab (fun m => Xtab {a} m) {j-1}")
                P(f"      ++ [Xtab {a} {j-1} - ∑ i ∈ Finset.range {j-1},")
                P(f"      Atab i {j-1} * (coordsAux Atab (fun m => Xtab {a} m) {j-1}).getD i 0] =")
                for l in clist_lines(col[:j], 6):
                    P(l)
                P(f"  rw [Lv{a}_{j-1}]")
                # a 1-element prefix needs only getD_cons_zero (succ would be
                # an unused simp argument — the style linter rejects it)
                succ = "List.getD_cons_succ, " if j >= 3 else ""
                P("  simp only [Atab, Xtab, Finset.sum_range_succ, Finset.sum_range_zero,")
                P(f"      {succ}List.getD_cons_zero, List.nil_append, List.cons_append]")
                P("  norm_num")
            P("")
    for c in range(n):
        for a in range(n):
            P(f"theorem entry_{c}_{a} : coordN Atab (fun m => Xtab {a} m) {c}")
            P(f"      = (({M[c][a]} : ℤ) : ℂ) := by")
            P("  simp only [coordN]")
            P(f"  rw [Lv{a}_{c+1}]")
            P("  rfl")
            P("")
    P("/-- **The characteristic polynomial of `T₂` on this weight.** -/")
    P("theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by")
    P(f"  have hdim := finrank_eq")
    P(f"  have hn : 0 < {n} := by norm_num")
    P(f"  rw [charpoly_dimN hn hdim fb Atab Xtab hzero hone hA T2 hX,")
    P("      ← CharpolyEngine.charpoly_of_eval_eq M P P_natDegree hevals, ← Matrix.charpoly_map]")
    P("  congr 1")
    P("  ext j i")
    P("  fin_cases j <;> fin_cases i")
    for c in range(n):
        for a in range(n):
            head = f"  · change coordN Atab (fun m => Xtab {a} m) {c}"
            tail = f" = (({M[c][a]} : ℤ) : ℂ)"
            if len(head) + len(tail) <= WIDTH:
                P(head + tail)
            else:
                P(head)
                P(f"      {tail}")
            P(f"    exact entry_{c}_{a}")
    P("")

    # --- Rabin certificates and the irreducibility theorem ---
    fle = [c % ell for c in cp[::-1]]
    F = (ell ** n).bit_length()
    assert len(fle) == n + 1 and fle[-1] == 1
    # sanity-check the h1 certificate with the reflected-engine model
    top = reflected_powmod(ell, fle, ell ** n)
    assert msp.pnorm(list(top)) == [0, 1], (k, ell, top)
    h2s = []
    for q in prime_divisors(n):
        hq = msp.psub_x(reflected_powmod(ell, fle, ell ** (n // q)), ell)
        g = msp.pgcd(list(fle), list(hq), ell)
        g = msp.pnorm(list(g))
        assert len(g) == 1, (k, q, g)
        steps = reflected_gcd_steps(ell, fle, hq)
        W = max(steps + 2, len(fle) + 4)
        h2s.append((q, W))
    fle2 = [c % ell2 for c in cp[::-1]]
    F2 = (ell2 ** n).bit_length()
    top2 = reflected_powmod(ell2, fle2, ell2 ** n)
    assert msp.pnorm(list(top2)) == [0, 1], (k, ell2, top2)

    P("/-- The characteristic polynomial mod the certificate prime (little-endian). -/")
    P(f"noncomputable def fr : List ℤ := {lean_list(fle, 2)}")
    P("")
    P("lemma hmap : P.map (Int.castRingHom (ZMod %d)) = RabinCert.toPoly %d fr := by" % (ell, ell))
    P("  simp only [P, RabinCert.toPoly_nil, RabinCert.toPoly_cons, fr,")
    P("      Polynomial.map_C, Polynomial.map_X, Polynomial.map_add, Polynomial.map_mul,")
    P("      Polynomial.map_pow, Int.coe_castRingHom, ← Polynomial.C_neg]")
    # per-coefficient kernel casts: c mod ell (the leading C 1 needs no rewrite)
    rw_items = []
    for i, c in enumerate(cp):
        if i == 0:
            continue
        suffix = f" * (X : ℤ[X]) ^ {n - i}" if i < n else ""
        chs = term_chunks(c, suffix)  # SAME decision as P's literal (syntactic match)
        if chs is None:
            head = f"show (({c} : ℤ) : ZMod {ell})"
            tail = f" = ({c % ell} : ZMod {ell}) from by decide +kernel"
            if 6 + len(head) + len(tail) <= WIDTH:
                rw_items.append(head + tail)
            elif 6 + len(head) <= WIDTH:
                rw_items.append(head + "\n          " + tail)
            else:  # the coefficient literal alone nearly fills the line: split the cast
                rw_items.append(f"show (({c} : ℤ)\n          : ZMod {ell})" + tail)
        else:
            # chunked coefficient: the pattern must be syntactically the cast of
            # NEGATED unit expression (what <- C_neg + map_C leave in the goal);
            # the inner tokens come from the same builder as P's C (…) literal
            toks = chunk_expr_tokens(chs)
            op = "show ((- (" if c < 0 else "show (("
            cl = ") : ℤ) : ZMod %d)" % ell if c < 0 else " : ℤ) : ZMod %d)" % ell
            lines = ["      " + op + toks[0]]
            lines += ["            " + t for t in toks[1:]]
            lines[-1] += cl
            lines.append("          = (%d : ZMod %d) from by decide +kernel" % (c % ell, ell))
            rw_items.append("\n".join(lines))
    P("  rw [" + ",\n      ".join(rw_items) + "]")
    P("  ring_nf")
    P("")
    P("lemma hmon' : (RabinCert.toPoly %d fr).Monic := by" % ell)
    P("  simp only [RabinCert.toPoly_nil, RabinCert.toPoly_cons, fr, mul_zero, add_zero]")
    P("  monicity!")
    P("")
    P(f"lemma hnd : (RabinCert.toPoly {ell} fr).natDegree = {n} := by")
    P("  simp only [RabinCert.toPoly_nil, RabinCert.toPoly_cons, fr, mul_zero, add_zero]")
    P("  compute_degree!")
    P("")
    P(f"lemma hF : {ell} ^ {n} < 2 ^ {F} := by norm_num")
    P("")
    P(f"lemma h1 : RabinCert.zpxw {ell} fr (RabinCert.bitsOf {F} ({ell} ^ {n})) [1] = [0, 1] :=")
    P("  by decide +kernel")
    P("")
    for q, W in h2s:
        P(f"lemma h2_{q} : ∃ w : ℕ, RabinCert.zpgcd {ell} w fr")
        P(f"      (RabinCert.zpxwsubX {ell} fr {F} ({ell} ^ ({n} / {q}))) = [1] :=")
        P(f"  ⟨{W}, by decide +kernel⟩")
        P("")
    P("lemma h2 : ∀ q : ℕ, q.Prime → q ∣ %d → ∃ w : ℕ," % n)
    P(f"      RabinCert.zpgcd {ell} w fr")
    P(f"      (RabinCert.zpxwsubX {ell} fr {F} ({ell} ^ ({n} / q))) = [1] := by")
    P("  intro q hq hq2")
    P(f"  have hqb : q ≤ {n} := Nat.le_of_dvd (by norm_num) hq2")
    P("  interval_cases q")
    # interval_cases yields the n+1 cases q = 0 .. n (primality/divisibility
    # literals are NOT auto-closed); refute composites via hq, primes not
    # dividing n via hq2 (q = 6 divides 6, so refute via primality there)
    hq_qs = {q for q, _ in h2s}
    for q in range(n + 1):
        if q in hq_qs:
            P(f"  · exact h2_{q}")
        elif is_prime(q):
            P("  · exact absurd hq2 (by decide)")
        else:
            P("  · exact absurd hq (by decide)")
    P("")
    P(f"/-- The second certificate prime (sanity decide, not used by `maeda`). -/")
    P(f"noncomputable def fr2 : List ℤ := {lean_list(fle2, 2)}")
    P("")
    P(f"lemma h1_2 : RabinCert.zpxw {ell2} fr2 (RabinCert.bitsOf {F2} ({ell2} ^ {n})) [1]")
    P(f"      = [0, 1] :=")
    P("  by decide +kernel")
    P("")
    P("/-- **Maeda's conjecture (irreducibility) in this weight.** -/")
    P("theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) :=")
    P(f"  haveI : Fact (Nat.Prime {ell}) := ⟨by norm_num⟩")
    P(f"  RabinCert.irreducible_of_rabin_int P_monic hmap hmon' hnd (by norm_num) hF h1 h2")
    P("")
    P(f"end {wname}")
    P("")
    return "\n".join(out)


HEADER = """import MathProof.ModularForms.CharpolyDimN
import MathProof.ModularForms.CharpolyEngine
import MathProof.ModularForms.RabinCert
import MathProof.ModularForms.MaedaCertC

/-!
# Maeda's conjecture (irreducibility), dimension {dim}: weights {klist}

Generated by `tools/gen_maedan.py` from
`research/iteration20/data/maeda_dim6_10.json` (byte-identical re-runs; do not
hand-edit).  For each weight the file provides the echelon basis, the literal
T₂-matrix with its characteristic polynomial (certified `eval_det`
determinants + interpolation through `CharpolyEngine.charpoly_of_eval_eq`),
and Rabin irreducibility certificates (`RabinCert.irreducible_of_rabin_int`).

Everything is light: `decide +kernel` certificates, no `set_option`, and no
module in this file is an ancestor of the heavy `MaedaGalois5Defs` chain.
-/

open UpperHalfPlane ModularForm CuspForm Polynomial MaedaLevelOne
open scoped MatrixGroups

"""


def emit_dim(dim):
    weights = sorted(w["k"] for w in DATA if w["dim"] == dim)
    assert len(weights) == 6, (dim, weights)
    body = HEADER.format(dim=dim, klist=", ".join(map(str, weights)))
    for k in weights:
        body += emit_weight(BY_K[k])
    return body


def main():
    check = "--check" in sys.argv
    only = None
    if "--only" in sys.argv:
        only = int(sys.argv[sys.argv.index("--only") + 1])
    dims = [only] if only else [6, 7, 8, 9, 10]
    for dim in dims:
        text = emit_dim(dim)
        path = ROOT / f"MathProof/ModularForms/MaedaDim{dim}Weights.lean"
        if check:
            old = path.read_text() if path.exists() else ""
            if old != text:
                print(f"NOT byte-identical: {path}")
                sys.exit(1)
            print(f"byte-identical: {path}")
        else:
            path.write_text(text)
            print(f"wrote {path} ({len(text.splitlines())} lines)")


if __name__ == "__main__":
    main()
