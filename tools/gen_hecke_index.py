#!/usr/bin/env python3
"""Generator for `MathProof/ModularForms/HeckeIndex{Small,}Weights.lean` (iteration 23, b2).

For each of the 54 level-one weights `24 ≤ k ≤ 134` with `2 ≤ dim S_k ≤ 10`
this emits, on the LANDED fb-coordinate literals (the G1 audit's re-pinning):

  * `Ik`   — the index `I_k = |det A|` (chunked literal),
  * `A`    — the Miller-coordinate matrix `A i j = a_{2^i}(f_j)` (chunked),
  * `det_A` — `A.det = ±I_k` by the certified Bareiss `eval_det` route
    (G3-measured at the worst dim-10 weight: seconds),
  * `hIkq` — `((Ik : ℤ) : ℚ) ≠ 0`,
  * `wp`   — the Cramer weights `w' = I_k · w` (chunked arms),
  * `scaled` — the entrywise kernel certificate
    `∑ wp j • M₂^j = Ik • M₃` (`ext`/`fin_cases` + `decide +kernel` per cell,
    never matrix-level decide),
  * `op_id` — the basis-independent operator identity
    `∑ (wp j : ℂ) • T₂^j = (Ik : ℂ) • T₃` via `HeckeIndex.int_poly_of_dimN`,
  * for the 48 weights with `D ≠ 1`: `Dn`, `scaled_idN` (the landed
    HeckeRational certificate re-stated over `Dn`), `hDq`, `hrepD`/`hrepI`
    (via `HeckeIndex.aeval_div_witness`), `minpoly_nd` (via
    `HeckeGeneratedByT2.minpoly_eq_charpoly_of_map_of_irreducible` + the
    per-weight `maeda` theorem), the Bézout witness `bez`/`bezc` for
    `gcd(N₀..N₉, D) = 1` (balanced extgcd tree, G1 strategy), and the
    composite `D_dvd_Ik : Dn ∣ Ik` via `HeckeIndex.den_dvd_index`;
  * for the six dim-2 weights (`D = 1`): the composite is `one_dvd`.

Everything is light: no `set_option`, entrywise `decide +kernel` only.
Data source: `research/iteration23/hecke-index/index_data.json` (the G1
audit's re-pinned values).  `--check` verifies byte-identical regeneration.
"""
import json
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MF = ROOT / "MathProof" / "ModularForms"
DATA = ROOT / "research" / "iteration23" / "hecke-index" / "index_data.json"
OUT = MF / "HeckeIndexWeights.lean"

WIDTH = 98          # linter.style.longLine limit is 100; keep a margin
PLAIN_DIGITS = 80   # plain literal renders fine up to this many digits
HORNER_CHUNK = 74   # Horner chunk width (gen_hecke_rat convention)


def int_lines(v):
    """Physical lines of the chunked ℤ expression for `v` (Horner base 10^74
    past PLAIN_DIGITS; every explicit power is 74 ≤ 256)."""
    if abs(v) < 10 ** PLAIN_DIGITS:
        return [str(v)]
    s = str(abs(v))
    chunks = []
    while s:
        chunks.insert(0, str(int(s[-HORNER_CHUNK:])))
        s = s[:-HORNER_CHUNK]
    head = chunks[0] + f" * 10 ^ {HORNER_CHUNK}" if len(chunks) > 1 else chunks[0]
    lines = ["(" * (len(chunks) - 1) + head]
    for j, ch in enumerate(chunks[1:], 1):
        tail = "" if j == len(chunks) - 1 else f" * 10 ^ {HORNER_CHUNK}"
        lines.append(f"+ {ch}){tail}")
    if v < 0:
        lines[0] = "-(" + lines[0]
        lines[-1] = lines[-1] + ")"
    return lines


def wrap_tokens(text, first_indent, cont_indent):
    """Greedily wrap a token stream to WIDTH."""
    out, cur = [], first_indent.rstrip()
    for tok in text.split(" "):
        if cur.strip() and len(cur) + 1 + len(tok) > WIDTH:
            out.append(cur)
            cur = cont_indent + tok
        else:
            cur = cur + (" " if cur.strip() else "") + tok
    out.append(cur)
    return out


def wrap_doc(doc, indent=""):
    """Wrap a doc-comment body to WIDTH lines `/-- ... -/`."""
    words = doc.split(" ")
    out, cur = [], "/--"
    for w in words:
        if len(cur) + 1 + len(w) + 3 > WIDTH:
            out.append(cur)
            cur = indent + "  " + w
        else:
            cur = cur + (" " if cur != "/--" else " ") + w
    out.append(cur + " -/")
    return out


def chunked_def(name, v, doc, indent=""):
    """Lines of `def name : ℤ := <chunked v>`."""
    out = wrap_doc(doc, indent) if doc else []
    out.append(f"{indent}def {name} : ℤ :=")
    for ln in int_lines(v):
        out.append(f"{indent}  " + ln if not ln.startswith("-(") else f"{indent}  " + ln)
    return out


def matrix_def(name, A, doc, lines_of=None):
    """Lines of `def name : Matrix (Fin n) (Fin n) ℤ := !![...]` (chunked)."""
    n = len(A)
    out = wrap_doc(doc)
    out.append(f"def {name} : Matrix (Fin {n}) (Fin {n}) ℤ := !![")
    for i, row in enumerate(A):
        toks = []
        for e in row:
            ls = (lines_of or int_lines)(e)
            toks.append(ls[0] if len(ls) == 1 else "(" + " ".join(ls) + ")")
        term = ";" if i < n - 1 else "]"
        lines = wrap_tokens(", ".join(toks) + term, "  ", "   ")
        out.extend(lines)
    return out


def seq_def(name, vals, doc):
    """Lines of `def name : ℕ → ℤ | 0 => .. | _ => 0` (chunked arms)."""
    out = wrap_doc(doc)
    out.append(f"def {name} : ℕ → ℤ")
    for i, v in enumerate(vals):
        ls = int_lines(v)
        first = f"  | {i} => "
        wrapped = wrap_tokens(" ".join(ls), first, "      ")
        out.extend(wrapped)
    out.append("  | _ => 0")
    return out


def det_exact(A):
    n = len(A)
    M = [[Fraction(x) for x in row] for row in A]
    det = Fraction(1)
    for i in range(n):
        p = next((r for r in range(i, n) if M[r][i] != 0), None)
        if p is None:
            return 0
        if p != i:
            M[i], M[p] = M[p], M[i]
            det = -det
        det *= M[i][i]
        for r in range(i + 1, n):
            f = M[r][i] / M[i][i]
            for c in range(i, n):
                M[r][c] -= f * M[i][c]
    assert det.denominator == 1
    return int(det)


def extgcd(a, b):
    """(g, s, t) with s*a + t*b = g."""
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    return old_r, old_s, old_t


def bezout_tree(Ns, D):
    """(e, c) with ∑ e_i N_i + c D = 1; balanced extgcd tree (G1 strategy)."""
    items = [(N, {i: 1}) for i, N in enumerate(Ns)]
    while len(items) > 1:
        nxt = []
        for i in range(0, len(items) - 1, 2):
            (a, ca), (b, cb) = items[i], items[i + 1]
            g, s, t = extgcd(a, b)
            cd = {}
            for k in set(ca) | set(cb):
                v = s * ca.get(k, 0) + t * cb.get(k, 0)
                if v:
                    cd[k] = v
            nxt.append((g, cd))
        if len(items) % 2:
            nxt.append(items[-1])
        items = nxt
    g, coeffs = items[0]
    g2, s, t = extgcd(g, D)
    assert g2 == 1
    e = {k: s * v for k, v in coeffs.items() if s * v}
    tot = sum(e.get(i, 0) * N for i, N in enumerate(Ns)) + t * D
    assert tot == 1
    return e, t


def maxdigits(*vals):
    return max((len(str(abs(v))) for v in vals), default=0)


def emit_weight(k, w, report):
    n = w["dim"]
    Ik = w["Ik"]
    A = w["A"]
    wp = w["wp"]
    N = w["N"]
    D = w["D"]
    assert len(A) == n and all(len(r) == n for r in A), k
    assert len(wp) == n and len(N) == n, k
    det = det_exact(A)
    assert abs(det) == Ik, (k, det, Ik)
    sign = "" if det > 0 else "-"

    # name templates per weight class
    if n >= 6:
        t2ns, t3ns, ratns = f"MaedaWeight{k}", f"MaedaT3Weight{k}", f"HeckeRatWeight{k}"
        T2, T3 = f"{t2ns}.T2", f"{t3ns}.T3"
        X2, X3 = f"{t2ns}.Xtab", f"{t3ns}.Xtab"
        hX2, hX3 = f"{t2ns}.hX", f"{t3ns}.hX"
        M2, M3 = f"{t2ns}.M", f"{t3ns}.M"
        hM2, hM3 = f"{ratns}.hM2", f"{ratns}.hM3"
        cert, heckerat_scaled = f"{ratns}.cert", f"{ratns}.scaled_id"
        fr, fb, Atab = f"{t3ns}.finrank_eq", f"{t3ns}.fb", f"{t3ns}.Atab"
        hzero, hone, hA = f"{t3ns}.hzero", f"{t3ns}.hone", f"{t3ns}.hA"
        pnd = f"exact {t2ns}.P_natDegree"
    else:
        t2ns, t3ns, ratns = f"MaedaWeight{k}", f"MaedaT3Weight{k}", f"HeckeRatWeight{k}"
        T2, T3 = f"{ratns}.T2", f"{t3ns}.T3"
        X2, X3 = f"{ratns}.Xtab2", f"{t3ns}.Xtab"
        hX2, hX3 = f"{ratns}.hX2", f"{t3ns}.hX"
        M2, M3 = f"{ratns}.M2", f"{t3ns}.M"
        hM2, hM3 = f"{ratns}.hM2", f"{ratns}.hM3"
        cert, heckerat_scaled = f"{ratns}.cert", f"{ratns}.scaled_id"
        fr, fb, Atab = f"{t3ns}.finrank_eq", f"{t3ns}.fb", f"{t3ns}.Atab"
        hzero, hone, hA = f"{t3ns}.hzero", f"{t3ns}.hone", f"{t3ns}.hA"
        pnd = f"unfold {t2ns}.P; compute_degree!"

    L = []
    L.append(f"/-! ### Weight {k} (dim {n}) -/")
    L.append(f"namespace HeckeIndexWeight{k}")
    L.append("")
    L.extend(chunked_def("Ik", Ik, f"The index `I_k = |det A|` at weight {k} (G1 audit)."))
    L.append("")
    L.extend(matrix_def("A", A,
                        f"The Miller-coordinate matrix at weight {k}: `A i j = a_(2^i)(f_j)` "
                        "(G1 audit, Miller strategy (a))."))
    L.append("")
    L.append("/-- `det A = ±I_k` (the signed G1 value; certified Bareiss `eval_det`). -/")
    L.append(f"theorem det_A : A.det = {sign}Ik := by")
    L.append("  simp only [A]")
    L.append("  eval_det")
    L.append("  norm_num [Ik]")
    L.append("")
    L.append("theorem hIkq : ((Ik : ℤ) : ℚ) ≠ 0 := by norm_num [Ik]")
    L.append("theorem hIkc : ((Ik : ℤ) : ℂ) ≠ 0 := by norm_num [Ik]")
    L.append("")
    L.extend(seq_def("wp", wp, f"The Cramer weights `w' = I_k · w` at weight {k} (G1 audit)."))
    L.append("")
    L.append(f"theorem scaled : (∑ j ∈ Finset.range {n}, wp j • {M2} ^ j)")
    L.append(f"    = Ik • {M3} := by")
    L.append("  ext a b")
    L.append("  fin_cases a <;> fin_cases b <;> decide +kernel")
    L.append("")
    L.append("/-- The basis-independent operator identity `∑ w'_j T₂^j = I_k • T₃`. -/")
    L.append(f"theorem op_id : ∑ j ∈ Finset.range {n}, ((wp j : ℤ) : ℂ) • {T2} ^ j")
    L.append(f"    = ((Ik : ℤ) : ℂ) • {T3} :=")
    L.append(f"  int_poly_of_dimN (by norm_num) {fr} {fb}")
    L.append(f"    {Atab} {X2} {X3}")
    L.append(f"    {hzero} {hone} {hA}")
    L.append(f"    {T2} {T3} {hX2} {hX3}")
    L.append(f"    {M2} {M3} {hM2} {hM3}")
    L.append("    wp Ik scaled")

    if D == 1:
        L.append("")
        L.append("/-- The denominator is trivial at this weight (`D = 1`). -/")
        L.append("theorem D_dvd_Ik : (1 : ℤ) ∣ Ik := one_dvd Ik")
        report[k] = ("trivial", n)
    else:
        e, c = bezout_tree(N, D)
        report[k] = ("full", n, maxdigits(c, *e.values()), len(str(abs(D))))
        L.append("")
        L.extend(chunked_def("Dn", D,
                             f"The reduced denominator of the landed rational witness at "
                             f"weight {k} (G1 audit)."))
        L.append("")
        L.append("theorem scaled_idN :")
        L.append(f"    (∑ j ∈ Finset.range {n}, {cert} j • {M2} ^ j)")
        L.append(f"      = Dn • {M3} := {heckerat_scaled}")
        L.append("")
        L.append("theorem hDq : ((Dn : ℤ) : ℚ) ≠ 0 := by norm_num [Dn]")
        L.append("theorem hDc : ((Dn : ℤ) : ℂ) ≠ 0 := by norm_num [Dn]")
        L.append("")
        L.append("/-- The rational-witness representation (from the landed certificate). -/")
        L.append(f"theorem hrepD : {T3} = Polynomial.aeval {T2}")
        L.append(f"    ((∑ j ∈ Finset.range {n}, C (((({cert} j : ℤ) : ℚ) / (Dn : ℚ)))")
        L.append("      * (X : ℚ[X]) ^ j).map (algebraMap ℚ ℂ)) :=")
        L.append(f"  aeval_div_witness {T2} {T3} {cert} Dn hDc")
        L.append(f"    (int_poly_of_dimN (by norm_num) {fr} {fb}")
        L.append(f"      {Atab} {X2} {X3}")
        L.append(f"      {hzero} {hone} {hA}")
        L.append(f"      {T2} {T3} {hX2} {hX3}")
        L.append(f"      {M2} {M3} {hM2} {hM3}")
        L.append(f"      {cert} Dn scaled_idN).symm")
        L.append("")
        L.append("/-- The index representation (from the new certificate). -/")
        L.append(f"theorem hrepI : {T3} = Polynomial.aeval {T2}")
        L.append(f"    ((∑ j ∈ Finset.range {n}, C ((((wp j : ℤ) : ℚ) / (Ik : ℚ)))")
        L.append("      * (X : ℚ[X]) ^ j).map (algebraMap ℚ ℂ)) :=")
        L.append(f"  aeval_div_witness {T2} {T3} wp Ik hIkc op_id.symm")
        L.append("")
        L.append("/-- `minpoly ℂ T₂` has degree `n` (the charpoly is irreducible). -/")
        L.append("theorem minpoly_nd : (minpoly ℂ (" + f"{t2ns}.T2 : Module.End ℂ")
        L.append(f"    (CuspForm 𝒮ℒ (({k} : ℕ) : ℤ)))).natDegree = {n} := by")
        L.append("  rw [HeckeGeneratedByT2.minpoly_eq_charpoly_of_map_of_irreducible")
        L.append(f"    {t2ns}.charpoly_T2 {t2ns}.maeda, {t2ns}.charpoly_T2,")
        L.append("    Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]")
        L.append("  " + pnd)
        L.append("")
        ekeys = [e.get(i, 0) for i in range(n)]
        L.extend(seq_def("bez", ekeys,
                         "The Bézout witness `∑ bez j * N j + bezc * D = 1` "
                         "(balanced extgcd tree, G1 strategy)."))
        L.append("")
        L.extend(chunked_def("bezc", c, "The Bézout coefficient of `D`."))
        L.append("")
        L.append("/-- The Bézout identity over a `List` sum: the kernel certificate (a")
        L.append("`Finset` sum would route through `Multiset`'s quotient and pull")
        L.append("`Classical.choice`/`Quot.sound` into the decide — CLAUDE.md rule). -/")
        L.append(f"theorem hbezL : ((List.range {n}).map fun j => bez j * {cert} j).sum")
        L.append("    + bezc * Dn = 1 := by")
        L.append("  decide +kernel")
        L.append("")
        L.append(f"theorem hbez : ∑ j ∈ Finset.range {n}, bez j * {cert} j")
        L.append("    + bezc * Dn = 1 := by")
        L.append("  rw [MaedaLevelOne.finset_sum_range_eq_list]")
        L.append("  exact hbezL")
        L.append("")
        L.append("/-- **The composite: the reduced denominator divides the index.** -/")
        L.append(f"theorem D_dvd_Ik : Dn ∣ Ik :=")
        L.append(f"  den_dvd_index (by norm_num) {T2} {T3} minpoly_nd")
        L.append(f"    {cert} wp Dn Ik hDq hIkq hrepD hrepI bez bezc hbez")
    L.append("")
    L.append(f"end HeckeIndexWeight{k}")
    return L


# Split by dimension (iteration-23 merge memory pass): the profile showed no
# hot declaration, only the import floor plus ~1.1 GiB of retained literals,
# pushing the build tree past 97 % of the default 8 GiB Modal request.  Each
# half now imports only its own parents and carries half the literals.
PARTS = [
    (MF / "HeckeIndexSmallWeights.lean", lambda d: d <= 5, "2 ≤ dim S_k ≤ 5", 24, [
        "MathProof.ModularForms.HeckeIndex",
        "MathProof.ModularForms.HeckeGeneratedByT2",
        "MathProof.ModularForms.HeckeRationalSmallWeights",
        "MathProof.ModularForms.MaedaSmallWeights",
        "MathProof.ModularForms.MaedaDim4Weights",
        "MathProof.ModularForms.MaedaDim5Weights",
    ]),
    (OUT, lambda d: d >= 6, "6 ≤ dim S_k ≤ 10", 30, [
        "MathProof.ModularForms.HeckeIndex",
        "MathProof.ModularForms.HeckeGeneratedByT2",
        "MathProof.ModularForms.HeckeRationalWeights",
    ]),
]


def render(keys, data, report, scope, count, imports):
    L = [f"import {m}" for m in imports]
    L.append("")
    L.append("open HeckeIndex Polynomial MaedaLevelOne")
    L.append("open scoped MatrixGroups")
    L.append("")
    L.append("/-!")
    L.append(f"# The Hecke index at every level-one weight with `{scope}`")
    L.append("")
    L.append("Generated by `tools/gen_hecke_index.py` from")
    L.append("`research/iteration23/hecke-index/index_data.json` (the G1 audit's")
    L.append("re-pinned data; byte-identical re-runs; do not hand-edit).  For each of")
    L.append(f"the {count} weights with `{scope}` (the 54 weights `24 ≤ k ≤ 134`")
    L.append("are split by dimension over `HeckeIndexSmallWeights` / `HeckeIndexWeights`):")
    L.append("the index `I_k = |det A|` with its certified Bareiss determinant")
    L.append("(`eval_det`), the Cramer weights `w' = I_k · w`, the entrywise kernel")
    L.append("certificate `∑ w'_j M₂^j = I_k M₃` (`decide +kernel` entrywise), the")
    L.append("basis-independent operator identity")
    L.append("`∑ (w'_j : ℂ) • T₂^j = (I_k : ℂ) • T₃`")
    L.append("(`HeckeIndex.int_poly_of_dimN`), and — for the weights with a")
    L.append("nontrivial reduced denominator `D` — the composite `D ∣ I_k` via")
    L.append("`HeckeIndex.den_dvd_index` (the reduced denominator of any")
    L.append("representation divides the denominator of every other).  At the")
    L.append("dim-2 weights the denominator is `1` and the divisibility is `one_dvd`.")
    L.append("")
    L.append("Everything is light: no `set_option`, no `native_decide`/`sorry`; the")
    L.append("only decides are entrywise per-matrix-cell certificates plus one small")
    L.append("Bézout identity per weight (over a `List` sum), all `decide +kernel`.")
    L.append("-/")
    L.append("")
    for k in keys:
        L.extend(emit_weight(k, data[k], report))
        L.append("")
    return "\n".join(L).rstrip("\n") + "\n"


# ---------------------------------------------------------------------------
# `--card` mode (iteration 24, b1 index-card): the lattice index
# `[𝕋 : ℤ[T₂]] = |I_k|` per weight, through `HeckeLatticeIndex.index_card_dimN`.
# Ground truth = the LANDED Lean literals (Atab of the MaedaT3 files, the T₂
# matrix of the HeckeRational / MaedaDim files, `Ik` + `det_A` sign of the
# HeckeIndex files), parsed with the iteration-23/24 G1 audit parsers
# (imported, not copied).  Per weight: the integer echelon table `atab`, the
# dual-coordinate matrix `C i j = a_1(T₂^i g_j) = ∑_c μ_{jc} (M₂^i)_{0c}`,
# its entrywise kernel certificate `hcard`, `det_C : C.det = ±I_k`
# (`eval_det`), and the index statements.

CARD_PARTS = [
    (MF / "HeckeIndexCardSmallWeights.lean", lambda d: d <= 5, "2 ≤ dim S_k ≤ 5", 24, [
        "MathProof.ModularForms.HeckeLatticeIndex",
        "MathProof.ModularForms.HeckeIndexSmallWeights",
        "MathProof.ModularForms.HeckeGeneratedByT2SmallWeights",
    ]),
    (MF / "HeckeIndexCardWeights.lean", lambda d: d >= 6, "6 ≤ dim S_k ≤ 10", 30, [
        "MathProof.ModularForms.HeckeLatticeIndex",
        "MathProof.ModularForms.HeckeIndexWeights",
    ]),
]


def _load_audits():
    import importlib.util
    i24 = ROOT / "research" / "iteration24" / "index-card" / "g1_audit.py"
    spec = importlib.util.spec_from_file_location("g1_audit_i24", i24)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)          # also imports the iteration-23 parsers as mod.G
    sys.path.insert(0, str(ROOT / "tools"))
    import gen_hecke_field as HF          # gent2_names / c_lemmas (hfi, hmin names)
    return mod, mod.G, HF


def miller_top_c(atab, n):
    """Mirror of `HeckeLatticeIndex.millerTopC` / `millerCoeff`: row j = the
    fb-coefficients of the Miller vector g_j."""
    acc = []
    for r in range(1, n + 1):
        j = n - r
        head = [int(c == j) for c in range(n)]
        for t in range(r - 1):
            a = atab.get((j, t + (n - r + 1)), 0)
            for c in range(n):
                head[c] -= a * acc[t][c]
        acc.insert(0, head)
    return acc


def card_data():
    """{weight: dict(dim, atab, M2, C, Ik, sign)} from the landed literals."""
    I24, G, HF = _load_audits()
    idx = I24.parse_index_files()
    t3, small = {}, set()
    for f in [G.T3_SMALL] + list(G.T3_DIM.values()):
        for ns, sec in G.namespaces(f).items():
            t3[G.weight_of(ns)] = sec
            if f is G.T3_SMALL:
                small.add(G.weight_of(ns))
    t2dim = {}
    for f in G.T2_DIM.values():
        for ns, sec in G.namespaces(f).items():
            t2dim[G.weight_of(ns)] = sec
    hr = {}
    for f in [G.HR_BIG, G.HR_SMALL]:
        for ns, sec in G.namespaces(f).items():
            hr[G.hr_weight_of(ns)] = sec
    gt, cl = HF.gent2_names(), HF.c_lemmas()
    out = {}
    for k in sorted(t3):
        sec3 = t3[k]
        atab = G.parse_Atab(sec3)
        M2 = G.parse_M2(hr[k]) if k in small else G.parse_M(t2dim[k])
        n = len(M2)
        assert cl[k] == n, (k, cl[k], n)
        mu = miller_top_c(atab, n)
        # cross-check: the iteration-24 audit's accumulator gives the same μ
        assert mu == I24.miller_top_c(lambda i, j: atab.get((i, j), 0), n), k
        pows = [G.matpow(M2, i) for i in range(n)]
        C = [[sum(mu[j][c] * pows[i][0][c] for c in range(n)) for j in range(n)]
             for i in range(n)]
        Ik = I24.parse_Ik(idx[k])
        d = det_exact(C)
        assert abs(d) == abs(Ik) and Ik > 0, (k, d, Ik)
        out[k] = dict(dim=n, atab=atab, M2=M2, C=C, Ik=Ik, sign=1 if d > 0 else -1,
                      small=k in small, gt=gt[k])
    assert len(out) == 54, len(out)
    return out


def atab_def(atab, k):
    out = [f"/-- The landed echelon table `MaedaT3Weight{k}.Atab`, integer-typed (G1 audit). -/",
           "def atab : ℕ → ℕ → ℤ"]
    for (i, j) in sorted(atab):
        out.extend(wrap_tokens(" ".join(int_lines(atab[(i, j)])), f"  | {i}, {j} => ",
                               "      "))
    out.append("  | _, _ => 0")
    return out


TAB_CHUNK = 40   # pow-free chunks: base written as a 41-digit numeral


def int_lines_nopow(v):
    """Pow-free chunked ℤ expression for `v` (Horner in the numeral base
    `10^TAB_CHUNK` written out): kernel certificates must not touch `Monoid.npow`
    (Mathlib's `ℤ` instances are not axiom-free); `*`, `+`, `-` are core."""
    if abs(v) < 10 ** PLAIN_DIGITS:
        return [str(v)]
    base = "1" + "0" * TAB_CHUNK
    s = str(abs(v))
    chunks = []
    while s:
        chunks.insert(0, str(int(s[-TAB_CHUNK:])))
        s = s[:-TAB_CHUNK]
    lines = ["(" * (len(chunks) - 1) + chunks[0] + f" * {base}"]
    for j, ch in enumerate(chunks[1:], 1):
        tail = "" if j == len(chunks) - 1 else f" * {base}"
        lines.append(f"+ {ch}){tail}")
    if v < 0:
        lines[0] = "-(" + lines[0]
        lines[-1] = lines[-1] + ")"
    return lines


def table_def(name, M, doc):
    """`def name : ℕ → ℕ → ℤ` from a square integer matrix (zero arms omitted)."""
    out = wrap_doc(doc) + [f"def {name} : ℕ → ℕ → ℤ"]
    for i, row in enumerate(M):
        for j, v in enumerate(row):
            if v:
                ls = int_lines_nopow(v)
                out.append(f"  | {i}, {j} => " + ls[0])
                out.extend("      " + ln for ln in ls[1:])
    out.append("  | _, _ => 0")
    return out


def emit_card_weight(k, w):
    n, C = w["dim"], w["C"]
    t3 = f"MaedaT3Weight{k}"
    ix = f"HeckeIndexWeight{k}"
    if w["small"]:
        rat = f"HeckeRatWeight{k}"
        X2, hX2, M2, hM2 = f"{rat}.Xtab2", f"{rat}.hX2", f"{rat}.M2", f"{rat}.hM2"
    else:
        t2 = f"MaedaWeight{k}"
        X2, hX2, M2, hM2 = f"{t2}.Xtab", f"{t2}.hX", f"{t2}.M", f"HeckeRatWeight{k}.hM2"
    t2op, cp, mae = w["gt"]
    sign = "" if w["sign"] > 0 else "-"
    kk = f"(({k} : ℕ) : ℤ)"
    L = [f"/-! ### Weight {k} (dim {n}) -/", f"namespace HeckeIndexCardWeight{k}", ""]
    L.extend(atab_def(w["atab"], k))
    L.append("")
    L.append(f"theorem hAeq : ∀ i j : ℕ, i < j → j < {n} →")
    L.append(f"    {t3}.Atab i j = ((atab i j : ℤ) : ℂ) := by")
    L.append("  intro i j hij hj")
    if n == 2:   # a single (i, j) cell: `<;>` would trip the unusedTactic linter
        L.append("  obtain rfl : j = 1 := by omega")
        L.append("  obtain rfl : i = 0 := by omega")
        L.append(f"  norm_num [{t3}.Atab, atab]")
    else:
        L.append(f"  interval_cases j <;> interval_cases i <;> norm_num [{t3}.Atab, atab]")
    L.append("")
    L.append(f"/-- The echelon basis at weight {k} has integer `q`-coefficients (all `m`). -/")
    L.append(f"theorem hfi : ∀ i : ℕ, i < {n} → ∀ m : ℕ,")
    L.append(f"    ∃ z : ℤ, (qExpansion 1 ({t3}.fb i)).coeff m = (z : ℂ)")
    for i in range(n):
        L.append(f"  | {i}, _, m => ⟨_, {t3}.c{i + 1} m⟩")
    L.append(f"  | _ + {n}, h, _ => absurd h (by omega)")
    L.append("")
    L.append(f"/-- `minpoly T₂` has degree `dim S_{k} = {n}` (Maeda: charpoly irreducible). -/")
    L.append(f"theorem hmin : (minpoly ℂ (heckeTM {kk} 2)).natDegree = {n} := by")
    L.append("  rw [HeckeTM.heckeTM_prime _ Nat.prime_two]")
    L.append(f"  change (minpoly ℂ ({t2op} :")
    L.append(f"    Module.End ℂ (CuspForm 𝒮ℒ {kk}))).natDegree = {n}")
    L.append("  rw [HeckeGeneratedByT2.minpoly_eq_charpoly_of_map_of_irreducible")
    L.append(f"    {cp}")
    L.append(f"    {mae},")
    L.append(f"    LinearMap.charpoly_natDegree, {t3}.finrank_eq]")
    L.append("")
    L.extend(matrix_def("C", C,
                        f"Dual coordinates at weight {k}: `T₂^i = ∑_j C i j • T_(j+1)`.",
                        int_lines_nopow))
    L.append("")
    L.extend(table_def("m2tab", w["M2"], f"The landed `T₂` matrix `{M2}` as an integer table."))
    L.append("")
    L.append(f"theorem hM2tab : ∀ i j : Fin {n}, {M2} i j = m2tab i.val j.val := by")
    L.append("  intro i j")
    L.append("  fin_cases i <;> fin_cases j <;> rfl")
    L.append("")
    L.extend(table_def("ctab", C, "The matrix `C` as an integer table."))
    L.append("")
    L.append(f"theorem hCtab : ∀ i j : Fin {n}, C i j = ctab i.val j.val := by")
    L.append("  intro i j")
    L.append("  fin_cases i <;> fin_cases j <;> rfl")
    L.append("")
    L.append("/-- The kernel certificate over `List` sums and integer tables (`propext`-only):")
    L.append("every cell of `C` is the Miller-conjugated row 0 of the powers of `T₂`. -/")
    L.append(f"theorem hcheck : cardCheck atab m2tab ctab {n} = true := by")
    L.append("  decide +kernel")
    L.append("")
    L.append("/-- The matrix identity consumed by `index_card_dimN` (`hcard_of_check`). -/")
    L.append(f"theorem hcard : Matrix.of (fun i j : Fin {n} =>")
    L.append(f"    ∑ c : Fin {n}, millerCoeff atab {n} j.val c.val")
    L.append(f"      * ({M2} ^ (i : ℕ)) 0 c) = C :=")
    L.append(f"  hcard_of_check atab {M2} C m2tab ctab hM2tab hCtab hcheck")
    L.append("")
    L.append("/-- `det C = ±I_k` (certified Bareiss `eval_det`; `I_k` the landed literal). -/")
    L.append(f"theorem det_C : C.det = {sign}{ix}.Ik := by")
    L.append("  simp only [C]")
    L.append("  eval_det")
    L.append(f"  norm_num [{ix}.Ik]")
    L.append("")
    habs = "by rw [det_C]" if not sign else "by rw [det_C, Int.natAbs_neg]"
    toks = ["(by norm_num)", "(by norm_num)", f"{t3}.finrank_eq", f"{t3}.fb", f"{t3}.Atab",
            f"{t3}.hzero", f"{t3}.hone", f"{t3}.hA", "hfi", "hmin", "atab", "hAeq",
            X2, hX2, M2, hM2, "C", "hcard", f"{ix}.Ik", f"({habs})"]

    def app(head):
        out, cur = [], "  " + head
        for t in toks:
            if len(cur) + 1 + len(t) > WIDTH:
                out.append(cur)
                cur = "    " + t
            else:
                cur += " " + t
        out.append(cur)
        return out

    L.append(f"/-- **The lattice index at weight {k}**: `[𝕋 : ℤ[T₂]] = |I_k|`. -/")
    L.append(f"theorem index_card : (t2Lattice (heckeTM {kk} 2) {n}).toAddSubgroup.relIndex")
    L.append(f"    (heckeLattice {kk} {n}).toAddSubgroup = {ix}.Ik.natAbs :=")
    L.extend(app("index_card_dimN"))
    L.append("")
    L.append(f"/-- **The lattice index at weight {k}**, as `Nat.card (𝕋 ⧸ ℤ[T₂])`. -/")
    L.append(f"theorem index_card_natCard : Nat.card (↥(heckeLattice {kk} {n}).toAddSubgroup ⧸")
    L.append(f"    (t2Lattice (heckeTM {kk} 2) {n}).toAddSubgroup.addSubgroupOf")
    L.append(f"      (heckeLattice {kk} {n}).toAddSubgroup) = {ix}.Ik.natAbs :=")
    L.extend(app("index_card_natCard_dimN"))
    L.append("")
    L.append(f"end HeckeIndexCardWeight{k}")
    return L


def render_card(keys, data, scope, count, imports):
    L = [f"import {m}" for m in imports]
    L.append("")
    L.append("open HeckeIndex HeckeLatticeIndex HeckeTM MaedaLevelOne")
    L.append("open UpperHalfPlane ModularForm CuspForm")
    L.append("open scoped MatrixGroups")
    L.append("")
    L.append("/-!")
    L.append(f"# The lattice index `[𝕋 : ℤ[T₂]]` at every level-one weight with `{scope}`")
    L.append("")
    L.append("Generated by `tools/gen_hecke_index.py --card` from the landed literals")
    L.append("(the `Atab` tables of the `MaedaT3` files, the `T₂` matrices of the")
    L.append("`HeckeRational` / `MaedaDim` files, `I_k` of the `HeckeIndex` files; parsed")
    L.append("with the iteration-23/24 G1 audit parsers; byte-identical re-runs, `--check`;")
    L.append(f"do not hand-edit).  For each of the {count} weights with `{scope}`")
    L.append("(the 54 weights `24 ≤ k ≤ 134` are split by dimension over")
    L.append("`HeckeIndexCardSmallWeights` / `HeckeIndexCardWeights`): the dual")
    L.append("coordinates `C i j = a_1(T₂^i g_j)` of the powers of `T₂` over the Hecke")
    L.append("basis `T_1, …, T_n` (`g` the Miller basis), certified by")
    L.append("one `List`-sum `decide +kernel` per weight (`hcheck`, bridged to `hcard`),")
    L.append("`det C = ±I_k` (`eval_det`), and the lattice")
    L.append("index `[𝕋 : ℤ[T₂]] = |I_k|` as an `AddSubgroup.relIndex` (`index_card`) and")
    L.append("as `Nat.card (𝕋 ⧸ ℤ[T₂])` (`index_card_natCard`), through")
    L.append("`HeckeLatticeIndex.index_card_dimN`.")
    L.append("")
    L.append("Everything is light: no `set_option`, no `native_decide`/`sorry`; the only")
    L.append("decide is the per-weight `hcheck` (`List` sums, `propext`-only).")
    L.append("-/")
    L.append("")
    for k in keys:
        L.extend(emit_card_weight(k, data[k]))
        L.append("")
    return "\n".join(L).rstrip("\n") + "\n"


def card_main(check):
    data = card_data()
    keys = sorted(data)
    failed = False
    for out, pick, scope, count, imports in CARD_PARTS:
        ks = [k for k in keys if pick(data[k]["dim"])]
        assert len(ks) == count, (out.name, len(ks))
        text = render_card(ks, data, scope, count, imports)
        if check:
            old = out.read_text() if out.exists() else ""
            if old == text:
                print(f"check OK: {out.name} byte-identical")
            else:
                print(f"check FAILED: {out.name} differs (lines", len(old.splitlines()),
                      "vs", len(text.splitlines()), ")")
                failed = True
            continue
        out.write_text(text)
        print(f"wrote {out}: {count} weights")
    return failed


def main():
    check = "--check" in sys.argv
    if "--card" in sys.argv and not check:
        card_main(False)
        return
    data = json.load(open(DATA))
    keys = sorted(data, key=int)
    assert len(keys) == 54, len(keys)
    report = {}
    failed = False
    for out, pick, scope, count, imports in PARTS:
        ks = [k for k in keys if pick(data[k]["dim"])]
        assert len(ks) == count, (out.name, len(ks))
        text = render(ks, data, report, scope, count, imports)
        if check:
            old = out.read_text() if out.exists() else ""
            if old == text:
                print(f"check OK: {out.name} byte-identical")
            else:
                print(f"check FAILED: {out.name} differs (lines", len(old.splitlines()),
                      "vs", len(text.splitlines()), ")")
                failed = True
            continue
        out.write_text(text)
        print(f"wrote {out}: {count} weights")
    if check:
        failed = card_main(True) or failed
        if failed:
            sys.exit(1)
        return
    full = [k for k in report if report[k][0] == "full"]
    print(f"54 weights, {len(full)} full composites")
    worst = sorted(full, key=lambda k: -report[k][2])[:3]
    for k in worst:
        r = report[k]
        print(f"  weight {k} (dim {r[1]}): max bez digit {r[2]}, D digits {r[3]}")


if __name__ == "__main__":
    main()
