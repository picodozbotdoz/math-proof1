#!/usr/bin/env python3
"""Generator for `MathProof/ModularForms/HeckeIndexWeights.lean` (iteration 23, b2).

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


def matrix_def(name, A, doc):
    """Lines of `def name : Matrix (Fin n) (Fin n) ℤ := !![...]` (chunked)."""
    n = len(A)
    out = wrap_doc(doc)
    out.append(f"def {name} : Matrix (Fin {n}) (Fin {n}) ℤ := !![")
    for i, row in enumerate(A):
        toks = []
        for e in row:
            ls = int_lines(e)
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
        L.append(f"theorem hbez : ∑ j ∈ Finset.range {n}, bez j * {cert} j")
        L.append("    + bezc * Dn = 1 := by")
        L.append("  decide +kernel")
        L.append("")
        L.append("/-- **The composite: the reduced denominator divides the index.** -/")
        L.append(f"theorem D_dvd_Ik : Dn ∣ Ik :=")
        L.append(f"  den_dvd_index (by norm_num) {T2} {T3} minpoly_nd")
        L.append(f"    {cert} wp Dn Ik hDq hIkq hrepD hrepI bez bezc hbez")
    L.append("")
    L.append(f"end HeckeIndexWeight{k}")
    return L


def main():
    check = "--check" in sys.argv
    data = json.load(open(DATA))
    keys = sorted(data, key=int)
    assert len(keys) == 54, len(keys)
    report = {}
    L = []
    L.append("import MathProof.ModularForms.HeckeIndex")
    L.append("import MathProof.ModularForms.HeckeGeneratedByT2")
    L.append("import MathProof.ModularForms.HeckeRationalWeights")
    L.append("import MathProof.ModularForms.HeckeRationalSmallWeights")
    L.append("import MathProof.ModularForms.MaedaSmallWeights")
    L.append("import MathProof.ModularForms.MaedaDim4Weights")
    L.append("import MathProof.ModularForms.MaedaDim5Weights")
    L.append("")
    L.append("open HeckeIndex Polynomial MaedaLevelOne")
    L.append("open scoped MatrixGroups")
    L.append("")
    L.append("/-!")
    L.append("# The Hecke index at every level-one weight with `2 ≤ dim S_k ≤ 10`")
    L.append("")
    L.append("Generated by `tools/gen_hecke_index.py` from")
    L.append("`research/iteration23/hecke-index/index_data.json` (the G1 audit's")
    L.append("re-pinned data; byte-identical re-runs; do not hand-edit).  For each of")
    L.append("the 54 weights `24 ≤ k ≤ 134` with `2 ≤ dim S_k ≤ 10`: the index")
    L.append("`I_k = |det A|` with its certified Bareiss determinant (`eval_det`),")
    L.append("the Cramer weights `w' = I_k · w`, the entrywise kernel certificate")
    L.append("`∑ w'_j M₂^j = I_k M₃` (`decide +kernel` entrywise), the")
    L.append("basis-independent operator identity")
    L.append("`∑ (w'_j : ℂ) • T₂^j = (I_k : ℂ) • T₃`")
    L.append("(`HeckeIndex.int_poly_of_dimN`), and — for the weights with a")
    L.append("nontrivial reduced denominator `D` — the composite `D ∣ I_k` via")
    L.append("`HeckeIndex.den_dvd_index` (the reduced denominator of any")
    L.append("representation divides the denominator of every other).  At the six")
    L.append("dim-2 weights the denominator is `1` and the divisibility is")
    L.append("`one_dvd`.")
    L.append("")
    L.append("Everything is light: no `set_option`, no `native_decide`/`sorry`; the")
    L.append("only decides are entrywise per-matrix-cell certificates plus one small")
    L.append("Bézout identity per weight, all `decide +kernel`.")
    L.append("-/")
    L.append("")
    for k in keys:
        L.extend(emit_weight(k, data[k], report))
        L.append("")
    L.append("end HeckeIndexWeights") if False else None
    text = "\n".join(L).rstrip("\n") + "\n"
    if check:
        old = OUT.read_text() if OUT.exists() else ""
        if old == text:
            print("check OK: byte-identical")
            return
        print("check FAILED: differs (lines", len(old.splitlines()), "vs",
              len(text.splitlines()), ")")
        sys.exit(1)
    OUT.write_text(text)
    full = [k for k in report if report[k][0] == "full"]
    print(f"wrote {OUT}: 54 weights, {len(full)} full composites")
    worst = sorted(full, key=lambda k: -report[k][2])[:3]
    for k in worst:
        r = report[k]
        print(f"  weight {k} (dim {r[1]}): max bez digit {r[2]}, D digits {r[3]}")


if __name__ == "__main__":
    main()
