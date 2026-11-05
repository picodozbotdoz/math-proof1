#!/usr/bin/env python3 -I
"""Generate the per-weight Hecke-ring generator instances (iteration 24).

For every level-one weight 24 ≤ k ≤ 134 with 2 ≤ n = dim S_k ≤ 10 (54
weights) this emits, in namespace `HeckeRingGensWeightKK`:

* `hfi` — the landed echelon basis `MaedaT3WeightKK.fb` has integer
  q-coefficients (the `c_i` seqP bridges);
* `heckeRing` — the Hecke ring `𝕋 = span_ℤ {T_1, …, T_n}` of `S_k`
  (`HeckeIndex.heckeRing` on the Miller basis of the landed echelon data);
* `heckeRing_eq_gens2357` — `𝕋 = ℤ[T₂, T₃, T₅, T₇]` (every weight);
* `heckeRing_eq_gens235` — `𝕋 = ℤ[T₂, T₃, T₅]` at every weight with n ≤ 6
  (certificate-free) and at the ten dims-7–9 weights where `T₇` is a
  {2,3,5}-smooth integer combination (`t7M`/`t7c` + `t7_rows`, a row
  certificate on the landed `q{i}_{m}` lemmas, m ≤ 3n);
* `heckeRing_eq_gens23` (n ≤ 4) and `heckeRing_eq_gens2` (n ≤ 2).

The T₇ certificate: in Miller coordinates `T_m = ∑_j a_m(g_j) T_{j+1}`, so
`T₇` is a smooth combination iff the T₇-coordinates `a_m(g_6)` of the smooth
`m ∈ (n, 3n]` have gcd 1 (they do exactly at the ten weights below, which
are the dims-7–9 members of the 22 {3,5}-weights of the G1 audit); the
generator takes the smallest such subset E (by size, then digits), Bezout
coefficients b, and `T₇ = ∑_{m∈E} b_m T_m − ∑_{j≠6} V_j T_{j+1}` with
`V = ∑ b_m vec(T_m)`.  Every certificate is re-verified here on the raw
basis rows (= `fb`, audit C1 of research/iteration23/hecke-index/g1_audit.py)
before it is emitted; Lean re-checks it on the landed literals.

Two files, split by dimension (each imports only its own data parents):
  HeckeRingGensSmallWeights.lean  (dims 2–5, parent MaedaT3SmallWeights)
  HeckeRingGensWeights.lean       (dims 6–10, parents MaedaT3Dim{6..10}Weights)
Both are root-only (their parents are not push-tier CI items).

Run:  python3 -I tools/gen_hecke_ring_gens.py            (write the files)
      python3 -I tools/gen_hecke_ring_gens.py --check    (byte-identity check)
"""

import functools
import itertools
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
MF = ROOT / "MathProof" / "ModularForms"
sys.path.insert(0, str(ROOT / "research" / "iteration23" / "hecke-index"))
import g1_audit as G  # noqa: E402  (prodForm arithmetic: raw / Miller basis)

T3_SMALL = MF / "MaedaT3SmallWeights.lean"
T3_DIM = {d: MF / f"MaedaT3Dim{d}Weights.lean" for d in range(6, 11)}
OUT_SMALL = MF / "HeckeRingGensSmallWeights.lean"
OUT_BIG = MF / "HeckeRingGensWeights.lean"

# the dims-7–9 {3,5}-weights (G1 audit, research/iteration24/hecke-ring-gens)
T7_WEIGHTS = [88, 92, 94, 98, 100, 104, 106, 110, 116, 122]
SMOOTH_EXP = 30  # every smooth M ≤ 30 divides 30^30


def weights_dims(path):
    """(weight, dim) for every `MaedaT3WeightKK` namespace of a landed file."""
    text = path.read_text()
    out = []
    for m in re.finditer(
            r"^lemma finrank_eq : Module\.finrank ℂ \(CuspForm 𝒮ℒ \(\((\d+) : ℕ\) : ℤ\)\) = (\d+)",
            text, flags=re.M):
        out.append((int(m.group(1)), int(m.group(2))))
    names = re.findall(r"^namespace MaedaT3Weight(\d+)$", text, flags=re.M)
    assert [w for w, _ in out] == [int(x) for x in names], path
    return out


def smooth235(m):
    for p in (2, 3, 5):
        while m % p == 0:
            m //= p
    return m == 1


def egcd_list(vals):
    """g, cs with sum(cs[i] * vals[i]) = g = gcd(vals) ≥ 0."""
    g, cs = 0, []
    for v in vals:
        a, b = g, v
        x0, y0, x1, y1 = 1, 0, 0, 1
        while b:
            q = a // b
            a, b = b, a - q * b
            x0, x1 = x1, x0 - q * x1
            y0, y1 = y1, y0 - q * y1
        cs = [c * x0 for c in cs] + [y0]
        g = a
    if g < 0:
        g, cs = -g, [-c for c in cs]
    return g, cs


@functools.cache
def t7_cert(k, n):
    """(M, c): T₇ = ∑ c_t T_{M_t}, all M_t {2,3,5}-smooth ≤ 3n; or None."""
    g = G.basis_miller(k, n)
    raw = G.basis_raw(k, n)
    pool = [m for m in range(n + 1, 3 * n + 1) if smooth235(m)]
    for r in (1, 2, 3):
        best = None
        for E in itertools.combinations(pool, r):
            gg, b = egcd_list([g[6][m] for m in E])
            if gg != 1:
                continue
            V = [sum(bm * g[j][m] for bm, m in zip(b, E)) for j in range(n)]
            assert V[6] == 1
            M = list(E) + [j + 1 for j in range(n) if j != 6]
            c = tuple(list(b) + [-V[j] for j in range(n) if j != 6])
            M = tuple(M)
            for i in range(n):  # re-verify on the raw (= fb) rows
                assert raw[i][7] == sum(ct * raw[i][mt] for ct, mt in zip(c, M)), (k, i)
            dig = max(len(str(abs(x))) for x in c)
            if best is None or dig < best[0]:
                best = (dig, M, c)
        if best:
            return best[1], best[2]
    return None


def int_list_lines(name, typ, vals, width=100, indent="    "):
    """`def name : ℕ → typ := fun t => [v₀, v₁, …].getD t 0`, packed at `width`."""
    out, cur = [f"def {name} : ℕ → {typ} := fun t =>"], indent + "["
    items = [str(v) for v in vals]
    for i, it in enumerate(items):
        piece = it + ("].getD t 0" if i == len(items) - 1 else ",")
        if len(cur) + 1 + len(piece) > width and not cur.endswith("["):
            out.append(cur)
            cur = indent + " " + piece
        else:
            cur = cur + ("" if cur.endswith("[") else " ") + piece
    out.append(cur)
    return out


def wrap_names(prefix, names, width=100, indent="    "):
    """`prefix [a, b, …]` wrapped at `width`."""
    out, cur = [], prefix + " ["
    for i, nm in enumerate(names):
        piece = nm + ("]" if i == len(names) - 1 else ",")
        if len(cur) + 1 + len(piece) > width and not cur.endswith("["):
            out.append(cur)
            cur = indent + piece
        else:
            cur = cur + ("" if cur.endswith("[") else " ") + piece
    out.append(cur)
    return out


def weight_block(k, n):
    ns = f"MaedaT3Weight{k}"
    L = []
    L.append(f"/-! ### Weight {k} (dim {n}) -/")
    L.append(f"namespace HeckeRingGensWeight{k}")
    L.append("")
    L.append(f"/-- The echelon basis at weight {k} has integer `q`-coefficients (all `m`). -/")
    L.append(f"theorem hfi : ∀ i : ℕ, i < {n} → ∀ m : ℕ,")
    L.append(f"    ∃ z : ℤ, (qExpansion 1 ({ns}.fb i)).coeff m = (z : ℂ)")
    for i in range(n):
        L.append(f"  | {i}, _, m => ⟨_, {ns}.c{i + 1} m⟩")
    L.append(f"  | _ + {n}, h, _ => absurd h (by omega)")
    L.append("")
    L.append(f"/-- The Hecke ring `𝕋 = span_ℤ {{T_1, …, T_{n}}}` of `S_{k}` (Miller basis of the")
    L.append("landed echelon data). -/")
    L.append("noncomputable def heckeRing :")
    L.append(f"    Subring (Module.End ℂ (CuspForm 𝒮ℒ (({k} : ℕ) : ℤ))) :=")
    L.append(f"  HeckeIndex.heckeRing (HeckeIndex.miller {ns}.fb {ns}.Atab {n})")
    L.append("    (by norm_num)")
    L.append(f"    (HeckeIndex.miller_linearIndependent _ _ {ns}.hzero {ns}.hone")
    L.append(f"      {ns}.hA)")
    L.append(f"    {ns}.finrank_eq")
    L.append(f"    (fun j m hj hm => HeckeIndex.miller_coeff' _ _ {ns}.hzero")
    L.append(f"      {ns}.hone {ns}.hA j m hj hm)")
    L.append(f"    (fun j m hj => HeckeFieldRat.miller_int _ _ {ns}.hA hfi j m hj)")
    L.append("    (by norm_num)")
    L.append("")
    L.append(f"/-- **`𝕋 = ℤ[T₂, T₃, T₅, T₇]` at weight {k}.** -/")
    L.append("theorem heckeRing_eq_gens2357 :")
    L.append("    heckeRing = Subring.closure (HeckeRingGens.gensOf _ [2, 3, 5, 7]) :=")
    L.append("  HeckeRingGens.heckeRing_eq_closure_gens2357 _ _ (by norm_num) _ _ _ _ _")
    L.append("")
    if n <= 6:
        L.append(f"/-- **`𝕋 = ℤ[T₂, T₃, T₅]` at weight {k}** (dim {n} ≤ 6: certificate-free). -/")
        L.append("theorem heckeRing_eq_gens235 :")
        L.append("    heckeRing = Subring.closure (HeckeRingGens.gensOf _ [2, 3, 5]) :=")
        L.append("  HeckeRingGens.heckeRing_eq_closure_gens235 _ _ (by norm_num) _ _ _ _ _")
        L.append("")
    elif k in T7_WEIGHTS:
        cert = t7_cert(k, n)
        assert cert is not None, k
        M, c = cert
        s = len(M)
        L.append(f"/-- The `T₇` relation at weight {k}: `T₇ = ∑_{{t<{s}}} t7c t • T_(t7M t)` with")
        L.append("{2,3,5}-smooth indices (generator-chosen Bezout combination). -/")
        L.extend(int_list_lines("t7M", "ℕ", M))
        L.append("")
        L.append(f"/-- The integer coefficients of the `T₇` relation at weight {k}. -/")
        L.extend(int_list_lines("t7c", "ℤ", c))
        L.append("")
        L.append("/-- The indices of the `T₇` relation are `{2,3,5}`-smooth. -/")
        L.append(f"theorem t7_smooth : ∀ t < {s}, 1 ≤ t7M t ∧")
        L.append(f"    ([2, 3, 5] : List ℕ).prod ^ {SMOOTH_EXP} % t7M t = 0 := by")
        L.append("  decide +kernel")
        L.append("")
        L.append("/-- The `T₇` relation on the first `q`-coefficients of the echelon basis. -/")
        L.append(f"theorem t7_rows : ∀ i : ℕ, i < {n} → (qExpansion 1 ({ns}.fb i)).coeff 7")
        L.append(f"    = ∑ t ∈ Finset.range {s},")
        L.append(f"      ((t7c t : ℤ) : ℂ) * (qExpansion 1 ({ns}.fb i)).coeff (t7M t) := by")
        L.append("  intro i hi")
        L.append("  interval_cases i")
        for i in range(n):
            idx = sorted(set([7] + list(M)))
            names = [f"{ns}.q{i + 1}_{m}" for m in idx]
            L.append(f"  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, t7M, t7c,")
            L.append(f"      List.getD_cons_succ, List.getD_cons_zero, {ns}.fb]")
            L.extend("    " + x for x in wrap_names("simp only", names, width=96, indent="  "))
            L.append("    norm_num")
        L.append("")
        L.append(f"/-- `T₇ ∈ ℤ[T₂, T₃, T₅]` at weight {k}. -/")
        L.append(f"theorem t7_mem : HeckeTM.heckeTM (({k} : ℕ) : ℤ) 7")
        L.append("    ∈ Subring.closure (HeckeRingGens.gensOf _ [2, 3, 5]) :=")
        L.append(f"  HeckeRingGens.heckeTM_mem_closure_of_rows (by norm_num) {ns}.finrank_eq")
        L.append(f"    {ns}.fb {ns}.Atab {ns}.hzero {ns}.hone")
        L.append(f"    {ns}.hA hfi (by norm_num) _")
        L.append("    (by simp [Nat.prime_two, Nat.prime_three, Nat.prime_five]) 7 (by norm_num)")
        L.append(f"    {s} t7M t7c {SMOOTH_EXP} t7_smooth t7_rows")
        L.append("")
        L.append(f"/-- **`𝕋 = ℤ[T₂, T₃, T₅]` at weight {k}** (dim {n}; `T₇` certificate). -/")
        L.append("theorem heckeRing_eq_gens235 :")
        L.append("    heckeRing = Subring.closure (HeckeRingGens.gensOf _ [2, 3, 5]) :=")
        L.append("  HeckeRingGens.heckeRing_eq_closure_gens235_of_t7 _ _ (by norm_num) _ _ _ _ _")
        L.append("    t7_mem")
        L.append("")
    if n <= 4:
        L.append(f"/-- **`𝕋 = ℤ[T₂, T₃]` at weight {k}** (dim {n} ≤ 4). -/")
        L.append("theorem heckeRing_eq_gens23 :")
        L.append("    heckeRing = Subring.closure (HeckeRingGens.gensOf _ [2, 3]) :=")
        L.append("  HeckeRingGens.heckeRing_eq_closure_gens23 _ _ (by norm_num) _ _ _ _ _")
        L.append("")
    if n <= 2:
        L.append(f"/-- **`𝕋 = ℤ[T₂]` at weight {k}** (dim {n} ≤ 2). -/")
        L.append("theorem heckeRing_eq_gens2 :")
        L.append("    heckeRing = Subring.closure (HeckeRingGens.gensOf _ [2]) :=")
        L.append("  HeckeRingGens.heckeRing_eq_closure_gens2 _ _ (by norm_num) _ _ _ _ _")
        L.append("")
    L.append(f"end HeckeRingGensWeight{k}")
    L.append("")
    return L


HEADER = """{imports}

/-!
# Hecke-ring generators: per-weight instances ({span})

Generated by `tools/gen_hecke_ring_gens.py` — regenerate, never hand-edit
(`python3 -I tools/gen_hecke_ring_gens.py --check` verifies byte-identity).

For each weight below (namespace `HeckeRingGensWeightKK`), `heckeRing` is
the Hecke ring `𝕋 = span_ℤ {{T_1, …, T_n}}` of `S_k` built on the landed
echelon data of `MaedaT3WeightKK`, and the generic layer `HeckeRingGens`
gives:

* `heckeRing_eq_gens2357`: `𝕋 = ℤ[T₂, T₃, T₅, T₇]` (every weight);
* `heckeRing_eq_gens235`: `𝕋 = ℤ[T₂, T₃, T₅]` — certificate-free for
  `n ≤ 6`; at the dims-7–9 weights where it holds, from a `T₇` row
  certificate (`t7M`, `t7c`, `t7_rows`, `t7_mem`);
* `heckeRing_eq_gens23` (`n ≤ 4`) and `heckeRing_eq_gens2` (`n ≤ 2`).

{note}
-/

open UpperHalfPlane ModularForm CuspForm MaedaLevelOne
open scoped MatrixGroups

"""

NOTE_SMALL = """Dims 2–5 (24 weights).  Root-only: its parent `MaedaT3SmallWeights` is not
a `defaultTargets`/CI item (see the lakefile note)."""
NOTE_BIG = """Dims 6–10 (30 weights; the dims-7–9 `T₇` certificates are the only data).
Root-only: its parents (the T₃ dim-6–10 files) are CI full-only roots."""


def render(blocks, imports, span, note):
    text = HEADER.format(imports="\n".join(f"import {m}" for m in imports),
                         span=span, note=note)
    for k, n in blocks:
        text += "\n".join(weight_block(k, n)) + "\n"
    return text.rstrip("\n") + "\n"


def main():
    small = weights_dims(T3_SMALL)
    big = []
    for d in range(6, 11):
        wd = weights_dims(T3_DIM[d])
        assert all(n == d for _, n in wd), d
        big += wd
    assert len(small) == 24 and len(big) == 30
    assert all(2 <= n <= 5 for _, n in small)
    big.sort()
    # the T₇ list is exactly the dims-7–9 weights where a smooth T₇ relation exists
    found = [k for k, n in big if 7 <= n <= 10 and t7_cert(k, n) is not None]
    assert found == T7_WEIGHTS, found
    files = {
        OUT_SMALL: render(sorted(small),
                          ["MathProof.ModularForms.HeckeRingGens",
                           "MathProof.ModularForms.MaedaT3SmallWeights"],
                          "dims 2–5", NOTE_SMALL),
        OUT_BIG: render(big,
                        ["MathProof.ModularForms.HeckeRingGens"]
                        + [f"MathProof.ModularForms.MaedaT3Dim{d}Weights" for d in range(6, 11)],
                        "dims 6–10", NOTE_BIG),
    }
    for path, text in files.items():
        for ln, line in enumerate(text.splitlines(), 1):
            assert len(line) <= 100, (path.name, ln, line)
    if "--check" in sys.argv:
        bad = [p.name for p, t in files.items() if not p.exists() or p.read_text() != t]
        if bad:
            print("MISMATCH:", bad)
            sys.exit(1)
        print("OK: byte-identical")
        return
    for path, text in files.items():
        path.write_text(text)
        print("wrote", path.relative_to(ROOT), len(text.splitlines()), "lines")


if __name__ == "__main__":
    main()
