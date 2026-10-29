# Findings — Maeda's conjecture, dims 6–10 (blueprint exploration, 2026-10-29)

Scope of Task AA cycle 1: de-risk **Iteration 19** (the generic Maeda engine,
`research/maeda-scaling-study.md` §4 step 3 / `iteration18-improvements.md`
P1-4) with real data and locally elaborated Lean pilots, and collect the
Frobenius data the eventual `S_n` Galois route will need.

Everything here is research-grade: numbers are certificate *candidates*;
Lean re-checks at build time. Regression anchors: the machinery reproduces
the charpolys **proved** in `MaedaWeight24.lean` (k=24) and
`MaedaDim4Weights.lean` (k=48) exactly.

## 1. The headline: Iteration 19 is much cheaper than the study assumed

`research/maeda-scaling-study.md` planned a hand-rolled reflected Bareiss
determinant + a Sylvester-identity correctness proof as "the main new
engineering". **The pinned Mathlib (v4.36.0-rc1) already ships all of it**:

| piece | Mathlib at the pin | validated by |
|---|---|---|
| certified det of a literal matrix | `Mathlib.Tactic.NormDet` — `norm_det` simproc / `eval_det` tactic (certified Bareiss echelon decomposition, `Mathlib/Tactic/Determinant/Echelon/Cert.lean:99` `proveEchelonDet`; Bird-division-free fallback) | `blueprint/lean/CharpolyInterpSketch.lean` — 7 dets of the real dim-6 T₂ matrix |
| `charpoly.eval t = det (t·1 − M)` | `Matrix.eval_charpoly` (`LinearAlgebra/Matrix/Charpoly/Basic.lean:143`) | same sketch (the engine lemma's core rewrite) |
| interpolation from n+1 points | `Polynomial.eq_of_natDegree_lt_card_of_eval_eq` (`Algebra/Polynomial/Roots.lean:757`, ι-indexed; `'` Finset variant at :772) | same |
| `natDegree`/`Monic` for literal polys | `compute_degree!` / `monicity!` (`Mathlib/Tactic/ComputeDegree.lean`) — the project's own pattern | same |
| monic mod-ℓ irreducibility lift | `Polynomial.Monic.irreducible_of_irreducible_map` (`Algebra/Polynomial/Eval/Irreducible.lean:39`) + Gauss (`Monic.irreducible_iff_irreducible_map_fraction_map`) | already used by the project's dim 2–5 files |
| `charpoly` degree | `Matrix.charpoly_natDegree_eq_dim` (`LinearAlgebra/Matrix/Charpoly/Coeff.lean:115`, `@[simp]`) | same |
| finite-field X^q − X theory | `FiniteField.roots_X_pow_card_sub_X`, `X_pow_card_sub_X_natDegree_eq` (`FieldTheory/Finite/Basic.lean:456,443`) | — (input to the Rabin theorem, §3) |

**Measured**: the full k=72 pilot — generic engine lemma + 7 certified Bareiss
determinants of a 6×6 matrix with ≤ 33-digit entries + 7 `norm_num`
evaluations of a 61-digit-coefficient polynomial + assembly — elaborates
**in ~5 s on this laptop** (`lake env lean`, no Modal). The dim-10 numbers
(≤ 61-digit entries, ≤ 200-digit coefficients, ~180-digit determinant values)
are the same regime for GMP arithmetic.

## 2. The data: all 30 weights of dims 6–10 are Rabin-irreducible, cheaply

`maeda_dim6_10_probe.py` (3.4 s): dims 6–10 = 30 weights, k ∈ {72, 76, 78,
80, 82, 86, 84, 88, …, 120, 124, 126, 128, 130, 134} (six per dim, one per
residue class of k mod 12). Full data in `data/maeda_dim6_10.json`
(charpolys, matrices, certificate primes, census).

| dim | #weights | matrix entries | charpoly coeffs | Rabin ℓ (max) | Rabin 2nd ℓ (max) | ZMod-muls (max) |
|-----|----------|----------------|-----------------|----------------|--------------------|------------------|
| 6 | 6 | ≤ 37 digits | ≤ 75 digits | 139 | 241 | 5 756 |
| 7 | 6 | ≤ 43 | ≤ 100 | 349 | 409 | 6 752 |
| 8 | 6 | ≤ 49 | ≤ 130 | 179 | 313 | 10 732 |
| 9 | 6 | ≤ 55 | ≤ 164 | 263 | 313 | 15 584 |
| 10 | 6 | ≤ 61 | ≤ 200 | 293 | 313 | 27 950 |

The cost column counts scalar multiplications in the reflected
square-and-multiply + gcds (the exact work a kernel `decide` performs). For
scale: the dim-5 ℓ²-scan certificates (committed, `MaedaDim5Weights` ~150 s
Modal for six weights) are ~10⁵–10⁶ operations each. **Rabin at dim 6–10 is
1–3 × 10⁴ operations per weight — one to two orders cheaper than the dim-5
certificates, while the charpoly side (Bareiss at elaboration + structural
certificate for the kernel) replaces the per-dimension hand formulas.**

Validated end to end for k = 72: `RabinCertSketch.lean` decides the first
Rabin condition `X^(107⁶) mod f̄ = X` (f̄ = charpoly mod 107, exponent
1 500 730 351 849) with the reflected `List ℤ` engine —
`#print axioms rabin72_step1` = **`[propext]`** (the project's proof
standard), ~8 s local elaboration including the toy checks.

## 3. What genuinely remains to build (the blueprint's scope)

1. **The Rabin theorem** (`f̄ ∣ X^(ℓⁿ) − X` + coprimality for q ∣ n ⟹
   `Irreducible f̄` over `ZMod ℓ`) — *not* in Mathlib. Contrapositive plan:
   f̄ reducible + f̄ ∣ X^(ℓⁿ) − X ⟹ every irreducible factor's degree m
   divides n (root α of a factor lies in F_{ℓᵐ} by irreducibility and in
   F_{ℓⁿ} as a root of X^(ℓⁿ) − X; subfield lattice of finite fields ⟹ m ∣ n),
   so a proper factor divides X^(ℓ^(n/q)) − X for some prime q ∣ n, making
   the gcd nontrivial. Entry points: `FiniteField.roots_X_pow_card_sub_X`,
   finite-field degree/subfield facts (grep `FiniteField` +
   `IntermediateField`/`Polynomial.splits_iff_card`).
2. **Reflected gcd** (`zpgcd`, fuelled Euclid — same pattern as the validated
   `zprem`) + the transport lemmas from `List ℤ` to `(ZMod ℓ)[X]` (the
   `LehmerMod` mirror pattern; keep statements axiom-clean per `HornerCert`).
3. **`charpoly_dimN`** — the abstract Fin n-structural back-substitution lemma
   generalizing `charpoly_dim2/3/4` (hypothesis-bundle over a triangular
   basis, induction peeling the top basis vector).
4. **Generator** `tools/gen_maedan.py` per weight: matrix + bridge literals,
   n+1 `eval_det` dets, `zpxw` decides, assembly (~the validated sketch,
   emitted).

## 4. Frobenius census (for the future Sₙ route, free at this point)

For every weight, the smallest prime of each factorization-type class
(squarefree primes only; `disc_nonres` = discriminant is a non-residue):
see `data/maeda_dim6_10.json` (`frobenius` per weight). Summary:

* **Every one of the 30 weights** has: an n-cycle prime (= the Rabin prime),
  an (n−1)-cycle prime ≤ 199, a `disc_nonres` prime ≤ 61, and (except
  k = 134) a Jordan p-cycle prime (p ≤ n−3) ≤ 109.
* Transposition primes exist ≤ 400 for all but k = 116 (ℓ = 1609), 130, 134
  (none ≤ 3000); k = 130, 134 instead have 7-cycles (p = 7 = n−3) at ℓ = 109
  / 557, k = 134 also at ℓ = 557 (wide scan, not in the JSON).
* Conditional on a future Dedekind–Frobenius + Jordan formalization
  (`blueprint/dedekind-frobenius/BLUEPRINT.md`), this data already
  certifies **Gal = Sₙ for all 30 weights**: irreducible ⟹ transitive;
  p-cycle with p ≤ n−3 ⟹ ⊇ Aₙ (Jordan); non-square discriminant ⟹ odd
  element ⟹ = Sₙ.

## 5. Scratchpad lessons (round trips saved for the implementation)

* `Polynomial` literals are **noncomputable** (`noncomputable def P72`);
  kernel `decide` cannot reduce `natDegree`/`Monic` of them — use
  `compute_degree!` / `monicity!` (elaborator-side), `norm_num` with the
  `Polynomial.eval_*` unfolding lemmas for point evaluations.
* `eval_det` needs the matrix as a `!![…]` literal shape; `(scalar t − M)`
  is bridged by a one-time symbolic lemma (`Matrix.ext` + `fin_cases` +
  `simp`, 36 subgoals at n = 6 — seconds).
* MSB-first square-and-multiply must square *and* conditionally multiply by
  X at every bit (an accumulator scheme that only tracks powers of X² is
  wrong for MSB-first order — caught by the toy example in the sketch).
* Elaborator `decide` on the reflected `zpxw` needs
  `set_option maxRecDepth 1000000` at ℓ = 107, n = 6 (bits 41); scale by
  ~n·log₂ℓ.
* Import surface (all verified at the pin): `Mathlib.Tactic.NormDet`,
  `Mathlib.Tactic.ComputeDegree`, `Mathlib.Algebra.Polynomial.Roots`,
  `Mathlib.Algebra.Polynomial.Eval.Irreducible`,
  `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`.
