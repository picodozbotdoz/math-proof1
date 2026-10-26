# Iteration 14 plan — Maeda's conjecture in small weights (resumable)

Checkpoint file: resume at the first stage not marked DONE.

## Decision record

* Considered first: τ congruences mod 5, 7 via Mathlib's Ramanujan θ-formulas
  (`D E₂ ≡ Δ (mod 5)`, `D E₄ ≡ −Δ/3 (mod 7)`).  Rejected for now: the combined
  691·5·7 sieve only lifts τ's unconditional bound 70481 → 96739, while it
  needs a new q-expansion lemma for `D` (termwise differentiation).
* Chosen: **Maeda's conjecture** (Hecke algebra of S_k(SL₂ℤ) is "as large as
  possible": charpoly of T₂ irreducible over ℚ, Galois group S_d).  Open in
  general; verified numerically to large weight, never formally.  dim S_k ≥ 2
  first at k = 24.  Infrastructure reused: `HeckeLevelOne` (weight-generic
  T_p on cusp forms + coefficient formula), Mathlib Sturm bound,
  `discriminantEquiv`, charpoly/irreducibility API.

## Weight 24 data (computed)

basis f₁ = Δ E₄³ = q + 696 q² + 162252 q³ + 12831808 q⁴ + …,
      f₂ = Δ²    = q² − 48 q³ + 1080 q⁴ + …
T₂ f₁ = 696 f₁ + 20736000 f₂,  T₂ f₂ = f₁ + 384 f₂
charpoly X² − 1080 X − 20468736, disc = 576 · 144169 (non-residue mod 23).

## Stages

1. [DONE] `MathProof/ModularForms/MaedaWeight24.lean`: coefficients, coordinate
   lemma (Sturm, order > 2), T₂ matrix, basis, `heckeTPₗ` linear map,
   `LinearMap.charpoly = X² − 1080X − 20468736`, irreducible over ℚ (mod 23 +
   Gauss).
2. [ ] Generalize: dims 2 (k = 28, 30, 32, 34, 38) and 3 (k = 36, 40, …) —
   kernel-computed coefficients, cubic irreducibility mod ℓ.
3. [ ] Log / README / docs / AGENTS; commit.

## Notes for stage 2 (from the weight-24 build)

* For k ≡ 2 (mod 12) (e.g. 38) the Sturm bound ⌊k/12⌋ exceeds dim S_k − 1,
  so the coordinate lemma must come from the rank (dimension formula +
  linear independence ⇒ basis), not from Sturm.
* Coefficients beyond index 4 should be computed by `decide` on integer
  convolutions (σ is kernel-computable; τ via a lookup table equal to
  `dlt` on the needed range), not by `simp` expansion.
* `decide` must run in a context without local `Fact` instances (state the
  finite check as a top-level lemma).
