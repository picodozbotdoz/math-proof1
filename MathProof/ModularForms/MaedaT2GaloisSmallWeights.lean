import MathProof.ModularForms.MaedaWeight24
import MathProof.ModularForms.MaedaSmallWeights
import MathProof.ModularForms.MaedaGaloisQuad

/-!
# Maeda's conjecture in full, T₂ twin, the six dim-2 weights: `Gal = S₂`

The degree-2 corner of the `Gal = Sₙ` run for the `T₂` characteristic
polynomials, closing the T₂-Gal-dim-2 gap (iteration22-review §6.3): the
existing `Gal = Sₙ` files for `T₂` start at dim 3 (`MaedaGalois`,
`MaedaGalois4`, `MaedaGalois5Weights`, `MaedaGaloisDim{6..10}Weights`), and
an irreducible quadratic already has `Gal = S₂`
(`MaedaGaloisQuad.bijective_of_quadratic`).  Each instance consumes only
landed inputs — the `P` / `charpoly_T2` / `maeda` of `MaedaWeight24` and
`MaedaSmallWeights` (weight 24's charpoly is proved in `MaedaWeight24` itself
with its own naming) — so this file adds no new kernel decides.  With it,
Maeda's `Gal = Sₙ` holds at every verified weight for BOTH generators `T₂`
(now including dim 2) and `T₃` (whose dim-2 corner is
`MaedaT3GaloisSmallWeights`).

Everything is light: no `set_option`, and no module in this file is an
ancestor of the heavy `MaedaGalois5Defs` chain.  All its parents are already
default targets / CI items and the file is a few seconds of elaboration, so
it is registered in the trio (`defaultTargets`, the root `MathProof.lean`,
and the CI build list).
-/

open Polynomial

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-! ### Weight 24 (dim 2) -/
namespace MaedaWeight24

lemma P24_natDegree : P24.natDegree = 2 := by
  unfold P24; compute_degree!

/-- **Maeda's conjecture in full in weight 24 (dim 2)**: `Gal = S₂`. -/
theorem maeda_galois_full :
    Function.Bijective (Gal.galActionHom (P24.map (Int.castRingHom ℚ)) ℂ) :=
  MaedaGaloisQuad.bijective_of_quadratic P24_monic P24_natDegree maeda_weight24

end MaedaWeight24

/-! ### Weight 28 (dim 2) -/
namespace MaedaWeight28

lemma P_monic : P.Monic := by
  unfold P; monicity!

lemma P_natDegree : P.natDegree = 2 := by
  unfold P; compute_degree!

/-- **Maeda's conjecture in full in weight 28 (dim 2)**: `Gal = S₂`. -/
theorem maeda_galois_full :
    Function.Bijective (Gal.galActionHom (P.map (Int.castRingHom ℚ)) ℂ) :=
  MaedaGaloisQuad.bijective_of_quadratic P_monic P_natDegree maeda

end MaedaWeight28

/-! ### Weight 30 (dim 2) -/
namespace MaedaWeight30

lemma P_monic : P.Monic := by
  unfold P; monicity!

lemma P_natDegree : P.natDegree = 2 := by
  unfold P; compute_degree!

/-- **Maeda's conjecture in full in weight 30 (dim 2)**: `Gal = S₂`. -/
theorem maeda_galois_full :
    Function.Bijective (Gal.galActionHom (P.map (Int.castRingHom ℚ)) ℂ) :=
  MaedaGaloisQuad.bijective_of_quadratic P_monic P_natDegree maeda

end MaedaWeight30

/-! ### Weight 32 (dim 2) -/
namespace MaedaWeight32

lemma P_monic : P.Monic := by
  unfold P; monicity!

lemma P_natDegree : P.natDegree = 2 := by
  unfold P; compute_degree!

/-- **Maeda's conjecture in full in weight 32 (dim 2)**: `Gal = S₂`. -/
theorem maeda_galois_full :
    Function.Bijective (Gal.galActionHom (P.map (Int.castRingHom ℚ)) ℂ) :=
  MaedaGaloisQuad.bijective_of_quadratic P_monic P_natDegree maeda

end MaedaWeight32

/-! ### Weight 34 (dim 2) -/
namespace MaedaWeight34

lemma P_monic : P.Monic := by
  unfold P; monicity!

lemma P_natDegree : P.natDegree = 2 := by
  unfold P; compute_degree!

/-- **Maeda's conjecture in full in weight 34 (dim 2)**: `Gal = S₂`. -/
theorem maeda_galois_full :
    Function.Bijective (Gal.galActionHom (P.map (Int.castRingHom ℚ)) ℂ) :=
  MaedaGaloisQuad.bijective_of_quadratic P_monic P_natDegree maeda

end MaedaWeight34

/-! ### Weight 38 (dim 2) -/
namespace MaedaWeight38

lemma P_monic : P.Monic := by
  unfold P; monicity!

lemma P_natDegree : P.natDegree = 2 := by
  unfold P; compute_degree!

/-- **Maeda's conjecture in full in weight 38 (dim 2)**: `Gal = S₂`. -/
theorem maeda_galois_full :
    Function.Bijective (Gal.galActionHom (P.map (Int.castRingHom ℚ)) ℂ) :=
  MaedaGaloisQuad.bijective_of_quadratic P_monic P_natDegree maeda

end MaedaWeight38
