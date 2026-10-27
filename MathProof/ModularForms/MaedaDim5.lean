import MathProof.ModularForms.MaedaDim4

/-!
# Maeda's conjecture machinery in dimension 5

Extends `MathProof/ModularForms/MaedaDim4.lean` to the level-one weights with
`dim S_k = 5` (`k = 60, 64, 66, 68, 70, 74`):

* `charpoly_dim5` — the matrix of an endomorphism in a triangular basis
  `f_i = q^i + O(q^(i+1))` is read off the first five q-coefficients of the images;
* `charpoly_fin_five` — the characteristic polynomial of a `5 × 5` matrix via
  its principal-minor sums;
* `irreducible_quintic` / `irreducible_quintic_of_mod` — for degree 5, as for
  degree 4, reducible means a factor of degree ≤ 2: no root and no factorization
  into a monic quadratic `(X² + uX + v)` times a monic cubic (whose `r, s, t`
  are forced by `u, v`) certify irreducibility — a scan over `ℓ²` pairs.
-/

open UpperHalfPlane ModularForm CuspForm Polynomial
open scoped MatrixGroups

namespace MaedaLevelOne

/-! ### Irreducible quintics
-/

theorem irreducible_quintic {K : Type*} [Field K] (a b c d e : K)
    (hroot : ∀ x : K, x ^ 5 + a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e ≠ 0)
    (hquad : ∀ u v : K,
      ¬ (u * (c - v * (a - u) - u * (b - v - u * (a - u)))
          + v * (b - v - u * (a - u)) = d
        ∧ v * (c - v * (a - u) - u * (b - v - u * (a - u))) = e)) :
    Irreducible (X ^ 5 + C a * X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e : K[X]) := by
  have hmon : (X ^ 5 + C a * X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e : K[X]).Monic := by
    monicity!
  have hdeg : (X ^ 5 + C a * X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e : K[X]).natDegree
      = 5 := by
    compute_degree!
  rw [hmon.irreducible_iff_natDegree']
  refine ⟨fun h => by simp [h] at hdeg, fun f g hf hg hfg hmem => ?_⟩
  rw [hdeg, Finset.mem_Ioc] at hmem
  have hfdeg : f.natDegree + g.natDegree = 5 := by rw [← hf.natDegree_mul hg, hfg, hdeg]
  rcases (by omega : g.natDegree = 1 ∨ g.natDegree = 2) with h1 | h2
  · -- a linear factor gives a root
    set r := g.coeff 0
    have hg1 : g = X + C r := hg.eq_X_add_C h1
    apply hroot (-r)
    have h := congrArg (eval (-r)) hfg
    rw [hg1] at h
    simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C, neg_add_cancel, mul_zero] at h
    exact h.symm
  · -- a monic quadratic times a monic cubic
    have hf3 : f.natDegree = 3 := by omega
    have hfs := hf.as_sum
    have hgs := hg.as_sum
    rw [hf3] at hfs
    rw [h2] at hgs
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
      pow_one] at hfs hgs
    set r := f.coeff 2
    set s := f.coeff 1
    set t := f.coeff 0
    set u := g.coeff 1
    set v := g.coeff 0
    have hprod : f * g = X ^ 5 + C (r + u) * X ^ 4 + C (s + r * u + v) * X ^ 3
        + C (t + s * u + r * v) * X ^ 2 + C (t * u + s * v) * X + C (t * v) := by
      rw [hfs, hgs]; simp only [map_add, map_mul]; ring
    rw [hprod] at hfg
    have d4 : r + u = a := by
      have h := congrArg (fun P : K[X] => P.coeff 4) hfg
      simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at h
      norm_num at h
      exact h
    have d3 : s + r * u + v = b := by
      have h := congrArg (fun P : K[X] => P.coeff 3) hfg
      simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at h
      norm_num at h
      exact h
    have d2 : t + s * u + r * v = c := by
      have h := congrArg (fun P : K[X] => P.coeff 2) hfg
      simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at h
      norm_num at h
      exact h
    have d1 : t * u + s * v = d := by
      have h := congrArg (fun P : K[X] => P.coeff 1) hfg
      simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at h
      norm_num at h
      exact h
    have d0 : t * v = e := by
      have h := congrArg (fun P : K[X] => P.coeff 0) hfg
      simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at h
      norm_num at h
      exact h
    apply hquad u v
    have hr : a - u = r := by linear_combination -d4
    have hs : b - v - u * (a - u) = s := by linear_combination -d3 + u * d4
    have ht : c - v * (a - u) - u * (b - v - u * (a - u)) = t := by
      linear_combination -d2 + u * d3 + (v - u * u) * d4
    rw [ht, hs]
    constructor
    · linear_combination d1
    · linear_combination d0

/-- **Irreducibility over `ℚ` from a quintic certificate mod `ℓ`.** -/
theorem irreducible_quintic_of_mod {P : ℤ[X]} (hmon : P.Monic) (ℓ : ℕ) [Fact ℓ.Prime]
    (a b c d e : ZMod ℓ)
    (hmap : P.map (Int.castRingHom (ZMod ℓ)) =
      X ^ 5 + C a * X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e)
    (hroot : ∀ x : ZMod ℓ, x ^ 5 + a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e ≠ 0)
    (hquad : ∀ u v : ZMod ℓ,
      ¬ (u * (c - v * (a - u) - u * (b - v - u * (a - u)))
          + v * (b - v - u * (a - u)) = d
        ∧ v * (c - v * (a - u) - u * (b - v - u * (a - u))) = e)) :
    Irreducible (P.map (Int.castRingHom ℚ)) := by
  have hmod : Irreducible (P.map (Int.castRingHom (ZMod ℓ))) := by
    rw [hmap]; exact irreducible_quintic a b c d e hroot hquad
  have hZ : Irreducible P :=
    Polynomial.Monic.irreducible_of_irreducible_map (φ := Int.castRingHom (ZMod ℓ)) P hmon hmod
  have hQ := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ) hmon).mp hZ
  simpa [algebraMap_int_eq] using hQ

/-! ### `5 × 5` characteristic polynomials
-/

/-- The characteristic polynomial of a `5 × 5` matrix: `X⁵ − e₁X⁴ + e₂X³ − e₃X² +
e₄X − det`, with `e_i` the sums of principal `i × i` minors. -/
lemma charpoly_fin_five {R : Type*} [CommRing R] (M : Matrix (Fin 5) (Fin 5) R) :
    M.charpoly = X ^ 5 - C (M 0 0 + M 1 1 + M 2 2 + M 3 3 + M 4 4) * X ^ 4
      + C ((M 0 0 * M 1 1 - M 0 1 * M 1 0) + (M 0 0 * M 2 2 - M 0 2 * M 2 0) + (M 0 0 * M
           3 3 - M 0 3 * M 3 0) + (M 0 0 * M 4 4 - M 0 4 * M 4 0) + (M 1 1 * M 2 2 - M 1 2
           * M 2 1) + (M 1 1 * M 3 3 - M 1 3 * M 3 1) + (M 1 1 * M 4 4 - M 1 4 * M 4 1) +
           (M 2 2 * M 3 3 - M 2 3 * M 3 2) + (M 2 2 * M 4 4 - M 2 4 * M 4 2) + (M 3 3 * M
           4 4 - M 3 4 * M 4 3)) * X ^ 3
      - C ((M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 * M 2 1 - M 0 1 * M 1 0 * M 2 2 + M 0 1
           * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0) + (M 0 0 * M 1
           1 * M 3 3 - M 0 0 * M 1 3 * M 3 1 - M 0 1 * M 1 0 * M 3 3 + M 0 1 * M 1 3 * M 3
           0 + M 0 3 * M 1 0 * M 3 1 - M 0 3 * M 1 1 * M 3 0) + (M 0 0 * M 1 1 * M 4 4 - M
           0 0 * M 1 4 * M 4 1 - M 0 1 * M 1 0 * M 4 4 + M 0 1 * M 1 4 * M 4 0 + M 0 4 * M
           1 0 * M 4 1 - M 0 4 * M 1 1 * M 4 0) + (M 0 0 * M 2 2 * M 3 3 - M 0 0 * M 2 3 *
           M 3 2 - M 0 2 * M 2 0 * M 3 3 + M 0 2 * M 2 3 * M 3 0 + M 0 3 * M 2 0 * M 3 2 -
           M 0 3 * M 2 2 * M 3 0) + (M 0 0 * M 2 2 * M 4 4 - M 0 0 * M 2 4 * M 4 2 - M 0 2
           * M 2 0 * M 4 4 + M 0 2 * M 2 4 * M 4 0 + M 0 4 * M 2 0 * M 4 2 - M 0 4 * M 2 2
           * M 4 0) + (M 0 0 * M 3 3 * M 4 4 - M 0 0 * M 3 4 * M 4 3 - M 0 3 * M 3 0 * M 4
           4 + M 0 3 * M 3 4 * M 4 0 + M 0 4 * M 3 0 * M 4 3 - M 0 4 * M 3 3 * M 4 0) + (M
           1 1 * M 2 2 * M 3 3 - M 1 1 * M 2 3 * M 3 2 - M 1 2 * M 2 1 * M 3 3 + M 1 2 * M
           2 3 * M 3 1 + M 1 3 * M 2 1 * M 3 2 - M 1 3 * M 2 2 * M 3 1) + (M 1 1 * M 2 2 *
           M 4 4 - M 1 1 * M 2 4 * M 4 2 - M 1 2 * M 2 1 * M 4 4 + M 1 2 * M 2 4 * M 4 1 +
           M 1 4 * M 2 1 * M 4 2 - M 1 4 * M 2 2 * M 4 1) + (M 1 1 * M 3 3 * M 4 4 - M 1 1
           * M 3 4 * M 4 3 - M 1 3 * M 3 1 * M 4 4 + M 1 3 * M 3 4 * M 4 1 + M 1 4 * M 3 1
           * M 4 3 - M 1 4 * M 3 3 * M 4 1) + (M 2 2 * M 3 3 * M 4 4 - M 2 2 * M 3 4 * M 4
           3 - M 2 3 * M 3 2 * M 4 4 + M 2 3 * M 3 4 * M 4 2 + M 2 4 * M 3 2 * M 4 3 - M 2
           4 * M 3 3 * M 4 2)) * X ^ 2
      + C ((M 0 0 * (M 1 1 * M 2 2 * M 3 3 - M 1 1 * M 2 3 * M 3 2 - M 1 2 * M 2 1 * M 3 3 + M 1
           2 * M 2 3 * M 3 1 + M 1 3 * M 2 1 * M 3 2 - M 1 3 * M 2 2 * M 3 1) - M 0 1 * (M 1 0 *
           M 2 2 * M 3 3 - M 1 0 * M 2 3 * M 3 2 - M 1 2 * M 2 0 * M 3 3 + M 1 2 * M 2 3 * M 3 0
           + M 1 3 * M 2 0 * M 3 2 - M 1 3 * M 2 2 * M 3 0) + M 0 2 * (M 1 0 * M 2 1 * M 3 3 - M
           1 0 * M 2 3 * M 3 1 - M 1 1 * M 2 0 * M 3 3 + M 1 1 * M 2 3 * M 3 0 + M 1 3 * M 2 0 *
           M 3 1 - M 1 3 * M 2 1 * M 3 0) - M 0 3 * (M 1 0 * M 2 1 * M 3 2 - M 1 0 * M 2 2 * M 3
           1 - M 1 1 * M 2 0 * M 3 2 + M 1 1 * M 2 2 * M 3 0 + M 1 2 * M 2 0 * M 3 1 - M 1 2 * M
           2 1 * M 3 0)) + (M 0 0 * (M 1 1 * M 2 2 * M 4 4 - M 1 1 * M 2 4 * M 4 2 - M 1 2 * M 2
           1 * M 4 4 + M 1 2 * M 2 4 * M 4 1 + M 1 4 * M 2 1 * M 4 2 - M 1 4 * M 2 2 * M 4 1) -
           M 0 1 * (M 1 0 * M 2 2 * M 4 4 - M 1 0 * M 2 4 * M 4 2 - M 1 2 * M 2 0 * M 4 4 + M 1
           2 * M 2 4 * M 4 0 + M 1 4 * M 2 0 * M 4 2 - M 1 4 * M 2 2 * M 4 0) + M 0 2 * (M 1 0 *
           M 2 1 * M 4 4 - M 1 0 * M 2 4 * M 4 1 - M 1 1 * M 2 0 * M 4 4 + M 1 1 * M 2 4 * M 4 0
           + M 1 4 * M 2 0 * M 4 1 - M 1 4 * M 2 1 * M 4 0) - M 0 4 * (M 1 0 * M 2 1 * M 4 2 - M
           1 0 * M 2 2 * M 4 1 - M 1 1 * M 2 0 * M 4 2 + M 1 1 * M 2 2 * M 4 0 + M 1 2 * M 2 0 *
           M 4 1 - M 1 2 * M 2 1 * M 4 0)) + (M 0 0 * (M 1 1 * M 3 3 * M 4 4 - M 1 1 * M 3 4 * M
           4 3 - M 1 3 * M 3 1 * M 4 4 + M 1 3 * M 3 4 * M 4 1 + M 1 4 * M 3 1 * M 4 3 - M 1 4 *
           M 3 3 * M 4 1) - M 0 1 * (M 1 0 * M 3 3 * M 4 4 - M 1 0 * M 3 4 * M 4 3 - M 1 3 * M 3
           0 * M 4 4 + M 1 3 * M 3 4 * M 4 0 + M 1 4 * M 3 0 * M 4 3 - M 1 4 * M 3 3 * M 4 0) +
           M 0 3 * (M 1 0 * M 3 1 * M 4 4 - M 1 0 * M 3 4 * M 4 1 - M 1 1 * M 3 0 * M 4 4 + M 1
           1 * M 3 4 * M 4 0 + M 1 4 * M 3 0 * M 4 1 - M 1 4 * M 3 1 * M 4 0) - M 0 4 * (M 1 0 *
           M 3 1 * M 4 3 - M 1 0 * M 3 3 * M 4 1 - M 1 1 * M 3 0 * M 4 3 + M 1 1 * M 3 3 * M 4 0
           + M 1 3 * M 3 0 * M 4 1 - M 1 3 * M 3 1 * M 4 0)) + (M 0 0 * (M 2 2 * M 3 3 * M 4 4 -
           M 2 2 * M 3 4 * M 4 3 - M 2 3 * M 3 2 * M 4 4 + M 2 3 * M 3 4 * M 4 2 + M 2 4 * M 3 2
           * M 4 3 - M 2 4 * M 3 3 * M 4 2) - M 0 2 * (M 2 0 * M 3 3 * M 4 4 - M 2 0 * M 3 4 * M
           4 3 - M 2 3 * M 3 0 * M 4 4 + M 2 3 * M 3 4 * M 4 0 + M 2 4 * M 3 0 * M 4 3 - M 2 4 *
           M 3 3 * M 4 0) + M 0 3 * (M 2 0 * M 3 2 * M 4 4 - M 2 0 * M 3 4 * M 4 2 - M 2 2 * M 3
           0 * M 4 4 + M 2 2 * M 3 4 * M 4 0 + M 2 4 * M 3 0 * M 4 2 - M 2 4 * M 3 2 * M 4 0) -
           M 0 4 * (M 2 0 * M 3 2 * M 4 3 - M 2 0 * M 3 3 * M 4 2 - M 2 2 * M 3 0 * M 4 3 + M 2
           2 * M 3 3 * M 4 0 + M 2 3 * M 3 0 * M 4 2 - M 2 3 * M 3 2 * M 4 0)) + (M 1 1 * (M 2 2
           * M 3 3 * M 4 4 - M 2 2 * M 3 4 * M 4 3 - M 2 3 * M 3 2 * M 4 4 + M 2 3 * M 3 4 * M 4
           2 + M 2 4 * M 3 2 * M 4 3 - M 2 4 * M 3 3 * M 4 2) - M 1 2 * (M 2 1 * M 3 3 * M 4 4 -
           M 2 1 * M 3 4 * M 4 3 - M 2 3 * M 3 1 * M 4 4 + M 2 3 * M 3 4 * M 4 1 + M 2 4 * M 3 1
           * M 4 3 - M 2 4 * M 3 3 * M 4 1) + M 1 3 * (M 2 1 * M 3 2 * M 4 4 - M 2 1 * M 3 4 * M
           4 2 - M 2 2 * M 3 1 * M 4 4 + M 2 2 * M 3 4 * M 4 1 + M 2 4 * M 3 1 * M 4 2 - M 2 4 *
           M 3 2 * M 4 1) - M 1 4 * (M 2 1 * M 3 2 * M 4 3 - M 2 1 * M 3 3 * M 4 2 - M 2 2 * M 3
           1 * M 4 3 + M 2 2 * M 3 3 * M 4 1 + M 2 3 * M 3 1 * M 4 2 - M 2 3 * M 3 2 * M 4 1))) * X
      - C (M 0 0 * (M 1 1 * (M 2 2 * M 3 3 * M 4 4 - M 2 2 * M 3 4 * M 4 3 - M 2 3 * M 3 2 * M 4
           4 + M 2 3 * M 3 4 * M 4 2 + M 2 4 * M 3 2 * M 4 3 - M 2 4 * M 3 3 * M 4 2) - M 1 2 *
           (M 2 1 * M 3 3 * M 4 4 - M 2 1 * M 3 4 * M 4 3 - M 2 3 * M 3 1 * M 4 4 + M 2 3 * M 3
           4 * M 4 1 + M 2 4 * M 3 1 * M 4 3 - M 2 4 * M 3 3 * M 4 1) + M 1 3 * (M 2 1 * M 3 2 *
           M 4 4 - M 2 1 * M 3 4 * M 4 2 - M 2 2 * M 3 1 * M 4 4 + M 2 2 * M 3 4 * M 4 1 + M 2 4
           * M 3 1 * M 4 2 - M 2 4 * M 3 2 * M 4 1) - M 1 4 * (M 2 1 * M 3 2 * M 4 3 - M 2 1 * M
           3 3 * M 4 2 - M 2 2 * M 3 1 * M 4 3 + M 2 2 * M 3 3 * M 4 1 + M 2 3 * M 3 1 * M 4 2 -
           M 2 3 * M 3 2 * M 4 1)) - M 0 1 * (M 1 0 * (M 2 2 * M 3 3 * M 4 4 - M 2 2 * M 3 4 * M
           4 3 - M 2 3 * M 3 2 * M 4 4 + M 2 3 * M 3 4 * M 4 2 + M 2 4 * M 3 2 * M 4 3 - M 2 4 *
           M 3 3 * M 4 2) - M 1 2 * (M 2 0 * M 3 3 * M 4 4 - M 2 0 * M 3 4 * M 4 3 - M 2 3 * M 3
           0 * M 4 4 + M 2 3 * M 3 4 * M 4 0 + M 2 4 * M 3 0 * M 4 3 - M 2 4 * M 3 3 * M 4 0) +
           M 1 3 * (M 2 0 * M 3 2 * M 4 4 - M 2 0 * M 3 4 * M 4 2 - M 2 2 * M 3 0 * M 4 4 + M 2
           2 * M 3 4 * M 4 0 + M 2 4 * M 3 0 * M 4 2 - M 2 4 * M 3 2 * M 4 0) - M 1 4 * (M 2 0 *
           M 3 2 * M 4 3 - M 2 0 * M 3 3 * M 4 2 - M 2 2 * M 3 0 * M 4 3 + M 2 2 * M 3 3 * M 4 0
           + M 2 3 * M 3 0 * M 4 2 - M 2 3 * M 3 2 * M 4 0)) + M 0 2 * (M 1 0 * (M 2 1 * M 3 3 *
           M 4 4 - M 2 1 * M 3 4 * M 4 3 - M 2 3 * M 3 1 * M 4 4 + M 2 3 * M 3 4 * M 4 1 + M 2 4
           * M 3 1 * M 4 3 - M 2 4 * M 3 3 * M 4 1) - M 1 1 * (M 2 0 * M 3 3 * M 4 4 - M 2 0 * M
           3 4 * M 4 3 - M 2 3 * M 3 0 * M 4 4 + M 2 3 * M 3 4 * M 4 0 + M 2 4 * M 3 0 * M 4 3 -
           M 2 4 * M 3 3 * M 4 0) + M 1 3 * (M 2 0 * M 3 1 * M 4 4 - M 2 0 * M 3 4 * M 4 1 - M 2
           1 * M 3 0 * M 4 4 + M 2 1 * M 3 4 * M 4 0 + M 2 4 * M 3 0 * M 4 1 - M 2 4 * M 3 1 * M
           4 0) - M 1 4 * (M 2 0 * M 3 1 * M 4 3 - M 2 0 * M 3 3 * M 4 1 - M 2 1 * M 3 0 * M 4 3
           + M 2 1 * M 3 3 * M 4 0 + M 2 3 * M 3 0 * M 4 1 - M 2 3 * M 3 1 * M 4 0)) - M 0 3 *
           (M 1 0 * (M 2 1 * M 3 2 * M 4 4 - M 2 1 * M 3 4 * M 4 2 - M 2 2 * M 3 1 * M 4 4 + M 2
           2 * M 3 4 * M 4 1 + M 2 4 * M 3 1 * M 4 2 - M 2 4 * M 3 2 * M 4 1) - M 1 1 * (M 2 0 *
           M 3 2 * M 4 4 - M 2 0 * M 3 4 * M 4 2 - M 2 2 * M 3 0 * M 4 4 + M 2 2 * M 3 4 * M 4 0
           + M 2 4 * M 3 0 * M 4 2 - M 2 4 * M 3 2 * M 4 0) + M 1 2 * (M 2 0 * M 3 1 * M 4 4 - M
           2 0 * M 3 4 * M 4 1 - M 2 1 * M 3 0 * M 4 4 + M 2 1 * M 3 4 * M 4 0 + M 2 4 * M 3 0 *
           M 4 1 - M 2 4 * M 3 1 * M 4 0) - M 1 4 * (M 2 0 * M 3 1 * M 4 2 - M 2 0 * M 3 2 * M 4
           1 - M 2 1 * M 3 0 * M 4 2 + M 2 1 * M 3 2 * M 4 0 + M 2 2 * M 3 0 * M 4 1 - M 2 2 * M
           3 1 * M 4 0)) + M 0 4 * (M 1 0 * (M 2 1 * M 3 2 * M 4 3 - M 2 1 * M 3 3 * M 4 2 - M 2
           2 * M 3 1 * M 4 3 + M 2 2 * M 3 3 * M 4 1 + M 2 3 * M 3 1 * M 4 2 - M 2 3 * M 3 2 * M
           4 1) - M 1 1 * (M 2 0 * M 3 2 * M 4 3 - M 2 0 * M 3 3 * M 4 2 - M 2 2 * M 3 0 * M 4 3
           + M 2 2 * M 3 3 * M 4 0 + M 2 3 * M 3 0 * M 4 2 - M 2 3 * M 3 2 * M 4 0) + M 1 2 * (M
           2 0 * M 3 1 * M 4 3 - M 2 0 * M 3 3 * M 4 1 - M 2 1 * M 3 0 * M 4 3 + M 2 1 * M 3 3 *
           M 4 0 + M 2 3 * M 3 0 * M 4 1 - M 2 3 * M 3 1 * M 4 0) - M 1 3 * (M 2 0 * M 3 1 * M 4
           2 - M 2 0 * M 3 2 * M 4 1 - M 2 1 * M 3 0 * M 4 2 + M 2 1 * M 3 2 * M 4 0 + M 2 2 * M
           3 0 * M 4 1 - M 2 2 * M 3 1 * M 4 0))) := by
  rw [Matrix.charpoly, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix_apply,
    Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.succAbove]
  ring

/-! ### Dimension 5
-/

/-- **Dimension 5.**  For a triangular basis `f_i = q^i + ⋯` of a 5-dimensional
`S_k` (coefficients `a_im`), the matrix of `T` is read off the first five
coefficients `x_jm` of `T f_j` by back-substitution. -/
theorem charpoly_dim5 {k : ℤ} (hdim : Module.finrank ℂ (CuspForm 𝒮ℒ k) = 5)
    (f1 f2 f3 f4 f5 : CuspForm 𝒮ℒ k) {a12 a13 a14 a15 a23 a24 a25 a34 a35 a45 : ℂ}
    (h11 : (qExpansion 1 f1).coeff 1 = 1) (h12 : (qExpansion 1 f1).coeff 2 = a12)
    (h13 : (qExpansion 1 f1).coeff 3 = a13) (h14 : (qExpansion 1 f1).coeff 4 = a14)
    (h15 : (qExpansion 1 f1).coeff 5 = a15) (h21 : (qExpansion 1 f2).coeff 1 = 0)
    (h22 : (qExpansion 1 f2).coeff 2 = 1) (h23 : (qExpansion 1 f2).coeff 3 = a23)
    (h24 : (qExpansion 1 f2).coeff 4 = a24) (h25 : (qExpansion 1 f2).coeff 5 = a25)
    (h31 : (qExpansion 1 f3).coeff 1 = 0) (h32 : (qExpansion 1 f3).coeff 2 = 0)
    (h33 : (qExpansion 1 f3).coeff 3 = 1) (h34 : (qExpansion 1 f3).coeff 4 = a34)
    (h35 : (qExpansion 1 f3).coeff 5 = a35) (h41 : (qExpansion 1 f4).coeff 1 = 0)
    (h42 : (qExpansion 1 f4).coeff 2 = 0) (h43 : (qExpansion 1 f4).coeff 3 = 0)
    (h44 : (qExpansion 1 f4).coeff 4 = 1) (h45 : (qExpansion 1 f4).coeff 5 = a45)
    (h51 : (qExpansion 1 f5).coeff 1 = 0) (h52 : (qExpansion 1 f5).coeff 2 = 0)
    (h53 : (qExpansion 1 f5).coeff 3 = 0) (h54 : (qExpansion 1 f5).coeff 4 = 0)
    (h55 : (qExpansion 1 f5).coeff 5 = 1)
    (T : CuspForm 𝒮ℒ k →ₗ[ℂ] CuspForm 𝒮ℒ k)
    {x11 x12 x13 x14 x15 x21 x22 x23 x24 x25 x31 x32 x33 x34 x35 x41 x42 x43 x44 x45 x51 x52 x53 x54
     x55 : ℂ}
    (hx11 : (qExpansion 1 (T f1)).coeff 1 = x11) (hx12 : (qExpansion 1 (T f1)).coeff 2 = x12)
    (hx13 : (qExpansion 1 (T f1)).coeff 3 = x13) (hx14 : (qExpansion 1 (T f1)).coeff 4 = x14)
    (hx15 : (qExpansion 1 (T f1)).coeff 5 = x15) (hx21 : (qExpansion 1 (T f2)).coeff 1 = x21)
    (hx22 : (qExpansion 1 (T f2)).coeff 2 = x22) (hx23 : (qExpansion 1 (T f2)).coeff 3 = x23)
    (hx24 : (qExpansion 1 (T f2)).coeff 4 = x24) (hx25 : (qExpansion 1 (T f2)).coeff 5 = x25)
    (hx31 : (qExpansion 1 (T f3)).coeff 1 = x31) (hx32 : (qExpansion 1 (T f3)).coeff 2 = x32)
    (hx33 : (qExpansion 1 (T f3)).coeff 3 = x33) (hx34 : (qExpansion 1 (T f3)).coeff 4 = x34)
    (hx35 : (qExpansion 1 (T f3)).coeff 5 = x35) (hx41 : (qExpansion 1 (T f4)).coeff 1 = x41)
    (hx42 : (qExpansion 1 (T f4)).coeff 2 = x42) (hx43 : (qExpansion 1 (T f4)).coeff 3 = x43)
    (hx44 : (qExpansion 1 (T f4)).coeff 4 = x44) (hx45 : (qExpansion 1 (T f4)).coeff 5 = x45)
    (hx51 : (qExpansion 1 (T f5)).coeff 1 = x51) (hx52 : (qExpansion 1 (T f5)).coeff 2 = x52)
    (hx53 : (qExpansion 1 (T f5)).coeff 3 = x53) (hx54 : (qExpansion 1 (T f5)).coeff 4 = x54)
    (hx55 : (qExpansion 1 (T f5)).coeff 5 = x55) :
    T.charpoly = Matrix.charpoly !![x11,
      x21,
      x31,
      x41,
      x51;
      (x12 - a12 * x11),
      (x22 - a12 * x21),
      (x32 - a12 * x31),
      (x42 - a12 * x41),
      (x52 - a12 * x51);
      (x13 - a13 * x11 - a23 * (x12 - a12 * x11)),
      (x23 - a13 * x21 - a23 * (x22 - a12 * x21)),
      (x33 - a13 * x31 - a23 * (x32 - a12 * x31)),
      (x43 - a13 * x41 - a23 * (x42 - a12 * x41)),
      (x53 - a13 * x51 - a23 * (x52 - a12 * x51));
      (x14 - a14 * x11 - a24 * (x12 - a12 * x11) - a34 * (x13 - a13 * x11 - a23 * (x12 - a12 *
        x11))),
      (x24 - a14 * x21 - a24 * (x22 - a12 * x21) - a34 * (x23 - a13 * x21 - a23 * (x22 - a12 *
        x21))),
      (x34 - a14 * x31 - a24 * (x32 - a12 * x31) - a34 * (x33 - a13 * x31 - a23 * (x32 - a12 *
        x31))),
      (x44 - a14 * x41 - a24 * (x42 - a12 * x41) - a34 * (x43 - a13 * x41 - a23 * (x42 - a12 *
        x41))),
      (x54 - a14 * x51 - a24 * (x52 - a12 * x51) - a34 * (x53 - a13 * x51 - a23 * (x52 - a12 *
        x51)));
      (x15 - a15 * x11 - a25 * (x12 - a12 * x11) - a35 * (x13 - a13 * x11 - a23 * (x12 - a12 *
        x11)) - a45 * (x14 - a14 * x11 - a24 * (x12 - a12 * x11) - a34 * (x13 - a13 * x11 - a23
        * (x12 - a12 * x11)))),
      (x25 - a15 * x21 - a25 * (x22 - a12 * x21) - a35 * (x23 - a13 * x21 - a23 * (x22 - a12 *
        x21)) - a45 * (x24 - a14 * x21 - a24 * (x22 - a12 * x21) - a34 * (x23 - a13 * x21 - a23
        * (x22 - a12 * x21)))),
      (x35 - a15 * x31 - a25 * (x32 - a12 * x31) - a35 * (x33 - a13 * x31 - a23 * (x32 - a12 *
        x31)) - a45 * (x34 - a14 * x31 - a24 * (x32 - a12 * x31) - a34 * (x33 - a13 * x31 - a23
        * (x32 - a12 * x31)))),
      (x45 - a15 * x41 - a25 * (x42 - a12 * x41) - a35 * (x43 - a13 * x41 - a23 * (x42 - a12 *
        x41)) - a45 * (x44 - a14 * x41 - a24 * (x42 - a12 * x41) - a34 * (x43 - a13 * x41 - a23
        * (x42 - a12 * x41)))),
      (x55 - a15 * x51 - a25 * (x52 - a12 * x51) - a35 * (x53 - a13 * x51 - a23 * (x52 - a12 *
        x51)) - a45 * (x54 - a14 * x51 - a24 * (x52 - a12 * x51) - a34 * (x53 - a13 * x51 - a23
        * (x52 - a12 * x51))))] := by
  have hli : LinearIndependent ℂ ![f1, f2, f3, f4, f5] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := coeff_sum Finset.univ g ![f1, f2, f3, f4, f5] 1
    have h2 := coeff_sum Finset.univ g ![f1, f2, f3, f4, f5] 2
    have h3 := coeff_sum Finset.univ g ![f1, f2, f3, f4, f5] 3
    have h4 := coeff_sum Finset.univ g ![f1, f2, f3, f4, f5] 4
    have h5 := coeff_sum Finset.univ g ![f1, f2, f3, f4, f5] 5
    simp only [hg, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.head_cons, FunLike.coe_zero, qExpansion_zero, map_zero, h11, h21, h31, h41, h51] at h1
    simp only [hg, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.head_cons, FunLike.coe_zero, qExpansion_zero, map_zero, h12, h22, h32, h42, h52] at h2
    simp only [hg, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.head_cons, FunLike.coe_zero, qExpansion_zero, map_zero, h13, h23, h33, h43, h53] at h3
    simp only [hg, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.head_cons, FunLike.coe_zero, qExpansion_zero, map_zero, h14, h24, h34, h44, h54] at h4
    simp only [hg, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.head_cons, FunLike.coe_zero, qExpansion_zero, map_zero, h15, h25, h35, h45, h55] at h5
    have g0 : g 0 = 0 := by linear_combination -h1
    have g1 : g 1 = 0 := by linear_combination -h2 + a12 * h1
    have g2 : g 2 = 0 := by linear_combination -h3 + a13 * h1 + a23 * (h2 - a12 * h1)
    have g3 : g 3 = 0 := by linear_combination -h4 + a14 * h1 + a24 * (h2 - a12 * h1) + a34 *
                              (h3 - a13 * h1 - a23 * (h2 - a12 * h1))
    have g4 : g 4 = 0 := by linear_combination -h5 + a15 * h1 + a25 * (h2 - a12 * h1) + a35 *
                              (h3 - a13 * h1 - a23 * (h2 - a12 * h1)) + a45 * (h4 - a14 * h1 -
                              a24 * (h2 - a12 * h1) - a34 * (h3 - a13 * h1 - a23 * (h2 - a12 *
                              h1)))
    fin_cases i
    · exact g0
    · exact g1
    · exact g2
    · exact g3
    · exact g4
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb : ∀ g, b.repr g 0 = (qExpansion 1 g).coeff 1
      ∧ b.repr g 1 = ((qExpansion 1 g).coeff 2 - a12 * (qExpansion 1 g).coeff 1)
      ∧ b.repr g 2 = ((qExpansion 1 g).coeff 3 - a13 * (qExpansion 1 g).coeff 1 - a23 *
                  ((qExpansion 1 g).coeff 2 - a12 * (qExpansion 1 g).coeff 1))
      ∧ b.repr g 3 = ((qExpansion 1 g).coeff 4 - a14 * (qExpansion 1 g).coeff 1 - a24 *
                  ((qExpansion 1 g).coeff 2 - a12 * (qExpansion 1 g).coeff 1) - a34 *
                  ((qExpansion 1 g).coeff 3 - a13 * (qExpansion 1 g).coeff 1 - a23 *
                  ((qExpansion 1 g).coeff 2 - a12 * (qExpansion 1 g).coeff 1)))
      ∧ b.repr g 4 = ((qExpansion 1 g).coeff 5 - a15 * (qExpansion 1 g).coeff 1 - a25 *
                  ((qExpansion 1 g).coeff 2 - a12 * (qExpansion 1 g).coeff 1) - a35 *
                  ((qExpansion 1 g).coeff 3 - a13 * (qExpansion 1 g).coeff 1 - a23 *
                  ((qExpansion 1 g).coeff 2 - a12 * (qExpansion 1 g).coeff 1)) - a45 *
                  ((qExpansion 1 g).coeff 4 - a14 * (qExpansion 1 g).coeff 1 - a24 *
                  ((qExpansion 1 g).coeff 2 - a12 * (qExpansion 1 g).coeff 1) - a34 *
                  ((qExpansion 1 g).coeff 3 - a13 * (qExpansion 1 g).coeff 1 - a23 *
                  ((qExpansion 1 g).coeff 2 - a12 * (qExpansion 1 g).coeff 1)))) := by
    intro g
    have hs := b.sum_repr g
    have h1 := coeff_sum Finset.univ (b.repr g) b 1
    have h2 := coeff_sum Finset.univ (b.repr g) b 2
    have h3 := coeff_sum Finset.univ (b.repr g) b 3
    have h4 := coeff_sum Finset.univ (b.repr g) b 4
    have h5 := coeff_sum Finset.univ (b.repr g) b 5
    rw [hs] at h1 h2 h3 h4 h5
    simp only [Fin.sum_univ_five, b, coe_basisOfLinearIndependentOfCardEqFinrank,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons, h11, h21, h31, h41, h51] at h1
    simp only [Fin.sum_univ_five, b, coe_basisOfLinearIndependentOfCardEqFinrank,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons, h12, h22, h32, h42, h52] at h2
    simp only [Fin.sum_univ_five, b, coe_basisOfLinearIndependentOfCardEqFinrank,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons, h13, h23, h33, h43, h53] at h3
    simp only [Fin.sum_univ_five, b, coe_basisOfLinearIndependentOfCardEqFinrank,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons, h14, h24, h34, h44, h54] at h4
    simp only [Fin.sum_univ_five, b, coe_basisOfLinearIndependentOfCardEqFinrank,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons, h15, h25, h35, h45, h55] at h5
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linear_combination -h1
    · linear_combination -h2 + a12 * h1
    · linear_combination -h3 + a13 * h1 + a23 * (h2 - a12 * h1)
    · linear_combination -h4 + a14 * h1 + a24 * (h2 - a12 * h1) + a34 * (h3 - a13
                            * h1 - a23 * (h2 - a12 * h1))
    · linear_combination -h5 + a15 * h1 + a25 * (h2 - a12 * h1) + a35 * (h3 - a13
                            * h1 - a23 * (h2 - a12 * h1)) + a45 * (h4 - a14 * h1 - a24 * (h2 -
                            a12 * h1) - a34 * (h3 - a13 * h1 - a23 * (h2 - a12 * h1)))
  rw [← LinearMap.charpoly_toMatrix T b]
  congr 1
  have hb0 : b 0 = f1 := by simp [b]
  have hb1 : b 1 = f2 := by simp [b]
  have hb2 : b 2 = f3 := by simp [b]
  have hb3 : b 3 = f4 := by simp [b]
  have hb4 : b 4 = f5 := by simp [b]
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j
  · change b.repr (T (b 0)) 0 = _; rw [(hb _).1, hb0, hx11]; rfl
  · change b.repr (T (b 1)) 0 = _; rw [(hb _).1, hb1, hx21]; rfl
  · change b.repr (T (b 2)) 0 = _; rw [(hb _).1, hb2, hx31]; rfl
  · change b.repr (T (b 3)) 0 = _; rw [(hb _).1, hb3, hx41]; rfl
  · change b.repr (T (b 4)) 0 = _; rw [(hb _).1, hb4, hx51]; rfl
  · change b.repr (T (b 0)) 1 = _; rw [(hb _).2.1, hb0, hx11, hx12]; rfl
  · change b.repr (T (b 1)) 1 = _; rw [(hb _).2.1, hb1, hx21, hx22]; rfl
  · change b.repr (T (b 2)) 1 = _; rw [(hb _).2.1, hb2, hx31, hx32]; rfl
  · change b.repr (T (b 3)) 1 = _; rw [(hb _).2.1, hb3, hx41, hx42]; rfl
  · change b.repr (T (b 4)) 1 = _; rw [(hb _).2.1, hb4, hx51, hx52]; rfl
  · change b.repr (T (b 0)) 2 = _; rw [(hb _).2.2.1, hb0, hx11, hx12, hx13]; rfl
  · change b.repr (T (b 1)) 2 = _; rw [(hb _).2.2.1, hb1, hx21, hx22, hx23]; rfl
  · change b.repr (T (b 2)) 2 = _; rw [(hb _).2.2.1, hb2, hx31, hx32, hx33]; rfl
  · change b.repr (T (b 3)) 2 = _; rw [(hb _).2.2.1, hb3, hx41, hx42, hx43]; rfl
  · change b.repr (T (b 4)) 2 = _; rw [(hb _).2.2.1, hb4, hx51, hx52, hx53]; rfl
  · change b.repr (T (b 0)) 3 = _; rw [(hb _).2.2.2.1, hb0, hx11, hx12, hx13, hx14]; rfl
  · change b.repr (T (b 1)) 3 = _; rw [(hb _).2.2.2.1, hb1, hx21, hx22, hx23, hx24]; rfl
  · change b.repr (T (b 2)) 3 = _; rw [(hb _).2.2.2.1, hb2, hx31, hx32, hx33, hx34]; rfl
  · change b.repr (T (b 3)) 3 = _; rw [(hb _).2.2.2.1, hb3, hx41, hx42, hx43, hx44]; rfl
  · change b.repr (T (b 4)) 3 = _; rw [(hb _).2.2.2.1, hb4, hx51, hx52, hx53, hx54]; rfl
  · change b.repr (T (b 0)) 4 = _; rw [(hb _).2.2.2.2, hb0, hx11, hx12, hx13, hx14, hx15]; rfl
  · change b.repr (T (b 1)) 4 = _; rw [(hb _).2.2.2.2, hb1, hx21, hx22, hx23, hx24, hx25]; rfl
  · change b.repr (T (b 2)) 4 = _; rw [(hb _).2.2.2.2, hb2, hx31, hx32, hx33, hx34, hx35]; rfl
  · change b.repr (T (b 3)) 4 = _; rw [(hb _).2.2.2.2, hb3, hx41, hx42, hx43, hx44, hx45]; rfl
  · change b.repr (T (b 4)) 4 = _; rw [(hb _).2.2.2.2, hb4, hx51, hx52, hx53, hx54, hx55]; rfl

end MaedaLevelOne
