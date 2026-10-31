import Mathlib.Tactic.NormDet
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Characteristic polynomials by certified determinant interpolation

The dimension-generic engine behind the Maeda weights of dimensions 6-10
(iteration 19): the characteristic polynomial of an integer `n × n` matrix is
pinned down by its values at the `n + 1` points `0, …, n`, and each value is
`det (t · 1 − M)` — supplied per point by Mathlib's certified Bareiss echelon
decomposition (the `eval_det` tactic, `Mathlib.Tactic.NormDet`).

* `CharpolyEngine.charpoly_of_eval_eq` — a polynomial `P : ℤ[X]` of degree
  `n` agreeing with `M.charpoly` at the `n + 1` points `0, …, n` equals
  `M.charpoly`.  Nothing here is dimension-specific; per weight, the
  determinant values are separate `eval_det` lemmas and the polynomial
  evaluations are `norm_num` lemmas (the validated pilot,
  `blueprint/lean/CharpolyInterpSketch.lean`).

The generated weight files assemble this with `RabinCert.irreducible_of_rabin_int`
to obtain irreducibility of `charpoly (T₂ | S_k)` over `ℚ`.
-/

namespace CharpolyEngine

open Polynomial Matrix

/-- **Generic charpoly engine (core lemma).**  A `P` of degree `n` whose
evaluations at the `n + 1` points `0, 1, …, n` agree with `det (t·1 − M)` is the
characteristic polynomial of `M`.  The determinant values are supplied per
point (by `eval_det`); nothing here is dimension-specific. -/
theorem charpoly_of_eval_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (P : ℤ[X])
    (hdeg : P.natDegree = n)
    (h : ∀ i : Fin (n + 1), P.eval ((i : ℕ) : ℤ)
      = (Matrix.scalar (Fin n) ((i : ℕ) : ℤ) - M).det) :
    M.charpoly = P := by
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq M.charpoly P (f := fun i : Fin (n + 1) =>
    ((i : ℕ) : ℤ)) (fun a b hab => Fin.ext (Nat.cast_injective hab)) ?_ ?_
  · intro i
    rw [Matrix.eval_charpoly]
    exact (h i).symm
  · rw [Matrix.charpoly_natDegree_eq_dim, hdeg]
    simp

end CharpolyEngine
