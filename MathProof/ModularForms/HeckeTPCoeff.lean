import MathProof.ModularForms.MaedaLevelOne

/-!
# The q-coefficient formula of `T_p` at natural weight, any prime `p`

`heckeT2_coeff` (in `MaedaLevelOne`) wraps the coefficient formula of the
Hecke operator `T₂` at natural weight `K`.  The underlying theorem
`heckeTP_qExpansion_coeff` is prime-generic; this module lifts the wrapper to
any prime `p`, so generated weight files can speak about `T₃` (or any `T_p`)
without editing `MaedaLevelOne` — an ancestor of the heavy `MaedaGalois5`
chain.  Kept in its own light module for exactly that reason.
-/

open UpperHalfPlane ModularForm CuspForm HeckeLevelOne Polynomial
open scoped MatrixGroups

namespace MaedaLevelOne

/-- The q-coefficients of `T_p f` in natural weight `K ≥ 1`, for any prime
`p`:  `(T_p f)_m = f_{p m} + p^(K-1) [p ∣ m] f_{m / p}`.  The `p = 2` case is
`heckeT2_coeff`; the proof is p-uniform. -/
lemma heckeTP_coeff {K : ℕ} (hK : 1 ≤ K) {p : ℕ} (hp : p.Prime)
    (f : CuspForm 𝒮ℒ (K : ℤ)) (m : ℕ) :
    (qExpansion 1 (heckeTPₗ (K : ℤ) hp f)).coeff m
      = (qExpansion 1 f).coeff (p * m)
        + (p : ℂ) ^ (K - 1)
          * (if p ∣ m then (qExpansion 1 f).coeff (m / p) else 0) := by
  rw [show heckeTPₗ (K : ℤ) hp f = heckeTP hp f from rfl, heckeTP_qExpansion_coeff,
    show ((K : ℤ) - 1) = ((K - 1 : ℕ) : ℤ) by omega, zpow_natCast]

end MaedaLevelOne
