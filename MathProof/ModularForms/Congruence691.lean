import MathProof.ModularForms.Weight12
import MathProof.Tau.Bridge
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# Ramanujan's congruence `τ(n) ≡ σ₁₁(n) (mod 691)`

This file proves Ramanujan's 1916 congruence for the tau function:

    τ(n) ≡ σ₁₁(n)  [ZMOD 691]   (`RamanujanCongruence.tau_modEq_sigma`)

The proof combines three ingredients, each formally verified:

* **Ramanujan's weight-12 identity** `691 • E₁₂ = 441 • E₄³ + 250 • E₆²`
  (`RamanujanWeight12.E12_rel`, proved via the Sturm bound), coefficientwise:

      65520 • σ₁₁(n) = 441 • (E₄³)ₙ + 250 • (E₆²)ₙ;

* **Jacobi's identity** `E₄³ − E₆² = 1728 • Δ` (from Mathlib's
  `discriminant_eq_E₄_cube_sub_E₆_sq`), coefficientwise together with the
  analytic-to-algebraic bridge (`Ramanujan.qExpansion_discriminant_coeff`)
  giving `(Δ)ₙ = τ(n)`:

      (E₄³)ₙ − (E₆²)ₙ = 1728 • τ(n);

* **Integrality**: the q-expansion coefficients of `E₄` and `E₆` are
  integer-valued (`240 σ₃(n)`, `−504 σ₅(n)`), hence so are those of their
  powers, so the two coefficient identities may be read in `ℤ`.

Eliminating `(E₄³)ₙ` and `(E₆²)ₙ` between the two identities gives

    691 • 441 (E₄³)ₙ = 65520 σ₁₁(n) + 432000 τ(n),

and reducing modulo the prime 691 (using `65520 = 566 + 94 • 691`,
`762048 = 566 + 1102 • 691`, `566 = 691 − 125`) yields
`125 • (τ(n) − σ₁₁(n)) ≡ 0 [ZMOD 691]`, then cancellation of the
prime-to-691 factor `125`.
-/

open UpperHalfPlane ModularForm EisensteinSeries ArithmeticFunction Polynomial
open scoped MatrixGroups

namespace RamanujanCongruence

/-! ### Basic coefficient lemmas -/

lemma coeff_add' {P Q : PowerSeries ℂ} (n : ℕ) :
    (P + Q).coeff n = P.coeff n + Q.coeff n := rfl

lemma coeff_sub' {P Q : PowerSeries ℂ} (n : ℕ) :
    (P - Q).coeff n = P.coeff n - Q.coeff n := rfl

/-! ### Integer-valued coefficients -/

/-- Products of power series with integer-valued coefficients have
integer-valued coefficients. -/
lemma coeff_mul_intCast {P Q : PowerSeries ℂ} (hP : ∀ m, ∃ c : ℤ, P.coeff m = ((c : ℤ) : ℂ))
    (hQ : ∀ m, ∃ c : ℤ, Q.coeff m = ((c : ℤ) : ℂ)) (n : ℕ) :
    ∃ a : ℤ, (P * Q).coeff n = ((a : ℤ) : ℂ) := by
  choose c hc using hP
  choose d hd using hQ
  refine ⟨∑ p ∈ Finset.antidiagonal n, c p.1 * d p.2, ?_⟩
  calc (P * Q).coeff n
      = ∑ p ∈ Finset.antidiagonal n, P.coeff p.1 * Q.coeff p.2 :=
        PowerSeries.coeff_mul n P Q
    _ = ∑ p ∈ Finset.antidiagonal n, (((c p.1 * d p.2 : ℤ) : ℤ) : ℂ) := by
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [hc p.1, hd p.2]
        push_cast
        ring
    _ = ((∑ p ∈ Finset.antidiagonal n, c p.1 * d p.2 : ℤ) : ℂ) := by
        rw [Int.cast_sum]

/-- Powers of power series with integer-valued coefficients have
integer-valued coefficients. -/
lemma coeff_pow_intCast {P : PowerSeries ℂ} (hP : ∀ m, ∃ c : ℤ, P.coeff m = ((c : ℤ) : ℂ)) :
    ∀ (j n : ℕ), ∃ a : ℤ, (P ^ j).coeff n = ((a : ℤ) : ℂ) := by
  intro j
  induction j with
  | zero =>
      intro n
      refine ⟨if n = 0 then 1 else 0, ?_⟩
      rw [pow_zero, PowerSeries.coeff_one]
      split_ifs <;> simp
  | succ j ih =>
      intro n
      rw [pow_succ]
      exact coeff_mul_intCast ih hP n

/-- The q-expansion coefficients of `E₄` are the integers `240 σ₃(n)`. -/
theorem E4_coeff_eq (m : ℕ) :
    (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)).coeff m
      = ((if m = 0 then 1 else 240 * (sigma 3 m : ℤ) : ℤ) : ℂ) := by
  have hk4 : 3 ≤ (4 : ℕ) := by norm_num
  have hk4e : Even (4 : ℕ) := by norm_num
  have h := E_qExpansion_coeff (k := 4) hk4 hk4e m
  rw [h, RamanujanWeight12.bernoulli_four]
  split_ifs with hm <;> push_cast <;> norm_num

/-- The q-expansion coefficients of `E₆` are the integers `−504 σ₅(n)`. -/
theorem E6_coeff_eq (m : ℕ) :
    (qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6)).coeff m
      = ((if m = 0 then 1 else -504 * (sigma 5 m : ℤ) : ℤ) : ℂ) := by
  have hk6 : 3 ≤ (6 : ℕ) := by norm_num
  have hk6e : Even (6 : ℕ) := by norm_num
  have h := E_qExpansion_coeff (k := 6) hk6 hk6e m
  rw [h, RamanujanWeight12.bernoulli_six]
  split_ifs with hm <;> push_cast <;> norm_num

/-! ### The two coefficient identities -/

/-- **Jacobi's identity, coefficient form**: as power series,
`(qExpansion E₄)³ − (qExpansion E₆)² = 1728 • qExpansion Δ`. -/
theorem E4cube_sub_E6sq_qExpansion :
    (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)) ^ 3 - (qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6)) ^ 2
      = (1728 : ℂ) • qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) := by
  -- the q-expansion of the combination `E₄³ − E₆²` (weight 12)
  have hqJ : qExpansion 1 ((ModularForm.mcast (show (3 : ℤ) * 4 = 12 by decide) (E₄.pow 3)
      - ModularForm.mcast (show (2 : ℤ) * 6 = 12 by decide) (E₆.pow 2) : ModularForm 𝒮ℒ 12))
      = (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)) ^ 3
        - (qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6)) ^ 2 := by
    have hsub : qExpansion 1 ((ModularForm.mcast (show (3 : ℤ) * 4 = 12 by decide) (E₄.pow 3)
        - ModularForm.mcast (show (2 : ℤ) * 6 = 12 by decide) (E₆.pow 2) : ModularForm 𝒮ℒ 12))
        = qExpansion 1 (ModularForm.mcast (show (3 : ℤ) * 4 = 12 by decide) (E₄.pow 3))
          - qExpansion 1 (ModularForm.mcast (show (2 : ℤ) * 6 = 12 by decide) (E₆.pow 2)) := by
      have h := (ModularForm.qExpansionAddHom one_pos one_mem_strictPeriods_SL 12).map_sub
        (ModularForm.mcast (show (3 : ℤ) * 4 = 12 by decide) (E₄.pow 3))
        (ModularForm.mcast (show (2 : ℤ) * 6 = 12 by decide) (E₆.pow 2))
      simpa using h
    rw [hsub, ModularForm.qExpansion_mcast (by decide) rfl,
      ModularForm.qExpansion_mcast (by decide) rfl,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  -- pointwise, the combination equals 1728 • Δ
  have hpt : ∀ z : ℍ, ((ModularForm.mcast (show (3 : ℤ) * 4 = 12 by decide) (E₄.pow 3)
      - ModularForm.mcast (show (2 : ℤ) * 6 = 12 by decide) (E₆.pow 2) : ModularForm 𝒮ℒ 12) : ℍ → ℂ) z
      = (1728 : ℂ) * (ModularForm.discriminant : ℍ → ℂ) z := by
    intro z
    have hcoe4 : ((ModularForm.mcast (show (3 : ℤ) * 4 = 12 by decide) (E₄.pow 3) :
        ModularForm 𝒮ℒ 12) : ℍ → ℂ) = fun w ↦ E₄ w ^ 3 := by
      rw [coe_mcast, ModularForm.coe_pow]
      funext w
      rfl
    have hcoe6 : ((ModularForm.mcast (show (2 : ℤ) * 6 = 12 by decide) (E₆.pow 2) :
        ModularForm 𝒮ℒ 12) : ℍ → ℂ) = fun w ↦ E₆ w ^ 2 := by
      rw [coe_mcast, ModularForm.coe_pow]
      funext w
      rfl
    have hval : ((ModularForm.mcast (show (3 : ℤ) * 4 = 12 by decide) (E₄.pow 3)
        - ModularForm.mcast (show (2 : ℤ) * 6 = 12 by decide) (E₆.pow 2) : ModularForm 𝒮ℒ 12) : ℍ → ℂ) z
        = E₄ z ^ 3 - E₆ z ^ 2 := by
      rw [FunLike.coe_sub, Pi.sub_apply, hcoe4, hcoe6]
    rw [hval, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z]
    field_simp
  -- transport through the function `z ↦ 1728 • Δ z`
  have hfun : ((ModularForm.mcast (show (3 : ℤ) * 4 = 12 by decide) (E₄.pow 3)
      - ModularForm.mcast (show (2 : ℤ) * 6 = 12 by decide) (E₆.pow 2) : ModularForm 𝒮ℒ 12) : ℍ → ℂ)
      = fun z ↦ (1728 : ℂ) * (ModularForm.discriminant : ℍ → ℂ) z :=
    funext hpt
  have hcoe : (((1728 : ℂ) • (CuspForm.discriminant : CuspForm 𝒮ℒ 12) :
      CuspForm 𝒮ℒ 12) : ℍ → ℂ)
      = fun z ↦ (1728 : ℂ) * (ModularForm.discriminant : ℍ → ℂ) z := by
    funext z
    rw [FunLike.coe_smul, Pi.smul_apply]
    rfl
  have hsmul : qExpansion 1 (((1728 : ℂ) • (CuspForm.discriminant : CuspForm 𝒮ℒ 12) :
      CuspForm 𝒮ℒ 12) : ℍ → ℂ)
      = (1728 : ℂ) • qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) := by
    have h := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (1728 : ℂ)
      (CuspForm.discriminant : CuspForm 𝒮ℒ 12)
    exact h
  calc (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)) ^ 3
      - (qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6)) ^ 2
      = qExpansion 1 ((ModularForm.mcast (show (3 : ℤ) * 4 = 12 by decide) (E₄.pow 3)
          - ModularForm.mcast (show (2 : ℤ) * 6 = 12 by decide) (E₆.pow 2) : ModularForm 𝒮ℒ 12)) := hqJ.symm
    _ = qExpansion 1 (((1728 : ℂ) • (CuspForm.discriminant : CuspForm 𝒮ℒ 12) :
          CuspForm 𝒮ℒ 12) : ℍ → ℂ) :=
          congrArg (qExpansion (1 : ℝ)) (hfun.trans hcoe.symm)
    _ = (1728 : ℂ) • qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) := hsmul

/-- **Ramanujan's identity, coefficient form**: as power series,
`691 • qExpansion E₁₂ = 441 • (qExpansion E₄)³ + 250 • (qExpansion E₆)²`. -/
theorem E12_rel_qExpansion :
    (691 : ℂ) • qExpansion 1 RamanujanWeight12.E₁₂
      = (441 : ℂ) • (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)) ^ 3
        + (250 : ℂ) • (qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6)) ^ 2 := by
  have hcombo : RamanujanWeight12.combo = 0 := by
    unfold RamanujanWeight12.combo
    rw [RamanujanWeight12.E12_rel]
    module
  have hq0 : qExpansion 1 RamanujanWeight12.combo = 0 := by
    rw [hcombo]
    simpa using (ModularForm.qExpansionAddHom one_pos one_mem_strictPeriods_SL 12).map_zero
  rw [RamanujanWeight12.combo_qExpansion_eq] at hq0
  rw [pow_three, pow_two, ← mul_assoc (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4))
    (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)) (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)),
    ← sub_eq_zero]
  have hrrw : ∀ x y z : PowerSeries ℂ, x - (y + z) = x - y - z := fun _ _ _ ↦ by module
  rw [hrrw]
  exact hq0

/-! ### The congruence -/

/-- The integers `α, β` with `(E₄³)ₙ = α`, `(E₆²)ₙ = β`. -/
lemma exists_int_coeff (n : ℕ) :
    ∃ α β : ℤ, ((qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)) ^ 3).coeff n = ((α : ℤ) : ℂ)
      ∧ ((qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6)) ^ 2).coeff n = ((β : ℤ) : ℂ) := by
  exact ⟨(coeff_pow_intCast (fun m ↦ ⟨_, E4_coeff_eq m⟩) 3 n).choose,
    (coeff_pow_intCast (fun m ↦ ⟨_, E6_coeff_eq m⟩) 2 n).choose,
    (coeff_pow_intCast (fun m ↦ ⟨_, E4_coeff_eq m⟩) 3 n).choose_spec,
    (coeff_pow_intCast (fun m ↦ ⟨_, E6_coeff_eq m⟩) 2 n).choose_spec⟩

/-- **Ramanujan's congruence** (1916): `τ(n) ≡ σ₁₁(n) (mod 691)` for all `n ≥ 1`. -/
theorem tau_modEq_sigma (n : ℕ) (hn : 1 ≤ n) :
    Ramanujan.tau n ≡ ((sigma 11 n : ℤ)) [ZMOD 691] := by
  obtain ⟨α, β, hα, hβ⟩ := exists_int_coeff n
  -- coefficient n of Ramanujan's weight-12 identity
  have hc1 := congrArg (fun P : PowerSeries ℂ ↦ P.coeff n) E12_rel_qExpansion
  rw [coeff_add' n, PowerSeries.coeff_smul, smul_eq_mul] at hc1
  simp only [PowerSeries.coeff_smul, smul_eq_mul] at hc1
  rw [hα, hβ, RamanujanWeight12.E12_qExpansion_coeff (by omega)] at hc1
  have hID1 : ((441 * α + 250 * β : ℤ) : ℂ)
      = ((65520 * (sigma 11 n : ℤ) : ℤ) : ℂ) := by
    calc ((441 * α + 250 * β : ℤ) : ℂ)
        = (441 : ℂ) * α + (250 : ℂ) * β := by push_cast; ring
      _ = 691 * ((65520 / 691 : ℂ) * (sigma 11 n : ℂ)) := hc1.symm
      _ = ((65520 * (sigma 11 n : ℤ) : ℤ) : ℂ) := by
          push_cast
          field_simp
  have h1 : (441 : ℤ) * α + 250 * β = 65520 * (sigma 11 n : ℤ) := Int.cast_injective hID1
  -- coefficient n of Jacobi's identity, combined with the bridge
  have hc2 := congrArg (fun P : PowerSeries ℂ ↦ P.coeff n) E4cube_sub_E6sq_qExpansion
  rw [coeff_sub' n, PowerSeries.coeff_smul, smul_eq_mul] at hc2
  rw [hα, hβ, Ramanujan.qExpansion_discriminant_coeff_of_ne_zero (by omega)] at hc2
  have hID2 : ((α - β : ℤ) : ℂ) = ((1728 * Ramanujan.tau n : ℤ) : ℂ) := by
    exact_mod_cast hc2
  have h2 : α - β = 1728 * Ramanujan.tau n := Int.cast_injective hID2
  -- eliminate α and β:  691 * β = 65520 σ₁₁(n) − 762048 τ(n)
  have hα' : α = β + 1728 * Ramanujan.tau n := by omega
  have hkey : (691 : ℤ) * β
      = 65520 * (sigma 11 n : ℤ) - 762048 * Ramanujan.tau n := by
    have h441 : (441 : ℤ) * (β + 1728 * Ramanujan.tau n) + 250 * β
        = 691 * β + 762048 * Ramanujan.tau n := by ring
    rw [hα', h441] at h1
    linarith
  -- divisibility chain
  have hdvd : (691 : ℤ) ∣ 65520 * (sigma 11 n : ℤ) - 762048 * Ramanujan.tau n :=
    ⟨β, hkey.symm⟩
  have hsub : (691 : ℤ) ∣ 566 * ((sigma 11 n : ℤ) - Ramanujan.tau n) := by
    have hexp : 566 * ((sigma 11 n : ℤ) - Ramanujan.tau n)
        + 691 * (94 * (sigma 11 n : ℤ) - 1102 * Ramanujan.tau n)
        = 65520 * (sigma 11 n : ℤ) - 762048 * Ramanujan.tau n := by
      have hsplit : 566 * ((sigma 11 n : ℤ) - Ramanujan.tau n)
          + 691 * (94 * (sigma 11 n : ℤ) - 1102 * Ramanujan.tau n)
          = (566 + 691 * 94) * (sigma 11 n : ℤ)
            - (566 + 691 * 1102) * Ramanujan.tau n := by ring
      rw [hsplit]
      norm_num
    refine ⟨β - (94 * (sigma 11 n : ℤ) - 1102 * Ramanujan.tau n), ?_⟩
    calc 566 * ((sigma 11 n : ℤ) - Ramanujan.tau n)
        = (65520 * (sigma 11 n : ℤ) - 762048 * Ramanujan.tau n)
            - 691 * (94 * (sigma 11 n : ℤ) - 1102 * Ramanujan.tau n) := by
          rw [← hexp]
          ring
      _ = 691 * β - 691 * (94 * (sigma 11 n : ℤ) - 1102 * Ramanujan.tau n) := by rw [hkey]
      _ = 691 * (β - (94 * (sigma 11 n : ℤ) - 1102 * Ramanujan.tau n)) := by ring
  have hsub2 : (691 : ℤ) ∣ 125 * ((sigma 11 n : ℤ) - Ramanujan.tau n) := by
    have hrw2 : 125 * ((sigma 11 n : ℤ) - Ramanujan.tau n)
        = 691 * ((sigma 11 n : ℤ) - Ramanujan.tau n)
          - 566 * ((sigma 11 n : ℤ) - Ramanujan.tau n) := by
      have h566 : (566 : ℤ) = 691 - 125 := by norm_num
      rw [h566]
      ring
    rw [hrw2]
    exact dvd_sub (dvd_mul_right _ _) hsub
  have hprime : Prime (691 : ℤ) :=
    Nat.prime_iff_prime_int.mp (by
      set_option maxRecDepth 100000 in decide)
  have h125 : ¬((691 : ℤ) ∣ 125) := by decide
  rcases hprime.dvd_mul.mp hsub2 with h | h
  · exact absurd h h125
  · exact Int.modEq_iff_dvd.mpr h

/-! ### Sanity checks -/

/-- `τ(2) = −24` and `σ₁₁(2) = 2049 = 3 • 691 − 24`: the congruence holds. -/
example : Ramanujan.tau 2 ≡ ((sigma 11 2 : ℤ)) [ZMOD 691] :=
  tau_modEq_sigma 2 (by omega)

/-- Both sides of the congruence at `n = 2`, evaluated by the kernel:
`τ 2 = −24`, `σ₁₁ 2 = 2049`, and `2049 − (−24) = 2073 = 3 • 691`. -/
example : ((sigma 11 2 : ℤ)) - Ramanujan.tau 2 = 3 * 691 := by
  rw [Ramanujan.tau_two]
  decide

end RamanujanCongruence
