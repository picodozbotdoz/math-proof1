import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Ramanujan's weight-12 identity `691 • E₁₂ = 441 • E₄³ + 250 • E₆²`

The space `M₁₂(SL(2, ℤ))` of level-one modular forms of weight 12 is spanned by
`E₄ ^ 3` and `E₆ ^ 2`.  Comparing the first two q-expansion coefficients of the
Eisenstein series `E₁₂` with those of `E₄ ^ 3` and `E₆ ^ 2` (a Sturm-bound
argument) gives Ramanujan's identity

    691 • E₁₂ = 441 • E₄³ + 250 • E₆²,

whose coefficientwise form is the classical source of Ramanujan's congruence
`τ(n) ≡ σ₁₁(n) (mod 691)`.

## Main statements

* `RamanujanWeight12.E12_rel` : `691 • E₁₂ = 441 • E₄³ + 250 • E₆²` in
  `M₁₂(SL(2, ℤ))`.
* `RamanujanWeight12.E12_qExpansion_coeff_one` : the coefficient of `q` in the
  q-expansion of `E₁₂` is `65520 / 691` (this is `−2k / B₁₂` with
  `B₁₂ = −691 / 2730` and `σ₁₁(1) = 1`).

## Tags

Eisenstein series, Sturm bound, Ramanujan congruence, Bernoulli numbers
-/

open ModularForm EisensteinSeries ArithmeticFunction

namespace RamanujanWeight12

/-- The proof term `3 ≤ 12`, named so that rewrite patterns match syntactically. -/
def hk12 : 3 ≤ 12 := by norm_num

/-- The proof term `Even 12`, named so that rewrite patterns match syntactically. -/
def hk12even : Even 12 := by norm_num

/-- The Bernoulli number `B₁₂ = -691 / 2730` (by computation). -/
theorem bernoulli_twelve : bernoulli 12 = -(691 / 2730 : ℚ) := by decide

/-- The Eisenstein series of weight 12. -/
def E₁₂ : ModularForm 𝒮ℒ 12 := E hk12

/-- The coefficient of `q` in the q-expansion of `E₁₂` is `65520 / 691`. -/
theorem E12_qExpansion_coeff_one :
    (qExpansion 1 E₁₂).coeff 1 = (65520 / 691 : ℂ) := by
  have hσ : (sigma 11 1 : ℂ) = 1 := by simp
  have h := E_qExpansion_coeff hk12 hk12even 1
  change (qExpansion 1 (E hk12)).coeff 1 = _
  rw [h, if_neg one_ne_zero, hσ, mul_one, bernoulli_twelve]
  norm_num

theorem E₄_coeff_zero : (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)).coeff 0 = 1 :=
  E_qExpansion_coeff_zero (by norm_num) (by norm_num)

theorem E₆_coeff_zero : (qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6)).coeff 0 = 1 :=
  E_qExpansion_coeff_zero (by norm_num) (by norm_num)

theorem E12_coeff_zero : (qExpansion 1 E₁₂).coeff 0 = 1 :=
  E_qExpansion_coeff_zero hk12 hk12even

/-- Coefficient `0` of a product of power series. -/
theorem coeff_mul_zero (A B : PowerSeries ℂ) :
    (A * B).coeff 0 = A.coeff 0 * B.coeff 0 := by
  simp [PowerSeries.coeff_mul]

/-- Coefficient `1` of a product of power series. -/
theorem coeff_mul_one (A B : PowerSeries ℂ) :
    (A * B).coeff 1 = A.coeff 0 * B.coeff 1 + A.coeff 1 * B.coeff 0 := by
  rw [PowerSeries.coeff_mul]
  have hA : Nat.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
  rw [hA, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_empty]
  ring

/-! ### Ramanujan's identity via the Sturm bound -/

/-- The coefficients `0` and `1` of the q-expansion of
`691 • E₁₂ − 441 • E₄³ − 250 • E₆²` vanish. -/
theorem combo_coeffs (m : ℕ) (hm : m ≤ 1) :
    (qExpansion 1 ((691 : ℂ) • E₁₂ - (441 : ℂ) • (E₄.mul E₄).mul E₄
      - (250 : ℂ) • E₆.mul E₆)).coeff m = 0 := by
  have hmul44 : qExpansion 1 ((E₄.mul E₄).mul (E₄ : ModularForm 𝒮ℒ 4))
      = (qExpansion 1 E₄) * (qExpansion 1 E₄) * (qExpansion 1 E₄) := by
    rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL]
  have hmul66 : qExpansion 1 ((E₆.mul E₆ : ModularForm 𝒮ℒ 12))
      = (qExpansion 1 E₆) * (qExpansion 1 E₆) := by
    rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL]
  match m with
  | 0 =>
      simp only [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
        hmul44, hmul66, PowerSeries.coeff_smul, smul_eq_mul,
        PowerSeries.coeff_sub, coeff_mul_zero, E₄_coeff_zero, E₆_coeff_zero,
        E12_coeff_zero]
      norm_num
  | 1 =>
      simp only [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
        hmul44, hmul66, PowerSeries.coeff_smul, smul_eq_mul,
        PowerSeries.coeff_sub, coeff_mul_one, E₄_coeff_zero, E₆_coeff_zero,
        E₄_qExpansion_coeff_one, E₆_qExpansion_coeff_one,
        E12_qExpansion_coeff_one, E12_coeff_zero]
      norm_num

/-- **Ramanujan's weight-12 identity**: `691 • E₁₂ = 441 • E₄³ + 250 • E₆²` in
`M₁₂(SL(2, ℤ))`, proved via the Sturm bound: the difference has q-expansion
coefficients `0` and `1` equal to zero, and the Sturm bound at weight 12 is 1. -/
theorem E12_rel : (691 : ℂ) • E₁₂
    = (441 : ℂ) • (E₄.mul E₄).mul E₄ + (250 : ℂ) • E₆.mul E₆ := by
  have hsturm : (1 : ℕ∞) < (qExpansion 1 ((691 : ℂ) • E₁₂
      - (441 : ℂ) • (E₄.mul E₄).mul E₄ - (250 : ℂ) • E₆.mul E₆)).order := by
    have h2 : (2 : ℕ∞) ≤ (qExpansion 1 ((691 : ℂ) • E₁₂
        - (441 : ℂ) • (E₄.mul E₄).mul E₄ - (250 : ℂ) • E₆.mul E₆)).order :=
      PowerSeries.nat_le_order _ 2 (fun i hi ↦ combo_coeffs i (by omega))
    exact lt_of_lt_of_le (by norm_num) h2
  have h0 := ModularForm.sturm_bound_levelOne_nat (k := 12) hsturm
  rw [sub_sub] at h0
  exact eq_of_sub_eq_zero h0

end RamanujanWeight12
