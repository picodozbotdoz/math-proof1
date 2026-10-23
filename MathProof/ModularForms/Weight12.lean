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
* `RamanujanWeight12.E12_qExpansion_coeff` : for `n ≥ 1` the coefficient of
  `q ^ n` in the q-expansion of `E₁₂` is `(65520 / 691) • σ₁₁(n)` (this is
  `−2k / B₁₂` with `B₁₂ = −691 / 2730`).

## Implementation notes

`bernoulli 12` is evaluated by chaining the defining recurrence
`bernoulli'_def` from the known values `B₀, …, B₄` (both `decide` and
`norm_num [bernoulli]` on the well-founded definition time out).

## Tags

Eisenstein series, Sturm bound, Ramanujan congruence, Bernoulli numbers
-/

open UpperHalfPlane ModularForm EisensteinSeries ArithmeticFunction

open scoped MatrixGroups

namespace RamanujanWeight12

/-! ### The twelfth Bernoulli number

Computed by unfolding the defining recurrence one step at a time; every step
is a fixed rational arithmetic problem for `norm_num`. -/

private theorem bernoulli'_five : bernoulli' 5 = 0 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four,
    show Nat.choose 5 2 = 10 from by decide]

private theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_five,
    show Nat.choose 6 2 = 15 from by decide,
    show Nat.choose 6 4 = 15 from by decide]

private theorem bernoulli'_seven : bernoulli' 7 = 0 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_five, bernoulli'_six,
    show Nat.choose 7 2 = 21 from by decide,
    show Nat.choose 7 4 = 35 from by decide]

private theorem bernoulli'_eight : bernoulli' 8 = -(1 / 30) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_five, bernoulli'_six,
    bernoulli'_seven,
    show Nat.choose 8 2 = 28 from by decide,
    show Nat.choose 8 4 = 70 from by decide,
    show Nat.choose 8 6 = 28 from by decide]

private theorem bernoulli'_nine : bernoulli' 9 = 0 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_five, bernoulli'_six,
    bernoulli'_seven, bernoulli'_eight,
    show Nat.choose 9 2 = 36 from by decide,
    show Nat.choose 9 4 = 126 from by decide,
    show Nat.choose 9 6 = 84 from by decide]

private theorem bernoulli'_ten : bernoulli' 10 = 5 / 66 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_five, bernoulli'_six,
    bernoulli'_seven, bernoulli'_eight, bernoulli'_nine,
    show Nat.choose 10 2 = 45 from by decide,
    show Nat.choose 10 4 = 210 from by decide,
    show Nat.choose 10 6 = 210 from by decide,
    show Nat.choose 10 8 = 45 from by decide]

private theorem bernoulli'_eleven : bernoulli' 11 = 0 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_five, bernoulli'_six,
    bernoulli'_seven, bernoulli'_eight, bernoulli'_nine, bernoulli'_ten,
    show Nat.choose 11 2 = 55 from by decide,
    show Nat.choose 11 4 = 330 from by decide,
    show Nat.choose 11 6 = 462 from by decide,
    show Nat.choose 11 8 = 165 from by decide]

private theorem bernoulli'_twelve : bernoulli' 12 = -(691 / 2730) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bernoulli'_five, bernoulli'_six,
    bernoulli'_seven, bernoulli'_eight, bernoulli'_nine, bernoulli'_ten, bernoulli'_eleven,
    show Nat.choose 12 2 = 66 from by decide,
    show Nat.choose 12 4 = 495 from by decide,
    show Nat.choose 12 6 = 924 from by decide,
    show Nat.choose 12 8 = 495 from by decide,
    show Nat.choose 12 10 = 66 from by decide]

/-- The Bernoulli number `B₁₂ = -691 / 2730`. -/
theorem bernoulli_twelve : bernoulli 12 = -(691 / 2730 : ℚ) := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_twelve]

/-- The Bernoulli number `B₄ = -1 / 30`. -/
theorem bernoulli_four : bernoulli 4 = -(1 / 30 : ℚ) := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]
  ring

/-- The proof term `3 ≤ 12`, named so that rewrite patterns match syntactically. -/
theorem hk12 : 3 ≤ 12 := by norm_num

/-- The proof term `Even 12`, named so that rewrite patterns match syntactically. -/
theorem hk12even : Even 12 := by norm_num

/-- The Eisenstein series of weight 12. -/
noncomputable def E₁₂ : ModularForm 𝒮ℒ 12 := E hk12

/-- The coefficient of `q ^ n` in the q-expansion of `E₁₂` is
`(65520 / 691) • σ₁₁(n)` for `n ≥ 1` (and the constant term is `1`). -/
theorem E12_qExpansion_coeff {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 E₁₂).coeff n = (65520 / 691 : ℂ) * (sigma 11 n : ℂ) := by
  have h := E_qExpansion_coeff hk12 hk12even n
  change (qExpansion 1 (E hk12)).coeff n = _
  rw [h, bernoulli_twelve]
  split_ifs with hn0
  · exact absurd hn0 hn
  · push_cast
    norm_num

/-- The coefficient of `q` in the q-expansion of `E₁₂` is `65520 / 691`. -/
theorem E12_qExpansion_coeff_one :
    (qExpansion 1 E₁₂).coeff 1 = (65520 / 691 : ℂ) := by
  rw [E12_qExpansion_coeff one_ne_zero]
  simp

theorem E₄_coeff_zero : (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)).coeff 0 = 1 :=
  E_qExpansion_coeff_zero (by norm_num) (by norm_num)

theorem E₆_coeff_zero : (qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6)).coeff 0 = 1 :=
  E_qExpansion_coeff_zero (by norm_num) (by norm_num)

theorem E12_coeff_zero : (qExpansion 1 E₁₂).coeff 0 = 1 :=
  E_qExpansion_coeff_zero hk12 hk12even

/-! ### Ramanujan's identity via the Sturm bound -/

/-- The combination `691 • E₁₂ − 441 • E₄³ − 250 • E₆²` as a modular form of
weight 12 (with `E₄³`, `E₆²` weight-cast from weights `4 * 3`, `6 * 2`). -/
noncomputable def combo : ModularForm 𝒮ℒ 12 :=
  (691 : ℂ) • E₁₂ - (441 : ℂ) • ModularForm.mcast (by decide) (E₄.pow 3)
    - (250 : ℂ) • ModularForm.mcast (by decide) (E₆.pow 2)

lemma qExpansion_sub' (f g : ModularForm 𝒮ℒ 12) :
    qExpansion 1 ((f - g : ModularForm 𝒮ℒ 12)) = qExpansion 1 f - qExpansion 1 g := by
  have h := (ModularForm.qExpansionAddHom one_pos one_mem_strictPeriods_SL 12).map_sub f g
  simpa using h

lemma qExpansion_smul' (c : ℂ) (f : ModularForm 𝒮ℒ 12) :
    qExpansion 1 ((c • f : ModularForm 𝒮ℒ 12)) = c • qExpansion 1 f :=
  ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c f

lemma combo_qExpansion_eq :
    qExpansion 1 combo = (691 : ℂ) • qExpansion 1 E₁₂
      - (441 : ℂ) • ((qExpansion 1 E₄) * (qExpansion 1 E₄) * (qExpansion 1 E₄))
      - (250 : ℂ) • ((qExpansion 1 E₆) * (qExpansion 1 E₆)) := by
  unfold combo
  rw [qExpansion_sub', qExpansion_sub', qExpansion_smul', qExpansion_smul', qExpansion_smul',
    ModularForm.qExpansion_mcast (by decide) rfl,
    ModularForm.qExpansion_mcast (by decide) rfl,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  simp only [pow_two, pow_three, mul_assoc]

/-- The constant coefficient of the q-expansion of `combo` vanishes:
`691 = 441 + 250`. -/
theorem combo_coeff_zero : (qExpansion 1 combo).coeff 0 = 0 := by
  rw [combo_qExpansion_eq]
  norm_num [PowerSeries.coeff_smul, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ,
    E₄_coeff_zero, E₆_coeff_zero, E12_coeff_zero,
    -PowerSeries.coeff_zero_eq_constantCoeff]

/-- The coefficient of `q` in the q-expansion of `combo` vanishes:
`691 • (65520 / 691) = 441 • 720 + 250 • (-504) = 65520`. -/
theorem combo_coeff_one : (qExpansion 1 combo).coeff 1 = 0 := by
  rw [combo_qExpansion_eq]
  norm_num [PowerSeries.coeff_smul, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ,
    E₄_coeff_zero, E₆_coeff_zero, E₄_qExpansion_coeff_one, E₆_qExpansion_coeff_one,
    E12_qExpansion_coeff_one, E12_coeff_zero,
    -PowerSeries.coeff_zero_eq_constantCoeff]

set_option maxHeartbeats 800000 in
-- reason: the statement involves weight-cast coercions with heavy defeq checks
/-- **Ramanujan's weight-12 identity**: `691 • E₁₂ = 441 • E₄³ + 250 • E₆²` in
`M₁₂(SL(2, ℤ))`, proved via the Sturm bound: the difference `combo` has
q-expansion coefficients `0` and `1` equal to zero, and the Sturm bound at
weight 12 is `12 / 12 = 1`. -/
theorem E12_rel : (691 : ℂ) • E₁₂
    = (441 : ℂ) • ModularForm.mcast (by decide) (E₄.pow 3)
      + (250 : ℂ) • ModularForm.mcast (by decide) (E₆.pow 2) := by
  have h2 : (2 : ℕ∞) ≤ (qExpansion 1 combo).order :=
    PowerSeries.nat_le_order _ 2 (by
      intro i hi
      match i with
      | 0 => exact combo_coeff_zero
      | 1 => exact combo_coeff_one)
  have hsturm : (1 : ℕ∞) < (qExpansion 1 combo).order :=
    lt_of_lt_of_le (by norm_num) h2
  have h0 := ModularForm.sturm_bound_levelOne_nat (k := 12) hsturm
  apply eq_of_sub_eq_zero
  simpa only [combo, sub_sub] using h0

end RamanujanWeight12
