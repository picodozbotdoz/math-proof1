import MathProof.ModularForms.EigenLevelOne
import MathProof.ModularForms.Congruence691
import MathProof.ModularForms.BernoulliHigh

/-!
# Lehmer's question in weight 22: the eigenform `Δ E₄E₆`

`S₁₆…₂₆(SL(2, ℤ))` are one-dimensional; in weight 22 the space is spanned by
the normalized Hecke eigenform `f₍22₎ = Δ E₄E₆ = q -288 q² -128844 q³ + ⋯`.
Same toolkit as `MathProof/ModularForms/LehmerWeight16.lean`; here the
Eisenstein factor `E₄E₆` is a product, and the congruence modulus
`77683 = 131 · 593` (from the numerator of `B_22`) is composite, so the
congruence is derived by `ℤ`-divisibility with a coprime cancellation and the
sieve runs prime by prime.

* `f22_isNormalizedRankOne` — `a22 n = Σ_{i + j = n} τ i · g j` with
  `g` the coefficients of `E₄E₆`; Hecke eigenform, multiplicative, recursion
  with `p ^ 21`;
* `a22_ne_zero_iff_primes` — Lehmer's reduction in weight 22;
* `a22_modEq_sigma` — `a_22 n ≡ σ_21 n [ZMOD 77683]`, from
  `E_22 − E₄⁴E₆ ∈ S_22`;
* `a22_prime_ne_zero_of_mod` — `a_22 p ≠ 0` for every prime
  `p ≢ −1 [MOD 77683]`;
* **`a22_ne_zero_of_lt_1087561`** — `a_22 n ≠ 0` for every `0 < n < 1087561`
  (`1087561` is the least prime `≡ −1 [MOD 77683]`).
-/

open UpperHalfPlane ModularForm CuspForm EisensteinSeries ArithmeticFunction
open scoped MatrixGroups

namespace LehmerWeight22

/-- The q-expansion of `E₄`. -/
local notation "q₄" => qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)

/-- The q-expansion of `E₆`. -/
local notation "q₆" => qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6)

/-! ### The form and its integer coefficients -/

/-- The integer q-coefficients of `E₄`. -/
def e4 (m : ℕ) : ℤ := if m = 0 then 1 else 240 * (sigma 3 m : ℤ)

/-- The integer q-coefficients of `E₆`. -/
def e6 (m : ℕ) : ℤ := if m = 0 then 1 else -504 * (sigma 5 m : ℤ)

/-- The integer q-coefficients of `E₄E₆` (the convolution `e₄ ⋆ e₆`). -/
def g22 (m : ℕ) : ℤ := ∑ x ∈ Finset.antidiagonal m, e4 x.1 * e6 x.2

/-- The integer q-coefficients of `Δ` (`τ n` for `n ≥ 1`, `0` at `n = 0`). -/
noncomputable def dlt (m : ℕ) : ℤ := if m = 0 then 0 else Ramanujan.tau m

/-- The coefficients of `Δ E₄E₆`: `a22 n = Σ_{i + j = n} τ i · g22 j`. -/
noncomputable def a22 (n : ℕ) : ℤ := ∑ x ∈ Finset.antidiagonal n, dlt x.1 * g22 x.2

/-- The weight-22 cusp form `Δ E₄E₆`. -/
noncomputable def f22 : CuspForm 𝒮ℒ ((22 : ℕ) : ℤ) :=
  ofMulDiscriminant (ModularForm.mcast (by norm_num) (E₄.mul E₆))

lemma delta_coeff (m : ℕ) :
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff m = ((dlt m : ℤ) : ℂ) := by
  unfold dlt
  split_ifs with hm
  · subst hm; rw [Ramanujan.qExpansion_discriminant_coeff_zero]; simp
  · exact Ramanujan.qExpansion_discriminant_coeff_of_ne_zero hm

lemma e4_coeff (m : ℕ) :
    (q₄).coeff m = ((e4 m : ℤ) : ℂ) :=
  RamanujanCongruence.E4_coeff_eq m

lemma e6_coeff (m : ℕ) :
    (q₆).coeff m = ((e6 m : ℤ) : ℂ) :=
  RamanujanCongruence.E6_coeff_eq m

lemma qExpansion_G :
    qExpansion 1 (E₄.mul E₆) = q₄ * q₆ :=
  ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL _ _

lemma g22_coeff (m : ℕ) : (q₄ * q₆).coeff m = ((g22 m : ℤ) : ℂ) := by
  rw [PowerSeries.coeff_mul, g22, Int.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [e4_coeff, e6_coeff, Int.cast_mul]

lemma qExpansion_f22 :
    qExpansion 1 f22 = qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) * (q₄ * q₆) := by
  rw [← qExpansion_G]
  exact ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) (E₄.mul E₆)

theorem f22_coeff (n : ℕ) : (qExpansion 1 f22).coeff n = ((a22 n : ℤ) : ℂ) := by
  rw [qExpansion_f22, PowerSeries.coeff_mul, a22, Int.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [delta_coeff, g22_coeff, Int.cast_mul]

theorem rank_cuspForm_22 : Module.rank ℂ (CuspForm 𝒮ℒ ((22 : ℕ) : ℤ)) = 1 := by
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 10 (by decide)
  norm_num [Nat.ModEq] at h
  exact h

/-! ### Small coefficients -/

lemma sigma3_two : sigma 3 2 = 9 := by decide
lemma sigma5_two : sigma 5 2 = 33 := by decide

theorem a22_one : a22 1 = 1 := by
  simp [a22, g22, Finset.Nat.antidiagonal_succ, dlt, e4, e6, Ramanujan.tau_one]

theorem a22_two : a22 2 = -288 := by
  simp [a22, g22, Finset.Nat.antidiagonal_succ, dlt, e4, e6, Ramanujan.tau_one,
    Ramanujan.tau_two]

theorem a22_three : a22 3 = -128844 := by
  simp [a22, g22, Finset.Nat.antidiagonal_succ, dlt, e4, e6, Ramanujan.tau_one,
    Ramanujan.tau_two, Ramanujan.tau_three, sigma3_two, sigma5_two]

theorem f22_isNormalizedRankOne : EigenLevelOne.IsNormalizedRankOne 22 f22 a22 where
  rank_one := rank_cuspForm_22
  coeff n _ := f22_coeff n
  one := a22_one
  weight_pos := by norm_num

/-! ### Mordell and Lehmer in weight 22 -/

/-- `Δ E₄E₆` is a Hecke eigenform: `T_p f = a22 p • f`. -/
theorem heckeTP_f22 {p : ℕ} (hp : p.Prime) :
    HeckeLevelOne.heckeTP hp f22 = ((a22 p : ℤ) : ℂ) • f22 :=
  f22_isNormalizedRankOne.heckeTP_eq hp

/-- Mordell multiplicativity in weight 22. -/
theorem a22_mul_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 0 < m) :
    a22 (m * n) = a22 m * a22 n :=
  f22_isNormalizedRankOne.mul_coprime hmn hm

lemma two_pow_not_dvd : ¬ (2 : ℤ) ^ (10 + 1) ∣ a22 2 := by rw [a22_two]; decide
lemma three_pow_not_dvd : ¬ (3 : ℤ) ^ (10 + 1) ∣ a22 3 := by rw [a22_three]; decide

/-- **Lehmer's reduction in weight 22**. -/
theorem a22_ne_zero_iff_primes :
    (∀ n : ℕ, 1 ≤ n → a22 n ≠ 0) ↔ ∀ p : ℕ, p.Prime → a22 p ≠ 0 :=
  f22_isNormalizedRankOne.ne_zero_iff_primes (j := 10) rfl two_pow_not_dvd three_pow_not_dvd

/-! ### The congruence mod 77683 -/

/-- The Eisenstein series of weight 22. -/
noncomputable def E22 : ModularForm 𝒮ℒ ((22 : ℕ) : ℤ) := E (by norm_num : 3 ≤ 22)

/-- `E₄⁴E₆` as a form of weight 22. -/
noncomputable def H22 : ModularForm 𝒮ℒ ((22 : ℕ) : ℤ) :=
  ModularForm.mcast (by norm_num) ((E₄.pow 4).mul E₆)

lemma qExpansion_H22 : qExpansion 1 H22 = (q₄) ^ 4 * q₆ := by
  rw [H22, ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos
    one_mem_strictPeriods_SL, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

lemma E22_coeff {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 E22).coeff n = (-552 / 77683 : ℂ) * (sigma 21 n : ℂ) := by
  have h := E_qExpansion_coeff (k := 22) (by norm_num) (by decide) n
  change (qExpansion 1 (E (by norm_num : 3 ≤ 22))).coeff n = _
  rw [h, RamanujanWeight12.bernoulli_twentyTwo, ite_eq_right_iff.mpr (fun h => absurd h hn)]
  push_cast
  norm_num

lemma qExpansion_sub22 (f g : ModularForm 𝒮ℒ ((22 : ℕ) : ℤ)) :
    qExpansion 1 ((f - g : ModularForm 𝒮ℒ ((22 : ℕ) : ℤ)))
      = qExpansion 1 f - qExpansion 1 g := by
  have h := (ModularForm.qExpansionAddHom one_pos one_mem_strictPeriods_SL
    ((22 : ℕ) : ℤ)).map_sub f g
  simpa using h

lemma E4_coeff_zero' : (q₄).coeff 0 = 1 := by
  rw [e4_coeff]; simp [e4]

lemma E4_coeff_one' : (q₄).coeff 1 = 240 := by
  rw [e4_coeff]; simp [e4]

lemma E6_coeff_zero' : (q₆).coeff 0 = 1 := by
  rw [e6_coeff]; simp [e6]

lemma E6_coeff_one' : (q₆).coeff 1 = -504 := by
  rw [e6_coeff]; simp [e6]

lemma H22_coeff_zero : (qExpansion 1 H22).coeff 0 = 1 := by
  rw [qExpansion_H22]
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, E4_coeff_zero', E6_coeff_zero', one_pow,
    one_mul]

lemma H22_coeff_one : (qExpansion 1 H22).coeff 1 = 456 := by
  rw [qExpansion_H22]
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E4_coeff_zero',
    E4_coeff_one', E6_coeff_zero', E6_coeff_one']
  norm_num

/-- `E_22 − E₄⁴E₆`, a cusp form of weight 22. -/
noncomputable def D22 : CuspForm 𝒮ℒ ((22 : ℕ) : ℤ) :=
  ModularForm.toCuspForm (E22 - H22) (by
    rw [qExpansion_sub22, map_sub, H22_coeff_zero,
      show E22 = E (by norm_num : 3 ≤ 22) from rfl, E_qExpansion_coeff_zero (by norm_num)
        (by decide)]
    simp)

lemma qExpansion_D22 : qExpansion 1 D22 = qExpansion 1 E22 - qExpansion 1 H22 :=
  qExpansion_sub22 E22 H22

/-- **The weight-22 Ramanujan congruence**: `a_22 n ≡ σ_21 n [ZMOD 77683]`. -/
theorem a22_modEq_sigma {n : ℕ} (hn : 1 ≤ n) :
    a22 n ≡ (sigma 21 n : ℤ) [ZMOD 77683] := by
  have hsm := f22_isNormalizedRankOne.eq_smul D22
  have hc : (qExpansion 1 D22).coeff 1 = (-552 / 77683 : ℂ) - 456 := by
    rw [qExpansion_D22, map_sub, E22_coeff one_ne_zero, H22_coeff_one,
      show sigma 21 1 = 1 by decide]
    norm_num
  rw [hc] at hsm
  have hcoef :=
    congrArg (fun g : CuspForm 𝒮ℒ ((22 : ℕ) : ℤ) => (qExpansion 1 g).coeff n) hsm
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, smul_eq_mul, f22_coeff, qExpansion_D22, map_sub,
    E22_coeff (by omega)] at hcoef
  obtain ⟨h, hh⟩ := RamanujanCongruence.coeff_mul_intCast
    (RamanujanCongruence.coeff_pow_intCast (fun m => ⟨e4 m, e4_coeff m⟩) 4)
    (fun m => ⟨e6 m, e6_coeff m⟩) n
  rw [qExpansion_H22, hh] at hcoef
  -- clear denominators: `-552 (σ − a) = 77683 (h − 456 a)`
  have hZ : (-552 : ℤ) * ((sigma 21 n : ℤ) - a22 n) = 77683 * (h - 456 * a22 n) := by
    have h' : (((-552 : ℤ) * ((sigma 21 n : ℤ) - a22 n) : ℤ) : ℂ)
        = ((77683 * (h - 456 * a22 n) : ℤ) : ℂ) := by
      push_cast
      linear_combination (77683 : ℂ) * hcoef
    exact_mod_cast h'
  have hdvd : (77683 : ℤ) ∣ (-552 : ℤ) * ((sigma 21 n : ℤ) - a22 n) := ⟨_, hZ⟩
  have hcop : Int.gcd 77683 (-552) = 1 := by norm_num
  exact (Int.modEq_iff_dvd.mpr (Int.dvd_of_dvd_mul_right_of_gcd_one hdvd hcop))

/-! ### The sieve and the initial segment -/

/-- `x ^ 21 = −1` forces `x = −1` in `ZMod 131` (`21 · 31 = 5 · 130 + 1`, `31` odd). -/
lemma eq_neg_one_mod131 {x : ZMod 131} (hx : x ^ 21 = -1) : x = -1 := by
  have : Fact (Nat.Prime 131) := ⟨by norm_num⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hx
    exact neg_ne_zero.mpr one_ne_zero hx.symm
  have h1 : x ^ 130 = 1 := ZMod.pow_card_sub_one_eq_one hx0
  calc x = (x ^ 130) ^ 5 * x := by rw [h1, one_pow, one_mul]
    _ = (x ^ 21) ^ 31 := by rw [← pow_mul, ← pow_mul, ← pow_succ]
    _ = -1 := by rw [hx]; norm_num

/-- `x ^ 21 = −1` forces `x = −1` in `ZMod 593` (`21 · 141 = 5 · 592 + 1`, `141` odd). -/
lemma eq_neg_one_mod593 {x : ZMod 593} (hx : x ^ 21 = -1) : x = -1 := by
  have : Fact (Nat.Prime 593) := ⟨by norm_num⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hx
    exact neg_ne_zero.mpr one_ne_zero hx.symm
  have h1 : x ^ 592 = 1 := ZMod.pow_card_sub_one_eq_one hx0
  calc x = (x ^ 592) ^ 5 * x := by rw [h1, one_pow, one_mul]
    _ = (x ^ 21) ^ 141 := by rw [← pow_mul, ← pow_mul, ← pow_succ]
    _ = -1 := by rw [hx]; norm_num

/-- From `1 + p ^ 21 ≡ 0 [ZMOD ℓ]` to `ℓ ∣ p + 1`, for one prime factor `ℓ`. -/
lemma dvd_succ_of_pow {ℓ p : ℕ} (h : ∀ x : ZMod ℓ, x ^ 21 = -1 → x = -1)
    (hz : (((1 + p ^ 21 : ℕ) : ℤ) : ZMod ℓ) = 0) : ℓ ∣ p + 1 := by
  push_cast at hz
  have hneg := h (p : ZMod ℓ) (by linear_combination hz)
  have hd : ((p + 1 : ℕ) : ZMod ℓ) = 0 := by push_cast; rw [hneg]; ring
  rwa [ZMod.natCast_eq_zero_iff] at hd

/-- **The weight-22 sieve**: `a_22 p ≠ 0` for every prime `p ≢ −1 [MOD 77683]`. -/
theorem a22_prime_ne_zero_of_mod {p : ℕ} (hp : p.Prime) (h : p % 77683 ≠ 77682) :
    a22 p ≠ 0 := by
  intro h0
  have hc := a22_modEq_sigma hp.one_lt.le
  rw [h0] at hc
  have hsig : sigma 21 p = 1 + p ^ 21 := by
    rw [show sigma 21 p = sigma 21 (p ^ 1) from by rw [pow_one],
      sigma_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_one]
    simp
  rw [hsig] at hc
  -- `77683 ∣ 1 + p ^ 21`, hence each prime factor divides `p + 1`
  have hL : (77683 : ℤ) ∣ ((1 + p ^ 21 : ℕ) : ℤ) := by
    have := (Int.modEq_iff_dvd.mp hc); simpa using this
  have h1 : (131 : ℤ) ∣ ((1 + p ^ 21 : ℕ) : ℤ) :=
    (show (131 : ℤ) ∣ 77683 by norm_num).trans hL
  have h2 : (593 : ℤ) ∣ ((1 + p ^ 21 : ℕ) : ℤ) :=
    (show (593 : ℤ) ∣ 77683 by norm_num).trans hL
  have d1 := dvd_succ_of_pow (ℓ := 131) (fun x hx => eq_neg_one_mod131 hx)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast h1))
  have d2 := dvd_succ_of_pow (ℓ := 593) (fun x hx => eq_neg_one_mod593 hx)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast h2))
  have d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 131 593) d1 d2
  omega

/-- No prime below 1087561 is `≡ −1 [MOD 77683]`: the 13 candidates
`77683 k + 77682` (`k ≤ 12`) are composite. -/
theorem no_bad_prime_lt_1087561 :
    ∀ p : ℕ, p.Prime → p < 1087561 → p % 77683 ≠ 77682 := by
  intro p hp hlt hmod
  obtain ⟨k, rfl⟩ : ∃ k, p = 77683 * k + 77682 := ⟨p / 77683, by omega⟩
  have hk : k ≤ 12 := by omega
  interval_cases k <;> norm_num at hp

/-- **Lehmer's question in weight 22, all `n < 1087561`**: the coefficients of
`Δ E₄E₆` satisfy `a_22 n ≠ 0` for every `0 < n < 1087561`. -/
theorem a22_ne_zero_of_lt_1087561 {n : ℕ} (hn : 0 < n) (hlt : n < 1087561) : a22 n ≠ 0 :=
  f22_isNormalizedRankOne.ne_zero_of_prime_factors (j := 10) rfl two_pow_not_dvd
    three_pow_not_dvd hn fun p hp hd =>
      a22_prime_ne_zero_of_mod hp
        (no_bad_prime_lt_1087561 p hp (lt_of_le_of_lt (Nat.le_of_dvd hn hd) hlt))

/-- **Unbounded weight-22 nonvanishing**: `a_22 n ≠ 0` for every `n ≥ 1` none
of whose prime factors is `≡ −1 [MOD 77683]` (any exponents). -/
theorem a22_ne_zero_of_prime_factors_mod {n : ℕ} (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p % 77683 ≠ 77682) : a22 n ≠ 0 :=
  f22_isNormalizedRankOne.ne_zero_of_prime_factors (j := 10) rfl two_pow_not_dvd
    three_pow_not_dvd hn fun p hp hd => a22_prime_ne_zero_of_mod hp (h p hp hd)

end LehmerWeight22
