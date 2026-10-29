import MathProof.ModularForms.EigenLevelOne
import MathProof.ModularForms.Congruence691
import MathProof.ModularForms.BernoulliHigh

/-!
# Lehmer's question in weight 16: the eigenform `Δ E₄`

`S₁₆(SL(2, ℤ))` is one-dimensional, spanned by the normalized Hecke eigenform
`f₁₆ = Δ E₄ = q + 216 q² − 3348 q³ + 13888 q⁴ + ⋯`.  The analogue of Lehmer's
conjecture — its coefficients `a₁₆ n` never vanish — is open, exactly as for
`τ`.  This file transports the whole Lehmer toolkit of Iterations 7–12 to
weight 16:

* `f16_isNormalizedRankOne` — `f₁₆` is a normalized generator with integer
  coefficients `a16 n = Σ_{i + j = n} τ i · e₄ j`; hence (generic
  `EigenLevelOne`) a Hecke eigenform, multiplicative, with the prime-power
  recursion `a (p^(r+2)) = a p · a (p^(r+1)) − p^15 · a (p^r)`;
* `a16_ne_zero_iff_primes` — Lehmer's reduction: nonvanishing for all `n`
  iff for all primes;
* `a16_modEq_sigma` — the weight-16 Ramanujan congruence
  `a₁₆ n ≡ σ₁₅ n [ZMOD 3617]` (`3617` = numerator of `B₁₆`), from
  `E₁₆ − E₄⁴ ∈ S₁₆`;
* `a16_prime_ne_zero_of_mod` — the sieve: `a₁₆ p ≠ 0` for every prime
  `p ≢ −1 [MOD 3617]`, of arbitrary size;
* **`a16_ne_zero_of_lt_21701`** — `a₁₆ n ≠ 0` for every `0 < n < 21701`
  (`21701` is the least prime `≡ −1 [MOD 3617]`), with no dense coefficient
  computation at all: congruence + Lehmer reduction alone.
-/

open UpperHalfPlane ModularForm CuspForm EisensteinSeries ArithmeticFunction
open scoped MatrixGroups

namespace LehmerWeight16

/-! ### The form and its integer coefficients -/

/-- The integer q-coefficients of `E₄`: `1, 240 σ₃ 1, 240 σ₃ 2, …`. -/
def e4 (m : ℕ) : ℤ := if m = 0 then 1 else 240 * (sigma 3 m : ℤ)

/-- The integer q-coefficients of `Δ` (`τ n` for `n ≥ 1`, `0` at `n = 0`). -/
noncomputable def dlt (m : ℕ) : ℤ := if m = 0 then 0 else Ramanujan.tau m

/-- The coefficients of `Δ E₄`: `a16 n = Σ_{i + j = n} τ i · e₄ j`. -/
noncomputable def a16 (n : ℕ) : ℤ := ∑ x ∈ Finset.antidiagonal n, dlt x.1 * e4 x.2

/-- The weight-16 cusp form `Δ E₄`. -/
noncomputable def f16 : CuspForm 𝒮ℒ ((16 : ℕ) : ℤ) :=
  ofMulDiscriminant (ModularForm.mcast (by norm_num) E₄)

lemma delta_coeff (m : ℕ) :
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff m = ((dlt m : ℤ) : ℂ) := by
  unfold dlt
  split_ifs with hm
  · subst hm; rw [Ramanujan.qExpansion_discriminant_coeff_zero]; simp
  · exact Ramanujan.qExpansion_discriminant_coeff_of_ne_zero hm

lemma e4_coeff (m : ℕ) :
    (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)).coeff m = ((e4 m : ℤ) : ℂ) :=
  RamanujanCongruence.E4_coeff_eq m

lemma qExpansion_f16 :
    qExpansion 1 f16 = qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)
      * qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4) :=
  ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) (E₄ : ModularForm 𝒮ℒ 4)

theorem f16_coeff (n : ℕ) : (qExpansion 1 f16).coeff n = ((a16 n : ℤ) : ℂ) := by
  rw [qExpansion_f16, PowerSeries.coeff_mul, a16, Int.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [delta_coeff, e4_coeff, Int.cast_mul]

theorem rank_cuspForm_16 : Module.rank ℂ (CuspForm 𝒮ℒ ((16 : ℕ) : ℤ)) = 1 := by
  rw [CuspForm.discriminantEquiv.rank_eq]
  exact ModularForm.levelOne_weight_four_rank_one

/-! ### Small coefficients -/

lemma sigma3_two : sigma 3 2 = 9 := by
  simp [ArithmeticFunction.sigma_apply, Nat.prime_two.divisors]

theorem a16_one : a16 1 = 1 := by
  simp [a16, Finset.Nat.antidiagonal_succ, dlt, e4, Ramanujan.tau_one]

theorem a16_two : a16 2 = 216 := by
  simp [a16, Finset.Nat.antidiagonal_succ, dlt, e4, Ramanujan.tau_one, Ramanujan.tau_two]

theorem a16_three : a16 3 = -3348 := by
  simp [a16, Finset.Nat.antidiagonal_succ, dlt, e4, Ramanujan.tau_one, Ramanujan.tau_two,
    Ramanujan.tau_three, sigma3_two]

theorem f16_isNormalizedRankOne : EigenLevelOne.IsNormalizedRankOne 16 f16 a16 where
  rank_one := rank_cuspForm_16
  coeff n _ := f16_coeff n
  one := a16_one
  weight_pos := by norm_num

/-! ### Mordell and Lehmer in weight 16 -/

/-- `Δ E₄` is a Hecke eigenform: `T_p f₁₆ = a₁₆ p • f₁₆`. -/
theorem heckeTP_f16 {p : ℕ} (hp : p.Prime) :
    HeckeLevelOne.heckeTP hp f16 = ((a16 p : ℤ) : ℂ) • f16 :=
  f16_isNormalizedRankOne.heckeTP_eq hp

/-- Mordell multiplicativity in weight 16. -/
theorem a16_mul_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 0 < m) :
    a16 (m * n) = a16 m * a16 n :=
  f16_isNormalizedRankOne.mul_coprime hmn hm

lemma two_pow_not_dvd : ¬ (2 : ℤ) ^ (7 + 1) ∣ a16 2 := by rw [a16_two]; decide
lemma three_pow_not_dvd : ¬ (3 : ℤ) ^ (7 + 1) ∣ a16 3 := by rw [a16_three]; decide

/-- **Lehmer's reduction in weight 16**. -/
theorem a16_ne_zero_iff_primes :
    (∀ n : ℕ, 1 ≤ n → a16 n ≠ 0) ↔ ∀ p : ℕ, p.Prime → a16 p ≠ 0 :=
  f16_isNormalizedRankOne.ne_zero_iff_primes (j := 7) rfl two_pow_not_dvd three_pow_not_dvd

/-! ### The congruence mod 3617 -/

/-- The Eisenstein series of weight 16. -/
noncomputable def E16 : ModularForm 𝒮ℒ ((16 : ℕ) : ℤ) := E (by norm_num : 3 ≤ 16)

/-- `E₄ ^ 4` as a form of weight 16. -/
noncomputable def E4pow4 : ModularForm 𝒮ℒ ((16 : ℕ) : ℤ) :=
  ModularForm.mcast (by norm_num) (E₄.pow 4)

lemma qExpansion_E4pow4 :
    qExpansion 1 E4pow4 = (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)) ^ 4 := by
  rw [E4pow4, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

lemma E16_coeff {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 E16).coeff n = (16320 / 3617 : ℂ) * (sigma 15 n : ℂ) := by
  have h := E_qExpansion_coeff (k := 16) (by norm_num) (by decide) n
  change (qExpansion 1 (E (by norm_num : 3 ≤ 16))).coeff n = _
  rw [h, RamanujanWeight12.bernoulli_sixteen, ite_eq_right_iff.mpr (fun h => absurd h hn)]
  push_cast
  norm_num

lemma qExpansion_sub16 (f g : ModularForm 𝒮ℒ ((16 : ℕ) : ℤ)) :
    qExpansion 1 ((f - g : ModularForm 𝒮ℒ ((16 : ℕ) : ℤ))) = qExpansion 1 f - qExpansion 1 g := by
  have h := (ModularForm.qExpansionAddHom one_pos one_mem_strictPeriods_SL
    ((16 : ℕ) : ℤ)).map_sub f g
  simpa using h

lemma E4_coeff_zero' : (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)).coeff 0 = 1 := by
  rw [e4_coeff]; simp [e4]

lemma E4_coeff_one' : (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)).coeff 1 = 240 := by
  rw [e4_coeff]; simp [e4]

lemma E4pow4_coeff_zero : (qExpansion 1 E4pow4).coeff 0 = 1 := by
  rw [qExpansion_E4pow4, PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, E4_coeff_zero', one_pow]

lemma E4pow4_coeff_one : (qExpansion 1 E4pow4).coeff 1 = 960 := by
  rw [qExpansion_E4pow4]
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E4_coeff_zero',
    E4_coeff_one']
  norm_num

/-- `E₁₆ − E₄⁴`, a cusp form of weight 16. -/
noncomputable def D16 : CuspForm 𝒮ℒ ((16 : ℕ) : ℤ) :=
  ModularForm.toCuspForm (E16 - E4pow4) (by
    rw [qExpansion_sub16, map_sub, E4pow4_coeff_zero,
      show E16 = E (by norm_num : 3 ≤ 16) from rfl, E_qExpansion_coeff_zero (by norm_num)
        (by decide)]
    simp)

lemma qExpansion_D16 : qExpansion 1 D16 = qExpansion 1 E16 - qExpansion 1 E4pow4 :=
  qExpansion_sub16 E16 E4pow4

/-- **The weight-16 Ramanujan congruence**: `a₁₆ n ≡ σ₁₅ n [ZMOD 3617]`. -/
theorem a16_modEq_sigma {n : ℕ} (hn : 1 ≤ n) : a16 n ≡ (sigma 15 n : ℤ) [ZMOD 3617] := by
  -- `D16 = c • f16` with `c = 16320 / 3617 − 960`
  have hsm := f16_isNormalizedRankOne.eq_smul D16
  have hc : (qExpansion 1 D16).coeff 1 = (16320 / 3617 : ℂ) - 960 := by
    rw [qExpansion_D16, map_sub, E16_coeff one_ne_zero, E4pow4_coeff_one,
      show sigma 15 1 = 1 by decide]
    norm_num
  rw [hc] at hsm
  have hcoef := congrArg (fun g : CuspForm 𝒮ℒ ((16 : ℕ) : ℤ) => (qExpansion 1 g).coeff n) hsm
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, smul_eq_mul, f16_coeff, qExpansion_D16, map_sub,
    E16_coeff (by omega)] at hcoef
  obtain ⟨h, hh⟩ := RamanujanCongruence.coeff_pow_intCast
    (fun m => ⟨e4 m, e4_coeff m⟩) 4 n
  rw [qExpansion_E4pow4, hh] at hcoef
  -- clear denominators: `16320 σ − 3617 h = (16320 − 3617 · 960) a`
  have hZ : 16320 * (sigma 15 n : ℤ) - 3617 * h = (16320 - 3617 * 960) * a16 n := by
    have h' : ((16320 * (sigma 15 n : ℤ) - 3617 * h : ℤ) : ℂ)
        = (((16320 - 3617 * 960) * a16 n : ℤ) : ℂ) := by
      push_cast
      linear_combination (3617 : ℂ) * hcoef
    exact_mod_cast h'
  -- reduce mod the prime 3617, where 16320 is a unit
  have hu : (16320 : ZMod 3617) ≠ 0 := by decide
  have h0 : (3617 : ZMod 3617) = 0 := by decide
  have : Fact (Nat.Prime 3617) := ⟨by norm_num⟩
  have hZ' := congrArg (fun z : ℤ => (z : ZMod 3617)) hZ
  push_cast at hZ'
  have hdiff : ((a16 n : ℤ) : ZMod 3617) = (((sigma 15 n : ℕ) : ℤ) : ZMod 3617) := by
    have hmul : (16320 : ZMod 3617)
        * (((sigma 15 n : ℕ) : ZMod 3617) - ((a16 n : ℤ) : ZMod 3617)) = 0 := by
      linear_combination hZ' + ((h : ZMod 3617) - 960 * ((a16 n : ℤ) : ZMod 3617)) * h0
    have hd := (mul_eq_zero.mp hmul).resolve_left hu
    push_cast
    linear_combination -hd
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hdiff

/-! ### The sieve and the initial segment -/

/-- `x ^ 15 = −1` forces `x = −1` in `ZMod 3617` (`15 · 3375 = 14 · 3616 + 1`,
`3375` odd). -/
lemma eq_neg_one_of_pow15 {x : ZMod 3617} (hx : x ^ 15 = -1) : x = -1 := by
  have : Fact (Nat.Prime 3617) := ⟨by norm_num⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hx
    exact neg_ne_zero.mpr one_ne_zero hx.symm
  have h1 : x ^ 3616 = 1 := ZMod.pow_card_sub_one_eq_one hx0
  calc x = (x ^ 3616) ^ 14 * x := by rw [h1, one_pow, one_mul]
    _ = (x ^ 15) ^ 3375 := by rw [← pow_mul, ← pow_mul, ← pow_succ]
    _ = -1 := by rw [hx]; norm_num

/-- **The weight-16 sieve**: `a₁₆ p ≠ 0` for every prime `p ≢ −1 [MOD 3617]`. -/
theorem a16_prime_ne_zero_of_mod {p : ℕ} (hp : p.Prime) (h : p % 3617 ≠ 3616) :
    a16 p ≠ 0 := by
  intro h0
  have hc := a16_modEq_sigma hp.one_lt.le
  rw [h0] at hc
  have hsig : sigma 15 p = 1 + p ^ 15 := by
    rw [show sigma 15 p = sigma 15 (p ^ 1) from by rw [pow_one],
      sigma_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_one]
    simp
  rw [hsig] at hc
  have hz : ((1 + p ^ 15 : ℕ) : ZMod 3617) = 0 := by
    have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hc
    push_cast at this ⊢
    rw [← this]
  push_cast at hz
  have hpow : ((p : ZMod 3617)) ^ 15 = -1 := by linear_combination hz
  have hneg := eq_neg_one_of_pow15 hpow
  have hdvd : ((p + 1 : ℕ) : ZMod 3617) = 0 := by push_cast; rw [hneg]; ring
  rw [ZMod.natCast_eq_zero_iff] at hdvd
  omega

/-- No prime below 21701 is `≡ −1 [MOD 3617]`: the candidates
`3616, 7233, 10850, 14467, 18084` are composite. -/
theorem no_bad_prime_lt_21701 :
    ∀ p : ℕ, p.Prime → p < 21701 → p % 3617 ≠ 3616 := by
  intro p hp hlt hmod
  obtain ⟨k, rfl⟩ : ∃ k, p = 3617 * k + 3616 := ⟨p / 3617, by omega⟩
  have hk : k ≤ 4 := by omega
  interval_cases k <;> norm_num at hp

/-- **Lehmer's question in weight 16, all `n < 21701`**: the coefficients of
`Δ E₄` satisfy `a₁₆ n ≠ 0` for every `0 < n < 21701`. -/
theorem a16_ne_zero_of_lt_21701 {n : ℕ} (hn : 0 < n) (hlt : n < 21701) : a16 n ≠ 0 :=
  f16_isNormalizedRankOne.ne_zero_of_prime_factors (j := 7) rfl two_pow_not_dvd
    three_pow_not_dvd hn fun p hp hd =>
      a16_prime_ne_zero_of_mod hp
        (no_bad_prime_lt_21701 p hp (lt_of_le_of_lt (Nat.le_of_dvd hn hd) hlt))

/-- **Unbounded weight-16 nonvanishing**: `a₁₆ n ≠ 0` for every `n ≥ 1` none
of whose prime factors is `≡ −1 [MOD 3617]` (any exponents). -/
theorem a16_ne_zero_of_prime_factors_mod {n : ℕ} (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p % 3617 ≠ 3616) : a16 n ≠ 0 :=
  f16_isNormalizedRankOne.ne_zero_of_prime_factors (j := 7) rfl two_pow_not_dvd
    three_pow_not_dvd hn fun p hp hd => a16_prime_ne_zero_of_mod hp (h p hp hd)

end LehmerWeight16
