import MathProof.ModularForms.EigenLevelOne
import MathProof.ModularForms.Congruence691
import MathProof.ModularForms.BernoulliHigh

/-!
# Lehmer's question in weight 20: the eigenform `Δ E₄²`

`S₁₆…₂₆(SL(2, ℤ))` are one-dimensional; in weight 20 the space is spanned by
the normalized Hecke eigenform `f₍20₎ = Δ E₄² = q +456 q² +50652 q³ + ⋯`.
Same toolkit as `MathProof/ModularForms/LehmerWeight16.lean`; here the
Eisenstein factor `E₄²` is a product, and the congruence modulus
`174611 = 283 · 617` (from the numerator of `B_20`) is composite, so the
congruence is derived by `ℤ`-divisibility with a coprime cancellation and the
sieve runs prime by prime.

* `f20_isNormalizedRankOne` — `a20 n = Σ_{i + j = n} τ i · g j` with
  `g` the coefficients of `E₄²`; Hecke eigenform, multiplicative, recursion
  with `p ^ 19`;
* `a20_ne_zero_iff_primes` — Lehmer's reduction in weight 20;
* `a20_modEq_sigma` — `a_20 n ≡ σ_19 n [ZMOD 174611]`, from
  `E_20 − E₄⁵ ∈ S_20`;
* `a20_prime_ne_zero_of_mod` — `a_20 p ≠ 0` for every prime
  `p ≢ −1 [MOD 174611]`;
* **`a20_ne_zero_of_lt_1746109`** — `a_20 n ≠ 0` for every `0 < n < 1746109`
  (`1746109` is the least prime `≡ −1 [MOD 174611]`).
-/

open UpperHalfPlane ModularForm CuspForm EisensteinSeries ArithmeticFunction
open scoped MatrixGroups

namespace LehmerWeight20

/-- The q-expansion of `E₄`. -/
local notation "q₄" => qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)

/-! ### The form and its integer coefficients -/

/-- The integer q-coefficients of `E₄`. -/
def e4 (m : ℕ) : ℤ := if m = 0 then 1 else 240 * (sigma 3 m : ℤ)

/-- The integer q-coefficients of `E₄²` (the convolution `e₄ ⋆ e₄`). -/
def g20 (m : ℕ) : ℤ := ∑ x ∈ Finset.antidiagonal m, e4 x.1 * e4 x.2

/-- The integer q-coefficients of `Δ` (`τ n` for `n ≥ 1`, `0` at `n = 0`). -/
noncomputable def dlt (m : ℕ) : ℤ := if m = 0 then 0 else Ramanujan.tau m

/-- The coefficients of `Δ E₄²`: `a20 n = Σ_{i + j = n} τ i · g20 j`. -/
noncomputable def a20 (n : ℕ) : ℤ := ∑ x ∈ Finset.antidiagonal n, dlt x.1 * g20 x.2

/-- The weight-20 cusp form `Δ E₄²`. -/
noncomputable def f20 : CuspForm 𝒮ℒ ((20 : ℕ) : ℤ) :=
  ofMulDiscriminant (ModularForm.mcast (by norm_num) (E₄.mul E₄))

lemma delta_coeff (m : ℕ) :
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff m = ((dlt m : ℤ) : ℂ) := by
  unfold dlt
  split_ifs with hm
  · subst hm; rw [Ramanujan.qExpansion_discriminant_coeff_zero]; simp
  · exact Ramanujan.qExpansion_discriminant_coeff_of_ne_zero hm

lemma e4_coeff (m : ℕ) :
    (q₄).coeff m = ((e4 m : ℤ) : ℂ) :=
  RamanujanCongruence.E4_coeff_eq m

lemma qExpansion_G :
    qExpansion 1 (E₄.mul E₄) = q₄ * q₄ :=
  ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL _ _

lemma g20_coeff (m : ℕ) : (q₄ * q₄).coeff m = ((g20 m : ℤ) : ℂ) := by
  rw [PowerSeries.coeff_mul, g20, Int.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [e4_coeff, e4_coeff, Int.cast_mul]

lemma qExpansion_f20 :
    qExpansion 1 f20 = qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) * (q₄ * q₄) := by
  rw [← qExpansion_G]
  exact ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) (E₄.mul E₄)

theorem f20_coeff (n : ℕ) : (qExpansion 1 f20).coeff n = ((a20 n : ℤ) : ℂ) := by
  rw [qExpansion_f20, PowerSeries.coeff_mul, a20, Int.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [delta_coeff, g20_coeff, Int.cast_mul]

theorem rank_cuspForm_20 : Module.rank ℂ (CuspForm 𝒮ℒ ((20 : ℕ) : ℤ)) = 1 := by
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 8 (by decide)
  norm_num [Nat.ModEq] at h
  exact h

/-! ### Small coefficients -/

lemma sigma3_two : sigma 3 2 = 9 := by decide

theorem a20_one : a20 1 = 1 := by
  simp [a20, g20, Finset.Nat.antidiagonal_succ, dlt, e4, Ramanujan.tau_one]

theorem a20_two : a20 2 = 456 := by
  simp [a20, g20, Finset.Nat.antidiagonal_succ, dlt, e4, Ramanujan.tau_one,
    Ramanujan.tau_two]

theorem a20_three : a20 3 = 50652 := by
  simp [a20, g20, Finset.Nat.antidiagonal_succ, dlt, e4, Ramanujan.tau_one,
    Ramanujan.tau_two, Ramanujan.tau_three, sigma3_two]

theorem f20_isNormalizedRankOne : EigenLevelOne.IsNormalizedRankOne 20 f20 a20 where
  rank_one := rank_cuspForm_20
  coeff n _ := f20_coeff n
  one := a20_one
  weight_pos := by norm_num

/-! ### Mordell and Lehmer in weight 20 -/

/-- `Δ E₄²` is a Hecke eigenform: `T_p f = a20 p • f`. -/
theorem heckeTP_f20 {p : ℕ} (hp : p.Prime) :
    HeckeLevelOne.heckeTP hp f20 = ((a20 p : ℤ) : ℂ) • f20 :=
  f20_isNormalizedRankOne.heckeTP_eq hp

/-- Mordell multiplicativity in weight 20. -/
theorem a20_mul_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 0 < m) :
    a20 (m * n) = a20 m * a20 n :=
  f20_isNormalizedRankOne.mul_coprime hmn hm

lemma two_pow_not_dvd : ¬ (2 : ℤ) ^ (9 + 1) ∣ a20 2 := by rw [a20_two]; decide
lemma three_pow_not_dvd : ¬ (3 : ℤ) ^ (9 + 1) ∣ a20 3 := by rw [a20_three]; decide

/-- **Lehmer's reduction in weight 20**. -/
theorem a20_ne_zero_iff_primes :
    (∀ n : ℕ, 1 ≤ n → a20 n ≠ 0) ↔ ∀ p : ℕ, p.Prime → a20 p ≠ 0 :=
  f20_isNormalizedRankOne.ne_zero_iff_primes (j := 9) rfl two_pow_not_dvd three_pow_not_dvd

/-! ### The congruence mod 174611 -/

/-- The Eisenstein series of weight 20. -/
noncomputable def E20 : ModularForm 𝒮ℒ ((20 : ℕ) : ℤ) := E (by norm_num : 3 ≤ 20)

/-- `E₄⁵` as a form of weight 20. -/
noncomputable def H20 : ModularForm 𝒮ℒ ((20 : ℕ) : ℤ) :=
  ModularForm.mcast (by norm_num) (E₄.pow 5)

lemma qExpansion_H20 : qExpansion 1 H20 = (q₄) ^ 5 := by
  rw [H20, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

lemma E20_coeff {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 E20).coeff n = (13200 / 174611 : ℂ) * (sigma 19 n : ℂ) := by
  have h := E_qExpansion_coeff (k := 20) (by norm_num) (by decide) n
  change (qExpansion 1 (E (by norm_num : 3 ≤ 20))).coeff n = _
  rw [h, RamanujanWeight12.bernoulli_twenty, ite_eq_right_iff.mpr (fun h => absurd h hn)]
  push_cast
  norm_num

lemma qExpansion_sub20 (f g : ModularForm 𝒮ℒ ((20 : ℕ) : ℤ)) :
    qExpansion 1 ((f - g : ModularForm 𝒮ℒ ((20 : ℕ) : ℤ)))
      = qExpansion 1 f - qExpansion 1 g := by
  have h := (ModularForm.qExpansionAddHom one_pos one_mem_strictPeriods_SL
    ((20 : ℕ) : ℤ)).map_sub f g
  simpa using h

lemma E4_coeff_zero' : (q₄).coeff 0 = 1 := by
  rw [e4_coeff]; simp [e4]

lemma E4_coeff_one' : (q₄).coeff 1 = 240 := by
  rw [e4_coeff]; simp [e4]

lemma H20_coeff_zero : (qExpansion 1 H20).coeff 0 = 1 := by
  rw [qExpansion_H20]
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, E4_coeff_zero', one_pow]

lemma H20_coeff_one : (qExpansion 1 H20).coeff 1 = 1200 := by
  rw [qExpansion_H20]
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E4_coeff_zero',
    E4_coeff_one']
  norm_num

/-- `E_20 − E₄⁵`, a cusp form of weight 20. -/
noncomputable def D20 : CuspForm 𝒮ℒ ((20 : ℕ) : ℤ) :=
  ModularForm.toCuspForm (E20 - H20) (by
    rw [qExpansion_sub20, map_sub, H20_coeff_zero,
      show E20 = E (by norm_num : 3 ≤ 20) from rfl, E_qExpansion_coeff_zero (by norm_num)
        (by decide)]
    simp)

lemma qExpansion_D20 : qExpansion 1 D20 = qExpansion 1 E20 - qExpansion 1 H20 :=
  qExpansion_sub20 E20 H20

/-- **The weight-20 Ramanujan congruence**: `a_20 n ≡ σ_19 n [ZMOD 174611]`. -/
theorem a20_modEq_sigma {n : ℕ} (hn : 1 ≤ n) :
    a20 n ≡ (sigma 19 n : ℤ) [ZMOD 174611] := by
  have hsm := f20_isNormalizedRankOne.eq_smul D20
  have hc : (qExpansion 1 D20).coeff 1 = (13200 / 174611 : ℂ) - 1200 := by
    rw [qExpansion_D20, map_sub, E20_coeff one_ne_zero, H20_coeff_one,
      show sigma 19 1 = 1 by decide]
    norm_num
  rw [hc] at hsm
  have hcoef :=
    congrArg (fun g : CuspForm 𝒮ℒ ((20 : ℕ) : ℤ) => (qExpansion 1 g).coeff n) hsm
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, smul_eq_mul, f20_coeff, qExpansion_D20, map_sub,
    E20_coeff (by omega)] at hcoef
  obtain ⟨h, hh⟩ := RamanujanCongruence.coeff_mul_intCast
    (RamanujanCongruence.coeff_pow_intCast (fun m => ⟨e4 m, e4_coeff m⟩) 4)
    (fun m => ⟨e4 m, e4_coeff m⟩) n
  rw [qExpansion_H20, pow_succ, hh] at hcoef
  -- clear denominators: `13200 (σ − a) = 174611 (h − 1200 a)`
  have hZ : (13200 : ℤ) * ((sigma 19 n : ℤ) - a20 n) = 174611 * (h - 1200 * a20 n) := by
    have h' : (((13200 : ℤ) * ((sigma 19 n : ℤ) - a20 n) : ℤ) : ℂ)
        = ((174611 * (h - 1200 * a20 n) : ℤ) : ℂ) := by
      push_cast
      linear_combination (174611 : ℂ) * hcoef
    exact_mod_cast h'
  have hdvd : (174611 : ℤ) ∣ (13200 : ℤ) * ((sigma 19 n : ℤ) - a20 n) := ⟨_, hZ⟩
  have hcop : Int.gcd 174611 13200 = 1 := by norm_num
  exact (Int.modEq_iff_dvd.mpr (Int.dvd_of_dvd_mul_right_of_gcd_one hdvd hcop))

/-! ### The sieve and the initial segment -/

/-- `x ^ 19 = −1` forces `x = −1` in `ZMod 283` (`19 · 193 = 13 · 282 + 1`, `193` odd). -/
lemma eq_neg_one_mod283 {x : ZMod 283} (hx : x ^ 19 = -1) : x = -1 := by
  have : Fact (Nat.Prime 283) := ⟨by norm_num⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hx
    exact neg_ne_zero.mpr one_ne_zero hx.symm
  have h1 : x ^ 282 = 1 := ZMod.pow_card_sub_one_eq_one hx0
  calc x = (x ^ 282) ^ 13 * x := by rw [h1, one_pow, one_mul]
    _ = (x ^ 19) ^ 193 := by rw [← pow_mul, ← pow_mul, ← pow_succ]
    _ = -1 := by rw [hx]; norm_num

/-- `x ^ 19 = −1` forces `x = −1` in `ZMod 617` (`19 · 227 = 7 · 616 + 1`, `227` odd). -/
lemma eq_neg_one_mod617 {x : ZMod 617} (hx : x ^ 19 = -1) : x = -1 := by
  have : Fact (Nat.Prime 617) := ⟨by norm_num⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hx
    exact neg_ne_zero.mpr one_ne_zero hx.symm
  have h1 : x ^ 616 = 1 := ZMod.pow_card_sub_one_eq_one hx0
  calc x = (x ^ 616) ^ 7 * x := by rw [h1, one_pow, one_mul]
    _ = (x ^ 19) ^ 227 := by rw [← pow_mul, ← pow_mul, ← pow_succ]
    _ = -1 := by rw [hx]; norm_num

/-- From `1 + p ^ 19 ≡ 0 [ZMOD ℓ]` to `ℓ ∣ p + 1`, for one prime factor `ℓ`. -/
lemma dvd_succ_of_pow {ℓ p : ℕ} (h : ∀ x : ZMod ℓ, x ^ 19 = -1 → x = -1)
    (hz : (((1 + p ^ 19 : ℕ) : ℤ) : ZMod ℓ) = 0) : ℓ ∣ p + 1 := by
  push_cast at hz
  have hneg := h (p : ZMod ℓ) (by linear_combination hz)
  have hd : ((p + 1 : ℕ) : ZMod ℓ) = 0 := by push_cast; rw [hneg]; ring
  rwa [ZMod.natCast_eq_zero_iff] at hd

/-- **The weight-20 sieve**: `a_20 p ≠ 0` for every prime `p ≢ −1 [MOD 174611]`. -/
theorem a20_prime_ne_zero_of_mod {p : ℕ} (hp : p.Prime) (h : p % 174611 ≠ 174610) :
    a20 p ≠ 0 := by
  intro h0
  have hc := a20_modEq_sigma hp.one_lt.le
  rw [h0] at hc
  have hsig : sigma 19 p = 1 + p ^ 19 := by
    rw [show sigma 19 p = sigma 19 (p ^ 1) from by rw [pow_one],
      sigma_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_one]
    simp
  rw [hsig] at hc
  -- `174611 ∣ 1 + p ^ 19`, hence each prime factor divides `p + 1`
  have hL : (174611 : ℤ) ∣ ((1 + p ^ 19 : ℕ) : ℤ) := by
    have := (Int.modEq_iff_dvd.mp hc); simpa using this
  have h1 : (283 : ℤ) ∣ ((1 + p ^ 19 : ℕ) : ℤ) :=
    (show (283 : ℤ) ∣ 174611 by norm_num).trans hL
  have h2 : (617 : ℤ) ∣ ((1 + p ^ 19 : ℕ) : ℤ) :=
    (show (617 : ℤ) ∣ 174611 by norm_num).trans hL
  have d1 := dvd_succ_of_pow (ℓ := 283) (fun x hx => eq_neg_one_mod283 hx)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast h1))
  have d2 := dvd_succ_of_pow (ℓ := 617) (fun x hx => eq_neg_one_mod617 hx)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast h2))
  have d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 283 617) d1 d2
  omega

/-- No prime below 1746109 is `≡ −1 [MOD 174611]`: the 9 candidates
`174611 k + 174610` (`k ≤ 8`) are composite. -/
theorem no_bad_prime_lt_1746109 :
    ∀ p : ℕ, p.Prime → p < 1746109 → p % 174611 ≠ 174610 := by
  intro p hp hlt hmod
  obtain ⟨k, rfl⟩ : ∃ k, p = 174611 * k + 174610 := ⟨p / 174611, by omega⟩
  have hk : k ≤ 8 := by omega
  interval_cases k <;> norm_num at hp

/-- **Lehmer's question in weight 20, all `n < 1746109`**: the coefficients of
`Δ E₄²` satisfy `a_20 n ≠ 0` for every `0 < n < 1746109`. -/
theorem a20_ne_zero_of_lt_1746109 {n : ℕ} (hn : 0 < n) (hlt : n < 1746109) : a20 n ≠ 0 :=
  f20_isNormalizedRankOne.ne_zero_of_prime_factors (j := 9) rfl two_pow_not_dvd
    three_pow_not_dvd hn fun p hp hd =>
      a20_prime_ne_zero_of_mod hp
        (no_bad_prime_lt_1746109 p hp (lt_of_le_of_lt (Nat.le_of_dvd hn hd) hlt))

/-- **Unbounded weight-20 nonvanishing**: `a_20 n ≠ 0` for every `n ≥ 1` none
of whose prime factors is `≡ −1 [MOD 174611]` (any exponents). -/
theorem a20_ne_zero_of_prime_factors_mod {n : ℕ} (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p % 174611 ≠ 174610) : a20 n ≠ 0 :=
  f20_isNormalizedRankOne.ne_zero_of_prime_factors (j := 9) rfl two_pow_not_dvd
    three_pow_not_dvd hn fun p hp hd => a20_prime_ne_zero_of_mod hp (h p hp hd)

end LehmerWeight20
