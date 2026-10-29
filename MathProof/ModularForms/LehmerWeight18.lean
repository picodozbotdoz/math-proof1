import MathProof.ModularForms.EigenLevelOne
import MathProof.ModularForms.Congruence691
import MathProof.ModularForms.BernoulliHigh

/-!
# Lehmer's question in weight 18: the eigenform `Δ E₆`

`S₁₈(SL(2, ℤ))` is one-dimensional, spanned by the normalized Hecke eigenform
`f₁₈ = Δ E₆ = q − 528 q² − 4284 q³ + 147712 q⁴ + ⋯`.  Same toolkit as
`MathProof/ModularForms/LehmerWeight16.lean`:

* `f18_isNormalizedRankOne` — `a18 n = Σ_{i + j = n} τ i · e₆ j`; Hecke
  eigenform, multiplicative, recursion with `p ^ 17`;
* `a18_ne_zero_iff_primes` — Lehmer's reduction in weight 18;
* `a18_modEq_sigma` — `a₁₈ n ≡ σ₁₇ n [ZMOD 43867]` (`43867` = numerator of
  `B₁₈`), from `E₁₈ − E₄³ E₆ ∈ S₁₈`;
* `a18_prime_ne_zero_of_mod` — `a₁₈ p ≠ 0` for every prime
  `p ≢ −1 [MOD 43867]`;
* **`a18_ne_zero_of_lt_263201`** — `a₁₈ n ≠ 0` for every `0 < n < 263201`
  (`263201` is the least prime `≡ −1 [MOD 43867]`).
-/

open UpperHalfPlane ModularForm CuspForm EisensteinSeries ArithmeticFunction
open scoped MatrixGroups

namespace LehmerWeight18

/-! ### The form and its integer coefficients -/

/-- The integer q-coefficients of `E₄`: `1, 240 σ₃ 1, 240 σ₃ 2, …`. -/
def e4 (m : ℕ) : ℤ := if m = 0 then 1 else 240 * (sigma 3 m : ℤ)

/-- The integer q-coefficients of `E₆`: `1, −504 σ₅ 1, −504 σ₅ 2, …`. -/
def e6 (m : ℕ) : ℤ := if m = 0 then 1 else -504 * (sigma 5 m : ℤ)

/-- The integer q-coefficients of `Δ` (`τ n` for `n ≥ 1`, `0` at `n = 0`). -/
noncomputable def dlt (m : ℕ) : ℤ := if m = 0 then 0 else Ramanujan.tau m

/-- The coefficients of `Δ E₆`: `a18 n = Σ_{i + j = n} τ i · e₆ j`. -/
noncomputable def a18 (n : ℕ) : ℤ := ∑ x ∈ Finset.antidiagonal n, dlt x.1 * e6 x.2

/-- The weight-18 cusp form `Δ E₆`. -/
noncomputable def f18 : CuspForm 𝒮ℒ ((18 : ℕ) : ℤ) :=
  ofMulDiscriminant (ModularForm.mcast (by norm_num) E₆)

lemma delta_coeff (m : ℕ) :
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff m = ((dlt m : ℤ) : ℂ) := by
  unfold dlt
  split_ifs with hm
  · subst hm; rw [Ramanujan.qExpansion_discriminant_coeff_zero]; simp
  · exact Ramanujan.qExpansion_discriminant_coeff_of_ne_zero hm

lemma e4_coeff (m : ℕ) :
    (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)).coeff m = ((e4 m : ℤ) : ℂ) :=
  RamanujanCongruence.E4_coeff_eq m

lemma e6_coeff (m : ℕ) :
    (qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6)).coeff m = ((e6 m : ℤ) : ℂ) :=
  RamanujanCongruence.E6_coeff_eq m

lemma qExpansion_f18 :
    qExpansion 1 f18 = qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)
      * qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6) :=
  ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) (E₆ : ModularForm 𝒮ℒ 6)

theorem f18_coeff (n : ℕ) : (qExpansion 1 f18).coeff n = ((a18 n : ℤ) : ℂ) := by
  rw [qExpansion_f18, PowerSeries.coeff_mul, a18, Int.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [delta_coeff, e6_coeff, Int.cast_mul]

theorem rank_cuspForm_18 : Module.rank ℂ (CuspForm 𝒮ℒ ((18 : ℕ) : ℤ)) = 1 := by
  rw [CuspForm.discriminantEquiv.rank_eq]
  exact ModularForm.levelOne_weight_six_rank_one

/-! ### Small coefficients -/

lemma sigma5_two : sigma 5 2 = 33 := by
  simp [ArithmeticFunction.sigma_apply, Nat.prime_two.divisors]

theorem a18_one : a18 1 = 1 := by
  simp [a18, Finset.Nat.antidiagonal_succ, dlt, e6, Ramanujan.tau_one]

theorem a18_two : a18 2 = -528 := by
  simp [a18, Finset.Nat.antidiagonal_succ, dlt, e6, Ramanujan.tau_one, Ramanujan.tau_two]

theorem a18_three : a18 3 = -4284 := by
  simp [a18, Finset.Nat.antidiagonal_succ, dlt, e6, Ramanujan.tau_one, Ramanujan.tau_two,
    Ramanujan.tau_three, sigma5_two]

theorem f18_isNormalizedRankOne : EigenLevelOne.IsNormalizedRankOne 18 f18 a18 where
  rank_one := rank_cuspForm_18
  coeff n _ := f18_coeff n
  one := a18_one
  weight_pos := by norm_num

/-! ### Mordell and Lehmer in weight 18 -/

/-- `Δ E₆` is a Hecke eigenform: `T_p f₁₈ = a₁₈ p • f₁₈`. -/
theorem heckeTP_f18 {p : ℕ} (hp : p.Prime) :
    HeckeLevelOne.heckeTP hp f18 = ((a18 p : ℤ) : ℂ) • f18 :=
  f18_isNormalizedRankOne.heckeTP_eq hp

/-- Mordell multiplicativity in weight 18. -/
theorem a18_mul_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 0 < m) :
    a18 (m * n) = a18 m * a18 n :=
  f18_isNormalizedRankOne.mul_coprime hmn hm

lemma two_pow_not_dvd : ¬ (2 : ℤ) ^ (8 + 1) ∣ a18 2 := by rw [a18_two]; decide
lemma three_pow_not_dvd : ¬ (3 : ℤ) ^ (8 + 1) ∣ a18 3 := by rw [a18_three]; decide

/-- **Lehmer's reduction in weight 18**. -/
theorem a18_ne_zero_iff_primes :
    (∀ n : ℕ, 1 ≤ n → a18 n ≠ 0) ↔ ∀ p : ℕ, p.Prime → a18 p ≠ 0 :=
  f18_isNormalizedRankOne.ne_zero_iff_primes (j := 8) rfl two_pow_not_dvd three_pow_not_dvd

/-! ### The congruence mod 43867 -/

/-- The Eisenstein series of weight 18. -/
noncomputable def E18 : ModularForm 𝒮ℒ ((18 : ℕ) : ℤ) := E (by norm_num : 3 ≤ 18)

/-- `E₄ ^ 3 E₆` as a form of weight 18. -/
noncomputable def H18 : ModularForm 𝒮ℒ ((18 : ℕ) : ℤ) :=
  ModularForm.mcast (by norm_num) ((E₄.pow 3).mul E₆)

lemma qExpansion_H18 :
    qExpansion 1 H18 = (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)) ^ 3
      * qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6) := by
  rw [H18, ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos
    one_mem_strictPeriods_SL, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

lemma E18_coeff {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 E18).coeff n = (-28728 / 43867 : ℂ) * (sigma 17 n : ℂ) := by
  have h := E_qExpansion_coeff (k := 18) (by norm_num) (by decide) n
  change (qExpansion 1 (E (by norm_num : 3 ≤ 18))).coeff n = _
  rw [h, RamanujanWeight12.bernoulli_eighteen, ite_eq_right_iff.mpr (fun h => absurd h hn)]
  push_cast
  norm_num

lemma qExpansion_sub18 (f g : ModularForm 𝒮ℒ ((18 : ℕ) : ℤ)) :
    qExpansion 1 ((f - g : ModularForm 𝒮ℒ ((18 : ℕ) : ℤ)))
      = qExpansion 1 f - qExpansion 1 g := by
  have h := (ModularForm.qExpansionAddHom one_pos one_mem_strictPeriods_SL
    ((18 : ℕ) : ℤ)).map_sub f g
  simpa using h

lemma E4_coeff_zero' : (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)).coeff 0 = 1 := by
  rw [e4_coeff]; simp [e4]

lemma E4_coeff_one' : (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)).coeff 1 = 240 := by
  rw [e4_coeff]; simp [e4]

lemma E6_coeff_zero' : (qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6)).coeff 0 = 1 := by
  rw [e6_coeff]; simp [e6]

lemma E6_coeff_one' : (qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6)).coeff 1 = -504 := by
  rw [e6_coeff]; simp [e6]

lemma H18_coeff_zero : (qExpansion 1 H18).coeff 0 = 1 := by
  rw [qExpansion_H18, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, E4_coeff_zero', E6_coeff_zero', one_pow,
    one_mul]

lemma H18_coeff_one : (qExpansion 1 H18).coeff 1 = 216 := by
  rw [qExpansion_H18]
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E4_coeff_zero',
    E4_coeff_one', E6_coeff_zero', E6_coeff_one']
  norm_num

/-- `E₁₈ − E₄³ E₆`, a cusp form of weight 18. -/
noncomputable def D18 : CuspForm 𝒮ℒ ((18 : ℕ) : ℤ) :=
  ModularForm.toCuspForm (E18 - H18) (by
    rw [qExpansion_sub18, map_sub, H18_coeff_zero,
      show E18 = E (by norm_num : 3 ≤ 18) from rfl, E_qExpansion_coeff_zero (by norm_num)
        (by decide)]
    simp)

lemma qExpansion_D18 : qExpansion 1 D18 = qExpansion 1 E18 - qExpansion 1 H18 :=
  qExpansion_sub18 E18 H18

/-- **The weight-18 Ramanujan congruence**: `a₁₈ n ≡ σ₁₇ n [ZMOD 43867]`. -/
theorem a18_modEq_sigma {n : ℕ} (hn : 1 ≤ n) : a18 n ≡ (sigma 17 n : ℤ) [ZMOD 43867] := by
  -- `D18 = c • f18` with `c = −28728 / 43867 − 216`
  have hsm := f18_isNormalizedRankOne.eq_smul D18
  have hc : (qExpansion 1 D18).coeff 1 = (-28728 / 43867 : ℂ) - 216 := by
    rw [qExpansion_D18, map_sub, E18_coeff one_ne_zero, H18_coeff_one,
      show sigma 17 1 = 1 by decide]
    norm_num
  rw [hc] at hsm
  have hcoef :=
    congrArg (fun g : CuspForm 𝒮ℒ ((18 : ℕ) : ℤ) => (qExpansion 1 g).coeff n) hsm
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, smul_eq_mul, f18_coeff, qExpansion_D18, map_sub,
    E18_coeff (by omega)] at hcoef
  obtain ⟨h, hh⟩ := RamanujanCongruence.coeff_mul_intCast
    (RamanujanCongruence.coeff_pow_intCast (fun m => ⟨e4 m, e4_coeff m⟩) 3)
    (fun m => ⟨e6 m, e6_coeff m⟩) n
  rw [qExpansion_H18, hh] at hcoef
  -- clear denominators: `−28728 σ − 43867 h = (−28728 − 43867 · 216) a`
  have hZ : -28728 * (sigma 17 n : ℤ) - 43867 * h = (-28728 - 43867 * 216) * a18 n := by
    have h' : ((-28728 * (sigma 17 n : ℤ) - 43867 * h : ℤ) : ℂ)
        = (((-28728 - 43867 * 216) * a18 n : ℤ) : ℂ) := by
      push_cast
      linear_combination (43867 : ℂ) * hcoef
    exact_mod_cast h'
  -- reduce mod the prime 43867, where 28728 is a unit
  have hu : (-28728 : ZMod 43867) ≠ 0 := by decide
  have h0 : (43867 : ZMod 43867) = 0 := by decide
  have : Fact (Nat.Prime 43867) := ⟨by norm_num⟩
  have hZ' := congrArg (fun z : ℤ => (z : ZMod 43867)) hZ
  push_cast at hZ'
  have hdiff : ((a18 n : ℤ) : ZMod 43867) = (((sigma 17 n : ℕ) : ℤ) : ZMod 43867) := by
    have hmul : (-28728 : ZMod 43867)
        * (((sigma 17 n : ℕ) : ZMod 43867) - ((a18 n : ℤ) : ZMod 43867)) = 0 := by
      linear_combination hZ' + ((h : ZMod 43867) - 216 * ((a18 n : ℤ) : ZMod 43867)) * h0
    have hd := (mul_eq_zero.mp hmul).resolve_left hu
    push_cast
    linear_combination -hd
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hdiff

/-! ### The sieve and the initial segment -/

/-- `x ^ 17 = −1` forces `x = −1` in `ZMod 43867` (`17 · 36125 = 14 · 43866 + 1`,
`36125` odd). -/
lemma eq_neg_one_of_pow17 {x : ZMod 43867} (hx : x ^ 17 = -1) : x = -1 := by
  have : Fact (Nat.Prime 43867) := ⟨by norm_num⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hx
    exact neg_ne_zero.mpr one_ne_zero hx.symm
  have h1 : x ^ 43866 = 1 := ZMod.pow_card_sub_one_eq_one hx0
  calc x = (x ^ 43866) ^ 14 * x := by rw [h1, one_pow, one_mul]
    _ = (x ^ 17) ^ 36125 := by rw [← pow_mul, ← pow_mul, ← pow_succ]
    _ = -1 := by rw [hx]; norm_num

/-- **The weight-18 sieve**: `a₁₈ p ≠ 0` for every prime `p ≢ −1 [MOD 43867]`. -/
theorem a18_prime_ne_zero_of_mod {p : ℕ} (hp : p.Prime) (h : p % 43867 ≠ 43866) :
    a18 p ≠ 0 := by
  intro h0
  have hc := a18_modEq_sigma hp.one_lt.le
  rw [h0] at hc
  have hsig : sigma 17 p = 1 + p ^ 17 := by
    rw [show sigma 17 p = sigma 17 (p ^ 1) from by rw [pow_one],
      sigma_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_one]
    simp
  rw [hsig] at hc
  have hz : ((1 + p ^ 17 : ℕ) : ZMod 43867) = 0 := by
    have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hc
    push_cast at this ⊢
    rw [← this]
  push_cast at hz
  have hpow : ((p : ZMod 43867)) ^ 17 = -1 := by linear_combination hz
  have hneg := eq_neg_one_of_pow17 hpow
  have hdvd : ((p + 1 : ℕ) : ZMod 43867) = 0 := by push_cast; rw [hneg]; ring
  rw [ZMod.natCast_eq_zero_iff] at hdvd
  omega

/-- No prime below 263201 is `≡ −1 [MOD 43867]`: the candidates
`43866, 87733, 131600, 175467, 219334` are composite. -/
theorem no_bad_prime_lt_263201 :
    ∀ p : ℕ, p.Prime → p < 263201 → p % 43867 ≠ 43866 := by
  intro p hp hlt hmod
  obtain ⟨k, rfl⟩ : ∃ k, p = 43867 * k + 43866 := ⟨p / 43867, by omega⟩
  have hk : k ≤ 4 := by omega
  interval_cases k <;> norm_num at hp

/-- **Lehmer's question in weight 18, all `n < 263201`**: the coefficients of
`Δ E₆` satisfy `a₁₈ n ≠ 0` for every `0 < n < 263201`. -/
theorem a18_ne_zero_of_lt_263201 {n : ℕ} (hn : 0 < n) (hlt : n < 263201) : a18 n ≠ 0 :=
  f18_isNormalizedRankOne.ne_zero_of_prime_factors (j := 8) rfl two_pow_not_dvd
    three_pow_not_dvd hn fun p hp hd =>
      a18_prime_ne_zero_of_mod hp
        (no_bad_prime_lt_263201 p hp (lt_of_le_of_lt (Nat.le_of_dvd hn hd) hlt))

/-- **Unbounded weight-18 nonvanishing**: `a₁₈ n ≠ 0` for every `n ≥ 1` none
of whose prime factors is `≡ −1 [MOD 43867]` (any exponents). -/
theorem a18_ne_zero_of_prime_factors_mod {n : ℕ} (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p % 43867 ≠ 43866) : a18 n ≠ 0 :=
  f18_isNormalizedRankOne.ne_zero_of_prime_factors (j := 8) rfl two_pow_not_dvd
    three_pow_not_dvd hn fun p hp hd => a18_prime_ne_zero_of_mod hp (h p hp hd)

end LehmerWeight18
