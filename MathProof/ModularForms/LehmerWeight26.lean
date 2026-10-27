import MathProof.ModularForms.EigenLevelOne
import MathProof.ModularForms.Congruence691
import MathProof.ModularForms.BernoulliHigh

/-!
# Lehmer's question in weight 26: the eigenform `Δ E₄² E₆`

Weight 26 is the last level-one weight with `dim S_k = 1`; the space is
spanned by `f₂₆ = Δ E₄² E₆ = q − 48 q² − 195804 q³ + ⋯`.  Same toolkit as
`MathProof/ModularForms/LehmerWeight16.lean`, with one new feature: the
congruence prime `657931` (from `B₂₆ = 8553103 / 6`, `8553103 = 13 · 657931`)
has `gcd(25, 657930) = 5`, so `p ^ 25 ≡ −1` no longer pins `p ≡ −1`.  The bad
classes are `−ζ` for the five fifth roots of unity `ζ ∈ ZMod 657931`, which
are exhibited explicitly (`X⁵ − 1 = (X − 1)(X − 30567)(X − 47671)(X − 79469)
(X − 500223)`, checked through its elementary symmetric functions).

* `f26_isNormalizedRankOne`, `a26_ne_zero_iff_primes` — Mordell + Lehmer;
* `a26_modEq_sigma` — `a₂₆ n ≡ σ₂₅ n [ZMOD 657931]`, from
  `E₂₆ − E₄⁵ E₆ ∈ S₂₆`;
* `a26_prime_ne_zero_of_mod` — `a₂₆ p ≠ 0` for every prime `p` outside the five
  classes `157708, 578462, 610260, 627364, 657930 [MOD 657931]`;
* **`a26_ne_zero_of_lt_1315861`** — `a₂₆ n ≠ 0` for every `0 < n < 1315861`
  (`1315861 = 2 · 657931 − 1` is the least prime in a bad class).
-/

open UpperHalfPlane ModularForm CuspForm EisensteinSeries ArithmeticFunction
open scoped MatrixGroups

namespace LehmerWeight26

/-- The q-expansion of `E₄`. -/
local notation "q₄" => qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)

/-- The q-expansion of `E₆`. -/
local notation "q₆" => qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6)

/-! ### The form and its integer coefficients -/

/-- The integer q-coefficients of `E₄`. -/
def e4 (m : ℕ) : ℤ := if m = 0 then 1 else 240 * (sigma 3 m : ℤ)

/-- The integer q-coefficients of `E₆`. -/
def e6 (m : ℕ) : ℤ := if m = 0 then 1 else -504 * (sigma 5 m : ℤ)

/-- The integer q-coefficients of `E₄²` (the convolution `e₄ ⋆ e₄`). -/
def e44 (m : ℕ) : ℤ := ∑ x ∈ Finset.antidiagonal m, e4 x.1 * e4 x.2

/-- The integer q-coefficients of `E₄² E₆` (the convolution `e₄₄ ⋆ e₆`). -/
def g26 (m : ℕ) : ℤ := ∑ x ∈ Finset.antidiagonal m, e44 x.1 * e6 x.2

/-- The integer q-coefficients of `Δ` (`τ n` for `n ≥ 1`, `0` at `n = 0`). -/
noncomputable def dlt (m : ℕ) : ℤ := if m = 0 then 0 else Ramanujan.tau m

/-- The coefficients of `Δ E₄² E₆`: `a26 n = Σ_{i + j = n} τ i · g26 j`. -/
noncomputable def a26 (n : ℕ) : ℤ := ∑ x ∈ Finset.antidiagonal n, dlt x.1 * g26 x.2

/-- The weight-26 cusp form `Δ E₄² E₆`. -/
noncomputable def f26 : CuspForm 𝒮ℒ ((26 : ℕ) : ℤ) :=
  ofMulDiscriminant (ModularForm.mcast (by norm_num) ((E₄.mul E₄).mul E₆))

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
    qExpansion 1 ((E₄.mul E₄).mul E₆) = q₄ * q₄ * q₆ := by
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL]

lemma e44_coeff (m : ℕ) : (q₄ * q₄).coeff m = ((e44 m : ℤ) : ℂ) := by
  rw [PowerSeries.coeff_mul, e44, Int.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [e4_coeff, e4_coeff, Int.cast_mul]

lemma g26_coeff (m : ℕ) : (q₄ * q₄ * q₆).coeff m = ((g26 m : ℤ) : ℂ) := by
  rw [PowerSeries.coeff_mul, g26, Int.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [e44_coeff, e6_coeff, Int.cast_mul]

lemma qExpansion_f26 :
    qExpansion 1 f26 = qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) * (q₄ * q₄ * q₆) := by
  rw [← qExpansion_G]
  exact ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) ((E₄.mul E₄).mul E₆)

theorem f26_coeff (n : ℕ) : (qExpansion 1 f26).coeff n = ((a26 n : ℤ) : ℂ) := by
  rw [qExpansion_f26, PowerSeries.coeff_mul, a26, Int.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [delta_coeff, g26_coeff, Int.cast_mul]

theorem rank_cuspForm_26 : Module.rank ℂ (CuspForm 𝒮ℒ ((26 : ℕ) : ℤ)) = 1 := by
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one 14 (by decide)
  norm_num [Nat.ModEq] at h
  exact h

/-! ### Small coefficients -/

lemma sigma3_two : sigma 3 2 = 9 := by decide
lemma sigma5_two : sigma 5 2 = 33 := by decide

theorem a26_one : a26 1 = 1 := by
  simp [a26, g26, e44, Finset.Nat.antidiagonal_succ, dlt, e4, e6, Ramanujan.tau_one]

theorem a26_two : a26 2 = -48 := by
  simp [a26, g26, e44, Finset.Nat.antidiagonal_succ, dlt, e4, e6, Ramanujan.tau_one,
    Ramanujan.tau_two]

theorem a26_three : a26 3 = -195804 := by
  simp [a26, g26, e44, Finset.Nat.antidiagonal_succ, dlt, e4, e6, Ramanujan.tau_one,
    Ramanujan.tau_two, Ramanujan.tau_three, sigma3_two, sigma5_two]

theorem f26_isNormalizedRankOne : EigenLevelOne.IsNormalizedRankOne 26 f26 a26 where
  rank_one := rank_cuspForm_26
  coeff n _ := f26_coeff n
  one := a26_one
  weight_pos := by norm_num

/-! ### Mordell and Lehmer in weight 26 -/

/-- `Δ E₄² E₆` is a Hecke eigenform: `T_p f = a26 p • f`. -/
theorem heckeTP_f26 {p : ℕ} (hp : p.Prime) :
    HeckeLevelOne.heckeTP hp f26 = ((a26 p : ℤ) : ℂ) • f26 :=
  f26_isNormalizedRankOne.heckeTP_eq hp

/-- Mordell multiplicativity in weight 26. -/
theorem a26_mul_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 0 < m) :
    a26 (m * n) = a26 m * a26 n :=
  f26_isNormalizedRankOne.mul_coprime hmn hm

lemma two_pow_not_dvd : ¬ (2 : ℤ) ^ (12 + 1) ∣ a26 2 := by rw [a26_two]; decide
lemma three_pow_not_dvd : ¬ (3 : ℤ) ^ (12 + 1) ∣ a26 3 := by rw [a26_three]; decide

/-- **Lehmer's reduction in weight 26**. -/
theorem a26_ne_zero_iff_primes :
    (∀ n : ℕ, 1 ≤ n → a26 n ≠ 0) ↔ ∀ p : ℕ, p.Prime → a26 p ≠ 0 :=
  f26_isNormalizedRankOne.ne_zero_iff_primes (j := 12) rfl two_pow_not_dvd three_pow_not_dvd

/-! ### The congruence mod 657931 -/

/-- The Eisenstein series of weight 26. -/
noncomputable def E26 : ModularForm 𝒮ℒ ((26 : ℕ) : ℤ) := E (by norm_num : 3 ≤ 26)

/-- `E₄⁵E₆` as a form of weight 26. -/
noncomputable def H26 : ModularForm 𝒮ℒ ((26 : ℕ) : ℤ) :=
  ModularForm.mcast (by norm_num) ((E₄.pow 5).mul E₆)

lemma qExpansion_H26 : qExpansion 1 H26 = (q₄) ^ 5 * q₆ := by
  rw [H26, ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos
    one_mem_strictPeriods_SL, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

lemma E26_coeff {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 E26).coeff n = (-24 / 657931 : ℂ) * (sigma 25 n : ℂ) := by
  have h := E_qExpansion_coeff (k := 26) (by norm_num) (by decide) n
  change (qExpansion 1 (E (by norm_num : 3 ≤ 26))).coeff n = _
  rw [h, RamanujanWeight12.bernoulli_twentySix, ite_eq_right_iff.mpr (fun h => absurd h hn)]
  push_cast
  norm_num

lemma qExpansion_sub26 (f g : ModularForm 𝒮ℒ ((26 : ℕ) : ℤ)) :
    qExpansion 1 ((f - g : ModularForm 𝒮ℒ ((26 : ℕ) : ℤ)))
      = qExpansion 1 f - qExpansion 1 g := by
  have h := (ModularForm.qExpansionAddHom one_pos one_mem_strictPeriods_SL
    ((26 : ℕ) : ℤ)).map_sub f g
  simpa using h

lemma E4_coeff_zero' : (q₄).coeff 0 = 1 := by
  rw [e4_coeff]; simp [e4]

lemma E4_coeff_one' : (q₄).coeff 1 = 240 := by
  rw [e4_coeff]; simp [e4]

lemma E6_coeff_zero' : (q₆).coeff 0 = 1 := by
  rw [e6_coeff]; simp [e6]

lemma E6_coeff_one' : (q₆).coeff 1 = -504 := by
  rw [e6_coeff]; simp [e6]

lemma H26_coeff_zero : (qExpansion 1 H26).coeff 0 = 1 := by
  rw [qExpansion_H26]
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, E4_coeff_zero', E6_coeff_zero', one_pow,
    one_mul]

lemma H26_coeff_one : (qExpansion 1 H26).coeff 1 = 696 := by
  rw [qExpansion_H26]
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E4_coeff_zero',
    E4_coeff_one', E6_coeff_zero', E6_coeff_one']
  norm_num

/-- `E_26 − E₄⁵E₆`, a cusp form of weight 26. -/
noncomputable def D26 : CuspForm 𝒮ℒ ((26 : ℕ) : ℤ) :=
  ModularForm.toCuspForm (E26 - H26) (by
    rw [qExpansion_sub26, map_sub, H26_coeff_zero,
      show E26 = E (by norm_num : 3 ≤ 26) from rfl, E_qExpansion_coeff_zero (by norm_num)
        (by decide)]
    simp)

lemma qExpansion_D26 : qExpansion 1 D26 = qExpansion 1 E26 - qExpansion 1 H26 :=
  qExpansion_sub26 E26 H26

/-- **The weight-26 Ramanujan congruence**: `a_26 n ≡ σ_25 n [ZMOD 657931]`. -/
theorem a26_modEq_sigma {n : ℕ} (hn : 1 ≤ n) :
    a26 n ≡ (sigma 25 n : ℤ) [ZMOD 657931] := by
  have hsm := f26_isNormalizedRankOne.eq_smul D26
  have hc : (qExpansion 1 D26).coeff 1 = (-24 / 657931 : ℂ) - 696 := by
    rw [qExpansion_D26, map_sub, E26_coeff one_ne_zero, H26_coeff_one,
      show sigma 25 1 = 1 by decide]
    norm_num
  rw [hc] at hsm
  have hcoef :=
    congrArg (fun g : CuspForm 𝒮ℒ ((26 : ℕ) : ℤ) => (qExpansion 1 g).coeff n) hsm
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, smul_eq_mul, f26_coeff, qExpansion_D26, map_sub,
    E26_coeff (by omega)] at hcoef
  obtain ⟨h, hh⟩ := RamanujanCongruence.coeff_mul_intCast
    (RamanujanCongruence.coeff_pow_intCast (fun m => ⟨e4 m, e4_coeff m⟩) 5)
    (fun m => ⟨e6 m, e6_coeff m⟩) n
  rw [qExpansion_H26, hh] at hcoef
  -- clear denominators: `-24 (σ − a) = 657931 (h − 696 a)`
  have hZ : (-24 : ℤ) * ((sigma 25 n : ℤ) - a26 n) = 657931 * (h - 696 * a26 n) := by
    have h' : (((-24 : ℤ) * ((sigma 25 n : ℤ) - a26 n) : ℤ) : ℂ)
        = ((657931 * (h - 696 * a26 n) : ℤ) : ℂ) := by
      push_cast
      linear_combination (657931 : ℂ) * hcoef
    exact_mod_cast h'
  have hdvd : (657931 : ℤ) ∣ (-24 : ℤ) * ((sigma 25 n : ℤ) - a26 n) := ⟨_, hZ⟩
  have hcop : Int.gcd 657931 (-24) = 1 := by norm_num
  exact (Int.modEq_iff_dvd.mpr (Int.dvd_of_dvd_mul_right_of_gcd_one hdvd hcop))

/-! ### The sieve and the initial segment -/

/-- The five fifth roots of unity of `ZMod 657931` exhaust the roots of
`X ^ 5 = 1`: `X⁵ − 1` splits through them (elementary symmetric functions
`0, 0, 0, 0, 1`). -/
lemma eq_of_pow_five {y : ZMod 657931} (hy : y ^ 5 = 1) :
    y = 1 ∨ y = 30567 ∨ y = 47671 ∨ y = 79469 ∨ y = 500223 := by
  have e1 : (1 + 30567 + 47671 + 79469 + 500223 : ZMod 657931) = 0 := by decide
  have e2 : (1 * 30567 + 1 * 47671 + 1 * 79469 + 1 * 500223 + 30567 * 47671 + 30567 * 79469
      + 30567 * 500223 + 47671 * 79469 + 47671 * 500223 + 79469 * 500223 : ZMod 657931) = 0 := by
    decide
  have e3 : (1 * 30567 * 47671 + 1 * 30567 * 79469 + 1 * 30567 * 500223 + 1 * 47671 * 79469
      + 1 * 47671 * 500223 + 1 * 79469 * 500223 + 30567 * 47671 * 79469
      + 30567 * 47671 * 500223 + 30567 * 79469 * 500223 + 47671 * 79469 * 500223 :
        ZMod 657931) = 0 := by
    decide
  have e4' : (1 * 30567 * 47671 * 79469 + 1 * 30567 * 47671 * 500223
      + 1 * 30567 * 79469 * 500223 + 1 * 47671 * 79469 * 500223
      + 30567 * 47671 * 79469 * 500223 : ZMod 657931) = 0 := by
    decide
  have e5 : (1 * 30567 * 47671 * 79469 * 500223 : ZMod 657931) = 1 := by decide
  have : Fact (Nat.Prime 657931) := ⟨by norm_num⟩
  have hprod : (y - 1) * (y - 30567) * (y - 47671) * (y - 79469) * (y - 500223) = 0 := by
    linear_combination hy - y ^ 4 * e1 + y ^ 3 * e2 - y ^ 2 * e3 + y * e4' - e5
  simp only [mul_eq_zero, sub_eq_zero] at hprod
  rcases hprod with (((h | h) | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- `x ^ 25 = −1` in `ZMod 657931` forces `x = −ζ` with `ζ ^ 5 = 1`
(`gcd(25, 657930) = 5`, `25 · 105269 = 5 + 4 · 657930`). -/
lemma neg_pow_five_of_pow25 {x : ZMod 657931} (hx : x ^ 25 = -1) : (-x) ^ 5 = 1 := by
  have : Fact (Nat.Prime 657931) := ⟨by norm_num⟩
  have hy : (-x) ^ 25 = 1 := by rw [neg_pow, hx]; norm_num
  have hy0 : -x ≠ 0 := by
    rintro h
    rw [h, zero_pow (by norm_num)] at hy
    exact zero_ne_one hy
  have h1 : (-x) ^ 657930 = 1 := ZMod.pow_card_sub_one_eq_one hy0
  calc (-x) ^ 5 = (-x) ^ 5 * ((-x) ^ 657930) ^ 4 := by rw [h1, one_pow, mul_one]
    _ = ((-x) ^ 25) ^ 105269 := by rw [← pow_mul, ← pow_mul, ← pow_add]
    _ = 1 := by rw [hy, one_pow]

/-- The five bad residues `657931 − ζ` (`ζ ^ 5 = 1`) modulo 657931. -/
def badRes : Finset ℕ := {657930, 627364, 610260, 578462, 157708}

/-- **The weight-26 sieve**: `a₂₆ p ≠ 0` for every prime `p` whose residue
mod 657931 avoids the five bad classes. -/
theorem a26_prime_ne_zero_of_mod {p : ℕ} (hp : p.Prime) (h : p % 657931 ∉ badRes) :
    a26 p ≠ 0 := by
  intro h0
  have hc := a26_modEq_sigma hp.one_lt.le
  rw [h0] at hc
  have hsig : sigma 25 p = 1 + p ^ 25 := by
    rw [show sigma 25 p = sigma 25 (p ^ 1) from by rw [pow_one],
      sigma_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_one]
    simp
  rw [hsig] at hc
  have hz : ((1 + p ^ 25 : ℕ) : ZMod 657931) = 0 := by
    have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hc
    push_cast at this ⊢
    rw [← this]
  push_cast at hz
  have hroot := eq_of_pow_five (neg_pow_five_of_pow25 (x := (p : ZMod 657931))
    (by linear_combination hz))
  have key : ∀ z : ℕ, (z : ZMod 657931) + (p : ZMod 657931) = 0 → 657931 ∣ z + p := by
    intro z hz'
    have : ((z + p : ℕ) : ZMod 657931) = 0 := by push_cast; exact hz'
    rwa [ZMod.natCast_eq_zero_iff] at this
  simp only [badRes, Finset.mem_insert, Finset.mem_singleton] at h
  rcases hroot with hr | hr | hr | hr | hr
  · have := key 1 (by push_cast; linear_combination -hr); omega
  · have := key 30567 (by push_cast; linear_combination -hr); omega
  · have := key 47671 (by push_cast; linear_combination -hr); omega
  · have := key 79469 (by push_cast; linear_combination -hr); omega
  · have := key 500223 (by push_cast; linear_combination -hr); omega

/-- No prime below 1315861 lies in a bad class: the nine candidates
`r` and `r + 657931` (`r ∈ badRes`, below the bound) are composite. -/
theorem no_bad_prime_lt_1315861 :
    ∀ p : ℕ, p.Prime → p < 1315861 → p % 657931 ∉ badRes := by
  intro p hp hlt hmem
  simp only [badRes, Finset.mem_insert, Finset.mem_singleton] at hmem
  have hp' : p = p % 657931 ∨ p = p % 657931 + 657931 := by omega
  rcases hmem with h | h | h | h | h <;> rw [h] at hp' <;> rcases hp' with rfl | rfl <;>
    first | omega | norm_num at hp

/-- **Lehmer's question in weight 26, all `n < 1315861`**: the coefficients of
`Δ E₄² E₆` satisfy `a₂₆ n ≠ 0` for every `0 < n < 1315861`. -/
theorem a26_ne_zero_of_lt_1315861 {n : ℕ} (hn : 0 < n) (hlt : n < 1315861) : a26 n ≠ 0 :=
  f26_isNormalizedRankOne.ne_zero_of_prime_factors (j := 12) rfl two_pow_not_dvd
    three_pow_not_dvd hn fun p hp hd =>
      a26_prime_ne_zero_of_mod hp
        (no_bad_prime_lt_1315861 p hp (lt_of_le_of_lt (Nat.le_of_dvd hn hd) hlt))

/-- **Unbounded weight-26 nonvanishing**: `a₂₆ n ≠ 0` for every `n ≥ 1` none
of whose prime factors lies in a bad class mod 657931 (any exponents). -/
theorem a26_ne_zero_of_prime_factors_mod {n : ℕ} (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p % 657931 ∉ badRes) : a26 n ≠ 0 :=
  f26_isNormalizedRankOne.ne_zero_of_prime_factors (j := 12) rfl two_pow_not_dvd
    three_pow_not_dvd hn fun p hp hd => a26_prime_ne_zero_of_mod hp (h p hp hd)

end LehmerWeight26
