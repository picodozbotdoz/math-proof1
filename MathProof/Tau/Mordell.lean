import MathProof.ModularForms.HeckeLevelOne
import MathProof.Tau.Bridge

/-!
# Mordell's theorem: multiplicativity of the Ramanujan τ function

For a prime `p`, the Hecke operator `T_p` (file `MathProof/ModularForms/HeckeLevelOne.lean`)
acts on the one-dimensional space `S₁₂(SL(2, ℤ))` of weight-12 cusp forms, so
`T_p Δ = λ_p • Δ` for the modular discriminant `Δ`.  Comparing q-expansion
coefficients (using the Iteration-2 bridge `(qExpansion 1 Δ)_n = τ n`) identifies
`λ_p = τ p` and yields:

* `heckeTP_discriminant_eq` : `T_p Δ = τ p • Δ` (the eigenform equation);
* `hecke_eigen_identity` : `τ (p * m) + p ^ 11 [p ∣ m] τ (m / p) = τ p * τ m`;
* `tau_prime_mul_of_not_dvd` : `τ (p * n) = τ p * τ n` if `p ∤ n`;
* `tau_prime_pow_succ` : `τ (p ^ (r + 2)) = τ p * τ (p ^ (r + 1)) - p ^ 11 * τ (p ^ r)`;
* `tau_prime_pow_mul` : `τ (p ^ a * n) = τ (p ^ a) * τ n` if `p ∤ n`;
* `tau_mul_coprime` : `τ (m * n) = τ m * τ n` for coprime `m, n ≥ 1`
  (**Mordell's theorem**, 1917).

Everything is about `Ramanujan.tau` from `MathProof/Tau/Basic.lean`; the
q-expansion bridge to Mathlib's analytic discriminant is
`Ramanujan.qExpansion_discriminant_coeff_of_ne_zero` (Iteration 2).
-/

open Ramanujan HeckeLevelOne UpperHalfPlane ModularForm CuspForm
open scoped MatrixGroups Manifold Real

namespace Ramanujan

variable {p : ℕ}

local notation "Δc" => (CuspForm.discriminant : CuspForm 𝒮ℒ 12)

/-- The q-expansion of the CuspForm-valued discriminant agrees with that of the
`ModularForm`-valued one (same underlying function; `CuspForm.coe_discriminant`
is `rfl`). -/
private lemma qExpansion_cuspDiscriminant :
    qExpansion 1 (Δc : CuspForm 𝒮ℒ 12) = qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) := rfl

/-- The `n`-th q-expansion coefficient of the CuspForm-valued discriminant is `τ n`
(`n ≥ 1`), via the Iteration-2 bridge. -/
private lemma cuspDiscriminant_coeff (n : ℕ) (hn : n ≠ 0) :
    (qExpansion 1 (Δc : CuspForm 𝒮ℒ 12)).coeff n = ((tau n : ℤ) : ℂ) := by
  rw [qExpansion_cuspDiscriminant]
  exact qExpansion_discriminant_coeff_of_ne_zero hn

/-- The weight-twelve exponent of Mathlib's coefficient formula is written
`(12 - 1 : ℤ)`; as a ℤ-power of a complex number it is the eleventh power. -/
private lemma cpow_sub_one (p : ℕ) : ((p : ℕ) : ℂ) ^ ((12 : ℤ) - 1) = ((p : ℕ) : ℂ) ^ 11 := by
  have h1 : ((12 : ℤ) - 1) = ((11 : ℕ) : ℤ) := rfl
  rw [h1, zpow_natCast]

/-- **The eigenform equation**: `T_p Δ = τ(p) • Δ` in `S₁₂(SL(2, ℤ))`. -/
theorem heckeTP_discriminant_eq (hp : p.Prime) :
    heckeTP hp (Δc : CuspForm 𝒮ℒ 12) = ((tau p : ℤ) : ℂ) • Δc := by
  obtain ⟨lam, hlam⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve (heckeTP hp Δc)
  have hc : (qExpansion 1 (lam • Δc : CuspForm 𝒮ℒ 12)).coeff 1
      = (qExpansion 1 (heckeTP hp Δc)).coeff 1 := by rw [hlam]
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul,
    smul_eq_mul, heckeTP_qExpansion_coeff hp Δc 1,
    cuspDiscriminant_coeff (p * 1) (mul_ne_zero hp.pos.ne' one_ne_zero),
    cuspDiscriminant_coeff 1 one_ne_zero, Nat.mul_one, cpow_sub_one] at hc
  norm_num [tau_one, hp.not_dvd_one] at hc
  rw [← hc]
  exact hlam.symm

/-- **The coefficient identity behind Mordell's theorem**: for every `m ≥ 1`,
`τ (p * m) + p ^ 11 [p ∣ m] τ (m / p) = τ p * τ m`. -/
theorem hecke_eigen_identity (hp : p.Prime) (m : ℕ) (hm : 1 ≤ m) :
    ((tau (p * m) : ℤ) : ℂ) + ((p : ℕ) : ℂ) ^ 11 * (if p ∣ m then ((tau (m / p) : ℤ) : ℂ) else 0)
      = ((tau p : ℤ) : ℂ) * ((tau m : ℤ) : ℂ) := by
  have hc : (qExpansion 1 (((tau p : ℤ) : ℂ) • Δc : CuspForm 𝒮ℒ 12)).coeff m
      = (qExpansion 1 (heckeTP hp Δc)).coeff m := by
    rw [heckeTP_discriminant_eq hp]
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul,
    smul_eq_mul, heckeTP_qExpansion_coeff hp Δc m,
    cuspDiscriminant_coeff m (by omega),
    cuspDiscriminant_coeff (p * m) (mul_ne_zero hp.pos.ne' (by omega)), cpow_sub_one] at hc
  by_cases hpm : p ∣ m
  · have hmp : p ≤ m := Nat.le_of_dvd (by omega) hpm
    have h1mp : 1 ≤ m / p := (Nat.one_le_div_iff hp.pos).mpr hmp
    rw [if_pos hpm, cuspDiscriminant_coeff (m / p) (by omega)] at hc
    rw [if_pos hpm]
    exact hc.symm
  · rw [if_neg hpm, mul_zero, add_zero] at hc
    rw [if_neg hpm, mul_zero, add_zero]
    exact hc.symm

/-- **Mordell**: `τ (p * n) = τ p * τ n` for a prime `p` not dividing `n`. -/
theorem tau_prime_mul_of_not_dvd (hp : p.Prime) {n : ℕ} (hn : ¬ p ∣ n) :
    tau (p * n) = tau p * tau n := by
  have hn1 : 1 ≤ n := by
    cases n with
    | zero => exact absurd (dvd_zero p) hn
    | succ k => omega
  have h := hecke_eigen_identity hp n hn1
  rw [if_neg hn, mul_zero, add_zero] at h
  exact_mod_cast h

/-- **The prime-power recursion**: `τ (p ^ (r+2)) = τ p * τ (p ^ (r+1)) - p ^ 11 * τ (p ^ r)`. -/
theorem tau_prime_pow_succ (hp : p.Prime) (r : ℕ) :
    tau (p ^ (r + 2)) = tau p * tau (p ^ (r + 1)) - p ^ 11 * tau (p ^ r) := by
  have hm : 1 ≤ p ^ (r + 1) := Nat.pow_pos hp.pos
  have h := hecke_eigen_identity hp (p ^ (r + 1)) hm
  have hdiv : p ∣ p ^ (r + 1) := by rw [pow_succ']; exact dvd_mul_right _ _
  have hdivpow : p ^ (r + 1) / p = p ^ r := by
    rw [pow_succ', Nat.mul_div_cancel_left _ hp.pos]
  rw [if_pos hdiv, hdivpow] at h
  have h' : tau (p * p ^ (r + 1)) + p ^ 11 * tau (p ^ r) = tau p * tau (p ^ (r + 1)) := by
    exact_mod_cast h
  rw [show p ^ (r + 2) = p * p ^ (r + 1) from by
    rw [show r + 2 = (r + 1) + 1 from rfl, pow_succ']]
  linarith

/-- **Prime powers are multiplicative against coprime factors**:
`τ (p ^ a * n) = τ (p ^ a) * τ n` when `p ∤ n`. -/
theorem tau_prime_pow_mul (hp : p.Prime) {n : ℕ} (hn : ¬ p ∣ n) (a : ℕ) :
    tau (p ^ a * n) = tau (p ^ a) * tau n := by
  have hn1 : 1 ≤ n := by
    cases n with
    | zero => exact absurd (dvd_zero p) hn
    | succ k => omega
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases a with _ | a
    · rw [pow_zero, one_mul, tau_one, one_mul]
    rcases a with _ | a
    · change tau (p ^ 1 * n) = tau (p ^ 1) * tau n
      rw [pow_one, tau_prime_mul_of_not_dvd hp hn]
    change tau (p ^ (a + 2) * n) = tau (p ^ (a + 2)) * tau n
    have hm : 1 ≤ p ^ (a + 1) * n :=
      Nat.mul_pos (Nat.pow_pos hp.pos) (by omega)
    have h := hecke_eigen_identity hp (p ^ (a + 1) * n) hm
    have hdiv : p ∣ p ^ (a + 1) * n := by
      rw [show p ^ (a + 1) * n = p * (p ^ a * n) from by rw [pow_succ']; ring]
      exact dvd_mul_right _ _
    have hdivpow : p ^ (a + 1) * n / p = p ^ a * n := by
      rw [show p ^ (a + 1) * n = p * (p ^ a * n) from by rw [pow_succ']; ring,
        Nat.mul_div_cancel_left _ hp.pos]
    rw [if_pos hdiv, hdivpow] at h
    have h' : tau (p * (p ^ (a + 1) * n)) + p ^ 11 * tau (p ^ a * n)
        = tau p * tau (p ^ (a + 1) * n) := by
      exact_mod_cast h
    rw [ih (a + 1) (by omega), ih a (by omega)] at h'
    rw [show p ^ (a + 2) * n = p * (p ^ (a + 1) * n) from by
        rw [show a + 2 = (a + 1) + 1 from rfl, pow_succ']; ring,
      tau_prime_pow_succ hp a]
    linear_combination h'

private lemma exists_prime_pow_decomp {q : ℕ} (hq : q.Prime) {m : ℕ} (hm : 0 < m)
    (hdvd : q ∣ m) : ∃ a k, 0 < a ∧ m = q ^ a * k ∧ ¬ q ∣ k := by
  revert hm hdvd
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hdvd
    obtain ⟨k, hk⟩ : ∃ k, m = q * k :=
      ⟨m / q, by rw [Nat.mul_div_cancel' hdvd]⟩
    have hq2 : 2 ≤ q := hq.two_le
    have hkpos : 0 < k := by
      cases k with
      | zero => rw [hk] at hm; simp at hm
      | succ k' => omega
    have hklt : k < m := by
      rw [hk]
      calc k = 1 * k := by ring
        _ < q * k := (Nat.mul_lt_mul_right hkpos).mpr (by omega)
    by_cases hkq : q ∣ k
    · obtain ⟨a, k', ha, hk'e, hk'q⟩ := ih k hklt hkpos hkq
      refine ⟨a + 1, k', by omega, ?_, hk'q⟩
      rw [hk, hk'e, pow_succ]
      ring
    · exact ⟨1, k, by omega, by rw [hk, pow_one], hkq⟩

/-- **Mordell's theorem (1917)**: `τ (m * n) = τ m * τ n` for coprime `m, n ≥ 1`. -/
theorem tau_mul_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 0 < m) (hn : 0 < n) :
    tau (m * n) = tau m * tau n := by
  revert hmn hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hmn hm
    rcases m with _ | m
    · simp at hm
    rcases m with _ | m
    · change tau (1 * n) = tau 1 * tau n
      rw [one_mul, tau_one, one_mul]
    · have hm2 : 2 ≤ m + 1 + 1 := by omega
      obtain ⟨q, hq, hqm⟩ : ∃ q, q.Prime ∧ q ∣ m + 1 + 1 :=
        ⟨(m + 1 + 1).minFac, (m + 1 + 1).minFac_prime (by omega), Nat.minFac_dvd _⟩
      obtain ⟨a, k, ha, hme, hkq⟩ := exists_prime_pow_decomp hq (by omega) hqm
      have hkpos : 0 < k := by
        cases k with
        | zero => rw [hme] at hm; simp at hm
        | succ k' => omega
      have hkn : Nat.Coprime k n := by
        refine hmn.coprime_dvd_left ?_
        rw [hme]
        exact dvd_mul_left _ _
      have hklt : k < m + 1 + 1 := by
        rw [hme]
        calc k = 1 * k := by ring
          _ < q ^ a * k := (Nat.mul_lt_mul_right hkpos).mpr (Nat.one_lt_pow ha.ne' hq.one_lt)
      have hqndvd : ¬ q ∣ n := by
        intro hd
        have hgd : q ∣ Nat.gcd (m + 1 + 1) n := Nat.dvd_gcd hqm hd
        rw [hmn.gcd_eq_one, Nat.dvd_one] at hgd
        exact hq.ne_one hgd
      have hkmn : ¬ q ∣ (k * n) := by
        intro hd
        rcases hq.dvd_mul.mp hd with h | h
        · exact hkq h
        · exact hqndvd h
      have h1 : tau (q ^ a * (k * n)) = tau (q ^ a) * tau (k * n) := tau_prime_pow_mul hq hkmn a
      have h2 : tau (k * n) = tau k * tau n := ih k hklt hkn hkpos
      have h3 : tau (q ^ a * k) = tau (q ^ a) * tau k := tau_prime_pow_mul hq hkq a
      rw [hme, show q ^ a * k * n = q ^ a * (k * n) from by ring, h1, h2, h3]
      ring

/-- Sanity: `τ 6 = τ 2 * τ 3` (`-6048 = -24 * 252`). -/
example : tau 6 = tau 2 * tau 3 := by
  rw [show 6 = 2 * 3 from rfl]
  exact tau_mul_coprime (by decide) (by decide) (by decide)

/-- Sanity: the prime-power recursion at `p = 2`, `r = 0` gives
`τ 4 = τ 2 * τ 2 - 2 ^ 11 = -1472`, matching the kernel-verified `tau_four`. -/
example : tau 4 = tau 2 * tau 2 - 2 ^ 11 := by
  have h0 : tau 4 = tau 2 * tau 2 - 2 ^ 11 * tau 1 := by
    have h := tau_prime_pow_succ (p := 2) Nat.prime_two 0
    rw [show ((0 : ℕ) + 2) = 2 from rfl, show ((0 : ℕ) + 1) = 1 from rfl,
      show (2 : ℕ) ^ 0 = 1 from rfl] at h
    simpa [tau_one] using h
  simpa [tau_one] using h0

end Ramanujan
