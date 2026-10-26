import MathProof.ModularForms.HeckeLevelOne
import MathProof.Tau.LehmerPrimeReduction

/-!
# Mordell and Lehmer for any rank-one level-one cusp space

Iterations 7 and 12 proved Mordell's theorem and Lehmer's prime-power lemma
for `Δ` (weight 12).  Both arguments only use that `S_k(SL(2, ℤ))` is
one-dimensional and that the spanning form is normalized with integer
coefficients.  This file runs them once, for an arbitrary even weight `k`,
so they apply verbatim to the normalized eigenforms `Δ E₄, Δ E₆, Δ E₄²,
Δ E₄ E₆, Δ E₄² E₆` of weights 16, 18, 20, 22, 26 — the remaining level-one
weights where `S_k` is one-dimensional.

Setting (`IsNormalizedRankOne k f a`): `f ∈ S_k(SL(2, ℤ))`, `rank S_k = 1`,
and the q-expansion coefficients of `f` are the integers `a n` (`n ≥ 1`) with
`a 1 = 1`.  Then:

* `heckeTP_eq` — `T_p f = a p • f` (every such `f` is a Hecke eigenform);
* `eigen_identity` — `a (p m) + p ^ (k-1) [p ∣ m] a (m / p) = a p * a m`;
* `prime_pow_succ` — `a (p ^ (r+2)) = a p * a (p ^ (r+1)) − p ^ (k-1) a (p ^ r)`;
* `mul_coprime` — `a (m n) = a m * a n` for coprime `m, n ≥ 1` (Mordell);
* `prime_pow_ne_zero` — `a p ≠ 0 → a (p ^ a) ≠ 0` (Lehmer), for `k ≡ 2 [MOD 4]`
  or `k ≡ 0 [MOD 4]` alike (only the oddness of `k − 1` matters), given the
  two small-prime side conditions `2 ^ (k/2) ∤ a 2`, `3 ^ (k/2) ∤ a 3`;
* `ne_zero_iff_primes` — the generalized Lehmer conjecture for `f` holds iff
  `a p ≠ 0` for every prime `p`.
-/

open UpperHalfPlane ModularForm CuspForm HeckeLevelOne
open scoped MatrixGroups

namespace EigenLevelOne

/-- `f` spans the one-dimensional space `S_k(SL(2, ℤ))` and has integer
q-expansion coefficients `a n` (`n ≥ 1`), normalized by `a 1 = 1`. -/
structure IsNormalizedRankOne (k : ℕ) (f : CuspForm 𝒮ℒ (k : ℤ)) (a : ℕ → ℤ) : Prop where
  rank_one : Module.rank ℂ (CuspForm 𝒮ℒ (k : ℤ)) = 1
  coeff : ∀ n, 1 ≤ n → (qExpansion 1 f).coeff n = ((a n : ℤ) : ℂ)
  one : a 1 = 1
  weight_pos : 1 ≤ k

variable {k : ℕ} {f : CuspForm 𝒮ℒ (k : ℤ)} {a : ℕ → ℤ} {p : ℕ}

namespace IsNormalizedRankOne

variable (hf : IsNormalizedRankOne k f a)
include hf

lemma ne_zero : f ≠ 0 := by
  intro h0
  have h := hf.coeff 1 le_rfl
  rw [h0, hf.one] at h
  simp [qExpansion_zero] at h

private lemma cpow_sub_one (p : ℕ) :
    ((p : ℕ) : ℂ) ^ ((k : ℤ) - 1) = ((p : ℕ) : ℂ) ^ (k - 1) := by
  have h1 : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by have := hf.weight_pos; omega
  rw [h1, zpow_natCast]

/-- Every cusp form of weight `k` is `(its q-coefficient) • f`. -/
theorem eq_smul (g : CuspForm 𝒮ℒ (k : ℤ)) : g = (qExpansion 1 g).coeff 1 • f := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' f hf.ne_zero).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp hf.rank_one) g
  have h1 : (qExpansion 1 (c • f : CuspForm 𝒮ℒ (k : ℤ))).coeff 1 = (qExpansion 1 g).coeff 1 := by
    rw [hc]
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, smul_eq_mul, hf.coeff 1 le_rfl, hf.one] at h1
  rw [← h1, Int.cast_one, mul_one, hc]

/-- **Every normalized generator is a Hecke eigenform**: `T_p f = a p • f`. -/
theorem heckeTP_eq (hp : p.Prime) : heckeTP hp f = ((a p : ℤ) : ℂ) • f := by
  obtain ⟨lam, hlam⟩ := (finrank_eq_one_iff_of_nonzero' f hf.ne_zero).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp hf.rank_one) (heckeTP hp f)
  have hc : (qExpansion 1 (lam • f : CuspForm 𝒮ℒ (k : ℤ))).coeff 1
      = (qExpansion 1 (heckeTP hp f)).coeff 1 := by rw [hlam]
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, smul_eq_mul, heckeTP_qExpansion_coeff hp f 1,
    hf.coeff 1 le_rfl, hf.coeff (p * 1) (by rw [Nat.mul_one]; exact hp.one_lt.le),
    Nat.mul_one, hf.one] at hc
  norm_num [hp.not_dvd_one] at hc
  rw [← hc]
  exact hlam.symm

/-- **The coefficient identity**: `a (p m) + p ^ (k-1) [p ∣ m] a (m / p) = a p * a m`. -/
theorem eigen_identity (hp : p.Prime) (m : ℕ) (hm : 1 ≤ m) :
    a (p * m) + (if p ∣ m then (p : ℤ) ^ (k - 1) * a (m / p) else 0) = a p * a m := by
  have hc : (qExpansion 1 (((a p : ℤ) : ℂ) • f : CuspForm 𝒮ℒ (k : ℤ))).coeff m
      = (qExpansion 1 (heckeTP hp f)).coeff m := by rw [hf.heckeTP_eq hp]
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, smul_eq_mul, heckeTP_qExpansion_coeff hp f m,
    hf.coeff m hm, hf.coeff (p * m) (Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero hp.pos.ne' (by omega))), hf.cpow_sub_one] at hc
  by_cases hpm : p ∣ m
  · have h1mp : 1 ≤ m / p :=
      (Nat.one_le_div_iff hp.pos).mpr (Nat.le_of_dvd (by omega) hpm)
    rw [ite_eq_left hpm, hf.coeff (m / p) h1mp] at hc
    rw [ite_eq_left hpm]
    exact_mod_cast hc.symm
  · rw [ite_eq_right hpm, mul_zero, add_zero] at hc
    rw [ite_eq_right hpm, add_zero]
    exact_mod_cast hc.symm

/-- `a (p n) = a p * a n` for a prime `p ∤ n`. -/
theorem prime_mul_of_not_dvd (hp : p.Prime) {n : ℕ} (hn : ¬ p ∣ n) :
    a (p * n) = a p * a n := by
  have hn1 : 1 ≤ n := by
    rcases n with _ | n
    · exact absurd (dvd_zero p) hn
    · omega
  have h := hf.eigen_identity hp n hn1
  rwa [ite_eq_right hn, add_zero] at h

/-- **The prime-power recursion**. -/
theorem prime_pow_succ (hp : p.Prime) (r : ℕ) :
    a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - (p : ℤ) ^ (k - 1) * a (p ^ r) := by
  have h := hf.eigen_identity hp (p ^ (r + 1)) (Nat.pow_pos hp.pos)
  have hdiv : p ∣ p ^ (r + 1) := dvd_pow_self p (Nat.succ_ne_zero r)
  rw [ite_eq_left hdiv, pow_succ, Nat.mul_div_cancel _ hp.pos, ← pow_succ] at h
  rw [show p ^ (r + 2) = p * p ^ (r + 1) by rw [pow_succ' p (r + 1)]]
  linarith

/-- `a (p ^ e * n) = a (p ^ e) * a n` for a prime `p ∤ n`. -/
theorem prime_pow_mul (hp : p.Prime) {n : ℕ} (hn : ¬ p ∣ n) (e : ℕ) :
    a (p ^ e * n) = a (p ^ e) * a n := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rcases e with _ | e
    · rw [pow_zero, one_mul, hf.one, one_mul]
    rcases e with _ | e
    · rw [pow_one, hf.prime_mul_of_not_dvd hp hn]
    have hn1 : 1 ≤ n := by
      rcases n with _ | n
      · exact absurd (dvd_zero p) hn
      · omega
    have h := hf.eigen_identity hp (p ^ (e + 1) * n) (Nat.mul_pos (Nat.pow_pos hp.pos) hn1)
    have hsplit : p ^ (e + 1) * n = p * (p ^ e * n) := by rw [pow_succ']; ring
    rw [ite_eq_left (by rw [hsplit]; exact dvd_mul_right _ _), hsplit,
      Nat.mul_div_cancel_left _ hp.pos, ← hsplit] at h
    rw [show p ^ (e + 2) * n = p * (p ^ (e + 1) * n) by rw [pow_succ' p (e + 1)]; ring,
      hf.prime_pow_succ hp e]
    rw [ih (e + 1) (by omega), ih e (by omega)] at h
    linear_combination h

/-- **Mordell's theorem for `f`**: `a (m n) = a m * a n` for coprime `m, n ≥ 1`. -/
theorem mul_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 0 < m) :
    a (m * n) = a m * a n := by
  revert hmn hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hmn hm
    rcases Nat.lt_or_ge 1 m with h1 | h1
    · obtain ⟨e, j, he, hme, hjq⟩ :=
        Ramanujan.exists_prime_pow_decomp (Nat.minFac_prime (by omega)) hm (Nat.minFac_dvd m)
      set q := m.minFac
      have hq : q.Prime := Nat.minFac_prime (by omega)
      have hjpos : 0 < j := by
        rcases j with _ | j
        · rw [hme] at hm; simp at hm
        · omega
      have hjn : Nat.Coprime j n := hmn.coprime_dvd_left (by rw [hme]; exact dvd_mul_left _ _)
      have hjlt : j < m := by
        rw [hme]
        calc j = 1 * j := by ring
          _ < q ^ e * j := (Nat.mul_lt_mul_right hjpos).mpr (Nat.one_lt_pow he.ne' hq.one_lt)
      have hqn : ¬ q ∣ n := fun hd => hq.ne_one
        (Nat.dvd_one.mp (hmn.gcd_eq_one ▸ Nat.dvd_gcd (Nat.minFac_dvd m) hd))
      have hqjn : ¬ q ∣ j * n := fun hd => (hq.dvd_mul.mp hd).elim hjq hqn
      rw [hme, show q ^ e * j * n = q ^ e * (j * n) by ring, hf.prime_pow_mul hq hqjn,
        ih j hjlt hjn hjpos, hf.prime_pow_mul hq hjq]
      ring
    · have : m = 1 := by omega
      subst this
      rw [one_mul, hf.one, one_mul]

/-- Nonvanishing from the prime-power blocks. -/
theorem ne_zero_of_prime_pows {n : ℕ} (hn : 0 < n)
    (hpp : ∀ q e : ℕ, q.Prime → 0 < e → q ^ e ∣ n → a (q ^ e) ≠ 0) : a n ≠ 0 := by
  revert hn hpp
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hpp
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · obtain ⟨q, hq, hqdvd⟩ : ∃ q, q.Prime ∧ q ∣ n :=
        ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩
      obtain ⟨e, j, he, hme, hjq⟩ := Ramanujan.exists_prime_pow_decomp hq hn hqdvd
      have hjpos : 0 < j := by
        rcases j with _ | j
        · rw [hme] at hn; simp at hn
        · omega
      have hjlt : j < n := by
        rw [hme]
        calc j = 1 * j := by ring
          _ < q ^ e * j := (Nat.mul_lt_mul_right hjpos).mpr (Nat.one_lt_pow he.ne' hq.one_lt)
      have hjn : j ∣ n := by rw [hme]; exact dvd_mul_left _ _
      have hqn : q ^ e ∣ n := by rw [hme]; exact dvd_mul_right _ _
      rw [hme, hf.prime_pow_mul hq hjq]
      exact mul_ne_zero (hpp _ e hq he hqn)
        (ih j hjlt hjpos fun r e' hr he' hd => hpp r e' hr he' (hd.trans hjn))
    · have : n = 1 := by omega
      subst this
      rw [hf.one]; exact one_ne_zero

/-- **Lehmer's prime-power lemma for `f`** (even weight `k = 2 j + 2`, so the
recursion exponent `k − 1 = 2 j + 1` is odd): `a p ≠ 0 → a (p ^ e) ≠ 0`, given
the side conditions `2 ^ (j+1) ∤ a 2` and `3 ^ (j+1) ∤ a 3` that rule out the
archimedean regime at the primes `2, 3 < 4`. -/
theorem prime_pow_ne_zero {j : ℕ} (hk : k = 2 * j + 2)
    (h2 : ¬ (2 : ℤ) ^ (j + 1) ∣ a 2) (h3 : ¬ (3 : ℤ) ^ (j + 1) ∣ a 3)
    (hp : p.Prime) (ht : a p ≠ 0) (e : ℕ) : a (p ^ e) ≠ 0 := by
  have hK : k - 1 = 2 * j + 1 := by omega
  have h0 : a (p ^ 0) = 1 := by rw [pow_zero, hf.one]
  have h1 : a (p ^ 1) = a p := by rw [pow_one]
  have hrec : ∀ r, a (p ^ (r + 2)) =
      a p * a (p ^ (r + 1)) - (p : ℤ) ^ (2 * j + 1) * a (p ^ r) := fun r => by
    rw [hf.prime_pow_succ hp r, hK]
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hj : (p : ℤ) ^ (j + 1) ∣ a p
  · have hp4 : 4 ≤ p := by
      have h2le := hp.two_le
      by_contra hlt
      interval_cases p
      · exact h2 (by exact_mod_cast hj)
      · exact h3 (by exact_mod_cast hj)
    obtain ⟨c, hc⟩ := hj
    have hc0 : c ≠ 0 := by rintro rfl; exact ht (by simpa using hc)
    have hc1 : 1 ≤ c ^ 2 := by
      have := sq_pos_of_ne_zero hc0
      omega
    have hp4' : (4 : ℤ) ≤ p := by exact_mod_cast hp4
    have hp0 : (0 : ℤ) ≤ (p : ℤ) ^ (2 * j + 1) := by positivity
    have hdom : 4 * (p : ℤ) ^ (2 * j + 1) ≤ a p ^ 2 := by
      rw [hc]
      calc 4 * (p : ℤ) ^ (2 * j + 1) ≤ (p : ℤ) * (p : ℤ) ^ (2 * j + 1) := by nlinarith
        _ = ((p : ℤ) ^ (j + 1)) ^ 2 * 1 := by ring
        _ ≤ ((p : ℤ) ^ (j + 1)) ^ 2 * c ^ 2 := by gcongr
        _ = ((p : ℤ) ^ (j + 1) * c) ^ 2 := by ring
    exact Ramanujan.rec_ne_zero_of_sq_ge (u := fun e => a (p ^ e)) ht hdom h0 h1 hrec e
  · obtain ⟨v, s', hs', hvs⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr ht) p hp.one_lt.ne'
    obtain ⟨s, hs, hts⟩ : ∃ s : ℤ, ¬ (p : ℤ) ∣ s ∧ a p = (p : ℤ) ^ v * s := by
      rcases Int.natAbs_eq (a p) with h | h
      · refine ⟨s', fun hd => hs' (Int.natCast_dvd_natCast.mp hd), ?_⟩
        rw [h, hvs]; push_cast; ring
      · refine ⟨-(s' : ℤ), fun hd => hs' (Int.natCast_dvd_natCast.mp (dvd_neg.mp hd)), ?_⟩
        rw [h, hvs]; push_cast; ring
    have hv : v ≤ j := by
      by_contra hlt
      exact hj (hts ▸ dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _)
    exact Ramanujan.rec_ne_zero_of_valuation (u := fun e => a (p ^ e)) (K := 2 * j + 1)
      hpZ hs (by omega) hts rfl h0 h1 hrec e

/-- Nonvanishing from the prime factors alone. -/
theorem ne_zero_of_prime_factors {j : ℕ} (hk : k = 2 * j + 2)
    (h2 : ¬ (2 : ℤ) ^ (j + 1) ∣ a 2) (h3 : ¬ (3 : ℤ) ^ (j + 1) ∣ a 3) {n : ℕ} (hn : 0 < n)
    (h : ∀ q : ℕ, q.Prime → q ∣ n → a q ≠ 0) : a n ≠ 0 :=
  hf.ne_zero_of_prime_pows hn fun q e hq he hd =>
    hf.prime_pow_ne_zero hk h2 h3 hq (h q hq ((dvd_pow_self q he.ne').trans hd)) e

/-- **The generalized Lehmer conjecture for `f` is a statement about primes**:
`a n ≠ 0` for all `n ≥ 1` iff `a p ≠ 0` for all primes `p`. -/
theorem ne_zero_iff_primes {j : ℕ} (hk : k = 2 * j + 2)
    (h2 : ¬ (2 : ℤ) ^ (j + 1) ∣ a 2) (h3 : ¬ (3 : ℤ) ^ (j + 1) ∣ a 3) :
    (∀ n : ℕ, 1 ≤ n → a n ≠ 0) ↔ ∀ p : ℕ, p.Prime → a p ≠ 0 :=
  ⟨fun h p hp => h p hp.one_lt.le, fun h _n hn =>
    hf.ne_zero_of_prime_factors hk h2 h3 hn fun q hq _ => h q hq⟩

end IsNormalizedRankOne

end EigenLevelOne
