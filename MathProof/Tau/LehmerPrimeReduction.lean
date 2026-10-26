import MathProof.Tau.Lehmer
import MathProof.Tau.LehmerSieve691

/-!
# Lehmer's reduction: the conjecture is a statement about primes

Lehmer (1947) observed that a minimal zero of `τ` must be a *prime*: if
`τ p ≠ 0`, then `τ (p ^ a) ≠ 0` for every exponent `a`.  Together with
Mordell multiplicativity this makes Lehmer's conjecture equivalent to
`τ p ≠ 0` for all primes `p`.

Iterations 8–11 needed nonvanishing at every prime-power block and could only
reach `p ^ a ≤ 2 ^ 32` by kernel-decided recursion chains (~144 GiB).  This
file removes the exponent from the picture entirely.

The proof is elementary and needs no Deligne bound.  Write
`u a = τ (p ^ a)` and `t = τ p`, so `u (a + 2) = t u (a + 1) − p ^ 11 u a`.

* If `p ^ 6 ∤ t`, write `t = p ^ v s` with `v ≤ 5`, `p ∤ s`.  Since
  `11 − 2 v ≥ 1`, the term `t u (a + 1)` dominates `p`-adically:
  `u a = p ^ (a v) w` with `w ≡ s ^ a [ZMOD p]`, so `u a ≠ 0`.
* If `p ^ 6 ∣ t`, then `p ≥ 5` (`τ 2 = −24`, `τ 3 = 252`), hence
  `t ^ 2 ≥ p ^ 12 ≥ 4 p ^ 11`: the sequence is sign-monotone
  (`0 < u a`, `t u a ≤ 2 u (a + 1)` for `t > 0`), so it never vanishes.

Main results:

* `tau_prime_pow_ne_zero` — `τ p ≠ 0 → τ (p ^ a) ≠ 0`;
* `tau_ne_zero_of_prime_factors` — `τ n ≠ 0` once `τ p ≠ 0` for the prime
  factors `p` of `n`;
* `lehmerConjecture_iff_primes` — `LehmerConjecture ↔ ∀ p prime, τ p ≠ 0`;
* `tau_ne_zero_of_prime_factors_mod` — the mod-691 sieve with *no* exponent
  restriction: `τ n ≠ 0` whenever no prime factor of `n` is `≡ −1 [MOD 691]`;
* `tau_ne_zero_of_lt_of_prime_gap` — parametric initial segment: verified
  primes up to `B` plus the absence of primes `≡ −1 [MOD 691]` in `(B, N)`
  give `τ n ≠ 0` for all `0 < n < N`.
-/

namespace Ramanujan

section Recurrence

variable {u : ℕ → ℤ} {t q : ℤ}

/-- The `p`-adically dominant case: if `t = p ^ v s` with `p ∤ s` and
`2 v < K`, a solution of `u (a + 2) = t u (a + 1) − p ^ K u a` with
`u 0 = 1`, `u 1 = t` never vanishes.  (For `τ`, `K = 11`; the weight-`k`
analogue has `K = k − 1`.) -/
theorem rec_ne_zero_of_valuation {p : ℤ} (hp : Prime p) {v K : ℕ} {s : ℤ}
    (hs : ¬ p ∣ s) (hv : 2 * v + 1 ≤ K) (ht : t = p ^ v * s) (hq : q = p ^ K)
    (h0 : u 0 = 1) (h1 : u 1 = t) (hrec : ∀ a, u (a + 2) = t * u (a + 1) - q * u a)
    (a : ℕ) : u a ≠ 0 := by
  set e := K - 2 * v with he
  have he1 : e ≠ 0 := by omega
  have hq' : q = p ^ v * p ^ v * p ^ e := by
    rw [hq, ← pow_add, ← pow_add]
    congr 1
    omega
  have key : ∀ a, (∃ w, u a = p ^ (a * v) * w ∧ w ≡ s ^ a [ZMOD p]) ∧
      (∃ w, u (a + 1) = p ^ ((a + 1) * v) * w ∧ w ≡ s ^ (a + 1) [ZMOD p]) := by
    intro a
    induction a with
    | zero => exact ⟨⟨1, by simp [h0], by simp⟩, ⟨s, by simp [h1, ht], by simp⟩⟩
    | succ a ih =>
      obtain ⟨⟨w0, hw0, _⟩, ⟨w1, hw1, hc1⟩⟩ := ih
      refine ⟨⟨w1, hw1, hc1⟩, ⟨s * w1 - p ^ e * w0, ?_, ?_⟩⟩
      · have hpow : p ^ ((a + 1 + 1) * v) = p ^ (a * v) * p ^ v * p ^ v := by
          rw [← pow_add, ← pow_add]
          congr 1
          ring
        have hpow1 : p ^ ((a + 1) * v) = p ^ (a * v) * p ^ v := by
          rw [← pow_add]
          congr 1
          ring
        rw [hrec, hw1, hw0, ht, hq', hpow, hpow1]
        ring
      · have hz : p ^ e * w0 ≡ 0 [ZMOD p] :=
          Int.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (dvd_pow_self p he1) _)
        have h := (hc1.mul_left s).sub hz
        rw [sub_zero] at h
        rwa [pow_succ' s (a + 1)]
  obtain ⟨w, hw, hc⟩ := (key a).1
  intro h
  rw [hw] at h
  rcases mul_eq_zero.mp h with h | h
  · exact hp.ne_zero (pow_eq_zero_iff'.mp h).1
  · rw [h] at hc
    exact hs (hp.dvd_of_dvd_pow (Int.modEq_zero_iff_dvd.mp hc.symm))

/-- The archimedean case for `t > 0`: if `4 q ≤ t ^ 2`, the solution with
`u 0 = 1`, `u 1 = t` stays positive (`t u a ≤ 2 u (a + 1)`). -/
theorem rec_pos_of_sq_ge (htpos : 0 < t) (hdom : 4 * q ≤ t ^ 2)
    (h0 : u 0 = 1) (h1 : u 1 = t) (hrec : ∀ a, u (a + 2) = t * u (a + 1) - q * u a)
    (a : ℕ) : 0 < u a ∧ t * u a ≤ 2 * u (a + 1) := by
  induction a with
  | zero => exact ⟨by rw [h0]; norm_num, by rw [h0, h1]; linarith⟩
  | succ a ih =>
    obtain ⟨hpos, hstep⟩ := ih
    have hpos1 : 0 < u (a + 1) := by nlinarith
    refine ⟨hpos1, ?_⟩
    rw [hrec a]
    have h2 : t * (t * u a) ≤ t * (2 * u (a + 1)) := mul_le_mul_of_nonneg_left hstep htpos.le
    have h3 : 4 * q * u a ≤ t ^ 2 * u a := mul_le_mul_of_nonneg_right hdom hpos.le
    nlinarith

/-- The archimedean case, either sign: if `t ≠ 0` and `4 q ≤ t ^ 2`, the
solution with `u 0 = 1`, `u 1 = t` never vanishes. -/
theorem rec_ne_zero_of_sq_ge (ht0 : t ≠ 0) (hdom : 4 * q ≤ t ^ 2)
    (h0 : u 0 = 1) (h1 : u 1 = t) (hrec : ∀ a, u (a + 2) = t * u (a + 1) - q * u a)
    (a : ℕ) : u a ≠ 0 := by
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · -- `(-1) ^ a * u a` solves the recurrence with `-t`.
    have h := rec_pos_of_sq_ge (u := fun a => (-1) ^ a * u a) (t := -t) (q := q)
      (by linarith) (by linarith [neg_sq t]) (by simp [h0]) (by simp [h1])
      (fun a => by simp only [hrec a, pow_succ]; ring) a
    intro hz
    simp [hz] at h
  · exact (rec_pos_of_sq_ge hpos hdom h0 h1 hrec a).1.ne'

end Recurrence

/-- **Lehmer's prime-power lemma** (1947): if `τ p ≠ 0` for a prime `p`, then
`τ (p ^ a) ≠ 0` for every exponent `a`.  So a minimal zero of `τ`, if any,
is a prime. -/
theorem tau_prime_pow_ne_zero {p : ℕ} (hp : p.Prime) (ht : tau p ≠ 0) (a : ℕ) :
    tau (p ^ a) ≠ 0 := by
  have h0 : tau (p ^ 0) = 1 := by simp [tau_one]
  have h1 : tau (p ^ 1) = tau p := by rw [pow_one]
  have hrec : ∀ r, tau (p ^ (r + 2)) =
      tau p * tau (p ^ (r + 1)) - (p : ℤ) ^ 11 * tau (p ^ r) := fun r => by
    rw [tau_prime_pow_succ hp r]
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases h6 : (p : ℤ) ^ 6 ∣ tau p
  · -- `p ≥ 5`, so `t ^ 2 ≥ p ^ 12 ≥ 4 p ^ 11`.
    have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      by_contra hlt
      interval_cases p
      · rw [tau_two] at h6; norm_num at h6
      · rw [tau_three] at h6; norm_num at h6
      · exact absurd hp (by norm_num)
    obtain ⟨c, hc⟩ := h6
    have hc0 : c ≠ 0 := by rintro rfl; exact ht (by simpa using hc)
    have hc1 : 1 ≤ c ^ 2 := by
      have := sq_pos_of_ne_zero hc0
      omega
    have hp5' : (5 : ℤ) ≤ p := by exact_mod_cast hp5
    have hp0 : (0 : ℤ) ≤ (p : ℤ) ^ 11 := by positivity
    have hdom : 4 * (p : ℤ) ^ 11 ≤ tau p ^ 2 := by
      rw [hc]
      calc 4 * (p : ℤ) ^ 11 ≤ (p : ℤ) * (p : ℤ) ^ 11 := by nlinarith
        _ = ((p : ℤ) ^ 6) ^ 2 * 1 := by ring
        _ ≤ ((p : ℤ) ^ 6) ^ 2 * c ^ 2 := by gcongr
        _ = ((p : ℤ) ^ 6 * c) ^ 2 := by ring
    exact rec_ne_zero_of_sq_ge (u := fun a => tau (p ^ a)) ht hdom h0 h1 hrec a
  · -- Factor `|τ p| = p ^ v * s'` with `p ∤ s'`; then `v ≤ 5`.
    obtain ⟨v, s', hs', hvs⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr ht) p hp.one_lt.ne'
    obtain ⟨s, hs, hts⟩ : ∃ s : ℤ, ¬ (p : ℤ) ∣ s ∧ tau p = (p : ℤ) ^ v * s := by
      rcases Int.natAbs_eq (tau p) with h | h
      · refine ⟨s', fun hd => hs' (Int.natCast_dvd_natCast.mp hd), ?_⟩
        rw [h, hvs]; push_cast; ring
      · refine ⟨-(s' : ℤ), fun hd => hs' (Int.natCast_dvd_natCast.mp (dvd_neg.mp hd)), ?_⟩
        rw [h, hvs]; push_cast; ring
    have hv : v ≤ 5 := by
      by_contra hlt
      exact h6 (hts ▸ dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _)
    exact rec_ne_zero_of_valuation (u := fun a => tau (p ^ a)) (K := 11) hpZ hs (by omega)
      hts rfl h0 h1 hrec a

/-- **Nonvanishing from the prime factors alone**: `τ n ≠ 0` for `n ≥ 1` as
soon as `τ p ≠ 0` for every prime `p ∣ n` — no condition on exponents. -/
theorem tau_ne_zero_of_prime_factors {n : ℕ} (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → tau p ≠ 0) : tau n ≠ 0 :=
  tau_ne_zero_of_prime_pows hn fun p a hp ha hd =>
    tau_prime_pow_ne_zero hp (h p hp ((dvd_pow_self p ha.ne').trans hd)) a

/-- **Lehmer's conjecture is a statement about primes**:
`τ n ≠ 0` for all `n ≥ 1` iff `τ p ≠ 0` for all primes `p`. -/
theorem lehmerConjecture_iff_primes :
    LehmerConjecture ↔ ∀ p : ℕ, p.Prime → tau p ≠ 0 :=
  ⟨fun h p hp => h p hp.one_lt.le, fun h _n hn =>
    tau_ne_zero_of_prime_factors hn fun p hp _ => h p hp⟩

/-- **The mod-691 sieve, all exponents**: `τ n ≠ 0` for every `n ≥ 1` none of
whose prime factors is `≡ −1 [MOD 691]` — e.g. `τ (65537 ^ a) ≠ 0` for every
`a`.  (Iteration 10 needed `691 ∤ σ₁₁ (p ^ a)` block by block.) -/
theorem tau_ne_zero_of_prime_factors_mod {n : ℕ} (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p % 691 ≠ 690) : tau n ≠ 0 :=
  tau_ne_zero_of_prime_factors hn fun p hp hd => tau_prime_ne_zero_of_mod hp (h p hp hd)

/-- **Verified primes plus the sieve, unbounded**: if `τ p ≠ 0` for all primes
`p ≤ B`, then `τ n ≠ 0` for every `n ≥ 1` whose prime factors are each `≤ B`
or `≢ −1 [MOD 691]`. -/
theorem tau_ne_zero_of_primes_le_or_mod {B : ℕ}
    (hB : ∀ p : ℕ, p.Prime → p ≤ B → tau p ≠ 0) {n : ℕ} (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ B ∨ p % 691 ≠ 690) : tau n ≠ 0 :=
  tau_ne_zero_of_prime_factors hn fun p hp hd =>
    (h p hp hd).elim (hB p hp) (tau_prime_ne_zero_of_mod hp)

/-- **Initial segments from a prime gap**: if `τ p ≠ 0` for all primes `p ≤ B`
and no prime in `(B, N)` is `≡ −1 [MOD 691]`, then `τ n ≠ 0` for every
`0 < n < N`. -/
theorem tau_ne_zero_of_lt_of_prime_gap {B N : ℕ}
    (hB : ∀ p : ℕ, p.Prime → p ≤ B → tau p ≠ 0)
    (hgap : ∀ p : ℕ, p.Prime → B < p → p < N → p % 691 ≠ 690)
    {n : ℕ} (hn : 0 < n) (hlt : n < N) : tau n ≠ 0 :=
  tau_ne_zero_of_primes_le_or_mod hB hn fun p hp hd => by
    by_cases hpB : p ≤ B
    · exact Or.inl hpB
    · exact Or.inr (hgap p hp (by omega) (lt_of_le_of_lt (Nat.le_of_dvd hn hd) hlt))

/-- Showcase: `τ (65537 ^ a) ≠ 0` for **every** exponent `a` (`65537` is the
Fermat prime `2 ^ 16 + 1`, beyond every chain bound). -/
theorem tau_65537_pow_ne_zero (a : ℕ) : tau (65537 ^ a) ≠ 0 :=
  tau_prime_pow_ne_zero (by norm_num) tau_of_65537_ne_zero a

/-- Showcase: `τ (2 ^ a) ≠ 0` for **every** exponent `a` (Iteration 10's
sieve reached `a ≤ 64`, the chains `a ≤ 32`). -/
theorem tau_two_pow_ne_zero (a : ℕ) : tau (2 ^ a) ≠ 0 :=
  tau_prime_pow_ne_zero Nat.prime_two (by rw [tau_two]; norm_num) a

end Ramanujan
