import MathProof.Tau.Mordell

/-!
# Lehmer's conjecture on an unbounded index set

Iteration 6 kernel-verified `τ n ≠ 0` for `1 ≤ n ≤ 65536` and stopped there:
the packed-bignum slot base saturates, and the kernel decides cost ~63 GiB of
heap already.  Mordell's theorem (Iteration 7) breaks that ceiling:
nonvanishing of `τ` is multiplicative over coprime factors, so a *finite* set
of verified values certifies nonvanishing on the whole multiplicative
semigroup those values generate — an *infinite, unbounded* family of indices.

The parametric theorem here is light (no kernel decides): pair it with any
nonvanishing bound `B` from any verification route.  The instantiation at
`B = 65536` (which imports the heavy Iteration-6 module) lives in
`MathProof/Tau/LehmerPrimePower.lean`.

* `tau_ne_zero_of_forall_prime_pow` : if `τ m ≠ 0` is known for every
  `1 ≤ m ≤ B`, then `τ n ≠ 0` for every `n ≥ 1` all of whose prime-power
  divisors `p ^ a` satisfy `p ^ a ≤ B`.
-/

open Ramanujan

namespace Ramanujan

/-- **Nonvanishing from prime-power data**: if `τ (p ^ a) ≠ 0` for every
prime-power divisor `p ^ a` of `n` (`p` prime, `a ≥ 1`), then `τ n ≠ 0`.
This is the primitive behind `tau_ne_zero_of_forall_prime_pow`: by Mordell,
nonvanishing only has to be established at the prime-power indices. -/
theorem tau_ne_zero_of_prime_pows {n : ℕ} (hn : 0 < n)
    (hpp : ∀ p a : ℕ, p.Prime → 0 < a → p ^ a ∣ n → tau (p ^ a) ≠ 0) : tau n ≠ 0 := by
  revert hn hpp
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hpp
    rcases n with _ | n
    · simp at hn
    rcases n with _ | n
    · change tau 1 ≠ 0
      simp [tau_one]
    · obtain ⟨q, hq, hqm⟩ : ∃ q, q.Prime ∧ q ∣ n + 1 + 1 :=
        ⟨(n + 1 + 1).minFac, (n + 1 + 1).minFac_prime (by omega), Nat.minFac_dvd _⟩
      obtain ⟨a, k, ha, hme, hkq⟩ := exists_prime_pow_decomp hq (by omega) hqm
      have hkpos : 0 < k := by
        cases k with
        | zero => rw [hme] at hn; simp at hn
        | succ k' => omega
      have hkdvdm : k ∣ n + 1 + 1 := by rw [hme]; exact dvd_mul_left _ _
      have hqpa : q ^ a ∣ n + 1 + 1 := by rw [hme]; exact dvd_mul_right _ _
      have hklt : k < n + 1 + 1 := by
        rw [hme]
        calc k = 1 * k := by ring
          _ < q ^ a * k := (Nat.mul_lt_mul_right hkpos).mpr (Nat.one_lt_pow ha.ne' hq.one_lt)
      have hppk : ∀ p a : ℕ, p.Prime → 0 < a → p ^ a ∣ k → tau (p ^ a) ≠ 0 :=
        fun p a hp ha hd => hpp p a hp ha (hd.trans hkdvdm)
      have h1 : tau (n + 1 + 1) = tau (q ^ a) * tau k := by
        rw [hme]
        exact tau_prime_pow_mul hq hkq a
      have h2 : tau k ≠ 0 := ih k hklt hkpos hppk
      have h3 : tau (q ^ a) ≠ 0 := hpp q a hq ha hqpa
      rw [h1]
      exact mul_ne_zero h3 h2

/-- **Lehmer nonvanishing on an unbounded index set**: given nonvanishing of
`τ` on `{1, …, B}` (by any route — e.g. Iteration 6's kernel decides at
`B = 65536`), every `n ≥ 1` whose every prime-power divisor `p ^ a`
(`p` prime, `a ≥ 1`) is at most `B` satisfies `τ n ≠ 0`.  Such `n` can be
arbitrarily large — e.g. any squarefree product of primes `≤ B` — so a
finite verification yields an infinite family: at `B = 65536` the largest
squarefree index covered, the primorial `∏_{p ≤ 65536} p` over the 6542
primes up to 65536, has 28 305 decimal digits. -/
theorem tau_ne_zero_of_forall_prime_pow {B : ℕ}
    (hB : ∀ m : ℕ, 1 ≤ m → m ≤ B → tau m ≠ 0) {n : ℕ} (hn : 0 < n)
    (hmax : ∀ p a : ℕ, p.Prime → 0 < a → p ^ a ∣ n → p ^ a ≤ B) : tau n ≠ 0 :=
  tau_ne_zero_of_prime_pows hn fun p a hp ha hdvd =>
    hB (p ^ a) (Nat.pow_pos hp.pos) (hmax p a hp ha hdvd)

end Ramanujan
