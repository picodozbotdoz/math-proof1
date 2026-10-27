import MathProof.Tau.LehmerPacked
import MathProof.Tau.LehmerPrimeReduction

/-!
# Lehmer nonvanishing from the prime data alone

Lehmer's prime-power lemma (`MathProof/Tau/LehmerPrimeReduction.lean`)
turns the Iteration-6 prime data `τ p ≠ 0` for `p ≤ 65536`
(`tau_prime_ne_zero_of_le_65536`) and the mod-691 sieve into statements with
**no exponent restriction** — superseding the Iteration-9/11 chains
(`p ^ a ≤ 2 ^ 32`, ~144 GiB) at less than half the kernel cost: this module
only needs the packed decide (~63 GiB).

* `tau_ne_zero_of_prime_factors_le_65536_or_mod` — `τ n ≠ 0` for every
  `n ≥ 1` whose prime factors are each `≤ 65536` or `≢ −1 [MOD 691]`
  (unbounded `n`, arbitrary exponents);
* `tau_ne_zero_of_lt_70481` — **`τ n ≠ 0` for every `0 < n < 70481`**, an
  unconditional initial segment past the dense 65536 bound: `70481` is the
  least prime above 65536 with `p ≡ −1 [MOD 691]` (the candidates
  `65644, 66335, …, 69790` in that class are composite).

Heavy (imports `LehmerPacked`): verified on Modal, not in CI.
-/

namespace Ramanujan

/-- **Unbounded nonvanishing, any exponents**: `τ n ≠ 0` for every `n ≥ 1`
each of whose prime factors is `≤ 65536` or `≢ −1 [MOD 691]`. -/
theorem tau_ne_zero_of_prime_factors_le_65536_or_mod {n : ℕ} (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ 65536 ∨ p % 691 ≠ 690) : tau n ≠ 0 :=
  tau_ne_zero_of_primes_le_or_mod (fun _ hp hle => tau_prime_ne_zero_of_le_65536 hp hle) hn h

/-- No prime in `(65536, 70481)` is `≡ −1 [MOD 691]`: the seven candidates
`691 k + 690` (`94 ≤ k ≤ 100`) are composite. -/
theorem prime_gap_691_65536_70481 :
    ∀ p : ℕ, p.Prime → 65536 < p → p < 70481 → p % 691 ≠ 690 := by
  intro p hp h1 h2 hmod
  obtain ⟨k, rfl⟩ : ∃ k, p = 691 * k + 690 := ⟨p / 691, by omega⟩
  have hk1 : 94 ≤ k := by omega
  have hk2 : k ≤ 100 := by omega
  interval_cases k <;> norm_num at hp

/-- **All indices below 70481**: `τ n ≠ 0` for every `0 < n < 70481`.
Beyond the dense kernel bound 65536, every prime factor of such `n` is either
`≤ 65536` (Iteration 6) or sieved by 691 (no prime `≡ −1 [MOD 691]` lies in
`(65536, 70481)`), and Lehmer's lemma handles every exponent. -/
theorem tau_ne_zero_of_lt_70481 {n : ℕ} (hn : 0 < n) (hlt : n < 70481) : tau n ≠ 0 :=
  tau_ne_zero_of_lt_of_prime_gap (fun _ hp hle => tau_prime_ne_zero_of_le_65536 hp hle)
    prime_gap_691_65536_70481 hn hlt

end Ramanujan

#print axioms Ramanujan.tau_ne_zero_of_lt_70481
#print axioms Ramanujan.tau_ne_zero_of_prime_factors_le_65536_or_mod
