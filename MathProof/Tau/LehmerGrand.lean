import MathProof.Tau.LehmerPow32
import MathProof.Tau.LehmerSieve691

/-!
# The grand nonvanishing theorem: chains + sieve fused

One theorem combining every verification route in the stack.  For a prime
power `p ^ a` dividing `n`, nonvanishing of `τ (p ^ a)` is known if either

* **chains** (Iteration 9): `p ≤ 65536` and `p ^ a ≤ 2 ^ 32` — the Mordell
  recursion chains seeded by the packed residues; or
* **sieve** (Iteration 10): `691 ∤ σ₁₁ (p ^ a)` — e.g. every prime
  `p ≢ −1 [MOD 691]` of arbitrary size.

Mordell multiplicativity (`tau_ne_zero_of_prime_pows`, Iteration 8) then
lifts the prime-power blocks to all of `n`.

* `tau_ne_zero_grand` — the fused divisor-indexed statement (unbounded `n`);
* `tau_ne_zero_of_lt_two_pow_32` — **every `n < 2 ^ 32` whose prime factors
  above 65536 avoid the single class `−1 [MOD 691]`** has `τ n ≠ 0`;
* `tau_of_4294967295_ne_zero` — showcase: `τ (2 ^ 32 − 1) ≠ 0`, the largest
  32-bit index (`2 ^ 32 − 1 = 3 · 5 · 17 · 257 · 65537`, Fermat).

Like `LehmerPow32`, this module is heavy (imports the kernel-decide chain
module) and is verified on Modal, not in CI.
-/

open Ramanujan ArithmeticFunction

namespace Ramanujan

/-- **The grand nonvanishing theorem**: `τ n ≠ 0` for every `n ≥ 1` such that
each prime-power divisor `p ^ a` of `n` is covered by the chains
(`p ≤ 65536`, `p ^ a ≤ 2 ^ 32`) or passes the mod-691 sieve
(`691 ∣ σ₁₁ (p ^ a)` fails).  No bound on `n`. -/
theorem tau_ne_zero_grand {n : ℕ} (hn : 0 < n)
    (h : ∀ p a : ℕ, p.Prime → 0 < a → p ^ a ∣ n →
      (p ≤ 65536 ∧ p ^ a ≤ 2 ^ 32) ∨ ¬ 691 ∣ sigma 11 (p ^ a)) : tau n ≠ 0 := by
  refine tau_ne_zero_of_prime_pows hn fun p a hp ha hdvd => ?_
  rcases h p a hp ha hdvd with ⟨h64, hle⟩ | hsieve
  · exact tau_prime_pow_ne_zero_of_le_two_pow_32 hp h64 hle
  · exact tau_ne_zero_of_not_dvd_sigma (Nat.pow_pos hp.pos) hsieve

/-- **All of 32 bits, minus one residue class**: `τ n ≠ 0` for every
`0 < n < 2 ^ 32` whose prime factors `p > 65536` satisfy
`p ≢ −1 [MOD 691]`.  (Prime factors `≤ 65536` are always fine: their prime
powers inside `n` are `< 2 ^ 32`, covered by the chains; a factor
`p > 65536 = 2 ^ 16` appears to the first power only, and is then covered by
the sieve unless `p ≡ −1 [MOD 691]`.) -/
theorem tau_ne_zero_of_lt_two_pow_32 {n : ℕ} (hn : 0 < n) (hlt : n < 2 ^ 32)
    (hbad : ∀ p : ℕ, p.Prime → p ∣ n → 65536 < p → p % 691 ≠ 690) :
    tau n ≠ 0 := by
  refine tau_ne_zero_grand hn fun p a hp ha hdvd => ?_
  have hpale : p ^ a ≤ n := Nat.le_of_dvd hn hdvd
  by_cases h64 : p ≤ 65536
  · exact Or.inl ⟨h64, Nat.le_of_lt (lt_of_le_of_lt hpale hlt)⟩
  · right
    have hgt : 65536 < p := by omega
    have ha1 : a = 1 := by
      by_contra hc
      have h2a : 2 ≤ a := by omega
      have hp65537 : 65537 ≤ p := by omega
      have h1 : (65537 : ℕ) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp65537 2
      have h2 : (2 : ℕ) ^ 32 < (65537 : ℕ) ^ 2 := by norm_num
      have hbig : (2 : ℕ) ^ 32 < p ^ 2 := by omega
      have hp2n : p ^ 2 ≤ p ^ a := Nat.pow_le_pow_right (by omega) h2a
      omega
    subst ha1
    rw [pow_one]
    intro hsigma
    have hpdvd : p ∣ n := dvd_trans (dvd_pow_self p one_ne_zero) hdvd
    exact absurd ((prime_dvd_sigma_iff hp).mp hsigma) (hbad p hp hpdvd hgt)

/-- `τ (2 ^ 32 − 1) ≠ 0`: the largest 32-bit index factors as
`3 · 5 · 17 · 257 · 65537` (Fermat primes), its only factor above 65536 is
65537, and `65537 % 691 = 583 ≠ 690`. -/
theorem tau_of_4294967295_ne_zero : tau 4294967295 ≠ 0 := by
  refine tau_ne_zero_of_lt_two_pow_32 (by norm_num) (by norm_num) ?_
  intro p hp hdvd hgt
  have hfac : 4294967295 = 65537 * 65535 := by norm_num
  have hpdvd : p ∣ 65537 * 65535 := by rw [← hfac]; exact hdvd
  rcases hp.dvd_mul.mp hpdvd with h | h
  · have hpeq : p = 65537 := by
      rcases (by norm_num : (65537 : ℕ).Prime).eq_one_or_self_of_dvd p h with h1 | h2
      · exact absurd h1 hp.ne_one
      · exact h2
    rw [hpeq]; norm_num
  · exact absurd (Nat.le_of_dvd (by norm_num : 0 < 65535) h) (by omega)

end Ramanujan
