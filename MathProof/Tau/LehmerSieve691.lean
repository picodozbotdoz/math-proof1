import MathProof.ModularForms.Congruence691
import MathProof.Tau.LehmerUnbounded

/-!
# The mod-691 Lehmer sieve — nonvanishing for unbounded primes

Ramanujan's congruence `τ n ≡ σ₁₁ n [ZMOD 691]` (Iteration 2) has an immediate
but far-reaching corollary: **if `691 ∤ σ₁₁ n`, then `τ n ≠ 0`** — a residue
nonvanishing test that needs no magnitude information about `τ` at all.  Since
`σ₁₁` is multiplicative, the test localizes at the prime-power blocks of `n`,
and for a *prime* index it collapses to a single congruence class:

* the only primes that can fail are `p ≡ −1 [MOD 691]` (`p % 691 = 690`);
  **every other prime — of arbitrary size — has `τ p ≠ 0`**
  (`tau_prime_ne_zero_of_mod`).

This is the first unbounded-prime coverage in the stack: Iterations 6/9 are
limited to indices built from primes `≤ 65536`, while this sieve covers, e.g.,
`τ 65537 ≠ 0` (the first prime past the 65536 wall) and
`τ 2147483647 ≠ 0` (the Mersenne prime `2³¹ − 1`) outright.

* `tau_ne_zero_of_not_dvd_sigma` — the sieve: `691 ∤ σ₁₁ n → τ n ≠ 0`;
* `prime_dvd_sigma_iff` — `691 ∣ σ₁₁ p ↔ p ≡ 690 [MOD 691]` for `p` prime;
* `tau_prime_ne_zero_of_mod` — `τ p ≠ 0` for primes `p ≢ 690 [MOD 691]`;
* `tau_ne_zero_of_sigma_prime_pows` — the divisor-indexed form (to be combined
  with `tau_ne_zero_of_prime_pows`);
* `tau_two_pow_ne_zero_sieve` — `τ (2 ^ a) ≠ 0` for all `a ≤ 64`
  (kernel-decided geometric sums; the index `2 ^ 64` is 2³² beyond the
  Iteration-9 chain bound);
* `lehmer_zero_dvd_sigma` — any zero of `τ` must satisfy `691 ∣ σ₁₁ n`:
  a *necessary* condition on Lehmer counterexamples.
-/

open ArithmeticFunction

namespace Ramanujan

/-! ### The sieve -/

/-- **The mod-691 sieve**: `τ n ≠ 0` whenever `691` does not divide `σ₁₁ n`.
No magnitude bound on `τ` is needed — a nonzero residue mod the prime 691
certifies nonvanishing. -/
theorem tau_ne_zero_of_not_dvd_sigma {n : ℕ} (hn : 0 < n)
    (h : ¬ 691 ∣ sigma 11 n) : tau n ≠ 0 := by
  intro h0
  have hcong : (sigma 11 n : ℤ) ≡ 0 [ZMOD 691] := by
    have h2 := RamanujanCongruence.tau_modEq_sigma n (by omega)
    rw [h0] at h2
    exact h2.symm
  exact h (Int.natCast_dvd_natCast.mp (Int.modEq_zero_iff_dvd.mp hcong))

/-- Any zero of `τ` is constrained: `691 ∣ σ₁₁ n` — a necessary condition on
Lehmer counterexamples (the sieve above is exactly the contrapositive). -/
theorem lehmer_zero_dvd_sigma {n : ℕ} (hn : 0 < n) (h0 : tau n = 0) :
    691 ∣ sigma 11 n := by
  by_contra h
  exact tau_ne_zero_of_not_dvd_sigma hn h h0

/-- `σ₁₁ p = 1 + p ^ 11` for a prime `p`. -/
private lemma sigma_prime (hp : p.Prime) : sigma 11 p = 1 + p ^ 11 := by
  rw [show sigma 11 p = sigma 11 (p ^ 1) from by rw [pow_one],
    sigma_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_one]
  simp

set_option maxRecDepth 200000
/-- The kernel-decided finite fact: the only residue `x < 691` with
`x ^ 11 ≡ −1 [MOD 691]` is `x = 690`. -/
private theorem bad_residues :
    ∀ x ∈ Finset.range 691, (1 + x ^ 11) % 691 = 0 ↔ x = 690 := by decide

/-- **The only escape class for primes**: for `p` prime, `691 ∣ σ₁₁ p` holds
exactly for `p ≡ −1 [MOD 691]`. -/
theorem prime_dvd_sigma_iff (hp : p.Prime) :
    691 ∣ sigma 11 p ↔ p % 691 = 690 := by
  rw [sigma_prime hp]
  constructor
  · intro hdvd
    have hz : (1 + p ^ 11) % 691 = 0 := by
      simpa [Nat.dvd_iff_mod_eq_zero] using hdvd
    have h11 : p ^ 11 % 691 = (p % 691) ^ 11 % 691 := Nat.pow_mod p 11 691
    rw [Nat.add_mod, h11] at hz
    norm_num at hz
    have hxlt : p % 691 < 691 := Nat.mod_lt _ (by norm_num)
    exact (bad_residues (p % 691) (Finset.mem_range.mpr hxlt)).mp hz
  · intro hmod
    have h11 : p ^ 11 % 691 = 690 := by
      rw [Nat.pow_mod, hmod]
    have hz : (1 + p ^ 11) % 691 = 0 := by
      rw [Nat.add_mod, h11]
    simpa [Nat.dvd_iff_mod_eq_zero] using hz

/-- **Unbounded prime coverage**: every prime `p ≢ 690 [MOD 691]` — of
arbitrary size — satisfies `τ p ≠ 0`. -/
theorem tau_prime_ne_zero_of_mod {p : ℕ} (hp : p.Prime) (h : p % 691 ≠ 690) :
    tau p ≠ 0 :=
  tau_ne_zero_of_not_dvd_sigma hp.pos fun hdvd => h ((prime_dvd_sigma_iff hp).mp hdvd)

/-- The divisor-indexed sieve: `τ n ≠ 0` if no prime-power divisor `p ^ a` of
`n` has `691 ∣ σ₁₁ (p ^ a)` (combine with `tau_ne_zero_of_prime_pows`; by
multiplicativity of `σ₁₁` the test need only be run on the prime-power
blocks). -/
theorem tau_ne_zero_of_sigma_prime_pows {n : ℕ} (hn : 0 < n)
    (h : ∀ p a : ℕ, p.Prime → 0 < a → p ^ a ∣ n → ¬ 691 ∣ sigma 11 (p ^ a)) :
    tau n ≠ 0 :=
  tau_ne_zero_of_prime_pows hn fun p a hp ha hdvd =>
    tau_ne_zero_of_not_dvd_sigma (Nat.pow_pos hp.pos) (h p a hp ha hdvd)

/-! ### Showcase: powers of two past 2³², and primes past the wall -/

set_option maxRecDepth 400000
set_option exponentiation.threshold 4096
/-- Kernel-decided: the geometric sums `σ₁₁ (2 ^ a) = Σ_{j ≤ a} 2^{11j}` are
nonzero mod 691 for every `a ≤ 64`. -/
private theorem two_pow_sigma_nonzero :
    ∀ a ∈ Finset.range 65, (∑ j ∈ Finset.range (a + 1), (2 : ℕ) ^ (j * 11)) % 691 ≠ 0 := by
  decide

/-- **Powers of two to `2 ^ 64`**: `τ (2 ^ a) ≠ 0` for every `a ≤ 64` — the
index `2 ^ 64` is `2 ^ 32` beyond the Iteration-9 chain bound, and the prime
`2` has no escape class here (`2 % 691 ≠ 690`). -/
theorem tau_two_pow_ne_zero_sieve {a : ℕ} (ha : a ≤ 64) :
    tau (2 ^ a) ≠ 0 := by
  refine tau_ne_zero_of_not_dvd_sigma (Nat.pow_pos (by norm_num)) ?_
  intro hdvd
  have hsum : sigma 11 (2 ^ a) = ∑ j ∈ Finset.range (a + 1), (2 : ℕ) ^ (j * 11) :=
    sigma_apply_prime_pow Nat.prime_two
  rw [hsum, Nat.dvd_iff_mod_eq_zero] at hdvd
  exact two_pow_sigma_nonzero a (Finset.mem_range.mpr (by omega)) hdvd

/-- The first prime past the 65536 wall: `τ 65537 ≠ 0` (65537 is prime and
`65537 % 691 = 583 ≠ 690`). -/
theorem tau_of_65537_ne_zero : tau 65537 ≠ 0 :=
  tau_prime_ne_zero_of_mod (by norm_num) (by norm_num)

set_option maxRecDepth 200000
/-- The Mersenne prime `2³¹ − 1`: `τ 2147483647 ≠ 0` (`2147483647 % 691 =
66 ≠ 690`). -/
theorem tau_of_2147483647_ne_zero : tau 2147483647 ≠ 0 :=
  tau_prime_ne_zero_of_mod (by norm_num) (by norm_num)

end Ramanujan
