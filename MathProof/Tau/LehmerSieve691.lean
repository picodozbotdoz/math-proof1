import MathProof.ModularForms.Congruence691
import MathProof.Tau.LehmerUnbounded
import Mathlib.NumberTheory.LucasLehmer

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

/-- The kernel-decided finite fact: the only residue `x < 691` with
`x ^ 11 ≡ −1 [MOD 691]` is `x = 690`. -/
private theorem bad_residues :
    ∀ x ∈ Finset.range 691, (1 + x ^ 11) % 691 = 0 ↔ x = 690 := by decide +kernel

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

/-- Kernel-decided: the geometric sums `σ₁₁ (2 ^ a) = Σ_{j ≤ a} 2^{11j}` are
nonzero mod 691 for every `a ≤ 64`. -/
private theorem two_pow_sigma_nonzero :
    ∀ a ∈ Finset.range 65, (∑ j ∈ Finset.range (a + 1), (2 : ℕ) ^ (j * 11)) % 691 ≠ 0 := by
  decide +kernel

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

/-- `2147483647 = 2³¹ − 1` is prime, by the Lucas–Lehmer test: the short
verified computation `LucasLehmerTest 31` replaces a trial-division
certificate whose kernel evaluation exceeded the default recursion depth. -/
private theorem prime_2147483647 : Nat.Prime 2147483647 := by
  have ht : LucasLehmerTest 31 := by norm_num
  have h := lucas_lehmer_sufficiency 31 (by norm_num) ht
  have hme : mersenne 31 = 2147483647 := by decide
  rwa [hme] at h

/-- The Mersenne prime `2³¹ − 1`: `τ 2147483647 ≠ 0` (`2147483647 % 691 =
66 ≠ 690`). -/
theorem tau_of_2147483647_ne_zero : tau 2147483647 ≠ 0 :=
  tau_prime_ne_zero_of_mod prime_2147483647 (by norm_num)


/-! ### The root-of-unity classification of bad prime-power classes -/

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩

private lemma natCast_zmod_eq_zero_iff (n : ℕ) :
    ((n : ℕ) : ZMod 691) = 0 ↔ 691 ∣ n := by
  constructor
  · intro h
    have h' : ((n : ℤ) : ZMod 691) = 0 := by exact_mod_cast h
    exact Int.natCast_dvd_natCast.mp (ZMod.intCast_zmod_eq_zero_iff_dvd _ _ |>.mp h')
  · intro hdvd
    have h' : ((n : ℤ) : ZMod 691) = 0 :=
      ZMod.intCast_zmod_eq_zero_iff_dvd _ _ |>.mpr (Int.natCast_dvd_natCast.mpr hdvd)
    exact_mod_cast h'

/-- `σ₁₁` of a prime power as a geometric sum in `ZMod 691`. -/
theorem sigma_prime_pow_zmod {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ((sigma 11 (p ^ (a + 1)) : ℕ) : ZMod 691)
      = ∑ j ∈ Finset.range (a + 2), (((p : ℕ) : ZMod 691) ^ 11) ^ j := by
  have hterm : ∀ j : ℕ, ((p ^ (j * 11) : ℕ) : ZMod 691)
      = (((p : ℕ) : ZMod 691) ^ 11) ^ j := by
    intro j
    push_cast
    rw [Nat.mul_comm j 11, pow_mul]
  rw [ArithmeticFunction.sigma_apply_prime_pow hp, Nat.cast_sum]
  exact Finset.sum_congr rfl fun j _ => hterm j

private lemma geom_sum_mul_sub (g : ZMod 691) (n : ℕ) :
    (g - 1) * ∑ j ∈ Finset.range n, g ^ j = g ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      linear_combination ih

/-- **Root-of-unity criterion**: for a prime `p` with `p ^ 11 ≢ 1 [MOD 691]`,
the prime-power block `p ^ (a+1)` fails the sieve — `691 ∣ σ₁₁ (p ^ (a+1))` —
exactly when `(p ^ 11) ^ (a + 2) ≡ 1 [MOD 691]`, a periodic condition on `a`
(period = the multiplicative order of `p ^ 11` in `(ZMod 691)ˣ`). -/
theorem prime_pow_dvd_sigma_iff {p : ℕ} (hp : p.Prime)
    (hne : (((p : ℕ) : ZMod 691) ^ 11) ≠ 1) (a : ℕ) :
    691 ∣ sigma 11 (p ^ (a + 1))
      ↔ (((p : ℕ) : ZMod 691) ^ 11) ^ (a + 2) = 1 := by
  set g : ZMod 691 := ((p : ℕ) : ZMod 691) ^ 11 with hg
  have hsum : ((sigma 11 (p ^ (a + 1)) : ℕ) : ZMod 691)
      = ∑ j ∈ Finset.range (a + 2), g ^ j := sigma_prime_pow_zmod hp a
  have htele := geom_sum_mul_sub g (a + 2)
  have hne' : g - 1 ≠ 0 := sub_ne_zero_of_ne hne
  constructor
  · intro hdvd
    have hz : ((sigma 11 (p ^ (a + 1)) : ℕ) : ZMod 691) = 0 :=
      (natCast_zmod_eq_zero_iff _).mpr hdvd
    rw [← hsum, hz, mul_zero] at htele
    exact sub_eq_zero.mp htele.symm
  · intro hroot
    rw [hroot, sub_self] at htele
    rcases mul_eq_zero.mp htele with h | h
    · exact absurd h hne'
    · have hzcast : ((sigma 11 (p ^ (a + 1)) : ℕ) : ZMod 691) = 0 := by
        rw [hsum]; exact h
      exact (natCast_zmod_eq_zero_iff (sigma 11 (p ^ (a + 1)))).mp hzcast

end Ramanujan

