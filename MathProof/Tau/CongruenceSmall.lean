import MathProof.Tau.Basic
import Mathlib.Algebra.CharP.Frobenius

/-!
# Congruence restrictions on `τ` modulo 2 and 3

The Ramanujan congruence `τ n ≡ σ₁₁ n [ZMOD 691]` (see
`MathProof/ModularForms/Congruence691.lean`) describes `τ` modulo the largest
prime for which a divisor-sum comparison holds.  Modulo the *small* primes the
structure is different and, in one direction, elementary: the defining product
`Δ = q ∏ (1 - q ^ m) ^ 24` collapses by the freshman's dream, because 24 is a
power of 2 times 3 and a power of 3 times 8:

* modulo 2: `(1 - T) ^ 24 = ((1 - T) ^ 8) ^ 3 = (1 - T ^ 8) ^ 3` in
  characteristic 2, so `Δ` reduces to a power series in `q ^ 8`;
* modulo 3: `(1 - T) ^ 24 = ((1 - T) ^ 3) ^ 8 = (1 - T ^ 3) ^ 8` in
  characteristic 3, so `Δ` reduces to a power series in `q ^ 3`.

Consequently (classical congruences going back to Ramanujan):

* `Ramanujan.tau_even_of_ne_one_mod_eight` : `τ n` is **even** unless `n ≡ 1 [MOD 8]`;
* `Ramanujan.tau_zero_mod_three_of_ne_one_mod_three` : `3 ∣ τ n` unless `n ≡ 1 [MOD 3]`;
* `Ramanujan.tau_div_two_and_three_of` : both divisibilities at once (hence
  `6 ∣ τ n` when `n ≢ 1` modulo both 8 and 3, since 2 and 3 are coprime).

The full characterization "`τ n` is odd ⟺ `n` is an odd square" additionally
requires Jacobi's identity `∏ (1 - q ^ m) ^ 3 = ∑ (-1)^k (2k+1) q ^ (k(k+1)/2)`
and remains open here; the mod-2 reduction above is the first half of that
story.

## Tags

Ramanujan tau function, congruences, freshman's dream, Frobenius
-/

namespace Ramanujan

open Polynomial

/-! ### Freshman's dream via the Frobenius homomorphism -/

/-- In characteristic 2, `(1 - Y) ^ 8 = 1 - Y ^ 8` (three iterated Frobenius
squarings). -/
private theorem one_sub_pow_eight {R : Type*} [CommRing R] [ExpChar R 2] (Y : R) :
    (1 - Y) ^ 8 = 1 - Y ^ 8 := by
  rw [show (8 : ℕ) = 2 ^ 3 from rfl, ← iterateFrobenius_def, map_sub,
    iterateFrobenius_def, iterateFrobenius_def, one_pow]

/-- In characteristic 3, `(1 - Y) ^ 3 = 1 - Y ^ 3` (one Frobenius cubing). -/
private theorem one_sub_pow_three {R : Type*} [CommRing R] [ExpChar R 3] (Y : R) :
    (1 - Y) ^ 3 = 1 - Y ^ 3 := by
  rw [show (3 : ℕ) = 3 ^ 1 from rfl, ← iterateFrobenius_def, map_sub,
    iterateFrobenius_def, iterateFrobenius_def, one_pow]

/-! ### Support: powers of `(1 - X ^ c)` and their products have no
coefficients at indices not divisible by `c` -/

/-- Coefficients of `(1 - X ^ (c * s)) ^ r` vanish at indices not divisible by
`c` (in fact off the multiples of `c * s`). -/
private theorem coeff_one_sub_X_pow_eq_zero {R : Type*} [CommRing R] {c s : ℕ}
    (hcs : 0 < c * s) (r b : ℕ) (hb : b % c ≠ 0) :
    ((1 - X ^ (c * s) : R[X]) ^ r).coeff b = 0 := by
  induction r generalizing b with
  | zero =>
      have hb0 : b ≠ 0 := fun h ↦ hb (by rw [h]; exact Nat.zero_mod c)
      simp [pow_zero, coeff_one, hb0]
  | succ r ih =>
      have hcoeff : ∀ k : ℕ, ((1 - X ^ (c * s) : R[X])).coeff k
          = if k = 0 then 1 else if k = c * s then -1 else 0 := by
        intro k
        rw [coeff_sub, coeff_one, coeff_X_pow]
        by_cases h0 : k = 0
        · subst h0
          rw [if_pos rfl, if_neg hcs.ne, if_pos rfl]
          ring
        · rw [if_neg h0, if_neg h0]
          by_cases hs : k = c * s
          · rw [if_pos hs, if_pos hs]
            ring
          · rw [if_neg hs, if_neg hs]
            ring
      rw [pow_succ, coeff_mul]
      refine Finset.sum_eq_zero fun x hx ↦ ?_
      obtain ⟨a, b'⟩ := x
      have hab : a + b' = b := Finset.mem_antidiagonal.mp hx
      dsimp only
      rcases Nat.eq_zero_or_pos b' with hb' | hb'
      · subst hb'
        rw [hcoeff, if_pos rfl, mul_one]
        rw [Nat.add_zero] at hab
        rw [hab]
        exact ih _ hb
      · by_cases hs : b' = c * s
        · rw [hcoeff, if_neg hb'.ne', if_pos hs, mul_neg_one, neg_eq_zero]
          refine ih _ ?_
          have key : b % c = a % c := by
            rw [← hab, hs, Nat.add_mul_mod_self_left]
          rw [key] at hb
          exact hb
        · rw [hcoeff, if_neg hb'.ne', if_neg hs, mul_zero]

/-- A product of powers `(1 - X ^ (c * (m + s))) ^ r` has no coefficients at
indices not divisible by `c`. -/
private theorem coeff_prod_one_sub_pow_eq_zero {R : Type*} [CommRing R] {c s : ℕ}
    (hc : 0 < c) (hs : 0 < s) (r : ℕ) :
    ∀ (N i : ℕ) (hi : i % c ≠ 0),
      (∏ m ∈ Finset.range N, (1 - X ^ (c * (m + s)) : R[X]) ^ r).coeff i = 0 := by
  intro N
  induction N with
  | zero =>
      intro i hi
      have hi0 : i ≠ 0 := fun h ↦ hi (by rw [h]; exact Nat.zero_mod c)
      rw [Finset.prod_range_zero, Polynomial.coeff_one, if_neg hi0]
  | succ N ih =>
      intro i hi
      rw [Finset.prod_range_succ, coeff_mul]
      refine Finset.sum_eq_zero fun x hx ↦ ?_
      obtain ⟨a, b⟩ := x
      have hab : a + b = i := Finset.mem_antidiagonal.mp hx
      dsimp only
      by_cases ha : a % c = 0
      · have hbc : b % c ≠ 0 := by
          intro h0
          rw [← hab, Nat.add_mod, ha, h0] at hi
          simp at hi
        rw [coeff_one_sub_X_pow_eq_zero (Nat.mul_pos hc (by omega)) r b hbc, mul_zero]
      · rw [ih a ha, zero_mul]

/-! ### Reduction of `Δ` modulo 2 and 3 -/

/-- The truncated Euler product maps factor by factor into any coefficient
ring. -/
private theorem map_etaPoly {S : Type*} [CommRing S] (φ : ℤ →+* S) (N : ℕ) :
    Polynomial.map φ (etaPoly N) = ∏ m ∈ Finset.range N, (1 - X ^ (m + 1) : S[X]) := by
  induction N with
  | zero => simp [etaPoly]
  | succ N ih =>
      rw [etaPoly_succ, Polynomial.map_mul, ih, Finset.prod_range_succ,
        Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow,
        Polynomial.map_X]

/-- Modulo 2, the truncated Euler product `(∏_{m=1}^{N} (1 - X ^ m)) ^ 24`
becomes `∏ (1 - X ^ (8m)) ^ 3`. -/
private theorem map_etaPow24_mod_two (N : ℕ) :
    Polynomial.map (Int.castRingHom (ZMod 2)) ((etaPoly N) ^ 24)
      = ∏ m ∈ Finset.range N, (1 - X ^ (8 * (m + 1)) : (ZMod 2)[X]) ^ 3 := by
  rw [Polynomial.map_pow, map_etaPoly, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun m _ ↦ ?_
  have hY : ((X ^ (m + 1) : (ZMod 2)[X])) ^ 8 = X ^ (8 * (m + 1)) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [show (24 : ℕ) = 8 * 3 from rfl,
    pow_mul (1 - X ^ (m + 1) : (ZMod 2)[X]) 8 3, one_sub_pow_eight, hY]

/-- Modulo 3, the truncated Euler product `(∏_{m=1}^{N} (1 - X ^ m)) ^ 24`
becomes `∏ (1 - X ^ (3m)) ^ 8`. -/
private theorem map_etaPow24_mod_three (N : ℕ) :
    Polynomial.map (Int.castRingHom (ZMod 3)) ((etaPoly N) ^ 24)
      = ∏ m ∈ Finset.range N, (1 - X ^ (3 * (m + 1)) : (ZMod 3)[X]) ^ 8 := by
  rw [Polynomial.map_pow, map_etaPoly, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun m _ ↦ ?_
  have hY : ((X ^ (m + 1) : (ZMod 3)[X])) ^ 3 = X ^ (3 * (m + 1)) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [show (24 : ℕ) = 3 * 8 from rfl,
    pow_mul (1 - X ^ (m + 1) : (ZMod 3)[X]) 3 8, one_sub_pow_three, hY]

/-- Transport step shared by both congruences: if the reduction of the
coefficient of `(etaPoly ((n-1)+1)) ^ 24` at index `n - 1` is a product of
powers `(1 - X ^ (c * (m + 1))) ^ r` over `ZMod p`, then `p ∣ τ n` whenever
`(n - 1) % c ≠ 0`. -/
private theorem tau_dvd_of_coeff_map_eq_zero (p : ℕ) {n : ℕ} (h1 : 1 ≤ n) {c r : ℕ}
    (hmap : ∀ N : ℕ, Polynomial.map (Int.castRingHom (ZMod p)) ((etaPoly N) ^ 24)
      = ∏ m ∈ Finset.range N, (1 - X ^ (c * (m + 1)) : (ZMod p)[X]) ^ r)
    (hc : 0 < c) (hi : (n - 1) % c ≠ 0) : (p : ℤ) ∣ tau n := by
  have hτ : tau n = ((etaPoly ((n - 1) + 1)) ^ 24).coeff (n - 1) := rfl
  have hcm : (((((etaPoly ((n - 1) + 1)) ^ 24).coeff (n - 1) : ℤ)) : ZMod p)
      = (Polynomial.map (Int.castRingHom (ZMod p))
          ((etaPoly ((n - 1) + 1)) ^ 24)).coeff (n - 1) := by
    rw [Polynomial.coeff_map]
    rfl
  have hz : (((tau n : ℤ) : ZMod p)) = 0 := by
    rw [hτ, hcm, hmap ((n - 1) + 1)]
    exact coeff_prod_one_sub_pow_eq_zero hc (by decide) r ((n - 1) + 1)
      (n - 1) hi
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz

/-! ### The congruences -/

/-- **`τ n` is even unless `n ≡ 1 [MOD 8]`.**  The coefficient of `q ^ n` in
`Δ = q ∏ (1 - q ^ m) ^ 24` reduced mod 2 lives in a power series in `q ^ 8`. -/
theorem tau_even_of_ne_one_mod_eight {n : ℕ} (h1 : 1 ≤ n) (h : n % 8 ≠ 1) :
    tau n % 2 = 0 := by
  have h2 : (2 : ℤ) ∣ tau n :=
    tau_dvd_of_coeff_map_eq_zero 2 h1 map_etaPow24_mod_two (by decide) (by omega)
  have hmod : tau n % (2 : ℤ) = 0 % (2 : ℤ) := Int.modEq_zero_iff_dvd.mpr h2
  simpa using hmod

/-- **`3 ∣ τ n` unless `n ≡ 1 [MOD 3]`.**  The coefficient of `q ^ n` in `Δ`
reduced mod 3 lives in a power series in `q ^ 3`. -/
theorem tau_zero_mod_three_of_ne_one_mod_three {n : ℕ} (h1 : 1 ≤ n) (h : n % 3 ≠ 1) :
    tau n % 3 = 0 := by
  have h3 : (3 : ℤ) ∣ tau n :=
    tau_dvd_of_coeff_map_eq_zero 3 h1 map_etaPow24_mod_three (by decide) (by omega)
  have hmod : tau n % (3 : ℤ) = 0 % (3 : ℤ) := Int.modEq_zero_iff_dvd.mpr h3
  simpa using hmod

/-- Both small-prime congruences at once: whenever `n ≢ 1 [MOD 8]` and
`n ≢ 1 [MOD 3]`, `τ n` is divisible by 2 and by 3, hence by 6 (2 and 3 are
coprime). -/
theorem tau_div_two_and_three_of {n : ℕ} (h1 : 1 ≤ n) (h8 : n % 8 ≠ 1) (h3 : n % 3 ≠ 1) :
    tau n % 2 = 0 ∧ tau n % 3 = 0 :=
  ⟨tau_even_of_ne_one_mod_eight h1 h8,
    tau_zero_mod_three_of_ne_one_mod_three h1 h3⟩

end Ramanujan
