import MathProof.Tau.LehmerPacked
import MathProof.Tau.PowChain
import MathProof.Tau.LehmerUnbounded

/-!
# Lehmer nonvanishing for prime powers to 2³² — the recursion chains

The dense kernel-verified bound of Iteration 6 stops at 65536 (packed-slot
saturation, ~63 GiB kernel heap).  Iteration 8 (Mordell multiplicativity)
made the *composites* free; this module makes the *prime powers* free:

`tau_prime_pow_succ` (Iteration 7) turns `τ (p ^ a)` into a two-term linear
recurrence over `ZMod P` (`P = 999999937`), seeded by the packed residues
`τ p mod P` of Iteration 6 (`LehmerPacked.tauResList`).  One kernel decide
walks all 65 535 chains of 32 steps each (~2.1 M small `ZMod` operations,
~200 s of kernel time on top of the packed-list evaluation) and thereby
certifies:

* `tau_prime_pow_ne_zero_of_le_two_pow_32` : `τ (p ^ a) ≠ 0` for every prime
  `p ≤ 65536` and `p ^ a ≤ 2 ^ 32`;
* `tau_ne_zero_of_prime_pow_le_two_pow_32` : `τ n ≠ 0` for every `n ≥ 1` all
  of whose prime-power divisors `p ^ a` have `p ≤ 65536` and `p ^ a ≤ 2 ^ 32`
  — in particular every 65536-smooth `n` up to `2 ^ 32` (e.g. all powers of
  two to `2 ^ 32`), and, combined with the coprime products of Iteration 8,
  every product of such prime-power blocks.

Like `LehmerPacked`, this module is **not** in the default/CI targets — it
imports the heavy kernel-decide module and adds one of its own — and is
verified on Modal (`LEAN_CHECK_MEMORY_MIB=98304 modal run lean_check.py
--target MathProof.Tau.LehmerPow32`).
-/

open Ramanujan

namespace Ramanujan

local notation "P" => 999999937

local instance : NeZero 999999937 := ⟨by norm_num⟩

private lemma cast_modP (n : ℕ) : ((n % P : ℕ) : ZMod P) = (n : ZMod P) :=
  (ZMod.natCast_eq_natCast_iff (n % P) n P).mpr (Nat.mod_modEq n P)

private lemma getD_tail (l : List ℕ) (i : ℕ) : l.tail.getD i 0 = l.getD (i + 1) 0 := by
  cases l with
  | nil => rfl
  | cons r l' =>
      cases i with
      | zero => rfl
      | succ i => rfl

/-- The tail of the packed residue list is the seed list for indices
`2, …, 65536`: entry `i` is `τ (i + 2)` reduced mod `P`. -/
private theorem tail_seed (i : ℕ) (hi : i < 65535) :
    (((tauResList 65536).tail.getD i 0 % P : ℕ) : ZMod P) = ((tau (i + 2) : ℤ) : ZMod P) := by
  rw [getD_tail, cast_modP]
  have h2 := tauResList_eq_tauZMod 65536 (i + 1) (le_refl _) (by omega)
  rw [h2]

private theorem tail_length : (tauResList 65536).tail.length = 65535 := by
  rw [List.length_tail, tauResList_length]

-- The chain decide: all 65 535 chains (seeds τ m, m = 2..65536) of 32 steps
-- check nonzero; ~200 s of kernel time on top of the packed-list evaluation,
-- ~63 GiB kernel heap (same scale as LehmerPacked's own 65536 decide).
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000 in
theorem chains_nonvanishing_65536 : chainsOK 2 (tauResList 65536).tail = true := by
  decide +kernel

/-- **Prime powers past the wall**: `τ (p ^ a) ≠ 0` for every prime `p ≤ 65536`
and every `p ^ a ≤ 2 ^ 32`.  The prime-power frontier moves from 65536 to
`2 ^ 32` — a factor of 65 536 — at the cost of one linear chain per prime
instead of a dense coefficient computation. -/
theorem tau_prime_pow_ne_zero_of_le_two_pow_32 {p a : ℕ} (hp : p.Prime)
    (hp64k : p ≤ 65536) (hle : p ^ a ≤ 2 ^ 32) : tau (p ^ a) ≠ 0 := by
  rcases a with _ | a
  · rw [pow_zero]
    simp [tau_one]
  · have hp2 : 2 ≤ p := hp.two_le
    have ha32 : a + 1 ≤ 32 := by
      by_contra hc
      have h2a := Nat.pow_lt_pow_right (by norm_num : 1 < (2 : ℕ)) (by omega : 32 < a + 1)
      have h2b : (2 : ℕ) ^ (a + 1) ≤ p ^ (a + 1) := Nat.pow_le_pow_left hp2 (a + 1)
      omega
    exact tau_prime_pow_ne_zero_of_chains tail_length tail_seed
      chains_nonvanishing_65536 hp hp2 hp64k (by omega) ha32

/-- **Lehmer nonvanishing for the 2³² prime-power blocks**: `τ n ≠ 0` for
every `n ≥ 1` all of whose prime-power divisors `p ^ a` have `p ≤ 65536` and
`p ^ a ≤ 2 ^ 32` (the hypotheses hold in particular for every `n ≤ 2 ^ 32`
that is 65536-smooth). -/
theorem tau_ne_zero_of_prime_pow_le_two_pow_32 {n : ℕ} (hn : 0 < n)
    (hpf : ∀ q : ℕ, q.Prime → q ∣ n → q ≤ 65536)
    (hpp : ∀ q a : ℕ, q.Prime → 0 < a → q ^ a ∣ n → q ^ a ≤ 2 ^ 32) : tau n ≠ 0 :=
  tau_ne_zero_of_prime_pows hn fun q a hq ha hdvd =>
    tau_prime_pow_ne_zero_of_le_two_pow_32 hq
      (hpf q hq (dvd_trans (dvd_pow_self q ha.ne') hdvd)) (hpp q a hq ha hdvd)

/-- Every power of two up to the 32nd: `τ (2 ^ a) ≠ 0` for `a ≤ 32`. -/
theorem tau_two_pow_ne_zero (a : ℕ) (ha : a ≤ 32) : tau (2 ^ a) ≠ 0 :=
  tau_prime_pow_ne_zero_of_le_two_pow_32 Nat.prime_two (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) ha)

/-- `τ 131072 = τ (2 ^ 17) ≠ 0` — the first power of two past the 65536 wall. -/
theorem tau_of_131072_ne_zero : tau 131072 ≠ 0 := by
  have h : tau (2 ^ 17) ≠ 0 := tau_two_pow_ne_zero 17 (by norm_num)
  rwa [show (2 : ℕ) ^ 17 = 131072 from by norm_num] at h

/-- `τ 4294967296 = τ (2 ^ 32) ≠ 0` — the full 2³² index, 65 536 times past
the dense Iteration-6 bound. -/
theorem tau_of_two_pow_32_ne_zero : tau 4294967296 ≠ 0 := by
  have h : tau (2 ^ 32) ≠ 0 := tau_two_pow_ne_zero 32 (le_refl _)
  rwa [show (2 : ℕ) ^ 32 = 4294967296 from by norm_num] at h

end Ramanujan
