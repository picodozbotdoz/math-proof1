import MathProof.Tau.LehmerSieve691
import Mathlib.Order.Interval.Finset.Nat

/-!
# Kernel-verified Lehmer coverage anchors (bad-prime census and counts)

`LehmerSieve691` leaves exactly one escape class above the dense kernel bound
65536: primes `p` with `p % 691 = 690` ("bad primes" — the class where
`691 ∣ σ₁₁ p`, so the mod-691 sieve cannot reach them).  The heavy
`LehmerPrimeGrand` statement lifts this to indices: `τ n ≠ 0` whenever every
prime factor of `n` is `≤ 65536` or `≢ 690 [MOD 691]`.  The *measure* of that
coverage was counted exactly (in Python) in
`research/iteration22/lehmer-coverage/STUDY.md`: below `2 ^ 32` exactly
3 894 333 of 4 294 967 295 indices are uncovered — multiples of the 294 618
bad primes, the first being 70481 (the Lean gap bound).  This module makes
the small-anchor part of that story **kernel-verified**:

* `badPrimes2p18_filter` — the census below `2 ^ 18`: among the 285
  arithmetic-progression candidates `691 * k + 690`, `k ∈ [94, 378]` (all
  numbers `≡ 690 [MOD 691]` in `(65536, 2 ^ 18]`), exactly the 17 listed
  primes pass a structural trial-division certificate (`decide +kernel`).
  The `2 ^ 20` twin (`badPrimes2p20_filter`) filters the 1 423 candidates
  below `2 ^ 20` down to the 98 bad primes.
* `badPrimes2p18_spec` / `bad_prime_lt_2p18_mem` — soundness and completeness
  of the census: the 17 listed are exactly the bad primes below `2 ^ 18`
  (same for the 98 below `2 ^ 20`).
* `card_uncoveredSet` — the no-overlap count identity (structural): below
  `2 ^ 32` two distinct primes `> 65536` never divide the same `n`
  (`65537 ^ 2 > 2 ^ 32`), so the uncovered count is `Σ ⌊(B − 1) / p⌋`.
* `uncovered_2p18` / `covered_count_2p18` — exactly 23 indices `n ∈ [1, 2 ^ 18)`
  are divisible by a bad prime; 262 120 of the 262 143 indices are covered
  (and 227 / 1 048 348 of 1 048 575 below `2 ^ 20`: `uncovered_2p20`,
  `covered_count_2p20`).

`Nat.Prime` itself cannot be kernel-decided (its `minFac` decidability
instance is well-founded recursion, invisible to `decide`), so the module
carries a small structural trial-division certificate `noFactorFrom` in the
`HornerCert` tradition: own kernel-friendly definition, one kernel `decide`,
correctness (`prime_of_noFactorFrom`) proven once.

The census and count numbers agree with the exact Python study cited above
(triple cross-checked there: formula vs direct marking vs the Lean-known
anchor 70481).
-/

namespace Ramanujan

/-! ### A structural trial-division primality certificate -/

/-- Boolean trial-division certificate: `noFactorFrom n d k = true` when none
of `d, d + 1, …, d + k − 1` divides `n` (one divisor test per step; `&&`
exits at the first hit).  Structural in `k`, so the kernel can evaluate it —
unlike `Nat.Prime`'s `minFac`-based instance, which is well-founded recursion
and cannot be reduced by `decide`. -/
def noFactorFrom (n d : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => (!(decide (d ∣ n))) && noFactorFrom n (d + 1) k

private theorem noFactorFrom_nodvd {n d k d' : ℕ} (h : noFactorFrom n d k = true)
    (hle : d ≤ d') (hlt : d' < d + k) : ¬ d' ∣ n := by
  induction k generalizing d with
  | zero => exact absurd hlt (by omega)
  | succ k ih =>
      simp only [noFactorFrom, Bool.and_eq_true] at h
      rcases Nat.lt_or_ge d' (d + 1) with hlt' | hge'
      · intro hddvd
        have hde : d' = d := Nat.le_antisymm (by omega) hle
        rw [hde] at hddvd
        have hdt : decide (d ∣ n) = true := by simp [hddvd]
        rw [hdt] at h
        exact absurd h.1 (by simp)
      · exact ih h.2 hge' (by omega)

private theorem noFactorFrom_of_prime {p : ℕ} (hp : p.Prime) {d k : ℕ}
    (hd : 2 ≤ d) (hdk : d + k ≤ p) : noFactorFrom p d k = true := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
      simp only [noFactorFrom, Bool.and_eq_true]
      refine ⟨?_, ih (by omega) (by omega)⟩
      cases hdd : decide (d ∣ p) with
      | true =>
          have hdvd : d ∣ p := of_decide_eq_true hdd
          rcases hp.eq_one_or_self_of_dvd d hdvd with h1 | h2
          · omega
          · omega
      | false => rfl

/-- Correctness of the certificate: `n ≥ 2` with no divisor in `[2, k + 1]`
is prime once `n < (k + 2) ^ 2` (any composite `n` has a factor `a` with
`a ^ 2 ≤ n`). -/
theorem prime_of_noFactorFrom {n k : ℕ} (hn : 2 ≤ n)
    (h : noFactorFrom n 2 k = true) (hk : n < (k + 2) * (k + 2)) : n.Prime := by
  by_contra hnp
  have hpos : 0 < n := by omega
  have hmdvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
  have hm2 : 2 ≤ Nat.minFac n := (Nat.minFac_prime (by omega)).two_le
  have hmsq : Nat.minFac n * Nat.minFac n ≤ n := by
    simpa [Nat.pow_two] using Nat.minFac_sq_le_self hpos hnp
  have hmlt : Nat.minFac n < k + 2 := by
    by_contra hge
    have hge' : k + 2 ≤ Nat.minFac n := Nat.ge_of_not_lt hge
    exact absurd ((Nat.mul_le_mul hge' hge').trans hmsq) (Nat.not_le.2 hk)
  exact noFactorFrom_nodvd h hm2 (by omega) hmdvd

/-! ### The bad-prime census below `2 ^ 18` -/

/-- The bad primes below `2 ^ 18` (the output of the kernel filter
`badPrimes2p18_filter`): the 17 primes `p` with `65536 < p < 2 ^ 18` and
`p % 691 = 690`. -/
def badPrimes2p18 : List ℕ :=
  [70481, 92593, 96739, 105031, 120233, 134053, 145109, 167221, 179659, 182423,
   186569, 187951, 192097, 194861, 212827, 216973, 233557]

/-- **Kernel census**: the numbers `≡ 690 [MOD 691]` in `(65536, 2 ^ 18]`
are `691 * k + 690` for `k = 94 + i`, `i < 285`; filtering the candidates by
the structural trial-division certificate (divisors `2, …, 512`; every
candidate is below `513 ^ 2 = 263169`) leaves exactly the 17 bad primes. -/
theorem badPrimes2p18_filter :
    (((List.range 285).filter fun i => noFactorFrom (691 * (i + 94) + 690) 2 511).map
        fun i => 691 * (i + 94) + 690) = badPrimes2p18 := by
  decide +kernel

theorem badPrimes2p18_spec {p : ℕ} (h : p ∈ badPrimes2p18) :
    p.Prime ∧ 65536 < p ∧ p < 2 ^ 18 ∧ p % 691 = 690 := by
  rw [← badPrimes2p18_filter] at h
  simp only [List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨i, ⟨hi1, hi2⟩, hi3⟩ := h
  have hpv : p = 691 * (i + 94) + 690 := hi3.symm
  have h218 : (2 : ℕ) ^ 18 = 262144 := by norm_num
  have hbounds : 65644 ≤ p ∧ p ≤ 261888 := ⟨by omega, by omega⟩
  refine ⟨prime_of_noFactorFrom (by omega) (by rwa [hpv]) ?_, by omega, by omega, by omega⟩
  · have h513 : (511 + 2) * (511 + 2) = 263169 := by norm_num
    omega

/-- **Completeness of the census**: every bad prime below `2 ^ 18` is one of
the 17 listed.  Together with `badPrimes2p18_spec`, the list is exactly
`{p | 65536 < p < 2 ^ 18 ∧ p % 691 = 690}`. -/
theorem bad_prime_lt_2p18_mem {p : ℕ} (hpr : p.Prime) (hgt : 65536 < p)
    (hlt : p < 2 ^ 18) (hmod : p % 691 = 690) : p ∈ badPrimes2p18 := by
  have h218 : (2 : ℕ) ^ 18 = 262144 := by norm_num
  have hj : ∃ j, p = 691 * j + 690 := ⟨p / 691, by omega⟩
  obtain ⟨j, hj⟩ := hj
  have hjb : 94 ≤ j ∧ j < 379 := ⟨by omega, by omega⟩
  have hflt : noFactorFrom p 2 511 = true := noFactorFrom_of_prime hpr (by omega) (by omega)
  have hval : 691 * ((j - 94) + 94) + 690 = p := by omega
  have hmem : j - 94 ∈
      (List.range 285).filter fun i => noFactorFrom (691 * (i + 94) + 690) 2 511 := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩
    rw [hval]
    exact hflt
  rw [← badPrimes2p18_filter]
  have hmap : 691 * ((j - 94) + 94) + 690 ∈
      ((List.range 285).filter fun i => noFactorFrom (691 * (i + 94) + 690) 2 511).map
        fun i => 691 * (i + 94) + 690 := List.mem_map_of_mem hmem
  rwa [hval] at hmap

private theorem badPrimes2p18_nodup : badPrimes2p18.Nodup := by
  rw [← badPrimes2p18_filter]
  exact List.Nodup.map (fun a b hab => by omega)
    (List.Nodup.filter _ (List.nodup_range (n := 285)))

/-! ### The bad-prime census below `2 ^ 20` -/

/-- The bad primes below `2 ^ 20` (the output of the kernel filter
`badPrimes2p20_filter`): the 98 primes `p` with `65536 < p < 2 ^ 20` and
`p % 691 = 690`. -/
def badPrimes2p20 : List ℕ :=
[
  70481, 92593, 96739, 105031, 120233, 134053, 145109, 167221,
  179659, 182423, 186569, 187951, 192097, 194861, 212827, 216973,
  233557, 281927, 286073, 290219, 304039, 310949, 312331, 344117,
  352409, 378667, 382813, 389723, 395251, 410453, 424273, 449149,
  464351, 469879, 472643, 478171, 485081, 505811, 507193, 514103,
  518249, 523777, 532069, 547271, 559709, 561091, 565237, 576293,
  581821, 592877, 602551, 609461, 610843, 613607, 623281, 631573,
  663359, 671651, 675797, 685471, 697909, 700673, 704819, 706201,
  733841, 739369, 772537, 776683, 789121, 813997, 818143, 820907,
  841637, 859603, 863749, 866513, 872041, 891389, 899681, 901063,
  903827, 905209, 920411, 924557, 928703, 946669, 961871, 963253,
  975691, 988129, 990893, 1008859, 1015769, 1021297, 1024061, 1025443,
  1028207, 1036499]

/-- **Kernel census at `2 ^ 20`**: the numbers `≡ 690 [MOD 691]` in
`(65536, 2 ^ 20]` are `691 * k + 690` for `k = 94 + i`, `i < 1423`; the
trial-division certificate with divisors `2, …, 1024` (every candidate is
below `1025 ^ 2 = 1050625`) leaves exactly the 98 bad primes. -/
theorem badPrimes2p20_filter :
    (((List.range 1423).filter fun i => noFactorFrom (691 * (i + 94) + 690) 2 1023).map
        fun i => 691 * (i + 94) + 690) = badPrimes2p20 := by
  decide +kernel

theorem badPrimes2p20_spec {p : ℕ} (h : p ∈ badPrimes2p20) :
    p.Prime ∧ 65536 < p ∧ p < 2 ^ 20 ∧ p % 691 = 690 := by
  rw [← badPrimes2p20_filter] at h
  simp only [List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨i, ⟨hi1, hi2⟩, hi3⟩ := h
  have hpv : p = 691 * (i + 94) + 690 := hi3.symm
  have h220 : (2 : ℕ) ^ 20 = 1048576 := by norm_num
  have hbounds : 65644 ≤ p ∧ p ≤ 1048246 := ⟨by omega, by omega⟩
  refine ⟨prime_of_noFactorFrom (by omega) (by rwa [hpv]) ?_, by omega, by omega, by omega⟩
  · have h1025 : (1023 + 2) * (1023 + 2) = 1050625 := by norm_num
    omega

/-- **Completeness of the census**: every bad prime below `2 ^ 20` is one of
the 98 listed. -/
theorem bad_prime_lt_2p20_mem {p : ℕ} (hpr : p.Prime) (hgt : 65536 < p)
    (hlt : p < 2 ^ 20) (hmod : p % 691 = 690) : p ∈ badPrimes2p20 := by
  have h220 : (2 : ℕ) ^ 20 = 1048576 := by norm_num
  have hj : ∃ j, p = 691 * j + 690 := ⟨p / 691, by omega⟩
  obtain ⟨j, hj⟩ := hj
  have hjb : 94 ≤ j ∧ j < 1517 := ⟨by omega, by omega⟩
  have hflt : noFactorFrom p 2 1023 = true := noFactorFrom_of_prime hpr (by omega) (by omega)
  have hval : 691 * ((j - 94) + 94) + 690 = p := by omega
  have hmem : j - 94 ∈
      (List.range 1423).filter fun i => noFactorFrom (691 * (i + 94) + 690) 2 1023 := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩
    rw [hval]
    exact hflt
  rw [← badPrimes2p20_filter]
  have hmap : 691 * ((j - 94) + 94) + 690 ∈
      ((List.range 1423).filter fun i => noFactorFrom (691 * (i + 94) + 690) 2 1023).map
        fun i => 691 * (i + 94) + 690 := List.mem_map_of_mem hmem
  rwa [hval] at hmap

private theorem badPrimes2p20_nodup : badPrimes2p20.Nodup := by
  rw [← badPrimes2p20_filter]
  exact List.Nodup.map (fun a b hab => by omega)
    (List.Nodup.filter _ (List.nodup_range (n := 1423)))

/-! ### The no-overlap count -/

/-- The uncovered indices with respect to a bad-prime list `L`: the
`n ∈ [1, B)` divisible by at least one `p ∈ L`. -/
def uncoveredSet (B : ℕ) (L : List ℕ) : Finset ℕ :=
  (Finset.Ico 1 B).filter fun n => L.any (fun p => decide (p ∣ n)) = true

private theorem uncoveredSet_cons (B : ℕ) (p : ℕ) (L : List ℕ) :
    uncoveredSet B (p :: L) =
      (Finset.Ico 1 B).filter (fun n => decide (p ∣ n) = true) ∪ uncoveredSet B L := by
  ext n
  simp only [uncoveredSet, List.any_cons, Finset.mem_filter, Finset.mem_union, Bool.or_eq_true,
    decide_eq_true_eq, and_or_left]

private theorem mem_uncoveredSet {B : ℕ} {n : ℕ} : ∀ {L : List ℕ},
    n ∈ uncoveredSet B L ↔ 1 ≤ n ∧ n < B ∧ ∃ p ∈ L, p ∣ n := by
  intro L
  induction L with
  | nil => simp [uncoveredSet]
  | cons p L ih =>
      rw [uncoveredSet_cons, Finset.mem_union, ih]
      simp only [Finset.mem_filter, decide_eq_true_eq, Finset.mem_Ico, and_assoc]
      constructor
      · rintro (⟨h1, h2, hqd⟩ | ⟨h1, h2, q, hq, hqd⟩)
        · exact ⟨h1, h2, p, List.mem_cons_self, hqd⟩
        · exact ⟨h1, h2, q, List.mem_cons_of_mem p hq, hqd⟩
      · rintro ⟨h1, h2, q, hq, hqd⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inl ⟨h1, h2, hqd⟩
        · exact Or.inr ⟨h1, h2, q, hq, hqd⟩

private theorem mul_gt_two_pow_32 {p q : ℕ} (h1 : 65537 ≤ p) (h2 : 65537 ≤ q) :
    2 ^ 32 < p * q := by
  have hle : 65537 * 65537 ≤ p * q := Nat.mul_le_mul h1 h2
  have hlt : 2 ^ 32 < 65537 * 65537 := by norm_num
  exact lt_of_lt_of_le hlt hle

private theorem disjoint_filter_uncovered {B p : ℕ} {L : List ℕ}
    (hpr : p.Prime) (hgt : 65536 < p) (hB : B ≤ 2 ^ 32)
    (hLpr : ∀ q ∈ L, q.Prime) (hLgt : ∀ q ∈ L, 65536 < q) (hnotmem : p ∉ L) :
    Disjoint ((Finset.Ico 1 B).filter fun n => decide (p ∣ n) = true)
      (uncoveredSet B L) := by
  rw [Finset.disjoint_right]
  intro x hxmem hx
  obtain ⟨_, _, q, hqL, hqvd⟩ := mem_uncoveredSet.mp hxmem
  have hqgt : 65536 < q := hLgt q hqL
  obtain ⟨hxIco, hxdvd⟩ := Finset.mem_filter.mp hx
  have hpq : p * q ∣ x :=
    Nat.Prime.dvd_mul_of_dvd_ne (fun h => hnotmem (by rw [h]; exact hqL)) hpr (hLpr q hqL)
      (of_decide_eq_true hxdvd) hqvd
  have hxle : p * q ≤ x :=
    Nat.le_of_dvd (by have := (Finset.mem_Ico.mp hxIco).1; omega) hpq
  have hchain : B < x :=
    Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hB (mul_gt_two_pow_32 (by omega) (by omega))) hxle
  have hxltB : x < B := (Finset.mem_Ico.mp hxIco).2
  omega

private theorem card_filter_dvd_Ico (p : ℕ) (hp : 0 < p) (B : ℕ) :
    ((Finset.Ico 1 B).filter fun n => decide (p ∣ n) = true).card = (B - 1) / p := by
  have himg : (Finset.Ico 1 B).filter (fun n => decide (p ∣ n) = true)
      = (Finset.Ico 1 ((B - 1) / p + 1)).image (fun m => m * p) := by
    ext n
    simp only [Finset.mem_filter, decide_eq_true_eq, Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, hdvd⟩
      obtain ⟨m, hm0⟩ := hdvd
      have hm : n = m * p := by rw [hm0, Nat.mul_comm]
      have hmpos : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with hz | hz
        · rw [hz, Nat.zero_mul] at hm; omega
        · omega
      have hnle : n ≤ B - 1 := by omega
      have hmple : m * p ≤ B - 1 := by rw [← hm]; exact hnle
      have hmle : m ≤ (B - 1) / p := (Nat.le_div_iff_mul_le hp).mpr hmple
      exact ⟨m, ⟨hmpos, by omega⟩, hm.symm⟩
    · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
      have hmp : m * p ≤ (B - 1) / p * p :=
        Nat.mul_le_mul_right _ (by omega)
      have hle : (B - 1) / p * p ≤ B - 1 := Nat.div_mul_le_self _ _
      have h1mp : 1 ≤ m * p := Nat.mul_le_mul hm1 hp
      have hB1 : 1 ≤ B - 1 := h1mp.trans (le_trans hmp hle)
      refine ⟨⟨h1mp, ?_⟩, dvd_mul_left p m⟩
      exact lt_of_le_of_lt (le_trans hmp hle) (Nat.sub_lt (by omega) (by norm_num))
  rw [himg, Finset.card_image_of_injOn]
  · simp only [Nat.card_Ico]
    exact Nat.add_sub_cancel ((B - 1) / p) 1
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_right hp hab

/-- **The no-overlap count identity**: for distinct primes `L`, all `> 65536`,
and any `B ≤ 2 ^ 32`, the indices `n ∈ [1, B)` divisible by some `p ∈ L`
number exactly `Σ_{p ∈ L} ⌊(B − 1) / p⌋` — no two distinct primes `> 65536`
divide the same `n < 2 ^ 32`, because `65537 ^ 2 > 2 ^ 32`. -/
theorem card_uncoveredSet {B : ℕ} (hB : B ≤ 2 ^ 32) : ∀ L : List ℕ,
    (∀ p ∈ L, p.Prime) → (∀ p ∈ L, 65536 < p) → L.Nodup →
      (uncoveredSet B L).card = (L.map fun p => (B - 1) / p).sum := by
  intro L
  induction L with
  | nil => simp [uncoveredSet]
  | cons p L ih =>
      intro hpr hgt hnd
      have hpnd : p ∉ L := (List.nodup_cons.mp hnd).1
      have hdisj := disjoint_filter_uncovered (hpr p List.mem_cons_self)
        (hgt p List.mem_cons_self) hB (fun q hq => hpr q (List.mem_cons_of_mem p hq))
        (fun q hq => hgt q (List.mem_cons_of_mem p hq)) hpnd
      rw [uncoveredSet_cons B p L, Finset.card_union_eq_card_add_card.mpr hdisj,
        card_filter_dvd_Ico p (by have := hgt p List.mem_cons_self; omega) B,
        ih (fun q hq => hpr q (List.mem_cons_of_mem p hq))
          (fun q hq => hgt q (List.mem_cons_of_mem p hq)) (List.nodup_cons.mp hnd).2]
      simp [List.sum_cons]

/-- **Kernel-verified count**: exactly 23 indices `n ∈ [1, 2 ^ 18)` are
divisible by a bad prime. -/
theorem uncovered_2p18 : (uncoveredSet (2 ^ 18) badPrimes2p18).card = 23 := by
  rw [card_uncoveredSet (by norm_num) badPrimes2p18
    (fun p hp => (badPrimes2p18_spec hp).1) (fun p hp => (badPrimes2p18_spec hp).2.1)
    badPrimes2p18_nodup]
  decide +kernel

/-- **Kernel-verified coverage count**: 262 120 of the 262 143 indices
`n ∈ [1, 2 ^ 18)` avoid every bad prime — the first kernel-verified coverage
*count* in the stack (combine with `LehmerPrimeGrand` for `τ n ≠ 0` on the
covered set). -/
theorem covered_count_2p18 :
    (2 ^ 18 - 1) - (uncoveredSet (2 ^ 18) badPrimes2p18).card = 262120 := by
  rw [uncovered_2p18]
  norm_num

/-- **Kernel-verified count at `2 ^ 20`**: exactly 227 indices `n ∈ [1, 2 ^ 20)`
are divisible by a bad prime; `2 ^ 20 − 1 − 227 = 1 048 348` are covered. -/
theorem uncovered_2p20 : (uncoveredSet (2 ^ 20) badPrimes2p20).card = 227 := by
  rw [card_uncoveredSet (by norm_num) badPrimes2p20
    (fun p hp => (badPrimes2p20_spec hp).1) (fun p hp => (badPrimes2p20_spec hp).2.1)
    badPrimes2p20_nodup]
  decide +kernel

theorem covered_count_2p20 :
    (2 ^ 20 - 1) - (uncoveredSet (2 ^ 20) badPrimes2p20).card = 1048348 := by
  rw [uncovered_2p20]
  norm_num

end Ramanujan
