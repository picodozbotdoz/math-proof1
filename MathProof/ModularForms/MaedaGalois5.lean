import MathProof.ModularForms.MaedaGalois5Identities
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

set_option maxRecDepth 8000

/-!
# The quintic `S₅` Galois criterion and the dim-5 Maeda instances

Group-theoretic prerequisites and the `F₂₀`-resolvent data live in
`MaedaGalois5Defs`; the kernel-verified coefficient identities live in
`MaedaGalois5Identities`.  This file contains the `S₅` criterion and its
instantiations for the six `dim S_k = 5` weights.
-/

open Equiv Subgroup Polynomial Module IntermediateField

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

namespace MaedaGalois

section Main

/-! ### The permutation action of the Galois group on the five roots

For the splitting field `K` of an irreducible quintic, every `K`-automorphism
over `ℚ` permutes the five roots; the induced map `ρ : Gal →* Perm (Fin 5)` is
injective, and a Galois element whose permutation normalizes `<c>` (a 5-cycle)
fixes the pentagon-pentagram product of `c`.  Combined with the subgroup
structure of `S₅` this yields the `S₅` criterion below. -/

/-- The pentagon sum of the power `c ^ 4` equals the pentagon sum of `c`
(any 5-cycle: `c ^ 5 = 1`). -/
theorem theta_pow4 {K : Type*} [Field K] (x : Fin 5 → K) (c : Equiv.Perm (Fin 5))
    (h5 : c ^ 5 = 1) : theta x ⇑(c ^ 4) = theta x ⇑c := by
  have h1 : ∀ w : Fin 5, (c ^ 4) (c w) = w := by
    intro w
    rw [← Perm.mul_apply, ← pow_succ, h5, Perm.one_apply]
  simp only [theta]
  rw [← Equiv.sum_comp c (fun u => x u * x ((c ^ 4) u))]
  refine Finset.sum_congr rfl fun w _ => ?_
  change x (c w) * x ((c ^ 4) (c w)) = x w * x (c w)
  rw [h1, mul_comm]

/-- The pentagon sum of the power `c ^ 3` equals the pentagon sum of `c ^ 2`. -/
theorem theta_pow3 {K : Type*} [Field K] (x : Fin 5 → K) (c : Equiv.Perm (Fin 5))
    (h5 : c ^ 5 = 1) : theta x ⇑(c ^ 3) = theta x ⇑(c * c) := by
  have h1 : ∀ w : Fin 5, (c ^ 3) ((c * c) w) = w := by
    intro w
    have hc : c ^ 3 * c * c = c ^ 5 := by group
    change (c ^ 3 * c * c) w = w
    rw [hc, h5, Perm.one_apply]
  simp only [theta]
  rw [← Equiv.sum_comp (c * c) (fun u => x u * x ((c ^ 3) u))]
  refine Finset.sum_congr rfl fun w _ => ?_
  change x ((c * c) w) * x ((c ^ 3) ((c * c) w)) = x w * x ((c * c) w)
  rw [h1, mul_comm]

/-- The six table cycles, as permutations. -/
noncomputable def cycPerm : Fin 6 → Equiv.Perm (Fin 5) := by
  intro j
  match j with
  | 0 => exact Equiv.ofBijective ![4, 0, 1, 2, 3] (by decide)
  | 1 => exact Equiv.ofBijective ![4, 0, 3, 1, 2] (by decide)
  | 2 => exact Equiv.ofBijective ![4, 2, 0, 1, 3] (by decide)
  | 3 => exact Equiv.ofBijective ![4, 2, 3, 0, 1] (by decide)
  | 4 => exact Equiv.ofBijective ![4, 3, 0, 2, 1] (by decide)
  | 5 => exact Equiv.ofBijective ![4, 3, 1, 0, 2] (by decide)

/-- Each table cycle satisfies `T ^ 5 = 1` and is nontrivial. -/
lemma cycPerm_pow5 (j : Fin 6) :
    (cycPerm j) ^ 5 = 1 ∧ cycPerm j ≠ 1 := by
  fin_cases j <;> decide

/-- Each table cycle has order 5. -/
lemma cycPerm_order (j : Fin 6) : orderOf (cycPerm j) = 5 := by
  have h1 : orderOf (cycPerm j) ∣ 5 :=
    (orderOf_dvd_iff_pow_eq_one (n := 5)).mpr (cycPerm_pow5 j).1
  have h2 : orderOf (cycPerm j) ≠ 1 := by
    intro hcon
    exact (cycPerm_pow5 j).2 (orderOf_eq_one_iff.mp hcon)
  have h5p : Nat.Prime 5 := by decide
  rcases h5p.eq_one_or_self_of_dvd _ h1 with h | h
  · exact absurd h h2
  · exact h

set_option maxHeartbeats 8000000 in
-- `fin_cases`/`decide` over `Perm (Fin 5)` and large normalizations need a larger budget
/-- Every nontrivial 5-torsion permutation is a power of exponent `1..4` of one
of the six table cycles. -/
lemma cycles_complete (σ : Equiv.Perm (Fin 5)) (h5 : σ ^ 5 = 1) (h1 : σ ≠ 1) :
    ∃ (j : Fin 6) (m : Fin 4), ∀ i, σ i = (cycPerm j ^ (m.val + 1)) i := by
  fin_cases σ
  all_goals first
    | exact absurd (by decide) h1
    | exact absurd h5 (by decide)
    | decide

/-- Powers of a conjugate: `(σ * c * σ⁻¹) ^ n = σ * c ^ n * σ⁻¹`. -/
private lemma pow_conj {G : Type*} [Group G] (σ c : G) (n : ℕ) :
    (σ * c * σ⁻¹) ^ n = σ * c ^ n * σ⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    group

/-- The order of a conjugate equals the order of the element. -/
private lemma orderOf_conj' {G : Type*} [Group G] (σ c : G) :
    orderOf (σ * c * σ⁻¹) = orderOf c := by
  have hiff : ∀ n : ℕ, (σ * c * σ⁻¹) ^ n = 1 ↔ c ^ n = 1 := by
    intro n
    constructor
    · intro h
      have hc := congrArg (fun z : G => σ⁻¹ * z * σ) h
      rw [pow_conj] at hc
      calc c ^ n = σ⁻¹ * (σ * c ^ n * σ⁻¹) * σ := by group
        _ = σ⁻¹ * 1 * σ := by rw [hc]
        _ = 1 := by group
    · intro h
      rw [pow_conj, h]
      group
  refine Nat.dvd_antisymm ?_ ?_
  · exact (orderOf_dvd_iff_pow_eq_one (n := orderOf c)).mpr
      ((hiff (orderOf c)).mpr (pow_orderOf_eq_one c))
  · exact (orderOf_dvd_iff_pow_eq_one (n := orderOf (σ * c * σ⁻¹))).mpr
      ((hiff (orderOf (σ * c * σ⁻¹))).mp (pow_orderOf_eq_one _))

set_option maxHeartbeats 8000000 in
-- `fin_cases`/`decide` over `Perm (Fin 5)` and large normalizations need a larger budget
/-- A subgroup of `S₅` of order 10 or 20 normalizes the cyclic subgroup
generated by one of its elements of order 5 (a 5-cycle). -/
theorem perm_order_5_normal_of_card (H : Subgroup (Equiv.Perm (Fin 5)))
    (hH : Nat.card H = 10 ∨ Nat.card H = 20) :
    ∃ c : Equiv.Perm (Fin 5), orderOf c = 5 ∧ ∀ σ ∈ H, σ * c * σ⁻¹ ∈ Subgroup.zpowers c := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5dvd : 5 ∣ Nat.card H := by rcases hH with h | h <;> rw [h] <;> norm_num
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 5 h5dvd
  have h5H : (c ^ 5 : ↥H) = 1 :=
    (congrArg (fun n : ℕ => (c ^ n : ↥H)) hc).symm.trans (pow_orderOf_eq_one c)
  have hco : orderOf (c : Equiv.Perm (Fin 5)) = 5 := by
    have h1 : (c : Equiv.Perm (Fin 5)) ^ 5 = 1 := by
      calc (c : Equiv.Perm (Fin 5)) ^ 5 = ((c ^ 5 : ↥H) : Equiv.Perm (Fin 5)) :=
          (Subgroup.coe_pow H c 5).symm
        _ = ((1 : ↥H) : Equiv.Perm (Fin 5)) := by rw [h5H]
        _ = 1 := by simp
    have hd1 : orderOf (c : Equiv.Perm (Fin 5)) ∣ 5 :=
      (orderOf_dvd_iff_pow_eq_one (n := 5)).mpr h1
    have hd2 : orderOf (c : Equiv.Perm (Fin 5)) ≠ 1 := by
      intro hcon
      have hc1 : (c : Equiv.Perm (Fin 5)) = 1 := orderOf_eq_one_iff.mp hcon
      have hc2 : c = (1 : ↥H) := by
        apply Subtype.ext
        simpa using hc1
      rw [hc2] at hc
      simp at hc
    have h5p : Nat.Prime 5 := by decide
    rcases h5p.eq_one_or_self_of_dvd _ hd1 with h | h
    · exact absurd h hd2
    · exact h
  refine ⟨(c : Equiv.Perm (Fin 5)), hco, ?_⟩
  -- in `↥H`: the normalizer `N` of `<c>` has |N| ≡ |H| [MOD 25] by the Sylow
  -- normalizer congruence, and 5 ≤ |N| ≤ |H| ∈ {10, 20}; the only value
  -- `≡ 10 resp. 20 [MOD 25]` in that range is |H| itself, so `<c> ⊴ H`.
  have hzc : Nat.card ↥(Subgroup.zpowers (c : ↥H)) = 5 := by
    rw [Nat.card_zpowers, hc]
  set N := Subgroup.normalizer (Subgroup.zpowers (c : ↥H) : Set ↥H) with hNdef
  have hmod : Nat.card ↥N % 25 = Nat.card ↥H % 25 :=
    Sylow.card_normalizer_modEq_card (p := 5) (n := 1) hzc
  have hNge : 5 ≤ Nat.card ↥N :=
    calc 5 = Nat.card ↥(Subgroup.zpowers (c : ↥H)) := hzc.symm
      _ ≤ Nat.card ↥N := Subgroup.card_le_of_le le_normalizer
  have hNle : Nat.card ↥N ≤ Nat.card ↥H := Subgroup.card_le_card_group N
  have hNcard : Nat.card ↥N = Nat.card ↥H := by
    rcases hH with h | h <;> omega
  have hNtop : N = ⊤ := Subgroup.eq_top_of_card_eq N hNcard
  intro σ hσ
  have hconj : ((⟨σ, hσ⟩ : ↥H) * c * (⟨σ, hσ⟩ : ↥H)⁻¹) ∈ Subgroup.zpowers (c : ↥H) := by
    have h1 : (⟨σ, hσ⟩ : ↥H) ∈ N := by
      rw [hNtop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_normalizer_iff] at h1
    exact (h1 c).mp (Subgroup.mem_zpowers c)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hconj
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  simpa using congrArg Subtype.val hk

set_option maxHeartbeats 8000000 in
-- `fin_cases`/`decide` over `Perm (Fin 5)` and large normalizations need a larger budget
/-- A Galois element whose induced permutation normalizes `<c>` fixes the
pentagon-pentagram product of `c`. -/
theorem gal_fixes_theta {K : Type*} [Field K] [Algebra ℚ K] (x : Fin 5 → K)
    (c : Equiv.Perm (Fin 5)) (hc5 : c ^ 5 = 1)
    (g : K ≃ₐ[ℚ] K) (σ : Equiv.Perm (Fin 5)) (hgx : ∀ i, g (x i) = x (σ i))
    (hnorm : σ * c * σ⁻¹ ∈ Subgroup.zpowers c) :
    g (theta x ⇑c * theta x ⇑(c * c)) = theta x ⇑c * theta x ⇑(c * c) := by
  have key : ∀ (d : Equiv.Perm (Fin 5)) (v : Fin 5), (σ * d * σ⁻¹) (σ v) = σ (d v) := by
    intro d v
    rw [Perm.mul_apply, Perm.mul_apply,
      show σ⁻¹ (σ v) = v from Equiv.symm_apply_apply σ v]
  have hgc : ∀ d : Equiv.Perm (Fin 5), g (theta x ⇑d) = theta x ⇑(σ * d * σ⁻¹) := by
    intro d
    change g (∑ v, x v * x (d v)) = ∑ v, x v * x ((σ * d * σ⁻¹) v)
    rw [map_sum]
    rw [← Equiv.sum_comp σ (fun u => x u * x ((σ * d * σ⁻¹) u))]
    refine Finset.sum_congr rfl fun v _ => ?_
    change g (x v * x (d v)) = x (σ v) * x ((σ * d * σ⁻¹) (σ v))
    rw [map_mul, hgx v, hgx (d v), key d v]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hnorm
  have h5z : (c : Equiv.Perm (Fin 5)) ^ ((5 : ℤ)) = 1 := by rw [zpow_ofNat, hc5]
  have hred : (c : Equiv.Perm (Fin 5)) ^ (k : ℤ) = c ^ (k % 5) := by
    have hk5 : (k : ℤ) = 5 * (k / 5) + k % 5 := by omega
    conv_lhs => rw [hk5]
    rw [zpow_add, zpow_mul, h5z, one_zpow, one_mul]
  have hmod : (k : ℤ) % 5 = 0 ∨ (k : ℤ) % 5 = 1 ∨ (k : ℤ) % 5 = 2 ∨ (k : ℤ) % 5 = 3
    ∨ (k : ℤ) % 5 = 4 := by
    have h1 : 0 ≤ (k : ℤ) % 5 := Int.emod_nonneg _ (by norm_num)
    have h2 : (k : ℤ) % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  rw [map_mul, hgc c, hgc (c * c)]
  have hsq : σ * (c * c) * σ⁻¹ = (σ * c * σ⁻¹) ^ 2 := by rw [sq]; group
  rw [hsq]
  rcases hmod with h0 | h1 | h2 | h3 | h4
  · have hz : c ^ (k : ℤ) = 1 := by rw [hred, h0]; norm_num
    have hq : σ * c * σ⁻¹ = (1 : Equiv.Perm (Fin 5)) := by rw [← hk, hz]
    have hc1 : c = 1 := by
      calc c = σ⁻¹ * (σ * c * σ⁻¹) * σ := by group
        _ = σ⁻¹ * 1 * σ := by rw [hq]
        _ = 1 := by group
    rw [hq, hc1, one_pow, one_mul]
  · have e1 : σ * c * σ⁻¹ = c ^ 1 := by rw [← hk, hred, h1, zpow_ofNat]
    rw [e1, pow_one, sq]
  · have e1 : σ * c * σ⁻¹ = c ^ 2 := by rw [← hk, hred, h2, zpow_ofNat]
    have q : (c ^ 2) ^ 2 = c ^ 4 := by rw [← pow_mul]
    rw [e1, q, theta_pow4 x c hc5, sq]
    ring
  · have e1 : σ * c * σ⁻¹ = c ^ 3 := by rw [← hk, hred, h3, zpow_ofNat]
    have q : (c ^ 3) ^ 2 = c := by
      rw [← pow_mul, show 3 * 2 = 5 + 1 from rfl, pow_succ, hc5, one_mul]
    rw [e1, q, theta_pow3 x c hc5]
    ring
  · have e1 : σ * c * σ⁻¹ = c ^ 4 := by rw [← hk, hred, h4, zpow_ofNat]
    have q : (c ^ 4) ^ 2 = c ^ 3 := by
      rw [← pow_mul, show 4 * 2 = 5 + 3 from rfl, pow_add, hc5, one_mul]
    rw [e1, q, theta_pow4 x c hc5, theta_pow3 x c hc5]

set_option maxHeartbeats 8000000 in
-- `fin_cases`/`decide` over `Perm (Fin 5)` and large normalizations need a larger budget
/-- `ThetaVals x j` is the pentagon-pentagram product of the table cycle
`cycPerm j` (the pentagram table is the square of the cycle table). -/
lemma thetaVals_cyc {K : Type*} [CommRing K] (x : Fin 5 → K) (j : Fin 6) :
    ThetaVals x j = theta x ⇑(cycPerm j) * theta x ⇑(cycPerm j * cycPerm j) := by
  fin_cases j <;>
  · change theta x _ * theta x _ = _
    congr 2; funext i; fin_cases i <;> rfl

/-- The pentagon-pentagram product of a 5-cycle depends only on the cyclic
group it generates: the powers `T ^ 1 … T ^ 4` all give the same value. -/
lemma theta_pair_pow {K : Type*} [Field K] (x : Fin 5 → K) (T : Equiv.Perm (Fin 5))
    (h5 : T ^ 5 = 1) (n : ℕ) (hn1 : 1 ≤ n) (hn4 : n ≤ 4) :
    theta x ⇑(T ^ n) * theta x ⇑(T ^ n * T ^ n) = theta x ⇑T * theta x ⇑(T * T) := by
  interval_cases n
  · rw [pow_one]
  · rw [← pow_add, show 2 + 2 = 4 from rfl, theta_pow4 x T h5, sq, mul_comm]
  · rw [← pow_add, show 3 + 3 = 5 + 1 from rfl, pow_add T 5 1, h5, one_mul, pow_one,
      theta_pow3 x T h5, mul_comm]
  · rw [← pow_add, show 4 + 4 = 5 + 3 from rfl, pow_add T 5 3, h5, one_mul, theta_pow4 x T h5,
      theta_pow3 x T h5]

set_option maxHeartbeats 8000000 in
-- `fin_cases`/`decide` over `Perm (Fin 5)` and large normalizations need a larger budget
/-- **Vieta for sextics**: a monic sextic whose coefficients are the signed
elementary symmetric functions of `t₀, …, t₅` factors as `∏ (X − tᵢ)`. -/
lemma sextic_vieta {K : Type*} [CommRing K] (t0 t1 t2 t3 t4 t5 c5 c4 c3 c2 c1 c0 : K)
    (h1 : t0 + t1 + t2 + t3 + t4 + t5 = -c5)
    (h2 : t0 * t1 + t0 * t2 + t0 * t3 + t0 * t4 + t0 * t5 + t1 * t2 + t1 * t3 + t1 * t4 + t1 * t5 +
      t2 * t3 + t2 * t4 + t2 * t5 + t3 * t4 + t3 * t5 + t4 * t5 = c4)
    (h3 : t0 * t1 * t2 + t0 * t1 * t3 + t0 * t1 * t4 + t0 * t1 * t5 + t0 * t2 * t3 + t0 * t2 * t4 +
      t0 * t2 * t5 + t0 * t3 * t4 + t0 * t3 * t5 + t0 * t4 * t5 + t1 * t2 * t3 + t1 * t2
      * t4 + t1 * t2 * t5 + t1 * t3 * t4 + t1 * t3 * t5 + t1 * t4 * t5 + t2 * t3 * t4 +
      t2 * t3 * t5 + t2 * t4 * t5 + t3 * t4 * t5 = -c3)
    (h4 : t0 * t1 * t2 * t3 + t0 * t1 * t2 * t4 + t0 * t1 * t2 * t5 + t0 * t1 * t3 * t4 + t0 * t1 *
      t3 * t5 + t0 * t1 * t4 * t5 + t0 * t2 * t3 * t4 + t0 * t2 * t3 * t5 + t0 * t2 * t4
      * t5 + t0 * t3 * t4 * t5 + t1 * t2 * t3 * t4 + t1 * t2 * t3 * t5 + t1 * t2 * t4 *
      t5 + t1 * t3 * t4 * t5 + t2 * t3 * t4 * t5 = c2)
    (h5 : t0 * t1 * t2 * t3 * t4 + t0 * t1 * t2 * t3 * t5 + t0 * t1 * t2 * t4 * t5 + t0 * t1 * t3 *
      t4 * t5 + t0 * t2 * t3 * t4 * t5 + t1 * t2 * t3 * t4 * t5 = -c1)
    (h6 : t0 * t1 * t2 * t3 * t4 * t5 = c0) :
    (X ^ 6 + C c5 * X ^ 5 + C c4 * X ^ 4 + C c3 * X ^ 3 + C c2 * X ^ 2 + C c1 * X ^ 1
        + C c0 * X ^ 0 : K[X])
      = (X - C t0) * (X - C t1) * (X - C t2) * (X - C t3) * (X - C t4) * (X - C t5) := by
  obtain rfl : c5 = -(t0 + t1 + t2 + t3 + t4 + t5) := by rw [h1, neg_neg]
  obtain rfl := h2
  obtain rfl : c3 = -(t0 * t1 * t2 + t0 * t1 * t3 + t0 * t1 * t4 + t0 * t1 * t5 + t0 * t2 * t3 +
      t0 * t2 * t4 +
      t0 * t2 * t5 + t0 * t3 * t4 + t0 * t3 * t5 + t0 * t4 * t5 + t1 * t2 * t3 + t1 * t2
      * t4 + t1 * t2 * t5 + t1 * t3 * t4 + t1 * t3 * t5 + t1 * t4 * t5 + t2 * t3 * t4 +
      t2 * t3 * t5 + t2 * t4 * t5 + t3 * t4 * t5) := by rw [h3, neg_neg]
  obtain rfl := h4
  obtain rfl : c1 = -(t0 * t1 * t2 * t3 * t4 + t0 * t1 * t2 * t3 * t5 + t0 * t1 * t2 * t4 * t5 +
      t0 * t1 * t3 *
      t4 * t5 + t0 * t2 * t3 * t4 * t5 + t1 * t2 * t3 * t4 * t5) := by rw [h5, neg_neg]
  obtain rfl := h6
  simp only [map_add, map_mul, map_neg]
  ring

set_option maxHeartbeats 400000000 in
-- `linear_combination` checks degree-24 coefficient identities (`theta_e6`)
/-- Each pentagon-pentagram product is a root of the `F₂₀` resolvent of the
quintic with roots `x`: the resolvent's coefficients are the signed elementary
symmetric functions of the six products (`theta_e1` … `theta_e6`, the
kernel-verified `Poly5` identities). -/
theorem resolvent_eval_theta {K : Type*} [Field K] (x : Fin 5 → K) (j : Fin 6) :
    (resolvent5 (va x) (vb x) (vc x) (vd x) (ve x)).eval (ThetaVals x j) = 0 := by
  have hfac : resolvent5 (va x) (vb x) (vc x) (vd x) (ve x)
      = ∏ i : Fin 6, (X - C (ThetaVals x i)) := by
    rw [Fin.prod_univ_six]
    refine sextic_vieta
      (theta x ![4,0,1,2,3] * theta x ![3,4,0,1,2])
      (theta x ![4,0,3,1,2] * theta x ![2,4,1,0,3])
      (theta x ![4,2,0,1,3] * theta x ![3,0,4,2,1])
      (theta x ![4,2,3,0,1] * theta x ![1,3,0,4,2])
      (theta x ![4,3,0,2,1] * theta x ![1,2,4,0,3])
      (theta x ![4,3,1,0,2] * theta x ![2,0,3,4,1])
      _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [r5c5, r5c4, r5c3, r5c2, r5c2p0, r5c2p1, r5c1, r5c1p0,
      r5c1p1, r5c1p2, r5c0, r5c0p0, r5c0p1, r5c0p2, r5c0p3, r5c0p4]
    · linear_combination theta_e1 x
    · linear_combination theta_e2 x
    · linear_combination theta_e3 x
    · linear_combination theta_e4 x
    · linear_combination theta_e5 x
    · linear_combination theta_e6 x
  rw [hfac, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)

end Main

section Criterion

/-! ### Galois group `S₅` from the resolvent

**Theorem.**  An irreducible quintic `X⁵ + aX⁴ + bX³ + cX² + dX + e` over `ℚ`
whose discriminant is not a square and whose `F₂₀` resolvent `resolvent5` has
no rational root has full Galois group `S₅` (its action on the five complex
roots is all of `Perm`).

The proof runs through the permutation representation `ρ` of the Galois group
on the five roots: `|G|` divides 120, is divisible by 5 (irreducibility) and by
2 (the discriminant quadratic subfield), so `|G| ∈ {10, 20, 30, 40, 60, 120}`;
30 and 40 are excluded because `S₅` has no subgroups of index 3 or 4, 60
because the index-2 subgroup would be `A₅`, which cannot contain the fixing
subgroup of the quadratic discriminant field, and 10 and 20 by the resolvent:
such a group normalizes some `<c>` (5-cycle), so the associated
pentagon-pentagram product is rational, hence a rational root of the
resolvent. -/

set_option maxHeartbeats 8000000 in
-- `fin_cases`/`decide` over `Perm (Fin 5)` and large normalizations need a larger budget
/-- The quintic discriminant is polynomial in the coefficients, hence commutes
with ring homomorphisms. -/
lemma disc5_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b c d e : R) :
    disc5 (f a) (f b) (f c) (f d) (f e) = f (disc5 a b c d e) := by
  simp only [disc5, map_add, map_sub, map_mul, map_pow, map_ofNat]

set_option maxHeartbeats 8000000 in
-- `fin_cases`/`decide` over `Perm (Fin 5)` and large normalizations need a larger budget
/-- The quintic resolvent is polynomial in the coefficients, hence commutes
with ring homomorphisms. -/
lemma resolvent5_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b c d e : R) :
    resolvent5 (f a) (f b) (f c) (f d) (f e) = (resolvent5 a b c d e).map f := by
  simp only [resolvent5, r5c5, r5c4, r5c3, r5c2, r5c1, r5c0,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C,
    map_add f, map_sub f, map_mul f, map_pow f, map_neg f, map_ofNat f]

/-- Degree of an element whose minimal polynomial is a given irreducible monic
polynomial divides `[K : ℚ]` (cf. `MaedaGalois4`). -/
lemma natDegree_dvd_finrank' {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {q : ℚ[X]} (hq : Irreducible q) (hmon : q.Monic) {y : K} (hy : aeval y q = 0) :
    q.natDegree ∣ Module.finrank ℚ K := by
  have hmin : minpoly ℚ y = q := (minpoly.eq_of_irreducible_of_monic hq hy hmon).symm
  rw [← hmin, ← adjoin.finrank (Algebra.IsIntegral.isIntegral y)]
  exact Module.finrank_dvd_finrank_right ℚ ℚ⟮y⟯ K

/-- The quintic resolvent is monic. -/
lemma resolvent5_monic {R : Type*} [CommRing R] (a b c d e : R) :
    (resolvent5 a b c d e).Monic := by
  unfold resolvent5
  monicity!

set_option maxHeartbeats 8000000 in
-- `fin_cases`/`decide` over `Perm (Fin 5)` and large normalizations need a larger budget
/-- **The quintic `S₅` criterion.** -/
theorem galActionHom_bijective_of_quintic {a b c d e : ℚ}
    (hirr : Irreducible (X ^ 5 + C a * X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e : ℚ[X]))
    (hdisc : ¬ IsSquare (disc5 a b c d e))
    (hres : ∀ r : ℚ, aeval r (resolvent5 a b c d e) ≠ 0) :
    Function.Bijective
      (Gal.galActionHom
        (X ^ 5 + C a * X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e : ℚ[X]) ℂ) := by
  classical
  set p : ℚ[X] := X ^ 5 + C a * X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e with hp
  have hmon : p.Monic := by rw [hp]; monicity!
  have hdeg : p.natDegree = 5 := by rw [hp]; compute_degree!
  have hsep : p.Separable := hirr.separable
  have hirrp : Irreducible p := hirr
  set K := p.SplittingField with hK
  have hφinj : Function.Injective (algebraMap ℚ K) := FaithfulSMul.algebraMap_injective ℚ K
  have hspl : Splits (p.map (algebraMap ℚ K)) := SplittingField.splits p
  have hsepK : Separable (p.map (algebraMap ℚ K)) := hsep.map
  have hne0 : p.map (algebraMap ℚ K) ≠ 0 :=
    Polynomial.map_ne_zero hmon.ne_zero
  -- the five roots, via an equiv-enumeration of the root set
  have hcard5 : Fintype.card (p.rootSet K) = 5 := by
    rw [card_rootSet_eq_natDegree (K := K) hsep hspl, hdeg]
  set s : Set K := p.rootSet K with hsd
  set ι : { x // x ∈ s } ≃ Fin 5 := Fintype.equivFinOfCardEq hcard5 with hι
  set x : Fin 5 → K := fun i => ((ι.symm i : { x // x ∈ s }) : K) with hxd
  have hx : ∀ i, x i ∈ s := fun i => (ι.symm i).property
  have hxinj : Function.Injective x := fun i j hij =>
    ι.symm.injective (Subtype.ext hij)
  have hnd : (p.map (algebraMap ℚ K)).roots.Nodup := Polynomial.nodup_roots hsepK
  have hmemroots : ∀ z : K, z ∈ (p.map (algebraMap ℚ K)).roots ↔ ∃ i : Fin 5, z = x i := by
    intro z
    constructor
    · intro hmem
      have hae : aeval z p = 0 := by
        rw [aeval_def, ← eval_map]
        exact (Polynomial.mem_roots'.mp hmem).2
      exact ⟨ι ⟨z, Polynomial.mem_rootSet'.mpr ⟨hne0, hae⟩⟩,
        (congrArg Subtype.val (Equiv.symm_apply_apply ι
          (⟨z, Polynomial.mem_rootSet'.mpr ⟨hne0, hae⟩⟩ : { w // w ∈ s }))).symm⟩
    · rintro ⟨i, rfl⟩
      refine Polynomial.mem_roots'.mpr ⟨hne0, ?_⟩
      change eval (x i) (p.map (algebraMap ℚ K)) = 0
      rw [eval_map, ← aeval_def]
      exact (Polynomial.mem_rootSet'.mp (hx i)).2
  have hrootsm : (p.map (algebraMap ℚ K)).roots = Multiset.map x Finset.univ.val := by
    refine Multiset.ext.mpr fun z => ?_
    by_cases hm : ∃ i : Fin 5, z = x i
    · obtain ⟨i, rfl⟩ := hm
      rw [Multiset.count_eq_one_of_mem hnd (hmemroots (x i) |>.mpr ⟨i, rfl⟩),
        Multiset.count_eq_one_of_mem (Multiset.Nodup.map hxinj Finset.univ.nodup)
          (Multiset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)]
    · rw [Multiset.count_eq_zero_of_notMem (fun hcon => hm (hmemroots z |>.mp hcon)),
        Multiset.count_eq_zero_of_notMem (fun hcon => hm
          (by obtain ⟨i, hi⟩ := Multiset.mem_map.mp hcon; exact ⟨i, hi.2.symm⟩))]
  have hfac : p.map (algebraMap ℚ K)
      = (X - C (x 0)) * (X - C (x 1)) * (X - C (x 2)) * (X - C (x 3)) * (X - C (x 4)) := by
    rw [hspl.eq_prod_roots_of_monic (hmon.map (algebraMap ℚ K)), hrootsm]
    simp only [Multiset.map_map, Function.comp_def, Finset.prod_map_val, Fin.prod_univ_five]
  have hmapP : p.map (algebraMap ℚ K)
      = X ^ 5 + C (algebraMap ℚ K a) * X ^ 4 + C (algebraMap ℚ K b) * X ^ 3
        + C (algebraMap ℚ K c) * X ^ 2 + C (algebraMap ℚ K d) * X
        + C (algebraMap ℚ K e) := by simp [hp]
  obtain ⟨hv1, hv2, hv3, hv4, hv5⟩ := vieta5 (hfac.symm.trans hmapP)
  -- the discriminant quadratic subfield
  set δ : K := (x 0 - x 1) * (x 0 - x 2) * (x 0 - x 3) * (x 0 - x 4) * (x 1 - x 2)
    * (x 1 - x 3) * (x 1 - x 4) * (x 2 - x 3) * (x 2 - x 4) * (x 3 - x 4) with hδdef
  have hδ2 : δ ^ 2 = algebraMap ℚ K (disc5 a b c d e) := by
    rw [hδdef, delta2_identity x, ← hv1, ← hv2, ← hv3, ← hv4, ← hv5, disc5_map]
  have hq : Irreducible (X ^ 2 - C (disc5 a b c d e) : ℚ[X]) := by
    refine irreducible_of_degree_le_three_of_not_isRoot ?_ fun r hr => hdisc ⟨r, ?_⟩
    · rw [natDegree_X_pow_sub_C]; decide
    · simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hr
      rw [← hr]; ring
  have hδroot : aeval δ (X ^ 2 - C (disc5 a b c d e) : ℚ[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hδ2, sub_self]
  have hδdeg : Module.finrank ℚ ℚ⟮δ⟯ = 2 := by
    rw [adjoin.finrank (Algebra.IsIntegral.isIntegral δ),
      (minpoly.eq_of_irreducible_of_monic hq hδroot (monic_X_pow_sub_C _ (by norm_num))).symm,
      natDegree_X_pow_sub_C]
  -- every Galois automorphism maps roots to roots
  have hgmem : ∀ (g : p.Gal) (i : Fin 5), g (x i) ∈ s := by
    intro g i
    refine Polynomial.mem_rootSet'.mpr ⟨hne0, ?_⟩
    have hxi : aeval (x i) p = 0 := (Polynomial.mem_rootSet'.mp (hx i)).2
    rw [Polynomial.aeval_algHom_apply, hxi, map_zero]
  -- the induced permutation, first as a plain function
  set σ : p.Gal → Fin 5 → Fin 5 := fun g i => ι ⟨g (x i), hgmem g i⟩ with hσdef
  have hgx : ∀ (g : p.Gal) (i : Fin 5), g (x i) = x (σ g i) := by
    intro g i
    have h1 : x (σ g i) = ((ι.symm (ι ⟨g (x i), hgmem g i⟩) : { w // w ∈ s }) : K) := rfl
    rw [h1, Equiv.symm_apply_apply]
  have hσinj : ∀ g : p.Gal, Function.Injective (σ g) := by
    intro g i j hij
    refine hxinj ((g : K ≃ₐ[ℚ] K).toEquiv.injective ?_)
    exact congrArg Subtype.val (ι.injective hij)
  set ρ : p.Gal →* Equiv.Perm (Fin 5) :=
    { toFun := fun g => Equiv.ofBijective (σ g)
        ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hσinj g, rfl⟩)
      map_one' := by
        refine Equiv.ext fun i => ?_
        change ι ⟨(1 : p.Gal) (x i), _⟩ = i
        have h1 : (⟨(1 : p.Gal) (x i), hgmem 1 i⟩ : { w // w ∈ s }) = ι.symm i :=
          Subtype.ext rfl
        rw [h1, Equiv.apply_symm_apply]
      map_mul' := by
        intro g h
        refine Equiv.ext fun i => ?_
        change ι ⟨(g * h) (x i), _⟩ = ι ⟨g (x (σ h i)), _⟩
        congr 1
        refine Subtype.ext ?_
        change (g * h) (x i) = g (x (σ h i))
        rw [show (g * h) (x i) = g (h (x i)) from rfl, hgx h i] } with hρdef
  have hgxρ : ∀ (g : p.Gal) (i : Fin 5), g (x i) = x (ρ g i) := by
    intro g i
    have h1 : x (ρ g i) = x (σ g i) := rfl
    rw [h1]
    exact hgx g i
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff ρ, eq_bot_iff]
    rintro g hg'
    have hgx' : ∀ i, g (x i) = x i := by
      intro i
      have := hgxρ g i
      rw [MonoidHom.mem_ker.mp hg', Perm.one_apply] at this
      exact this
    rw [Subgroup.mem_bot]
    refine Polynomial.Gal.ext p fun z hz => ?_
    obtain ⟨i, rfl⟩ : ∃ i, z = x i := ⟨ι ⟨z, hz⟩,
      (congrArg Subtype.val (Equiv.symm_apply_apply ι ⟨z, hz⟩)).symm⟩
    rw [hgx' i]
    rfl
  -- counting
  have hN : Nat.card p.Gal = Module.finrank ℚ K := Gal.card_of_separable hsep
  have hroot0 : aeval (x 0) p = 0 := (Polynomial.mem_rootSet'.mp (hx 0)).2
  have h5dvd : 5 ∣ Module.finrank ℚ K := hdeg ▸ natDegree_dvd_finrank' hirrp hmon hroot0
  have h2dvd : 2 ∣ Module.finrank ℚ K := by
    rw [← hδdeg]
    exact Module.finrank_dvd_finrank_right ℚ ℚ⟮δ⟯ K
  have h10 : 10 ∣ Nat.card p.Gal := by
    rw [hN]; exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 5 2) h5dvd h2dvd
  have hpos : 0 < Nat.card p.Gal := Nat.card_pos
  have : IsGalois ℚ K := IsGalois.of_separable_splitting_field hsep
  have hcard_range : Nat.card (MonoidHom.range ρ) = Nat.card p.Gal :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_fin]; rfl
  have hdvd120 : Nat.card p.Gal ∣ 120 := by
    have h := Subgroup.card_subgroup_dvd_card (MonoidHom.range ρ)
    rwa [hcard_range, h120] at h
  -- the `|G| = 60` exclusion
  have sixty_case : Nat.card p.Gal = 60 → False := by
    intro hN60
    have hidx2 : (MonoidHom.range ρ).index = 2 := by
      have h := (MonoidHom.range ρ).index_mul_card
      rw [hcard_range, hN60, h120] at h
      have hne : (MonoidHom.range ρ).index ≠ 0 := by
        exact Subgroup.index_ne_zero_of_finite
      omega
    have hrangeA : MonoidHom.range ρ = alternatingGroup (Fin 5) :=
      Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx2
    set F : Subgroup p.Gal := (ℚ⟮δ⟯ : IntermediateField ℚ K).fixingSubgroup with hFdef
    have hFcard : Nat.card F = 30 := by
      change Nat.card (ℚ⟮δ⟯ : IntermediateField ℚ K).fixingSubgroup = 30
      rw [IsGalois.card_fixingSubgroup_eq_finrank]
      have htower := Module.finrank_mul_finrank ℚ ℚ⟮δ⟯ K
      rw [hδdeg, ← hN, hN60] at htower
      omega
    have hFidx : F.index = 2 := by
      have h := F.index_mul_card
      rw [hFcard, hN60] at h
      omega
    have h3cyc : alternatingGroup (Fin 5) ≤ F.map ρ := by
      rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
      intro σ hσ
      have hσA : σ ∈ MonoidHom.range ρ :=
        hrangeA ▸ Equiv.Perm.IsThreeCycle.mem_alternatingGroup hσ
      obtain ⟨g, rfl⟩ := hσA
      have hg2 : g ^ 2 ∈ F := Subgroup.sq_mem_of_index_two hFidx g
      refine ⟨(g ^ 2) ^ 2, F.pow_mem hg2 2, ?_⟩
      have h3 : (ρ g) ^ 3 = 1 := by rw [← hσ.orderOf]; exact pow_orderOf_eq_one _
      rw [map_pow, map_pow, ← pow_mul, show (ρ g) ^ (2 * 2) = (ρ g) ^ 3 * ρ g by
        rw [← pow_succ]]
      rw [h3, one_mul]
    have hmapcard : Nat.card (F.map ρ) = 30 := by
      rw [← hFcard]
      exact Nat.card_congr (F.equivMapOfInjective ρ hinj).toEquiv.symm
    have hAcard : Nat.card (alternatingGroup (Fin 5)) = 60 := card_alternating_five rfl
    have hle' : Nat.card (alternatingGroup (Fin 5)) ≤ Nat.card (F.map ρ) :=
      Subgroup.card_le_of_le h3cyc
    omega
  -- the `|G| = 30` / `|G| = 40` exclusion
  have index34_case : Nat.card p.Gal = 30 ∨ Nat.card p.Gal = 40 → False := by
    rintro (hN | hN)
    · refine perm_no_index_three_four (H := MonoidHom.range ρ) (Fintype.card_fin 5) (Or.inr ?_)
      have h := (MonoidHom.range ρ).index_mul_card
      rw [hcard_range, hN, h120] at h
      have hne : (MonoidHom.range ρ).index ≠ 0 := by
        exact Subgroup.index_ne_zero_of_finite
      omega
    · refine perm_no_index_three_four (H := MonoidHom.range ρ) (Fintype.card_fin 5) (Or.inl ?_)
      have h := (MonoidHom.range ρ).index_mul_card
      rw [hcard_range, hN, h120] at h
      have hne : (MonoidHom.range ρ).index ≠ 0 := by
        exact Subgroup.index_ne_zero_of_finite
      omega
  -- the `|G| ∈ {10, 20}` exclusion (the resolvent step)
  have resolvent_case : Nat.card p.Gal = 10 ∨ Nat.card p.Gal = 20 → False := by
    rintro (hNcase | hNcase)
    all_goals
      exfalso
      obtain ⟨κ, hco5, hcnorm⟩ :=
        perm_order_5_normal_of_card (MonoidHom.range ρ) (by rw [hcard_range]; omega)
      have hκ5 : κ ^ 5 = 1 := by
        have h := pow_orderOf_eq_one κ
        rwa [hco5] at h
      have hκ1 : κ ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hco5
        exact absurd hco5 (by norm_num)
      set t : K := theta x ⇑κ * theta x ⇑(κ * κ) with ht
      have hfixt : ∀ g : p.Gal, g t = t := fun g => gal_fixes_theta x κ hκ5 g (ρ g)
        (hgxρ g) (hcnorm (ρ g) (MonoidHom.mem_range.mpr ⟨g, rfl⟩))
      have hbot : t ∈ (⊥ : IntermediateField ℚ K) :=
        (IsGalois.mem_bot_iff_fixed t).mpr fun σ => hfixt σ
      obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp hbot
      -- `t` is one of the six resolvent roots
      obtain ⟨j, m, hm⟩ := cycles_complete κ hκ5 hκ1
      have hκT : κ = cycPerm j ^ (m.val + 1) := Equiv.ext hm
      have htv : t = ThetaVals x j := by
        rw [ht, thetaVals_cyc x j, hκT,
          theta_pair_pow x _ (cycPerm_pow5 j).1 _ (by omega) (by have := m.isLt; omega)]
      -- `t` is a root of the resolvent
      have hRmap : (resolvent5 (va x) (vb x) (vc x) (vd x) (ve x))
          = (resolvent5 a b c d e).map (algebraMap ℚ K) := by
        rw [← hv1, ← hv2, ← hv3, ← hv4, ← hv5, resolvent5_map]
      have hrootK : ((resolvent5 a b c d e).map (algebraMap ℚ K)).eval (algebraMap ℚ K r) = 0 := by
        rw [← hRmap, hr, htv]
        exact resolvent_eval_theta x j
      refine hres r ?_
      refine hφinj ?_
      have hae : algebraMap ℚ K (aeval r (resolvent5 a b c d e))
          = aeval (algebraMap ℚ K r) ((resolvent5 a b c d e).map (algebraMap ℚ K)) := by
        refine map_aeval_eq_aeval_map (p := resolvent5 a b c d e) (a := r) ?_
        simp
      rw [hae, map_zero, Polynomial.coe_aeval_eq_eval]
      exact hrootK
  -- finish by enumerating the divisors of 120 divisible by 10
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨Gal.galActionHom_injective p ℂ, ?_⟩
  rw [show Nat.card (Equiv.Perm (p.rootSet ℂ)) = 120 from by
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _), hdeg]; norm_num]
  obtain ⟨v, hv⟩ := h10
  obtain ⟨w, hw⟩ := hdvd120
  have hv1' : 0 < v := by have := hpos; omega
  have hv12 : v ∣ 12 := by
    have h1 : 10 * (v * w) = 10 * 12 := by rw [← mul_assoc, ← hv, ← hw]
    exact ⟨w, (Nat.eq_of_mul_eq_mul_left (by norm_num) h1).symm⟩
  have hvle : v ≤ 12 := Nat.le_of_dvd (by norm_num) hv12
  interval_cases v
  · exact (resolvent_case (Or.inl (by omega))).elim
  · exact (resolvent_case (Or.inr (by omega))).elim
  · exact (index34_case (Or.inl (by omega))).elim
  · exact (index34_case (Or.inr (by omega))).elim
  · omega
  · exact (sixty_case (by omega)).elim
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

end Criterion

end MaedaGalois
