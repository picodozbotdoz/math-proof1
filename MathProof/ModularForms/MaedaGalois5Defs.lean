import MathProof.ModularForms.MaedaDim5
import MathProof.ModularForms.MaedaGalois
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

-- heavy polynomial normalizations below need generous budgets
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

/-!
# Subgroup structure of `S₅`, and Galois group `S₅` for the dim-5 weights

Group-theoretic prerequisites for the quintic `S₅` criterion:

* `perm_normal_cases` — a normal subgroup of `Equiv.Perm α` (`card α = 5`) is
  `⊤`, `alternatingGroup α`, or has at most 2 elements (the last case via
  `alternatingGroup.isSimpleGroup` and the sign homomorphism);
* `perm_no_index_three_four` — `S₅` has no subgroups of index 3 or 4 (the
  normal core's index divides `index!`, and each normal case contradicts the
  sizes);
* `alternating_no_index_two` — `A₅` has no subgroup of index 2 (index 2 is
  normal; `A₅` is simple).
-/

open Equiv Subgroup Polynomial Module IntermediateField

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

namespace MaedaGalois

section S5

variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "SG" => Equiv.Perm α

lemma nontrivial_of_card_five (hα : Fintype.card α = 5) : Nontrivial α := by
  rw [← Fintype.one_lt_card_iff_nontrivial, hα]; norm_num

/-- `S₅` has 120 elements. -/
lemma card_perm_five (hα : Fintype.card α = 5) : Nat.card SG = 120 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, hα]; norm_num

/-- `A₅` (on five letters) has 60 elements. -/
lemma card_alternating_five (hα : Fintype.card α = 5) :
    Nat.card (alternatingGroup α) = 60 := by
  haveI : Nontrivial α := nontrivial_of_card_five hα
  have h := two_mul_nat_card_alternatingGroup (α := α)
  rw [card_perm_five hα] at h
  omega

/-- A normal subgroup of `S₅` is `⊤`, `A₅`, or tiny (at most two elements). -/
theorem perm_normal_cases (hα : Fintype.card α = 5) {N : Subgroup SG} (hN : N.Normal) :
    N = ⊤ ∨ N = alternatingGroup α ∨ Nat.card N ≤ 2 := by
  haveI hA5n : (alternatingGroup α).Normal := alternatingGroup.normal
  have hA5s : IsSimpleGroup (alternatingGroup α) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, hα])
  have hMA : (N.subgroupOf (alternatingGroup α)).Normal := by
    constructor
    intro g hg a
    refine Subgroup.mem_subgroupOf.mpr ?_
    show ((a * g * a⁻¹ : ↥(alternatingGroup α)) : SG) ∈ N
    have hco : ((a * g * a⁻¹ : ↥(alternatingGroup α)) : SG)
        = (a : SG) * (g : SG) * (a : SG)⁻¹ := by
      push_cast; ring
    rw [hco]
    exact hN.conj_mem _ (Subgroup.mem_subgroupOf.mp hg) _
  rcases hA5s.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup α)) with hb | ht
  · -- `N ⊓ A₅ = ⊥`: sign is injective on `N`, so `|N| ≤ 2`.
    refine Or.inr (Or.inr ?_)
    have hbot : ∀ z : SG, z ∈ N → z ∈ alternatingGroup α → z = 1 := by
      intro z hzN hzA
      have hmem : (⟨z, hzA⟩ : ↥(alternatingGroup α))
          ∈ N.subgroupOf (alternatingGroup α) := Subgroup.mem_subgroupOf.mpr hzN
      rw [hb, Subgroup.mem_bot] at hmem
      simpa using congrArg Subtype.val hmem
    have hker : (MonoidHom.comp Equiv.Perm.sign N.subtype).ker = ⊥ := by
      refine eq_bot_iff.mpr fun g hg => ?_
      rw [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype] at hg
      exact Subtype.ext (hbot _ g.2 (Equiv.Perm.mem_alternatingGroup.mpr hg))
    have hinj : Function.Injective (MonoidHom.comp Equiv.Perm.sign N.subtype) :=
      (MonoidHom.ker_eq_bot_iff _).mp hker
    have h2 : Nat.card (ℤˣ) = 2 := by rw [Nat.card_eq_fintype_card]; decide
    have hle := Nat.card_le_card_of_injective
      (fun g : N => (MonoidHom.comp Equiv.Perm.sign N.subtype) g) hinj
    simpa [h2] using hle
  · -- `A₅ ≤ N`: `|N| ∣ 120` and `|N| ≥ 60` force `|N| ∈ {60, 120}`.
    have hle : alternatingGroup α ≤ N := by
      intro g hg
      exact Subgroup.mem_subgroupOf.mp
        (by rw [ht]; trivial : (⟨g, hg⟩ : ↥(alternatingGroup α))
          ∈ N.subgroupOf (alternatingGroup α))
    have hdvd : Nat.card N ∣ Nat.card SG := Subgroup.card_subgroup_dvd_card N
    rw [card_perm_five hα] at hdvd
    have hge : 60 ≤ Nat.card N := by
      rw [← card_alternating_five hα]
      exact Subgroup.card_le_of_le hle
    obtain ⟨k, hk⟩ := hdvd
    have hk12 : k = 1 ∨ k = 2 := by
      rcases Nat.lt_or_ge k 3 with h3 | h3
      · interval_cases k <;> omega
      · exfalso
        have h1 : Nat.card N * 3 ≤ Nat.card N * k := Nat.mul_le_mul_left _ h3
        have h2 : (180 : ℕ) ≤ Nat.card N * 3 := by
          have := Nat.mul_le_mul_left ((3 : ℕ)) hge
          calc (180 : ℕ) = 3 * 60 := rfl
            _ ≤ 3 * Nat.card N := Nat.mul_le_mul_left _ hge
            _ = Nat.card N * 3 := Nat.mul_comm _ _
        nlinarith [hk, h1, h2]
    rcases hk12 with h | h
    · -- k = 1 : |N| = 120 : N = ⊤
      rw [h, mul_one] at hk
      left
      have htop : Nat.card ↥(⊤ : Subgroup SG) = 120 :=
        (Nat.card_congr (Subgroup.topEquiv.toEquiv : ↥(⊤ : Subgroup SG) ≃ SG)).trans
          (card_perm_five hα)
      refine Subgroup.eq_of_le_of_card_ge le_top ?_
      rw [htop, ← hk]
    · -- k = 2 : |N| = 60 : N = A₅
      rw [h, mul_two] at hk
      have hN : Nat.card N = 60 := by omega
      right; left
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      rw [card_alternating_five hα, hN]

/-- `S₅` has no subgroups of index 3 or 4. -/
theorem perm_no_index_three_four (hα : Fintype.card α = 5) {H : Subgroup SG}
    (hH : H.index = 3 ∨ H.index = 4) : False := by
  have hdvd : H.normalCore.index ∣ Nat.factorial H.index :=
    Subgroup.index_normalCore_dvd_factorial_index H
  have hncle : H.normalCore ≤ H := H.normalCore_le
  have hncn : H.normalCore.Normal := H.normalCore_normal
  have hcardH : H.index * Nat.card H = Nat.card SG := Subgroup.index_mul_card H
  rw [card_perm_five hα] at hcardH
  rcases perm_normal_cases hα hncn with ht | hA | hsmall
  · rw [ht] at hncle
    rw [eq_top_iff.mpr hncle, Subgroup.index_top] at hH
    simp at hH
  · rw [hA] at hncle
    have h60 : 60 ≤ Nat.card H := by
      rw [← card_alternating_five hα]
      exact Subgroup.card_le_of_le hncle
    rcases hH with h | h <;> rw [h] at hcardH <;> omega
  · -- `|normalCore| ≤ 2` but its index is `≥ 60` and divides `3!` or `4!`
    haveI : Nonempty ↥H.normalCore := ⟨1, H.normalCore.one_mem⟩
    have hpos : 0 < Nat.card H.normalCore := Nat.card_pos
    have hidx : H.normalCore.index * Nat.card H.normalCore = 120 := by
      rw [Subgroup.index_mul_card, card_perm_five hα]
    have hbig : H.normalCore.index ≥ 60 := by
      rcases (by omega : Nat.card H.normalCore = 1 ∨ Nat.card H.normalCore = 2) with h | h
      · rw [h, mul_one] at hidx; omega
      · rw [h, mul_two] at hidx; omega
    rcases hH with h | h <;> rw [h] at hdvd <;> norm_num at hdvd
    all_goals have hle := Nat.le_of_dvd (by omega) hdvd
    all_goals omega

/-- `A₅` has no subgroup of index 2. -/
theorem alternating_no_index_two (hα : Fintype.card α = 5)
    {A : Subgroup (alternatingGroup α)} (hA : A.index = 2) : False := by
  have hAsimple : IsSimpleGroup (alternatingGroup α) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, hα])
  have hn : A.Normal := normal_of_index_eq_two hA
  rcases hAsimple.eq_bot_or_eq_top_of_normal A with h | h
  · rw [h, Subgroup.index_bot, card_alternating_five hα] at hA
    norm_num at hA
  · rw [h] at hA
    simp at hA

end S5


section Quintic

/-- A multiset of cardinality five is a five-fold insert. -/
lemma multiset_card_eq_five {M : Type*} {s : Multiset M} (h : Multiset.card s = 5) :
    ∃ a b c d e, s = {a, b, c, d, e} := by
  refine Quot.inductionOn s (fun l h => ?_) h
  have h5 : l.length = 5 := by simpa using h
  let [a, b, c, d, e] := l
  exact ⟨a, b, c, d, e, rfl⟩

end Quintic

section Resolvent

/-! ### The `F₂₀` resolvent of a quintic -/

/-- The discriminant of `X⁵ + aX⁴ + bX³ + cX² + dX + e` (as a polynomial in the
coefficients; `delta2_identity` proves it equals `∏_{i<j} (xᵢ - xⱼ)²`). -/
def disc5 {R : Type*} [CommRing R] (a b c d e : R) : R :=
  a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 - 4 * a ^ 2 * b ^ 2 * c ^ 3 * e - 4 * a ^ 2 * b ^ 3 * d ^ 3
  + 18 * a ^ 2 * b ^ 3 * c * d * e - 27 * a ^ 2 * b ^ 4 * e ^ 2 - 4 * a ^ 3 * c ^ 3 * d ^ 2
  + 16 * a ^ 3 * c ^ 4 * e + 18 * a ^ 3 * b * c * d ^ 3 - 80 * a ^ 3 * b * c ^ 2 * d * e
  - 6 * a ^ 3 * b ^ 2 * d ^ 2 * e + 144 * a ^ 3 * b ^ 2 * c * e ^ 2 - 27 * a ^ 4 * d ^ 4
  + 144 * a ^ 4 * c * d ^ 2 * e - 128 * a ^ 4 * c ^ 2 * e ^ 2 - 192 * a ^ 4 * b * d * e ^ 2
  + 256 * a ^ 5 * e ^ 3 - 4 * b ^ 3 * c ^ 2 * d ^ 2 + 16 * b ^ 3 * c ^ 3 * e
  + 16 * b ^ 4 * d ^ 3 - 72 * b ^ 4 * c * d * e + 108 * b ^ 5 * e ^ 2
  + 18 * a * b * c ^ 3 * d ^ 2 - 72 * a * b * c ^ 4 * e - 80 * a * b ^ 2 * c * d ^ 3
  + 356 * a * b ^ 2 * c ^ 2 * d * e + 24 * a * b ^ 3 * d ^ 2 * e - 630 * a * b ^ 3 * c * e ^ 2
  - 6 * a ^ 2 * c ^ 2 * d ^ 3 + 24 * a ^ 2 * c ^ 3 * d * e + 144 * a ^ 2 * b * d ^ 4
  - 746 * a ^ 2 * b * c * d ^ 2 * e + 560 * a ^ 2 * b * c ^ 2 * e ^ 2
  + 1020 * a ^ 2 * b ^ 2 * d * e ^ 2 - 36 * a ^ 3 * d ^ 3 * e + 160 * a ^ 3 * c * d * e ^ 2
  - 1600 * a ^ 3 * b * e ^ 3 - 27 * c ^ 4 * d ^ 2 + 108 * c ^ 5 * e + 144 * b * c ^ 2 * d ^ 3
  - 630 * b * c ^ 3 * d * e - 128 * b ^ 2 * d ^ 4 + 560 * b ^ 2 * c * d ^ 2 * e
  + 825 * b ^ 2 * c ^ 2 * e ^ 2 - 900 * b ^ 3 * d * e ^ 2 - 192 * a * c * d ^ 4
  + 1020 * a * c ^ 2 * d ^ 2 * e - 900 * a * c ^ 3 * e ^ 2 + 160 * a * b * d ^ 3 * e
  - 2050 * a * b * c * d * e ^ 2 + 2250 * a * b ^ 2 * e ^ 3 - 50 * a ^ 2 * d ^ 2 * e ^ 2
  + 2000 * a ^ 2 * c * e ^ 3 + 256 * d ^ 5 - 1600 * c * d ^ 3 * e + 2250 * c ^ 2 * d * e ^ 2
  + 2000 * b * d ^ 2 * e ^ 2 - 3750 * b * c * e ^ 3 - 2500 * a * d * e ^ 3 + 3125 * e ^ 4

/-- The `F₂₀` sextic resolvent of `X⁵ + aX⁴ + bX³ + cX² + dX + e`: the monic
sextic whose roots are the six values `θ(c) * θ(c²)` (`c` a 5-cycle, `θ(c) =
∑ᵥ xᵢ x_{c v}` — one per 5-cycle subgroup).  `resolvent_eval_theta` proves each
pentagon product is a root.  A rational root certifies the Galois group fixes a
pentagon structure, i.e. lies in `F₂₀`. -/
noncomputable def resolvent5 {R : Type*} [CommRing R] (a b c d e : R) : R[X] :=
  X ^ 6
    + C (  -4 * a * c + 10 * d) * X ^ 5
    + C (  6 * a ^ 2 * c ^ 2 + 2 * a ^ 2 * b * d - 8 * a ^ 3 * e + 2 * b * c ^ 2 - 6 * b ^ 2 * d
  - 34 * a * c * d + 30 * a * b * e + 55 * d ^ 2 - 50 * c * e) * X ^ 4
    + C (  -4 * a ^ 3 * c ^ 3 - 6 * a ^ 3 * b * c * d + 2 * a ^ 3 * b ^ 2 * e + 2 * a ^ 4 * d ^ 2
  + 16 * a ^ 4 * c * e - 6 * a * b * c ^ 3 + 19 * a * b ^ 2 * c * d - 9 * a * b ^ 3 * e
  + 42 * a ^ 2 * c ^ 2 * d + 3 * a ^ 2 * b * d ^ 2 - 54 * a ^ 2 * b * c * e - 52 * a ^ 3 * d * e
  + 2 * c ^ 4 + 3 * b * c ^ 2 * d - 32 * b ^ 2 * d ^ 2 + 15 * b ^ 2 * c * e
  - 128 * a * c * d ^ 2 + 80 * a * c ^ 2 * e + 170 * a * b * d * e + 50 * a ^ 2 * e ^ 2
  + 140 * d ^ 3 - 200 * c * d * e - 125 * b * e ^ 2) * X ^ 3
    + C (  a ^ 4 * c ^ 4 + 6 * a ^ 4 * b * c ^ 2 * d + a ^ 4 * b ^ 2 * d ^ 2 - 4 * a ^ 4 * b ^ 2 * c * e
  - 4 * a ^ 5 * c * d ^ 2 - 8 * a ^ 5 * c ^ 2 * e - 8 * a ^ 5 * b * d * e + 16 * a ^ 6 * e ^ 2
  + 6 * a ^ 2 * b * c ^ 4 - 18 * a ^ 2 * b ^ 2 * c ^ 2 * d - 6 * a ^ 2 * b ^ 3 * d ^ 2
  + 18 * a ^ 2 * b ^ 3 * c * e - 22 * a ^ 3 * c ^ 3 * d - 10 * a ^ 3 * b * c * d ^ 2
  + 10 * a ^ 3 * b * c ^ 2 * e + 64 * a ^ 3 * b ^ 2 * d * e + 10 * a ^ 4 * d ^ 3
  + 80 * a ^ 4 * c * d * e - 120 * a ^ 4 * b * e ^ 2 + b ^ 2 * c ^ 4 - 6 * b ^ 3 * c ^ 2 * d
  + 9 * b ^ 4 * d ^ 2 - 4 * a * c ^ 5 - 10 * a * b * c ^ 3 * d + 81 * a * b ^ 2 * c * d ^ 2
  - 135 * a * b ^ 3 * d * e + 95 * a ^ 2 * c ^ 2 * d ^ 2 - 10 * a ^ 2 * c ^ 3 * e
  - 5 * a ^ 2 * b * d ^ 3 - 270 * a ^ 2 * b * c * d * e + 225 * a ^ 2 * b ^ 2 * e ^ 2
  - 180 * a ^ 3 * d ^ 2 * e + 100 * a ^ 3 * c * e ^ 2 + 10 * c ^ 4 * d - 5 * b * c ^ 2 * d ^ 2
  - 50 * b * c ^ 3 * e - 100 * b ^ 2 * d ^ 3 + 225 * b ^ 2 * c * d * e - 180 * a * c * d ^ 3
  + 150 * a * c ^ 2 * d * e + 550 * a * b * d ^ 2 * e - 500 * a * b * c * e ^ 2
  + 250 * a ^ 2 * d * e ^ 2 + 175 * d ^ 4 - 500 * c * d ^ 2 * e + 625 * c ^ 2 * e ^ 2
  - 625 * b * d * e ^ 2) * X ^ 2
    + C (  -2 * a ^ 5 * b * c ^ 3 * d - 2 * a ^ 5 * b ^ 2 * c * d ^ 2 + 2 * a ^ 5 * b ^ 2 * c ^ 2 * e
  + 2 * a ^ 5 * b ^ 3 * d * e + 2 * a ^ 6 * c ^ 2 * d ^ 2 + 2 * a ^ 6 * b * d ^ 3
  + 8 * a ^ 6 * b * c * d * e - 8 * a ^ 6 * b ^ 2 * e ^ 2 - 8 * a ^ 7 * d ^ 2 * e
  - 2 * a ^ 3 * b * c ^ 5 + 3 * a ^ 3 * b ^ 2 * c ^ 3 * d + 13 * a ^ 3 * b ^ 3 * c * d ^ 2
  - 7 * a ^ 3 * b ^ 3 * c ^ 2 * e - 15 * a ^ 3 * b ^ 4 * d * e + 4 * a ^ 4 * c ^ 4 * d
  + 13 * a ^ 4 * b * c ^ 2 * d ^ 2 + 14 * a ^ 4 * b * c ^ 3 * e - 13 * a ^ 4 * b ^ 2 * d ^ 3
  - 66 * a ^ 4 * b ^ 2 * c * d * e + 66 * a ^ 4 * b ^ 3 * e ^ 2 - 14 * a ^ 5 * c * d ^ 3
  - 28 * a ^ 5 * c ^ 2 * d * e + 46 * a ^ 5 * b * d ^ 2 * e - 24 * a ^ 5 * b * c * e ^ 2
  + 48 * a ^ 6 * d * e ^ 2 - 2 * a * b ^ 2 * c ^ 5 + 13 * a * b ^ 3 * c ^ 3 * d
  - 21 * a * b ^ 4 * c * d ^ 2 - 9 * a * b ^ 4 * c ^ 2 * e + 27 * a * b ^ 5 * d * e
  + 2 * a ^ 2 * c ^ 6 + 13 * a ^ 2 * b * c ^ 4 * d - 76 * a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2
  - 13 * a ^ 2 * b ^ 2 * c ^ 3 * e + 15 * a ^ 2 * b ^ 3 * d ^ 3
  + 183 * a ^ 2 * b ^ 3 * c * d * e - 162 * a ^ 2 * b ^ 4 * e ^ 2 - 30 * a ^ 3 * c ^ 3 * d ^ 2
  - 12 * a ^ 3 * c ^ 4 * e + 39 * a ^ 3 * b * c * d ^ 3 + 4 * a ^ 3 * b * c ^ 2 * d * e
  - 17 * a ^ 3 * b ^ 2 * d ^ 2 * e + 124 * a ^ 3 * b ^ 2 * c * e ^ 2 + 3 * a ^ 4 * d ^ 4
  + 170 * a ^ 4 * c * d ^ 2 * e + 2 * a ^ 4 * c ^ 2 * e ^ 2 - 402 * a ^ 4 * b * d * e ^ 2
  + 56 * a ^ 5 * e ^ 3 + 2 * b * c ^ 6 - 13 * b ^ 2 * c ^ 4 * d + 15 * b ^ 3 * c ^ 2 * d ^ 2
  + 31 * b ^ 3 * c ^ 3 * e + 22 * b ^ 4 * d ^ 3 - 117 * b ^ 4 * c * d * e + 108 * b ^ 5 * e ^ 2
  - 14 * a * c ^ 5 * d + 39 * a * b * c ^ 3 * d ^ 2 - 12 * a * b * c ^ 4 * e
  + 33 * a * b ^ 2 * c * d ^ 3 + 51 * a * b ^ 2 * c ^ 2 * d * e - 201 * a * b ^ 3 * d ^ 2 * e
  - 180 * a * b ^ 3 * c * e ^ 2 + 30 * a ^ 2 * c ^ 2 * d ^ 3 + 114 * a ^ 2 * c ^ 3 * d * e
  + 29 * a ^ 2 * b * d ^ 4 - 541 * a ^ 2 * b * c * d ^ 2 * e + 35 * a ^ 2 * b * c ^ 2 * e ^ 2
  + 1045 * a ^ 2 * b ^ 2 * d * e ^ 2 - 176 * a ^ 3 * d ^ 3 * e - 90 * a ^ 3 * c * d * e ^ 2
  - 350 * a ^ 3 * b * e ^ 3 + 3 * c ^ 4 * d ^ 2 + 58 * c ^ 5 * e + 29 * b * c ^ 2 * d ^ 3
  - 405 * b * c ^ 3 * d * e - 128 * b ^ 2 * d ^ 4 + 685 * b ^ 2 * c * d ^ 2 * e
  + 325 * b ^ 2 * c ^ 2 * e ^ 2 - 525 * b ^ 3 * d * e ^ 2 - 92 * a * c * d ^ 4
  + 320 * a * c ^ 2 * d ^ 2 * e - 400 * a * c ^ 3 * e ^ 2 + 310 * a * b * d ^ 3 * e
  - 925 * a * b * c * d * e ^ 2 + 375 * a * b ^ 2 * e ^ 3 + 700 * a ^ 2 * d ^ 2 * e ^ 2
  + 750 * a ^ 2 * c * e ^ 3 + 106 * d ^ 5 - 600 * c * d ^ 3 * e + 1000 * c ^ 2 * d * e ^ 2
  + 125 * b * d ^ 2 * e ^ 2 - 625 * b * c * e ^ 3 - 2500 * a * d * e ^ 3 + 3125 * e ^ 4) * X ^ 1
    + C (  a ^ 6 * b ^ 2 * c ^ 2 * d ^ 2 - 2 * a ^ 6 * b ^ 3 * c * d * e + a ^ 6 * b ^ 4 * e ^ 2
  - 2 * a ^ 7 * b * c * d ^ 3 + 2 * a ^ 7 * b ^ 2 * d ^ 2 * e + a ^ 8 * d ^ 4
  + 2 * a ^ 4 * b ^ 2 * c ^ 4 * d - 7 * a ^ 4 * b ^ 3 * c ^ 2 * d ^ 2
  - 2 * a ^ 4 * b ^ 3 * c ^ 3 * e + 16 * a ^ 4 * b ^ 4 * c * d * e - 9 * a ^ 4 * b ^ 5 * e ^ 2
  - 6 * a ^ 5 * b * c ^ 3 * d ^ 2 + 14 * a ^ 5 * b ^ 2 * c * d ^ 3
  - 2 * a ^ 5 * b ^ 2 * c ^ 2 * d * e - 16 * a ^ 5 * b ^ 3 * d ^ 2 * e
  + 6 * a ^ 5 * b ^ 3 * c * e ^ 2 + 4 * a ^ 6 * c ^ 2 * d ^ 3 - 7 * a ^ 6 * b * d ^ 4
  + 18 * a ^ 6 * b * c * d ^ 2 * e - 12 * a ^ 6 * b ^ 2 * d * e ^ 2 - 12 * a ^ 7 * d ^ 3 * e
  + a ^ 2 * b ^ 2 * c ^ 6 - 7 * a ^ 2 * b ^ 3 * c ^ 4 * d + 12 * a ^ 2 * b ^ 4 * c ^ 2 * d ^ 2
  + 10 * a ^ 2 * b ^ 4 * c ^ 3 * e + a ^ 2 * b ^ 5 * d ^ 3 - 36 * a ^ 2 * b ^ 5 * c * d * e
  + 27 * a ^ 2 * b ^ 6 * e ^ 2 - 6 * a ^ 3 * b * c ^ 5 * d + 29 * a ^ 3 * b ^ 2 * c ^ 3 * d ^ 2
  - 8 * a ^ 3 * b ^ 2 * c ^ 4 * e - 27 * a ^ 3 * b ^ 3 * c * d ^ 3
  + a ^ 3 * b ^ 3 * c ^ 2 * d * e + 31 * a ^ 3 * b ^ 4 * d ^ 2 * e
  - 48 * a ^ 3 * b ^ 4 * c * e ^ 2 + 6 * a ^ 4 * c ^ 4 * d ^ 2 - 23 * a ^ 4 * b * c ^ 2 * d ^ 3
  + 44 * a ^ 4 * b * c ^ 3 * d * e + 17 * a ^ 4 * b ^ 2 * d ^ 4
  - 102 * a ^ 4 * b ^ 2 * c * d ^ 2 * e + 21 * a ^ 4 * b ^ 2 * c ^ 2 * e ^ 2
  + 122 * a ^ 4 * b ^ 3 * d * e ^ 2 + 2 * a ^ 5 * c * d ^ 4 - 44 * a ^ 5 * c ^ 2 * d ^ 2 * e
  + 62 * a ^ 5 * b * d ^ 3 * e - 86 * a ^ 5 * b * c * d * e ^ 2 - 14 * a ^ 5 * b ^ 2 * e ^ 3
  + 86 * a ^ 6 * d ^ 2 * e ^ 2 + b ^ 5 * c ^ 2 * d ^ 2 - 4 * b ^ 5 * c ^ 3 * e
  - 4 * b ^ 6 * d ^ 3 + 18 * b ^ 6 * c * d * e - 27 * b ^ 7 * e ^ 2 - 2 * a * b * c ^ 7
  + 14 * a * b ^ 2 * c ^ 5 * d - 27 * a * b ^ 3 * c ^ 3 * d ^ 2 - 6 * a * b ^ 3 * c ^ 4 * e
  + 13 * a * b ^ 4 * c * d ^ 3 - 5 * a * b ^ 4 * c ^ 2 * d * e + 3 * a * b ^ 5 * d ^ 2 * e
  + 90 * a * b ^ 5 * c * e ^ 2 + 4 * a ^ 2 * c ^ 6 * d - 23 * a ^ 2 * b * c ^ 4 * d ^ 2
  + 26 * a ^ 2 * b * c ^ 5 * e + 29 * a ^ 2 * b ^ 2 * c ^ 2 * d ^ 3
  - 87 * a ^ 2 * b ^ 2 * c ^ 3 * d * e - 29 * a ^ 2 * b ^ 3 * d ^ 4
  + 189 * a ^ 2 * b ^ 3 * c * d ^ 2 * e - 5 * a ^ 2 * b ^ 3 * c ^ 2 * e ^ 2
  - 345 * a ^ 2 * b ^ 4 * d * e ^ 2 + 4 * a ^ 3 * c ^ 3 * d ^ 3 - 52 * a ^ 3 * c ^ 4 * d * e
  + 3 * a ^ 3 * b * c * d ^ 4 + 108 * a ^ 3 * b * c ^ 2 * d ^ 2 * e
  - 110 * a ^ 3 * b * c ^ 3 * e ^ 2 - 59 * a ^ 3 * b ^ 2 * d ^ 3 * e
  + 280 * a ^ 3 * b ^ 2 * c * d * e ^ 2 + 50 * a ^ 3 * b ^ 3 * e ^ 3 - 10 * a ^ 4 * d ^ 5
  + 38 * a ^ 4 * c * d ^ 3 * e + 220 * a ^ 4 * c ^ 2 * d * e ^ 2
  - 420 * a ^ 4 * b * d ^ 2 * e ^ 2 + 150 * a ^ 4 * b * c * e ^ 3 - 300 * a ^ 5 * d * e ^ 3
  + c ^ 8 - 7 * b * c ^ 6 * d + 17 * b ^ 2 * c ^ 4 * d ^ 2 - 12 * b ^ 2 * c ^ 5 * e
  - 29 * b ^ 3 * c ^ 2 * d ^ 3 + 105 * b ^ 3 * c ^ 3 * d * e + 33 * b ^ 4 * d ^ 4
  - 155 * b ^ 4 * c * d ^ 2 * e - 150 * b ^ 4 * c ^ 2 * e ^ 2 + 225 * b ^ 5 * d * e ^ 2
  + 2 * a * c ^ 5 * d ^ 2 - 20 * a * c ^ 6 * e + 3 * a * b * c ^ 3 * d ^ 3
  + 40 * a * b * c ^ 4 * d * e + 11 * a * b ^ 2 * c * d ^ 4
  - 115 * a * b ^ 2 * c ^ 2 * d ^ 2 * e + 200 * a * b ^ 2 * c ^ 3 * e ^ 2
  - 15 * a * b ^ 3 * d ^ 3 * e - 19 * a ^ 2 * c ^ 2 * d ^ 4 + 80 * a ^ 2 * c ^ 3 * d ^ 2 * e
  + 150 * a ^ 2 * c ^ 4 * e ^ 2 + 35 * a ^ 2 * b * d ^ 5 - 185 * a ^ 2 * b * c * d ^ 3 * e
  - 475 * a ^ 2 * b * c ^ 2 * d * e ^ 2 + 500 * a ^ 2 * b ^ 2 * d ^ 2 * e ^ 2
  - 500 * a ^ 2 * b ^ 2 * c * e ^ 3 + 60 * a ^ 3 * d ^ 4 * e - 250 * a ^ 3 * c * d ^ 2 * e ^ 2
  - 500 * a ^ 3 * c ^ 2 * e ^ 3 + 1250 * a ^ 3 * b * d * e ^ 3 + 625 * a ^ 4 * e ^ 4
  - 10 * c ^ 4 * d ^ 3 + 50 * c ^ 5 * d * e + 35 * b * c ^ 2 * d ^ 4
  - 175 * b * c ^ 3 * d ^ 2 * e - 125 * b * c ^ 4 * e ^ 2 - 54 * b ^ 2 * d ^ 5
  + 275 * b ^ 2 * c * d ^ 3 * e + 250 * b ^ 2 * c ^ 2 * d * e ^ 2 - 375 * b ^ 3 * d ^ 2 * e ^ 2
  - 10 * a * c * d ^ 5 + 150 * a * c ^ 2 * d ^ 3 * e - 500 * a * c ^ 3 * d * e ^ 2
  - 100 * a * b * d ^ 4 * e + 375 * a * b * c * d ^ 2 * e ^ 2 + 1250 * a * b * c ^ 2 * e ^ 3
  - 625 * a * b ^ 2 * d * e ^ 3 - 250 * a ^ 2 * d ^ 3 * e ^ 2 + 1250 * a ^ 2 * c * d * e ^ 3
  - 3125 * a ^ 2 * b * e ^ 4 + 25 * d ^ 6 - 250 * c * d ^ 4 * e + 625 * c ^ 2 * d ^ 2 * e ^ 2
  + 625 * b * d ^ 3 * e ^ 2 - 3125 * b * c * d * e ^ 3 + 3125 * b ^ 2 * e ^ 4) * X ^ 0

/-- The Vieta coefficient functions of five quantities `x 0, …, x 4`. -/
noncomputable def va {K : Type*} [CommRing K] (x : Fin 5 → K) : K :=
  -(x 0 + x 1 + x 2 + x 3 + x 4)

/-- See `va`. -/
noncomputable def vb {K : Type*} [CommRing K] (x : Fin 5 → K) : K :=
  x 0 * x 1 + x 0 * x 2 + x 0 * x 3 + x 0 * x 4 + x 1 * x 2 + x 1 * x 3 + x 1 * x 4
    + x 2 * x 3 + x 2 * x 4 + x 3 * x 4

/-- See `va`. -/
noncomputable def vc {K : Type*} [CommRing K] (x : Fin 5 → K) : K :=
  -(x 0 * x 1 * x 2 + x 0 * x 1 * x 3 + x 0 * x 1 * x 4 + x 0 * x 2 * x 3
    + x 0 * x 2 * x 4 + x 0 * x 3 * x 4 + x 1 * x 2 * x 3 + x 1 * x 2 * x 4
    + x 1 * x 3 * x 4 + x 2 * x 3 * x 4)

/-- See `va`. -/
noncomputable def vd {K : Type*} [CommRing K] (x : Fin 5 → K) : K :=
  x 0 * x 1 * x 2 * x 3 + x 0 * x 1 * x 2 * x 4 + x 0 * x 1 * x 3 * x 4
    + x 0 * x 2 * x 3 * x 4 + x 1 * x 2 * x 3 * x 4

/-- See `va`. -/
noncomputable def ve {K : Type*} [CommRing K] (x : Fin 5 → K) : K :=
  -(x 0 * x 1 * x 2 * x 3 * x 4)

/-- The pentagon sum of the cycle `c`: `∑ᵥ x ᵥ * x (c v)`. -/
noncomputable def theta {K : Type*} [CommRing K] (x : Fin 5 → K)
    (c : Fin 5 → Fin 5) : K :=
  ∑ v : Fin 5, x v * x (c v)

/-- The six 5-cycle subgroup representatives of `Fin 5` (as index maps). -/
def cyclesTable : Fin 6 → (Fin 5 → Fin 5) :=
![![4, 0, 1, 2, 3],
  ![4, 0, 3, 1, 2],
  ![4, 2, 0, 1, 3],
  ![4, 2, 3, 0, 1],
  ![4, 3, 0, 2, 1],
  ![4, 3, 1, 0, 2]]

/-- The six pentagon-pentagram products, one per 5-cycle subgroup. -/
noncomputable def ThetaVals {K : Type*} [CommRing K] (x : Fin 5 → K) :
    Fin 6 → K :=
![theta x ![4, 0, 1, 2, 3] * theta x ![3, 4, 0, 1, 2],
  theta x ![4, 0, 3, 1, 2] * theta x ![2, 4, 1, 0, 3],
  theta x ![4, 2, 0, 1, 3] * theta x ![3, 0, 4, 2, 1],
  theta x ![4, 2, 3, 0, 1] * theta x ![1, 3, 0, 4, 2],
  theta x ![4, 3, 0, 2, 1] * theta x ![1, 2, 4, 0, 3],
  theta x ![4, 3, 1, 0, 2] * theta x ![2, 0, 3, 4, 1]]

/-- **Vieta for quintics.** -/
lemma vieta5 {K : Type*} [Field K] {x : Fin 5 → K} {a b c d e : K}
    (h : (X - C (x 0)) * (X - C (x 1)) * (X - C (x 2)) * (X - C (x 3)) * (X - C (x 4))
      = X ^ 5 + C a * X ^ 4 + C b * X ^ 3 + C c * X ^ 2 + C d * X + C e) :
    a = va x ∧ b = vb x ∧ c = vc x ∧ d = vd x ∧ e = ve x := by
  have hprod : (X - C (x 0)) * (X - C (x 1)) * (X - C (x 2)) * (X - C (x 3))
        * (X - C (x 4))
      = X ^ 5 + C (va x) * X ^ 4 + C (vb x) * X ^ 3 + C (vc x) * X ^ 2
        + C (vd x) * X + C (ve x) := by
    simp only [va, vb, vc, vd, ve, map_neg, map_add, map_mul]
    ring
  rw [hprod] at h
  have e4 : a = va x := by
    have h4 := congrArg (fun P : K[X] => P.coeff 4) h
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at h4
    norm_num at h4
    exact h4.symm
  have e3 : b = vb x := by
    have h3 := congrArg (fun P : K[X] => P.coeff 3) h
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at h3
    norm_num at h3
    exact h3.symm
  have e2 : c = vc x := by
    have h2 := congrArg (fun P : K[X] => P.coeff 2) h
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at h2
    norm_num at h2
    exact h2.symm
  have e1 : d = vd x := by
    have h1 := congrArg (fun P : K[X] => P.coeff 1) h
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at h1
    norm_num at h1
    exact h1.symm
  have e0 : e = ve x := by
    have h0 := congrArg (fun P : K[X] => P.coeff 0) h
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at h0
    norm_num at h0
    exact h0.symm
  exact ⟨e4, e3, e2, e1, e0⟩

end Resolvent

end MaedaGalois
