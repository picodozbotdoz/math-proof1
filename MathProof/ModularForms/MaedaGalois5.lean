import MathProof.ModularForms.MaedaDim5
import MathProof.ModularForms.MaedaGalois
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

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

open Equiv Subgroup Polynomial

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
      rw [hb, mem_bot] at hmem
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

end MaedaGalois
