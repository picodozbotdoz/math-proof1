import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# The `(n−1)`-cycle + swap route to the full symmetric group

Iteration 21, the group-theoretic finish of the Maeda `Sₙ` program for
`6 ≤ dim ≤ 10`.  Mathlib's Jordan theorem for prime-order cycles (Wielandt
13.9) is still a TODO (`Mathlib.GroupTheory.GroupAction.Jordan`), so the
corrected-Jordan route of the blueprint is not available; instead every
weight is finished through the *elementary* combination

* transitive + containing a permutation of cycle type `{n−1}` (an `(n−1)`-cycle
  with one fixed point) ⟹ **preprimitive**
  (`isPreprimitive_of_isPretransitive_of_cycleType_mem`).  The block argument:
  let `g` be the `(n−1)`-cycle, `O` its support (size `n−1`), `pt` its unique
  fixed point.  For a block `B`, either `g • B = B` — then `B` is a union of
  `g`-orbits; if it meets `O` it contains `O`, and the translate `h⁻¹ • B`
  with `h • pt ∈ B` (transitivity) contains `pt`, so it cannot be disjoint
  from `B`, hence equals `B`, giving `pt ∈ B` and `B = univ`; otherwise
  `B ⊆ {pt}` — or `g • B ⊥ B` — then `pt` lies in no `g^k`-translate of `B`,
  the `g^k`-translates cover `O`, so the translate containing `pt` is disjoint
  from `O`, hence is the singleton `{pt}`; either way `B` is trivial;
* preprimitive + containing a swap ⟹ the full symmetric group (Mathlib,
  `Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`).

The Frobenius certificates discharge the two membership hypotheses through
`FrobeniusCycleType` (`FrobHasCycleType q {n-1}` and `FrobHasCycleType q {2}`;
by `Equiv.Perm.isSwap_iff_cycleType` the latter is exactly a swap, since
`cycleType` records only the nontrivial cycles).

Everything here is light and imports only Mathlib.
-/

open Equiv Polynomial
open scoped Pointwise

namespace MaedaGalois

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] [Fintype α] in
/-- Within the support of a cycle, every point is a nonnegative iterate of
any other point of the support. -/
theorem exists_pow_eq_of_isCycle [Finite α] {g : Equiv.Perm α} (hg : g.IsCycle) {x y : α}
    (hx : g x ≠ x) (hy : g y ≠ y) : ∃ k : ℕ, (g ^ k) x = y := by
  obtain ⟨w, -, hs⟩ := hg
  obtain ⟨k, -, hk⟩ := ((hs hx).symm.trans (hs hy)).exists_pow_eq'
  exact ⟨k, hk⟩

/-- **Transitive + `(n−1)`-cycle ⟹ preprimitive.**  A pretransitive subgroup
of the permutations of an `n`-element type (`n ≥ 3`) containing a permutation
of cycle type `{n−1}` is preprimitive. -/
theorem isPreprimitive_of_isPretransitive_of_cycleType_mem
    (G : Subgroup (Equiv.Perm α)) (hcard : Fintype.card α = n) (hn : 3 ≤ n)
    (htrans : MulAction.IsPretransitive G α)
    {g : Equiv.Perm α} (hg : g ∈ G) (hct : g.cycleType = {n - 1}) :
    MulAction.IsPreprimitive G α := by
  classical
  -- g is a cycle whose support has n - 1 elements
  have hgc : g.IsCycle := by
    refine Equiv.Perm.card_cycleType_eq_one.mp ?_
    rw [hct]; simp
  have hsup : g.support.card = n - 1 := by
    have h := Equiv.Perm.IsCycle.cycleType hgc
    rw [hct] at h
    exact (Multiset.singleton_inj.mp h).symm
  -- exactly one fixed point pt
  have hfixcard : ((g.support : Finset α)ᶜ).card = 1 := by
    rw [Finset.card_compl, hsup, hcard]; omega
  obtain ⟨pt, hcompl⟩ := Finset.card_eq_one.mp hfixcard
  have hgpt : g pt = pt := by
    have h : pt ∈ (g.support : Finset α)ᶜ := by
      rw [hcompl]; exact Finset.mem_singleton_self pt
    exact Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp h)
  have hptuniq : ∀ x : α, g x = x → x = pt := by
    intro x hx
    have h : x ∈ (g.support : Finset α)ᶜ := by
      refine Finset.mem_compl.mpr fun hmem => ?_
      rw [Equiv.Perm.mem_support] at hmem
      exact hmem hx
    rw [hcompl] at h
    exact Finset.mem_singleton.mp h
  have horbit : ∀ x y : α, g x ≠ x → g y ≠ y → ∃ k : ℕ, (g ^ k) x = y :=
    fun x y hx hy => exists_pow_eq_of_isCycle hgc hx hy
  -- the support is univ minus pt, in particular nonempty (n ≥ 3)
  have hsO : (g.support : Finset α) = Finset.univ.erase pt := by
    refine Finset.ext fun x => ?_
    rw [Finset.mem_erase, Equiv.Perm.mem_support]
    constructor
    · intro h
      exact ⟨fun hxpt => h (by rw [hxpt]; exact hgpt), Finset.mem_univ x⟩
    · intro h hgx
      exact h.1 (hptuniq x hgx)
  refine { toIsPretransitive := htrans, isTrivialBlock_of_isBlock := ?_ }
  intro B hB
  set g' : G := ⟨g, hg⟩ with hg'def
  -- the powers of g fix pt
  have hgpt' : ∀ k : ℕ, (g ^ k : Equiv.Perm α) pt = pt := by
    intro k
    induction k with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, hgpt, ih]
  rcases eq_or_ne (g' • B) B with hcase | hcase
  · -- Case 1: B is g-invariant, hence a union of g-orbits
    have hcase' : ((g' : G) : Equiv.Perm α) • B = B := hcase
    have hinv : ∀ k : ℕ, ((g' ^ k : G) : Equiv.Perm α) • B = B := by
      intro k
      rw [SubmonoidClass.coe_pow]
      induction k with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, mul_smul, hcase', ih]
    rcases Set.eq_empty_or_nonempty (B ∩ (g.support : Set α)) with hbo | hbo
    · refine Or.inl ?_
      intro a ha b hb
      have haa : a = pt := by
        apply hptuniq
        have hns : a ∉ (g.support : Set α) := fun h =>
          (Set.eq_empty_iff_forall_notMem.mp hbo a (Set.mem_inter ha h)).elim
        exact Equiv.Perm.notMem_support.mp hns
      have hbb : b = pt := by
        apply hptuniq
        have hns : b ∉ (g.support : Set α) := fun h =>
          (Set.eq_empty_iff_forall_notMem.mp hbo b (Set.mem_inter hb h)).elim
        exact Equiv.Perm.notMem_support.mp hns
      rw [haa, hbb]
    · -- the support is inside B
      have hOB : (g.support : Set α) ⊆ B := by
        intro x hx
        have hxb : g x ≠ x := Equiv.Perm.mem_support.mp hx
        obtain ⟨b, hb⟩ := hbo
        have hbb : g b ≠ b := Equiv.Perm.mem_support.mp hb.2
        obtain ⟨k, hk⟩ := horbit b x hbb hxb
        have hxm : x ∈ ((g' ^ k : G) : Equiv.Perm α) • B := by
          rw [SubmonoidClass.coe_pow]
          exact ⟨b, hb.1, hk⟩
        rwa [hinv k] at hxm
      -- move pt into B: pick h with h • pt ∈ O ∩ B (transitivity); then
      -- pt ∈ h⁻¹ • B, so h⁻¹ • B meets B and must equal B
      obtain ⟨o, hoB, hoO⟩ := hbo
      obtain ⟨h, hh⟩ := htrans.exists_smul_eq pt o
      have hpt' : pt ∈ (h⁻¹ : G) • B := by
        refine Set.mem_smul_set.mpr ⟨o, hoB, ?_⟩
        rw [← hh]
        exact Equiv.symm_apply_apply _ _
      rcases eq_or_ne ((h⁻¹ : G) • B) B with heq | hne
      · refine Or.inr (Set.eq_univ_of_forall ?_)
        intro x
        by_cases hgx : g x = x
        · rw [hptuniq x hgx]; exact heq ▸ hpt'
        · exact hOB (Equiv.Perm.mem_support.mpr hgx)
      · -- h⁻¹ • B is disjoint from B ⊇ O, contains pt: it is the singleton {pt}
        have hdisj := hB (g₁ := h⁻¹) (g₂ := 1) (by simpa using hne)
        rw [one_smul] at hdisj
        have hOempty : Disjoint ((h⁻¹ : G) • B) (g.support : Set α) :=
          Set.disjoint_of_subset_right hOB hdisj
        refine Or.inl ?_
        intro a ha b hb
        have haa : ((h⁻¹ : G) : Equiv.Perm α) a = pt := by
          have hx : ((h⁻¹ : G) : Equiv.Perm α) a ∈ ((h⁻¹ : G) : Equiv.Perm α) • B :=
            Set.mem_smul_set.mpr ⟨a, ha, rfl⟩
          have hx2 : ((h⁻¹ : G) : Equiv.Perm α) a ∉ (g.support : Set α) := fun hmem =>
            Set.disjoint_left.mp hOempty hx hmem
          exact hptuniq _ (Equiv.Perm.notMem_support.mp hx2)
        have hbb' : ((h⁻¹ : G) : Equiv.Perm α) b = pt := by
          have hx : ((h⁻¹ : G) : Equiv.Perm α) b ∈ ((h⁻¹ : G) : Equiv.Perm α) • B :=
            Set.mem_smul_set.mpr ⟨b, hb, rfl⟩
          have hx2 : ((h⁻¹ : G) : Equiv.Perm α) b ∉ (g.support : Set α) := fun hmem =>
            Set.disjoint_left.mp hOempty hx hmem
          exact hptuniq _ (Equiv.Perm.notMem_support.mp hx2)
        exact ((h⁻¹ : G) : Equiv.Perm α).injective (haa.trans hbb'.symm)
  · -- Case 2: g • B is disjoint from B
    have hdisj := hB (g₁ := g') (g₂ := 1) (by simpa using hcase)
    rw [one_smul] at hdisj
    -- pt is not in B, nor in any g^k translate
    have hptnB : pt ∉ B := by
      intro h
      exact Set.disjoint_left.mp hdisj
        (Set.mem_smul_set.mpr ⟨pt, h, hgpt⟩) h
    have hptnsmul : ∀ k : ℕ, pt ∉ ((g' ^ k : G) : Equiv.Perm α) • B := by
      intro k hmem
      obtain ⟨b, hb, hbk⟩ := Set.mem_smul_set.mp hmem
      apply hptnB
      have hbk' : (g ^ k : Equiv.Perm α) b = pt := hbk
      have h1 : (g ^ k : Equiv.Perm α) b = (g ^ k : Equiv.Perm α) pt := by
        rw [hbk', hgpt' k]
      exact ((g ^ k : Equiv.Perm α).injective h1) ▸ hb
    rcases Set.eq_empty_or_nonempty B with hb0 | hb0
    · exact Or.inl (hb0 ▸ Set.subsingleton_empty)
    obtain ⟨b₀, hb₀⟩ := hb0
    have hb₀O : g b₀ ≠ b₀ := fun h => hptnB (hptuniq b₀ h ▸ hb₀)
    have hcover : (g.support : Set α) ⊆ ⋃ k : ℕ, ((g' ^ k : G) : Equiv.Perm α) • B := by
      intro x hx
      have hxb : g x ≠ x := Equiv.Perm.mem_support.mp hx
      obtain ⟨k, hk⟩ := horbit b₀ x hb₀O hxb
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      rw [SubmonoidClass.coe_pow]
      exact ⟨b₀, hb₀, hk⟩
    -- the translate containing pt is disjoint from all of them, hence from O
    obtain ⟨h, hpt⟩ := htrans.exists_smul_eq b₀ pt
    have hptB : pt ∈ h • B := Set.mem_smul_set.mpr ⟨b₀, hb₀, hpt⟩
    have hsingle : h • B ⊆ {pt} := by
      intro x hx
      have hxO : x ∉ (g.support : Set α) := by
        intro hmem
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcover hmem)
        have hne : h • B ≠ ((g' ^ k : G) : Equiv.Perm α) • B := by
          intro heq
          exact hptnsmul k (heq ▸ hptB)
        exact Set.disjoint_left.mp (hB (g₁ := h) (g₂ := g' ^ k) hne) hx hk
      have hgx : g x = x := Equiv.Perm.notMem_support.mp hxO
      exact hptuniq x hgx
    refine Or.inl ?_
    intro a ha b hb
    have haa : ((h : Equiv.Perm α)) • a = pt :=
      Set.mem_singleton_iff.mp (hsingle (Set.mem_smul_set.mpr ⟨a, ha, rfl⟩))
    have hbb' : ((h : Equiv.Perm α)) • b = pt :=
      Set.mem_singleton_iff.mp (hsingle (Set.mem_smul_set.mpr ⟨b, hb, rfl⟩))
    exact (h : Equiv.Perm α).injective (haa.trans hbb'.symm)

/-- **The `Sₙ` finish.**  A pretransitive subgroup of the permutations of an
`n`-element type (`n ≥ 3`) containing a permutation of cycle type `{n−1}` and
a swap is the full symmetric group. -/
theorem eq_top_of_isPretransitive_of_cycleType_of_isSwap_mem
    (G : Subgroup (Equiv.Perm α)) (hcard : Fintype.card α = n) (hn : 3 ≤ n)
    (htrans : MulAction.IsPretransitive G α)
    {c : Equiv.Perm α} (hc : c ∈ G) (hct : c.cycleType = {n - 1})
    {s : Equiv.Perm α} (hs : s ∈ G) (hst : s.IsSwap) :
    G = ⊤ :=
  Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
    (isPreprimitive_of_isPretransitive_of_cycleType_mem G hcard hn htrans hc hct) s hst hs

end MaedaGalois
