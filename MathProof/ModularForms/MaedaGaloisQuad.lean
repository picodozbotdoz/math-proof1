import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Maeda in full, degree 2: `Gal = S₂` from irreducibility

The degree-2 corner of the `Gal = Sₙ` proofs.  `MaedaGaloisFull.
bijective_of_frobenius` needs `3 ≤ n` (its group-theoretic finish is vacuous
below), but for a monic quadratic irreducible over `ℚ` the conclusion is
immediate: over `ℂ` there are two roots, the Galois action on them is
pretransitive (irreducibility), so the image of `galActionHom` has at least two
elements — and as a subgroup of the permutations of a two-element type it has
at most two.  Mathlib has no such lemma at the pin: the closest,
`Gal.galActionHom_bijective_of_prime_degree`, demands two non-real roots,
which Hecke eigenvalues are not.

Everything here is light and imports only Mathlib; nothing is an ancestor of
the heavy `MaedaGalois5Defs` chain.
-/

open Polynomial

namespace MaedaGaloisQuad

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-- **The degree-2 finish.**  A monic integer quadratic irreducible over `ℚ`
has `Gal = S₂`: the pretransitive action on the two complex roots makes the
`galActionHom` image have at least two elements, and as a subgroup of the
permutation group of a two-element type it has at most two. -/
theorem bijective_of_quadratic {q : ℤ[X]} (hq : q.Monic) (hdeg : q.natDegree = 2)
    (hirr : Irreducible (q.map (Int.castRingHom ℚ))) :
    Function.Bijective (Gal.galActionHom (q.map (Int.castRingHom ℚ)) ℂ) := by
  classical
  have hcard : Fintype.card ((q.map (Int.castRingHom ℚ)).rootSet ℂ) = 2 := by
    rw [card_rootSet_eq_natDegree hirr.separable (IsAlgClosed.splits _),
      hq.natDegree_map, hdeg]
  have htrans : MulAction.IsPretransitive (Gal.galActionHom
      (q.map (Int.castRingHom ℚ)) ℂ).range ((q.map (Int.castRingHom ℚ)).rootSet ℂ) := by
    have := Gal.galAction_isPretransitive (q.map (Int.castRingHom ℚ)) ℂ hirr
    refine ⟨fun a b => ?_⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (q.map (Int.castRingHom ℚ)).Gal a b
    exact ⟨⟨_, g, rfl⟩, hg⟩
  obtain ⟨a⟩ : Nonempty ((q.map (Int.castRingHom ℚ)).rootSet ℂ) :=
    Fintype.card_pos_iff.mp (by rw [hcard]; norm_num)
  have hsurj : Function.Surjective
      (fun g : (Gal.galActionHom (q.map (Int.castRingHom ℚ)) ℂ).range =>
        (g : Equiv.Perm ((q.map (Int.castRingHom ℚ)).rootSet ℂ)) • a) :=
    fun b => htrans.exists_smul_eq a b
  have hge : 2 ≤ Fintype.card (Gal.galActionHom (q.map (Int.castRingHom ℚ)) ℂ).range := by
    have := Fintype.card_le_of_surjective _ hsurj
    rw [hcard] at this
    omega
  have hle : Fintype.card (Gal.galActionHom (q.map (Int.castRingHom ℚ)) ℂ).range
      ≤ Fintype.card (Equiv.Perm ((q.map (Int.castRingHom ℚ)).rootSet ℂ)) :=
    Fintype.card_le_of_injective _ (SubmonoidClass.subtype_injective _)
  have hperm : Fintype.card (Equiv.Perm ((q.map (Int.castRingHom ℚ)).rootSet ℂ)) = 2 := by
    rw [Fintype.card_perm, hcard]
    norm_num
  have htop : (Gal.galActionHom (q.map (Int.castRingHom ℚ)) ℂ).range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
      (G := Equiv.Perm ((q.map (Int.castRingHom ℚ)).rootSet ℂ))
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hperm]
    omega
  exact ⟨Gal.galActionHom_injective _ _, MonoidHom.range_eq_top.mp htop⟩

end MaedaGaloisQuad
