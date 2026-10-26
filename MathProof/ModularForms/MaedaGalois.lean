import MathProof.ModularForms.MaedaSmallWeights
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Maeda's conjecture in full for the cubic weights: Galois group `S₃`

Maeda's conjecture asks for more than irreducibility: the Galois group of the
characteristic polynomial of `T₂` on `S_k` should be the full symmetric group.
For `dim S_k = 2` this is automatic once the polynomial is irreducible.  For the
six weights with `dim S_k = 3` (`k = 36, 40, 42, 44, 46, 50`) this file proves
that the Galois group acts on the three complex roots as all of `S₃`.

Mathlib's prime-degree criterion (`galActionHom_bijective_of_prime_degree`)
needs two non-real roots, which never happens here: Hecke eigenvalues are real.
Instead, `galActionHom_bijective_of_cubic` uses the discriminant: in the
splitting field `K`, `δ = (x − y)(x − z)(y − z)` satisfies `δ² = disc`; a
non-square discriminant makes `ℚ⟮δ⟯` quadratic, so `2 ∣ [K : ℚ]`; irreducibility
gives `3 ∣ [K : ℚ]`; and `Gal ↪ S₃` forces `|Gal| = 6`.
-/

open Polynomial Module IntermediateField

namespace MaedaGalois

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-- **An irreducible cubic with non-square discriminant has Galois group `S₃`**:
the Galois action on the complex roots is a bijection onto all permutations. -/
theorem galActionHom_bijective_of_cubic {b c d : ℚ}
    (hirr : Irreducible (Cubic.toPoly ⟨1, b, c, d⟩ : ℚ[X]))
    (hdisc : ¬ IsSquare (Cubic.discr ⟨1, b, c, d⟩ : ℚ)) :
    Function.Bijective (Gal.galActionHom (Cubic.toPoly ⟨1, b, c, d⟩ : ℚ[X]) ℂ) := by
  set P : Cubic ℚ := ⟨1, b, c, d⟩ with hP
  set p := P.toPoly
  have ha : P.a ≠ 0 := by simp [hP]
  have hdeg : p.natDegree = 3 := Cubic.natDegree_of_a_ne_zero ha
  have hsep := hirr.separable
  have h1 : Fintype.card (p.rootSet ℂ) = 3 := by
    rw [card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _), hdeg]
  have hinj := Gal.galActionHom_injective p ℂ
  have hperm : Nat.card (Equiv.Perm (p.rootSet ℂ)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, h1]; rfl
  have hle : Nat.card p.Gal ≤ 6 := hperm ▸ Nat.card_le_card_of_injective _ hinj
  have h3 : 3 ∣ Nat.card p.Gal :=
    hdeg ▸ Gal.prime_degree_dvd_card hirr (hdeg ▸ Nat.prime_three)
  have h2 : 2 ∣ Nat.card p.Gal := by
    rw [Gal.card_of_separable hsep]
    have hspl : Splits (p.map (algebraMap ℚ p.SplittingField)) := SplittingField.splits p
    obtain ⟨x, y, z, hroots⟩ :=
      (Cubic.splits_iff_roots_eq_three (φ := algebraMap ℚ p.SplittingField) ha).mp hspl
    have hd := Cubic.discr_eq_prod_three_roots (φ := algebraMap ℚ p.SplittingField) ha hroots
    set δ := (x - y) * (x - z) * (y - z) with hδdef
    have hδ : δ ^ 2 = algebraMap ℚ p.SplittingField P.discr := by
      rw [hd]; simp [hP, hδdef]
    have hq : Irreducible (X ^ 2 - C P.discr : ℚ[X]) := by
      refine irreducible_of_degree_le_three_of_not_isRoot ?_ fun r hr => hdisc ⟨r, ?_⟩
      · rw [natDegree_X_pow_sub_C]; decide
      · simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hr
        rw [← hr]; ring
    have hmin : minpoly ℚ δ = X ^ 2 - C P.discr :=
      (minpoly.eq_of_irreducible_of_monic hq (by simp [hδ])
        (monic_X_pow_sub_C _ (by norm_num))).symm
    have hfin : finrank ℚ ℚ⟮δ⟯ = 2 := by
      rw [adjoin.finrank (Algebra.IsIntegral.isIntegral δ), hmin, natDegree_X_pow_sub_C]
    rw [← hfin]
    exact Module.finrank_dvd_finrank_right ℚ ℚ⟮δ⟯ p.SplittingField
  have h6 : Nat.card p.Gal = 6 := by
    obtain ⟨m, hm⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2 h3
    have hpos : 0 < Nat.card p.Gal := Nat.card_pos
    omega
  exact (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, h6.trans hperm.symm⟩

/-! ### Weight 36 -/

/-- The discriminant of the weight-36 cubic,
`606037485049196709344808901017600`,
is not a square mod 29. -/
lemma nonsquare36 : ∀ x : ZMod 29,
    (606037485049196709344808901017600 : ZMod 29) ≠ x * x := by
  decide

/-- **Maeda's conjecture in weight 36, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_36` acts on its three roots as `S₃`. -/
theorem maeda_galois36 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight36.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hP : MaedaWeight36.P.map (Int.castRingHom ℚ)
      = Cubic.toPoly ⟨1, (-139656 : ℚ), (-59208339456 : ℚ),
        (-1467625047588864 : ℚ)⟩ := by
    simp [MaedaWeight36.P, Cubic.toPoly, map_ofNat]
  have hirr := MaedaWeight36.maeda
  rw [hP] at hirr ⊢
  refine galActionHom_bijective_of_cubic hirr ?_
  rw [show Cubic.discr ⟨1, (-139656 : ℚ), (-59208339456 : ℚ), (-1467625047588864 : ℚ)⟩
      = ((606037485049196709344808901017600 : ℤ) : ℚ) by
    norm_num [Cubic.discr], Rat.isSquare_intCast_iff]
  rintro ⟨n, hn⟩
  have h := congrArg (fun z : ℤ => (z : ZMod 29)) hn
  push_cast at h
  exact nonsquare36 n h

/-! ### Weight 40 -/

/-- The discriminant of the weight-40 cubic,
`2942804749388599757494744709175705600`,
is not a square mod 41. -/
lemma nonsquare40 : ∀ x : ZMod 41,
    (2942804749388599757494744709175705600 : ZMod 41) ≠ x * x := by
  decide

/-- **Maeda's conjecture in weight 40, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_40` acts on its three roots as `S₃`. -/
theorem maeda_galois40 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight40.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hP : MaedaWeight40.P.map (Int.castRingHom ℚ)
      = Cubic.toPoly ⟨1, (-548856 : ℚ), (-810051757056 : ℚ),
        (213542160549543936 : ℚ)⟩ := by
    simp [MaedaWeight40.P, Cubic.toPoly, map_ofNat]
  have hirr := MaedaWeight40.maeda
  rw [hP] at hirr ⊢
  refine galActionHom_bijective_of_cubic hirr ?_
  rw [show Cubic.discr ⟨1, (-548856 : ℚ), (-810051757056 : ℚ), (213542160549543936 : ℚ)⟩
      = ((2942804749388599757494744709175705600 : ℤ) : ℚ) by
    norm_num [Cubic.discr], Rat.isSquare_intCast_iff]
  rintro ⟨n, hn⟩
  have h := congrArg (fun z : ℤ => (z : ZMod 41)) hn
  push_cast at h
  exact nonsquare40 n h

/-! ### Weight 42 -/

/-- The discriminant of the weight-42 cubic,
`1054512765852281785358885792805971558400`,
is not a square mod 43. -/
lemma nonsquare42 : ∀ x : ZMod 43,
    (1054512765852281785358885792805971558400 : ZMod 43) ≠ x * x := by
  decide

/-- **Maeda's conjecture in weight 42, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_42` acts on its three roots as `S₃`. -/
theorem maeda_galois42 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight42.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hP : MaedaWeight42.P.map (Int.castRingHom ℚ)
      = Cubic.toPoly ⟨1, (344688 : ℚ), (-6374982426624 : ℚ),
        (-520435526440845312 : ℚ)⟩ := by
    simp [MaedaWeight42.P, Cubic.toPoly, map_ofNat]
  have hirr := MaedaWeight42.maeda
  rw [hP] at hirr ⊢
  refine galActionHom_bijective_of_cubic hirr ?_
  rw [show Cubic.discr ⟨1, (344688 : ℚ), (-6374982426624 : ℚ), (-520435526440845312 : ℚ)⟩
      = ((1054512765852281785358885792805971558400 : ℤ) : ℚ) by
    norm_num [Cubic.discr], Rat.isSquare_intCast_iff]
  rintro ⟨n, hn⟩
  have h := congrArg (fun z : ℤ => (z : ZMod 43)) hn
  push_cast at h
  exact nonsquare42 n h

/-! ### Weight 44 -/

/-- The discriminant of the weight-44 cubic,
`19104694120990804233835415658184468070400`,
is not a square mod 41. -/
lemma nonsquare44 : ∀ x : ZMod 41,
    (19104694120990804233835415658184468070400 : ZMod 41) ≠ x * x := by
  decide

/-- **Maeda's conjecture in weight 44, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_44` acts on its three roots as `S₃`. -/
theorem maeda_galois44 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight44.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hP : MaedaWeight44.P.map (Int.castRingHom ℚ)
      = Cubic.toPoly ⟨1, (2209944 : ℚ), (-15663522502656 : ℚ),
        (-19976984434430705664 : ℚ)⟩ := by
    simp [MaedaWeight44.P, Cubic.toPoly, map_ofNat]
  have hirr := MaedaWeight44.maeda
  rw [hP] at hirr ⊢
  refine galActionHom_bijective_of_cubic hirr ?_
  rw [show Cubic.discr ⟨1, (2209944 : ℚ), (-15663522502656 : ℚ), (-19976984434430705664 : ℚ)⟩
      = ((19104694120990804233835415658184468070400 : ℤ) : ℚ) by
    norm_num [Cubic.discr], Rat.isSquare_intCast_iff]
  rintro ⟨n, hn⟩
  have h := congrArg (fun z : ℤ => (z : ZMod 41)) hn
  push_cast at h
  exact nonsquare44 n h

/-! ### Weight 46 -/

/-- The discriminant of the weight-46 cubic,
`332169986114217137585368052148622432665600`,
is not a square mod 23. -/
lemma nonsquare46 : ∀ x : ZMod 23,
    (332169986114217137585368052148622432665600 : ZMod 23) ≠ x * x := by
  decide

/-- **Maeda's conjecture in weight 46, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_46` acts on its three roots as `S₃`. -/
theorem maeda_galois46 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight46.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hP : MaedaWeight46.P.map (Int.castRingHom ℚ)
      = Cubic.toPoly ⟨1, (-3814272 : ℚ), (-44544640241664 : ℚ),
        (135250282417024401408 : ℚ)⟩ := by
    simp [MaedaWeight46.P, Cubic.toPoly, map_ofNat]
  have hirr := MaedaWeight46.maeda
  rw [hP] at hirr ⊢
  refine galActionHom_bijective_of_cubic hirr ?_
  rw [show Cubic.discr ⟨1, (-3814272 : ℚ), (-44544640241664 : ℚ), (135250282417024401408 : ℚ)⟩
      = ((332169986114217137585368052148622432665600 : ℤ) : ℚ) by
    norm_num [Cubic.discr], Rat.isSquare_intCast_iff]
  rintro ⟨n, hn⟩
  have h := congrArg (fun z : ℤ => (z : ZMod 23)) hn
  push_cast at h
  exact nonsquare46 n h

/-! ### Weight 50 -/

/-- The discriminant of the weight-50 cubic,
`42077422585405140357700605017762782248960000`,
is not a square mod 41. -/
lemma nonsquare50 : ∀ x : ZMod 41,
    (42077422585405140357700605017762782248960000 : ZMod 41) ≠ x * x := by
  decide

/-- **Maeda's conjecture in weight 50, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_50` acts on its three roots as `S₃`. -/
theorem maeda_galois50 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight50.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hP : MaedaWeight50.P.map (Int.castRingHom ℚ)
      = Cubic.toPoly ⟨1, (24225168 : ℚ), (-566746931810304 : ℚ),
        (-13634883228742736412672 : ℚ)⟩ := by
    simp [MaedaWeight50.P, Cubic.toPoly, map_ofNat]
  have hirr := MaedaWeight50.maeda
  rw [hP] at hirr ⊢
  refine galActionHom_bijective_of_cubic hirr ?_
  rw [show Cubic.discr ⟨1, (24225168 : ℚ), (-566746931810304 : ℚ), (-13634883228742736412672 : ℚ)⟩
      = ((42077422585405140357700605017762782248960000 : ℤ) : ℚ) by
    norm_num [Cubic.discr], Rat.isSquare_intCast_iff]
  rintro ⟨n, hn⟩
  have h := congrArg (fun z : ℤ => (z : ZMod 41)) hn
  push_cast at h
  exact nonsquare50 n h

end MaedaGalois
