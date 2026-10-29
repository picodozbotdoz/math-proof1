import MathProof.ModularForms.MaedaDim4Weights
import MathProof.ModularForms.MaedaGalois

/-!
# Maeda's conjecture in full for dimension 4: Galois group `S₄`

For the six level-one weights with `dim S_k = 4` (`k = 48, 52, 54, 56, 58, 62`),
`MathProof/ModularForms/MaedaDim4Weights.lean` proves the characteristic
polynomial `P` of `T₂` irreducible.  Here we prove its Galois group is all of
`S₄`.

`galActionHom_bijective_of_quartic` — an irreducible monic quartic over `ℚ`
whose resolvent cubic is irreducible and whose discriminant is not a square has
Galois group `S₄`.  The proof counts degrees and uses one fact about `A₄`:

* in the splitting field `K`, a root `x₀` has degree 4, and the resolvent root
  `θ = x₀x₁ + x₂x₃` has degree 3, so `12 ∣ [K : ℚ] = |Gal|`; `Gal ↪ S₄` gives
  `|Gal| ∈ {12, 24}`;
* if `|Gal| = 12`, its image is the index-2 subgroup `A₄`; but
  `δ = ∏_{i<j} (x_i − x_j)` has `δ² = disc ∉ ℚ²`, so `ℚ(δ)` is a quadratic
  subfield and its fixing subgroup has index 2 in `Gal ≅ A₄`;
* an index-2 subgroup contains every square, every 3-cycle `c = (c²)²` is a
  square, and the 3-cycles generate `A₄` — contradiction.
-/

open Polynomial Module IntermediateField

namespace MaedaGalois

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-- The discriminant of `X⁴ + a X³ + b X² + c X + d`. -/
def disc4 {R : Type*} [CommRing R] (a b c d : R) : R :=
  256 * d ^ 3 - 192 * a * c * d ^ 2 - 128 * b ^ 2 * d ^ 2 + 144 * b * c ^ 2 * d - 27 * c ^ 4
    + 144 * a ^ 2 * b * d ^ 2 - 6 * a ^ 2 * c ^ 2 * d - 80 * a * b ^ 2 * c * d
    + 18 * a * b * c ^ 3 + 16 * b ^ 4 * d - 4 * b ^ 3 * c ^ 2 - 27 * a ^ 4 * d ^ 2
    + 18 * a ^ 3 * b * c * d - 4 * a ^ 3 * c ^ 3 - 4 * a ^ 2 * b ^ 3 * d
    + a ^ 2 * b ^ 2 * c ^ 2

/-- The resolvent cubic `Y³ − b Y² + (ac − 4d) Y − (a²d − 4bd + c²)`, whose root is
`x₀x₁ + x₂x₃`. -/
noncomputable def resolvent {K : Type*} [Field K] (a b c d : K) : K[X] :=
  X ^ 3 + C (-b) * X ^ 2 + C (a * c - 4 * d) * X + C (-(a ^ 2 * d - 4 * b * d + c ^ 2))

/-- **Vieta for quartics.** -/
lemma vieta4 {K : Type*} [Field K] {x₀ x₁ x₂ x₃ a b c d : K}
    (h : (X - C x₀) * (X - C x₁) * (X - C x₂) * (X - C x₃)
      = X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) :
    a = -(x₀ + x₁ + x₂ + x₃)
      ∧ b = x₀ * x₁ + x₀ * x₂ + x₀ * x₃ + x₁ * x₂ + x₁ * x₃ + x₂ * x₃
      ∧ c = -(x₀ * x₁ * x₂ + x₀ * x₁ * x₃ + x₀ * x₂ * x₃ + x₁ * x₂ * x₃)
      ∧ d = x₀ * x₁ * x₂ * x₃ := by
  have hprod : (X - C x₀) * (X - C x₁) * (X - C x₂) * (X - C x₃)
      = X ^ 4 + C (-(x₀ + x₁ + x₂ + x₃)) * X ^ 3
        + C (x₀ * x₁ + x₀ * x₂ + x₀ * x₃ + x₁ * x₂ + x₁ * x₃ + x₂ * x₃) * X ^ 2
        + C (-(x₀ * x₁ * x₂ + x₀ * x₁ * x₃ + x₀ * x₂ * x₃ + x₁ * x₂ * x₃)) * X
        + C (x₀ * x₁ * x₂ * x₃) := by
    simp only [map_neg, map_add, map_mul]; ring
  rw [hprod] at h
  have d3 := congrArg (fun P : K[X] => P.coeff 3) h
  have d2 := congrArg (fun P : K[X] => P.coeff 2) h
  have d1 := congrArg (fun P : K[X] => P.coeff 1) h
  have d0 := congrArg (fun P : K[X] => P.coeff 0) h
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at d3 d2 d1 d0
  norm_num at d3 d2 d1 d0
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination -d3
  · linear_combination -d2
  · linear_combination -d1
  · linear_combination -d0

/-- Degree of an element whose minimal polynomial is a given irreducible monic
polynomial divides `[K : ℚ]`. -/
lemma natDegree_dvd_finrank {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    {q : ℚ[X]} (hq : Irreducible q) (hmon : q.Monic) {y : K} (hy : aeval y q = 0) :
    q.natDegree ∣ finrank ℚ K := by
  have hmin : minpoly ℚ y = q := (minpoly.eq_of_irreducible_of_monic hq hy hmon).symm
  rw [← hmin, ← adjoin.finrank (Algebra.IsIntegral.isIntegral y)]
  exact Module.finrank_dvd_finrank_right ℚ ℚ⟮y⟯ K

/-- **An irreducible quartic with irreducible resolvent cubic and non-square
discriminant has Galois group `S₄`.** -/
theorem galActionHom_bijective_of_quartic {a b c d : ℚ}
    (hirr : Irreducible (X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d : ℚ[X]))
    (hres : Irreducible (resolvent a b c d))
    (hdisc : ¬ IsSquare (disc4 a b c d)) :
    Function.Bijective
      (Gal.galActionHom (X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d : ℚ[X]) ℂ) := by
  set p : ℚ[X] := X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d with hp
  have hmon : p.Monic := by rw [hp]; monicity!
  have hdeg : p.natDegree = 4 := by rw [hp]; compute_degree!
  have hsep := hirr.separable
  set K := p.SplittingField
  set φ := algebraMap ℚ K
  -- the four roots in `K`, and Vieta
  have hspl : Splits (p.map φ) := SplittingField.splits p
  have hcard : (p.map φ).roots.card = 4 := by
    rw [(splits_iff_card_roots).mp hspl, hmon.natDegree_map, hdeg]
  obtain ⟨x₀, x₁, x₂, x₃, hroots⟩ := Multiset.card_eq_four.mp hcard
  have hfac : p.map φ = (X - C x₀) * (X - C x₁) * (X - C x₂) * (X - C x₃) := by
    rw [hspl.eq_prod_roots_of_monic (hmon.map φ), hroots]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.map_singleton, Multiset.prod_singleton]
    ring
  have hmapGen : ∀ (L : Type) [Field L] [Algebra ℚ L],
      (X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d : ℚ[X]).map (algebraMap ℚ L)
        = X ^ 4 + C (algebraMap ℚ L a) * X ^ 3 + C (algebraMap ℚ L b) * X ^ 2
          + C (algebraMap ℚ L c) * X + C (algebraMap ℚ L d) := fun L _ _ => by simp
  have hmapP : p.map φ = X ^ 4 + C (φ a) * X ^ 3 + C (φ b) * X ^ 2 + C (φ c) * X + C (φ d) :=
    hmapGen K
  obtain ⟨va, vb, vc, vd⟩ := vieta4 (hfac.symm.trans hmapP)
  -- degree 4: the root `x₀`
  have hx₀ : aeval x₀ p = 0 := by
    rw [aeval_def, ← eval_map, hfac]; simp
  have h4 : 4 ∣ finrank ℚ K := hdeg ▸ natDegree_dvd_finrank hirr hmon hx₀
  -- degree 3: the resolvent root `θ = x₀x₁ + x₂x₃`
  have hresmon : (resolvent a b c d).Monic := by unfold resolvent; monicity!
  have hresdeg : (resolvent a b c d).natDegree = 3 := by unfold resolvent; compute_degree!
  have hθ : aeval (x₀ * x₁ + x₂ * x₃) (resolvent a b c d) = 0 := by
    simp only [resolvent, map_add, map_mul, map_pow, aeval_X, aeval_C, map_neg, map_sub,
      map_ofNat]
    rw [← show φ a = algebraMap ℚ K a from rfl, va, vb, vc, vd]
    ring
  have h3 : 3 ∣ finrank ℚ K := hresdeg ▸ natDegree_dvd_finrank hres hresmon hθ
  -- `|Gal| ∈ {12, 24}`
  have hcardGal : Nat.card p.Gal = finrank ℚ K := Gal.card_of_separable hsep
  have h1 : Fintype.card (p.rootSet ℂ) = 4 := by
    rw [card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _), hdeg]
  have hinj := Gal.galActionHom_injective p ℂ
  have hperm : Nat.card (Equiv.Perm (p.rootSet ℂ)) = 24 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, h1]; rfl
  have hle : Nat.card p.Gal ≤ 24 := hperm ▸ Nat.card_le_card_of_injective _ hinj
  have h12 : 12 ∣ Nat.card p.Gal := by
    rw [hcardGal]; exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3
  have hpos : 0 < Nat.card p.Gal := Nat.card_pos
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  rw [hperm]
  rcases (by obtain ⟨m, hm⟩ := h12; omega :
      Nat.card p.Gal = 12 ∨ Nat.card p.Gal = 24) with h | h
  swap
  · exact h
  exfalso
  -- the quadratic subfield `ℚ(δ)`
  set δ := (x₀ - x₁) * (x₀ - x₂) * (x₀ - x₃) * (x₁ - x₂) * (x₁ - x₃) * (x₂ - x₃) with hδdef
  have hδ : δ ^ 2 = φ (disc4 a b c d) := by
    simp only [disc4, map_add, map_sub, map_mul, map_pow, map_ofNat]
    rw [va, vb, vc, vd, hδdef]
    ring
  have hq : Irreducible (X ^ 2 - C (disc4 a b c d) : ℚ[X]) := by
    refine irreducible_of_degree_le_three_of_not_isRoot ?_ fun r hr => hdisc ⟨r, ?_⟩
    · rw [natDegree_X_pow_sub_C]; decide
    · simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hr
      rw [← hr]; ring
  have hδroot : aeval δ (X ^ 2 - C (disc4 a b c d) : ℚ[X]) = 0 := by simp [hδ, φ]
  have hδdeg : finrank ℚ ℚ⟮δ⟯ = 2 := by
    rw [adjoin.finrank (Algebra.IsIntegral.isIntegral δ),
      (minpoly.eq_of_irreducible_of_monic hq hδroot (monic_X_pow_sub_C _ (by norm_num))).symm,
      natDegree_X_pow_sub_C]
  -- its fixing subgroup has index 2
  have : IsGalois ℚ K := IsGalois.of_separable_splitting_field hsep
  let F : Subgroup p.Gal := (ℚ⟮δ⟯ : IntermediateField ℚ K).fixingSubgroup
  have hF : Nat.card F = 6 := by
    change Nat.card (ℚ⟮δ⟯ : IntermediateField ℚ K).fixingSubgroup = 6
    rw [IsGalois.card_fixingSubgroup_eq_finrank]
    have htower := Module.finrank_mul_finrank ℚ ℚ⟮δ⟯ K
    rw [hδdeg, ← hcardGal, h] at htower
    omega
  have hFidx : F.index = 2 := by
    have := F.index_mul_card
    rw [hF, h] at this
    omega
  -- the image of `Gal` in `S₄` is `A₄`
  set f := Gal.galActionHom p ℂ
  have hrange : f.range = alternatingGroup (p.rootSet ℂ) := by
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    have hc : Nat.card f.range = 12 := by
      rw [← h]; exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    have := f.range.index_mul_card
    rw [hc, hperm] at this
    omega
  -- every 3-cycle lies in the image of `F`
  have h3cyc : alternatingGroup (p.rootSet ℂ) ≤ F.map f := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro σ hσ
    have hσA : σ ∈ f.range := hrange ▸ (Equiv.Perm.IsThreeCycle.mem_alternatingGroup hσ)
    obtain ⟨g, rfl⟩ := hσA
    have hg2 : g ^ 2 ∈ F := Subgroup.sq_mem_of_index_two hFidx g
    refine ⟨(g ^ 2) ^ 2, F.pow_mem hg2 2, ?_⟩
    have h3 : (f g) ^ 3 = 1 := by
      rw [← hσ.orderOf]; exact pow_orderOf_eq_one _
    rw [map_pow, map_pow, ← pow_mul,
      show (f g) ^ (2 * 2) = (f g) ^ 3 * f g by rw [← pow_succ]]
    rw [h3, one_mul]
  have hle' : Nat.card (alternatingGroup (p.rootSet ℂ)) ≤ Nat.card (F.map f) :=
    Subgroup.card_le_of_le h3cyc
  have hmapcard : Nat.card (F.map f) = 6 := by
    rw [← hF]; exact Nat.card_congr (F.equivMapOfInjective f hinj).toEquiv.symm
  have hAcard : Nat.card (alternatingGroup (p.rootSet ℂ)) = 12 := by
    rw [← hrange, ← h]; exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  omega

/-! ### Weight 48 -/

namespace Weight48

/-- The resolvent cubic of the weight-48 quartic, over `ℤ`. -/
noncomputable def R : ℤ[X] :=
  X ^ 3 + C (467142374034432) * X ^ 2
    + C (-21446669142705803440133505024) * X
    + C (-8308616729745868551297190273263222933946368)

/-- Axiom-free certificate: plain `ℤ` arithmetic over bounded `ℕ` (`HornerCert`). -/
lemma noRootR_cert : ∀ y : ℕ, y < 43 → ((y : ℤ) ^ 3 + (467142374034432) * (y : ℤ) ^ 2 +
      (-21446669142705803440133505024) * (y : ℤ) + (-8308616729745868551297190273263222933946368))
      % 43 ≠ 0 := by
  decide +kernel

lemma noRootR : ∀ y : ZMod 43,
    y ^ 3 + (467142374034432 : ZMod 43) * y ^ 2
      + (-21446669142705803440133505024 : ZMod 43) * y
      + (-8308616729745868551297190273263222933946368 : ZMod 43) ≠ 0 := by
  intro y h1
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq y
  refine noRootR_cert z hz (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- The discriminant of the weight-48 quartic. -/
def Dval : ℤ :=
  3162223814975332907582154541 * 10 ^ 60
    + 908107145851772707217804681584460594432386392764973056000000

/-- Axiom-free certificate (`HornerCert`): the discriminant is not a square mod 23. -/
lemma nonsquare_cert : ∀ y : ℕ, y < 23 → (Dval - (y : ℤ) * (y : ℤ)) % 23 ≠ 0 := by
  decide +kernel

/-- The discriminant is not a square mod 23. -/
lemma nonsquare : ∀ x : ZMod 23, ((Dval : ℤ) : ZMod 23) ≠ x * x := by
  intro x h1
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq x
  refine nonsquare_cert z hz (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

lemma hP : MaedaWeight48.P.map (Int.castRingHom ℚ)
    = X ^ 4 + C (-5785560 : ℚ) * X ^ 3 + C (-467142374034432 : ℚ) * X ^ 2
      + C (1426830562183253852160 : ℚ) * X + C (3297913828840214320807673856 : ℚ) := by
  simp [MaedaWeight48.P, map_ofNat]

lemma hR : resolvent (-5785560 : ℚ) (-467142374034432 : ℚ) (1426830562183253852160 : ℚ)
      (3297913828840214320807673856 : ℚ) = R.map (Int.castRingHom ℚ) := by
  simp [resolvent, R, map_ofNat]
  norm_num

lemma hD : disc4 (-5785560 : ℚ) (-467142374034432 : ℚ) (1426830562183253852160 : ℚ)
      (3297913828840214320807673856 : ℚ) = ((Dval : ℤ) : ℚ) := by
  norm_num [disc4, Dval]

end Weight48

/-- **Maeda's conjecture in weight 48, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_48` acts on its four roots as `S₄`. -/
theorem maeda_galois48 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight48.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hirr := MaedaWeight48.maeda
  rw [Weight48.hP] at hirr ⊢
  refine galActionHom_bijective_of_quartic hirr ?_ ?_
  · have : Fact (Nat.Prime 43) := ⟨by norm_num⟩
    rw [Weight48.hR]
    refine MaedaLevelOne.irreducible_of_noRoot (by unfold Weight48.R; monicity!) ?_ 43
      fun y hy => Weight48.noRootR y ?_
    · rw [show Weight48.R.natDegree = 3 by unfold Weight48.R; compute_degree!]; decide
    · simpa [Weight48.R] using hy
  · rw [Weight48.hD, Rat.isSquare_intCast_iff]
    rintro ⟨n, hn⟩
    have h := congrArg (fun z : ℤ => (z : ZMod 23)) hn
    push_cast at h
    exact Weight48.nonsquare n (by rw [h])

/-! ### Weight 52 -/

namespace Weight52

/-- The resolvent cubic of the weight-52 quartic, over `ℤ`. -/
noncomputable def R : ℤ[X] :=
  X ^ 3 + C (7956172284567552) * X ^ 2
    + C (-27293510302774154857049021743104) * X
    + C (-224518765122805048047034799291103928016235921408)

/-- Axiom-free certificate: plain `ℤ` arithmetic over bounded `ℕ` (`HornerCert`). -/
lemma noRootR_cert : ∀ y : ℕ, y < 53 → ((y : ℤ) ^ 3 + (7956172284567552) * (y : ℤ) ^ 2 +
      (-27293510302774154857049021743104) * (y : ℤ) +
      (-224518765122805048047034799291103928016235921408)) % 53 ≠ 0 := by
  decide +kernel

lemma noRootR : ∀ y : ZMod 53,
    y ^ 3 + (7956172284567552 : ZMod 53) * y ^ 2
      + (-27293510302774154857049021743104 : ZMod 53) * y
      + (-224518765122805048047034799291103928016235921408 : ZMod 53) ≠ 0 := by
  intro y h1
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq y
  refine noRootR_cert z hz (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- The discriminant of the weight-52 quartic. -/
def Dval : ℤ :=
  97330908765702604639063896235197413 * 10 ^ 60
    + 751066579167949973325285984844742144363313932623937536000000

/-- Axiom-free certificate (`HornerCert`): the discriminant is not a square mod 29. -/
lemma nonsquare_cert : ∀ y : ℕ, y < 29 → (Dval - (y : ℤ) * (y : ℤ)) % 29 ≠ 0 := by
  decide +kernel

/-- The discriminant is not a square mod 29. -/
lemma nonsquare : ∀ x : ZMod 29, ((Dval : ℤ) : ZMod 29) ≠ x * x := by
  intro x h1
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq x
  refine nonsquare_cert z hz (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

lemma hP : MaedaWeight52.P.map (Int.castRingHom ℚ)
    = X ^ 4 + C (-32756040 : ℚ) * X ^ 3 + C (-7956172284567552 : ℚ) * X ^ 2
      + C (269568678949709508771840 : ℚ) * X + C (4615876968087578049834569957376 : ℚ) := by
  simp [MaedaWeight52.P, map_ofNat]

lemma hR : resolvent (-32756040 : ℚ) (-7956172284567552 : ℚ) (269568678949709508771840 : ℚ)
      (4615876968087578049834569957376 : ℚ) = R.map (Int.castRingHom ℚ) := by
  simp [resolvent, R, map_ofNat]
  norm_num

lemma hD : disc4 (-32756040 : ℚ) (-7956172284567552 : ℚ) (269568678949709508771840 : ℚ)
      (4615876968087578049834569957376 : ℚ) = ((Dval : ℤ) : ℚ) := by
  norm_num [disc4, Dval]

end Weight52

/-- **Maeda's conjecture in weight 52, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_52` acts on its four roots as `S₄`. -/
theorem maeda_galois52 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight52.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hirr := MaedaWeight52.maeda
  rw [Weight52.hP] at hirr ⊢
  refine galActionHom_bijective_of_quartic hirr ?_ ?_
  · have : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    rw [Weight52.hR]
    refine MaedaLevelOne.irreducible_of_noRoot (by unfold Weight52.R; monicity!) ?_ 53
      fun y hy => Weight52.noRootR y ?_
    · rw [show Weight52.R.natDegree = 3 by unfold Weight52.R; compute_degree!]; decide
    · simpa [Weight52.R] using hy
  · rw [Weight52.hD, Rat.isSquare_intCast_iff]
    rintro ⟨n, hn⟩
    have h := congrArg (fun z : ℤ => (z : ZMod 29)) hn
    push_cast at h
    exact Weight52.nonsquare n (by rw [h])

/-! ### Weight 54 -/

namespace Weight54

/-- The resolvent cubic of the weight-54 quartic, over `ℤ`. -/
noncomputable def R : ℤ[X] :=
  X ^ 3 + C (19584715019010048) * X ^ 2
    + C (-231965802664780604285009163976704) * X
    + C (-4448694761996293716971078167345064424815084961792)

/-- Axiom-free certificate: plain `ℤ` arithmetic over bounded `ℕ` (`HornerCert`). -/
lemma noRootR_cert : ∀ y : ℕ, y < 47 → ((y : ℤ) ^ 3 + (19584715019010048) * (y : ℤ) ^ 2 +
      (-231965802664780604285009163976704) * (y : ℤ) +
      (-4448694761996293716971078167345064424815084961792)) % 47 ≠ 0 := by
  decide +kernel

lemma noRootR : ∀ y : ZMod 47,
    y ^ 3 + (19584715019010048 : ZMod 47) * y ^ 2
      + (-231965802664780604285009163976704 : ZMod 47) * y
      + (-4448694761996293716971078167345064424815084961792 : ZMod 47) ≠ 0 := by
  intro y h1
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq y
  refine noRootR_cert z hz (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- The discriminant of the weight-54 quartic. -/
def Dval : ℤ :=
  33670898108132403594211663077253810797 * 10 ^ 60
    + 217667352121563148360107346892630172944577599065030656000000

/-- Axiom-free certificate (`HornerCert`): the discriminant is not a square mod 29. -/
lemma nonsquare_cert : ∀ y : ℕ, y < 29 → (Dval - (y : ℤ) * (y : ℤ)) % 29 ≠ 0 := by
  decide +kernel

/-- The discriminant is not a square mod 29. -/
lemma nonsquare : ∀ x : ZMod 29, ((Dval : ℤ) : ZMod 29) ≠ x * x := by
  intro x h1
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq x
  refine nonsquare_cert z hz (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

lemma hP : MaedaWeight54.P.map (Int.castRingHom ℚ)
    = X ^ 4 + C (68476320 : ℚ) * X ^ 3 + C (-19584715019010048 : ℚ) * X ^ 2
      + C (-1083312724663489297121280 : ℚ) * X + C (39446133467662904714689328971776 : ℚ) := by
  simp [MaedaWeight54.P, map_ofNat]

lemma hR : resolvent (68476320 : ℚ) (-19584715019010048 : ℚ) (-1083312724663489297121280 : ℚ)
      (39446133467662904714689328971776 : ℚ) = R.map (Int.castRingHom ℚ) := by
  simp [resolvent, R, map_ofNat]
  norm_num

lemma hD : disc4 (68476320 : ℚ) (-19584715019010048 : ℚ) (-1083312724663489297121280 : ℚ)
      (39446133467662904714689328971776 : ℚ) = ((Dval : ℤ) : ℚ) := by
  norm_num [disc4, Dval]

end Weight54

/-- **Maeda's conjecture in weight 54, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_54` acts on its four roots as `S₄`. -/
theorem maeda_galois54 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight54.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hirr := MaedaWeight54.maeda
  rw [Weight54.hP] at hirr ⊢
  refine galActionHom_bijective_of_quartic hirr ?_ ?_
  · have : Fact (Nat.Prime 47) := ⟨by norm_num⟩
    rw [Weight54.hR]
    refine MaedaLevelOne.irreducible_of_noRoot (by unfold Weight54.R; monicity!) ?_ 47
      fun y hy => Weight54.noRootR y ?_
    · rw [show Weight54.R.natDegree = 3 by unfold Weight54.R; compute_degree!]; decide
    · simpa [Weight54.R] using hy
  · rw [Weight54.hD, Rat.isSquare_intCast_iff]
    rintro ⟨n, hn⟩
    have h := congrArg (fun z : ℤ => (z : ZMod 29)) hn
    push_cast at h
    exact Weight54.nonsquare n (by rw [h])

/-! ### Weight 56 -/

namespace Weight56

/-- The resolvent cubic of the weight-56 quartic, over `ℤ`. -/
noncomputable def R : ℤ[X] :=
  X ^ 3 + C (69659795501724672) * X ^ 2
    + C (-1278785767850917911663371442192384) * X
    + C (-39332447916091063227336331600133628703891991298048)

/-- Axiom-free certificate: plain `ℤ` arithmetic over bounded `ℕ` (`HornerCert`). -/
lemma noRootR_cert : ∀ y : ℕ, y < 47 → ((y : ℤ) ^ 3 + (69659795501724672) * (y : ℤ) ^ 2 +
      (-1278785767850917911663371442192384) * (y : ℤ) +
      (-39332447916091063227336331600133628703891991298048)) % 47 ≠ 0 := by
  decide +kernel

lemma noRootR : ∀ y : ZMod 47,
    y ^ 3 + (69659795501724672 : ZMod 47) * y ^ 2
      + (-1278785767850917911663371442192384 : ZMod 47) * y
      + (-39332447916091063227336331600133628703891991298048 : ZMod 47) ≠ 0 := by
  intro y h1
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq y
  refine noRootR_cert z hz (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- The discriminant of the weight-56 quartic. -/
def Dval : ℤ :=
  90778194376858155463846341618250985518379 * 10 ^ 60
    + 914782083632162388683561987793062110040704076607851069440000

/-- Axiom-free certificate (`HornerCert`): the discriminant is not a square mod 29. -/
lemma nonsquare_cert : ∀ y : ℕ, y < 29 → (Dval - (y : ℤ) * (y : ℤ)) % 29 ≠ 0 := by
  decide +kernel

/-- The discriminant is not a square mod 29. -/
lemma nonsquare : ∀ x : ZMod 29, ((Dval : ℤ) : ZMod 29) ≠ x * x := by
  intro x h1
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq x
  refine nonsquare_cert z hz (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

lemma hP : MaedaWeight56.P.map (Int.castRingHom ℚ)
    = X ^ 4 + C (-208622520 : ℚ) * X ^ 3 + C (-69659795501724672 : ℚ) * X ^ 2
      + C (11031882363768735132549120 : ℚ) * X + C (-255678332805518077225389998997504 : ℚ) := by
  simp [MaedaWeight56.P, map_ofNat]

lemma hR : resolvent (-208622520 : ℚ) (-69659795501724672 : ℚ) (11031882363768735132549120 : ℚ)
      (-255678332805518077225389998997504 : ℚ) = R.map (Int.castRingHom ℚ) := by
  simp [resolvent, R, map_ofNat]
  norm_num

lemma hD : disc4 (-208622520 : ℚ) (-69659795501724672 : ℚ) (11031882363768735132549120 : ℚ)
      (-255678332805518077225389998997504 : ℚ) = ((Dval : ℤ) : ℚ) := by
  norm_num [disc4, Dval]

end Weight56

/-- **Maeda's conjecture in weight 56, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_56` acts on its four roots as `S₄`. -/
theorem maeda_galois56 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight56.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hirr := MaedaWeight56.maeda
  rw [Weight56.hP] at hirr ⊢
  refine galActionHom_bijective_of_quartic hirr ?_ ?_
  · have : Fact (Nat.Prime 47) := ⟨by norm_num⟩
    rw [Weight56.hR]
    refine MaedaLevelOne.irreducible_of_noRoot (by unfold Weight56.R; monicity!) ?_ 47
      fun y hy => Weight56.noRootR y ?_
    · rw [show Weight56.R.natDegree = 3 by unfold Weight56.R; compute_degree!]; decide
    · simpa [Weight56.R] using hy
  · rw [Weight56.hD, Rat.isSquare_intCast_iff]
    rintro ⟨n, hn⟩
    have h := congrArg (fun z : ℤ => (z : ZMod 29)) hn
    push_cast at h
    exact Weight56.nonsquare n (by rw [h])

/-! ### Weight 58 -/

namespace Weight58

/-- The resolvent cubic of the weight-58 quartic, over `ℤ`. -/
noncomputable def R : ℤ[X] :=
  X ^ 3 + C (411086477602603008) * X ^ 2
    + C (-83970534274004337362634983671332864) * X
    + C (-33406661530772641858613853476935397620808925327654912)

/-- Axiom-free certificate: plain `ℤ` arithmetic over bounded `ℕ` (`HornerCert`). -/
lemma noRootR_cert : ∀ y : ℕ, y < 53 → ((y : ℤ) ^ 3 + (411086477602603008) * (y : ℤ) ^ 2 +
      (-83970534274004337362634983671332864) * (y : ℤ) +
      (-33406661530772641858613853476935397620808925327654912)) % 53 ≠ 0 := by
  decide +kernel

lemma noRootR : ∀ y : ZMod 53,
    y ^ 3 + (411086477602603008 : ZMod 53) * y ^ 2
      + (-83970534274004337362634983671332864 : ZMod 53) * y
      + (-33406661530772641858613853476935397620808925327654912 : ZMod 53) ≠ 0 := by
  intro y h1
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq y
  refine noRootR_cert z hz (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- The discriminant of the weight-58 quartic. -/
def Dval : ℤ :=
  3467902326314543866526735027947816341671398307 * 10 ^ 60
    + 400337559553178649250593229238005486977919896097380106240000

/-- Axiom-free certificate (`HornerCert`): the discriminant is not a square mod 31. -/
lemma nonsquare_cert : ∀ y : ℕ, y < 31 → (Dval - (y : ℤ) * (y : ℤ)) % 31 ≠ 0 := by
  decide +kernel

/-- The discriminant is not a square mod 31. -/
lemma nonsquare : ∀ x : ZMod 31, ((Dval : ℤ) : ZMod 31) ≠ x * x := by
  intro x h1
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq x
  refine nonsquare_cert z hz (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

lemma hP : MaedaWeight58.P.map (Int.castRingHom ℚ)
    = X ^ 4 + C (217744560 : ℚ) * X ^ 3 + C (-411086477602603008 : ℚ) * X ^ 2
      + C (-42515907658957794091991040 : ℚ) * X + C (18678231666950985607375948785647616 : ℚ) := by
  simp [MaedaWeight58.P, map_ofNat]

lemma hR : resolvent (217744560 : ℚ) (-411086477602603008 : ℚ) (-42515907658957794091991040 : ℚ)
      (18678231666950985607375948785647616 : ℚ) = R.map (Int.castRingHom ℚ) := by
  simp [resolvent, R, map_ofNat]
  norm_num

lemma hD : disc4 (217744560 : ℚ) (-411086477602603008 : ℚ) (-42515907658957794091991040 : ℚ)
      (18678231666950985607375948785647616 : ℚ) = ((Dval : ℤ) : ℚ) := by
  norm_num [disc4, Dval]

end Weight58

/-- **Maeda's conjecture in weight 58, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_58` acts on its four roots as `S₄`. -/
theorem maeda_galois58 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight58.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hirr := MaedaWeight58.maeda
  rw [Weight58.hP] at hirr ⊢
  refine galActionHom_bijective_of_quartic hirr ?_ ?_
  · have : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    rw [Weight58.hR]
    refine MaedaLevelOne.irreducible_of_noRoot (by unfold Weight58.R; monicity!) ?_ 53
      fun y hy => Weight58.noRootR y ?_
    · rw [show Weight58.R.natDegree = 3 by unfold Weight58.R; compute_degree!]; decide
    · simpa [Weight58.R] using hy
  · rw [Weight58.hD, Rat.isSquare_intCast_iff]
    rintro ⟨n, hn⟩
    have h := congrArg (fun z : ℤ => (z : ZMod 31)) hn
    push_cast at h
    exact Weight58.nonsquare n (by rw [h])

/-! ### Weight 62 -/

namespace Weight62

/-- The resolvent cubic of the weight-62 quartic, over `ℤ`. -/
noncomputable def R : ℤ[X] :=
  X ^ 3 + C (6156169255669690368) * X ^ 2
    + C (-17245355982718527061788448056907137024) * X
    + C (-99399080093060775942196205372106815846059351474628984832)

/-- Axiom-free certificate: plain `ℤ` arithmetic over bounded `ℕ` (`HornerCert`). -/
lemma noRootR_cert : ∀ y : ℕ, y < 53 → ((y : ℤ) ^ 3 + (6156169255669690368) * (y : ℤ) ^ 2 +
      (-17245355982718527061788448056907137024) * (y : ℤ) +
      (-99399080093060775942196205372106815846059351474628984832)) % 53 ≠ 0 := by
  decide +kernel

lemma noRootR : ∀ y : ZMod 53,
    y ^ 3 + (6156169255669690368 : ZMod 53) * y ^ 2
      + (-17245355982718527061788448056907137024 : ZMod 53) * y
      + (-99399080093060775942196205372106815846059351474628984832 : ZMod 53) ≠ 0 := by
  intro y h1
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq y
  refine noRootR_cert z hz (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

/-- The discriminant of the weight-62 quartic. -/
def Dval : ℤ :=
  47733615108317839217727397393985521299829654908653475 * 10 ^ 60
    + 117858264773407979113238155503536661106523915981433077760000

/-- Axiom-free certificate (`HornerCert`): the discriminant is not a square mod 29. -/
lemma nonsquare_cert : ∀ y : ℕ, y < 29 → (Dval - (y : ℤ) * (y : ℤ)) % 29 ≠ 0 := by
  decide +kernel

/-- The discriminant is not a square mod 29. -/
lemma nonsquare : ∀ x : ZMod 29, ((Dval : ℤ) : ZMod 29) ≠ x * x := by
  intro x h1
  obtain ⟨z, hz, rfl⟩ := HornerCert.exists_natCast_eq x
  refine nonsquare_cert z hz (HornerCert.emod_eq_zero_of_cast ?_)
  push_cast
  linear_combination h1

lemma hP : MaedaWeight62.P.map (Int.castRingHom ℚ)
    = X ^ 4 + C (-1146312000 : ℚ) * X ^ 3 + C (-6156169255669690368 : ℚ) * X ^ 2
      + C (2540887466526178560442368000 : ℚ) * X
      + C (3583176547297492565952659077522784256 : ℚ) := by
  simp [MaedaWeight62.P, map_ofNat]

lemma hR : resolvent (-1146312000 : ℚ) (-6156169255669690368 : ℚ) (2540887466526178560442368000 : ℚ)
      (3583176547297492565952659077522784256 : ℚ) = R.map (Int.castRingHom ℚ) := by
  simp [resolvent, R, map_ofNat]
  norm_num

lemma hD : disc4 (-1146312000 : ℚ) (-6156169255669690368 : ℚ) (2540887466526178560442368000 : ℚ)
      (3583176547297492565952659077522784256 : ℚ) = ((Dval : ℤ) : ℚ) := by
  norm_num [disc4, Dval]

end Weight62

/-- **Maeda's conjecture in weight 62, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_62` acts on its four roots as `S₄`. -/
theorem maeda_galois62 :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight62.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hirr := MaedaWeight62.maeda
  rw [Weight62.hP] at hirr ⊢
  refine galActionHom_bijective_of_quartic hirr ?_ ?_
  · have : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    rw [Weight62.hR]
    refine MaedaLevelOne.irreducible_of_noRoot (by unfold Weight62.R; monicity!) ?_ 53
      fun y hy => Weight62.noRootR y ?_
    · rw [show Weight62.R.natDegree = 3 by unfold Weight62.R; compute_degree!]; decide
    · simpa [Weight62.R] using hy
  · rw [Weight62.hD, Rat.isSquare_intCast_iff]
    rintro ⟨n, hn⟩
    have h := congrArg (fun z : ℤ => (z : ZMod 29)) hn
    push_cast at h
    exact Weight62.nonsquare n (by rw [h])

end MaedaGalois
