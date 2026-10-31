import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.Choose

/-!
# Frobenius cycle types from factorizations mod `ℓ` (Dedekind's theorem)

The Iteration-21 core: a factorization certificate of the reduction of a
monic integer polynomial `q` modulo a prime `ℓ` (squarefree reduction, i.e.
`ℓ ∤ resultant q q.derivative`) produces an element of `Polynomial.Gal`
whose permutation of the complex roots has cycle type equal to the multiset
of the factor degrees — Dedekind's theorem in the cycle-type form the Maeda
`Sₙ` program needs.

The proof is deliberately elementary (no ideal theory in number fields, no
decomposition groups):

* `exists_frobenius_perm` (the *golden lemma*, abstract): if a finite group
  `G` acts on a finite-dimensional `F_ℓ`-algebra `A` by algebra automorphisms
  with `#G = dim A`, elements `y i` with pairwise-unit differences and `G`
  acting freely through them, then some `τ : G` and some hom `χ` satisfy
  `χ (τ • y i) = (χ (y i)) ^ ℓ` for all `i`.  Distinct algebra homs into a
  field are linearly independent (`linearIndependent_algHom_toLinearMap`,
  Dedekind), giving `#Hom ≤ dim`; freeness gives `#G ≤ #Hom`; the Frobenius
  postcomposition permutes the single `G`-orbit of homs.
* The instantiation replaces `A` by `ℤ[x₁,…,xₙ] ⊗ (ZMod ℓ)` for the roots
  `x i` of `q` in its splitting field (a finite free `ℤ`-module of rank
  `[K : ℚ] = #Gal`); the unit differences come from a Bézout certificate
  against `resultant q q.derivative` and `resultant_eq_prod_eval`.
* `frob_cycleType_of_factorization`: the packaged theorem — from a
  reflected factorization `q̄ = ∏ (X − C rᵢ) * ḡ` with `ḡ` irreducible of
  degree `≥ 2` and the `rᵢ` distinct, conclude
  `MaedaGalois.FrobHasCycleType q (replicate s 1 + {deg ḡ})`.

Everything here is light; nothing is an ancestor of the heavy
`MaedaGalois5Defs` chain.
-/

open Polynomial Module

namespace FrobeniusCert

/-! The algebraic closure of `ZMod ℓ` for `[Fact ℓ.Prime]` (any algebraically
closed `F_ℓ`-algebra would do; this one has all the instances we need). -/
section
variable {ℓ : ℕ} [Fact ℓ.Prime]

local notation "F̄" => AlgebraicClosure (ZMod ℓ)

-- Finiteness of the range of a map out of a finite type transports to a
-- `Fintype` on the coerced range (needed for the cardinality argument below;
-- Mathlib's `Set.Finite.fintype` takes the finiteness as an explicit argument
-- and so cannot be registered as an instance directly).
@[instance_reducible]
private noncomputable def rangeFintype {α β : Type*} [Finite α] (f : α → β) :
    Fintype ↑(Set.range f) :=
  Set.Finite.fintype (Set.toFinite (Set.range f))

attribute [local instance] rangeFintype

/-! ### The Dedekind count -/

/-- **The Dedekind count.**  A finite-dimensional algebra over `ZMod ℓ` has at
most `finrank`-many algebra homs into the algebraic closure `F̄`: distinct
homs are `F̄`-linearly independent as linear maps
(`linearIndependent_algHom_toLinearMap`), and evaluating a basis embeds the
homs into `F̄ ^ finrank`. -/
theorem card_algHom_le_finrank {A : Type*} [CommRing A] [Nontrivial A]
    [Algebra (ZMod ℓ) A] [Module.Finite (ZMod ℓ) A] :
    Fintype.card (A →ₐ[ZMod ℓ] F̄) ≤ Module.finrank (ZMod ℓ) A := by
  classical
  set d := Module.finrank (ZMod ℓ) A
  set b : Basis (Fin d) (ZMod ℓ) A := Module.finBasis (ZMod ℓ) A with hb
  -- the evaluated family is F̄-linearly independent, by Dedekind
  have hli : LinearIndependent F̄
      (fun (χ : A →ₐ[ZMod ℓ] F̄) (i : Fin d) => χ (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    -- the linear combination of homs vanishing on the basis is the zero map
    have hzero : (∑ χ, g χ • (χ : A →ₗ[ZMod ℓ] F̄)) = 0 := by
      refine Basis.ext b fun i => ?_
      rw [LinearMap.zero_apply]
      have h1 : ∑ χ, g χ • χ (b i) = 0 := by
        have h2 := congrFun hg i
        simpa using h2
      simpa [LinearMap.sum_apply, smul_eq_mul] using h1
    have hin := (linearIndependent_algHom_toLinearMap (ZMod ℓ) A F̄)
    rw [Fintype.linearIndependent_iff] at hin
    exact hin g hzero
  have hcard := hli.fintype_card_le_finrank (R := F̄) (M := Fin d → F̄)
  simpa [finrank_fin_fun] using hcard

/-! ### Basic structural facts -/

/-- A field extension of `ZMod ℓ` is torsion-free over `ZMod ℓ`: the algebra
map is injective (a unital map out of a field), so a regular scalar acts as a
unit. -/
instance {κ : Type*} [Field κ] [Algebra (ZMod ℓ) κ] : Module.IsTorsionFree (ZMod ℓ) κ where
  isSMulRegular r hr m₁ m₂ h := by
    have hr0 : r ≠ 0 := by
      intro h0
      exact one_ne_zero (hr.left (show r * 1 = r * 0 by simp [h0]))
    have hu : IsUnit (algebraMap (ZMod ℓ) κ r) := by
      refine IsUnit.mk0 _ ?_
      intro h0
      exact hr0 ((algebraMap (ZMod ℓ) κ).injective (by rw [h0, map_zero]))
    have h' : algebraMap (ZMod ℓ) κ r * m₁ = algebraMap (ZMod ℓ) κ r * m₂ := by
      have h2 : r • m₁ = r • m₂ := h
      rw [Algebra.smul_def, Algebra.smul_def] at h2
      exact h2
    exact hu.mul_left_cancel h'

/-- A nonzero finite `F_ℓ`-algebra admits an algebra homomorphism into the
algebraic closure: a maximal ideal gives a finite (hence algebraic) field
extension of `ZMod ℓ`, lifted into `F̄` by `IsAlgClosed.lift`. -/
theorem nonempty_algHom {A : Type*} [CommRing A] [Nontrivial A]
    [Algebra (ZMod ℓ) A] [Module.Finite (ZMod ℓ) A] :
    Nonempty (A →ₐ[ZMod ℓ] F̄) := by
  classical
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (α := A)
  have : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have : Module.Finite (ZMod ℓ) (A ⧸ 𝔪) := inferInstance
  exact ⟨(IsAlgClosed.lift : (A ⧸ 𝔪) →ₐ[ZMod ℓ] F̄).comp
    (Ideal.Quotient.mkₐ (ZMod ℓ) 𝔪)⟩

/-- The hom set `A →ₐ[ZMod ℓ] F̄` from a finite algebra is finite: each `χ a`
is a root of `minpoly (ZMod ℓ) a`, and there are only finitely many roots. -/
instance (priority := 100) finite_algHom {A : Type*} [CommRing A] [Nontrivial A]
    [Algebra (ZMod ℓ) A] [Module.Finite (ZMod ℓ) A] [Fintype A] :
    Finite (A →ₐ[ZMod ℓ] F̄) := by
  classical
  have hroot : ∀ (χ : A →ₐ[ZMod ℓ] F̄) (a : A),
      χ a ∈ (minpoly (ZMod ℓ) a).rootSet F̄ := by
    intro χ a
    refine Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero (IsIntegral.of_finite (ZMod ℓ) a), ?_⟩
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  refine Finite.of_injective
    (fun (χ : A →ₐ[ZMod ℓ] F̄) (a : A) =>
      (⟨χ a, hroot χ a⟩ : (minpoly (ZMod ℓ) a).rootSet F̄)) ?_
  intro χ₁ χ₂ h
  exact AlgHom.ext fun a => congrArg Subtype.val (congrFun h a)

/-! ### The golden lemma -/

/-- **The golden lemma.**  Let a finite group `G` act on a nonzero
finite-dimensional `F_ℓ`-algebra `A` through algebra automorphisms, with
distinguished elements `y i` whose pairwise differences are units, such that
`G` permutes the `y i` and acts freely through them, and `#G = dim A`.
Then some group element `τ` and some algebra homomorphism `χ : A →ₐ F̄`
satisfy `χ (τ • y i) = (χ (y i)) ^ ℓ` for every `i`.

The proof: `χ ↦ χ ∘ τ` acts freely on the homs (the `χ (y i)` are distinct,
because the differences are units), the Dedekind count bounds `#homs ≤ #G`,
so the orbit of any `χ₀` is everything, and the Frobenius postcomposition
`χ ↦ (· ^ ℓ) ∘ χ` commutes with the `G`-action. -/
theorem exists_frobenius_perm {A : Type*} [CommRing A] [Nontrivial A]
    [Algebra (ZMod ℓ) A] [Module.Finite (ZMod ℓ) A] [Fintype A]
    {G : Type*} [Group G] [Fintype G]
    (act : G →* (A ≃ₐ[ZMod ℓ] A)) (y : Fin n → A)
    (hperm : ∀ g : G, ∀ i, ∃ j, act g (y i) = y j)
    (hfree : ∀ g : G, (∀ i, act g (y i) = y i) → g = 1)
    (hunit : ∀ i j, i ≠ j → IsUnit (y i - y j))
    (hcard : Fintype.card G = Module.finrank (ZMod ℓ) A) :
    ∃ (χ : A →ₐ[ZMod ℓ] F̄) (τ : G) (π : Equiv.Perm (Fin n)),
      (∀ i, act τ (y i) = y (π i)) ∧
      ∀ i, χ (y (π i)) = χ (y i) ^ (ℓ : ℕ) := by
  classical
  -- composition of two group elements acting on an element, and the identity
  have hactmul : ∀ (g₁ g₂ : G) (a : A), act (g₁ * g₂) a = act g₁ (act g₂ a) := by
    intro g₁ g₂ a
    rw [map_mul]; rfl
  have hactone : ∀ a : A, act 1 a = a := by
    intro a
    rw [map_one]; rfl
  -- (0) every hom separates the y i, because it maps unit differences to units
  have hdist : ∀ χ : A →ₐ[ZMod ℓ] F̄, ∀ i j, i ≠ j → χ (y i) ≠ χ (y j) := by
    intro χ i j hij hcontr
    have h1 : χ (y i - y j) = 0 := by
      rw [map_sub, hcontr, sub_self]
    exact absurd (IsUnit.map χ.toRingHom (hunit i j hij)) (fun hu => hu.ne_zero h1)
  have hyinj : Function.Injective y := by
    intro i j hij
    by_contra hne
    exact hdist (nonempty_algHom.some) i j hne (by rw [hij])
  -- (1) the orbit map g ↦ χ₀ ∘ act g is injective
  obtain ⟨χ₀⟩ := nonempty_algHom (ℓ := ℓ) (A := A)
  set Φ : G → (A →ₐ[ZMod ℓ] F̄) := fun g => χ₀.comp (act g).toAlgHom with hΦdef
  have hΦapply : ∀ (g : G) (a : A), Φ g a = χ₀ (act g a) := fun _ _ => rfl
  have hΦinj : Function.Injective Φ := by
    intro g g' hgg'
    have hfix : ∀ i, act (g⁻¹ * g') (y i) = y i := by
      intro i
      obtain ⟨a, ha⟩ := hperm g i
      obtain ⟨b, hb⟩ := hperm g' i
      have hEq' : χ₀ (act g (y i)) = χ₀ (act g' (y i)) := by
        rw [← hΦapply, ← hΦapply]
        exact congrArg (fun φ => φ (y i)) hgg'
      rw [ha, hb] at hEq'
      have hab : a = b := by
        rcases eq_or_ne a b with hab | hab
        · exact hab
        · exact absurd hEq' (hdist χ₀ a b hab)
      have hEq : act g' (y i) = act g (y i) := by rw [hb, ← hab, ← ha]
      calc act (g⁻¹ * g') (y i) = act g⁻¹ (act g' (y i)) := hactmul _ _ _
        _ = act g⁻¹ (act g (y i)) := by rw [hEq]
        _ = act (g⁻¹ * g) (y i) := (hactmul _ _ _).symm
        _ = y i := by rw [inv_mul_cancel, hactone]
    have h1 : g⁻¹ * g' = 1 := hfree _ hfix
    rw [← mul_one g, ← h1, mul_inv_cancel_left]
  -- (2) the Dedekind count bounds the homs by #G, so the orbit is everything
  have hcount : Fintype.card (A →ₐ[ZMod ℓ] F̄) ≤ Fintype.card G :=
    (card_algHom_le_finrank (ℓ := ℓ) (A := A)).trans hcard.symm.le
  have hle2 : Fintype.card G ≤ Fintype.card (A →ₐ[ZMod ℓ] F̄) :=
    Fintype.card_le_of_injective Φ hΦinj
  have heq : Fintype.card (A →ₐ[ZMod ℓ] F̄) = Fintype.card G := le_antisymm hcount hle2
  have hsurj : ∀ χ : A →ₐ[ZMod ℓ] F̄, ∃ τ : G, Φ τ = χ := by
    have hcardrange : Fintype.card (Set.range Φ) = Fintype.card (A →ₐ[ZMod ℓ] F̄) := by
      rw [Set.card_range_of_injective hΦinj, heq.symm]
    intro χ
    have hbinj : Function.Bijective ((↑) : Set.range Φ → (A →ₐ[ZMod ℓ] F̄)) := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨Subtype.val_injective, hcardrange⟩
    obtain ⟨x, hx⟩ := hbinj.surjective χ
    obtain ⟨τ, hτ⟩ := x.2
    exact ⟨τ, hτ.trans hx⟩
  -- (3) the Frobenius postcomposition is a hom, hence lands in the orbit
  obtain ⟨τ, hτ⟩ := hsurj ((FiniteField.frobeniusAlgHom (ZMod ℓ) F̄).comp χ₀)
  -- (4) the action of τ on the y i is a permutation, and χ₀ conjugates it to
  -- the Frobenius on the χ₀ (y i)
  have hfun : ∃ f : Fin n → Fin n, ∀ i, act τ (y i) = y (f i) :=
    ⟨fun i => Classical.choose (hperm τ i), fun i => Classical.choose_spec (hperm τ i)⟩
  obtain ⟨f, hf⟩ := hfun
  have hfinj : Function.Injective f := by
    intro i j hij
    refine hyinj ?_
    have h2 : act τ (y i) = act τ (y j) := by rw [hf i, hf j, hij]
    exact (act τ).injective h2
  refine ⟨χ₀, τ, Equiv.ofBijective f hfinj.bijective_of_finite, hf, ?_⟩
  intro i
  change χ₀ (y (f i)) = χ₀ (y i) ^ (ℓ : ℕ)
  rw [← hf i, ← hΦapply τ (y i), hτ, AlgHom.comp_apply,
    FiniteField.coe_frobeniusAlgHom, ZMod.card]

end

/-! ### The factorization certificate: the resultant does not vanish mod `ℓ`

The per-weight input for the Maeda program is a factorization certificate:
the reduction `Qb` of a monic integer polynomial factors as `(X - C r) * gb`
with `gb` monic irreducible of degree `n - 1 ≥ 2` and `gb(r) ≠ 0`.  This
section derives the consequence used by the Dedekind machinery: the integer
resultant `Res(q, q')` does not vanish mod `ℓ`, and `Qb` is coprime to its
derivative. -/

section Certificate

variable {q : ℤ[X]} {ℓ : ℕ} [Fact ℓ.Prime]

/-- Coprimality is stable under adding a multiple of the first argument to
the second. -/
private theorem isCoprime_add_mul_self {R : Type*} [CommRing R] {x y z : R}
    (h : IsCoprime x y) : IsCoprime x (y + x * z) := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨u - v * z, v, ?_⟩
  rw [mul_add, sub_mul]
  linear_combination huv

/-- Coprimality is stable under adding the first argument to the second. -/
private theorem isCoprime_add_self {R : Type*} [CommRing R] {x y : R}
    (h : IsCoprime x y) : IsCoprime x (x + y) := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨u - v, v, ?_⟩
  rw [sub_mul, mul_add]
  linear_combination huv

/-- Over the perfect field `ZMod ℓ`, a polynomial of degree `≥ 2` whose
derivative vanishes is not irreducible: irreducibility would force separability
(`PerfectField.separable_of_irreducible`), and separability with zero
derivative forces the polynomial to be a unit. -/
theorem not_irreducible_of_derivative_eq_zero {gb : (ZMod ℓ)[X]}
    (hdeg : 2 ≤ gb.natDegree) (hd : gb.derivative = 0) : ¬ Irreducible gb := by
  have hpF : PerfectField (ZMod ℓ) := PerfectRing.toPerfectField (ZMod ℓ) ℓ
  intro hirr
  obtain ⟨u, v, huv⟩ := hpF.separable_of_irreducible hirr
  rw [hd, mul_zero, add_zero] at huv
  have hu : IsUnit gb := IsUnit.of_mul_eq_one (a := gb) u (by rw [mul_comm]; exact huv)
  obtain ⟨r, -, hrC⟩ := Polynomial.isUnit_iff.mp hu
  rw [hrC.symm, Polynomial.natDegree_C] at hdeg
  omega

/-- **The factorization certificate.**  If a monic `q : ℤ[X]` reduces mod `ℓ`
as `(X - C r) * gb` with `gb` monic irreducible of degree `q.natDegree - 1 ≥ 2`,
`gb(r) ≠ 0` and `ℓ ∤ q.natDegree`, then the integer resultant `Res(q, q')`
is nonzero mod `ℓ`, and `Qb` is coprime to its derivative. -/
theorem resultant_ne_zero_of_linear_mul_irreducible
    (hq : q.Monic) (hln : (q.natDegree : ZMod ℓ) ≠ 0)
    (r : ZMod ℓ) (gb : (ZMod ℓ)[X]) (_hgbm : gb.Monic)
    (hdeg : gb.natDegree = q.natDegree - 1) (h2 : 2 ≤ gb.natDegree)
    (hirr : Irreducible gb) (hrgb : gb.eval r ≠ 0)
    (hfact : q.map (Int.castRingHom (ZMod ℓ)) = (X - C r) * gb) :
    (q.resultant q.derivative : ZMod ℓ) ≠ 0 ∧
      IsCoprime (q.map (Int.castRingHom (ZMod ℓ)))
        ((q.map (Int.castRingHom (ZMod ℓ))).derivative) := by
  classical
  set Qb := q.map (Int.castRingHom (ZMod ℓ)) with hQb
  have hpF : PerfectField (ZMod ℓ) := PerfectRing.toPerfectField (ZMod ℓ) ℓ
  have hQbm : Qb.Monic := hq.map _
  have hQbd : Qb.natDegree = q.natDegree :=
    Polynomial.Monic.natDegree_map hq (Int.castRingHom (ZMod ℓ))
  -- the derivative of Qb in factored form
  have hQb' : Qb.derivative = gb + (X - C r) * gb.derivative := by
    rw [hfact, derivative_mul, derivative_X_sub_C, one_mul]
  -- gb' ≠ 0: gb is separable (irreducible over the perfect field ZMod ℓ)
  have hgb'ne : gb.derivative ≠ 0 :=
    (Polynomial.separable_iff_derivative_ne_zero hirr).mp
      (hpF.separable_of_irreducible hirr)
  -- gb does not divide its derivative
  have hnd : ¬ (gb ∣ gb.derivative) := by
    intro hdvd
    rcases eq_or_ne gb.derivative 0 with h0 | h0
    · exact hgb'ne h0
    · refine hgb'ne (Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd ?_)
      refine Polynomial.natDegree_derivative_lt ?_
      rw [hdeg]
      omega
  -- IsCoprime (X - C r, gb): the factor theorem against gb(r) ≠ 0
  have hc1 : IsCoprime (X - C r) gb := by
    have hdvd : (X - C r) ∣ gb - C (gb.eval r) := by
      refine Polynomial.dvd_iff_isRoot.mpr ?_
      rw [IsRoot, Polynomial.eval_sub, Polynomial.eval_C]
      ring
    obtain ⟨s, hs⟩ := dvd_iff_exists_eq_mul_left.mp hdvd
    have hbez : C ((gb.eval r)⁻¹) * gb - 1 = C ((gb.eval r)⁻¹) * (s * (X - C r)) := by
      have h1 : C ((gb.eval r)⁻¹) * (gb - C (gb.eval r))
          = C ((gb.eval r)⁻¹) * (s * (X - C r)) := by rw [hs]
      rw [mul_sub] at h1
      rwa [← Polynomial.C_mul, inv_mul_cancel₀ hrgb, Polynomial.C_1] at h1
    have hbez' : (-(C ((gb.eval r)⁻¹) * s)) • (X - C r) +
        (C ((gb.eval r)⁻¹)) • gb = 1 := by
      simp only [smul_eq_mul, neg_mul]
      linear_combination hbez
    exact ⟨-(C ((gb.eval r)⁻¹) * s), C ((gb.eval r)⁻¹), hbez'⟩
  -- IsCoprime (X - C r, Qb') and IsCoprime (gb, Qb'), via the factored derivative
  have hc3 : IsCoprime (X - C r) (gb + (X - C r) * gb.derivative) :=
    isCoprime_add_mul_self hc1
  have hc2 : IsCoprime gb (gb + (X - C r) * gb.derivative) :=
    isCoprime_add_self (IsCoprime.mul_right hc1.symm
      ((EuclideanDomain.dvd_or_coprime gb gb.derivative hirr).resolve_left hnd))
  -- the coprimality of Qb and its derivative
  have hcop : IsCoprime Qb Qb.derivative := by
    rw [hQb', hfact]
    exact IsCoprime.mul_left hc3 hc2
  refine ⟨?_, hcop⟩
  -- the resultant transport
  have h1 : Qb.resultant Qb.derivative ≠ 0 :=
    Polynomial.resultant_ne_zero _ _ hcop
  have h3 : q.natDegree - 1 + 1 = q.natDegree := by omega
  have hz : ((q.natDegree - 1 : ℕ) : ℤ) + 1 = ((q.natDegree : ℕ) : ℤ) :=
    ((Nat.cast_add_one (q.natDegree - 1)).symm.trans (congrArg Nat.cast (by omega)))
  have hdnat : (q.derivative).natDegree = q.natDegree - 1 := by
    refine le_antisymm (Polynomial.natDegree_derivative_le _) ?_
    refine le_natDegree_of_ne_zero ?_
    rw [Polynomial.coeff_derivative, h3, Polynomial.coeff_natDegree, hq.leadingCoeff,
      one_mul, hz]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hdQb' : Qb.derivative.natDegree = q.derivative.natDegree := by
    rw [derivative_map]
    refine le_antisymm (Polynomial.natDegree_map_le (f := Int.castRingHom (ZMod ℓ))
      (p := q.derivative)) ?_
    refine le_natDegree_of_ne_zero ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_derivative, hdnat, h3,
      Polynomial.coeff_natDegree, hq.leadingCoeff, one_mul, hz, Int.coe_castRingHom]
    simp only [Int.cast_natCast]
    exact isUnit_iff_ne_zero.mpr hln |>.ne_zero
  have hres : (q.resultant q.derivative : ZMod ℓ) = Qb.resultant Qb.derivative := by
    rw [hQbd, hdQb', hQb, derivative_map,
      show ((q.resultant q.derivative : ℤ) : ZMod ℓ) =
        (Int.castRingHom (ZMod ℓ)) (q.resultant q.derivative) from rfl]
    exact (Polynomial.resultant_map_map _ _ _ _ _).symm
  rw [hres]
  exact h1

end Certificate
end FrobeniusCert
