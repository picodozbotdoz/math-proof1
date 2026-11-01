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
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Algebra.ZMod
import MathProof.ModularForms.MaedaPermCriterion

/-!
# Frobenius cycle types from factorizations mod `ℓ` (Dedekind's theorem)

The Iteration-21 core: a factorization certificate of the reduction of a
monic integer polynomial `q` modulo a prime `ℓ` (squarefree reduction, i.e.
`ℓ ∤ resultant q q.derivative`) produces an element of `Polynomial.Gal`
whose permutation of the complex roots has cycle type equal to the multiset
of the factor degrees — Dedekind's theorem in the cycle-type form the Maeda
`Sₙ` program needs.

The route (`frob_cycleType_of_factorization`):

* `IsArithFrobAt.exists_of_isInvariant` (Mathlib) gives a Frobenius `σ` at a
  maximal ideal `𝔪` over `ℓ` of the root order `O = ℤ[x₁,…,xₙ]` inside the
  splitting field: the group acts on `O`, and `ℤ` is the invariant ring.
* Separability of the reduction makes the reduced roots distinct in `O ⧸ 𝔪`, so
  `σ` acts on them as the `ℓ`-power map.
* `cycleType_of_frobenius_roots`: such a permutation fixes the roots of the
  linear factors and is a single cycle on the roots of the irreducible factor
  (its orbits are bounded below through `FiniteField.orderOf_frobeniusAlgHom`).

The earlier sections (`exists_frobenius_perm`, a Dedekind-count proof of the
Frobenius step, and `resultant_ne_zero_of_linear_mul_irreducible`) are not used
by this route.

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
    [Algebra (ZMod ℓ) A] [Module.Finite (ZMod ℓ) A] [Finite A] :
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
    [Algebra (ZMod ℓ) A] [Module.Finite (ZMod ℓ) A] [Finite A]
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

/-! ### The Frobenius orbits on the roots of a factored reduction

The finite-field half of Dedekind's theorem, stated for an arbitrary field `F`
over `ZMod ℓ` and an arbitrary index type: a permutation of a separable root
family that acts as the `ℓ`-power map fixes the roots of the linear factors and
is one cycle on the roots of the irreducible factor. -/

section Orbit

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- A root `α` of an irreducible `gb` over `ZMod ℓ` satisfying `α ^ ℓ ^ k = α`
forces `deg gb ≤ k`: the root of `gb` in `AdjoinRoot gb` satisfies the same
identity, so the `k`-th power of the Frobenius of that field is trivial, and the
Frobenius has order `deg gb` (`FiniteField.orderOf_frobeniusAlgHom`). -/
theorem natDegree_le_of_pow_eq {F : Type*} [Field F] [Algebra (ZMod ℓ) F]
    {gb : (ZMod ℓ)[X]} (hgm : gb.Monic) (hirr : Irreducible gb) {α : F}
    (hα : aeval α gb = 0) {k : ℕ} (hk : 0 < k) (hpow : α ^ ℓ ^ k = α) :
    gb.natDegree ≤ k := by
  have : Fact (Irreducible gb) := ⟨hirr⟩
  have hne : gb ≠ 0 := hirr.ne_zero
  have hfin : Module.Finite (ZMod ℓ) (AdjoinRoot gb) := (AdjoinRoot.powerBasis hne).finite
  have : Finite (AdjoinRoot gb) := Module.finite_of_finite (ZMod ℓ)
  have hdvd : gb ∣ X ^ ℓ ^ k - X := by
    rw [minpoly.eq_of_irreducible_of_monic hirr hα hgm]
    exact minpoly.dvd _ _ (by simp [hpow])
  have hθ : AdjoinRoot.root gb ^ ℓ ^ k = AdjoinRoot.root gb := by
    obtain ⟨c, hc⟩ := hdvd
    have h0 : aeval (AdjoinRoot.root gb) (X ^ ℓ ^ k - X : (ZMod ℓ)[X]) = 0 := by
      rw [hc, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
    simpa [sub_eq_zero] using h0
  have hone : FiniteField.frobeniusAlgHom (ZMod ℓ) (AdjoinRoot gb) ^ k = 1 := by
    refine AdjoinRoot.algHom_ext ?_
    rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
    exact hθ
  have hle := Nat.le_of_dvd hk (orderOf_dvd_of_pow_eq_one hone)
  rwa [FiniteField.orderOf_frobeniusAlgHom, (AdjoinRoot.powerBasis hne).finrank,
    AdjoinRoot.powerBasis_dim] at hle

/-- **The Frobenius orbits.**  Let `y` be an injective family in a field `F` over
`ZMod ℓ` with `∏ᵢ (X - y i)` the image of `∏_{r ∈ rs} (X - r) * gb`, `gb` monic
irreducible of degree `≥ 2`.  A permutation acting on the family as the `ℓ`-power
map has cycle type exactly `{deg gb}`: it fixes the roots coming from `rs`, and
any cycle through a root of `gb` has length `≥ deg gb` by
`natDegree_le_of_pow_eq`, hence exhausts those `≤ deg gb` roots. -/
theorem cycleType_of_frobenius_roots {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    [Algebra (ZMod ℓ) F] (rs : Finset (ZMod ℓ)) {gb : (ZMod ℓ)[X]} (hgm : gb.Monic)
    (hirr : Irreducible gb) (h2 : 2 ≤ gb.natDegree) (y : ι → F)
    (hy : Function.Injective y) (π : Equiv.Perm ι) (hπ : ∀ i, y (π i) = y i ^ ℓ)
    (hprod : ∏ i, (X - C (y i)) =
      ((∏ r ∈ rs, (X - C r)) * gb).map (algebraMap (ZMod ℓ) F)) :
    π.cycleType = {gb.natDegree} := by
  classical
  have hiter : ∀ (k : ℕ) (i : ι), y ((π ^ k) i) = y i ^ ℓ ^ k := by
    intro k i
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, hπ, ih, ← pow_mul, pow_succ]
  -- every `y i` is a root of a linear factor or of `gb`
  have hroot : ∀ i, (∃ r ∈ rs, y i = algebraMap (ZMod ℓ) F r) ∨ aeval (y i) gb = 0 := by
    intro i
    have h0 : eval (y i) (∏ j, (X - C (y j))) = 0 := by
      rw [eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    rw [hprod, eval_map_algebraMap, map_mul, map_prod, mul_eq_zero,
      Finset.prod_eq_zero_iff] at h0
    rcases h0 with ⟨r, hr, h⟩ | h
    · refine Or.inl ⟨r, hr, ?_⟩
      simpa [sub_eq_zero] using h
    · exact Or.inr h
  -- the linear roots are fixed
  have hfix : ∀ i, (∃ r ∈ rs, y i = algebraMap (ZMod ℓ) F r) → π i = i := by
    rintro i ⟨r, -, hr⟩
    refine hy ?_
    rw [hπ, hr, ← map_pow, ZMod.pow_card]
  -- at most `deg gb` indices are roots of `gb`
  set S : Finset ι := Finset.univ.filter fun i => aeval (y i) gb = 0 with hS
  have hScard : S.card ≤ gb.natDegree := by
    have hsub : S.image y ⊆ ((gb.map (algebraMap (ZMod ℓ) F)).roots).toFinset := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      have hi' : aeval (y i) gb = 0 := (Finset.mem_filter.mp hi).2
      refine Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨(hgm.map _).ne_zero, ?_⟩)
      rwa [IsRoot.def, eval_map_algebraMap]
    calc S.card = (S.image y).card := (Finset.card_image_of_injective _ hy).symm
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Multiset.toFinset_card_le _
      _ ≤ _ := card_roots' _
      _ ≤ gb.natDegree := natDegree_map_le
  have hsupp : π.support ⊆ S := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
    exact (hroot i).resolve_left fun h => Equiv.Perm.mem_support.mp hi (hfix i h)
  -- the degree count: there are more indices than linear factors
  have hcard : Fintype.card ι = rs.card + gb.natDegree := by
    have hL : (∏ r ∈ rs, (X - C r) : (ZMod ℓ)[X]).Monic :=
      monic_prod_of_monic _ _ fun r _ => monic_X_sub_C r
    have h1 := congrArg natDegree hprod
    rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C (y j),
      (hL.mul hgm).natDegree_map, hL.natDegree_mul hgm,
      natDegree_prod_of_monic _ _ fun r _ => monic_X_sub_C r] at h1
    simpa using h1
  obtain ⟨i₀, hi₀⟩ : ∃ i, ¬ ∃ r ∈ rs, y i = algebraMap (ZMod ℓ) F r := by
    by_contra hall
    push Not at hall
    have hsub : Finset.univ.image y ⊆ rs.image (algebraMap (ZMod ℓ) F) := by
      intro a ha
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨r, hr, h⟩ := hall i
      exact Finset.mem_image.mpr ⟨r, hr, h.symm⟩
    have hle : Fintype.card ι ≤ rs.card := by
      calc Fintype.card ι = (Finset.univ.image y).card :=
            (Finset.card_image_of_injective _ hy).symm
        _ ≤ (rs.image (algebraMap (ZMod ℓ) F)).card := Finset.card_le_card hsub
        _ ≤ rs.card := Finset.card_image_le
    omega
  have hα : aeval (y i₀) gb = 0 := (hroot i₀).resolve_left hi₀
  -- a return to `i₀` after `k > 0` steps takes at least `deg gb` steps
  have hret : ∀ k, 0 < k → (π ^ k) i₀ = i₀ → gb.natDegree ≤ k := by
    intro k hk h
    refine natDegree_le_of_pow_eq hgm hirr hα hk ?_
    rw [← hiter, h]
  have hne : π i₀ ≠ i₀ := by
    intro h
    have := hret 1 one_pos (by simpa using h)
    omega
  -- the cycle through `i₀` is everything
  have hc := Equiv.Perm.isCycle_cycleOf π hne
  set c := π.cycleOf i₀ with hcdef
  have hmge : gb.natDegree ≤ c.support.card := by
    refine hret _ (by have := hc.two_le_card_support; omega) ?_
    rw [← Equiv.Perm.cycleOf_pow_apply_self, ← hcdef, ← hc.orderOf, pow_orderOf_eq_one,
      Equiv.Perm.one_apply]
  have hsubs : c.support ⊆ π.support := Equiv.Perm.support_cycleOf_le π i₀
  have hsame : c.support = π.support :=
    Finset.eq_of_subset_of_card_le hsubs
      ((Finset.card_le_card hsupp).trans (hScard.trans hmge))
  have hπc : π = c := by
    ext a
    by_cases ha : a ∈ π.support
    · have hsc := (Equiv.Perm.mem_support_cycleOf_iff.mp (hsame ▸ ha)).1
      exact hsc.cycleOf_apply.symm
    · have h1 : π a = a := Equiv.Perm.notMem_support.mp ha
      have h2 : c a = a := Equiv.Perm.notMem_support.mp (hsame ▸ ha)
      rw [h1, h2]
  have hcard' : c.support.card = gb.natDegree :=
    le_antisymm (by rw [hsame]; exact (Finset.card_le_card hsupp).trans hScard) hmge
  rw [hπc, hc.cycleType, hcard']

/-- The reduction `∏_{r ∈ rs} (X - r) * gb` is separable when `deg gb ≥ 2`: `gb` is
irreducible over the perfect field `ZMod ℓ`, hence has no root, and the linear
factors are distinct. -/
theorem separable_prod_mul {rs : Finset (ZMod ℓ)} {gb : (ZMod ℓ)[X]}
    (hirr : Irreducible gb) (h2 : 2 ≤ gb.natDegree) :
    ((∏ r ∈ rs, (X - C r)) * gb).Separable := by
  have hpF : PerfectField (ZMod ℓ) := PerfectRing.toPerfectField (ZMod ℓ) ℓ
  refine Separable.mul ?_ (hpF.separable_of_irreducible hirr) ?_
  · exact separable_prod_X_sub_C_iff'.mpr fun a _ b _ h => h
  · refine IsCoprime.prod_left fun r hr => ?_
    refine (irreducible_X_sub_C r).coprime_iff_not_dvd.mpr ?_
    rw [dvd_iff_isRoot]
    intro hroot
    have hd := degree_eq_one_of_irreducible_of_root hirr hroot
    have hnat : gb.natDegree = 1 := natDegree_eq_of_degree_eq_some (n := 1) (by rw [hd]; rfl)
    omega

end Orbit

/-! ### The Dedekind/Frobenius instantiation

Mathlib's `IsArithFrobAt.exists_of_isInvariant` (`Mathlib.RingTheory.Frobenius`)
provides the Frobenius element directly: the finite group `Q.Gal` acts on the
root order `O = ℤ[x₁,…,xₙ]` inside the splitting field `K` of `Q = q.map ℚ`,
`ℤ` is the invariant base, and a maximal ideal `𝔪` of `O` over `ℓ` has finite
residue.  Reducing the roots modulo `𝔪` transports `σ`'s permutation of the
roots to the Frobenius `x ↦ x^ℓ` on the reduced roots, whose orbits are exactly
the factor degrees of the reduction of `Q` modulo `ℓ`. -/

section Dedekind

open Polynomial.Gal

variable {q : ℤ[X]} {n : ℕ}

/-- The rational polynomial attached to `q : ℤ[X]`. -/
noncomputable abbrev ratOf (q : ℤ[X]) : ℚ[X] := q.map (Int.castRingHom ℚ)

/-- The splitting field of the rational polynomial attached to `q`. -/
noncomputable abbrev splField (q : ℤ[X]) : Type := (ratOf q).SplittingField

/-- The roots of the rational polynomial attached to `q` in its splitting
field, enumerated by `Fin n`. -/
noncomputable def rootsE (hcard : Fintype.card ((ratOf q).rootSet (splField q)) = n) :
    Fin n ≃ (ratOf q).rootSet (splField q) := (Fintype.equivFinOfCardEq hcard).symm

/-- The `i`-th enumerated root, as an element of the splitting field. -/
noncomputable def rootK (x : Fin n ≃ (ratOf q).rootSet (splField q)) (i : Fin n) :
    splField q := (x i : (ratOf q).rootSet (splField q))

/-- The root order `O = ℤ[x₁,…,xₙ]` as a `ℤ`-subalgebra of the splitting
field. -/
noncomputable def rootOrder (x : Fin n ≃ (ratOf q).rootSet (splField q)) :
    Subalgebra ℤ (splField q) :=
  Algebra.adjoin ℤ (Set.range (rootK x))

theorem rootK_mem (x : Fin n ≃ (ratOf q).rootSet (splField q)) (i : Fin n) :
    rootK x i ∈ rootOrder x :=
  Algebra.mem_adjoin_of_mem (Set.mem_range_self i)

/-- `algebraMap ℤ K` factors through `ℚ`. -/
theorem algebraMap_int_eq (q : ℤ[X]) :
    algebraMap ℤ (splField q) = (algebraMap ℚ (splField q)).comp (Int.castRingHom ℚ) := by
  ext a
  simp

theorem rootK_isIntegral (hq : q.Monic)
    (x : Fin n ≃ (ratOf q).rootSet (splField q)) (i : Fin n) :
    IsIntegral ℤ (rootK x i) := by
  have hroot : Polynomial.eval (rootK x i)
      ((ratOf q).map (algebraMap ℚ (splField q))) = 0 := by
    rw [Polynomial.eval_map]
    exact (Polynomial.mem_rootSet.mp (x i).2).2
  refine ⟨q, hq, ?_⟩
  rw [← Polynomial.eval_map, algebraMap_int_eq, ← map_map]
  exact hroot

/-- Every element of the root order is integral over `ℤ`. -/
theorem rootOrder_isIntegral (hq : q.Monic)
    (x : Fin n ≃ (ratOf q).rootSet (splField q)) (a : rootOrder x) :
    IsIntegral ℤ ((a : rootOrder x) : splField q) := by
  have hint : Algebra.IsIntegral ℤ (rootOrder x) :=
    Algebra.IsIntegral.adjoin (fun b hb => by
      obtain ⟨j, hj⟩ := Set.mem_range.mp hb
      exact hj ▸ rootK_isIntegral hq x j)
  exact IsIntegral.map (IsScalarTower.toAlgHom ℤ (rootOrder x) (splField q))
    (hint.isIntegral a)

/-- The root order is a finite `ℤ`-module. -/
theorem rootOrder_finite (hq : q.Monic)
    (x : Fin n ≃ (ratOf q).rootSet (splField q)) : Module.Finite ℤ (rootOrder x) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range (rootK x))
    (fun b hb => by
      obtain ⟨j, hj⟩ := Set.mem_range.mp hb
      exact hj ▸ rootK_isIntegral hq x j)

/-- The splitting field of a separable polynomial is Galois. -/
theorem isGalois_splField (hsep : (ratOf q).Separable) : IsGalois ℚ (splField q) :=
  IsGalois.of_separable_splitting_field hsep

/-! ### The action of the Galois group on the root order -/

section Action

variable (x : Fin n ≃ (ratOf q).rootSet (splField q))

private theorem algebraMap_int_apply (z : ℤ) :
    algebraMap ℤ (splField q) z = algebraMap ℚ (splField q) ((z : ℤ) : ℚ) := by
  rw [algebraMap_int_eq]
  simp

/-- A Galois element, as a `ℚ`-algebra automorphism of the splitting field. -/
private noncomputable def galE (σ : (ratOf q).Gal) :
    splField q ≃ₐ[ℚ] splField q := σ

private theorem smul_eq_coe (σ : (ratOf q).Gal) (y : splField q) :
    σ • y = galE σ y := rfl

/-- Each group element permutes the enumerated roots. -/
theorem rootK_smul (σ : (ratOf q).Gal) (i : Fin n) :
    ∃ j, σ • rootK x i = rootK x j := by
  have hmem : (galE σ).toAlgHom (rootK x i) ∈ (ratOf q).rootSet (splField q) :=
    rootSet_mapsTo (galE σ).toAlgHom (x i).2
  refine ⟨x.symm ⟨σ • rootK x i, hmem⟩, ?_⟩
  have h1 := Equiv.apply_symm_apply x ⟨σ • rootK x i, hmem⟩
  exact (congrArg Subtype.val h1).symm

/-- Each Galois element acts as a `ℤ`-algebra endomorphism of the splitting
field. -/
noncomputable def toAlgHomInt (σ : (ratOf q).Gal) : splField q →ₐ[ℤ] splField q where
  toFun y := σ • y
  map_one' := smul_one σ
  map_mul' y₁ y₂ := MulSemiringAction.smul_mul σ y₁ y₂
  map_zero' := smul_zero σ
  map_add' := smul_add σ
  commutes' z := by
    change σ • (algebraMap ℤ (splField q)) z = (algebraMap ℤ (splField q)) z
    rw [algebraMap_int_apply, smul_eq_coe]
    exact AlgEquiv.commutes _ _

/-- The root order is stable under the Galois action. -/
theorem rootOrder_smul_mem (σ : (ratOf q).Gal) (a : rootOrder x) :
    σ • ((a : rootOrder x) : splField q) ∈ rootOrder x := by
  have hss : ∀ (τ : (ratOf q).Gal) (y : splField q), y ∈ Set.range (rootK x) →
      τ • y ∈ Set.range (rootK x) := by
    intro τ y hy
    obtain ⟨i, rfl⟩ := Set.mem_range.mp hy
    obtain ⟨j, hj⟩ := rootK_smul x τ i
    exact ⟨j, hj.symm⟩
  have himg : ((toAlgHomInt σ : splField q → splField q)) '' Set.range (rootK x)
      = Set.range (rootK x) := by
    refine Set.eq_of_subset_of_subset ?_ ?_
    · rw [Set.image_subset_iff]
      exact hss σ
    · intro y hy
      refine ⟨toAlgHomInt σ⁻¹ y, hss σ⁻¹ y hy, ?_⟩
      change σ • (σ⁻¹ • y) = y
      have h2 : ((σ * σ⁻¹ : (ratOf q).Gal) • y) = y := by
        rw [mul_inv_cancel, one_smul]
      rwa [mul_smul] at h2
  have hmap : (toAlgHomInt σ) ((a : rootOrder x) : splField q)
      ∈ Subalgebra.map (toAlgHomInt σ)
        (Algebra.adjoin ℤ (Set.range (rootK x))) :=
    Subalgebra.mem_map.mpr ⟨a, a.2, rfl⟩
  rw [AlgHom.map_adjoin, himg] at hmap
  exact hmap

end Action

section ActionInst

variable {x : Fin n ≃ (ratOf q).rootSet (splField q)}

/-- The action of `Q.Gal` on the root order, transported from the splitting
field. -/
@[instance_reducible]
noncomputable instance instActionRootOrder :
    MulSemiringAction (ratOf q).Gal (rootOrder x) where
  smul σ a := ⟨σ • ((a : rootOrder x) : splField q), rootOrder_smul_mem x σ a⟩
  one_smul a := Subtype.ext (one_smul (ratOf q).Gal ((a : rootOrder x) : splField q))
  mul_smul g h a := Subtype.ext (mul_smul g h ((a : rootOrder x) : splField q))
  smul_zero σ := Subtype.ext (smul_zero σ)
  smul_add σ _a _b := Subtype.ext (smul_add σ _ _)
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ _a _b := Subtype.ext (MulSemiringAction.smul_mul σ _ _)

end ActionInst

/-- The `ℚ → K` algebra map is injective (`K` is a field). -/
private theorem algebraMap_rat_injective :
    Function.Injective (algebraMap ℚ (splField q)) := by
  intro a b hab
  by_contra hne
  have hd : (a - b : ℚ) ≠ 0 := sub_ne_zero_of_ne hne
  have h3 : algebraMap ℚ (splField q) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have h2 : algebraMap ℚ (splField q) (a - b)
      * algebraMap ℚ (splField q) (a - b)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd, map_one]
  rw [h3, zero_mul] at h2
  exact zero_ne_one h2

section WithAction

variable (x : Fin n ≃ (ratOf q).rootSet (splField q))

private theorem coe_smul_action (σ : (ratOf q).Gal) (a : rootOrder x) :
    ((σ • a : rootOrder x) : splField q) = σ • ((a : rootOrder x) : splField q) := rfl

private theorem coe_smul_int (z : ℤ) (a : rootOrder x) :
    ((z • a : rootOrder x) : splField q) = z • ((a : rootOrder x) : splField q) := rfl

/-- The action commutes with the `ℤ`-scalars. -/
theorem instSMulCommClassRootOrder :
    SMulCommClass (ratOf q).Gal ℤ (rootOrder x) := by
  refine ⟨fun σ (z : ℤ) a => Subtype.ext ?_⟩
  have hfix : σ • algebraMap ℤ (splField q) z = algebraMap ℤ (splField q) z := by
    rw [algebraMap_int_apply, smul_eq_coe]
    exact AlgEquiv.commutes _ _
  rw [coe_smul_action x σ (z • a), coe_smul_int x z,
    show σ • (z • ((a : rootOrder x) : splField q)) =
      z • (σ • ((a : rootOrder x) : splField q)) from by
      rw [Algebra.smul_def, MulSemiringAction.smul_mul, hfix, ← Algebra.smul_def],
    ← coe_smul_action x σ a, ← coe_smul_int x z]

/-- The root order is invariant: every fixed point is an integer. -/
theorem isInvariant_rootOrder (hq : q.Monic) (hsep : (ratOf q).Separable) :
    Algebra.IsInvariant ℤ (rootOrder x) (ratOf q).Gal := by
  have hG := isGalois_splField hsep
  have hbot : IntermediateField.fixedField (⊤ : Subgroup (ratOf q).Gal) = ⊥ :=
    ((IsGalois.tfae (F := ℚ) (E := splField q)).out 1 2).mp hG
  refine ⟨fun b hb => ?_⟩
  have hbK : ∀ g : (ratOf q).Gal,
      g • ((b : rootOrder x) : splField q) = ((b : rootOrder x) : splField q) := by
    intro g
    rw [← coe_smul_action x g b]
    exact congrArg Subtype.val (hb g)
  have hfix : ((b : rootOrder x) : splField q)
      ∈ IntermediateField.fixedField (⊤ : Subgroup (ratOf q).Gal) := by
    intro σ
    exact hbK σ.val
  rw [hbot, IntermediateField.mem_bot] at hfix
  obtain ⟨k, hk⟩ := hfix
  have hint : IsIntegral ℤ k :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ (splField q))
      algebraMap_rat_injective (x := k)).mp
      (show IsIntegral ℤ ((IsScalarTower.toAlgHom ℤ ℚ (splField q)) k) by
        change IsIntegral ℤ (algebraMap ℚ (splField q) k)
        rw [hk]
        exact rootOrder_isIntegral hq x b)
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨z, ?_⟩
  have h1 : ((algebraMap ℤ (rootOrder x) z : rootOrder x) : splField q)
      = ((b : rootOrder x) : splField q) := by
    rw [Subalgebra.coe_algebraMap, algebraMap_int_apply,
      show ((z : ℤ) : ℚ) = algebraMap ℤ ℚ z from rfl, hz, hk]
  exact Subtype.val_injective h1

end WithAction

/-! ### A maximal ideal of the root order over `ℓ` -/

section MaxIdeal

variable (x : Fin n ≃ (ratOf q).rootSet (splField q)) {ℓ : ℕ} [Fact ℓ.Prime]

/-- The ideal `ℓ · O` of the root order is proper: `1 / ℓ` is not integral. -/
theorem span_ell_ne_top (hq : q.Monic) :
    Ideal.span {(ℓ : rootOrder x)} ≠ (⊤ : Ideal (rootOrder x)) := by
  intro htop
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((Ideal.eq_top_iff_one _).mp htop)
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  have hK : ((c : rootOrder x) : splField q) * algebraMap ℚ (splField q) (ℓ : ℚ) = 1 := by
    have h1 := congrArg (algebraMap (rootOrder x) (splField q)) hc
    rw [map_mul, map_natCast, map_one] at h1
    rw [map_natCast]
    exact h1
  have hcinv : algebraMap ℚ (splField q) (ℓ : ℚ)⁻¹ = ((c : rootOrder x) : splField q) := by
    rw [map_inv₀]
    exact (eq_inv_of_mul_eq_one_left hK).symm
  have hint : IsIntegral ℤ (ℓ : ℚ)⁻¹ :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ (splField q))
      algebraMap_rat_injective).mp
      (show IsIntegral ℤ (algebraMap ℚ (splField q) (ℓ : ℚ)⁻¹) by
        rw [hcinv]
        exact rootOrder_isIntegral hq x c)
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hcon : z * (ℓ : ℤ) = 1 := by
    have hrw : (z : ℚ) * (ℓ : ℚ) = 1 := by
      rw [show (z : ℚ) = algebraMap ℤ ℚ z from rfl, hz, inv_mul_cancel₀ hℓ0]
    exact_mod_cast hrw
  have hdvd : (ℓ : ℤ) ∣ ((1 : ℕ) : ℤ) := ⟨z, by rw [mul_comm, hcon]; rfl⟩
  exact (Fact.out : ℓ.Prime).not_dvd_one (Int.natCast_dvd_natCast.mp hdvd)

/-- The quotient by a proper ideal containing `ℓ` has characteristic `ℓ`. -/
theorem charP_quotient (𝔪 : Ideal (rootOrder x)) (hne : 𝔪 ≠ ⊤)
    (hℓ : (ℓ : rootOrder x) ∈ 𝔪) : CharP (rootOrder x ⧸ 𝔪) ℓ := by
  have : Nontrivial (rootOrder x ⧸ 𝔪) := Ideal.Quotient.nontrivial_iff.mpr hne
  refine (CharP.charP_iff_prime_eq_zero (Fact.out : ℓ.Prime)).mpr ?_
  rw [← map_natCast (Ideal.Quotient.mk 𝔪)]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hℓ

/-- An ideal over `ℓ` contracts to `(ℓ)` in `ℤ`. -/
theorem comap_eq_span_ell (𝔪 : Ideal (rootOrder x)) (hne : 𝔪 ≠ ⊤)
    (hℓ : (ℓ : rootOrder x) ∈ 𝔪) :
    Ideal.comap (algebraMap ℤ (rootOrder x)) 𝔪 = Ideal.span {(ℓ : ℤ)} := by
  have := charP_quotient x 𝔪 hne hℓ
  ext a
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    show Ideal.Quotient.mk 𝔪 (algebraMap ℤ (rootOrder x) a) = ((a : ℤ) : rootOrder x ⧸ 𝔪) by
      simp,
    CharP.intCast_eq_zero_iff _ ℓ]

/-- The Frobenius exponent is exactly `ℓ`. -/
theorem natCard_comap_eq_ell (𝔪 : Ideal (rootOrder x)) (hne : 𝔪 ≠ ⊤)
    (hℓ : (ℓ : rootOrder x) ∈ 𝔪) :
    Nat.card (ℤ ⧸ Ideal.comap (algebraMap ℤ (rootOrder x)) 𝔪) = ℓ := by
  rw [comap_eq_span_ell x 𝔪 hne hℓ,
    Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv, Nat.card_zmod]

/-- The residue ring over `ℓ` is finite: it is a finite `ℤ`-module killed by `ℓ`. -/
theorem finite_quotient (hq : q.Monic) (𝔪 : Ideal (rootOrder x)) (hne : 𝔪 ≠ ⊤)
    (hℓ : (ℓ : rootOrder x) ∈ 𝔪) : Finite (rootOrder x ⧸ 𝔪) := by
  have := charP_quotient x 𝔪 hne hℓ
  have : Module.Finite ℤ (rootOrder x) := rootOrder_finite hq x
  have : Module.Finite ℤ (rootOrder x ⧸ 𝔪) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ 𝔪).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ 𝔪)
  let _ : Algebra (ZMod ℓ) (rootOrder x ⧸ 𝔪) := ZMod.algebra (rootOrder x ⧸ 𝔪) ℓ
  have : Module.Finite (ZMod ℓ) (rootOrder x ⧸ 𝔪) :=
    Module.Finite.of_restrictScalars_finite ℤ (ZMod ℓ) (rootOrder x ⧸ 𝔪)
  exact Module.finite_of_finite (ZMod ℓ)

end MaxIdeal

/-! ### The roots inside the root order -/

section Roots

variable (x : Fin n ≃ (ratOf q).rootSet (splField q))

/-- A root in the splitting field, as an element of the root order. -/
noncomputable def rootO (z : (ratOf q).rootSet (splField q)) : rootOrder x :=
  ⟨z, by
    have h := rootK_mem x (x.symm z)
    simpa [rootK] using h⟩

/-- The Galois action on the roots is the action on the root order. -/
theorem smul_rootO (σ : (ratOf q).Gal) (z : (ratOf q).rootSet (splField q)) :
    σ • rootO x z = rootO x (σ • z) := rfl

/-- `q` splits over the root order, with the expected roots. -/
theorem map_eq_prod_rootO (hq : q.Monic) (hsep : (ratOf q).Separable) :
    q.map (algebraMap ℤ (rootOrder x)) = ∏ z, (X - C (rootO x z)) := by
  classical
  refine Polynomial.map_injective (algebraMap (rootOrder x) (splField q))
    Subtype.val_injective ?_
  have hQ : (ratOf q).map (algebraMap ℚ (splField q))
      = q.map (algebraMap ℤ (splField q)) := by
    rw [map_map, algebraMap_int_eq]
  have hm : ((ratOf q).map (algebraMap ℚ (splField q))).Monic := (hq.map _).map _
  have hsplit := (SplittingField.splits (ratOf q))
  have hnd : ((ratOf q).aroots (splField q)).Nodup := nodup_roots hsep.map
  rw [map_map, ← IsScalarTower.algebraMap_eq, ← hQ, hsplit.eq_prod_roots_of_monic hm,
    Polynomial.map_prod]
  simp only [Polynomial.map_sub, map_X, map_C]
  refine Eq.trans ?_ (Finset.prod_subtype (p := fun a => a ∈ (ratOf q).rootSet (splField q))
    ((ratOf q).aroots (splField q)).toFinset (fun a => by rw [rootSet_def]; simp)
    (fun a => (X - C a : (splField q)[X])))
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]

end Roots

/-! ### Dedekind's theorem in cycle-type form -/

section Main

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ Ideal.Quotient.field

/-- **Dedekind's theorem, cycle-type form.**  If the reduction of a monic `q` with
separable rational image factors mod `ℓ` as `∏_{r ∈ rs} (X - r) * gb`, with `gb`
monic irreducible of degree `≥ 2`, then the Galois group of `q` contains an
element of cycle type `{deg gb}`.  Mathlib's
`IsArithFrobAt.exists_of_isInvariant` provides the Frobenius `σ` at a maximal
ideal `𝔪` of the root order over `ℓ`; separability of the reduction makes the
reduced roots distinct, and `cycleType_of_frobenius_roots` reads off the cycle
type of the action of `σ` on the complex roots. -/
theorem frob_cycleType_of_factorization {q : ℤ[X]} (hq : q.Monic)
    (hsep : (ratOf q).Separable) {ℓ : ℕ} [Fact ℓ.Prime] (rs : Finset (ZMod ℓ))
    {gb : (ZMod ℓ)[X]} (hgm : gb.Monic) (hirr : Irreducible gb)
    (h2 : 2 ≤ gb.natDegree)
    (hfact : q.map (Int.castRingHom (ZMod ℓ)) = (∏ r ∈ rs, (X - C r)) * gb) :
    MaedaGalois.FrobHasCycleType (ratOf q) {gb.natDegree} := by
  classical
  let x := rootsE (q := q) rfl
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ (span_ell_ne_top (ℓ := ℓ) x hq)
  have hℓ : (ℓ : rootOrder x) ∈ 𝔪 := hle (Ideal.mem_span_singleton_self _)
  have hne𝔪 : 𝔪 ≠ ⊤ := h𝔪.ne_top
  have := h𝔪
  have : Finite (rootOrder x ⧸ 𝔪) := finite_quotient x hq 𝔪 hne𝔪 hℓ
  have : CharP (rootOrder x ⧸ 𝔪) ℓ := charP_quotient x 𝔪 hne𝔪 hℓ
  let _ : Algebra (ZMod ℓ) (rootOrder x ⧸ 𝔪) := ZMod.algebra (rootOrder x ⧸ 𝔪) ℓ
  have : SMulCommClass (ratOf q).Gal ℤ (rootOrder x) := instSMulCommClassRootOrder x
  have : Algebra.IsInvariant ℤ (rootOrder x) (ratOf q).Gal := isInvariant_rootOrder x hq hsep
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (ratOf q).Gal 𝔪
  have hfrob : ∀ a : rootOrder x, Ideal.Quotient.mk 𝔪 (σ • a) = Ideal.Quotient.mk 𝔪 a ^ ℓ := by
    intro a
    have h := AlgHom.IsArithFrobAt.mk_apply hσ a
    rw [show Nat.card (ℤ ⧸ Ideal.under ℤ 𝔪) = ℓ from natCard_comap_eq_ell x 𝔪 hne𝔪 hℓ] at h
    exact h
  -- the reduced roots, indexed by the complex roots
  let e := Gal.rootsEquivRootsAux (ratOf q) ℂ
  let y : (ratOf q).rootSet ℂ → rootOrder x ⧸ 𝔪 :=
    fun w => Ideal.Quotient.mk 𝔪 (rootO x (e.symm w))
  have hcomp : (Ideal.Quotient.mk 𝔪).comp (algebraMap ℤ (rootOrder x))
      = (algebraMap (ZMod ℓ) (rootOrder x ⧸ 𝔪)).comp (Int.castRingHom (ZMod ℓ)) :=
    RingHom.ext_int _ _
  have hprod : ∏ w, (X - C (y w)) =
      ((∏ r ∈ rs, (X - C r)) * gb).map (algebraMap (ZMod ℓ) (rootOrder x ⧸ 𝔪)) := by
    rw [← hfact, map_map, ← hcomp, ← map_map, map_eq_prod_rootO x hq hsep, Polynomial.map_prod,
      ← Equiv.prod_comp e.symm]
    simp [y]
  have hyinj : Function.Injective y := by
    refine separable_prod_X_sub_C_iff.mp ?_
    rw [hprod]
    exact (separable_prod_mul hirr h2).map
  refine ⟨σ, cycleType_of_frobenius_roots rs hgm hirr h2 y hyinj _ (fun w => ?_) hprod⟩
  have hsm : e.symm (Gal.galActionHom (ratOf q) ℂ σ w) = σ • e.symm w := by
    change e.symm (e (σ • e.symm w)) = _
    rw [Equiv.symm_apply_apply]
  simp only [y]
  rw [hsm, ← smul_rootO, hfrob]

end Main

end Dedekind

end FrobeniusCert
