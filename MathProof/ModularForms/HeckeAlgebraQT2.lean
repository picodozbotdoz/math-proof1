import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The Hecke-algebra upgrade, algebra half: commuting endomorphisms are polynomials

If `T₂ : V →ₗ[K] V` has irreducible characteristic polynomial, then `T₂` generates its
commutant: every endomorphism of `V` commuting with `T₂` is of the form
`Polynomial.aeval T₂ q` for some `q : K[X]`.  This is the pure-algebra core of the
Maeda-statement upgrade (`research/maeda-scaling-study.md` §4 step 5 and
`blueprint/hecke-algebra-upgrade/BLUEPRINT.md`): applied with `K = ℚ`, `V` a level-one
cusp form space and `Tₙ` a Hecke operator, it upgrades every "charpoly of `T₂` is
irreducible" theorem to the Hecke-algebra statement `Tₙ ∈ ℚ[T₂]` once `Tₙ T₂ = T₂ Tₙ`
is known.

Proof outline (no weight-specific data enters anywhere):
* step 1: `minpoly K T₂ = charpoly T₂` — `minpoly ∣ charpoly`, both are monic, and
  irreducibility leaves no other associate (as validated in
  `blueprint/lean/MinpolyCharpolySketch.lean`);
* steps 2–4: every `v₀ ≠ 0` is *cyclic* for `T₂`.  Indeed, if `r` with `deg r < deg f`
  (where `f = charpoly T₂`) satisfies `aeval T₂ r v₀ = 0`, then `r` is coprime to the
  irreducible `f` (else `f ∣ r`, contradicting the degree bound), and a Bézout identity
  `a * f + b * r = 1` evaluated at `T₂` gives `v₀ = 0`.  So evaluation at `T₂` restricts
  to an injection on the `n`-dimensional space of polynomials of degree `< n = deg f`
  (`Polynomial.degreeLT`), and `finrank`-counting (`LinearMap.finrank_range_of_inj`,
  `Submodule.eq_top_of_finrank_eq`) shows every `w ∈ V` is `aeval T₂ p v₀`;
* steps 5–6: `Tₙ` commutes with every `aeval T₂ p` (induction on `p`), so with
  `Tₙ v₀ = aeval T₂ q₀ v₀` the endomorphism `Tₙ - aeval T₂ q₀` kills `v₀` and all its
  polynomial images, hence vanishes: `Tₙ = aeval T₂ q₀`.

The Hecke-side input `Tₙ T₂ = T₂ Tₙ` is *not* proved here (planned follow-up module
`MathProof/ModularForms/HeckeCommute.lean`); this module is generic over the
endomorphisms, so it re-uses verbatim for every weight and every level-one space.
-/

open Polynomial

namespace HeckeAlgebra

/-! ### Steps 2–4: evaluation of polynomials at a vector, and the Bézout step

Auxiliary material: it needs neither `FiniteDimensional K V` nor more than a field
structure, so it lives in its own section with a minimal variable context (no unused
section variables are pulled into the private declarations). -/

section Aux

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Evaluation of polynomials at `T`, applied to a fixed vector `v`:
`p ↦ (Polynomial.aeval T p) v`. -/
private noncomputable def evalAeval (T : V →ₗ[K] V) (v : V) : K[X] →ₗ[K] V where
  toFun p := Polynomial.aeval T p v
  map_add' p q := by rw [map_add, LinearMap.add_apply]
  map_smul' c p := by rw [RingHom.id_apply, map_smul, LinearMap.smul_apply]

@[simp]
private lemma evalAeval_apply (T : V →ₗ[K] V) (v : V) (p : K[X]) :
    evalAeval T v p = Polynomial.aeval T p v := rfl

/-- **Bézout step.**  Let `f` be monic and irreducible with `aeval T f = 0`.  If a
polynomial `r` of degree below `deg f` annihilates a nonzero vector `v` under
`p ↦ (aeval T p) v`, then `r = 0`: otherwise `f ∣ r` contradicts the degree bound, so
`r` is coprime to `f`, and a Bézout identity `a * f + b * r = 1` evaluates to `v = 0`
at `T`. -/
private theorem eq_zero_of_degree_lt_of_ker_eval (T : V →ₗ[K] V) (f : K[X]) (hmonic : f.Monic)
    (hf : Irreducible f) (hfe : Polynomial.aeval T f = 0) {v : V} (hv : v ≠ 0) (r : K[X])
    (hr : Polynomial.aeval T r v = 0) (hdeg : r.degree < f.degree) : r = 0 := by
  rcases eq_or_ne r 0 with h0 | h0
  · exact h0
  rcases hf.isCoprime_or_dvd r with hcopr | hdvd
  · obtain ⟨a, b, hab⟩ := hcopr
    exfalso
    apply hv
    have hfev : (Polynomial.aeval T f) v = 0 := by rw [hfe, LinearMap.zero_apply]
    have h1 : Polynomial.aeval T (a * f + b * r) v = v := by
      rw [hab, map_one, one_apply_eq_self]
    have h2 : Polynomial.aeval T (a * f + b * r) v = 0 := by
      simp only [map_add, LinearMap.add_apply, map_mul, mul_apply_eq_comp]
      rw [hfev, map_zero, hr, map_zero, add_zero]
    exact h1.symm.trans h2
  · refine absurd hdeg (not_lt.2 ?_)
    rw [degree_eq_natDegree hmonic.ne_zero, degree_eq_natDegree h0]
    exact WithBot.coe_le_coe.mpr (hmonic.natDegree_le_of_dvd h0 hdvd)

end Aux

/-! ### Steps 1 and 5–6: the upgrade theorem -/

section Main

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- If the characteristic polynomial of `T` is irreducible (and `V ≠ 0`), it already is
the minimal polynomial. -/
theorem minpoly_eq_charpoly_of_irreducible_charpoly {T : V →ₗ[K] V} [Nontrivial V]
    (h : Irreducible (LinearMap.charpoly T)) : minpoly K T = LinearMap.charpoly T := by
  have hmon : (minpoly K T).Monic := minpoly.monic (LinearMap.isIntegral T)
  obtain ⟨F, hF⟩ := LinearMap.minpoly_dvd_charpoly T
  rcases h.isUnit_or_isUnit hF with hu | hu
  · exfalso
    rcases Polynomial.isUnit_iff.mp hu with ⟨c, -, hC⟩
    have hc1 : c = 1 := by
      have : (C c).Monic := by rw [hC]; exact hmon
      simpa [Monic, Polynomial.leadingCoeff_C] using this
    have hz : Polynomial.aeval T (minpoly K T) = 0 := minpoly.aeval K T
    rw [← hC, hc1] at hz
    simp at hz
  · obtain ⟨u, rfl⟩ : ∃ u : K[X]ˣ, (u : K[X]) = F := ⟨hu.unit, hu.unit_spec⟩
    exact eq_of_monic_of_associated hmon (LinearMap.charpoly_monic T) ⟨u, hF.symm⟩

/-- **The upgrade theorem (algebra half).**  If `T₂` has irreducible characteristic
polynomial (and `V ≠ 0`), then every endomorphism commuting with `T₂` is a polynomial
in `T₂`. -/
theorem exists_aeval_of_commute_of_irreducible_charpoly {T2 : V →ₗ[K] V} [Nontrivial V]
    (hchar : Irreducible (LinearMap.charpoly T2)) (Tn : V →ₗ[K] V) (hcomm : Commute Tn T2) :
    ∃ q : K[X], Tn = Polynomial.aeval T2 q := by
  have hmp : minpoly K T2 = LinearMap.charpoly T2 :=
    minpoly_eq_charpoly_of_irreducible_charpoly hchar
  have hfmonic : (LinearMap.charpoly T2).Monic := LinearMap.charpoly_monic T2
  have hf0 : LinearMap.charpoly T2 ≠ 0 := hfmonic.ne_zero
  have hfdeg : (LinearMap.charpoly T2).degree =
      ((LinearMap.charpoly T2).natDegree : WithBot ℕ) := degree_eq_natDegree hf0
  have hfe : Polynomial.aeval T2 (LinearMap.charpoly T2) = 0 := by
    rw [← hmp]
    exact minpoly.aeval K T2
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  -- Steps 2–4: `v₀` is a cyclic vector for `T₂`.
  have key : ∀ r : K[X], Polynomial.aeval T2 r v₀ = 0 →
      r.degree < (LinearMap.charpoly T2).degree → r = 0 :=
    eq_zero_of_degree_lt_of_ker_eval T2 (LinearMap.charpoly T2) hfmonic hchar hfe hv₀
  have hinj : Function.Injective ⇑
      ((evalAeval T2 v₀).comp
        (Polynomial.degreeLT K (LinearMap.charpoly T2).natDegree).subtype) := by
    intro x y hxy
    have hxy' : evalAeval T2 v₀ x.val = evalAeval T2 v₀ y.val := by
      simpa only [LinearMap.comp_apply, Submodule.coe_subtype] using hxy
    have hmem : x.val - y.val ∈ Polynomial.degreeLT K (LinearMap.charpoly T2).natDegree :=
      Submodule.sub_mem (Polynomial.degreeLT K (LinearMap.charpoly T2).natDegree) x.2 y.2
    have hr : Polynomial.aeval T2 (x.val - y.val) v₀ = 0 := by
      rw [← evalAeval_apply, map_sub, hxy', sub_self]
    refine Subtype.ext (sub_eq_zero.mp (key (x.val - y.val) hr ?_))
    rw [hfdeg]
    exact Polynomial.mem_degreeLT.mp hmem
  have hdimLT : Module.finrank K
      (Polynomial.degreeLT K (LinearMap.charpoly T2).natDegree) =
      (LinearMap.charpoly T2).natDegree := by
    rw [LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv K (LinearMap.charpoly T2).natDegree)]
    exact Module.finrank_fin_fun
  have hfrange : Module.finrank K (LinearMap.range
      ((evalAeval T2 v₀).comp
        (Polynomial.degreeLT K (LinearMap.charpoly T2).natDegree).subtype)) =
      (LinearMap.charpoly T2).natDegree := by
    rw [LinearMap.finrank_range_of_inj hinj, hdimLT]
  have hsub : LinearMap.range ((evalAeval T2 v₀).comp
      (Polynomial.degreeLT K (LinearMap.charpoly T2).natDegree).subtype) ≤
      LinearMap.range (evalAeval T2 v₀) := by
    intro w hw
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hw
    refine LinearMap.mem_range.mpr ⟨x.val, ?_⟩
    simpa only [LinearMap.comp_apply, Submodule.coe_subtype] using hx
  have hle : (LinearMap.charpoly T2).natDegree ≤
      Module.finrank K (LinearMap.range (evalAeval T2 v₀)) := by
    rw [← hfrange]
    exact Submodule.finrank_mono hsub
  have htop : LinearMap.range (evalAeval T2 v₀) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
    rw [← LinearMap.charpoly_natDegree T2]
    exact hle
  -- Step 5: `Tₙ` commutes with every polynomial in `T₂`.
  have hpow : ∀ n : ℕ, Commute Tn (T2 ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact Commute.one_right Tn
    | succ n ih => rw [pow_succ]; exact Commute.mul_right ih hcomm
  have hTnaev : ∀ p : K[X], Commute Tn (Polynomial.aeval T2 p) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q ihp ihq =>
      rw [map_add]
      exact Commute.add_right ihp ihq
    | monomial n a =>
      rw [aeval_monomial]
      exact (Algebra.commute_algebraMap_right a Tn).mul_right (hpow n)
  have hswap : ∀ p : K[X], Tn (Polynomial.aeval T2 p v₀) = Polynomial.aeval T2 p (Tn v₀) := by
    intro p
    rw [← mul_apply_eq_comp, (hTnaev p).eq, mul_apply_eq_comp]
  -- Step 6: finish.
  have hmulcomm : ∀ p q : K[X], Polynomial.aeval T2 p * Polynomial.aeval T2 q
      = Polynomial.aeval T2 q * Polynomial.aeval T2 p := by
    intro p q
    rw [← map_mul, mul_comm p q, map_mul]
  have hmemq : Tn v₀ ∈ LinearMap.range (evalAeval T2 v₀) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨q₀, hq₀⟩ := LinearMap.mem_range.mp hmemq
  have hq₀' : Polynomial.aeval T2 q₀ v₀ = Tn v₀ := by
    rw [← evalAeval_apply]
    exact hq₀
  refine ⟨q₀, LinearMap.ext fun w => ?_⟩
  obtain ⟨p, hp⟩ : ∃ p : K[X], Polynomial.aeval T2 p v₀ = w := by
    have hw : w ∈ LinearMap.range (evalAeval T2 v₀) := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨p, hp⟩ := LinearMap.mem_range.mp hw
    exact ⟨p, by rw [← evalAeval_apply]; exact hp⟩
  have h2 : Polynomial.aeval T2 p (Tn v₀) =
      Polynomial.aeval T2 p (Polynomial.aeval T2 q₀ v₀) := by
    rw [hq₀']
  have h3 : Polynomial.aeval T2 p (Polynomial.aeval T2 q₀ v₀)
      = Polynomial.aeval T2 q₀ (Polynomial.aeval T2 p v₀) := by
    rw [← mul_apply_eq_comp, hmulcomm p q₀, mul_apply_eq_comp]
  calc Tn w = Tn (Polynomial.aeval T2 p v₀) := by rw [hp]
    _ = Polynomial.aeval T2 p (Tn v₀) := hswap p
    _ = Polynomial.aeval T2 p (Polynomial.aeval T2 q₀ v₀) := h2
    _ = Polynomial.aeval T2 q₀ (Polynomial.aeval T2 p v₀) := h3
    _ = Polynomial.aeval T2 q₀ w := by rw [hp]

end Main

end HeckeAlgebra
