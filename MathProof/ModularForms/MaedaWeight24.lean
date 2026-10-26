import MathProof.ModularForms.LehmerWeight16
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Maeda's conjecture in weight 24

**Maeda's conjecture** (1997) predicts that for every level-one weight `k` the
Hecke algebra of `S_k(SL(2, ℤ))` is as large as possible: the characteristic
polynomial of `T₂` acting on `S_k` is irreducible over `ℚ` (with full symmetric
Galois group).  It is verified numerically to large weights but open in
general.  Weight 24 is the first weight with `dim S_k ≥ 2`, and the first
nontrivial case.

This file proves the weight-24 case formally, from the Hecke operator itself:

* `f1 = Δ E₄³ = q + 696 q² + ⋯`, `f2 = Δ² = q² − 48 q³ + ⋯` form a basis of
  `S₂₄` (`basis24`); every cusp form is determined by its first two
  coefficients (`eq_comb`, via the Sturm bound `24 / 12 = 2`);
* `T₂ f1 = 696 f1 + 20736000 f2`, `T₂ f2 = f1 + 384 f2` (`heckeT2_f1`,
  `heckeT2_f2`), from the coefficient formula of `HeckeLevelOne`;
* **`charpoly_heckeT2`** — the characteristic polynomial of the linear map
  `T₂ : S₂₄ → S₂₄` is `X² − 1080 X − 20468736` (discriminant
  `576 · 144169`, so the Hecke field is `ℚ(√144169)`);
* **`maeda_weight24`** — it is irreducible over `ℚ` (it has no root mod 23,
  then Gauss's lemma).  For degree 2 the Galois group is automatically `S₂`.
-/

open UpperHalfPlane ModularForm CuspForm EisensteinSeries HeckeLevelOne Polynomial
open scoped MatrixGroups

namespace MaedaWeight24

/-- The q-expansion of `E₄`. -/
local notation "q₄" => qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)

/-- The q-expansion of `Δ`. -/
local notation "qΔ" => qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)

/-- The weight-24 cusp form space. -/
local notation "S24" => CuspForm 𝒮ℒ ((24 : ℕ) : ℤ)

/-! ### The forms and their first coefficients -/

/-- `Δ E₄³`. -/
noncomputable def f1 : S24 := ofMulDiscriminant (ModularForm.mcast (by norm_num) (E₄.pow 3))

/-- `Δ²`. -/
noncomputable def f2 : S24 :=
  ofMulDiscriminant (ModularForm.mcast (by norm_num) (CuspForm.discriminant : ModularForm 𝒮ℒ 12))

lemma qExpansion_f1 : qExpansion 1 f1 = qΔ * q₄ ^ 3 := by
  rw [← ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  exact ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) (E₄.pow 3)

lemma qExpansion_f2 : qExpansion 1 f2 = qΔ * qΔ :=
  ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) (CuspForm.discriminant : CuspForm 𝒮ℒ 12)

lemma dΔ (m : ℕ) : (qΔ).coeff m = ((LehmerWeight16.dlt m : ℤ) : ℂ) := LehmerWeight16.delta_coeff m

lemma d0 : PowerSeries.constantCoeff (qΔ) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, dΔ]; simp [LehmerWeight16.dlt]
lemma d1 : (qΔ).coeff 1 = 1 := by rw [dΔ]; simp [LehmerWeight16.dlt, Ramanujan.tau_one]
lemma d2 : (qΔ).coeff 2 = -24 := by rw [dΔ]; simp [LehmerWeight16.dlt, Ramanujan.tau_two]
lemma d3 : (qΔ).coeff 3 = 252 := by rw [dΔ]; simp [LehmerWeight16.dlt, Ramanujan.tau_three]
lemma d4 : (qΔ).coeff 4 = -1472 := by rw [dΔ]; simp [LehmerWeight16.dlt, Ramanujan.tau_four]

lemma e0 : PowerSeries.constantCoeff (q₄) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, LehmerWeight16.e4_coeff]
  simp [LehmerWeight16.e4]
lemma e1 : (q₄).coeff 1 = 240 := by rw [LehmerWeight16.e4_coeff]; simp [LehmerWeight16.e4]
lemma e2 : (q₄).coeff 2 = 2160 := by
  rw [LehmerWeight16.e4_coeff]; norm_num [LehmerWeight16.e4, LehmerWeight16.sigma3_two]
lemma e3 : (q₄).coeff 3 = 6720 := by
  rw [LehmerWeight16.e4_coeff]
  norm_num [LehmerWeight16.e4, show ArithmeticFunction.sigma 3 3 = 28 by decide]

lemma cube_coeff :
    PowerSeries.constantCoeff (q₄ ^ 3) = 1 ∧ (q₄ ^ 3).coeff 1 = 720 ∧ (q₄ ^ 3).coeff 2 = 179280
      ∧ (q₄ ^ 3).coeff 3 = 16954560 := by
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, e0, e1, e2, e3]
  norm_num

lemma f1_coeff :
    PowerSeries.constantCoeff (qExpansion 1 f1) = 0 ∧ (qExpansion 1 f1).coeff 1 = 1
      ∧ (qExpansion 1 f1).coeff 2 = 696 ∧ (qExpansion 1 f1).coeff 4 = 12831808 := by
  obtain ⟨c0, c1, c2, c3⟩ := cube_coeff
  rw [qExpansion_f1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_mul, d0, zero_mul]
  all_goals
    simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, d0, d1, d2, d3, d4, e0, c1, c2, c3]
    try norm_num

lemma f2_coeff :
    PowerSeries.constantCoeff (qExpansion 1 f2) = 0 ∧ (qExpansion 1 f2).coeff 1 = 0
      ∧ (qExpansion 1 f2).coeff 2 = 1 ∧ (qExpansion 1 f2).coeff 4 = 1080 := by
  rw [qExpansion_f2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_mul, d0, zero_mul]
  all_goals
    simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, d0, d1, d2, d3, d4]
    try norm_num

/-! ### Every cusp form of weight 24 is fixed by two coefficients -/

/-- The q-expansion as an additive map on `S₂₄` (through the inclusion into
modular forms). -/
noncomputable def qL : S24 →+ PowerSeries ℂ :=
  (ModularForm.qExpansionAddHom one_pos one_mem_strictPeriods_SL ((24 : ℕ) : ℤ)).comp
    (toModularFormₗ : S24 →ₗ[ℂ] ModularForm 𝒮ℒ ((24 : ℕ) : ℤ)).toAddMonoidHom

lemma qL_apply (f : S24) : qL f = qExpansion 1 f := rfl

lemma qe_add (f g : S24) : qExpansion 1 ⇑(f + g) = qExpansion 1 f + qExpansion 1 g := by
  rw [← qL_apply, map_add, qL_apply, qL_apply]

lemma qe_sub (f g : S24) : qExpansion 1 ⇑(f - g) = qExpansion 1 f - qExpansion 1 g := by
  rw [← qL_apply, map_sub, qL_apply, qL_apply]

lemma qe_smul (c : ℂ) (f : S24) : qExpansion 1 ⇑(c • f) = c • qExpansion 1 f :=
  ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c f

/-- **Coordinates in `S₂₄`**: `g = g₁ • f1 + (g₂ − 696 g₁) • f2`. -/
theorem eq_comb (g : S24) :
    g = (qExpansion 1 g).coeff 1 • f1
      + ((qExpansion 1 g).coeff 2 - 696 * (qExpansion 1 g).coeff 1) • f2 := by
  set x := (qExpansion 1 g).coeff 1
  set y := (qExpansion 1 g).coeff 2 - 696 * x
  obtain ⟨a0, a1, a2, -⟩ := f1_coeff
  obtain ⟨b0, b1, b2, -⟩ := f2_coeff
  have hg0 : PowerSeries.constantCoeff (qExpansion 1 g) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact CuspFormClass.qExpansion_coeff_zero g one_pos one_mem_strictPeriods_SL
  set G : S24 := g - x • f1 - y • f2 with hG
  have hq : qExpansion 1 G = qExpansion 1 g - x • qExpansion 1 f1 - y • qExpansion 1 f2 := by
    rw [hG, qe_sub, qe_sub, qe_smul, qe_smul]
  have h3 : (3 : ℕ∞) ≤ (qExpansion 1 (toModularFormₗ G)).order :=
    PowerSeries.nat_le_order _ 3 fun i hi => by
      change (qExpansion 1 G).coeff i = 0
      rw [hq]
      simp only [map_sub, PowerSeries.coeff_smul, smul_eq_mul]
      interval_cases i
      · simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0, a0, b0]; ring
      · rw [a1, b1]; ring
      · rw [a2, b2]; simp only [y, x]; ring
  have hH : ((24 / 12 : ℕ) : ℕ∞) < (qExpansion 1 (toModularFormₗ G)).order :=
    lt_of_lt_of_le (by norm_num) h3
  have hG0 : G = 0 := by
    apply toModularFormₗ_injective
    rw [map_zero]
    exact ModularForm.sturm_bound_levelOne_nat hH
  rw [hG, sub_sub, sub_eq_zero] at hG0
  exact hG0

/-! ### The Hecke operator `T₂` -/

/-- `T₂` as a `ℂ`-linear endomorphism of `S₂₄`. -/
noncomputable def heckeT2 : S24 →ₗ[ℂ] S24 where
  toFun := heckeTP Nat.prime_two
  map_add' f g := by
    ext z
    simp only [heckeTP_apply, FunLike.coe_add, heckeTPFun_add, Pi.add_apply]
  map_smul' c f := by
    ext z
    simp only [heckeTP_apply, FunLike.coe_smul, heckeTPFun_smul, Pi.smul_apply,
      RingHom.id_apply]

lemma two_pow : ((2 : ℕ) : ℂ) ^ (((24 : ℕ) : ℤ) - 1) = 8388608 := by
  rw [show ((24 : ℕ) : ℤ) - 1 = ((23 : ℕ) : ℤ) by norm_num, zpow_natCast]
  norm_num

lemma heckeT2_coeff (f : S24) :
    (qExpansion 1 (heckeT2 f)).coeff 1 = (qExpansion 1 f).coeff 2
      ∧ (qExpansion 1 (heckeT2 f)).coeff 2
        = (qExpansion 1 f).coeff 4 + 8388608 * (qExpansion 1 f).coeff 1 := by
  refine ⟨?_, ?_⟩
  · rw [show heckeT2 f = heckeTP Nat.prime_two f from rfl, heckeTP_qExpansion_coeff]
    simp
  · rw [show heckeT2 f = heckeTP Nat.prime_two f from rfl, heckeTP_qExpansion_coeff, two_pow]
    simp

/-- `T₂ (Δ E₄³) = 696 Δ E₄³ + 20736000 Δ²`. -/
theorem heckeT2_f1 : heckeT2 f1 = (696 : ℂ) • f1 + (20736000 : ℂ) • f2 := by
  obtain ⟨-, a1, a2, a4⟩ := f1_coeff
  obtain ⟨h1, h2⟩ := heckeT2_coeff f1
  rw [eq_comb (heckeT2 f1), h1, h2, a1, a2, a4]
  norm_num

/-- `T₂ (Δ²) = Δ E₄³ + 384 Δ²`. -/
theorem heckeT2_f2 : heckeT2 f2 = (1 : ℂ) • f1 + (384 : ℂ) • f2 := by
  obtain ⟨-, b1, b2, b4⟩ := f2_coeff
  obtain ⟨h1, h2⟩ := heckeT2_coeff f2
  rw [eq_comb (heckeT2 f2), h1, h2, b1, b2, b4]
  norm_num

/-! ### The basis and the characteristic polynomial -/

lemma linearIndependent_f : LinearIndependent ℂ ![f1, f2] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  obtain ⟨-, a1, a2, -⟩ := f1_coeff
  obtain ⟨-, b1, b2, -⟩ := f2_coeff
  have h : qExpansion 1 ⇑(s • f1 + t • f2) = 0 := by rw [hst]; simp [qExpansion_zero]
  rw [qe_add, qe_smul, qe_smul] at h
  have hc1 := congrArg (fun P : PowerSeries ℂ => P.coeff 1) h
  have hc2 := congrArg (fun P : PowerSeries ℂ => P.coeff 2) h
  simp only [map_add, PowerSeries.coeff_smul, smul_eq_mul, a1, a2, b1, b2, map_zero] at hc1 hc2
  constructor
  · linear_combination hc1
  · linear_combination hc2 - 696 * hc1

lemma span_f : ⊤ ≤ Submodule.span ℂ (Set.range ![f1, f2]) := by
  intro g _
  rw [eq_comb g]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

/-- The basis `(Δ E₄³, Δ²)` of `S₂₄`. -/
noncomputable def basis24 : Module.Basis (Fin 2) ℂ S24 := Module.Basis.mk linearIndependent_f span_f

noncomputable instance : Module.Free ℂ S24 := Module.Free.of_basis basis24
noncomputable instance : Module.Finite ℂ S24 := Module.Finite.of_basis basis24

lemma basis24_zero : basis24 0 = f1 := by simp [basis24]
lemma basis24_one : basis24 1 = f2 := by simp [basis24]

lemma repr_f1 : basis24.repr f1 = Finsupp.single 0 1 := by
  rw [← basis24_zero]; exact basis24.repr_self 0

lemma repr_f2 : basis24.repr f2 = Finsupp.single 1 1 := by
  rw [← basis24_one]; exact basis24.repr_self 1

/-- The matrix of `T₂` in the basis `(Δ E₄³, Δ²)`. -/
theorem toMatrix_heckeT2 :
    LinearMap.toMatrix basis24 basis24 heckeT2 = !![696, 1; 20736000, 384] := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j
  · change (basis24.repr (heckeT2 (basis24 0))) 0 = 696
    rw [basis24_zero, heckeT2_f1, map_add, map_smul, map_smul, repr_f1, repr_f2]; simp
  · change (basis24.repr (heckeT2 (basis24 1))) 0 = 1
    rw [basis24_one, heckeT2_f2, map_add, map_smul, map_smul, repr_f1, repr_f2]; simp
  · change (basis24.repr (heckeT2 (basis24 0))) 1 = 20736000
    rw [basis24_zero, heckeT2_f1, map_add, map_smul, map_smul, repr_f1, repr_f2]; simp
  · change (basis24.repr (heckeT2 (basis24 1))) 1 = 384
    rw [basis24_one, heckeT2_f2, map_add, map_smul, map_smul, repr_f1, repr_f2]; simp

/-- The integer polynomial `X² − 1080 X − 20468736`. -/
noncomputable def P24 : ℤ[X] := X ^ 2 - C 1080 * X - C 20468736

/-- **The characteristic polynomial of `T₂` on `S₂₄`** is `X² − 1080 X − 20468736`. -/
theorem charpoly_heckeT2 : heckeT2.charpoly = P24.map (Int.castRingHom ℂ) := by
  rw [← LinearMap.charpoly_toMatrix heckeT2 basis24, toMatrix_heckeT2, Matrix.charpoly_fin_two]
  simp [P24, Matrix.trace_fin_two, Matrix.det_fin_two, map_ofNat]
  ring

lemma P24_monic : P24.Monic := by unfold P24; monicity!

/-- `X² − 1080 X − 20468736` has no root modulo 23 (its discriminant
`576 · 144169` is a non-residue mod 23). -/
lemma no_root_mod23 : ∀ x : ZMod 23, x ^ 2 - 1080 * x - 20468736 ≠ 0 := by decide

/-- **Maeda's conjecture in weight 24**: the characteristic polynomial of `T₂`
on `S₂₄(SL(2, ℤ))` is irreducible over `ℚ`. -/
theorem maeda_weight24 : Irreducible (P24.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have hdeg : P24.natDegree = 2 := by unfold P24; compute_degree!
  have hmod : Irreducible (P24.map (Int.castRingHom (ZMod 23))) := by
    refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [P24_monic.natDegree_map, hdeg]; decide
    · intro x hx
      apply no_root_mod23 x
      simpa [P24, IsRoot] using hx
  have hZ : Irreducible P24 :=
    Polynomial.Monic.irreducible_of_irreducible_map (φ := Int.castRingHom (ZMod 23)) P24
      P24_monic hmod
  have hQ := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)
    P24_monic).mp hZ
  simpa [algebraMap_int_eq] using hQ

end MaedaWeight24
