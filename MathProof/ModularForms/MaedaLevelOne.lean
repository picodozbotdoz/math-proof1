import MathProof.ModularForms.LehmerWeight16
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Weight-generic machinery for Maeda's conjecture in level one

`MathProof/ModularForms/MaedaWeight24.lean` proves the first case by hand.
This file packages every step so that a further weight only costs numbers:

* **Forms with computable coefficients.** `prodForm k i a b` is the cusp form
  `Δ^(i+1) E₄^a E₆^b` of weight `k = 12 (i+1) + 4a + 6b`; its q-coefficients
  are the integers `seqP i a b n`, built from `conv` (Cauchy product) of
  `σ`-sequences and a lookup table of `τ` (`dC`, equal to the verified values
  `tau_one … tau_twenty_one`).  Concrete coefficients are then evaluated by
  `decide +kernel`.
* **Hecke operators as linear maps.** `heckeTPₗ`, and the coefficient formula
  of `T₂` at natural weight (`heckeT2_coeff`).
* **From coefficients to characteristic polynomials.** `charpoly_dim2` /
  `charpoly_dim3`: if `S_k` has dimension 2 (resp. 3) and `f₁, f₂(, f₃)` are
  triangular (`f_i = q^i + O(q^(i+1))`), the matrix of any endomorphism `T` in
  this basis is read off the first q-coefficients of `T f_j`.  No Sturm bound is
  used (the basis comes from the dimension formula), so weights `k ≡ 2 (mod 12)`
  are covered too.
* **Irreducibility.** `irreducible_of_noRoot`: a monic integer polynomial of
  degree 2 or 3 without roots modulo a prime `ℓ` is irreducible over `ℚ`.
-/

open UpperHalfPlane ModularForm CuspForm EisensteinSeries HeckeLevelOne Polynomial
open scoped MatrixGroups

namespace MaedaLevelOne

/-- The q-expansion of `Δ`. -/
local notation "qΔ" => qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)

/-! ### Integer coefficient sequences -/

/-- Cauchy product of integer sequences. -/
def conv (p q : ℕ → ℤ) (n : ℕ) : ℤ := ∑ x ∈ Finset.antidiagonal n, p x.1 * q x.2

/-- The sequence of the power series `1`. -/
def one (n : ℕ) : ℤ := if n = 0 then 1 else 0

/-- Cauchy powers of an integer sequence. -/
def cpow (p : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0 => one
  | m + 1 => conv (cpow p m) p

lemma coeff_mul_conv {P Q : PowerSeries ℂ} {p q : ℕ → ℤ} (hP : ∀ n, P.coeff n = p n)
    (hQ : ∀ n, Q.coeff n = q n) (n : ℕ) : (P * Q).coeff n = conv p q n := by
  rw [PowerSeries.coeff_mul, conv, Int.cast_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [hP, hQ, Int.cast_mul]

lemma coeff_pow_cpow {P : PowerSeries ℂ} {p : ℕ → ℤ} (hP : ∀ n, P.coeff n = p n) (m : ℕ) :
    ∀ n, (P ^ m).coeff n = cpow p m n := by
  induction m with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    simp only [cpow, one]
    split_ifs <;> simp
  | succ m ih =>
    intro n
    rw [pow_succ]
    exact coeff_mul_conv ih hP n

/-- The integer q-coefficients of `E₄`. -/
def e4 (m : ℕ) : ℤ := if m = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 m : ℤ)

/-- The integer q-coefficients of `E₆`. -/
def e6 (m : ℕ) : ℤ := if m = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 m : ℤ)

/-- `τ 0, …, τ 21` (with the convention `0` at index `0`), as kernel-verified
in `MathProof/Tau/Basic.lean`. -/
def tauTable : List ℤ :=
  [0, 1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944,
    -577738, 401856, 1217160, 987136, -6905934, 2727432, 10661420, -7109760, -4219488]

/-- The q-coefficients of `Δ`, read from `tauTable` up to index 21 (so that
concrete coefficients are kernel-computable). -/
noncomputable def dC (m : ℕ) : ℤ := if m ≤ 21 then tauTable.getD m 0 else Ramanujan.tau m

lemma delta_coeff_dC (m : ℕ) : (qΔ).coeff m = dC m := by
  rw [LehmerWeight16.delta_coeff]
  congr 1
  unfold LehmerWeight16.dlt dC
  by_cases hm : m ≤ 21
  · simp only [hm, ↓reduceIte]
    interval_cases m <;>
      simp [tauTable, Ramanujan.tau_one, Ramanujan.tau_two, Ramanujan.tau_three,
        Ramanujan.tau_four, Ramanujan.tau_five, Ramanujan.tau_six, Ramanujan.tau_seven,
        Ramanujan.tau_eight, Ramanujan.tau_nine, Ramanujan.tau_ten, Ramanujan.tau_eleven,
        Ramanujan.tau_twelve, Ramanujan.tau_thirteen, Ramanujan.tau_fourteen,
        Ramanujan.tau_fifteen, Ramanujan.tau_sixteen, Ramanujan.tau_seventeen,
        Ramanujan.tau_eighteen, Ramanujan.tau_nineteen, Ramanujan.tau_twenty,
        Ramanujan.tau_twenty_one]
  · simp only [hm, ↓reduceIte, show m ≠ 0 by omega]

lemma e4_coeff (m : ℕ) : (qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)).coeff m = e4 m :=
  RamanujanCongruence.E4_coeff_eq m

lemma e6_coeff (m : ℕ) : (qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6)).coeff m = e6 m :=
  RamanujanCongruence.E6_coeff_eq m

/-- The coefficients of `Δ^(i+1) E₄^a E₆^b`. -/
noncomputable def seqP (i a b : ℕ) : ℕ → ℤ :=
  conv dC (conv (cpow dC i) (conv (cpow e4 a) (cpow e6 b)))

/-! ### The product forms -/

/-- The cusp form `Δ^(i+1) E₄^a E₆^b` of weight `k`. -/
noncomputable def prodForm (k : ℤ) (i a b : ℕ)
    (hk : (i : ℤ) * 12 + ((a : ℤ) * 4 + (b : ℤ) * 6) = k - 12) : CuspForm 𝒮ℒ k :=
  ofMulDiscriminant (ModularForm.mcast hk
    (((CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow i).mul ((E₄.pow a).mul (E₆.pow b))))

lemma qExpansion_prodForm (k : ℤ) (i a b : ℕ)
    (hk : (i : ℤ) * 12 + ((a : ℤ) * 4 + (b : ℤ) * 6) = k - 12) :
    qExpansion 1 (prodForm k i a b hk) = qΔ * ((qΔ) ^ i
      * ((qExpansion 1 (E₄ : ModularForm 𝒮ℒ 4)) ^ a
        * (qExpansion 1 (E₆ : ModularForm 𝒮ℒ 6)) ^ b)) := by
  have h := ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12)
    (((CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow i).mul ((E₄.pow a).mul (E₆.pow b)))
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL] at h
  exact h

theorem prodForm_coeff (k : ℤ) (i a b : ℕ)
    (hk : (i : ℤ) * 12 + ((a : ℤ) * 4 + (b : ℤ) * 6) = k - 12) (n : ℕ) :
    (qExpansion 1 (prodForm k i a b hk)).coeff n = seqP i a b n := by
  rw [qExpansion_prodForm]
  exact coeff_mul_conv delta_coeff_dC
    (coeff_mul_conv (coeff_pow_cpow delta_coeff_dC i)
      (coeff_mul_conv (coeff_pow_cpow e4_coeff a) (coeff_pow_cpow e6_coeff b))) n

/-! ### Linear structure -/

instance (k : ℤ) : FiniteDimensional ℂ (CuspForm 𝒮ℒ k) :=
  LinearEquiv.finiteDimensional CuspForm.discriminantEquiv.symm

/-- The q-expansion as an additive map on `S_k`. -/
noncomputable def qL (k : ℤ) : CuspForm 𝒮ℒ k →+ PowerSeries ℂ :=
  (ModularForm.qExpansionAddHom one_pos one_mem_strictPeriods_SL k).comp
    (toModularFormₗ : CuspForm 𝒮ℒ k →ₗ[ℂ] ModularForm 𝒮ℒ k).toAddMonoidHom

lemma qL_apply {k : ℤ} (f : CuspForm 𝒮ℒ k) : qL k f = qExpansion 1 f := rfl

lemma qe_smul {k : ℤ} (c : ℂ) (f : CuspForm 𝒮ℒ k) :
    qExpansion 1 ⇑(c • f) = c • qExpansion 1 f :=
  ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c f

/-- The coefficients of a finite linear combination. -/
lemma coeff_sum {k : ℤ} {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → CuspForm 𝒮ℒ k)
    (n : ℕ) : (qExpansion 1 ⇑(∑ i ∈ s, c i • f i)).coeff n
      = ∑ i ∈ s, c i * (qExpansion 1 (f i)).coeff n := by
  rw [← qL_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [qL_apply, qe_smul, PowerSeries.coeff_smul, smul_eq_mul]

/-- `T_p` as a `ℂ`-linear endomorphism of `S_k`. -/
noncomputable def heckeTPₗ (k : ℤ) {p : ℕ} (hp : p.Prime) :
    CuspForm 𝒮ℒ k →ₗ[ℂ] CuspForm 𝒮ℒ k where
  toFun := heckeTP hp
  map_add' f g := by
    ext z
    simp only [heckeTP_apply, FunLike.coe_add, heckeTPFun_add, Pi.add_apply]
  map_smul' c f := by
    ext z
    simp only [heckeTP_apply, FunLike.coe_smul, heckeTPFun_smul, Pi.smul_apply,
      RingHom.id_apply]

/-- The q-coefficients of `T₂ f` in natural weight `K ≥ 1`. -/
lemma heckeT2_coeff {K : ℕ} (hK : 1 ≤ K) (f : CuspForm 𝒮ℒ (K : ℤ)) (m : ℕ) :
    (qExpansion 1 (heckeTPₗ (K : ℤ) Nat.prime_two f)).coeff m
      = (qExpansion 1 f).coeff (2 * m)
        + (2 : ℂ) ^ (K - 1) * (if 2 ∣ m then (qExpansion 1 f).coeff (m / 2) else 0) := by
  rw [show heckeTPₗ (K : ℤ) Nat.prime_two f = heckeTP Nat.prime_two f from rfl,
    heckeTP_qExpansion_coeff, show ((K : ℤ) - 1) = ((K - 1 : ℕ) : ℤ) by omega, zpow_natCast]
  push_cast
  rfl

/-! ### From coefficients to the characteristic polynomial -/

/-- **Dimension 2.**  If `dim S_k = 2` and `f₁ = q + a q² + ⋯`, `f₂ = q² + ⋯`,
then the matrix of `T` in the basis `(f₁, f₂)` is read off the first two
coefficients `x_j, y_j` of `T f_j`. -/
theorem charpoly_dim2 {k : ℤ} (hdim : Module.finrank ℂ (CuspForm 𝒮ℒ k) = 2)
    (f₁ f₂ : CuspForm 𝒮ℒ k) {a : ℂ} (h11 : (qExpansion 1 f₁).coeff 1 = 1)
    (h12 : (qExpansion 1 f₁).coeff 2 = a) (h21 : (qExpansion 1 f₂).coeff 1 = 0)
    (h22 : (qExpansion 1 f₂).coeff 2 = 1) (T : CuspForm 𝒮ℒ k →ₗ[ℂ] CuspForm 𝒮ℒ k)
    {x₁ y₁ x₂ y₂ : ℂ} (hx₁ : (qExpansion 1 (T f₁)).coeff 1 = x₁)
    (hy₁ : (qExpansion 1 (T f₁)).coeff 2 = y₁) (hx₂ : (qExpansion 1 (T f₂)).coeff 1 = x₂)
    (hy₂ : (qExpansion 1 (T f₂)).coeff 2 = y₂) :
    T.charpoly = Matrix.charpoly !![x₁, x₂; y₁ - a * x₁, y₂ - a * x₂] := by
  have hli : LinearIndependent ℂ ![f₁, f₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := coeff_sum Finset.univ ![s, t] ![f₁, f₂] 1
    have h2 := coeff_sum Finset.univ ![s, t] ![f₁, f₂] 2
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hst,
      FunLike.coe_zero, qExpansion_zero, map_zero, h11, h12, h21, h22] at h1 h2
    constructor
    · linear_combination -h1
    · linear_combination -h2 + a * h1
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb : ∀ g, b.repr g 0 = (qExpansion 1 g).coeff 1
      ∧ b.repr g 1 = (qExpansion 1 g).coeff 2 - a * (qExpansion 1 g).coeff 1 := by
    intro g
    have hs := b.sum_repr g
    have h1 := coeff_sum Finset.univ (b.repr g) b 1
    have h2 := coeff_sum Finset.univ (b.repr g) b 2
    rw [hs] at h1 h2
    simp only [Fin.sum_univ_two, b, coe_basisOfLinearIndependentOfCardEqFinrank,
      Matrix.cons_val_zero, Matrix.cons_val_one, h11, h12, h21, h22] at h1 h2
    constructor
    · linear_combination -h1
    · linear_combination -h2 + a * h1
  rw [← LinearMap.charpoly_toMatrix T b]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply]
  have hb0 : b 0 = f₁ := by simp [b]
  have hb1 : b 1 = f₂ := by simp [b]
  fin_cases i <;> fin_cases j
  · change b.repr (T (b 0)) 0 = _; rw [(hb _).1, hb0, hx₁]; rfl
  · change b.repr (T (b 1)) 0 = _; rw [(hb _).1, hb1, hx₂]; rfl
  · change b.repr (T (b 0)) 1 = _; rw [(hb _).2, hb0, hx₁, hy₁]; rfl
  · change b.repr (T (b 1)) 1 = _; rw [(hb _).2, hb1, hx₂, hy₂]; rfl

/-- **Dimension 3.**  If `dim S_k = 3` and `f₁ = q + a q² + c q³ + ⋯`,
`f₂ = q² + d q³ + ⋯`, `f₃ = q³ + ⋯`, the matrix of `T` in `(f₁, f₂, f₃)` is read off
the first three coefficients `x_j, y_j, z_j` of `T f_j` by back-substitution. -/
theorem charpoly_dim3 {k : ℤ} (hdim : Module.finrank ℂ (CuspForm 𝒮ℒ k) = 3)
    (f₁ f₂ f₃ : CuspForm 𝒮ℒ k) {a c d : ℂ}
    (h11 : (qExpansion 1 f₁).coeff 1 = 1) (h12 : (qExpansion 1 f₁).coeff 2 = a)
    (h13 : (qExpansion 1 f₁).coeff 3 = c)
    (h21 : (qExpansion 1 f₂).coeff 1 = 0) (h22 : (qExpansion 1 f₂).coeff 2 = 1)
    (h23 : (qExpansion 1 f₂).coeff 3 = d)
    (h31 : (qExpansion 1 f₃).coeff 1 = 0) (h32 : (qExpansion 1 f₃).coeff 2 = 0)
    (h33 : (qExpansion 1 f₃).coeff 3 = 1)
    (T : CuspForm 𝒮ℒ k →ₗ[ℂ] CuspForm 𝒮ℒ k) {x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ : ℂ}
    (hx₁ : (qExpansion 1 (T f₁)).coeff 1 = x₁) (hy₁ : (qExpansion 1 (T f₁)).coeff 2 = y₁)
    (hz₁ : (qExpansion 1 (T f₁)).coeff 3 = z₁)
    (hx₂ : (qExpansion 1 (T f₂)).coeff 1 = x₂) (hy₂ : (qExpansion 1 (T f₂)).coeff 2 = y₂)
    (hz₂ : (qExpansion 1 (T f₂)).coeff 3 = z₂)
    (hx₃ : (qExpansion 1 (T f₃)).coeff 1 = x₃) (hy₃ : (qExpansion 1 (T f₃)).coeff 2 = y₃)
    (hz₃ : (qExpansion 1 (T f₃)).coeff 3 = z₃) :
    T.charpoly = Matrix.charpoly !![x₁, x₂, x₃;
      y₁ - a * x₁, y₂ - a * x₂, y₃ - a * x₃;
      z₁ - c * x₁ - d * (y₁ - a * x₁), z₂ - c * x₂ - d * (y₂ - a * x₂),
        z₃ - c * x₃ - d * (y₃ - a * x₃)] := by
  have hli : LinearIndependent ℂ ![f₁, f₂, f₃] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := coeff_sum Finset.univ g ![f₁, f₂, f₃] 1
    have h2 := coeff_sum Finset.univ g ![f₁, f₂, f₃] 2
    have h3 := coeff_sum Finset.univ g ![f₁, f₂, f₃] 3
    simp only [hg, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, FunLike.coe_zero,
      qExpansion_zero, map_zero, h11, h12, h13, h21, h22, h23, h31, h32, h33] at h1 h2 h3
    have g0 : g 0 = 0 := by linear_combination -h1
    have g1 : g 1 = 0 := by linear_combination -h2 + a * h1
    have g2 : g 2 = 0 := by linear_combination -h3 + c * h1 + d * (h2 - a * h1)
    fin_cases i
    · exact g0
    · exact g1
    · exact g2
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb : ∀ g, b.repr g 0 = (qExpansion 1 g).coeff 1
      ∧ b.repr g 1 = (qExpansion 1 g).coeff 2 - a * (qExpansion 1 g).coeff 1
      ∧ b.repr g 2 = (qExpansion 1 g).coeff 3 - c * (qExpansion 1 g).coeff 1
          - d * ((qExpansion 1 g).coeff 2 - a * (qExpansion 1 g).coeff 1) := by
    intro g
    have hs := b.sum_repr g
    have h1 := coeff_sum Finset.univ (b.repr g) b 1
    have h2 := coeff_sum Finset.univ (b.repr g) b 2
    have h3 := coeff_sum Finset.univ (b.repr g) b 3
    rw [hs] at h1 h2 h3
    simp only [Fin.sum_univ_three, b, coe_basisOfLinearIndependentOfCardEqFinrank,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, h11, h12, h13, h21, h22, h23, h31, h32, h33] at h1 h2 h3
    refine ⟨?_, ?_, ?_⟩
    · linear_combination -h1
    · linear_combination -h2 + a * h1
    · linear_combination -h3 + c * h1 + d * (h2 - a * h1)
  rw [← LinearMap.charpoly_toMatrix T b]
  congr 1
  have hb0 : b 0 = f₁ := by simp [b]
  have hb1 : b 1 = f₂ := by simp [b]
  have hb2 : b 2 = f₃ := by simp [b]
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j
  · change b.repr (T (b 0)) 0 = _; rw [(hb _).1, hb0, hx₁]; rfl
  · change b.repr (T (b 1)) 0 = _; rw [(hb _).1, hb1, hx₂]; rfl
  · change b.repr (T (b 2)) 0 = _; rw [(hb _).1, hb2, hx₃]; rfl
  · change b.repr (T (b 0)) 1 = _; rw [(hb _).2.1, hb0, hx₁, hy₁]; rfl
  · change b.repr (T (b 1)) 1 = _; rw [(hb _).2.1, hb1, hx₂, hy₂]; rfl
  · change b.repr (T (b 2)) 1 = _; rw [(hb _).2.1, hb2, hx₃, hy₃]; rfl
  · change b.repr (T (b 0)) 2 = _; rw [(hb _).2.2, hb0, hx₁, hy₁, hz₁]; rfl
  · change b.repr (T (b 1)) 2 = _; rw [(hb _).2.2, hb1, hx₂, hy₂, hz₂]; rfl
  · change b.repr (T (b 2)) 2 = _; rw [(hb _).2.2, hb2, hx₃, hy₃, hz₃]; rfl

/-- The characteristic polynomial of a `3 × 3` matrix. -/
lemma charpoly_fin_three {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    M.charpoly = X ^ 3 - C (M 0 0 + M 1 1 + M 2 2) * X ^ 2
      + C (M 0 0 * M 1 1 + M 0 0 * M 2 2 + M 1 1 * M 2 2 - M 0 1 * M 1 0 - M 0 2 * M 2 0
        - M 1 2 * M 2 1) * X - C M.det := by
  rw [Matrix.charpoly, Matrix.det_fin_three, Matrix.det_fin_three]
  simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply]
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, map_sub, map_add, map_mul]
  ring

/-! ### Irreducibility -/

/-- A monic integer polynomial of degree 2 or 3 with no root modulo a prime `ℓ`
is irreducible over `ℚ`. -/
theorem irreducible_of_noRoot {P : ℤ[X]} (hmon : P.Monic) (hdeg : P.natDegree ∈ Finset.Icc 2 3)
    (ℓ : ℕ) [Fact ℓ.Prime] (hroot : ∀ x : ZMod ℓ, (P.map (Int.castRingHom (ZMod ℓ))).eval x ≠ 0) :
    Irreducible (P.map (Int.castRingHom ℚ)) := by
  have hmod : Irreducible (P.map (Int.castRingHom (ZMod ℓ))) := by
    refine irreducible_of_degree_le_three_of_not_isRoot ?_ fun x hx => hroot x hx
    rw [hmon.natDegree_map]
    simp only [Finset.mem_Icc] at hdeg ⊢
    omega
  have hZ : Irreducible P :=
    Polynomial.Monic.irreducible_of_irreducible_map (φ := Int.castRingHom (ZMod ℓ)) P hmon hmod
  have hQ := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ) hmon).mp hZ
  simpa [algebraMap_int_eq] using hQ

end MaedaLevelOne
