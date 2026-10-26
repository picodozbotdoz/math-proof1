import MathProof.Tau.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The q-expansion of the modular discriminant is `∑ τ(n) q^n`

This file proves the **analytic-to-algebraic bridge** for the Ramanujan tau
function: the `n`-th coefficient of the `q`-expansion of Mathlib's modular
discriminant `Δ` (an analytic object, defined through the Dedekind η function)
equals the algebraically-defined `Ramanujan.tau n` (the coefficient of `X^n` in
the polynomial product `(∏_{m ≤ n} (1 - X ^ m)) ^ 24 ∈ ℤ[X]`):

    (qExpansion 1 Δ).coeff n = if n = 0 then 0 else τ(n)

The proof combines Mathlib's product formula for `Δ` on the unit disc
(`discriminant_cuspFunction_eqOn`), the truncation-stability of the finite
products (`Ramanujan.etaPow24_stable`), a coefficient bound
`|coeff of (η_M) ^ 24| ≤ 2 ^ (24 * M)` making `∑ τ(n) z^n` converge
geometrically on a small disc, and uniqueness of power-series representations.
-/

set_option maxRecDepth 10000

namespace Ramanujan

open Polynomial UpperHalfPlane ModularForm Filter Topology

open scoped MatrixGroups

/-! ### A coefficient 1-norm on `ℤ[X]` -/

/-- The sum of absolute values of all coefficients of `p : ℤ[X]`. -/
def pnorm (p : ℤ[X]) : ℕ := ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i).natAbs

theorem coeff_natAbs_le_pnorm {p : ℤ[X]} {i : ℕ} : (p.coeff i).natAbs ≤ pnorm p := by
  by_cases h : i < p.natDegree + 1
  · exact Finset.single_le_sum (f := fun j ↦ (p.coeff j).natAbs)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr h)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

theorem pnorm_eq_of_le {p : ℤ[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    pnorm p = ∑ i ∈ Finset.range (n + 1), (p.coeff i).natAbs := by
  unfold pnorm
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_
  intro x _ hx
  have hx' : p.natDegree < x := by
    by_contra h
    exact hx (Finset.mem_range.mpr (by omega))
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hx']
  simp

/-- Any initial segment of the coefficient-absolute-value sequence of `p` is
bounded by `pnorm p`. -/
theorem sum_range_natAbs_le_pnorm (p : ℤ[X]) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (p.coeff j).natAbs ≤ pnorm p := by
  rcases Nat.lt_or_ge n p.natDegree with h | h
  · exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
  · rw [pnorm_eq_of_le h]

/-- The key combinatorial estimate: summing `a j * b k` over all antidiagonals
below `N` (i.e. over the triangle `{(j, k) : j + k < N}`) is bounded by the
product of the section sums, because the triangle is a subset of the square. -/
theorem sum_antidiagonal_range_le {N : ℕ} (a b : ℕ → ℕ) :
    ∑ i ∈ Finset.range N, ∑ x ∈ Finset.antidiagonal i, a x.1 * b x.2
      ≤ (∑ j ∈ Finset.range N, a j) * (∑ k ∈ Finset.range N, b k) := by
  classical
  have hflat : ∑ i ∈ Finset.range N, ∑ x ∈ Finset.antidiagonal i, a x.1 * b x.2
      = ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p ↦ p.1 + p.2 < N),
          a p.1 * b p.2 := by
    rw [Finset.sum_sigma' (t := fun i ↦ Finset.antidiagonal i)
      (f := fun _ x ↦ a x.1 * b x.2)]
    refine Finset.sum_nbij' (i := fun p ↦ p.2) (j := fun q ↦ ⟨q.1 + q.2, q⟩) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_sigma] at hp
      have h2 : p.2.1 + p.2.2 = p.1 := Finset.mem_antidiagonal.mp hp.2
      have h1 : p.1 < N := Finset.mem_range.mp hp.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, by omega⟩
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
      obtain ⟨⟨h1, h2⟩, h3⟩ := hq
      rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal]
      exact ⟨by omega, rfl⟩
    · intro p hp
      simp only [Finset.mem_sigma] at hp
      have h2 : p.2.1 + p.2.2 = p.1 := Finset.mem_antidiagonal.mp hp.2
      exact Sigma.ext h2 (heq_of_eq rfl)
    · intro q hq
      rfl
    · intro p hp
      rfl
  rw [hflat]
  calc ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p ↦ p.1 + p.2 < N), a p.1 * b p.2
      ≤ ∑ p ∈ Finset.range N ×ˢ Finset.range N, a p.1 * b p.2 :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = (∑ j ∈ Finset.range N, a j) * (∑ k ∈ Finset.range N, b k) := by
        rw [Finset.sum_product]
        change ∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N, a x * b y
          = (∑ j ∈ Finset.range N, a j) * (∑ k ∈ Finset.range N, b k)
        exact (Finset.sum_mul_sum (s := Finset.range N) (t := Finset.range N)
          (f := a) (g := b)).symm

/-- The 1-norm is submultiplicative. -/
theorem pnorm_mul_le (p q : ℤ[X]) : pnorm (p * q) ≤ pnorm p * pnorm q := by
  have key : ∀ i : ℕ, ((p * q).coeff i).natAbs
      ≤ ∑ x ∈ Finset.antidiagonal i, (p.coeff x.1).natAbs * (q.coeff x.2).natAbs := by
    intro i
    calc ((p * q).coeff i).natAbs
        = (∑ x ∈ Finset.antidiagonal i, p.coeff x.1 * q.coeff x.2).natAbs := by
            rw [Polynomial.coeff_mul]
      _ ≤ ∑ x ∈ Finset.antidiagonal i, (p.coeff x.1 * q.coeff x.2).natAbs :=
          Int.natAbs_sum_le _ _
      _ = ∑ x ∈ Finset.antidiagonal i, (p.coeff x.1).natAbs * (q.coeff x.2).natAbs :=
          Finset.sum_congr rfl fun x _ ↦ Int.natAbs_mul _ _
  have h2 := sum_antidiagonal_range_le (N := (p * q).natDegree + 1)
    (fun j ↦ (p.coeff j).natAbs) (fun k ↦ (q.coeff k).natAbs)
  calc pnorm (p * q)
      = ∑ i ∈ Finset.range ((p * q).natDegree + 1), ((p * q).coeff i).natAbs := rfl
    _ ≤ ∑ i ∈ Finset.range ((p * q).natDegree + 1),
          ∑ x ∈ Finset.antidiagonal i, (p.coeff x.1).natAbs * (q.coeff x.2).natAbs :=
        Finset.sum_le_sum (fun i _ ↦ key i)
    _ ≤ (∑ j ∈ Finset.range ((p * q).natDegree + 1), (p.coeff j).natAbs) *
        (∑ k ∈ Finset.range ((p * q).natDegree + 1), (q.coeff k).natAbs) := h2
    _ ≤ pnorm p * pnorm q :=
        Nat.mul_le_mul (sum_range_natAbs_le_pnorm _ _) (sum_range_natAbs_le_pnorm _ _)

theorem pnorm_one : pnorm (1 : ℤ[X]) = 1 := by
  simp [pnorm, Polynomial.natDegree_one, Polynomial.coeff_one]

theorem pnorm_pow_le {p : ℤ[X]} {n : ℕ} : pnorm (p ^ n) ≤ (pnorm p) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact pnorm_one.le
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (pnorm_mul_le _ _).trans (Nat.mul_le_mul ih le_rfl)

theorem pnorm_one_sub_X (m : ℕ) (hm : 1 ≤ m) : pnorm (1 - (X ^ m : ℤ[X])) = 2 := by
  have hm0 : m ≠ 0 := by omega
  have hdeg : (1 - (X ^ m : ℤ[X])).natDegree ≤ m := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    rw [Polynomial.natDegree_one, Polynomial.natDegree_X_pow]
    simp
  rw [pnorm_eq_of_le hdeg]
  have hc : ∀ i ∈ Finset.range (m + 1),
      ((1 - (X ^ m : ℤ[X])).coeff i).natAbs
        = (if i = 0 then 1 else 0) + (if i = m then 1 else 0) := by
    intro i _
    rw [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl hc]
  simp [Finset.sum_add_distrib]

set_option maxHeartbeats 2000000 in
-- reason: the succ-step proof chains `pnorm_mul_le` (a large `Finset.sum_le_sum`)
-- with `Nat.pow` arithmetic and trips the default 200000 budget
/-- The coefficients of the truncated η-powers are exponentially bounded. -/
theorem pnorm_etaPow24_le (M : ℕ) : pnorm ((etaPoly M) ^ 24) ≤ 2 ^ (24 * M) := by
  induction M with
  | zero =>
      simp only [etaPoly, Finset.range_zero, Finset.prod_empty, one_pow, Nat.mul_zero,
        Nat.pow_zero]
      exact pnorm_one.le
  | succ M ih =>
      have hrw : (etaPoly (M + 1)) ^ 24
          = ((etaPoly M) ^ 24) * ((1 - (X ^ (M + 1) : ℤ[X])) ^ 24) := by
        rw [etaPoly_succ, mul_pow]
      rw [hrw]
      have h2 : pnorm ((1 - (X ^ (M + 1) : ℤ[X])) ^ 24) ≤ 2 ^ 24 := by
        refine pnorm_pow_le.trans ?_
        rw [pnorm_one_sub_X (M + 1) (by omega)]
      have h3 : 2 ^ (24 * M) * 2 ^ 24 ≤ 2 ^ (24 * (M + 1)) := by
        have he : 24 * M + 24 = 24 * (M + 1) := by omega
        rw [← he, ← Nat.pow_add]
      exact (pnorm_mul_le _ _).trans ((Nat.mul_le_mul ih h2).trans h3)

theorem tauOf_natAbs_le (i : ℕ) : (tauOf i).natAbs ≤ 2 ^ (24 * (i + 1)) :=
  (coeff_natAbs_le_pnorm (p := (etaPoly (i + 1)) ^ 24) (i := i)).trans
    (pnorm_etaPow24_le _)

/-! ### Evaluating the truncated products -/

theorem etaPoly_aeval (M : ℕ) (z : ℂ) :
    (aeval z) (etaPoly M) = ∏ i ∈ Finset.range M, (1 - z ^ (i + 1)) := by
  simp only [etaPoly, map_prod]
  exact Finset.prod_congr rfl fun i _ ↦ by simp

/-- The truncated product `X * (η_M)^24`, whose coefficients agree with `τ`
in degrees `1, …, M` and whose evaluation at `z` is the `M`-th partial
product of the analytic product formula for `Δ`. -/
noncomputable def deltaPoly (M : ℕ) : ℤ[X] := X * (etaPoly M) ^ 24

theorem deltaPoly_aeval (M : ℕ) (z : ℂ) :
    (aeval z) (deltaPoly M) = z * ∏ i ∈ Finset.range M, (1 - z ^ (i + 1)) ^ 24 := by
  unfold deltaPoly
  rw [map_mul, aeval_X, map_pow, etaPoly_aeval, ← Finset.prod_pow]

theorem deltaPoly_coeff (M : ℕ) {m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ M) :
    (deltaPoly M).coeff m = tau m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h0 : (deltaPoly M).coeff (k + 1) = ((etaPoly M) ^ 24).coeff k :=
    Polynomial.coeff_X_mul _ k
  rw [h0, etaPow24_stable k M (by omega)]
  rfl

theorem etaPoly_natDegree_le (M : ℕ) : (etaPoly M).natDegree ≤ M * M := by
  change (∏ i ∈ Finset.range M, (1 - (X ^ (i + 1) : ℤ[X]))).natDegree ≤ M * M
  have h1 : ∀ i ∈ Finset.range M, (1 - (X ^ (i + 1) : ℤ[X])).natDegree ≤ M := by
    intro i hi
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    rw [Polynomial.natDegree_one, Polynomial.natDegree_X_pow]
    have hip : i + 1 ≤ M := by
      have := Finset.mem_range.mp hi
      omega
    simp [hip]
  have h2 : (∏ i ∈ Finset.range M, (1 - (X ^ (i + 1) : ℤ[X]))).natDegree
      ≤ ∑ i ∈ Finset.range M, (1 - (X ^ (i + 1) : ℤ[X])).natDegree :=
    Polynomial.natDegree_prod_le (s := Finset.range M)
      (f := fun i ↦ 1 - (X ^ (i + 1) : ℤ[X]))
  calc (∏ i ∈ Finset.range M, (1 - (X ^ (i + 1) : ℤ[X]))).natDegree
      ≤ ∑ _i ∈ Finset.range M, M := h2.trans (Finset.sum_le_sum h1)
    _ = M * M := by simp [Finset.sum_const, Finset.card_range]

theorem deltaPoly_natDegree_le (M : ℕ) :
    (deltaPoly M).natDegree ≤ 1 + 24 * (M * M) := by
  have h2 : ((etaPoly M) ^ 24).natDegree ≤ 24 * (M * M) :=
    Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (etaPoly_natDegree_le M))
  have h3 : (X * (etaPoly M) ^ 24 : ℤ[X]).natDegree
      ≤ (X : ℤ[X]).natDegree + ((etaPoly M) ^ 24).natDegree := natDegree_mul_le
  rw [Polynomial.natDegree_X] at h3
  have h4 : (deltaPoly M).natDegree = (X * (etaPoly M) ^ 24 : ℤ[X]).natDegree := rfl
  omega

/-! ### The analytic bridge -/

/-- The coefficient sequence of Δ as complex numbers: `δ 0 = 0`, `δ m = τ m`. -/
noncomputable def deltaCoeffsFun : ℕ → ℂ := fun m ↦ if m = 0 then 0 else ((tau m : ℤ) : ℂ)

theorem deltaCoeffsFun_zero : deltaCoeffsFun 0 = 0 := by
  simp [deltaCoeffsFun]

theorem deltaCoeffsFun_pos (m : ℕ) (hm : m ≠ 0) : deltaCoeffsFun m = ((tau m : ℤ) : ℂ) := by
  rw [deltaCoeffsFun]
  simp [hm]

/-- Exponential bound on the coefficients of `δ`. -/
theorem norm_deltaCoeffsFun_le (m : ℕ) : ‖deltaCoeffsFun m‖ ≤ 2 ^ (24 * m) := by
  rcases Nat.eq_zero_or_pos m with rfl | h0
  · rw [deltaCoeffsFun_zero]
    simp
  · rw [deltaCoeffsFun_pos m (by omega)]
    have h1 : (tau m).natAbs ≤ 2 ^ (24 * m) := by
      have hm' : m = (m - 1) + 1 := by omega
      rw [hm']
      have := tauOf_natAbs_le (m - 1)
      have hexp : 24 * ((m - 1) + 1) = 24 * (m - 1 + 1) := by rw [hm']
      rw [hexp]
      exact this
    have h2 : ‖((tau m : ℤ) : ℂ)‖ ≤ ((2 ^ (24 * m) : ℕ) : ℝ) := by
      have hz : |tau m| ≤ ((2 ^ (24 * m) : ℕ) : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast h1
      rw [Complex.norm_intCast]
      push_cast
      exact_mod_cast hz
    exact h2.trans_eq (Nat.cast_pow 2 (24 * m))

theorem summable_deltaCoeffsFun {z : ℂ} (hz : 2 ^ 24 * ‖z‖ < 1) :
    Summable fun m ↦ z ^ m * deltaCoeffsFun m := by
  have h0 : (0:ℝ) ≤ 2 ^ 24 * ‖z‖ := by positivity
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one h0 hz) ?_
  intro m
  calc ‖z ^ m * deltaCoeffsFun m‖ = ‖z ^ m‖ * ‖deltaCoeffsFun m‖ := norm_mul _ _
    _ = ‖z‖ ^ m * ‖deltaCoeffsFun m‖ := by rw [norm_pow]
    _ ≤ ‖z‖ ^ m * 2 ^ (24 * m) :=
        mul_le_mul_of_nonneg_left (norm_deltaCoeffsFun_le m)
          (pow_nonneg (norm_nonneg z) m)
    _ = (2 ^ 24 * ‖z‖) ^ m := by
        rw [mul_pow, ← pow_mul]
        ring

/-- Geometric partial sums are bounded by the full geometric sum. -/
private lemma sum_range_pow_le_tsum (K : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∑ k ∈ Finset.range K, ρ ^ k ≤ (1 - ρ)⁻¹ := by
  have hs : Summable fun k : ℕ ↦ ρ ^ k := summable_geometric_of_lt_one hρ hρ1
  have hmono : Monotone fun N ↦ ∑ k ∈ Finset.range N, ρ ^ k := fun a b hab ↦
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hab)
      (fun k _ _ ↦ pow_nonneg hρ k)
  calc ∑ k ∈ Finset.range K, ρ ^ k
      ≤ ∑' k : ℕ, ρ ^ k := hmono.ge_of_tendsto hs.hasSum.tendsto_sum_nat K
    _ = (1 - ρ)⁻¹ := tsum_geometric_of_lt_one hρ hρ1

/-- **The core estimate**: on a small disc, the `M`-th partial sum of `∑ τ(m) z^m`
is within `2 ^ (24 * M) * ‖z‖ ^ (M+1) / (1 - ‖z‖)` of the `M`-th partial product
of the analytic product formula for `Δ`. -/
theorem dist_poly_sum_le {z : ℂ} (hz1 : ‖z‖ < 1) (M : ℕ) :
    ‖(aeval z) (deltaPoly M)
      - ∑ m ∈ Finset.range (M + 1), z ^ m * deltaCoeffsFun m‖
      ≤ 2 ^ (24 * M) * (‖z‖ ^ (M + 1) / (1 - ‖z‖)) := by
  set ρ := ‖z‖ with hρdef
  have hρ : 0 ≤ ρ := norm_nonneg z
  set n := (M + 1) + (1 + 24 * (M * M)) with hn
  have hndeg : (deltaPoly M).natDegree < n := by
    have := deltaPoly_natDegree_le M
    omega
  -- expand the evaluation as a long finite sum and split it at M+1
  have heval : (aeval z) (deltaPoly M)
      = ∑ i ∈ Finset.range n, ((deltaPoly M).coeff i : ℂ) * z ^ i := by
    rw [Polynomial.aeval_eq_sum_range' hndeg z]
    exact Finset.sum_congr rfl fun i _ ↦ by simp
  -- split the degree range at `M + 1`: the low part carries the τ-values
  -- (degrees `≤ M`), the high part is the geometric tail bounded in `hhigh`
  have hsplit : ∑ i ∈ Finset.range n, ((deltaPoly M).coeff i : ℂ) * z ^ i
      = (∑ i ∈ Finset.range (M + 1), ((deltaPoly M).coeff i : ℂ) * z ^ i)
        + ∑ k ∈ Finset.range (n - (M + 1)),
            ((deltaPoly M).coeff (M + 1 + k) : ℂ) * z ^ (M + 1 + k) := by
    rw [← Finset.sum_range_add, show (M + 1) + (n - (M + 1)) = n from by omega]
  -- the low part agrees with the τ-sum
  have hlow : ∑ i ∈ Finset.range (M + 1), ((deltaPoly M).coeff i : ℂ) * z ^ i
      = ∑ i ∈ Finset.range (M + 1), z ^ i * deltaCoeffsFun i := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rcases Nat.eq_zero_or_pos i with rfl | h0
    · have hc0 : (deltaPoly M).coeff 0 = 0 := by
        change (X * (etaPoly M) ^ 24 : ℤ[X]).coeff 0 = 0
        exact Polynomial.coeff_X_mul_zero _
      rw [hc0, deltaCoeffsFun_zero]
      simp
    · rw [deltaPoly_coeff M (by omega) (by
        have := Finset.mem_range.mp hi
        omega)]
      rw [deltaCoeffsFun_pos i (by omega)]
      simp [mul_comm]
  -- the high part is a geometric tail
  have hhigh : ‖∑ k ∈ Finset.range (n - (M + 1)),
        ((deltaPoly M).coeff (M + 1 + k) : ℂ) * z ^ (M + 1 + k)‖
      ≤ 2 ^ (24 * M) * (ρ ^ (M + 1) / (1 - ρ)) := by
    have hcbound : ∀ k : ℕ,
        ((deltaPoly M).coeff (M + 1 + k)).natAbs ≤ 2 ^ (24 * M) := by
      intro k
      have hidx : M + 1 + k = (M + k) + 1 := by omega
      have hshift : (deltaPoly M).coeff (M + 1 + k) = ((etaPoly M) ^ 24).coeff (M + k) := by
        rw [hidx]
        change (X * (etaPoly M) ^ 24 : ℤ[X]).coeff ((M + k) + 1) = ((etaPoly M) ^ 24).coeff (M + k)
        exact Polynomial.coeff_X_mul _ (M + k)
      rw [hshift]
      exact coeff_natAbs_le_pnorm.trans (pnorm_etaPow24_le M)
    have hterm : ∀ k ∈ Finset.range (n - (M + 1)),
        ‖((deltaPoly M).coeff (M + 1 + k) : ℂ) * z ^ (M + 1 + k)‖
          ≤ 2 ^ (24 * M) * ρ ^ (M + 1 + k) := by
      intro k _
      have h1 : ‖((deltaPoly M).coeff (M + 1 + k) : ℂ)‖ ≤ (2 ^ (24 * M) : ℝ) := by
        rw [Complex.norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs]
        exact_mod_cast hcbound k
      calc ‖((deltaPoly M).coeff (M + 1 + k) : ℂ) * z ^ (M + 1 + k)‖
          = ‖((deltaPoly M).coeff (M + 1 + k) : ℂ)‖ * ‖z ^ (M + 1 + k)‖ := norm_mul _ _
        _ = ‖((deltaPoly M).coeff (M + 1 + k) : ℂ)‖ * ρ ^ (M + 1 + k) := by
            rw [norm_pow]
        _ ≤ 2 ^ (24 * M) * ρ ^ (M + 1 + k) :=
            mul_le_mul_of_nonneg_right h1 (pow_nonneg hρ _)
    have hsum : ‖∑ k ∈ Finset.range (n - (M + 1)),
        ((deltaPoly M).coeff (M + 1 + k) : ℂ) * z ^ (M + 1 + k)‖
        ≤ ∑ k ∈ Finset.range (n - (M + 1)), 2 ^ (24 * M) * ρ ^ (M + 1 + k) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ hterm k hk)
    have hcalc : ∑ k ∈ Finset.range (n - (M + 1)), 2 ^ (24 * M) * ρ ^ (M + 1 + k)
        = 2 ^ (24 * M) * ρ ^ (M + 1) * ∑ k ∈ Finset.range (n - (M + 1)), ρ ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      have hadd : ρ ^ (M + 1 + k) = ρ ^ (M + 1) * ρ ^ k := by rw [← pow_add]
      rw [hadd]
      ring
    calc ‖∑ k ∈ Finset.range (n - (M + 1)),
          ↑((deltaPoly M).coeff (M + 1 + k)) * z ^ (M + 1 + k)‖
        ≤ ∑ k ∈ Finset.range (n - (M + 1)), 2 ^ (24 * M) * ρ ^ (M + 1 + k) := hsum
      _ = 2 ^ (24 * M) * ρ ^ (M + 1) * ∑ k ∈ Finset.range (n - (M + 1)), ρ ^ k := hcalc
      _ ≤ 2 ^ (24 * M) * ρ ^ (M + 1) * (1 - ρ)⁻¹ := by
          refine mul_le_mul_of_nonneg_left (sum_range_pow_le_tsum _ hρ hz1) ?_
          positivity
      _ = 2 ^ (24 * M) * (ρ ^ (M + 1) / (1 - ρ)) := by
          field_simp
  rw [heval, hsplit, hlow, add_sub_cancel_left]
  exact hhigh

/-! ### Identifying the q-expansion of `Δ` -/

/-- **The value of the τ-series**: on the disc `2 ^ 24 • |z| < 1`, the series
`∑ τ(m) z^m` converges and equals the analytic product `z ∏' (1 - z^{m+1})^24`
for `Δ`. -/
theorem tsum_deltaCoeffsFun_eq {z : ℂ} (hz : 2 ^ 24 * ‖z‖ < 1) :
    (∑' m, z ^ m * deltaCoeffsFun m) = z * ∏' i, (1 - z ^ (i + 1)) ^ 24 := by
  have hρ1 : ‖z‖ < 1 := by
    have h1 : (1 : ℝ) ≤ 2 ^ 24 := by norm_num
    have h2 : (1 : ℝ) * ‖z‖ ≤ 2 ^ 24 * ‖z‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg z)
    rw [one_mul] at h2
    linarith
  have hsT : Tendsto (fun M ↦ ∑ m ∈ Finset.range (M + 1), z ^ m * deltaCoeffsFun m) atTop
      (𝓝 (∑' m, z ^ m * deltaCoeffsFun m)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (summable_deltaCoeffsFun hz).hasSum.tendsto_sum_nat
  have hm : Multipliable fun i ↦ 1 - z ^ (i + 1) := multipliable_one_sub_pow hρ1
  have hm24 : Multipliable fun i ↦ (1 - z ^ (i + 1)) ^ 24 := hm.pow 24
  have hpT : Tendsto (fun M ↦ z * ∏ i ∈ Finset.range M, (1 - z ^ (i + 1)) ^ 24) atTop
      (𝓝 (z * ∏' i, (1 - z ^ (i + 1)) ^ 24)) :=
    tendsto_const_nhds.mul hm24.hasProd.tendsto_prod_nat
  have hdist : ∀ M, ‖z * ∏ i ∈ Finset.range M, (1 - z ^ (i + 1)) ^ 24
      - ∑ m ∈ Finset.range (M + 1), z ^ m * deltaCoeffsFun m‖
      ≤ 2 ^ (24 * M) * (‖z‖ ^ (M + 1) / (1 - ‖z‖)) := by
    intro M
    have h := dist_poly_sum_le hρ1 M
    rwa [deltaPoly_aeval] at h
  have hbnd : Tendsto (fun M ↦ 2 ^ (24 * M) * (‖z‖ ^ (M + 1) / (1 - ‖z‖))) atTop (𝓝 0) := by
    have h1ρ : (1 : ℝ) - ‖z‖ ≠ 0 := sub_ne_zero_of_ne (by linarith)
    have hkey : (fun M ↦ 2 ^ (24 * M) * (‖z‖ ^ (M + 1) / (1 - ‖z‖)))
        = fun M ↦ (‖z‖ / (1 - ‖z‖)) * (2 ^ 24 * ‖z‖) ^ M := by
      funext M
      field_simp
      rw [pow_mul, mul_comm ‖z‖ (2 ^ 24), mul_pow, pow_succ]
      ring
    rw [hkey]
    have hc : Tendsto (fun _ : ℕ ↦ ‖z‖ / (1 - ‖z‖)) atTop
        (𝓝 (‖z‖ / (1 - ‖z‖))) := tendsto_const_nhds
    simpa [mul_zero] using
      hc.mul (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hz)
  have hse : Tendsto (fun M ↦ z * ∏ i ∈ Finset.range M, (1 - z ^ (i + 1)) ^ 24
      - ∑ m ∈ Finset.range (M + 1), z ^ m * deltaCoeffsFun m) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun M ↦ norm_nonneg _) hdist hbnd
  have hsum := hsT.add hse
  have hrw : (fun M ↦ (∑ m ∈ Finset.range (M + 1), z ^ m * deltaCoeffsFun m)
      + (z * ∏ i ∈ Finset.range M, (1 - z ^ (i + 1)) ^ 24
        - ∑ m ∈ Finset.range (M + 1), z ^ m * deltaCoeffsFun m))
      = fun M ↦ z * ∏ i ∈ Finset.range M, (1 - z ^ (i + 1)) ^ 24 :=
    funext fun M ↦ by ring
  rw [hrw] at hsum
  exact (tendsto_nhds_unique hpT (by simpa using hsum)).symm

/-- The cusp function of `Δ` is analytic at `0`. -/
private lemma analyticAt_cuspFunction_delta :
    AnalyticAt ℂ (cuspFunction 1 (ModularForm.discriminant : ℍ → ℂ)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero
    (f := (CuspForm.discriminant : CuspForm 𝒮ℒ 12)) one_pos one_mem_strictPeriods_SL

/-- The cusp function of `Δ` has the q-expansion power series at `0`. -/
private lemma hasFPowSeries_cuspFunction_delta :
    HasFPowerSeriesAt (cuspFunction 1 (ModularForm.discriminant : ℍ → ℂ))
      (qExpansionFormalMultilinearSeries 1 (CuspForm.discriminant : CuspForm 𝒮ℒ 12)) 0 := by
  simpa [qExpansionFormalMultilinearSeries, qExpansion_coeff, div_eq_mul_inv, mul_comm] using
    analyticAt_cuspFunction_delta.hasFPowerSeriesAt

/-- The τ-series has the scalar power series at `0`. -/
private lemma hasFPowSeries_deltaFun :
    HasFPowerSeriesAt (fun z ↦ ∑' m, z ^ m * deltaCoeffsFun m)
      (FormalMultilinearSeries.ofScalars ℂ deltaCoeffsFun) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by positivity : (0 : ℝ) < 1 / 2 ^ 24)] with z hz
  rw [mem_ball_zero_iff] at hz
  have hz24 : 2 ^ 24 * ‖z‖ < 1 := by
    have h1 : (2 : ℝ) ^ 24 * (1 / (2 : ℝ) ^ 24) = 1 := by field_simp
    calc 2 ^ 24 * ‖z‖ < 2 ^ 24 * (1 / 2 ^ 24) :=
          mul_lt_mul_of_pos_left hz (by positivity : (0 : ℝ) < 2 ^ 24)
      _ = 1 := h1
  simpa [smul_eq_mul, FormalMultilinearSeries.coeff_ofScalars, zero_add] using
    (summable_deltaCoeffsFun hz24).hasSum

/-- Near `0`, the cusp function of `Δ` agrees with the τ-series. -/
private lemma eventually_eq_cuspFunction_deltaFun :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      cuspFunction 1 (ModularForm.discriminant : ℍ → ℂ) z
        = ∑' m, z ^ m * deltaCoeffsFun m := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by positivity : (0 : ℝ) < 1 / 2 ^ 24)] with z hz
  rw [mem_ball_zero_iff] at hz
  have hz24 : 2 ^ 24 * ‖z‖ < 1 := by
    have h1 : (2 : ℝ) ^ 24 * (1 / (2 : ℝ) ^ 24) = 1 := by field_simp
    calc 2 ^ 24 * ‖z‖ < 2 ^ 24 * (1 / 2 ^ 24) :=
          mul_lt_mul_of_pos_left hz (by positivity : (0 : ℝ) < 2 ^ 24)
      _ = 1 := h1
  have hz1 : ‖z‖ < 1 := by
    have h1 : (1 : ℝ) ≤ 2 ^ 24 := by norm_num
    have h2 : (1 : ℝ) * ‖z‖ ≤ 2 ^ 24 * ‖z‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg z)
    rw [one_mul] at h2
    linarith
  rw [tsum_deltaCoeffsFun_eq hz24,
    ModularForm.discriminant_cuspFunction_eqOn (mem_ball_zero_iff.mpr hz1)]

/-- **The analytic-to-algebraic bridge for τ**: the `n`-th coefficient of the
q-expansion of the modular discriminant is `δ n`, i.e. `τ n` for `n ≥ 1` and
`0` for `n = 0`. -/
theorem qExpansion_discriminant_coeff (n : ℕ) :
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff n = deltaCoeffsFun n := by
  have hp : qExpansionFormalMultilinearSeries 1 (CuspForm.discriminant : CuspForm 𝒮ℒ 12)
      = FormalMultilinearSeries.ofScalars ℂ deltaCoeffsFun :=
    hasFPowSeries_cuspFunction_delta.eq_formalMultilinearSeries_of_eventually
      hasFPowSeries_deltaFun eventually_eq_cuspFunction_deltaFun
  have h := qExpansionFormalMultilinearSeries_coeff (h := 1)
    (f := (CuspForm.discriminant : CuspForm 𝒮ℒ 12)) n
  rw [hp, FormalMultilinearSeries.coeff_ofScalars] at h
  exact h.symm

/-- **The Fourier coefficients of Δ are the Ramanujan τ numbers**: for `n ≥ 1`,
the `n`-th q-expansion coefficient of the modular discriminant equals
`τ n` (as an integer, cast to `ℂ`). -/
theorem qExpansion_discriminant_coeff_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff n = ((tau n : ℤ) : ℂ) := by
  rw [qExpansion_discriminant_coeff, deltaCoeffsFun_pos n hn]

/-- The constant coefficient of the q-expansion of `Δ` vanishes. -/
theorem qExpansion_discriminant_coeff_zero :
    (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff 0 = 0 := by
  rw [qExpansion_discriminant_coeff, deltaCoeffsFun_zero]

/-- Consistency with Mathlib's `discriminant_qExpansion_coeff_one` and
`tau_one`: both give coefficient `1`. -/
example : (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff 1 = 1 := by
  rw [qExpansion_discriminant_coeff_of_ne_zero one_ne_zero, tau_one]
  norm_num

end Ramanujan
