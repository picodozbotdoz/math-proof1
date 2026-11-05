import MathProof.ModularForms.HeckeIndex
import MathProof.ModularForms.HeckeFieldRat
import MathProof.ModularForms.MaedaCertC
import Mathlib.RingTheory.PowerBasis
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Module.Submodule.Lattice

/-!
# HeckeLatticeIndex: the lattice index `[𝕋 : ℤ[T₂]]` as a determinant

The generic core of the index-card track (iteration 24, b1): the index of the
Hecke lattice `𝕋` over the polynomial lattice `ℤ[T₂]`, as an honest
`AddSubgroup.relIndex` equal to `|det C|` of the integer basis-change matrix.

* `t2Lattice T2 n` — the lattice `ℤ[T₂] = span_ℤ {T₂^i : i < n}` inside
  `End ℂ V` (as a `Submodule ℤ`), and `relIndex_t2_eq_det` — the **core
  theorem**: with the minimal polynomial of `T₂` of degree `n`, a
  ℂ-independent family `u` and integer expansions
  `T₂^i = ∑_j C i j • u j`, the relative index of the two lattices is
  `C.det.natAbs` — `AddSubgroup.relIndex_eq_natAbs_det` applied with the
  ℤ-bases of the two spans (`LinearIndependent.restrict_scalars'` +
  `Basis.mk`), the determinant read off through `Basis.det_apply`.
  `natCard_quot_eq_det` is the `Nat.card (𝕋 ⧸ ℤ[T₂])` phrasing.
* `millerTopC` / `millerCoeff` — the fb-coefficients of the Miller basis as a
  ℤ-structural accumulator mirroring `HeckeIndex.millerTop` (kernel-reducible),
  with the bridge `miller_eq_fb_sum`.
* The **dual-coordinates route** to the per-weight expansion hypothesis:
  `coeff_one_heckeTM` (`a_1 (T_{l+1} (g j)) = δ_{lj}` on the Miller basis),
  `op_eq_zero_of_dual_zero` (an operator expanding over the Hecke family with
  vanishing dual coordinates is zero), and `t2_pow_eq_smul_heckeTM`: the
  coordinates of the powers `T₂^i` over `T_1, …, T_n` follow from ONE integer
  matrix identity `hcard` — the row-0s of the fb-matrix powers conjugated by
  the Miller transform — which the generated per-weight files certify
  entrywise by `decide +kernel`.
* `index_card_hecke` / `index_card_hecke_natCard` — the per-weight entry
  points consumed by `HeckeIndexCard{Small,}Weights.lean`.

Everything here is generic (no data, no `decide`); light: no `set_option`,
and nothing is an ancestor of the heavy `MaedaGalois5` chain.
-/

namespace HeckeLatticeIndex

open Module MaedaLevelOne Polynomial HeckeTM HeckeIndex HeckeFieldRat
open UpperHalfPlane ModularForm CuspForm
open scoped MatrixGroups

/-! ### The ℤ-span basis machinery -/

section Span

variable {M : Type*} [AddCommGroup M] {n : ℕ}

/-- **Basis-change determinant.**  If the family `w` expands over the
independent family `u` with the integer matrix `D` (`w i = ∑_j D i j • u j`),
then the determinant of any family with the same values over the induced
basis `Basis.span` of `span ℤ (range u)` is `D.det`. -/
private theorem det_eq_of_expansions (u : Fin n → M) (hli : LinearIndependent ℤ u)
    (D : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → M)
    (hw : ∀ i : Fin n, w i = ∑ j : Fin n, D i j • u j)
    (v : Fin n → ↥(Submodule.span ℤ (Set.range u)))
    (hv : ∀ i : Fin n, ((v i : ↥(Submodule.span ℤ (Set.range u))) : M) = w i) :
    (Basis.span hli).det v = D.det := by
  have hbl : ∀ l : Fin n,
      ((Basis.span hli l : ↥(Submodule.span ℤ (Set.range u))) : M) = u l :=
    fun l => Basis.coe_span_apply hli l
  have hvj : ∀ i : Fin n, v i = ∑ l : Fin n, D i l • Basis.span hli l := by
    intro i
    refine Subtype.ext ?_
    rw [hv i, hw i, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast
    rw [hbl l]
  rw [Basis.det_apply]
  have htm : (Basis.span hli).toMatrix v = Matrix.transpose D := by
    ext i j
    rw [Basis.toMatrix_apply, hvj j, map_sum, Finsupp.finsetSum_apply]
    have hsmul : ∀ l : Fin n, (Basis.span hli).repr (D j l • Basis.span hli l) i
        = D j l * (if l = i then (1 : ℤ) else 0) := by
      intro l
      rw [map_smul, Finsupp.smul_apply, Basis.repr_self_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl fun l _ => hsmul l]
    simp [Matrix.transpose_apply]
  rw [htm, Matrix.det_transpose]

end Span

/-! ### The lattice `ℤ[T₂]` and the core index theorem -/

section Lattice

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

/-- The polynomial lattice `ℤ[T₂] = span_ℤ {T₂^i : i < n}` of an operator on
`V`, as a submodule of `End ℂ V` over ℤ. -/
noncomputable def t2Lattice (T2 : V →ₗ[ℂ] V) (n : ℕ) :
    Submodule ℤ (V →ₗ[ℂ] V) :=
  Submodule.span ℤ (Set.range fun i : Fin n => (T2 : Module.End ℂ V) ^ (i : ℕ))

/-- **The core index theorem.**  With the minimal polynomial of `T₂` of
degree `n`, a ℂ-independent target family `u`, and integer expansions of the
powers `T₂^i = ∑_j C i j • u j`, the relative index of the ℤ-span of the
powers in the ℤ-span of `u` is exactly `|det C|`. -/
theorem relIndex_t2_eq_det (T2 : V →ₗ[ℂ] V)
    (hmin : (minpoly ℂ (T2 : Module.End ℂ V)).natDegree = n)
    (u : Fin n → (V →ₗ[ℂ] V)) (hli : LinearIndependent ℂ u)
    (C : Matrix (Fin n) (Fin n) ℤ)
    (hC : ∀ i : Fin n, (T2 : Module.End ℂ V) ^ (i : ℕ)
      = ∑ j : Fin n, ((C i j : ℤ) : ℂ) • u j) :
    (t2Lattice T2 n).toAddSubgroup.relIndex
        (Submodule.span ℤ (Set.range u)).toAddSubgroup = C.det.natAbs := by
  classical
  -- memberships and the lattice inclusion
  have hw : ∀ i : Fin n, (T2 : Module.End ℂ V) ^ (i : ℕ)
      = ∑ j : Fin n, C i j • u j := by
    intro i
    rw [hC i]
    exact Finset.sum_congr rfl fun j _ => Int.cast_smul_eq_zsmul ℂ _ _
  have hmem : ∀ i : Fin n, (T2 : Module.End ℂ V) ^ (i : ℕ)
      ∈ Submodule.span ℤ (Set.range u) := by
    intro i
    rw [hw i]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ (C i j) (Submodule.subset_span (Set.mem_range_self j))
  have H : t2Lattice T2 n ≤ Submodule.span ℤ (Set.range u) := by
    rw [t2Lattice, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  -- ℂ-independence of the powers
  have hpowli : LinearIndependent ℂ
      (fun i : Fin n => (T2 : Module.End ℂ V) ^ (i : ℕ)) := by
    have h := linearIndependent_pow (K := ℂ) (T2 : Module.End ℂ V)
    rw [hmin] at h
    exact h
  have hdet := det_eq_of_expansions u (LinearIndependent.restrict_scalars' ℤ hli) C
    (fun i => (T2 : Module.End ℂ V) ^ (i : ℕ)) hw
    (fun i => (⟨(T2 : Module.End ℂ V) ^ (i : ℕ), hmem i⟩ :
      ↥(Submodule.span ℤ (Set.range u)))) (fun _ => rfl)
  let B₁ : Basis (Fin n) ℤ ↥(t2Lattice T2 n) :=
    Basis.span (LinearIndependent.restrict_scalars' ℤ hpowli)
  let B₂ : Basis (Fin n) ℤ ↥(Submodule.span ℤ (Set.range u)) :=
    Basis.span (LinearIndependent.restrict_scalars' ℤ hli)
  have hB₁v : ∀ i : Fin n,
      ((B₁ i : ↥(t2Lattice T2 n)) : Module.End ℂ V) = (T2 : Module.End ℂ V) ^ (i : ℕ) :=
    fun i => Basis.coe_span_apply
      (LinearIndependent.restrict_scalars' ℤ hpowli) i
  have hfamily : (fun i : Fin n =>
      (⟨((B₁ i : ↥(t2Lattice T2 n)) : Module.End ℂ V),
        H (SetLike.coe_mem (B₁ i))⟩ : ↥(Submodule.span ℤ (Set.range u))))
      = fun i : Fin n => (⟨(T2 : Module.End ℂ V) ^ (i : ℕ), hmem i⟩ :
        ↥(Submodule.span ℤ (Set.range u))) := by
    funext i
    exact Subtype.ext (hB₁v i)
  have hdet2 : B₂.det (fun i : Fin n => (⟨(T2 : Module.End ℂ V) ^ (i : ℕ), hmem i⟩ :
      ↥(Submodule.span ℤ (Set.range u)))) = C.det := hdet
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ H B₁ B₂]
  calc (B₂.det fun i : Fin n =>
        (⟨((B₁ i : ↥(t2Lattice T2 n)) : Module.End ℂ V),
          H (SetLike.coe_mem (B₁ i))⟩ : ↥(Submodule.span ℤ (Set.range u)))).natAbs
      = (B₂.det fun i : Fin n => (⟨(T2 : Module.End ℂ V) ^ (i : ℕ), hmem i⟩ :
          ↥(Submodule.span ℤ (Set.range u)))).natAbs := by rw [hfamily]
    _ = C.det.natAbs := congrArg Int.natAbs hdet2

/-- **The quotient-cardinality phrasing.**  The same index as the cardinal of
the quotient of the `u`-span by the power lattice. -/
theorem natCard_quot_eq_det (T2 : V →ₗ[ℂ] V)
    (hmin : (minpoly ℂ (T2 : Module.End ℂ V)).natDegree = n)
    (u : Fin n → (V →ₗ[ℂ] V)) (hli : LinearIndependent ℂ u)
    (C : Matrix (Fin n) (Fin n) ℤ)
    (hC : ∀ i : Fin n, (T2 : Module.End ℂ V) ^ (i : ℕ)
      = ∑ j : Fin n, ((C i j : ℤ) : ℂ) • u j) :
    Nat.card (↥(Submodule.span ℤ (Set.range u)).toAddSubgroup ⧸
      (t2Lattice T2 n).toAddSubgroup.addSubgroupOf
        (Submodule.span ℤ (Set.range u)).toAddSubgroup) = C.det.natAbs := by
  have h := relIndex_t2_eq_det T2 hmin u hli C hC
  rw [show AddSubgroup.relIndex (t2Lattice T2 n).toAddSubgroup
      (Submodule.span ℤ (Set.range u)).toAddSubgroup
      = ((t2Lattice T2 n).toAddSubgroup.addSubgroupOf
          (Submodule.span ℤ (Set.range u)).toAddSubgroup).index from rfl,
    AddSubgroup.index_eq_card] at h
  exact h

end Lattice

/-! ### The ℤ-valued Miller accumulator -/

section MillerCoeffs

variable {k : ℤ} {n : ℕ}

/-- The ℤ-valued Miller accumulator over an integer echelon table: position
`t` of `millerTopC a n r` holds the fb-coefficients (over `f_0, …, f_{n-1}`)
of `g_{t + (n - r)}` — the same accumulator shape as `HeckeIndex.millerTop`,
with the family replaced by unit rows.  Structural on the accumulator length,
so it kernel-reduces on numerals. -/
def millerTopC (a : ℕ → ℕ → ℤ) (n : ℕ) : ℕ → List (ℕ → ℤ)
  | 0 => []
  | r + 1 =>
      (fun c => (if c = n - 1 - r then 1 else 0)
        - ((List.range r).map fun t => a (n - 1 - r) (t + (n - r))
            * (millerTopC a n r).getD t (fun _ => 0) c).sum) :: millerTopC a n r

/-- The recursion step of `millerTopC` with the reduction as a `Finset` sum
(the definition uses a `List` sum so that kernel certificates stay
`propext`-only — AGENTS.md "Finset sums inside a decide"). -/
theorem millerTopC_succ (a : ℕ → ℕ → ℤ) (n r : ℕ) :
    millerTopC a n (r + 1)
      = (fun c => (if c = n - 1 - r then 1 else 0)
        - ∑ t ∈ Finset.range r, a (n - 1 - r) (t + (n - r))
            * (millerTopC a n r).getD t (fun _ => 0) c) :: millerTopC a n r := by
  simp only [millerTopC, MaedaLevelOne.finset_sum_range_eq_list]

/-- The fb-coefficients of the Miller vector `g_j` (row of `millerTopC a n`
at position `0` of the accumulator stopped at `n - j`, mirroring
`HeckeIndex.miller`). -/
def millerCoeff (a : ℕ → ℕ → ℤ) (n j c : ℕ) : ℤ :=
  (millerTopC a n (n - j)).getD 0 (fun _ => 0) c

/-- The accumulator bridge: the Miller vectors expand over the echelon family
with `millerCoeff` coefficients. -/
theorem miller_eq_fb_sum (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (a : ℕ → ℕ → ℤ) (hAeq : ∀ i j : ℕ, i < j → j < n → A i j = ((a i j : ℤ) : ℂ))
    (j : ℕ) (hj : j < n) :
    miller f A n j
      = ∑ c : Fin n, ((millerCoeff a n j c.val : ℤ) : ℂ) • f c.val := by
  -- the echelon family expands over itself with unit rows
  have hunit : ∀ i : ℕ, i < n → f i = ∑ c ∈ Finset.range n,
      (((if c = i then 1 else 0 : ℤ) : ℂ)) • f c := by
    intro i hi
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hni
      exact absurd (Finset.mem_range.mpr hi) hni
  have main : ∀ r : ℕ, r ≤ n → ∀ t : ℕ, t < r →
      miller f A n (t + (n - r))
        = ∑ c ∈ Finset.range n,
            (((millerTopC a n r).getD t (fun _ => 0) c : ℤ) : ℂ) • f c := by
    intro r
    induction r with
    | zero => intro _ t ht; exact absurd ht (Nat.not_lt_zero t)
    | succ r ih =>
      intro hr t ht
      rw [millerTopC_succ]
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · -- the fresh head: the reduction of `f_{n-1-r}` against the rows above
        have hjx : n - 1 - r < n := by omega
        have hidx : 0 + (n - (r + 1)) = n - 1 - r := by omega
        -- per-entry split of the head row (unit row minus reduction rows)
        have hper : ∀ c ∈ Finset.range n,
            (((if c = n - 1 - r then (1 : ℤ) else 0)
              - ∑ t ∈ Finset.range r, a (n - 1 - r) (t + (n - r))
                * (millerTopC a n r).getD t (fun _ => 0) c : ℤ) : ℂ) • f c
            = (((if c = n - 1 - r then (1 : ℤ) else 0) : ℂ)) • f c
              - ∑ t ∈ Finset.range r, ((a (n - 1 - r) (t + (n - r))
                  * (millerTopC a n r).getD t (fun _ => 0) c : ℤ) : ℂ) • f c := by
          intro c _
          have hc1 : ((∑ t ∈ Finset.range r, a (n - 1 - r) (t + (n - r))
                * (millerTopC a n r).getD t (fun _ => 0) c : ℤ) : ℂ) • f c
              = ∑ t ∈ Finset.range r, ((a (n - 1 - r) (t + (n - r))
                  * (millerTopC a n r).getD t (fun _ => 0) c : ℤ) : ℂ) • f c := by
            push_cast
            exact Finset.sum_smul
          rw [Int.cast_sub, sub_smul, hc1]
          congr 1
          by_cases hb : c = n - 1 - r <;> simp [hb]
        -- per-entry split, summed: the double-sum exchange is hex
        have hL : ∑ c ∈ Finset.range n,
                (((if c = n - 1 - r then (1 : ℤ) else 0)
                  - ∑ t ∈ Finset.range r, a (n - 1 - r) (t + (n - r))
                    * (millerTopC a n r).getD t (fun _ => 0) c : ℤ) : ℂ) • f c
            = ∑ c ∈ Finset.range n,
                  (((if c = n - 1 - r then (1 : ℤ) else 0) : ℂ)) • f c
                - ∑ t ∈ Finset.range r, ((a (n - 1 - r) (t + (n - r)) : ℤ) : ℂ)
                    • ∑ c ∈ Finset.range n,
                        (((millerTopC a n r).getD t (fun _ => 0) c : ℤ) : ℂ) • f c := by
          have hex : ∑ c ∈ Finset.range n, ∑ t ∈ Finset.range r,
                  ((a (n - 1 - r) (t + (n - r))
                    * (millerTopC a n r).getD t (fun _ => 0) c : ℤ) : ℂ) • f c
              = ∑ t ∈ Finset.range r, ((a (n - 1 - r) (t + (n - r)) : ℤ) : ℂ)
                  • ∑ c ∈ Finset.range n,
                      (((millerTopC a n r).getD t (fun _ => 0) c : ℤ) : ℂ) • f c := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun t _ => ?_
            simp only [Int.cast_mul, mul_smul]
            rw [← Finset.smul_sum]
          calc ∑ c ∈ Finset.range n,
                (((if c = n - 1 - r then (1 : ℤ) else 0)
                  - ∑ t ∈ Finset.range r, a (n - 1 - r) (t + (n - r))
                    * (millerTopC a n r).getD t (fun _ => 0) c : ℤ) : ℂ) • f c
              = ∑ c ∈ Finset.range n,
                  ((((if c = n - 1 - r then (1 : ℤ) else 0) : ℂ) • f c
                    - ∑ t ∈ Finset.range r, ((a (n - 1 - r) (t + (n - r))
                      * (millerTopC a n r).getD t (fun _ => 0) c : ℤ) : ℂ) • f c)) :=
                  Finset.sum_congr rfl fun c hc => hper c hc
            _ = (∑ c ∈ Finset.range n,
                  (((if c = n - 1 - r then (1 : ℤ) else 0) : ℂ)) • f c)
                - ∑ t ∈ Finset.range r, ((a (n - 1 - r) (t + (n - r)) : ℤ) : ℂ)
                    • ∑ c ∈ Finset.range n,
                        (((millerTopC a n r).getD t (fun _ => 0) c : ℤ) : ℂ) • f c := by
                  rw [Finset.sum_sub_distrib, hex]
        -- the reduction terms, integrally and by the induction hypothesis
        have htr : ∀ t ∈ Finset.range r, t < r := fun t ht => Finset.mem_range.mp ht
        have hred : ∑ t ∈ Finset.range r, A (n - 1 - r) (t + (n - r))
                • miller f A n (t + (n - r))
            = ∑ t ∈ Finset.range r, ((a (n - 1 - r) (t + (n - r)) : ℤ) : ℂ)
                • ∑ c ∈ Finset.range n,
                    (((millerTopC a n r).getD t (fun _ => 0) c : ℤ) : ℂ) • f c := by
          refine Finset.sum_congr rfl fun t ht => ?_
          have htr' : t < r := htr t ht
          rw [hAeq (n - 1 - r) (t + (n - r)) (by omega) (by omega),
            ih (by omega) t htr']
        rw [hidx, miller_of_lt f A n hjx,
          show n - 1 - (n - 1 - r) = r from by omega,
          show n - 1 - r + 1 = n - r from by omega,
          List.getD_cons_zero, hunit (n - 1 - r) hjx, hred, hL]
        refine congrArg₂ Sub.sub ?_ rfl
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases hb : c = n - 1 - r <;> simp [hb]
      · -- an older entry: the induction hypothesis, index shifted
        obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        rw [List.getD_cons_succ,
          show s + 1 + (n - (r + 1)) = s + (n - r) from by omega]
        exact ih (by omega) s (by omega)
  have h := main (n - j) (by omega) 0 (by omega)
  rw [show 0 + (n - (n - j)) = j from by omega] at h
  rw [h]
  exact (Fin.sum_univ_eq_sum_range
    (fun c : ℕ => (((millerTopC a n (n - j)).getD 0 (fun _ => 0) c : ℤ) : ℂ) • f c) n).symm

end MillerCoeffs

/-! ### The dual-coordinates route to the expansion hypothesis -/

section Dual

variable {k : ℤ} {n : ℕ}

/-- Coefficients of a difference. -/
private lemma coeff_sub_l (f g : CuspForm 𝒮ℒ k) (m : ℕ) :
    (qExpansion 1 ⇑(f - g)).coeff m
      = (qExpansion 1 ⇑f).coeff m - (qExpansion 1 ⇑g).coeff m := by
  have h1 : (qL k (f - g)).coeff m = (qL k f - qL k g).coeff m := by rw [map_sub]
  have h2 : (qL k f - qL k g).coeff m = (qL k f).coeff m - (qL k g).coeff m := by
    rw [map_sub]
  rw [← qL_apply (f - g), ← qL_apply f, ← qL_apply g, h1, h2]

/-- First coefficients of the echelon family: `a_1 (f_l) = δ_{l0}` for
`l < n`. -/
theorem coeff_one_fb (f : ℕ → CuspForm 𝒮ℒ k)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (l : ℕ) (hl : l < n) :
    (qExpansion 1 (f l)).coeff 1 = if l = 0 then (1 : ℂ) else 0 := by
  rcases Nat.eq_zero_or_pos l with h0 | hpos
  · subst h0
    simp [hone 0 hl]
  · have hl0 : l ≠ 0 := by omega
    rw [hzero l 1 hl le_rfl (by omega)]
    simp [hl0]

/-- **Duality on the Miller basis**: `a_1 (T_{l+1} (g j)) = δ_{lj}`. -/
theorem coeff_one_heckeTM (g : ℕ → CuspForm 𝒮ℒ k)
    (hδ : ∀ j m : ℕ, j < n → m < n →
      (qExpansion 1 (g j)).coeff (m + 1) = if m = j then 1 else 0)
    (l j : Fin n) :
    (qExpansion 1 (heckeTM k (l.val + 1) (g j.val))).coeff 1
      = if l = j then (1 : ℂ) else 0 := by
  rw [coeff_heckeTM_symm (g j.val) (by omega) le_rfl, heckeTM_id, LinearMap.id_apply,
    hδ j.val l.val j.isLt l.isLt]
  by_cases h : l = j
  · subst h
    simp
  · have hv : l.val ≠ j.val := fun hh => h (Fin.val_inj.mp hh)
    simp [h, hv]

/-- An operator expanding over the Hecke family with vanishing dual
coordinates is zero. -/
theorem op_eq_zero_of_dual_zero (g : ℕ → CuspForm 𝒮ℒ k)
    (hδ : ∀ j m : ℕ, j < n → m < n →
      (qExpansion 1 (g j)).coeff (m + 1) = if m = j then 1 else 0)
    (S : Module.End ℂ (CuspForm 𝒮ℒ k)) (σ : Fin n → ℂ)
    (hS : S = ∑ l : Fin n, σ l • heckeTM k (l.val + 1))
    (h0 : ∀ j : Fin n, (qExpansion 1 (S (g j.val))).coeff 1 = 0) : S = 0 := by
  have hσ : ∀ j : Fin n, σ j = 0 := by
    intro j
    have happ : S (g j.val)
        = ∑ l : Fin n, σ l • heckeTM k (l.val + 1) (g j.val) := by
      rw [hS, LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun l _ => LinearMap.smul_apply _ _ _
    have hc : (qExpansion 1 (S (g j.val))).coeff 1
        = ∑ l : Fin n, σ l * (if l = j then (1 : ℂ) else 0) := by
      rw [happ, coeff_sum Finset.univ σ
          (fun l => heckeTM k (l.val + 1) (g j.val)) 1]
      exact Finset.sum_congr rfl fun l _ => by rw [coeff_one_heckeTM g hδ l j]
    simp only [mul_ite, mul_one, mul_zero] at hc
    rw [Finset.sum_ite_eq' Finset.univ j (fun l => σ l), h0 j] at hc
    simp only [Finset.mem_univ, ite_true] at hc
    exact hc.symm
  calc S = ∑ l : Fin n, σ l • heckeTM k (l.val + 1) := hS
    _ = ∑ l : Fin n, (0 : ℂ) • heckeTM k (l.val + 1) :=
        Finset.sum_congr rfl fun l _ => by rw [hσ l]
    _ = 0 := by simp

end Dual

/-! ### The `List`-based kernel certificate for `hcard` -/

section ListCert

variable {n : ℕ}

/-- Matrix entries at natural-number indices (`0` outside the range). -/
def mget (M : Matrix (Fin n) (Fin n) ℤ) (i j : ℕ) : ℤ :=
  if h : i < n ∧ j < n then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- Row `0` of the powers `M^i` as `List`s (`List` sums: kernel-reducible
without `Finset`'s quotient, so certificates stay `propext`-only). -/
def rowPowL (m : ℕ → ℕ → ℤ) (n : ℕ) : ℕ → List ℤ
  | 0 => (List.range n).map fun c => if c = 0 then 1 else 0
  | i + 1 => (List.range n).map fun c =>
      ((List.range n).map fun l => (rowPowL m n i).getD l 0 * m l c).sum

/-- The `List` twin of the `hcard` cell `∑_c μ_{jc} (M2^i)_{0c}`. -/
def cellL (a m : ℕ → ℕ → ℤ) (n i j : ℕ) : ℤ :=
  ((List.range n).map fun c => millerCoeff a n j c * (rowPowL m n i).getD c 0).sum

/-- The whole `hcard` identity as ONE boolean (one `decide +kernel` per weight). -/
def cardCheck (a : ℕ → ℕ → ℤ) (M2 C : Matrix (Fin n) (Fin n) ℤ) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j =>
    cellL a (mget M2) n i j == mget C i j

lemma getD_map_range (f : ℕ → ℤ) {c : ℕ} (hc : c < n) :
    ((List.range n).map f).getD c 0 = f c := by
  rw [List.getD_eq_getElem _ _ (by simpa using hc)]
  simp

lemma list_sum_eq_fin_sum (f : ℕ → ℤ) :
    ((List.range n).map f).sum = ∑ l : Fin n, f l.val := by
  rw [← MaedaLevelOne.finset_sum_range_eq_list]
  exact (Fin.sum_univ_eq_sum_range f n).symm

lemma mget_apply (M : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    mget M i.val j.val = M i j := by
  simp [mget, i.isLt, j.isLt]

lemma rowPowL_getD [NeZero n] (M : Matrix (Fin n) (Fin n) ℤ) (i : ℕ) (c : Fin n) :
    (rowPowL (mget M) n i).getD c.val 0 = (M ^ i) 0 c := by
  induction i generalizing c with
  | zero =>
      rw [rowPowL, getD_map_range _ c.isLt, pow_zero, Matrix.one_apply]
      by_cases h : c.val = 0
      · have hc : (0 : Fin n) = c := Fin.ext (by rw [h]; rfl)
        simp [h, hc]
      · have hc : (0 : Fin n) ≠ c := fun hh => h (by rw [← hh]; rfl)
        simp [h, hc]
  | succ i ih =>
      rw [rowPowL, getD_map_range _ c.isLt, pow_succ, Matrix.mul_apply,
        list_sum_eq_fin_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [ih l, mget_apply]

lemma cellL_eq [NeZero n] (a : ℕ → ℕ → ℤ) (M2 : Matrix (Fin n) (Fin n) ℤ) (i j : ℕ) :
    cellL a (mget M2) n i j
      = ∑ c : Fin n, millerCoeff a n j c.val * (M2 ^ i) 0 c := by
  rw [cellL, list_sum_eq_fin_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [rowPowL_getD]

/-- **The `hcard` bridge**: the boolean certificate gives the matrix identity
consumed by `index_card_dimN`. -/
theorem hcard_of_check [NeZero n] (a : ℕ → ℕ → ℤ) (M2 C : Matrix (Fin n) (Fin n) ℤ)
    (h : cardCheck a M2 C = true) :
    Matrix.of (fun i j : Fin n =>
      ∑ c : Fin n, millerCoeff a n j.val c.val * (M2 ^ (i : ℕ)) 0 c) = C := by
  ext i j
  simp only [cardCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [Matrix.of_apply, ← cellL_eq, h i.val i.isLt j.val j.isLt, mget_apply]

end ListCert

/-! ### The per-weight expansion from the matrix-power certificate -/

section Assemble

variable {k : ℤ} {n : ℕ} [NeZero n]

/-- **The key coefficient computation.**  The dual coordinate of a power of
`T₂` is the row-0 of the Miller-conjugated matrix power: `a_1 (T₂^i (g j))`
is the dot product of the Miller row `j` with the row-0 readoffs of
`(M2 ^ i)` — exactly the entries the per-weight files decide. -/
theorem coeff_one_t2_pow (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (a : ℕ → ℕ → ℤ) (hAeq : ∀ i j : ℕ, i < j → j < n → A i j = ((a i j : ℤ) : ℂ))
    (M2 : Matrix (Fin n) (Fin n) ℤ)
    (hrep2 : ∀ i : Fin n, heckeTM k 2 (f i.val)
      = ∑ l : Fin n, ((M2 l i : ℤ) : ℂ) • f l.val)
    (i j : Fin n) :
    (qExpansion 1 ((heckeTM k 2 ^ (i : ℕ) : Module.End ℂ (CuspForm 𝒮ℒ k))
      (miller f A n j.val))).coeff 1
      = ((∑ c : Fin n, millerCoeff a n j.val c.val * (M2 ^ (i : ℕ)) 0 c : ℤ) : ℂ) := by
  have hpow := pow_rep (heckeTM k 2) M2 f hrep2
  -- the action on the Miller vector, collapsed to one sum over the fb index
  have hact : (heckeTM k 2 ^ (i : ℕ) : Module.End ℂ (CuspForm 𝒮ℒ k)) (miller f A n j.val)
      = ∑ l : Fin n, ((∑ c : Fin n,
          millerCoeff a n j.val c.val * (M2 ^ (i : ℕ)) l c : ℤ) : ℂ) • f l.val := by
    rw [miller_eq_fb_sum f A a hAeq j.val j.isLt, map_sum]
    have hterm : ∀ c : Fin n,
        ((heckeTM k 2 ^ (i : ℕ) : Module.End ℂ (CuspForm 𝒮ℒ k))
            (((millerCoeff a n j.val c.val : ℤ) : ℂ) • f c.val))
        = ∑ l : Fin n, (((millerCoeff a n j.val c.val
            * (M2 ^ (i : ℕ)) l c : ℤ) : ℂ)) • f l.val := by
      intro c
      rw [map_smul, hpow i.val c, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [smul_smul, ← Int.cast_mul]
    rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast
    exact Finset.sum_smul.symm
  -- read off the first coefficient
  rw [hact,
    show (qExpansion 1 ⇑(∑ l : Fin n, ((∑ c : Fin n, millerCoeff a n j.val c.val
        * (M2 ^ (i : ℕ)) l c : ℤ) : ℂ) • f l.val)).coeff 1
      = ∑ l : Fin n, ((∑ c : Fin n, millerCoeff a n j.val c.val
        * (M2 ^ (i : ℕ)) l c : ℤ) : ℂ) * (qExpansion 1 (f l.val)).coeff 1 from
      coeff_sum Finset.univ (fun l : Fin n =>
        ((∑ c : Fin n, millerCoeff a n j.val c.val
          * (M2 ^ (i : ℕ)) l c : ℤ) : ℂ)) (fun l : Fin n => f l.val) 1,
    Finset.sum_congr rfl fun l _ => by rw [coeff_one_fb f hzero hone l.val l.isLt],
    Finset.sum_eq_single (0 : Fin n)]
  · simp
  · intro l _ hl
    have hv : l.val ≠ 0 := fun h => hl (Fin.val_inj.mp h)
    simp [hv]
  · intro h0
    exact absurd (Finset.mem_univ (0 : Fin n)) h0

/-- **The expansion assembler.**  From the entrywise matrix identity `hcard`
(the per-weight kernel certificate) the powers of `T₂` expand over the Hecke
family `T_1, …, T_n` with the integer coordinates `C`. -/
theorem t2_pow_eq_smul_heckeTM (hn : 0 < n) (hk : 1 ≤ k)
    (hdim : Module.finrank ℂ (CuspForm 𝒮ℒ k) = n)
    (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j)
    (hfi : ∀ i : ℕ, i < n → ∀ m : ℕ, ∃ z : ℤ, (qExpansion 1 (f i)).coeff m = (z : ℂ))
    (a : ℕ → ℕ → ℤ) (hAeq : ∀ i j : ℕ, i < j → j < n → A i j = ((a i j : ℤ) : ℂ))
    (M2 : Matrix (Fin n) (Fin n) ℤ)
    (hrep2 : ∀ i : Fin n, heckeTM k 2 (f i.val)
      = ∑ l : Fin n, ((M2 l i : ℤ) : ℂ) • f l.val)
    (C : Matrix (Fin n) (Fin n) ℤ)
    (hcard : Matrix.of (fun i j : Fin n =>
      ∑ c : Fin n, millerCoeff a n j.val c.val * (M2 ^ (i : ℕ)) 0 c) = C) :
    ∀ i : Fin n, (heckeTM k 2 : Module.End ℂ (CuspForm 𝒮ℒ k)) ^ (i : ℕ)
      = ∑ j : Fin n, ((C i j : ℤ) : ℂ) • heckeTM k (j.val + 1) := by
  have hδ : ∀ j m : ℕ, j < n → m < n →
      (qExpansion 1 (miller f A n j)).coeff (m + 1) = if m = j then 1 else 0 :=
    fun j m hj hm => miller_coeff' f A hzero hone hA j m hj hm
  have hint : ∀ j m : ℕ, j < n → ∃ z : ℤ,
      (qExpansion 1 (miller f A n j)).coeff m = (z : ℂ) :=
    fun j m hj => miller_int f A hA hfi j m hj
  -- the powers lie in the ℂ-span of the Hecke family
  have hZ : ∀ i : Fin n, ∃ z : Fin n → ℂ,
      (heckeTM k 2 : Module.End ℂ (CuspForm 𝒮ℒ k)) ^ (i : ℕ)
        = ∑ l : Fin n, z l • heckeTM k (l.val + 1) := by
    intro i
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp
      (T2_pow_mem_heckeRing (miller f A n) hn
        (miller_linearIndependent f A hzero hone hA) hdim hδ hint hk i.val)
    refine ⟨fun l => ((w l : ℤ) : ℂ), ?_⟩
    rw [← hw]
    exact Finset.sum_congr rfl fun l _ => (Int.cast_smul_eq_zsmul ℂ _ _).symm
  intro i
  obtain ⟨z, hz⟩ := hZ i
  have hentry : ∀ j : Fin n, ((∑ c : Fin n,
      millerCoeff a n j.val c.val * (M2 ^ (i : ℕ)) 0 c : ℤ) : ℂ) = ((C i j : ℤ) : ℂ) := by
    intro j
    have hc := congrArg (fun X : Matrix (Fin n) (Fin n) ℤ => X i j) hcard
    simp only [Matrix.of_apply] at hc
    exact_mod_cast hc
  have key : ((heckeTM k 2 ^ (i : ℕ) : Module.End ℂ (CuspForm 𝒮ℒ k))
      - ∑ j : Fin n, ((C i j : ℤ) : ℂ) • heckeTM k (j.val + 1)) = 0 := by
    refine op_eq_zero_of_dual_zero (miller f A n) hδ _
      (fun l => z l - ((C i l : ℤ) : ℂ)) ?_ ?_
    · calc (heckeTM k 2 ^ (i : ℕ) : Module.End ℂ (CuspForm 𝒮ℒ k))
          - ∑ l : Fin n, ((C i l : ℤ) : ℂ) • heckeTM k (l.val + 1)
          = (∑ l : Fin n, z l • heckeTM k (l.val + 1))
            - ∑ l : Fin n, ((C i l : ℤ) : ℂ) • heckeTM k (l.val + 1) := by rw [hz]
        _ = ∑ l : Fin n, (z l - ((C i l : ℤ) : ℂ)) • heckeTM k (l.val + 1) := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun l _ => (sub_smul _ _ _).symm
    · intro j
      rw [LinearMap.sub_apply, coeff_sub_l,
        coeff_one_t2_pow f A hzero hone a hAeq M2 hrep2 i j, hentry j,
        LinearMap.sum_apply]
      simp only [LinearMap.smul_apply]
      rw [coeff_sum Finset.univ (fun l => ((C i l : ℤ) : ℂ))
          (fun l => heckeTM k (l.val + 1) (miller f A n j.val)) 1,
        Finset.sum_congr rfl fun l _ => by
          rw [coeff_one_heckeTM (miller f A n) hδ l j]]
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ j (fun l => ((C i l : ℤ) : ℂ)),
        ite_eq_left (Finset.mem_univ j), sub_self]
  exact sub_eq_zero.mp key

/-- **The per-weight index card.**  The relative index of `ℤ[T₂]` inside the
Hecke lattice `𝕋` equals `|det C|`, where `C` is certified entrywise by
`hcard` (the Miller-conjugated matrix-power rows). -/
theorem index_card_hecke (hn : 0 < n) (hk : 1 ≤ k)
    (hdim : Module.finrank ℂ (CuspForm 𝒮ℒ k) = n)
    (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j)
    (hfi : ∀ i : ℕ, i < n → ∀ m : ℕ, ∃ z : ℤ, (qExpansion 1 (f i)).coeff m = (z : ℂ))
    (hmin : (minpoly ℂ (heckeTM k 2 : Module.End ℂ (CuspForm 𝒮ℒ k))).natDegree = n)
    (a : ℕ → ℕ → ℤ) (hAeq : ∀ i j : ℕ, i < j → j < n → A i j = ((a i j : ℤ) : ℂ))
    (M2 : Matrix (Fin n) (Fin n) ℤ)
    (hrep2 : ∀ i : Fin n, heckeTM k 2 (f i.val)
      = ∑ l : Fin n, ((M2 l i : ℤ) : ℂ) • f l.val)
    (C : Matrix (Fin n) (Fin n) ℤ)
    (hcard : Matrix.of (fun i j : Fin n =>
      ∑ c : Fin n, millerCoeff a n j.val c.val * (M2 ^ (i : ℕ)) 0 c) = C) :
    (t2Lattice (heckeTM k 2) n).toAddSubgroup.relIndex
        (heckeLattice k n).toAddSubgroup = C.det.natAbs :=
  relIndex_t2_eq_det (heckeTM k 2) hmin
    (fun j : Fin n => heckeTM k (j.val + 1))
    (hecke_independent (miller f A n)
      (fun j m hj hm => miller_coeff' f A hzero hone hA j m hj hm))
    C (t2_pow_eq_smul_heckeTM hn hk hdim f A hzero hone hA hfi a hAeq M2 hrep2 C hcard)

/-- **The per-weight index card, quotient-cardinality phrasing.** -/
theorem index_card_hecke_natCard (hn : 0 < n) (hk : 1 ≤ k)
    (hdim : Module.finrank ℂ (CuspForm 𝒮ℒ k) = n)
    (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j)
    (hfi : ∀ i : ℕ, i < n → ∀ m : ℕ, ∃ z : ℤ, (qExpansion 1 (f i)).coeff m = (z : ℂ))
    (hmin : (minpoly ℂ (heckeTM k 2 : Module.End ℂ (CuspForm 𝒮ℒ k))).natDegree = n)
    (a : ℕ → ℕ → ℤ) (hAeq : ∀ i j : ℕ, i < j → j < n → A i j = ((a i j : ℤ) : ℂ))
    (M2 : Matrix (Fin n) (Fin n) ℤ)
    (hrep2 : ∀ i : Fin n, heckeTM k 2 (f i.val)
      = ∑ l : Fin n, ((M2 l i : ℤ) : ℂ) • f l.val)
    (C : Matrix (Fin n) (Fin n) ℤ)
    (hcard : Matrix.of (fun i j : Fin n =>
      ∑ c : Fin n, millerCoeff a n j.val c.val * (M2 ^ (i : ℕ)) 0 c) = C) :
    Nat.card (↥(heckeLattice k n).toAddSubgroup ⧸
      (t2Lattice (heckeTM k 2) n).toAddSubgroup.addSubgroupOf
        (heckeLattice k n).toAddSubgroup) = C.det.natAbs :=
  natCard_quot_eq_det (heckeTM k 2) hmin
    (fun j : Fin n => heckeTM k (j.val + 1))
    (hecke_independent (miller f A n)
      (fun j m hj hm => miller_coeff' f A hzero hone hA j m hj hm))
    C (t2_pow_eq_smul_heckeTM hn hk hdim f A hzero hone hA hfi a hAeq M2 hrep2 C hcard)

omit [NeZero n] in
/-- `T₂ = heckeTM k 2` acts on the echelon family by the integer matrix `M2`,
from the landed `coordN`-form data (`represents_dimN` + `heckeTM_prime`). -/
theorem heckeTM_two_rep_of_dimN (hn : 0 < n)
    (hdim : Module.finrank ℂ (CuspForm 𝒮ℒ k) = n)
    (f : ℕ → CuspForm 𝒮ℒ k) (A X2 : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j)
    (hX2 : ∀ (i m : ℕ), i < n → m < n →
      (qExpansion 1 (heckeTPₗ k Nat.prime_two (f i))).coeff (m + 1) = X2 i m)
    (M2 : Matrix (Fin n) (Fin n) ℤ)
    (hM2 : ∀ (i l : Fin n), coordN A (fun m => X2 i.val m) l.val = ((M2 l i : ℤ) : ℂ)) :
    ∀ i : Fin n, heckeTM k 2 (f i.val) = ∑ l : Fin n, ((M2 l i : ℤ) : ℂ) • f l.val := by
  intro i
  rw [heckeTM_prime k Nat.prime_two,
    represents_dimN hn hdim f A X2 hzero hone hA _ hX2 i]
  exact Finset.sum_congr rfl fun l _ => by rw [hM2 i l]

/-- **The per-weight index card from the landed echelon data**: the generated
files' entry point — `index_card_hecke` with `hrep2` derived from the
`coordN`-form `T₂` data and the determinant pinned to a signed literal `I`. -/
theorem index_card_dimN (hn : 0 < n) (hk : 1 ≤ k)
    (hdim : Module.finrank ℂ (CuspForm 𝒮ℒ k) = n)
    (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j)
    (hfi : ∀ i : ℕ, i < n → ∀ m : ℕ, ∃ z : ℤ, (qExpansion 1 (f i)).coeff m = (z : ℂ))
    (hmin : (minpoly ℂ (heckeTM k 2 : Module.End ℂ (CuspForm 𝒮ℒ k))).natDegree = n)
    (a : ℕ → ℕ → ℤ) (hAeq : ∀ i j : ℕ, i < j → j < n → A i j = ((a i j : ℤ) : ℂ))
    (X2 : ℕ → ℕ → ℂ)
    (hX2 : ∀ (i m : ℕ), i < n → m < n →
      (qExpansion 1 (heckeTPₗ k Nat.prime_two (f i))).coeff (m + 1) = X2 i m)
    (M2 : Matrix (Fin n) (Fin n) ℤ)
    (hM2 : ∀ (i l : Fin n), coordN A (fun m => X2 i.val m) l.val = ((M2 l i : ℤ) : ℂ))
    (C : Matrix (Fin n) (Fin n) ℤ)
    (hcard : Matrix.of (fun i j : Fin n =>
      ∑ c : Fin n, millerCoeff a n j.val c.val * (M2 ^ (i : ℕ)) 0 c) = C)
    (I : ℤ) (hdet : C.det.natAbs = I.natAbs) :
    (t2Lattice (heckeTM k 2) n).toAddSubgroup.relIndex
        (heckeLattice k n).toAddSubgroup = I.natAbs := by
  rw [index_card_hecke hn hk hdim f A hzero hone hA hfi hmin a hAeq M2
    (heckeTM_two_rep_of_dimN hn hdim f A X2 hzero hone hA hX2 M2 hM2) C hcard, hdet]

/-- **The per-weight index card, quotient-cardinality phrasing** (the form
consumed as `hcard` downstream). -/
theorem index_card_natCard_dimN (hn : 0 < n) (hk : 1 ≤ k)
    (hdim : Module.finrank ℂ (CuspForm 𝒮ℒ k) = n)
    (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j)
    (hfi : ∀ i : ℕ, i < n → ∀ m : ℕ, ∃ z : ℤ, (qExpansion 1 (f i)).coeff m = (z : ℂ))
    (hmin : (minpoly ℂ (heckeTM k 2 : Module.End ℂ (CuspForm 𝒮ℒ k))).natDegree = n)
    (a : ℕ → ℕ → ℤ) (hAeq : ∀ i j : ℕ, i < j → j < n → A i j = ((a i j : ℤ) : ℂ))
    (X2 : ℕ → ℕ → ℂ)
    (hX2 : ∀ (i m : ℕ), i < n → m < n →
      (qExpansion 1 (heckeTPₗ k Nat.prime_two (f i))).coeff (m + 1) = X2 i m)
    (M2 : Matrix (Fin n) (Fin n) ℤ)
    (hM2 : ∀ (i l : Fin n), coordN A (fun m => X2 i.val m) l.val = ((M2 l i : ℤ) : ℂ))
    (C : Matrix (Fin n) (Fin n) ℤ)
    (hcard : Matrix.of (fun i j : Fin n =>
      ∑ c : Fin n, millerCoeff a n j.val c.val * (M2 ^ (i : ℕ)) 0 c) = C)
    (I : ℤ) (hdet : C.det.natAbs = I.natAbs) :
    Nat.card (↥(heckeLattice k n).toAddSubgroup ⧸
      (t2Lattice (heckeTM k 2) n).toAddSubgroup.addSubgroupOf
        (heckeLattice k n).toAddSubgroup) = I.natAbs := by
  rw [index_card_hecke_natCard hn hk hdim f A hzero hone hA hfi hmin a hAeq M2
    (heckeTM_two_rep_of_dimN hn hdim f A X2 hzero hone hA hX2 M2 hM2) C hcard, hdet]

end Assemble

end HeckeLatticeIndex
