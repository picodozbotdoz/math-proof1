import MathProof.ModularForms.HeckeIndex
import Mathlib.RingTheory.PowerBasis

/-!
# T-Rat: every `T_m` is a rational polynomial in `T₂`

The generic-`m` rationality theorem of the Hecke-field track (iteration 23,
b3): on a level-one `S_k` whose `T₂` has minimal polynomial of degree
`n = dim S_k` (Maeda irreducibility), for **every** `m ≥ 1`

    `∃ Q : ℚ[X], T_m = Q(T₂)`.

No per-`m` certificate is involved.  The route (all generic):

* `millerTop_int` / `miller_int` — the Miller basis of an echelon family with
  integer `q`-coefficients (all `m`) again has integer coefficients: the
  reduction table is read off the family itself (`hA`), so it is integral too;
* the powers `T₂^i` (`i < n`) lie in the Hecke lattice
  `𝕋 = span_ℤ {T_1, …, T_n}` (`HeckeIndex.T2_pow_mem_heckeRing`): an integer
  matrix `Z` with `T₂^i = ∑_j Z i j • T_{j+1}`;
* `Z` is invertible over `ℂ`: both families are independent of size `n`
  (`linearIndependent_pow`, `HeckeIndex.hecke_independent`), so their spans
  coincide and the coordinates of `T_{j+1}` in the powers give a left inverse;
* Cramer (`HeckeIndex.cramer_inverse`) gives
  `det Z • T_{j+1} = ∑_i adj(Z)_{ji} • T₂^i`, and duality
  (`HeckeIndex.hecke_dual`) with integer Miller coefficients assembles
  `det Z • T_m` as an integer combination of the powers; dividing by
  `det Z ≠ 0` is `HeckeIndex.aeval_div_witness`.

`heckeTM_eq_aeval_rat_of_echelon` packages the theorem on the echelon data
(`fb`, `Atab`, `hzero`, `hone`, `hA`) the per-weight files already carry.

Everything is light: no `set_option`, no `decide`.
-/

open Polynomial MaedaLevelOne HeckeTM HeckeIndex
open UpperHalfPlane ModularForm CuspForm
open scoped MatrixGroups

namespace HeckeFieldRat

variable {k : ℤ} {n : ℕ}

/-- Coefficients of a difference. -/
private lemma coeff_sub' (f g : CuspForm 𝒮ℒ k) (m : ℕ) :
    (qExpansion 1 ⇑(f - g)).coeff m
      = (qExpansion 1 ⇑f).coeff m - (qExpansion 1 ⇑g).coeff m := by
  have h1 : (qL k (f - g)).coeff m = (qL k f - qL k g).coeff m := by rw [map_sub]
  have h2 : (qL k f - qL k g).coeff m = (qL k f).coeff m - (qL k g).coeff m := by
    rw [map_sub]
  rw [← qL_apply (f - g), ← qL_apply f, ← qL_apply g, h1, h2]

/-! ### Integrality of the Miller basis -/

/-- Every row of the Miller accumulator has integer `q`-coefficients when the
echelon family does (all `m`). -/
theorem millerTop_int (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j)
    (hfi : ∀ i : ℕ, i < n → ∀ m : ℕ, ∃ z : ℤ, (qExpansion 1 (f i)).coeff m = (z : ℂ)) :
    ∀ r : ℕ, r ≤ n → ∀ t : ℕ, t < r → ∀ m : ℕ,
      ∃ z : ℤ, (qExpansion 1 ((millerTop f A n r).getD t 0)).coeff m = (z : ℂ) := by
  intro r
  induction r with
  | zero => intro _ t ht; exact absurd ht (Nat.not_lt_zero t)
  | succ r ih =>
    intro hr t ht m
    rcases t with _ | s
    · have hT : ∀ t : ℕ, ∃ z : ℤ, t < r →
          (qExpansion 1 ((millerTop f A n r).getD t 0)).coeff m = (z : ℂ) := by
        intro t
        by_cases htr : t < r
        · obtain ⟨z, hz⟩ := ih (by omega) t htr m
          exact ⟨z, fun _ => hz⟩
        · exact ⟨0, fun h => absurd h htr⟩
      have hAz : ∀ t : ℕ, ∃ z : ℤ, t < r → A (n - 1 - r) (t + (n - r)) = (z : ℂ) := by
        intro t
        by_cases htr : t < r
        · obtain ⟨z, hz⟩ := hfi (n - 1 - r) (by omega) (t + (n - r) + 1)
          refine ⟨z, fun _ => ?_⟩
          rw [← hA (n - 1 - r) (t + (n - r)) (by omega) (by omega), hz]
        · exact ⟨0, fun h => absurd h htr⟩
      choose zt hzt using hT
      choose zA hzA using hAz
      obtain ⟨zf, hzf⟩ := hfi (n - 1 - r) (by omega) m
      refine ⟨zf - ∑ t ∈ Finset.range r, zA t * zt t, ?_⟩
      rw [millerTop, List.getD_cons_zero, coeff_sub', coeff_sum, hzf]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun t ht => ?_
      have htr := Finset.mem_range.mp ht
      rw [hzA t htr, hzt t htr]
    · obtain ⟨z, hz⟩ := ih (by omega) s (by omega) m
      refine ⟨z, ?_⟩
      rw [millerTop, List.getD_cons_succ]
      exact hz

/-- **Integrality of the Miller basis**: integer echelon coefficients (all
`m`) give integer Miller coefficients (all `m`). -/
theorem miller_int (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j)
    (hfi : ∀ i : ℕ, i < n → ∀ m : ℕ, ∃ z : ℤ, (qExpansion 1 (f i)).coeff m = (z : ℂ))
    (j m : ℕ) (hj : j < n) :
    ∃ z : ℤ, (qExpansion 1 (miller f A n j)).coeff m = (z : ℂ) := by
  rw [miller]
  exact millerTop_int f A hA hfi (n - j) (by omega) 0 (by omega) m

/-! ### The rationality theorem -/

/-- **T-Rat (generic).**  With `g` a normalized basis of `S_k` with integer
coefficients, `k ≥ 1`, and `minpoly T₂` of degree `n = dim S_k`, every `T_m`
(`m ≥ 1`) is a rational polynomial in `T₂`. -/
theorem heckeTM_eq_aeval_rat (g : ℕ → CuspForm 𝒮ℒ k) (hn : 0 < n)
    (hg : LinearIndependent ℂ (fun i : Fin n => g i.val))
    (hdim : Module.finrank ℂ (CuspForm 𝒮ℒ k) = n)
    (hδ : ∀ j m : ℕ, j < n → m < n →
      (qExpansion 1 (g j)).coeff (m + 1) = if m = j then 1 else 0)
    (hint : ∀ j m : ℕ, j < n → ∃ z : ℤ, (qExpansion 1 (g j)).coeff m = (z : ℂ))
    (hk : 1 ≤ k) (hmin : (minpoly ℂ (heckeTM k 2)).natDegree = n)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ Q : ℚ[X], heckeTM k m = Polynomial.aeval (heckeTM k 2) (Q.map (algebraMap ℚ ℂ)) := by
  -- integer coordinates `Z` of the powers `T₂^i` over `T_1 … T_n`
  have hZ : ∀ i : Fin n, ∃ z : Fin n → ℤ,
      ∑ j, z j • heckeTM k (j.val + 1) = heckeTM k 2 ^ i.val := fun i =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp
      (T2_pow_mem_heckeRing g hn hg hdim hδ hint hk i.val)
  choose Z hZ using hZ
  let ZM : Matrix (Fin n) (Fin n) ℤ := Matrix.of Z
  have hP : ∀ i : Fin n, heckeTM k 2 ^ i.val
      = ∑ j : Fin n, ((ZM i j : ℤ) : ℂ) • heckeTM k (j.val + 1) := fun i => by
    rw [← hZ i]
    exact Finset.sum_congr rfl fun j _ => (Int.cast_smul_eq_zsmul ℂ _ _).symm
  -- both families are independent of size `n`, so their spans agree
  have hu : LinearIndependent ℂ (fun j : Fin n => heckeTM k (j.val + 1)) :=
    hecke_independent g hδ
  have hpw : LinearIndependent ℂ (fun i : Fin n => heckeTM k 2 ^ i.val) := by
    have h := linearIndependent_pow (K := ℂ) (heckeTM k 2)
    rw [hmin] at h
    exact h
  have hle : Submodule.span ℂ (Set.range fun i : Fin n => heckeTM k 2 ^ i.val)
      ≤ Submodule.span ℂ (Set.range fun j : Fin n => heckeTM k (j.val + 1)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change heckeTM k 2 ^ i.val ∈ _
    rw [hP i]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have heq : Submodule.span ℂ (Set.range fun i : Fin n => heckeTM k 2 ^ i.val)
      = Submodule.span ℂ (Set.range fun j : Fin n => heckeTM k (j.val + 1)) := by
    have : FiniteDimensional ℂ
        (Submodule.span ℂ (Set.range fun j : Fin n => heckeTM k (j.val + 1))) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    exact Submodule.eq_of_le_of_finrank_eq hle
      (by rw [finrank_span_eq_card hpw, finrank_span_eq_card hu])
  -- complex coordinates `c` of `T_{j+1}` over the powers: a left inverse of `Z`
  have hc : ∀ j : Fin n, ∃ c : Fin n → ℂ,
      ∑ i, c i • heckeTM k 2 ^ i.val = heckeTM k (j.val + 1) := fun j =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp
      (heq ▸ Submodule.subset_span ⟨j, rfl⟩)
  choose c hc using hc
  have hkey : ∀ j : Fin n, ∑ l : Fin n, (∑ i : Fin n, c j i * ((ZM i l : ℤ) : ℂ))
      • heckeTM k (l.val + 1) = heckeTM k (j.val + 1) := by
    intro j
    conv_rhs => rw [← hc j]
    simp_rw [hP, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hcz : (Matrix.of c) * (ZM.map (Int.cast : ℤ → ℂ)) = 1 := by
    ext j l
    have hrel : ∑ l' : Fin n, ((∑ i : Fin n, c j i * ((ZM i l' : ℤ) : ℂ))
        - (if l' = j then 1 else 0)) • heckeTM k (l'.val + 1) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [hkey j, sub_self]
    have h0 := Fintype.linearIndependent_iff.mp hu _ hrel l
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply, Matrix.map_apply]
    by_cases hlj : l = j
    · subst hlj
      rw [ite_eq_left rfl] at h0
      rw [ite_eq_left rfl]
      exact sub_eq_zero.mp h0
    · rw [ite_eq_right hlj, sub_zero] at h0
      rw [ite_eq_right (fun h => hlj h.symm)]
      exact h0
  have hdet : ((ZM.det : ℤ) : ℂ) ≠ 0 := by
    have hmap := RingHom.map_det (Int.castRingHom ℂ) ZM
    simp only [eq_intCast] at hmap
    rw [hmap]
    exact Matrix.det_ne_zero_of_left_inverse hcz
  -- assemble `det Z • T_m` over the powers
  have hw : ∀ j : Fin n, ∃ z : ℤ, (qExpansion 1 (g j.val)).coeff m = (z : ℂ) :=
    fun j => hint j.val m j.isLt
  choose w hw using hw
  let r : ℕ → ℤ := fun i =>
    if h : i < n then ∑ j : Fin n, w j * ZM.adjugate j ⟨i, h⟩ else 0
  have hsum : ((ZM.det : ℤ) : ℂ) • heckeTM k m
      = ∑ i ∈ Finset.range n, ((r i : ℤ) : ℂ) • heckeTM k 2 ^ i := by
    rw [hecke_dual g hn hg hdim hδ m hm, Finset.smul_sum]
    have hj : ∀ j : Fin n, ((ZM.det : ℤ) : ℂ)
        • ((qExpansion 1 (g j.val)).coeff m • heckeTM k (j.val + 1))
        = ∑ i : Fin n, ((w j * ZM.adjugate j i : ℤ) : ℂ) • heckeTM k 2 ^ i.val := by
      intro j
      rw [smul_comm, cramer_inverse (fun j : Fin n => heckeTM k (j.val + 1)) ZM
        (fun i : Fin n => heckeTM k 2 ^ i.val) hP j, hw j, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, ← Int.cast_mul]
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm,
      ← Fin.sum_univ_eq_sum_range (fun i => ((r i : ℤ) : ℂ) • heckeTM k 2 ^ i) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul, ← Int.cast_sum]
    simp only [r, dite_eq_left i.isLt, Fin.eta]
  exact ⟨_, aeval_div_witness (heckeTM k 2) (heckeTM k m) r ZM.det hdet hsum⟩

/-- **T-Rat on echelon data.**  The form the per-weight files consume: an
echelon basis `f` (the `charpoly_dimN` hypotheses) with integer coefficients
for all `m`, `dim S_k = n`, `k ≥ 1` and `minpoly T₂` of degree `n` give
`T_m ∈ ℚ[T₂]` for every `m ≥ 1`. -/
theorem heckeTM_eq_aeval_rat_of_echelon (hn : 0 < n)
    (hdim : Module.finrank ℂ (CuspForm 𝒮ℒ k) = n)
    (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j)
    (hfi : ∀ i : ℕ, i < n → ∀ m : ℕ, ∃ z : ℤ, (qExpansion 1 (f i)).coeff m = (z : ℂ))
    (hk : 1 ≤ k) (hmin : (minpoly ℂ (heckeTM k 2)).natDegree = n)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ Q : ℚ[X], heckeTM k m = Polynomial.aeval (heckeTM k 2) (Q.map (algebraMap ℚ ℂ)) :=
  heckeTM_eq_aeval_rat (miller f A n) hn (miller_linearIndependent f A hzero hone hA) hdim
    (fun j m hj hm => miller_coeff' f A hzero hone hA j m hj hm)
    (fun j m hj => miller_int f A hA hfi j m hj) hk hmin m hm

end HeckeFieldRat
