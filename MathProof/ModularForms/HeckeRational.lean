import MathProof.ModularForms.CharpolyDimN

/-!
# HeckeRational: rational polynomial witnesses for Hecke operators

The companion of `CharpolyDimN`: where `charpoly_dimN` extracts the
characteristic polynomial of an endomorphism from echelon q-coefficient
tables, this module extracts the *representation itself* and turns a
certified integer matrix identity into a **rational polynomial witness**.

* `linearIndependent_dimN` — the echelon family is linearly independent
  (leading-term argument, the elimination core of `charpoly_dimN`);
* `represents_dimN` — same echelon hypotheses as `charpoly_dimN`, but
  concluding `T (f i) = ∑ l, coordN A (X i) l • f l` (the matrix of `T` in
  the echelon basis, coordinate by coordinate);
* `exists_aeval_rat_of_rep` — module-generic: if `T₂`, `T₃` are represented
  by the integer matrices `M₂`, `M₃` on a basis-sized independent family,
  and the scaled identity `∑_{j<n} c j • M₂^j = D • M₃` holds over `ℤ`,
  then `T₃ = aeval T₂ (Q.map (algebraMap ℚ ℂ))` for the rational
  polynomial `Q = ∑ j < n, C (c j / D) * X ^ j` built inside the proof;
* `exists_aeval_rat_dimN` — the echelon-bundle form consumed by the
  generated per-weight files (`HeckeRationalWeights.lean`).

No commutativity hypothesis is needed: the scaled identity *is* the proof
that the two operators agree on the echelon basis, and the basis spans
(linear independence + `finrank` counting, as in `charpoly_dimN`).

This module is new infrastructure (the `HornerCert`/`MaedaCertC` pattern):
nothing here is an ancestor of the heavy `MaedaGalois5` chain.
-/

namespace MaedaLevelOne

open UpperHalfPlane ModularForm CuspForm Polynomial
open scoped MatrixGroups

/-! ### The echelon representation (sibling of `charpoly_dimN`) -/

/-- Splitting a range sum by the trichotomy against `m` (as in `CharpolyDimN`). -/
private lemma sum_range_split (F : ℕ → ℂ) :
    ∀ (m : ℕ) (e : ℕ → ℂ) (n : ℕ), m < n →
      (∑ x ∈ Finset.range n, (if x < m then F x else if x = m then e x else 0))
        = (∑ x ∈ Finset.range m, F x) + e m := by
  intro m
  induction m with
  | zero =>
      intro e n hn
      have hz : ∀ x : ℕ, (if x < 0 then F x else if x = 0 then e x else 0)
          = (if x = 0 then e x else 0) := fun x => by simp
      rw [Finset.sum_congr rfl fun x _ => hz x, Finset.sum_ite_eq' (Finset.range n) 0 e,
        ite_eq_left (Finset.mem_range.mpr hn), Finset.sum_range_zero, zero_add]
  | succ m ih =>
      intro e n hn
      show (∑ x ∈ Finset.range n, (if x < m + 1 then F x else if x = m + 1 then e x else 0))
          = (∑ x ∈ Finset.range (m + 1), F x) + e (m + 1)
      have hpt : ∀ x : ℕ, (if x < m + 1 then F x else if x = m + 1 then e x else 0)
          = (if x < m then F x else if x = m then F x else 0)
            + (if x = m + 1 then e x else 0) := by
        intro x
        rcases Nat.lt_trichotomy x (m + 1) with h | h | h
        · rcases Nat.lt_trichotomy x m with h2 | h2 | h2
          · rw [ite_eq_left h, ite_eq_left h2,
              ite_eq_right (show ¬(x = m + 1) from by omega)]
            ring
          · rw [ite_eq_left h, ite_eq_right (show ¬(x < m) from by omega),
              ite_eq_left (show x = m from h2),
              ite_eq_right (show ¬(x = m + 1) from by omega)]
            ring
          · exact (by omega : False).elim
        · rw [ite_eq_right (show ¬(x < m + 1) from by omega),
            ite_eq_left (show x = m + 1 from h),
            ite_eq_right (show ¬(x < m) from by omega),
            ite_eq_right (show ¬(x = m) from by omega)]
          ring
        · rw [ite_eq_right (show ¬(x < m + 1) from by omega),
            ite_eq_right (show ¬(x = m + 1) from by omega),
            ite_eq_right (show ¬(x < m) from by omega),
            ite_eq_right (show ¬(x = m) from by omega)]
          ring
      have hsumH := ih F n (by omega)
      simp only [hpt, Finset.sum_add_distrib]
      rw [hsumH, Finset.sum_ite_eq' (Finset.range n) (m + 1) e,
        ite_eq_left (Finset.mem_range.mpr hn), Finset.sum_range_succ]

/-- The coordinates of `g = ∑ γ l • f l` are the back-substitution of the
q-coefficients of `g` (the elimination core of `charpoly_dimN`, used there
only internally). -/
private lemma coord_eq_of_echelon {k : ℤ} {n : ℕ}
    (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j) :
    ∀ (g : CuspForm 𝒮ℒ k) (γ : Fin n → ℂ), (∑ l, γ l • f l.val) = g →
      ∀ j : Fin n, γ j = coordN A (fun p => (qExpansion 1 g).coeff (p + 1)) j.val := by
  have coefftri : ∀ (m : ℕ), m < n → ∀ l : Fin n, (qExpansion 1 (f l)).coeff (m + 1)
      = if (l : ℕ) < m then A l.val m else if (l : ℕ) = m then 1 else 0 := by
    intro m hm l
    rcases Nat.lt_trichotomy l.val m with h | h | h
    · rw [ite_eq_left h, hA l.val m h hm]
    · rw [ite_eq_right (show ¬((l : ℕ) < m) from by omega), ite_eq_left h, ← h]
      exact hone l.val (by omega)
    · rw [ite_eq_right (show ¬((l : ℕ) < m) from by omega),
        ite_eq_right (show ¬((l : ℕ) = m) from by omega),
        hzero l.val (m + 1) l.isLt (by omega) (by omega)]
  intro g γ hg
  set γd : ℕ → ℂ := fun x => if h : x < n then γ ⟨x, h⟩ else 0 with hγddef
  have hγd : ∀ x : ℕ, ∀ hx : x < n, γd x = γ ⟨x, hx⟩ := by
    intro x hx
    simp only [hγddef, dite_eq_left hx]
  have hgsum : ∀ m : ℕ, m < n → (qExpansion 1 g).coeff (m + 1)
      = (∑ x ∈ Finset.range m, A x m * γd x) + γd m := by
    intro m hm
    have heq := coeff_sum (Finset.univ (α := Fin n)) γ (fun i : Fin n => f i.val) (m + 1)
    rw [hg] at heq
    have hpt2 : ∀ l : Fin n,
        γ l * (qExpansion 1 (f l.val)).coeff (m + 1)
          = (if (l : ℕ) < m then A l.val m * γd l.val
             else if (l : ℕ) = m then γd l.val else 0) := by
      intro l
      rw [coefftri m hm l, hγd l.val l.isLt]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun l _ => hpt2 l] at heq
    rw [Fin.sum_univ_eq_sum_range
      (f := fun x => if x < m then A x m * γd x else if x = m then γd x else 0)] at heq
    rw [sum_range_split (fun x => A x m * γd x) m γd n hm] at heq
    exact heq
  have key : ∀ m : ℕ, ∀ j : Fin n, j.val ≤ m →
      γ j = coordN A (fun p => (qExpansion 1 g).coeff (p + 1)) j.val := by
    intro m
    induction m with
    | zero =>
        intro j hj0
        have hjv : j.val = 0 := by omega
        rw [hjv, coordN_zero, hgsum 0 (by omega), Finset.sum_range_zero, zero_add,
          hγd 0 (by omega)]
        exact congrArg γ (Fin.ext hjv)
    | succ m ih =>
        intro j hjm
        rcases Nat.lt_or_ge j.val (m + 1) with hj | hj
        · exact ih j (by omega)
        · have hjv : j.val = m + 1 := by omega
          have hjn : m + 1 < n := by rw [← hjv]; exact j.isLt
          rw [hjv, coordN_succ, hgsum (m + 1) hjn]
          have hsub : ∑ x ∈ Finset.range (m + 1),
              A x (m + 1) * coordN A (fun p => (qExpansion 1 g).coeff (p + 1)) x
              = ∑ x ∈ Finset.range (m + 1), A x (m + 1) * γd x := by
            refine Finset.sum_congr rfl fun x hx => ?_
            have hxlt : x < m + 1 := Finset.mem_range.mp hx
            have hxn : x < n := by omega
            have hxm : x ≤ m := by omega
            rw [← ih ⟨x, hxn⟩ hxm, hγd x hxn]
          rw [hsub, add_sub_cancel_left, hγd (m + 1) hjn]
          exact congrArg γ (Fin.ext hjv)
  intro j
  exact key j.val j (Nat.le_refl _)

/-- **Linear independence of the echelon family** (leading-term argument):
the extraction core behind `charpoly_dimN`, exported for the
representation route. -/
theorem linearIndependent_dimN {k : ℤ} {n : ℕ}
    (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j) :
    LinearIndependent ℂ (fun i : Fin n => f i.val) := by
  rw [Fintype.linearIndependent_iff]
  intro γ hγ j
  have h0 : (fun p => (qExpansion 1 (0 : CuspForm 𝒮ℒ k)).coeff (p + 1)) = fun _ => (0 : ℂ) := by
    funext p
    have hz : (qExpansion 1 (0 : CuspForm 𝒮ℒ k)) = 0 := by rw [← qL_apply, map_zero]
    rw [hz]
    simp
  rw [coord_eq_of_echelon f A hzero hone hA 0 γ hγ j, h0, coordN_zero_c]

/-- **The dimension-generic representation.**  Same echelon hypotheses as
`charpoly_dimN`: the action of any endomorphism `T` on the echelon family
is the back-substitution of the `T`-coefficient table — one column of the
matrix of `T`, read off coordinate by coordinate. -/
theorem represents_dimN {k : ℤ} {n : ℕ} (hn : 0 < n)
    (hdim : Module.finrank ℂ (CuspForm 𝒮ℒ k) = n)
    (f : ℕ → CuspForm 𝒮ℒ k) (A X : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j)
    (T : CuspForm 𝒮ℒ k →ₗ[ℂ] CuspForm 𝒮ℒ k)
    (hX : ∀ (i m : ℕ), i < n → m < n → (qExpansion 1 (T (f i))).coeff (m + 1) = X i m) :
    ∀ i : Fin n, T (f i.val)
      = ∑ l : Fin n, coordN A (fun m => X i.val m) l.val • f l.val := by
  intro i
  have hli := linearIndependent_dimN f A hzero hone hA
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcard : Fintype.card (Fin n) = Module.finrank ℂ (CuspForm 𝒮ℒ k) := by simp [hdim]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ∀ l : Fin n, b l = f l.val := by
    intro l
    simp [b]
  have hg' : (∑ l, b.repr (T (f i.val)) l • f l.val) = T (f i.val) :=
    (Finset.sum_congr rfl fun l _ => by rw [hb l]).trans (b.sum_repr (T (f i.val)))
  calc T (f i.val) = ∑ l : Fin n, b.repr (T (f i.val)) l • f l.val := hg'.symm
    _ = ∑ l : Fin n, coordN A (fun m => X i.val m) l.val • f l.val := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [coord_eq_of_echelon f A hzero hone hA (T (f i.val)) (b.repr (T (f i.val))) hg' l,
          coordN_congr l.val fun p hp => hX i.val p i.isLt (by omega)]

/-! ### From representations to the rational witness -/

section Witness

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

/-- The rational witness `∑_{j<n} C (c j / D) * X ^ j`. -/
private noncomputable def ratWitness (c : ℕ → ℤ) (D : ℤ) : ℚ[X] :=
  ∑ j ∈ Finset.range n, C (((c j : ℤ) : ℚ) / ((D : ℤ) : ℚ)) * (X : ℚ[X]) ^ j

/-- Powers of `T₂` act by powers of its matrix, on the represented family. -/
private lemma pow_rep (T2 : V →ₗ[ℂ] V) (M2 : Matrix (Fin n) (Fin n) ℤ) (f : ℕ → V)
    (hrep2 : ∀ i : Fin n, T2 (f i.val) = ∑ l : Fin n, ((M2 l i : ℤ) : ℂ) • f l.val) :
    ∀ (j : ℕ) (i : Fin n), (T2 ^ j) (f i.val)
      = ∑ l : Fin n, (((M2 ^ j) l i : ℤ) : ℂ) • f l.val := by
  intro j
  induction j with
  | zero =>
      intro i
      rw [pow_zero, Module.End.one_apply]
      have hzeroM : ∀ l : Fin n, (((M2 ^ (0 : ℕ)) l i : ℤ) : ℂ) = if l = i then 1 else 0 := by
        intro l
        have h1 : ((M2 ^ (0 : ℕ)) l i : ℤ) = if l = i then 1 else 0 := by
          rw [pow_zero]
          exact Matrix.one_apply
        rw [h1]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl fun l _ => by rw [hzeroM l]]
      have hone : ((if i = i then (1 : ℂ) else 0) • f ↑i.val) = f ↑i.val := by simp
      rw [← hone]
      exact (Finset.sum_eq_single (f := fun l => (if l = i then (1 : ℂ) else 0) • f l.val) i
        (fun l _ hl => by rw [ite_eq_right hl, zero_smul])
        (fun hl => absurd (Finset.mem_univ i) hl)).symm
  | succ j ih =>
      intro i
      rw [pow_succ, Module.End.mul_apply, hrep2 i, map_sum,
        Finset.sum_congr rfl fun l _ => by
          rw [map_smul, ih l, Finset.smul_sum, Finset.sum_congr rfl fun t _ => by
              rw [smul_smul]],
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      have hcast : (((∑ x : Fin n, (M2 ^ j) y x * M2 x i : ℤ)) : ℂ)
          = ∑ x : Fin n, (((M2 ^ j) y x * M2 x i : ℤ) : ℂ) := Int.cast_sum _ _
      have hfold : (∑ x : Fin n, (((M2 ^ j) y x * M2 x i : ℤ) : ℂ)) • f ↑y
          = ∑ x : Fin n, ((((M2 ^ j) y x * M2 x i : ℤ) : ℂ)) • f ↑y :=
        Finset.sum_smul
      have h1 : ∑ x : Fin n, (((M2 x i : ℤ) : ℂ) * (((M2 ^ j) y x : ℤ) : ℂ)) • f ↑y
          = (((∑ x : Fin n, (M2 ^ j) y x * M2 x i : ℤ)) : ℂ) • f ↑y := by
        rw [hcast, hfold]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Int.cast_mul, mul_comm]
      rw [h1, pow_succ, Matrix.mul_apply]

/-- The witness evaluates on the family as the (divided) scaled identity. -/
private lemma aeval_ratWitness_apply (T2 : V →ₗ[ℂ] V) (M2 : Matrix (Fin n) (Fin n) ℤ)
    (f : ℕ → V)
    (hpow : ∀ (j : ℕ) (i : Fin n), (T2 ^ j) (f i.val)
      = ∑ l : Fin n, (((M2 ^ j) l i : ℤ) : ℂ) • f l.val)
    (c : ℕ → ℤ) (D : ℤ) (i : Fin n) :
    (Polynomial.aeval T2 ((ratWitness (n := n) c D).map (algebraMap ℚ ℂ))) (f i.val)
      = ∑ l : Fin n, ((((D : ℤ) : ℂ))⁻¹ *
            (((∑ j ∈ Finset.range n, c j * (M2 ^ j) l i) : ℤ) : ℂ)) • f l.val := by
  have hmap : (ratWitness (n := n) c D).map (algebraMap ℚ ℂ)
      = ∑ j ∈ Finset.range n, C (algebraMap ℚ ℂ
          (((c j : ℤ) : ℚ) / ((D : ℤ) : ℚ))) * (X : ℂ[X]) ^ j := by
    simp only [ratWitness, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  have hcoef : ∀ l : Fin n,
      ∑ j ∈ Finset.range n, (algebraMap ℚ ℂ (((c j : ℤ) : ℚ) / ((D : ℤ) : ℚ))) *
          (((M2 ^ j) l i : ℤ) : ℂ)
        = (((D : ℤ) : ℂ))⁻¹ * (((∑ j ∈ Finset.range n, c j * (M2 ^ j) l i) : ℤ) : ℂ) := by
    intro l
    have h0 : ∀ j ∈ Finset.range n,
        (algebraMap ℚ ℂ (((c j : ℤ) : ℚ) / ((D : ℤ) : ℚ)))
          = (((D : ℤ) : ℂ))⁻¹ * ((c j : ℤ) : ℂ) := by
      intro j _
      rw [map_div₀, map_intCast, map_intCast, div_eq_inv_mul, mul_comm]
    have hcast : (((∑ j ∈ Finset.range n, c j * (M2 ^ j) l i) : ℤ) : ℂ)
        = ∑ j ∈ Finset.range n, ((c j * (M2 ^ j) l i : ℤ) : ℂ) := Int.cast_sum _ _
    have hmulsum : (((D : ℤ) : ℂ))⁻¹ * ∑ j ∈ Finset.range n, ((c j * (M2 ^ j) l i : ℤ) : ℂ)
        = ∑ j ∈ Finset.range n, (((D : ℤ) : ℂ))⁻¹ * ((c j * (M2 ^ j) l i : ℤ) : ℂ) :=
      Finset.mul_sum _ _ _
    have hmul : ∀ j : ℕ, ((c j * (M2 ^ j) l i : ℤ) : ℂ)
        = ((c j : ℤ) : ℂ) * (((M2 ^ j) l i : ℤ) : ℂ) := fun j => Int.cast_mul _ _
    rw [Finset.sum_congr rfl fun j hj => by rw [h0 j hj, mul_assoc], hcast, hmulsum]
    exact Finset.sum_congr rfl fun j _ => by rw [hmul j]
  rw [hmap, map_sum, LinearMap.sum_apply]
  have hterm : ∀ j ∈ Finset.range n,
      (Polynomial.aeval T2 (C (algebraMap ℚ ℂ
          (((c j : ℤ) : ℚ) / ((D : ℤ) : ℚ))) * (X : ℂ[X]) ^ j)) (f i.val)
        = (algebraMap ℚ ℂ (((c j : ℤ) : ℚ) / ((D : ℤ) : ℚ))) • ((T2 ^ j) (f i.val)) := by
    intro j _
    rw [map_mul, Module.End.mul_apply, aeval_X_pow, aeval_C,
      Module.algebraMap_end_apply]
  rw [Finset.sum_congr rfl fun j hj => by rw [hterm j hj, hpow j i],
    Finset.sum_congr rfl fun j _ => by
      rw [Finset.smul_sum, Finset.sum_congr rfl fun l _ => by rw [smul_smul]],
    Finset.sum_comm, Finset.sum_congr rfl fun l _ => by rw [← Finset.sum_smul]]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hcoef l]

/-- **The rational witness theorem.**  If `T₂`, `T₃` act by the integer
matrices `M₂`, `M₃` on an independent family of `finrank` vectors, and the
scaled identity `∑_{j<n} c j • M₂^j = D • M₃` holds with `D ≠ 0` in `ℂ`,
then `T₃` is a polynomial in `T₂` with **rational** coefficients. -/
theorem exists_aeval_rat_of_rep (hn : 0 < n)
    (hdim : Module.finrank ℂ V = n)
    (f : ℕ → V)
    (hli : LinearIndependent ℂ (fun i : Fin n => f i.val))
    (T2 T3 : V →ₗ[ℂ] V)
    (M2 M3 : Matrix (Fin n) (Fin n) ℤ)
    (hrep2 : ∀ i : Fin n, T2 (f i.val) = ∑ l : Fin n, ((M2 l i : ℤ) : ℂ) • f l.val)
    (hrep3 : ∀ i : Fin n, T3 (f i.val) = ∑ l : Fin n, ((M3 l i : ℤ) : ℂ) • f l.val)
    (c : ℕ → ℤ) (D : ℤ) (hD : ((D : ℤ) : ℂ) ≠ 0)
    (hid : ∑ j ∈ Finset.range n, c j • M2 ^ j = D • M3) :
    ∃ Q : ℚ[X], T3 = Polynomial.aeval T2 (Q.map (algebraMap ℚ ℂ)) := by
  have hpow := pow_rep T2 M2 f hrep2
  have hide : ∀ l i : Fin n, (∑ j ∈ Finset.range n, c j * (M2 ^ j) l i) = D * M3 l i := by
    intro l i
    have h := congrArg (fun X : Matrix (Fin n) (Fin n) ℤ => X l i) hid
    rw [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_apply, smul_eq_mul]] at h
    exact h
  have hcard : Fintype.card (Fin n) = Module.finrank ℂ V := by simp [hdim]
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ∀ l : Fin n, b l = f l.val := by
    intro l
    simp [b]
  have key : ∀ l : Fin n,
      (Polynomial.aeval T2 ((ratWitness (n := n) c D).map (algebraMap ℚ ℂ))) (f l.val)
        = T3 (f l.val) := by
    intro l
    rw [aeval_ratWitness_apply T2 M2 f hpow c D l, hrep3 l]
    refine Finset.sum_congr rfl fun row _ => ?_
    rw [hide row l, Int.cast_mul, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  refine ⟨ratWitness (n := n) c D, LinearMap.ext fun x => ?_⟩
  have step : ∀ (G : V →ₗ[ℂ] V),
      G x = ∑ l : Fin n, (b.repr x) l • G (f l.val) := by
    intro G
    have hrepr := b.sum_repr x
    calc G x = G (∑ l : Fin n, (b.repr x) l • b l) := by rw [hrepr]
      _ = ∑ l : Fin n, (b.repr x) l • G (b l) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun l _ => by rw [map_smul]
      _ = ∑ l : Fin n, (b.repr x) l • G (f l.val) :=
          Finset.sum_congr rfl fun l _ => by rw [hb l]
  rw [step T3, step _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [key l]

end Witness

/-- **`T₃ ∈ ℚ[T₂]`, dimension-generic form.**  For an echelon family `f` of
`S_k` (the `charpoly_dimN` hypotheses) on which `T₂` and `T₃` act by the
integer matrices `M₂` and `M₃` (pinned entrywise through `coordN` by `hM2`,
`hM3`), any exact certificate `∑_{j<n} c j • M₂^j = D • M₃` over `ℤ` with
`D ≠ 0` yields a rational polynomial `Q` with
`T₃ = aeval T₂ (Q.map (algebraMap ℚ ℂ))`.  No commutativity input: the
certificate is the proof. -/
theorem exists_aeval_rat_dimN {k : ℤ} {n : ℕ} (hn : 0 < n)
    (hdim : Module.finrank ℂ (CuspForm 𝒮ℒ k) = n)
    (f : ℕ → CuspForm 𝒮ℒ k) (A X2 X3 : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j)
    (T2 T3 : CuspForm 𝒮ℒ k →ₗ[ℂ] CuspForm 𝒮ℒ k)
    (hX2 : ∀ (i m : ℕ), i < n → m < n → (qExpansion 1 (T2 (f i))).coeff (m + 1) = X2 i m)
    (hX3 : ∀ (i m : ℕ), i < n → m < n → (qExpansion 1 (T3 (f i))).coeff (m + 1) = X3 i m)
    (M2 M3 : Matrix (Fin n) (Fin n) ℤ)
    (hM2 : ∀ (i l : Fin n), coordN A (fun m => X2 i.val m) l.val = ((M2 l i : ℤ) : ℂ))
    (hM3 : ∀ (i l : Fin n), coordN A (fun m => X3 i.val m) l.val = ((M3 l i : ℤ) : ℂ))
    (c : ℕ → ℤ) (D : ℤ) (hD : ((D : ℤ) : ℂ) ≠ 0)
    (hid : ∑ j ∈ Finset.range n, c j • M2 ^ j = D • M3) :
    ∃ Q : ℚ[X], T3 = Polynomial.aeval T2 (Q.map (algebraMap ℚ ℂ)) := by
  have hrep2 : ∀ i : Fin n, T2 (f i.val)
      = ∑ l : Fin n, ((M2 l i : ℤ) : ℂ) • f l.val := by
    intro i
    rw [represents_dimN hn hdim f A X2 hzero hone hA T2 hX2 i]
    exact Finset.sum_congr rfl fun l _ => by rw [hM2 i l]
  have hrep3 : ∀ i : Fin n, T3 (f i.val)
      = ∑ l : Fin n, ((M3 l i : ℤ) : ℂ) • f l.val := by
    intro i
    rw [represents_dimN hn hdim f A X3 hzero hone hA T3 hX3 i]
    exact Finset.sum_congr rfl fun l _ => by rw [hM3 i l]
  exact exists_aeval_rat_of_rep hn hdim f
    (linearIndependent_dimN f A hzero hone hA) T2 T3 M2 M3 hrep2 hrep3 c D hD hid

end MaedaLevelOne
