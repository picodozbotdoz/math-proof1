import MathProof.ModularForms.HeckeRational

/-!
# HeckeIndex: the Miller basis, Cramer certificates, and reduced denominators

Generic infrastructure for the Hecke-index formalization (iteration 23, b2):
the index `[𝕋 : ℤ[T₂]] = |det (a_{2^i}(f_j))|` of the Hecke ring 𝕋 over the
polynomial ring `ℤ[T₂]`.  This first half is independent of the `HeckeTM`
calculus (b1): everything is built from the landed prime theory
(`HeckeRational`) plus new weight-generic lemmas.

* `millerTop` / `miller` — the **Miller basis** of an echelon family: the
  unit-triangular reduction `g j = f j − ∑_{j < i < n} A j i • g i`, built as
  a top-down structural recursion over an accumulator list (the `coordsAux`
  pattern, prepending).  `miller_coeff'` is the normalization
  `a_{m+1}(g j) = δ_{mj}` for `m, j < n`; `miller_linearIndependent` makes the
  Miller family a basis-sized independent family.  The module is analytic —
  nothing here is kernel-decided, so the `List.getD` bookkeeping is purely
  proof-side.
* `pow_rep` — powers of an operator act by powers of its matrix (the
  certificate glue; `HeckeRational.pow_rep` is private, so it is re-proved
  here once, publicly).
* `int_poly_of_rep` / `int_poly_of_dimN` — the **integer Cramer certificate**:
  if `T₂`, `T₃` act by the integer matrices `M₂`, `M₃` on an independent
  family and `∑_i w i • M₂^i = I • M₃` holds over ℤ, then
  `∑_i w i • T₂^i = I • T₃` as operators.  Per weight this is decided
  entrywise on the landed fb-coordinate literals (the operator identity is
  basis-independent).
* `cramer_scale` — the abstract Cramer inversion `C.det • S =
  ∑_i (∑_k v k * adj C k i) • P i` for families expanding with integer
  coordinates over a common family (pure algebra, no independence needed).
* `aeval_inj_of_minpoly` — polynomial representatives of degree `< n` are
  unique when the minimal polynomial has degree `n` (via `minpoly.dvd`).
* `den_dvd_index` — the **reduced-denominator divisibility**: if the witness
  `∑ N_j X^j / D` (reduced, certified by a Bézout combination
  `∑ e_j N_j + c D = 1`) and the new certificate `∑ w_j X^j / I_k` represent
  the same operator, then `D ∣ I_k`.

Nothing here is an ancestor of the heavy `MaedaGalois5` chain.
-/

namespace HeckeIndex

open MaedaLevelOne Polynomial
open UpperHalfPlane ModularForm CuspForm
open scoped MatrixGroups

/-! ### Coefficient helpers -/

/-- Coefficients of a difference (the `coeff_sum` companion). -/
private lemma coeff_sub {k : ℤ} (f g : CuspForm 𝒮ℒ k) (m : ℕ) :
    (qExpansion 1 ⇑(f - g)).coeff m
      = (qExpansion 1 ⇑f).coeff m - (qExpansion 1 ⇑g).coeff m := by
  have h1 : (qL k (f - g)).coeff m
      = (qL k f - qL k g).coeff m := by rw [map_sub]
  have h2 : (qL k f - qL k g).coeff m = (qL k f).coeff m - (qL k g).coeff m := by
    rw [map_sub]
  rw [← qL_apply (f - g), ← qL_apply f, ← qL_apply g, h1, h2]

/-- The coefficient trichotomy of an echelon family: below the leading term
zero, on it one, above it the `A`-table entry. -/
private lemma echelon_coeff {k : ℤ} {n : ℕ} (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j)
    (i m : ℕ) (hi : i < n) (hm : m < n) :
    (qExpansion 1 (f i)).coeff (m + 1)
      = if m = i then 1 else if m < i then 0 else A i m := by
  rcases Nat.lt_trichotomy m i with h | h | h
  · rw [ite_eq_right (by omega), ite_eq_left h, hzero i (m + 1) hi (by omega) (by omega)]
  · subst h
    rw [ite_eq_left rfl, hone m hi]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), hA i m h hm]

/-! ### The Miller basis -/

section Miller

variable {k : ℤ}

/-- The Miller rows, top-down accumulator: `millerTop f A n r` is the list
`[g_{n−r}, …, g_{n−1}]` (position `t` holds `g_{t + (n − r)}`), where each
`g i` reduces `f i` against the already-built rows above it:
`g i = f i − ∑_{i < i' < n} A i i' • g i'`.  Structural on the accumulator
length (the `coordsAux` pattern, prepending); nothing here is kernel-decided.
-/
noncomputable def millerTop (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ) (n : ℕ) :
    ℕ → List (CuspForm 𝒮ℒ k)
  | 0 => []
  | r + 1 =>
      (f (n - 1 - r)
          - ∑ t ∈ Finset.range r, A (n - 1 - r) (t + (n - r))
              • (millerTop f A n r).getD t 0) :: millerTop f A n r

lemma millerTop_length (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ) (n : ℕ) :
    ∀ r : ℕ, (millerTop f A n r).length = r := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
      change ((f (n - 1 - r)
          - ∑ t ∈ Finset.range r, A (n - 1 - r) (t + (n - r))
              • (millerTop f A n r).getD t 0) :: millerTop f A n r).length = r + 1
      rw [List.length_cons, ih]

/-- **The Miller vector at index `j`** (zero for `j ≥ n`): the head of the
accumulator stopped at `n − j`, i.e. `g j` freshly prepended. -/
noncomputable def miller (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ) (n : ℕ) (j : ℕ) :
    CuspForm 𝒮ℒ k := (millerTop f A n (n - j)).getD 0 0

lemma miller_eq_zero_of_ge (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ) (n : ℕ) {j : ℕ}
    (hj : n ≤ j) : miller f A n j = 0 := by
  rw [miller, Nat.sub_eq_zero_of_le hj]
  rfl

/-- Position-to-index translation inside the accumulator: position `t` of
`millerTop f A n r` is `miller f A n (t + (n − r))`. -/
lemma millerTop_getD (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ) (n : ℕ) :
    ∀ (r t : ℕ), t < r → r ≤ n →
      (millerTop f A n r).getD t 0 = miller f A n (t + (n - r)) := by
  intro r
  induction r with
  | zero => intro t ht; exact absurd ht (Nat.not_lt_zero t)
  | succ r ih =>
      intro t ht hr
      change ((f (n - 1 - r)
          - ∑ s ∈ Finset.range r, A (n - 1 - r) (s + (n - r))
              • (millerTop f A n r).getD s 0) :: millerTop f A n r).getD t 0
        = miller f A n (t + (n - (r + 1)))
      cases t with
      | zero =>
          have hn : n - (0 + (n - (r + 1))) = r + 1 := by omega
          rw [List.getD_cons_zero, miller, hn]
          rfl
      | succ s =>
          rw [List.getD_cons_succ, ih s (by omega) (by omega)]
          have he : s + 1 + (n - (r + 1)) = s + (n - r) := by omega
          rw [he]

/-- The defining recurrence of the Miller vector: `g j` is `f j` reduced
against the rows above it. -/
lemma miller_of_lt (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ) (n : ℕ) {j : ℕ}
    (hj : j < n) : miller f A n j
      = f j - ∑ t ∈ Finset.range (n - 1 - j), A j (t + (j + 1))
          • miller f A n (t + (j + 1)) := by
  have h1 : n - 1 - (n - 1 - j) = j := by omega
  have h2 : n - (n - 1 - j) = j + 1 := by omega
  rw [miller, show n - j = (n - 1 - j) + 1 from by omega]
  change ((f (n - 1 - (n - 1 - j))
      - ∑ t ∈ Finset.range (n - 1 - j), A (n - 1 - (n - 1 - j)) (t + (n - (n - 1 - j)))
          • (millerTop f A n (n - 1 - j)).getD t 0)
      :: millerTop f A n (n - 1 - j)).getD 0 0 = _
  rw [List.getD_cons_zero, h1, h2]
  refine congrArg (fun x => f j - x) ?_
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [millerTop_getD f A n (n - 1 - j) t (Finset.mem_range.mp ht) (by omega), h2]

/-- **The Miller normalization** (accumulator form): for an echelon family
`f` (the `charpoly_dimN` hypotheses), position `t` of `millerTop f A n r`
has coefficient `δ` at `q^{m+1}` — the unit-triangular reduction kills every
in-range coefficient above the leading term. -/
theorem miller_coeff {k : ℤ} {n : ℕ} (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j) :
    ∀ (r : ℕ), r ≤ n → ∀ (t : ℕ), t < r → ∀ (m : ℕ), m < n →
      (qExpansion 1 ((millerTop f A n r).getD t 0)).coeff (m + 1)
        = if m = t + (n - r) then 1 else 0 := by
  intro r
  induction r with
  | zero => intro _ t ht; exact absurd ht (Nat.not_lt_zero t)
  | succ r ih =>
      intro hr t ht m hm
      change (qExpansion 1 (((f (n - 1 - r)
          - ∑ s ∈ Finset.range r, A (n - 1 - r) (s + (n - r))
              • (millerTop f A n r).getD s 0) :: millerTop f A n r).getD t 0)).coeff (m + 1)
        = if m = t + (n - (r + 1)) then 1 else 0
      rcases Nat.eq_zero_or_pos t with ht0 | ht0
      · -- the fresh head: the three-case coefficient computation
          subst ht0
          have heq0 : (0 : ℕ) + (n - (r + 1)) = n - 1 - r := by omega
          rw [heq0]
          have hin : n - 1 - r < n := by omega
          have hsum : (qExpansion 1 ⇑(∑ s ∈ Finset.range r,
              A (n - 1 - r) (s + (n - r)) • (millerTop f A n r).getD s 0)).coeff (m + 1)
              = ∑ s ∈ Finset.range r, A (n - 1 - r) (s + (n - r))
                  * (qExpansion 1 ((millerTop f A n r).getD s 0)).coeff (m + 1) := by
            rw [coeff_sum]
          have hY : ∀ s ∈ Finset.range r,
              (qExpansion 1 ((millerTop f A n r).getD s 0)).coeff (m + 1)
                = if m = s + (n - r) then (1 : ℂ) else 0 := fun s hs =>
            ih (by omega) s (Finset.mem_range.mp hs) m hm
          rw [List.getD_cons_zero, coeff_sub, hsum,
            Finset.sum_congr rfl fun s hs => by rw [hY s hs]]
          have hX : (qExpansion 1 (f (n - 1 - r))).coeff (m + 1)
              = if m = n - 1 - r then (1 : ℂ) else
                  if m < n - 1 - r then 0 else A (n - 1 - r) m :=
            echelon_coeff f A hzero hone hA (n - 1 - r) m hin hm
          by_cases hmi : m = n - 1 - r
          · -- no `s` matches: `m = n - 1 - r < n - r ≤ s + (n - r)`
              have hno : ∀ s ∈ Finset.range r, A (n - 1 - r) (s + (n - r))
                  * (if m = s + (n - r) then (1 : ℂ) else 0) = 0 := by
                intro s hs
                rw [ite_eq_right (by omega), mul_zero]
              rw [Finset.sum_congr rfl hno, Finset.sum_const_zero, sub_zero, hX,
                ite_eq_left hmi, ite_eq_left hmi]
          · rcases Nat.lt_or_ge m (n - 1 - r) with hlt | hge
            · -- below the leading term: nothing matches either
                have hno : ∀ s ∈ Finset.range r, A (n - 1 - r) (s + (n - r))
                    * (if m = s + (n - r) then (1 : ℂ) else 0) = 0 := by
                  intro s hs
                  rw [ite_eq_right (by omega), mul_zero]
                rw [Finset.sum_congr rfl hno, Finset.sum_const_zero, sub_zero, hX,
                  ite_eq_right hmi, ite_eq_left hlt, ite_eq_right (by omega)]
            · -- above it: exactly the `s = m - (n - r)` term matches
                have hmge : n - 1 - r < m := by omega
                have hX2 : (qExpansion 1 (f (n - 1 - r))).coeff (m + 1)
                    = A (n - 1 - r) m := by
                  rw [hX, ite_eq_right hmi, ite_eq_right (by omega)]
                have hsingle : ∑ s ∈ Finset.range r, A (n - 1 - r) (s + (n - r))
                    * (if m = s + (n - r) then (1 : ℂ) else 0) = A (n - 1 - r) m := by
                  rw [Finset.sum_eq_single (m - (n - r))]
                  · rw [ite_eq_left (by omega), mul_one,
                      show m - (n - r) + (n - r) = m from by omega]
                  · intro b _ hb
                    rw [ite_eq_right (by omega), mul_zero]
                  · intro hnr
                    exact absurd (Finset.mem_range.mpr (by omega)) hnr
                rw [hsingle, hX2, sub_self, ite_eq_right (by omega)]
      · -- an older entry: the induction hypothesis, indices shifted
          obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
          rw [List.getD_cons_succ, ih (by omega) s (by omega) m hm]
          have he : s + 1 + (n - (r + 1)) = s + (n - r) := by omega
          rw [he]

/-- **The Miller normalization, indexed by `miller`.** -/
theorem miller_coeff' {k : ℤ} {n : ℕ}
    (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j) :
    ∀ (j m : ℕ), j < n → m < n →
      (qExpansion 1 (miller f A n j)).coeff (m + 1) = if m = j then 1 else 0 := by
  intro j m hj hm
  rw [miller, miller_coeff f A hzero hone hA (n - j) (by omega) 0 (by omega) m hm]
  rw [show (0 : ℕ) + (n - (n - j)) = j from by omega]

/-- **Linear independence of the Miller family** (one line from the
normalization: a vanishing combination has all coefficients read off the
`q^{m+1}`-coefficients). -/
theorem miller_linearIndependent {k : ℤ} {n : ℕ}
    (f : ℕ → CuspForm 𝒮ℒ k) (A : ℕ → ℕ → ℂ)
    (hzero : ∀ (i m : ℕ), i < n → 1 ≤ m → m ≤ i → (qExpansion 1 (f i)).coeff m = 0)
    (hone : ∀ i : ℕ, i < n → (qExpansion 1 (f i)).coeff (i + 1) = 1)
    (hA : ∀ (i j : ℕ), i < j → j < n → (qExpansion 1 (f i)).coeff (j + 1) = A i j) :
    LinearIndependent ℂ (fun i : Fin n => miller f A n i.val) := by
  rw [Fintype.linearIndependent_iff]
  intro γ hγ j
  have hzq : (qExpansion 1 (0 : CuspForm 𝒮ℒ k)) = 0 := by rw [← qL_apply, map_zero]
  have hc := coeff_sum (Finset.univ (α := Fin n)) γ
    (fun i : Fin n => miller f A n i.val) (j.val + 1)
  rw [hγ] at hc
  have hzc : (qExpansion 1 ⇑(0 : CuspForm 𝒮ℒ k)).coeff (j.val + 1) = (0 : ℂ) := by
    rw [← qL_apply (0 : CuspForm 𝒮ℒ k), map_zero]
    simp
  rw [hzc] at hc
  have hterm : ∀ i : Fin n,
      γ i * (qExpansion 1 (miller f A n i.val)).coeff (j.val + 1)
        = (if i = j then γ i else 0) := by
    intro i
    rw [miller_coeff' f A hzero hone hA i.val j.val i.isLt j.isLt]
    by_cases h : i = j
    · subst h
      simp
    · rw [ite_eq_right h]
      have hv : j.val ≠ i.val := fun hh => h (Fin.val_inj.mp hh.symm)
      rw [ite_eq_right hv, mul_zero]
  rw [Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_ite_eq' Finset.univ j (fun i => γ i),
    ite_eq_left (Finset.mem_univ j)] at hc
  exact hc.symm

end Miller

/-! ### The integer Cramer certificate on a represented family -/

section Rep

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

/-- Powers of `T₂` act by powers of its matrix, on the represented family
(public twin of `HeckeRational`'s private `pow_rep`). -/
theorem pow_rep (T2 : V →ₗ[ℂ] V) (M2 : Matrix (Fin n) (Fin n) ℤ) (f : ℕ → V)
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

/-- **The integer Cramer certificate.**  If `T₂`, `T₃` act by the integer
matrices `M₂`, `M₃` on an independent family of `finrank` vectors, and the
scaled identity `∑_{j<n} w j • M₂^j = I • M₃` holds over `ℤ`, then
`∑_{j<n} w j • T₂^j = I • T₃` as operators — with `I = |det|`, this is
`I • T₃ ∈ ℤ[T₂]` written out. -/
theorem int_poly_of_rep (hn : 0 < n)
    (hdim : Module.finrank ℂ V = n)
    (f : ℕ → V)
    (hli : LinearIndependent ℂ (fun i : Fin n => f i.val))
    (T2 T3 : V →ₗ[ℂ] V)
    (M2 M3 : Matrix (Fin n) (Fin n) ℤ)
    (hrep2 : ∀ i : Fin n, T2 (f i.val) = ∑ l : Fin n, ((M2 l i : ℤ) : ℂ) • f l.val)
    (hrep3 : ∀ i : Fin n, T3 (f i.val) = ∑ l : Fin n, ((M3 l i : ℤ) : ℂ) • f l.val)
    (w : ℕ → ℤ) (I : ℤ)
    (hid : ∑ j ∈ Finset.range n, w j • M2 ^ j = I • M3) :
    ∑ j ∈ Finset.range n, ((w j : ℤ) : ℂ) • T2 ^ j = ((I : ℤ) : ℂ) • T3 := by
  have hpow := pow_rep T2 M2 f hrep2
  have hide : ∀ l i : Fin n, (∑ j ∈ Finset.range n, w j * (M2 ^ j) l i) = I * M3 l i := by
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
  have key : ∀ l : Fin n, (∑ j ∈ Finset.range n, ((w j : ℤ) : ℂ) • T2 ^ j) (f l.val)
      = ((I : ℤ) : ℂ) • T3 (f l.val) := by
    intro l
    rw [LinearMap.sum_apply]
    have hstep : ∀ j ∈ Finset.range n, (((w j : ℤ) : ℂ) • T2 ^ j) (f l.val)
        = ∑ row : Fin n, (((w j * (M2 ^ j) row l : ℤ)) : ℂ) • f row.val := by
      intro j _
      rw [LinearMap.smul_apply, hpow j l, Finset.smul_sum]
      exact Finset.sum_congr rfl fun row _ => by rw [smul_smul, ← Int.cast_mul]
    rw [Finset.sum_congr rfl fun j hj => hstep j hj]
    have hswap : ∑ j ∈ Finset.range n, ∑ row : Fin n,
        (((w j * (M2 ^ j) row l : ℤ)) : ℂ) • f row.val
        = ∑ row : Fin n,
          (∑ j ∈ Finset.range n, ((w j * (M2 ^ j) row l : ℤ)) : ℂ) • f row.val := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun row _ => by rw [← Finset.sum_smul]
    rw [hswap]
    have hcoef : ∀ row : Fin n, (∑ j ∈ Finset.range n, ((w j * (M2 ^ j) row l : ℤ)) : ℂ)
        = (((I * M3 row l : ℤ)) : ℂ) := by
      intro row
      rw [← Int.cast_sum, hide row l, Int.cast_mul]
    rw [hrep3 l, Finset.smul_sum]
    refine Finset.sum_congr rfl fun row' _ => ?_
    rw [hcoef row', Int.cast_mul, smul_smul]
  refine LinearMap.ext fun x => ?_
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
  rw [step (∑ j ∈ Finset.range n, ((w j : ℤ) : ℂ) • T2 ^ j), step (((I : ℤ) : ℂ) • T3)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [key l, LinearMap.smul_apply]

/-- **`I • T₃ ∈ ℤ[T₂]`, dimension-generic form** (the sibling of
`exists_aeval_rat_dimN`): the same echelon bundle, with the integer
certificate concluded at the operator level. -/
theorem int_poly_of_dimN {k : ℤ} {n : ℕ} (hn : 0 < n)
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
    (w : ℕ → ℤ) (I : ℤ)
    (hid : ∑ j ∈ Finset.range n, w j • M2 ^ j = I • M3) :
    ∑ j ∈ Finset.range n, ((w j : ℤ) : ℂ) • T2 ^ j = ((I : ℤ) : ℂ) • T3 := by
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
  exact int_poly_of_rep hn hdim f (linearIndependent_dimN f A hzero hone hA) T2 T3 M2 M3
    hrep2 hrep3 w I hid

end Rep

/-! ### The abstract Cramer inversion -/

section Cramer

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

/-- **Cramer inversion on an expanding family.**  If each `P i` expands over
the family `u` with integer coefficient row `C i`, and `S` expands with `v`,
then `C.det • S = ∑ i, (∑_k v k * adj C k i) • P i`.  Pure algebra (the
adjugate identity `C.adjugate * C = C.det • 1`); no independence needed. -/
theorem cramer_scale (u : Fin n → (V →ₗ[ℂ] V))
    (C : Matrix (Fin n) (Fin n) ℤ)
    (P : Fin n → (V →ₗ[ℂ] V)) (hP : ∀ i, P i = ∑ j : Fin n, ((C i j : ℤ) : ℂ) • u j)
    (v : Fin n → ℤ) (S : V →ₗ[ℂ] V) (hS : S = ∑ j : Fin n, ((v j : ℤ) : ℂ) • u j) :
    ((C.det : ℤ) : ℂ) • S
      = ∑ i : Fin n, (((∑ k : Fin n, v k * C.adjugate k i : ℤ)) : ℂ) • P i := by
  have hadj : ∀ k j : Fin n,
      (∑ i : Fin n, C.adjugate k i * C i j) = C.det * if k = j then 1 else 0 := by
    intro k j
    have h := congrFun (congrFun (Matrix.adjugate_mul C) k) j
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
    exact h
  -- per-coordinate identity: the Cramer weights express through the adjugate
  have hcoord : ∀ j : Fin n,
      (∑ i : Fin n, (∑ k : Fin n, v k * C.adjugate k i) * C i j) = C.det * v j := by
    intro j
    have hstep : ∀ i : Fin n, (∑ k : Fin n, v k * C.adjugate k i) * C i j
        = ∑ k : Fin n, v k * C.adjugate k i * C i j := fun i => Finset.sum_mul _ _ _
    have hswap : (∑ i : Fin n, (∑ k : Fin n, v k * C.adjugate k i) * C i j)
        = ∑ k : Fin n, v k * (∑ i : Fin n, C.adjugate k i * C i j) := by
      rw [Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hdist : ∀ k : Fin n, v k * (C.det * (if k = j then (1 : ℤ) else 0))
        = (if k = j then v k * C.det else 0) := by
      intro k
      by_cases hk : k = j
      · subst hk
        simp
      · rw [ite_eq_right hk, ite_eq_right hk, mul_zero, mul_zero]
    rw [hswap, Finset.sum_congr rfl fun k _ => by rw [hadj k j],
      Finset.sum_congr rfl fun k _ => hdist k,
      Finset.sum_ite_eq' Finset.univ j (fun k => v k * C.det),
      ite_eq_left (Finset.mem_univ j), mul_comm]
  -- both sides expand over `u` with equal coordinates
  have hL : ((C.det : ℤ) : ℂ) • S
      = ∑ j : Fin n, (((C.det : ℤ) * (v j : ℤ) : ℤ) : ℂ) • u j := by
    rw [hS, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, Int.cast_mul]
  have hR : ∑ i : Fin n, (((∑ k : Fin n, v k * C.adjugate k i : ℤ)) : ℂ) • P i
      = ∑ j : Fin n, (((C.det : ℤ) * (v j : ℤ) : ℤ) : ℂ) • u j := by
    rw [Finset.sum_congr rfl fun i _ => by rw [hP i, Finset.smul_sum], Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hper : ∀ i : Fin n, (((∑ k : Fin n, v k * C.adjugate k i : ℤ)) : ℂ) •
        (((C i j : ℤ) : ℂ) • u j)
        = ((( (∑ k : Fin n, v k * C.adjugate k i) * C i j : ℤ)) : ℂ) • u j := by
      intro i
      rw [smul_smul, ← Int.cast_mul]
    rw [Finset.sum_congr rfl fun i _ => hper i, ← Finset.sum_smul, ← Int.cast_sum,
      hcoord j]
  rw [hL, hR]

end Cramer

/-! ### Uniqueness of representing polynomials, and `D ∣ I_k` -/

section Reduced

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

/-- **Uniqueness of representing polynomials of degree `< n`** when the
minimal polynomial has degree `n`. -/
theorem aeval_inj_of_minpoly [Nontrivial V] (T : V →ₗ[ℂ] V)
    (hmin : (minpoly ℂ (T : Module.End ℂ V)).natDegree = n)
    {p q : ℂ[X]} (hp : p.natDegree < n) (hq : q.natDegree < n)
    (h : Polynomial.aeval (T : Module.End ℂ V) p = Polynomial.aeval (T : Module.End ℂ V) q) :
    p = q := by
  have hz : Polynomial.aeval (T : Module.End ℂ V) (p - q) = 0 := by
    rw [map_sub, h, sub_self]
  have hdvd := minpoly.dvd (A := ℂ) (x := (T : Module.End ℂ V)) hz
  by_contra hpq
  have hpq0 : p - q ≠ 0 := sub_ne_zero_of_ne hpq
  have hsub : (p - q).natDegree ≤ max p.natDegree q.natDegree :=
    Polynomial.natDegree_sub_le p q
  have hle : (minpoly ℂ (T : Module.End ℂ V)).natDegree ≤ (p - q).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hpq0
  omega

/-- The coefficient of the witness polynomial `∑_{j<n} C (r j) * X ^ j`. -/
private lemma coeff_witness {n : ℕ} (R : Type*) [CommRing R] (r : ℕ → R) (t : ℕ) :
    (∑ j ∈ Finset.range n, C (r j) * (X : R[X]) ^ j).coeff t
      = if t < n then r t else 0 := by
  have h1 : ∀ j ∈ Finset.range n, (C (r j) * (X : R[X]) ^ j).coeff t
      = (if j = t then r j else 0) := by
    intro j _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : j = t
    · rw [ite_eq_left h, ite_eq_left (show t = j by omega), mul_one]
    · rw [ite_eq_right h, ite_eq_right (show t ≠ j by omega), mul_zero]
  rw [Polynomial.finsetSum_coeff, Finset.sum_congr rfl h1,
    Finset.sum_ite_eq' (Finset.range n) t r]
  by_cases ht : t < n
  · rw [ite_eq_left (Finset.mem_range.mpr ht), ite_eq_left ht]
  · rw [ite_eq_right ht, ite_eq_right (fun hmem => ht (Finset.mem_range.mp hmem))]

/-- The degree of the witness polynomial is `< n`. -/
private lemma natDegree_witness_lt {n : ℕ} (R : Type*) [CommRing R] (hn : 0 < n)
    (r : ℕ → R) : (∑ j ∈ Finset.range n, C (r j) * (X : R[X]) ^ j).natDegree < n := by
  have hsum : (∑ j ∈ Finset.range n, C (r j) * (X : R[X]) ^ j).natDegree ≤ n - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le (Finset.range n)
      (fun j => C (r j) * (X : R[X]) ^ j) (fun j hj => ?_)
    have hjn : j < n := Finset.mem_range.mp hj
    have hle : (C (r j) * (X : R[X]) ^ j).natDegree ≤ j :=
      Polynomial.natDegree_C_mul_X_pow_le (r j) j
    omega
  omega

/-- **The reduced-denominator divisibility.**  If the witness polynomial
`Q = ∑_j C (N j / D) * X ^ j` (reduced: `∑_j e j * N j + c * D = 1`) and the
Cramer certificate polynomial `Q' = ∑_j C (w j / Ik) * X ^ j` represent the
same operator, and the minimal polynomial of `T₂` has degree `n`, then
`D ∣ Ik`: the reduced denominator of any representation divides the
denominator of every other. -/
theorem den_dvd_index [Nontrivial V] (hn : 0 < n) (T2 T3 : V →ₗ[ℂ] V)
    (hmin : (minpoly ℂ (T2 : Module.End ℂ V)).natDegree = n)
    (N w : ℕ → ℤ) (D Ik : ℤ)
    (hD : ((D : ℤ) : ℚ) ≠ 0) (hIk : ((Ik : ℤ) : ℚ) ≠ 0)
    (hrepD : T3 = Polynomial.aeval T2
      ((∑ j ∈ Finset.range n, C (((N j : ℤ) : ℚ) / ((D : ℤ) : ℚ))
        * (X : ℚ[X]) ^ j).map (algebraMap ℚ ℂ)))
    (hrepI : T3 = Polynomial.aeval T2
      ((∑ j ∈ Finset.range n, C (((w j : ℤ) : ℚ) / ((Ik : ℤ) : ℚ))
        * (X : ℚ[X]) ^ j).map (algebraMap ℚ ℂ)))
    (e : ℕ → ℤ) (c : ℤ) (hbez : ∑ j ∈ Finset.range n, e j * N j + c * D = 1) :
    D ∣ Ik := by
  -- the two ℚ-polynomials are equal (uniqueness after mapping to ℂ)
  have hdegP : (∑ j ∈ Finset.range n, C (((N j : ℤ) : ℚ) / ((D : ℤ) : ℚ))
      * (X : ℚ[X]) ^ j).natDegree < n := natDegree_witness_lt ℚ hn _
  have hdegP' : (∑ j ∈ Finset.range n, C (((w j : ℤ) : ℚ) / ((Ik : ℤ) : ℚ))
      * (X : ℚ[X]) ^ j).natDegree < n := natDegree_witness_lt ℚ hn _
  have hcc : Polynomial.aeval (T2 : Module.End ℂ V)
      ((∑ j ∈ Finset.range n, C (((N j : ℤ) : ℚ) / ((D : ℤ) : ℚ))
        * (X : ℚ[X]) ^ j).map (algebraMap ℚ ℂ))
      = Polynomial.aeval (T2 : Module.End ℂ V)
      ((∑ j ∈ Finset.range n, C (((w j : ℤ) : ℚ) / ((Ik : ℤ) : ℚ))
        * (X : ℚ[X]) ^ j).map (algebraMap ℚ ℂ)) := by
    rw [← hrepD, ← hrepI]
  have hPP' : (∑ j ∈ Finset.range n, C (((N j : ℤ) : ℚ) / ((D : ℤ) : ℚ))
      * (X : ℚ[X]) ^ j) = (∑ j ∈ Finset.range n, C (((w j : ℤ) : ℚ) / ((Ik : ℤ) : ℚ))
      * (X : ℚ[X]) ^ j) := by
    refine Polynomial.map_injective (algebraMap ℚ ℂ)
      (by intro a b h; exact_mod_cast h) ?_
    refine aeval_inj_of_minpoly T2 hmin ?_ ?_ hcc
    · rw [Polynomial.natDegree_map]; exact hdegP
    · rw [Polynomial.natDegree_map]; exact hdegP'
  -- coefficientwise cross-multiplication
  have hcross : ∀ j < n, N j * Ik = w j * D := by
    intro j hj
    have hc : (∑ j' ∈ Finset.range n, C (((N j' : ℤ) : ℚ) / ((D : ℤ) : ℚ))
        * (X : ℚ[X]) ^ j').coeff j = (∑ j' ∈ Finset.range n,
        C (((w j' : ℤ) : ℚ) / ((Ik : ℤ) : ℚ)) * (X : ℚ[X]) ^ j').coeff j :=
      congrArg (fun Q : ℚ[X] => Q.coeff j) hPP'
    rw [coeff_witness ℚ _ j, ite_eq_left hj, coeff_witness ℚ _ j, ite_eq_left hj] at hc
    have hdiv : ((N j : ℤ) : ℚ) / ((D : ℤ) : ℚ) = ((w j : ℤ) : ℚ) / ((Ik : ℤ) : ℚ) := hc
    exact_mod_cast (div_eq_div_iff hD hIk).mp hdiv
  -- the Bézout combination transfers the divisibility
  have hfin : Ik = D * (∑ j ∈ Finset.range n, e j * w j + c * Ik) := by
    have step1 : (∑ j ∈ Finset.range n, e j * N j + c * D) * Ik
        = (∑ j ∈ Finset.range n, e j * (N j * Ik)) + c * (D * Ik) := by
      have hA : (∑ j ∈ Finset.range n, e j * N j + c * D) * Ik
          = (∑ j ∈ Finset.range n, (e j * N j) * Ik) + (c * D) * Ik := by
        rw [add_mul, Finset.sum_mul]
      have hB : (∑ j ∈ Finset.range n, (e j * N j) * Ik)
          = ∑ j ∈ Finset.range n, e j * (N j * Ik) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_assoc]
      rw [hA, hB, mul_assoc c D Ik]
    have step3 : (∑ j ∈ Finset.range n, e j * (N j * Ik)) + c * (D * Ik)
        = D * (∑ j ∈ Finset.range n, e j * w j + c * Ik) := by
      have h3 : (∑ j ∈ Finset.range n, e j * (N j * Ik))
          = ∑ j ∈ Finset.range n, (e j * w j) * D := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hcross j (Finset.mem_range.mp hj)]
        ring
      rw [h3, ← Finset.sum_mul]
      ring
    calc Ik = (∑ j ∈ Finset.range n, e j * N j + c * D) * Ik := by rw [hbez, one_mul]
      _ = (∑ j ∈ Finset.range n, e j * (N j * Ik)) + c * (D * Ik) := step1
      _ = D * (∑ j ∈ Finset.range n, e j * w j + c * Ik) := step3
  exact Dvd.intro _ hfin.symm

end Reduced

end HeckeIndex
