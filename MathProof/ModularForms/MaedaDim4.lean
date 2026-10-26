import MathProof.ModularForms.MaedaLevelOne

/-!
# Maeda's conjecture machinery in dimension 4

Extends `MathProof/ModularForms/MaedaLevelOne.lean` to the level-one weights
with `dim S_k = 4` (`k = 48, 52, 54, 56, 58, 62`):

* `charpoly_dim4` — the matrix of an endomorphism in a triangular basis
  `f_i = q^i + O(q^(i+1))` is read off the first four q-coefficients of the images;
* `charpoly_fin_four` — the characteristic polynomial of a `4 × 4` matrix via
  its principal-minor sums;
* `irreducible_quartic` / `irreducible_quartic_of_mod` — for degree 4,
  "no root mod ℓ" is not enough: a monic quartic over a field is irreducible
  iff it has no root and no factorization into two monic quadratics, and the
  latter reduces (by solving for the second factor) to a check over pairs
  `(u, v)` — `ℓ²` cases, decidable by `decide` for small `ℓ`.
-/

open UpperHalfPlane ModularForm CuspForm Polynomial
open scoped MatrixGroups

namespace MaedaLevelOne

/-! ### Memoized coefficient evaluation

`seqP` is defined by nested Cauchy products; evaluating it directly in the kernel
recomputes subterms exponentially often.  `seqPL` computes the first `N`
coefficients as lists (each product `O(N²)`), and `seqP_getD` transfers. -/

/-- The first `N` values of a sequence. -/
def lst (p : ℕ → ℤ) (N : ℕ) : List ℤ := (List.range N).map p

/-- Cauchy product of two coefficient lists (truncated to the first list's length). -/
def convL (P Q : List ℤ) : List ℤ :=
  (List.range P.length).map fun n => ∑ i ∈ Finset.range (n + 1), P.getD i 0 * Q.getD (n - i) 0

lemma lst_getD {p : ℕ → ℤ} {N n : ℕ} (h : n < N) : (lst p N).getD n 0 = p n := by
  simp [lst, List.getD_eq_getElem?_getD, h]

lemma convL_lst (p q : ℕ → ℤ) (N : ℕ) : convL (lst p N) (lst q N) = lst (conv p q) N := by
  simp only [convL, lst, List.length_map, List.length_range]
  refine List.map_congr_left fun n hn => ?_
  rw [List.mem_range] at hn
  rw [conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p i * q j)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [← lst, ← lst, lst_getD (by omega), lst_getD (by omega)]

/-- `cpow` on lists. -/
def cpowL (p : ℕ → ℤ) (N : ℕ) : ℕ → List ℤ
  | 0 => lst one N
  | m + 1 => convL (cpowL p N m) (lst p N)

lemma cpowL_eq (p : ℕ → ℤ) (N : ℕ) (m : ℕ) : cpowL p N m = lst (cpow p m) N := by
  induction m with
  | zero => rfl
  | succ m ih => rw [cpowL, ih, convL_lst]; rfl

/-- `seqP` on lists. -/
noncomputable def seqPL (i a b N : ℕ) : List ℤ :=
  convL (lst dC N) (convL (cpowL dC N i) (convL (cpowL e4 N a) (cpowL e6 N b)))

lemma seqP_getD {i a b N n : ℕ} (h : n < N) : seqP i a b n = (seqPL i a b N).getD n 0 := by
  rw [seqPL, cpowL_eq, cpowL_eq, cpowL_eq, convL_lst, convL_lst, convL_lst, lst_getD h]
  rfl

/-! ### Irreducible quartics -/

/-- **A monic quartic certificate**: if `X⁴ + a X³ + b X² + c X + d` has no root
and no factorization `(X² + u X + v)(X² + s X + t)` (where `s, t` are forced:
`s = a − u`, `t = b − v − u s`), it is irreducible. -/
theorem irreducible_quartic {K : Type*} [Field K] (a b c d : K)
    (hroot : ∀ x : K, x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d ≠ 0)
    (hquad : ∀ u v : K,
      ¬ (u * (b - v - u * (a - u)) + v * (a - u) = c ∧ v * (b - v - u * (a - u)) = d)) :
    Irreducible (X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d : K[X]) := by
  have hmon : (X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d : K[X]).Monic := by monicity!
  have hdeg : (X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d : K[X]).natDegree = 4 := by
    compute_degree!
  rw [hmon.irreducible_iff_natDegree']
  refine ⟨fun h => by simp [h] at hdeg, fun f g hf hg hfg hmem => ?_⟩
  rw [hdeg, Finset.mem_Ioc] at hmem
  have hfdeg : f.natDegree + g.natDegree = 4 := by rw [← hf.natDegree_mul hg, hfg, hdeg]
  rcases (by omega : g.natDegree = 1 ∨ g.natDegree = 2) with h1 | h2
  · -- a linear factor gives a root
    set r := g.coeff 0
    have hg1 : g = X + C r := hg.eq_X_add_C h1
    apply hroot (-r)
    have h := congrArg (eval (-r)) hfg
    rw [hg1] at h
    simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C, neg_add_cancel, mul_zero] at h
    exact h.symm
  · -- two monic quadratics
    have hf2 : f.natDegree = 2 := by omega
    have hfs := hf.as_sum
    have hgs := hg.as_sum
    rw [hf2] at hfs
    rw [h2] at hgs
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
      pow_one] at hfs hgs
    set s := f.coeff 1
    set t := f.coeff 0
    set u := g.coeff 1
    set v := g.coeff 0
    have hprod : f * g = X ^ 4 + C (s + u) * X ^ 3 + C (t + v + s * u) * X ^ 2
        + C (s * v + t * u) * X + C (t * v) := by
      rw [hfs, hgs]; simp only [map_add, map_mul]; ring
    rw [hprod] at hfg
    have d3 := congrArg (fun P : K[X] => P.coeff 3) hfg
    have d2 := congrArg (fun P : K[X] => P.coeff 2) hfg
    have d1 := congrArg (fun P : K[X] => P.coeff 1) hfg
    have d0 := congrArg (fun P : K[X] => P.coeff 0) hfg
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C] at d3 d2 d1 d0
    norm_num at d3 d2 d1 d0
    apply hquad u v
    have hs : a - u = s := by linear_combination -d3
    have ht : b - v - u * (a - u) = t := by linear_combination -d2 + u * d3
    rw [ht, hs]
    constructor
    · linear_combination d1
    · linear_combination d0

/-- **Irreducibility over `ℚ` from a quartic certificate mod `ℓ`.** -/
theorem irreducible_quartic_of_mod {P : ℤ[X]} (hmon : P.Monic) (ℓ : ℕ) [Fact ℓ.Prime]
    (a b c d : ZMod ℓ)
    (hmap : P.map (Int.castRingHom (ZMod ℓ)) = X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d)
    (hroot : ∀ x : ZMod ℓ, x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d ≠ 0)
    (hquad : ∀ u v : ZMod ℓ,
      ¬ (u * (b - v - u * (a - u)) + v * (a - u) = c ∧ v * (b - v - u * (a - u)) = d)) :
    Irreducible (P.map (Int.castRingHom ℚ)) := by
  have hmod : Irreducible (P.map (Int.castRingHom (ZMod ℓ))) := by
    rw [hmap]; exact irreducible_quartic a b c d hroot hquad
  have hZ : Irreducible P :=
    Polynomial.Monic.irreducible_of_irreducible_map (φ := Int.castRingHom (ZMod ℓ)) P hmon hmod
  have hQ := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ) hmon).mp hZ
  simpa [algebraMap_int_eq] using hQ

/-! ### `4 × 4` characteristic polynomials -/

/-- The characteristic polynomial of a `4 × 4` matrix: `X⁴ − e₁ X³ + e₂ X² − e₃ X + det`,
with `e_i` the sums of principal `i × i` minors. -/
lemma charpoly_fin_four {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    M.charpoly = X ^ 4 - C (M 0 0 + M 1 1 + M 2 2 + M 3 3) * X ^ 3
      + C ((M 0 0 * M 1 1 - M 0 1 * M 1 0) + (M 0 0 * M 2 2 - M 0 2 * M 2 0)
        + (M 0 0 * M 3 3 - M 0 3 * M 3 0) + (M 1 1 * M 2 2 - M 1 2 * M 2 1)
        + (M 1 1 * M 3 3 - M 1 3 * M 3 1) + (M 2 2 * M 3 3 - M 2 3 * M 3 2)) * X ^ 2
      - C ((M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 * M 2 1 - M 0 1 * M 1 0 * M 2 2 +
        M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0)
        + (M 0 0 * M 1 1 * M 3 3 - M 0 0 * M 1 3 * M 3 1 - M 0 1 * M 1 0 * M 3 3 +
        M 0 1 * M 1 3 * M 3 0 + M 0 3 * M 1 0 * M 3 1 - M 0 3 * M 1 1 * M 3 0)
        + (M 0 0 * M 2 2 * M 3 3 - M 0 0 * M 2 3 * M 3 2 - M 0 2 * M 2 0 * M 3 3 +
        M 0 2 * M 2 3 * M 3 0 + M 0 3 * M 2 0 * M 3 2 - M 0 3 * M 2 2 * M 3 0)
        + (M 1 1 * M 2 2 * M 3 3 - M 1 1 * M 2 3 * M 3 2 - M 1 2 * M 2 1 * M 3 3 +
        M 1 2 * M 2 3 * M 3 1 + M 1 3 * M 2 1 * M 3 2 - M 1 3 * M 2 2 * M 3 1)) * X
      + C (M 0 0 * (M 1 1 * M 2 2 * M 3 3 - M 1 1 * M 2 3 * M 3 2
          - M 1 2 * M 2 1 * M 3 3 + M 1 2 * M 2 3 * M 3 1
          + M 1 3 * M 2 1 * M 3 2 - M 1 3 * M 2 2 * M 3 1)
        - M 0 1 * (M 1 0 * M 2 2 * M 3 3 - M 1 0 * M 2 3 * M 3 2
          - M 1 2 * M 2 0 * M 3 3 + M 1 2 * M 2 3 * M 3 0
          + M 1 3 * M 2 0 * M 3 2 - M 1 3 * M 2 2 * M 3 0)
        + M 0 2 * (M 1 0 * M 2 1 * M 3 3 - M 1 0 * M 2 3 * M 3 1
          - M 1 1 * M 2 0 * M 3 3 + M 1 1 * M 2 3 * M 3 0
          + M 1 3 * M 2 0 * M 3 1 - M 1 3 * M 2 1 * M 3 0)
        - M 0 3 * (M 1 0 * M 2 1 * M 3 2 - M 1 0 * M 2 2 * M 3 1
          - M 1 1 * M 2 0 * M 3 2 + M 1 1 * M 2 2 * M 3 0
          + M 1 2 * M 2 0 * M 3 1 - M 1 2 * M 2 1 * M 3 0)) := by
  rw [Matrix.charpoly, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.charmatrix_apply,
    Matrix.diagonal_apply, Fin.succAbove]
  ring

/-! ### Dimension 4 -/

/-- **Dimension 4.**  For a triangular basis `f_i = q^i + ⋯` of a 4-dimensional
`S_k` (coefficients `a_im`), the matrix of `T` is read off the first four
coefficients `x_jm` of `T f_j` by back-substitution. -/
theorem charpoly_dim4 {k : ℤ} (hdim : Module.finrank ℂ (CuspForm 𝒮ℒ k) = 4)
    (f1 f2 f3 f4 : CuspForm 𝒮ℒ k) {a12 a13 a14 a23 a24 a34 : ℂ}
    (h11 : (qExpansion 1 f1).coeff 1 = 1) (h12 : (qExpansion 1 f1).coeff 2 = a12)
    (h13 : (qExpansion 1 f1).coeff 3 = a13) (h14 : (qExpansion 1 f1).coeff 4 = a14)
    (h21 : (qExpansion 1 f2).coeff 1 = 0) (h22 : (qExpansion 1 f2).coeff 2 = 1)
    (h23 : (qExpansion 1 f2).coeff 3 = a23) (h24 : (qExpansion 1 f2).coeff 4 = a24)
    (h31 : (qExpansion 1 f3).coeff 1 = 0) (h32 : (qExpansion 1 f3).coeff 2 = 0)
    (h33 : (qExpansion 1 f3).coeff 3 = 1) (h34 : (qExpansion 1 f3).coeff 4 = a34)
    (h41 : (qExpansion 1 f4).coeff 1 = 0) (h42 : (qExpansion 1 f4).coeff 2 = 0)
    (h43 : (qExpansion 1 f4).coeff 3 = 0) (h44 : (qExpansion 1 f4).coeff 4 = 1)
    (T : CuspForm 𝒮ℒ k →ₗ[ℂ] CuspForm 𝒮ℒ k)
    {x11 x12 x13 x14 x21 x22 x23 x24 x31 x32 x33 x34 x41 x42 x43 x44 : ℂ}
    (hx11 : (qExpansion 1 (T f1)).coeff 1 = x11)
      (hx12 : (qExpansion 1 (T f1)).coeff 2 = x12)
    (hx13 : (qExpansion 1 (T f1)).coeff 3 = x13)
      (hx14 : (qExpansion 1 (T f1)).coeff 4 = x14)
    (hx21 : (qExpansion 1 (T f2)).coeff 1 = x21)
      (hx22 : (qExpansion 1 (T f2)).coeff 2 = x22)
    (hx23 : (qExpansion 1 (T f2)).coeff 3 = x23)
      (hx24 : (qExpansion 1 (T f2)).coeff 4 = x24)
    (hx31 : (qExpansion 1 (T f3)).coeff 1 = x31)
      (hx32 : (qExpansion 1 (T f3)).coeff 2 = x32)
    (hx33 : (qExpansion 1 (T f3)).coeff 3 = x33)
      (hx34 : (qExpansion 1 (T f3)).coeff 4 = x34)
    (hx41 : (qExpansion 1 (T f4)).coeff 1 = x41)
      (hx42 : (qExpansion 1 (T f4)).coeff 2 = x42)
    (hx43 : (qExpansion 1 (T f4)).coeff 3 = x43)
      (hx44 : (qExpansion 1 (T f4)).coeff 4 = x44) :
    T.charpoly = Matrix.charpoly
      !![x11,
      x21,
      x31,
      x41;
      (x12 - a12 * x11),
      (x22 - a12 * x21),
      (x32 - a12 * x31),
      (x42 - a12 * x41);
      (x13 - a13 * x11 - a23 * (x12 - a12 * x11)),
      (x23 - a13 * x21 - a23 * (x22 - a12 * x21)),
      (x33 - a13 * x31 - a23 * (x32 - a12 * x31)),
      (x43 - a13 * x41 - a23 * (x42 - a12 * x41));
      (x14 - a14 * x11 - a24 * (x12 - a12 * x11)
        - a34 * (x13 - a13 * x11 - a23 * (x12 - a12 * x11))),
      (x24 - a14 * x21 - a24 * (x22 - a12 * x21)
        - a34 * (x23 - a13 * x21 - a23 * (x22 - a12 * x21))),
      (x34 - a14 * x31 - a24 * (x32 - a12 * x31)
        - a34 * (x33 - a13 * x31 - a23 * (x32 - a12 * x31))),
      (x44 - a14 * x41 - a24 * (x42 - a12 * x41)
        - a34 * (x43 - a13 * x41 - a23 * (x42 - a12 * x41)))] := by
  have hli : LinearIndependent ℂ ![f1, f2, f3, f4] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := coeff_sum Finset.univ g ![f1, f2, f3, f4] 1
    have h2 := coeff_sum Finset.univ g ![f1, f2, f3, f4] 2
    have h3 := coeff_sum Finset.univ g ![f1, f2, f3, f4] 3
    have h4 := coeff_sum Finset.univ g ![f1, f2, f3, f4] 4
    simp only [hg, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons,
      FunLike.coe_zero, qExpansion_zero, map_zero, h11, h12, h13, h14, h21, h22, h23, h24,
      h31, h32, h33, h34, h41, h42, h43, h44] at h1 h2 h3 h4
    have g0 : g 0 = 0 := by linear_combination -h1
    have g1 : g 1 = 0 := by linear_combination -h2 + a12 * h1
    have g2 : g 2 = 0 := by linear_combination -h3 + a13 * h1 + a23 * (h2 - a12 * h1)
    have g3 : g 3 = 0 := by linear_combination -h4 + a14 * h1 + a24 * (h2 - a12 * h1) + a34 * (h3
      - a13 * h1 - a23 * (h2 - a12 * h1))
    fin_cases i
    · exact g0
    · exact g1
    · exact g2
    · exact g3
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb : ∀ g, b.repr g 0 = (qExpansion 1 g).coeff 1
      ∧ b.repr g 1 = ((qExpansion 1 g).coeff 2 - a12 * (qExpansion 1 g).coeff 1)
      ∧ b.repr g 2 = ((qExpansion 1 g).coeff 3 - a13 * (qExpansion 1 g).coeff 1
        - a23 * ((qExpansion 1 g).coeff 2 - a12 * (qExpansion 1 g).coeff 1))
      ∧ b.repr g 3 = ((qExpansion 1 g).coeff 4 - a14 * (qExpansion 1 g).coeff 1
        - a24 * ((qExpansion 1 g).coeff 2
        - a12 * (qExpansion 1 g).coeff 1) - a34 * ((qExpansion 1 g).coeff 3
        - a13 * (qExpansion 1 g).coeff 1 - a23 * ((qExpansion 1 g).coeff 2
        - a12 * (qExpansion 1 g).coeff 1))) := by
    intro g
    have hs := b.sum_repr g
    have h1 := coeff_sum Finset.univ (b.repr g) b 1
    have h2 := coeff_sum Finset.univ (b.repr g) b 2
    have h3 := coeff_sum Finset.univ (b.repr g) b 3
    have h4 := coeff_sum Finset.univ (b.repr g) b 4
    rw [hs] at h1 h2 h3 h4
    simp only [Fin.sum_univ_four, b, coe_basisOfLinearIndependentOfCardEqFinrank,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.head_cons, h11, h12, h13, h14, h21, h22, h23, h24, h31, h32,
      h33, h34, h41, h42, h43, h44] at h1 h2 h3 h4
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination -h1
    · linear_combination -h2 + a12 * h1
    · linear_combination -h3 + a13 * h1 + a23 * (h2 - a12 * h1)
    · linear_combination -h4 + a14 * h1 + a24 * (h2 - a12 * h1) + a34 * (h3 - a13 * h1 - a23 * (h2
      - a12 * h1))
  rw [← LinearMap.charpoly_toMatrix T b]
  congr 1
  have hb0 : b 0 = f1 := by simp [b]
  have hb1 : b 1 = f2 := by simp [b]
  have hb2 : b 2 = f3 := by simp [b]
  have hb3 : b 3 = f4 := by simp [b]
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j
  · change b.repr (T (b 0)) 0 = _; rw [(hb _).1, hb0, hx11]; rfl
  · change b.repr (T (b 1)) 0 = _; rw [(hb _).1, hb1, hx21]; rfl
  · change b.repr (T (b 2)) 0 = _; rw [(hb _).1, hb2, hx31]; rfl
  · change b.repr (T (b 3)) 0 = _; rw [(hb _).1, hb3, hx41]; rfl
  · change b.repr (T (b 0)) 1 = _; rw [(hb _).2.1, hb0, hx11, hx12]; rfl
  · change b.repr (T (b 1)) 1 = _; rw [(hb _).2.1, hb1, hx21, hx22]; rfl
  · change b.repr (T (b 2)) 1 = _; rw [(hb _).2.1, hb2, hx31, hx32]; rfl
  · change b.repr (T (b 3)) 1 = _; rw [(hb _).2.1, hb3, hx41, hx42]; rfl
  · change b.repr (T (b 0)) 2 = _; rw [(hb _).2.2.1, hb0, hx11, hx12, hx13]; rfl
  · change b.repr (T (b 1)) 2 = _; rw [(hb _).2.2.1, hb1, hx21, hx22, hx23]; rfl
  · change b.repr (T (b 2)) 2 = _; rw [(hb _).2.2.1, hb2, hx31, hx32, hx33]; rfl
  · change b.repr (T (b 3)) 2 = _; rw [(hb _).2.2.1, hb3, hx41, hx42, hx43]; rfl
  · change b.repr (T (b 0)) 3 = _; rw [(hb _).2.2.2, hb0, hx11, hx12, hx13, hx14]; rfl
  · change b.repr (T (b 1)) 3 = _; rw [(hb _).2.2.2, hb1, hx21, hx22, hx23, hx24]; rfl
  · change b.repr (T (b 2)) 3 = _; rw [(hb _).2.2.2, hb2, hx31, hx32, hx33, hx34]; rfl
  · change b.repr (T (b 3)) 3 = _; rw [(hb _).2.2.2, hb3, hx41, hx42, hx43, hx44]; rfl

end MaedaLevelOne
