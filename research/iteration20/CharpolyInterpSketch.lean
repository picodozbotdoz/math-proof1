/-
Blueprint scratchpad (Iteration 19 pilot): characteristic polynomial of a
literal integer matrix from n+1 evaluated determinants + interpolation.

Validates, at the pinned Mathlib revision (v4.36.0-rc1):
  * `Matrix.eval_charpoly` — `M.charpoly.eval t = (scalar t - M).det`;
  * `Polynomial.eq_of_natDegree_lt_card_of_eval_eq` — interpolation over an
    injective family of n+1 points (`Fin (n+1) → ℤ` via the ℕ cast);
  * `eval_det` / `norm_det` — Mathlib's certified Bareiss echelon
    decomposition — on the real dim-6 T2 matrix of S_72 (entries ≤ 33 digits);
  * `compute_degree!` / `monicity!` for the degree/monic side conditions;
  * `norm_num` for evaluating the polynomial side at the 7 points.

Data: research/iteration20/data/maeda_dim6_10.json (k = 72), produced by
research/iteration20/maeda_dim6_10_probe.py which regresses against the
charpolys proved in MaedaWeight24 / MaedaDim4Weights.

Check-only file: `lake env lean blueprint/lean/CharpolyInterpSketch.lean`.
Not part of the library.
-/
import Mathlib.Tactic.NormDet
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

open Polynomial Matrix

/-- **Generic charpoly engine (core lemma).**  A `P` of degree `n` whose
evaluations at the n+1 points `0, 1, …, n` agree with `det (t·1 − M)` is the
characteristic polynomial of `M`.  The determinant values are supplied per
point (by `eval_det`); nothing here is dimension-specific. -/
theorem charpoly_of_eval_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (P : ℤ[X])
    (hdeg : P.natDegree = n)
    (h : ∀ i : Fin (n + 1), P.eval ((i : ℕ) : ℤ)
      = (Matrix.scalar (Fin n) ((i : ℕ) : ℤ) - M).det) :
    M.charpoly = P := by
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq M.charpoly P (f := fun i : Fin (n + 1) =>
    ((i : ℕ) : ℤ)) (fun a b hab => Fin.ext (Nat.cast_injective hab)) ?_ ?_
  · intro i
    rw [Matrix.eval_charpoly]
    exact (h i).symm
  · rw [Matrix.charpoly_natDegree_eq_dim, hdeg]
    simp

/-- The matrix of `T₂` on the echelon basis of `S_72` (`dim S_72 = 6`), the
first weight of the dim-6 block (exploration data). -/
def M72 : Matrix (Fin 6) (Fin 6) ℤ :=
      !![3576, 1, 0, 0, 0, 0;
      2361183241441063680000, 3686784, 2088, 1, 0, 0;
      -6686870937316024320000000, 1569300480000, 1047300096, 740352, 600, 1;
      5257014245625692160000000000, 2361354558898176000000, 84053458944000, 31486377984, -1024000, 8064;
      -1009146538984734720000000000000, -3167692353699840000000000, 1265866113024000000, -27179089920000, 33594802176, 2949120;
      11555266180939776000000000000000, 213986410758144000000000000, 3962711310336000000000, 73383542784000000, 1358954496000, 25165824]

/-- The translated matrices `t·1 − M₇₂`, as an explicit literal (symbolic in
`t`); `eval_det` needs this shape. -/
def MT72 (t : ℤ) : Matrix (Fin 6) (Fin 6) ℤ :=
      !![t - 3576, (-1), (0), (0), (0), (0);
      (-2361183241441063680000), t - 3686784, (-2088), (-1), (0), (0);
      (6686870937316024320000000), (-1569300480000), t - 1047300096, (-740352), (-600), (-1);
      (-5257014245625692160000000000), (-2361354558898176000000), (-84053458944000), t - 31486377984, (1024000), (-8064);
      (1009146538984734720000000000000), (3167692353699840000000000), (-1265866113024000000), (27179089920000), t - 33594802176, (-2949120);
      (-11555266180939776000000000000000), (-213986410758144000000000000), (-3962711310336000000000), (-73383542784000000), (-1358954496000), t - 25165824]

/-- One-time symbolic bridge, reused by all seven determinant lemmas. -/
theorem scalar_sub_M72 (t : ℤ) : Matrix.scalar (Fin 6) t - M72 = MT72 t := by
  ext a b
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.sub_apply, M72, MT72,
    Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_succ]
  fin_cases a <;> fin_cases b <;> simp

/-- The characteristic polynomial of `T₂` on `S_72` (descending literal). -/
noncomputable def P72 : ℤ[X] := (X : ℤ[X]) ^ 6 + - C (66157336440) * X ^ 5 + - C (9002758724278005040128) * X ^ 4 + C (500728382584538732877523640647680) * X ^ 3 + C (19397273510102970423350650896766446839267328) * X ^ 2 + - C (841390377086653548715101191193731810412939033433866240) * X ^ 1 + C (4171558450151166049898984513691112295971825841981859595680743424)

theorem P72_natDegree : P72.natDegree = 6 := by unfold P72; compute_degree!

theorem P72_monic : P72.Monic := by unfold P72; monicity!

/-- `det (t·1 − M₇₂)` at `t = 0`, by the certified Bareiss echelon decomposition. -/ theorem det72_0 : (Matrix.scalar (Fin 6) (0 : ℤ) - M72).det = 4171558450151166049898984513691112295971825841981859595680743424 := by
  rw [scalar_sub_M72]
  simp only [MT72]
  eval_det

/-- `det (t·1 − M₇₂)` at `t = 1`, by the certified Bareiss echelon decomposition. -/ theorem det72_1 : (Matrix.scalar (Fin 6) (1 : ℤ) - M72).det = 4171558449309775672831728238486614803584020218439840188564415625 := by
  rw [scalar_sub_M72]
  simp only [MT72]
  eval_det

/-- `det (t·1 − M₇₂)` at `t = 2`, by the certified Bareiss echelon decomposition. -/ theorem det72_2 : (Matrix.scalar (Fin 6) (2 : ℤ) - M72).det = 4171558448468385295803266510305327622338297090466476940179853632 := by
  rw [scalar_sub_M72]
  simp only [MT72]
  eval_det

/-- `det (t·1 − M₇₂)` at `t = 3`, by the certified Bareiss echelon decomposition. -/ theorem det72_3 : (Matrix.scalar (Fin 6) (3 : ℤ) - M72).det = 4171558447626994918813599329150255122529839591144951060589033457 := by
  rw [scalar_sub_M72]
  simp only [MT72]
  eval_det

/-- `det (t·1 − M₇₂)` at `t = 4`, by the certified Bareiss echelon decomposition. -/ theorem det72_4 : (Matrix.scalar (Fin 6) (4 : ℤ) - M72).det = 4171558446785604541862726695024401674453614787349045209972224000 := by
  rw [scalar_sub_M72]
  simp only [MT72]
  eval_det

/-- `det (t·1 − M₇₂)` at `t = 5`, by the certified Bareiss echelon decomposition. -/ theorem det72_5 : (Matrix.scalar (Fin 6) (5 : ℤ) - M72).det = 4171558445944214164950648607930771648404373679743135559747616049 := by
  rw [scalar_sub_M72]
  simp only [MT72]
  eval_det

/-- `det (t·1 − M₇₂)` at `t = 6`, by the certified Bareiss echelon decomposition. -/ theorem det72_6 : (Matrix.scalar (Fin 6) (6 : ℤ) - M72).det = 4171558445102823788077365067872369414676651202782183853690952000 := by
  rw [scalar_sub_M72]
  simp only [MT72]
  eval_det

theorem ev72_0 : P72.eval (0 : ℤ) = 4171558450151166049898984513691112295971825841981859595680743424 := by
  norm_num [P72, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_neg]

theorem ev72_1 : P72.eval (1 : ℤ) = 4171558449309775672831728238486614803584020218439840188564415625 := by
  norm_num [P72, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_neg]

theorem ev72_2 : P72.eval (2 : ℤ) = 4171558448468385295803266510305327622338297090466476940179853632 := by
  norm_num [P72, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_neg]

theorem ev72_3 : P72.eval (3 : ℤ) = 4171558447626994918813599329150255122529839591144951060589033457 := by
  norm_num [P72, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_neg]

theorem ev72_4 : P72.eval (4 : ℤ) = 4171558446785604541862726695024401674453614787349045209972224000 := by
  norm_num [P72, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_neg]

theorem ev72_5 : P72.eval (5 : ℤ) = 4171558445944214164950648607930771648404373679743135559747616049 := by
  norm_num [P72, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_neg]

theorem ev72_6 : P72.eval (6 : ℤ) = 4171558445102823788077365067872369414676651202782183853690952000 := by
  norm_num [P72, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_neg]

/-- Assembly: seven determinant evaluations + interpolation. -/
theorem charpoly_M72 : M72.charpoly = P72 := by
  refine charpoly_of_eval_eq M72 P72 P72_natDegree ?_
  intro i
  fin_cases i
    · exact ev72_0
    · exact ev72_1
    · exact ev72_2
    · exact ev72_3
    · exact ev72_4
    · exact ev72_5
    · exact ev72_6
