#!/usr/bin/env python3
"""Generate blueprint/lean/CharpolyInterpSketch.lean from the exploration JSON.

The k=72 (dim S_k = 6) pilot: charpoly of the T2 matrix by 7 evaluated
determinants (Mathlib `eval_det` = certified Bareiss echelon decomposition)
plus interpolation.  Numerals are computed here, never by hand.

Round-2 lessons baked in (see blueprint findings): `Polynomial` literals are
noncomputable; natDegree/Monic go through `compute_degree!` / `monicity!`;
`(scalar t - M)` is bridged to a `!![...]` literal once, symbolically, by
`Matrix.ext` + `fin_cases`.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
w = next(x for x in json.load(open(ROOT / "blueprint/exploration/data/maeda_dim6_10.json"))
         if x["k"] == 72)
M, cp = w["matrix"], w["charpoly"]
n = w["dim"]
assert n == 6 and len(cp) == 7 and cp[0] == 1

EVAL_LEMMAS = ("Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, "
               "Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, "
               "Polynomial.eval_neg")


def det_t(t):
    m = [[(t if i == j else 0) - M[i][j] for j in range(n)] for i in range(n)]
    sign, prev = 1, 1
    for k in range(n - 1):
        piv = next((i for i in range(k, n) if m[i][k]), None)
        if piv is None:
            return 0
        if piv != k:
            m[k], m[piv] = m[piv], m[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                m[i][j] = (m[i][j] * m[k][k] - m[i][k] * m[k][j]) // prev
        prev = m[k][k]
    return sign * m[n - 1][n - 1]


vals = [det_t(t) for t in range(n + 1)]
for t in range(n + 1):  # cross-check vs the probe's interpolation
    ev = 0
    for c in cp:
        ev = ev * t + c
    assert ev == vals[t], (t, ev, vals[t])

rows = ";\n      ".join(", ".join(str(x) for x in r) for r in M)
# symbolic literal (t - m) on the diagonal, (- m) off
lit_rows = ";\n      ".join(
    ", ".join(("t - " + str(M[i][j])) if i == j else ("(" + str(-M[i][j]) + ")")
              for j in range(n)) for i in range(n))
terms = []
for i, c in enumerate(cp):
    if i == 0:
        terms.append("(X : ℤ[X]) ^ 6")
    elif i < n:
        terms.append(f"C ({c}) * X ^ {n - i}" if c >= 0 else f"- C ({-c}) * X ^ {n - i}")
    else:
        terms.append(f"C ({c})" if c >= 0 else f"- C ({-c})")
P = " + ".join(terms)

det_l = "\n\n".join(
    f"/-- `det (t·1 − M₇₂)` at `t = {t}`, by the certified Bareiss echelon decomposition. -/ "
    f"theorem det72_{t} : (Matrix.scalar (Fin 6) ({t} : ℤ) - M72).det = {vals[t]} := by\n"
    f"  rw [scalar_sub_M72]\n"
    f"  simp only [MT72]\n"
    f"  eval_det"
    for t in range(n + 1))

ev_l = "\n\n".join(
    f"theorem ev72_{t} : P72.eval ({t} : ℤ) = {vals[t]} := by\n"
    f"  norm_num [P72, {EVAL_LEMMAS}]"
    for t in range(n + 1))

exact_l = "\n    ".join(f"· exact ev72_{t}" for t in range(n + 1))
exact_l = "    " + exact_l

out = f"""/-
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

Data: blueprint/exploration/data/maeda_dim6_10.json (k = 72), produced by
blueprint/exploration/maeda_dim6_10_probe.py which regresses against the
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
theorem charpoly_of_eval_eq {{n : ℕ}} (M : Matrix (Fin n) (Fin n) ℤ) (P : ℤ[X])
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
      !![{rows}]

/-- The translated matrices `t·1 − M₇₂`, as an explicit literal (symbolic in
`t`); `eval_det` needs this shape. -/
def MT72 (t : ℤ) : Matrix (Fin 6) (Fin 6) ℤ :=
      !![{lit_rows}]

/-- One-time symbolic bridge, reused by all seven determinant lemmas. -/
theorem scalar_sub_M72 (t : ℤ) : Matrix.scalar (Fin 6) t - M72 = MT72 t := by
  ext a b
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.sub_apply, M72, MT72]
  fin_cases a <;> fin_cases b <;> simp

/-- The characteristic polynomial of `T₂` on `S_72` (descending literal). -/
noncomputable def P72 : ℤ[X] := {P}

theorem P72_natDegree : P72.natDegree = 6 := by unfold P72; compute_degree!

theorem P72_monic : P72.Monic := by unfold P72; monicity!

{det_l}

{ev_l}

/-- Assembly: seven determinant evaluations + interpolation. -/
theorem charpoly_M72 : M72.charpoly = P72 := by
  refine charpoly_of_eval_eq M72 P72 P72_natDegree ?_
  intro i
  fin_cases i
{exact_l}
"""

p = Path(__file__).resolve().parent / "CharpolyInterpSketch.lean"
p.write_text(out)
print("wrote", p)
print("vals:", vals)
