import MathProof.ModularForms.MaedaDim4
import MathProof.ModularForms.HornerCert

/-!
# Axiom-free coefficient lists for the Maeda certificates

The proof standard (CLAUDE.md) asks `decide` certificates to depend on
`propext` only.  A certificate about `seqPL` cannot: `seqPL` is built from
`Finset.sum` and `ArithmeticFunction.sigma` (`Finset`/`Multiset`: `Classical.choice`,
`Quot.sound`) and from `dC` (which mentions `Ramanujan.tau`).  `seqPLc`
computes the same lists from `List` sums, trial-division `σ` and `tauTable`
only; `seqPLc_eq` transfers (for `N ≤ 22`).  Kept in its own module (not in
`MaedaDim4`) so the heavy `MaedaGalois5` chain, which imports `MaedaDim5`, is
not invalidated.
-/

open UpperHalfPlane ModularForm CuspForm Polynomial
open scoped MatrixGroups

namespace MaedaLevelOne

/-- `σ_k(m)` by trial division. -/
def sigmaL (k m : ℕ) : ℕ :=
  ((List.range m).map fun d => if m % (d + 1) = 0 then (d + 1) ^ k else 0).sum

lemma finset_sum_range_eq_list {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

lemma sigmaL_eq (k m : ℕ) : sigmaL k m = ArithmeticFunction.sigma k m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [sigmaL]
  rw [ArithmeticFunction.sigma_apply, ← Nat.filter_dvd_eq_divisors hm.ne', Finset.sum_filter,
    Finset.sum_range_succ', finset_sum_range_eq_list, sigmaL]
  simp only [zero_dvd_iff, hm.ne', ↓reduceIte, add_zero, Nat.dvd_iff_mod_eq_zero]

/-- `e4` with `sigmaL`. -/
def e4c (m : ℕ) : ℤ := if m = 0 then 1 else 240 * (sigmaL 3 m : ℤ)

/-- `e6` with `sigmaL`. -/
def e6c (m : ℕ) : ℤ := if m = 0 then 1 else -504 * (sigmaL 5 m : ℤ)

lemma e4c_eq : e4c = e4 := funext fun m => by simp only [e4c, e4, sigmaL_eq]

lemma e6c_eq : e6c = e6 := funext fun m => by simp only [e6c, e6, sigmaL_eq]

/-- `dC` read from `tauTable` only (agrees with `dC` below index 22). -/
def dCc (m : ℕ) : ℤ := tauTable.getD m 0

lemma lst_dCc {N : ℕ} (hN : N ≤ 22) : lst dCc N = lst dC N := by
  refine List.map_congr_left fun n hn => ?_
  rw [List.mem_range] at hn
  simp [dCc, dC, show n ≤ 21 by omega]

/-- `convL` with a `List` sum. -/
def convLc (P Q : List ℤ) : List ℤ :=
  (List.range P.length).map fun n =>
    ((List.range (n + 1)).map fun i => P.getD i 0 * Q.getD (n - i) 0).sum

lemma convLc_eq : convLc = convL := by
  funext P Q
  simp only [convLc, convL, finset_sum_range_eq_list]

/-- `cpowL` with `convLc`. -/
def cpowLc (p : ℕ → ℤ) (N : ℕ) : ℕ → List ℤ
  | 0 => lst one N
  | m + 1 => convLc (cpowLc p N m) (lst p N)

lemma cpowLc_eq (p : ℕ → ℤ) (N m : ℕ) : cpowLc p N m = cpowL p N m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [cpowLc, cpowL, ih, convLc_eq]

lemma cpowLc_dCc {N : ℕ} (hN : N ≤ 22) (m : ℕ) : cpowLc dCc N m = cpowL dC N m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [cpowLc, cpowL, ih, convLc_eq, lst_dCc hN]

/-- `seqPL` without `Finset`, `ArithmeticFunction` or `Ramanujan.tau`. -/
def seqPLc (i a b N : ℕ) : List ℤ :=
  convLc (lst dCc N) (convLc (cpowLc dCc N i) (convLc (cpowLc e4c N a) (cpowLc e6c N b)))

lemma seqPLc_eq {i a b N : ℕ} (hN : N ≤ 22) : seqPLc i a b N = seqPL i a b N := by
  rw [seqPLc, seqPL, lst_dCc hN, cpowLc_dCc hN, cpowLc_eq, cpowLc_eq, e4c_eq, e6c_eq,
    convLc_eq]

end MaedaLevelOne
