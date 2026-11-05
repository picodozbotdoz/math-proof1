import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD

/-!
# `propext`-only certificates for scaled matrix-polynomial identities

The generated files `HeckeIndex{Small,}Weights` and `HeckeRational{Small,}Weights`
certify identities of the shape

    (∑ j ∈ Finset.range d, w j • M2 ^ j) = s • N

for integer matrices `M2`, `N` given as `!![…]` literals.  Deciding them cell by
cell drags `Finset` sums (the `Multiset` quotient), the `!![…]` notation
(`Quot.sound`) and `^` on numerals (`Monoid.npow`, whose `ℤ` instance is not
axiom-free) into every certificate.  Here the identity is reduced to ONE boolean
over integer tables and `List` sums:

* `powL m n i` — the rows of the `i`-th power of the `n × n` table `m`, as lists;
* `cellL` — the `(r, c)` cell of `∑_{j<d} w j • m^j`;
* `scaledCheck` — all `n²` cells equal `s * t r c` (comparison by `Int.decEq`,
  never the `BEq ℤ` instance, which routes through `Classical.choice`);
* `scaled_of_check` — the bridge back to the matrix identity, given table
  bridges `M2 i j = m i j`, `N i j = t i j` and pow-free value bridges
  `w j = wv j`, `s = sv` (all proved by `rfl` in the generated files).

The `decide +kernel` of `scaledCheck … = true` then depends on `propext` only
(the iteration-24 recipe `HeckeLatticeIndex.hcard_of_check`).
-/

namespace ScaledCert

/-- The rows of the `i`-th power of the `n × n` integer table `m`, as `List`s. -/
def powL (m : ℕ → ℕ → ℤ) (n : ℕ) : ℕ → List (List ℤ)
  | 0 => (List.range n).map fun r => (List.range n).map fun c => if r = c then 1 else 0
  | i + 1 => (List.range n).map fun r => (List.range n).map fun c =>
      ((List.range n).map fun l => ((powL m n i).getD r []).getD l 0 * m l c).sum

/-- The `(r, c)` cell of `∑_{j<d} w j • m^j`, over `List` sums. -/
def cellL (w : ℕ → ℤ) (m : ℕ → ℕ → ℤ) (n d r c : ℕ) : ℤ :=
  ((List.range d).map fun j => w j * ((powL m n j).getD r []).getD c 0).sum

/-- The whole identity `∑_{j<d} w j • m^j = s • t` as ONE boolean. -/
def scaledCheck (w : ℕ → ℤ) (m : ℕ → ℕ → ℤ) (s : ℤ) (t : ℕ → ℕ → ℤ) (n d : ℕ) : Bool :=
  (List.range n).all fun r => (List.range n).all fun c =>
    (Int.decEq (cellL w m n d r c) (s * t r c)).decide

variable {n : ℕ}

lemma getD_map_range {α : Type*} (f : ℕ → α) (x : α) {c : ℕ} (hc : c < n) :
    ((List.range n).map f).getD c x = f c := by
  rw [List.getD_eq_getElem _ _ (by simpa using hc)]
  simp

lemma list_sum_eq_finset_sum (f : ℕ → ℤ) (d : ℕ) :
    ((List.range d).map f).sum = ∑ j ∈ Finset.range d, f j := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ← ih, List.range_succ, List.map_append, List.sum_append]
    simp

lemma list_sum_eq_fin_sum (f : ℕ → ℤ) :
    ((List.range n).map f).sum = ∑ l : Fin n, f l.val := by
  rw [list_sum_eq_finset_sum]
  exact (Fin.sum_univ_eq_sum_range f n).symm

lemma powL_getD (M : Matrix (Fin n) (Fin n) ℤ) (m : ℕ → ℕ → ℤ)
    (hM : ∀ i j : Fin n, M i j = m i.val j.val) (i : ℕ) (r c : Fin n) :
    ((powL m n i).getD r.val []).getD c.val 0 = (M ^ i) r c := by
  induction i generalizing r c with
  | zero =>
      rw [powL, getD_map_range _ _ r.isLt, getD_map_range _ _ c.isLt, pow_zero,
        Matrix.one_apply]
      simp only [Fin.val_inj]
  | succ i ih =>
      rw [powL, getD_map_range _ _ r.isLt, getD_map_range _ _ c.isLt, pow_succ,
        Matrix.mul_apply, list_sum_eq_fin_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [ih r l, ← hM l c]

lemma cellL_eq (w : ℕ → ℤ) (M : Matrix (Fin n) (Fin n) ℤ) (m : ℕ → ℕ → ℤ)
    (hM : ∀ i j : Fin n, M i j = m i.val j.val) (d : ℕ) (r c : Fin n) :
    cellL w m n d r.val c.val = ∑ j ∈ Finset.range d, w j * (M ^ j) r c := by
  rw [cellL, list_sum_eq_finset_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [powL_getD M m hM]

/-- **The bridge**: the boolean certificate over integer tables gives the matrix
identity `∑_{j<d} w j • M2^j = s • N`. -/
theorem scaled_of_check (d : ℕ) (w wv : ℕ → ℤ) (M2 N : Matrix (Fin n) (Fin n) ℤ)
    (s sv : ℤ) (m t : ℕ → ℕ → ℤ) (hw : ∀ j : Fin d, w j = wv j) (hs : s = sv)
    (hM : ∀ i j : Fin n, M2 i j = m i.val j.val)
    (hN : ∀ i j : Fin n, N i j = t i.val j.val)
    (h : scaledCheck wv m sv t n d = true) :
    (∑ j ∈ Finset.range d, w j • M2 ^ j) = s • N := by
  ext a b
  simp only [scaledCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  rw [Matrix.sum_apply, Matrix.smul_apply, hN, hs, smul_eq_mul,
    ← h a.val a.isLt b.val b.isLt, cellL_eq wv M2 m hM]
  exact Finset.sum_congr rfl fun j hj => by
    rw [Matrix.smul_apply, smul_eq_mul, hw ⟨j, Finset.mem_range.1 hj⟩]

end ScaledCert
