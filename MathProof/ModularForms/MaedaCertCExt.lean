import MathProof.ModularForms.MaedaCertC

/-!
# Extended coefficient lists (`N ≤ 31`) for the T₃ Maeda certificates

`MaedaCertC.seqPLc` reads the q-coefficients of `Δ` from `tauTable` (indices
0–21), which caps its transfer lemma `seqPLc_eq` at `N ≤ 22` — enough for the
T₂ weight files (`N = 2n + 1 ≤ 21` at dim 10).  The T₃ coefficient formula
`(T₃ f)_m = f_{3 m} + 3^(k-1) [3 ∣ m] f_{m/3}` reads basis coefficients up to
index `3n = 30`, i.e. `N = 3n + 1 = 31` at dim 10.

This module extends the table to `τ 30` (each new value kernel-verified
against `Ramanujan.tau`, exactly as `tau_one … tau_twenty_one` are) and
mirrors `seqPLc` / `seqPLc_eq` with the cap `N ≤ 31`.  Kept in its own module
so that no ancestor of the heavy `MaedaGalois5` chain is edited.
-/

open UpperHalfPlane ModularForm CuspForm Polynomial
open scoped MatrixGroups

namespace MaedaLevelOne

/-! ### The τ values 22 … 30 -/

theorem tau22 : Ramanujan.tau 22 = -12830688 := by
  change Ramanujan.tauOf 21 = -12830688
  rw [Ramanujan.tauOf_eq_getD 22 21 (by omega)]; decide

theorem tau23 : Ramanujan.tau 23 = 18643272 := by
  change Ramanujan.tauOf 22 = 18643272
  rw [Ramanujan.tauOf_eq_getD 23 22 (by omega)]; decide

theorem tau24 : Ramanujan.tau 24 = 21288960 := by
  change Ramanujan.tauOf 23 = 21288960
  rw [Ramanujan.tauOf_eq_getD 24 23 (by omega)]; decide

theorem tau25 : Ramanujan.tau 25 = -25499225 := by
  change Ramanujan.tauOf 24 = -25499225
  rw [Ramanujan.tauOf_eq_getD 25 24 (by omega)]; decide

theorem tau26 : Ramanujan.tau 26 = 13865712 := by
  change Ramanujan.tauOf 25 = 13865712
  rw [Ramanujan.tauOf_eq_getD 26 25 (by omega)]; decide

theorem tau27 : Ramanujan.tau 27 = -73279080 := by
  change Ramanujan.tauOf 26 = -73279080
  rw [Ramanujan.tauOf_eq_getD 27 26 (by omega)]; decide

theorem tau28 : Ramanujan.tau 28 = 24647168 := by
  change Ramanujan.tauOf 27 = 24647168
  rw [Ramanujan.tauOf_eq_getD 28 27 (by omega)]; decide

theorem tau29 : Ramanujan.tau 29 = 128406630 := by
  change Ramanujan.tauOf 28 = 128406630
  rw [Ramanujan.tauOf_eq_getD 29 28 (by omega)]; decide

theorem tau30 : Ramanujan.tau 30 = -29211840 := by
  change Ramanujan.tauOf 29 = -29211840
  rw [Ramanujan.tauOf_eq_getD 30 29 (by omega)]; decide

/-! ### The extended table -/

/-- `τ 22, …, τ 30` (the suffix extending `tauTable` to index 30). -/
def tauTableExt : List ℤ :=
  [-12830688, 18643272, 21288960, -25499225, 13865712, -73279080, 24647168,
    128406630, -29211840]

/-- `τ 0, …, τ 30` (with the convention `0` at index `0`), each value
kernel-verified (`tau_one … tau_twenty_one` and `tau22 … tau30` above). -/
def tauTableX : List ℤ := tauTable ++ tauTableExt

/-- The q-coefficients of `Δ`, read from `tauTableX` up to index 30 (so that
concrete coefficients stay kernel-computable one truncation further than
`dCc`). -/
def dCc3 (m : ℕ) : ℤ := tauTableX.getD m 0

lemma tauTable_length : tauTable.length = 22 := by decide

lemma dCc3_eq_dC {m : ℕ} (hm : m ≤ 30) : dCc3 m = dC m := by
  have h22 : tauTable.length = 22 := tauTable_length
  rcases Nat.lt_or_ge m 22 with h | h
  · rw [dCc3, dC, tauTableX, List.getD_append _ _ _ _ (by omega)]
    split
    · rfl
    · next h1 => exact absurd h1 (by omega)
  · rw [dCc3, dC, tauTableX, List.getD_append_right _ _ _ _ (by omega)]
    split
    · next h1 => exact absurd h1 (by omega)
    · interval_cases m <;>
        simp [h22, tauTableExt, tau22, tau23, tau24, tau25, tau26, tau27, tau28, tau29,
          tau30]

lemma lst_dCc3 {N : ℕ} (hN : N ≤ 31) : lst dCc3 N = lst dC N := by
  refine List.map_congr_left fun n hn => ?_
  rw [List.mem_range] at hn
  exact dCc3_eq_dC (by omega)

lemma cpowLc_dCc3 {N : ℕ} (hN : N ≤ 31) (m : ℕ) : cpowLc dCc3 N m = cpowL dC N m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [cpowLc, cpowL, ih, convLc_eq, lst_dCc3 hN]

/-- `seqPL` without `Finset`, `ArithmeticFunction` or `Ramanujan.tau`, for
truncations up to `N ≤ 31` (the T₃ files need `N = 3n + 1`). -/
def seqPLc3 (i a b N : ℕ) : List ℤ :=
  convLc (lst dCc3 N) (convLc (cpowLc dCc3 N i) (convLc (cpowLc e4c N a) (cpowLc e6c N b)))

lemma seqPLc3_eq {i a b N : ℕ} (hN : N ≤ 31) : seqPLc3 i a b N = seqPL i a b N := by
  rw [seqPLc3, seqPL, lst_dCc3 hN, cpowLc_dCc3 hN, cpowLc_eq, cpowLc_eq, e4c_eq, e6c_eq,
    convLc_eq]

end MaedaLevelOne
