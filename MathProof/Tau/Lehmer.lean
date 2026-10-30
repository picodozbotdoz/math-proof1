import MathProof.Tau.Basic

/-!
# Lehmer's conjecture and a verified non-vanishing bound

**Lehmer's conjecture** (1947) asserts that the Ramanujan tau function never
vanishes: `τ n ≠ 0` for all `n ≥ 1` (`Ramanujan.LehmerConjecture`).  It is one of
the oldest open problems in the theory of modular forms.  The best
computer-assisted verifications in the literature (using floating-point /
interval arithmetic outside any proof assistant) show `τ n ≠ 0` up to very large
bounds (well beyond `10 ^ 10`), and it is known (M. R. Murty) that the number of
`n ≤ x` with `τ n = 0` is `O(x / (log x)^{1-ε})`-thin under standard hypotheses;
unconditionally, `τ n ≠ 0` for almost all `n` in a density sense.

This file contributes a *formally verified* computation: every value
`τ n` for `1 ≤ n ≤ 128` is nonzero, where each value is evaluated by Lean's
kernel (`decide`), so the result does not rely on any external computer algebra
system or on the Lean compiler being correct — only on Lean's small trusted
kernel and the axioms of Mathlib.  (All 128 values were also cross-checked
against OEIS A000594.)

## Main statements

* `Ramanujan.deltaCoeffs_128_nonvanishing` : the kernel-level computation.
* `Ramanujan.tau_ne_zero_of_le_128` : `tau n ≠ 0` for `1 ≤ n ≤ 128`.
* `Ramanujan.tau_prime_ne_zero_of_le_128` : in particular `τ p ≠ 0` for every
  prime `p ≤ 128` — i.e. for the first 31 primes.

## Tags

Lehmer's conjecture, Ramanujan tau function, non-vanishing
-/

namespace Ramanujan

/-- Check that all entries of a list at indices `< N` are nonzero.  The test
uses `Int.decEq` explicitly: `!=` on `ℤ` resolves through
`Int.instLinearOrderPackage`, which drags `Classical.choice` into the
certificate below (the proof standard asks `propext` only). -/
def allNonzeroLt : ℕ → List ℤ → Bool
  | 0, _ => true
  | d + 1, l => !(@decide (l.getD d 0 = 0) (Int.decEq _ _)) && allNonzeroLt d l

theorem allNonzeroLt_eq_true_iff {N : ℕ} {l : List ℤ} :
    allNonzeroLt N l = true ↔ ∀ i < N, l.getD i 0 ≠ 0 := by
  induction N with
  | zero => simp [allNonzeroLt]
  | succ N ih =>
      constructor
      · intro h i hi
        rw [allNonzeroLt, Bool.and_eq_true] at h
        obtain ⟨hN, hrest⟩ := h
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
        · exact ih.mp hrest i h'
        · subst h'
          simpa using hN
      · intro h
        rw [allNonzeroLt, Bool.and_eq_true]
        refine ⟨?_, ih.mpr fun i hi ↦ h i (Nat.lt_succ_of_lt hi)⟩
        simpa using h N (Nat.lt_succ_self N)

/-- **Verified non-vanishing of `τ` up to 128.** Every coefficient `τ n` for
`1 ≤ n ≤ 128` is nonzero.  This is checked by Lean's kernel via
`decide +kernel` (the kernel alone evaluates the verified list
`deltaCoeffs 128`; the elaborator-side re-evaluation of plain `decide`
exceeds the default recursion depth); no external computation is trusted. -/
theorem deltaCoeffs_128_nonvanishing : allNonzeroLt 128 (deltaCoeffs 128) = true := by
  decide +kernel

/-- **Lehmer's conjecture** (1947): the Ramanujan tau function never vanishes. -/
def LehmerConjecture : Prop := ∀ n : ℕ, 1 ≤ n → tau n ≠ 0

/-- Every value `τ n` with `1 ≤ n ≤ 128` is nonzero: a formally verified partial
result toward Lehmer's conjecture. -/
theorem tau_ne_zero_of_le_128 {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 128) : tau n ≠ 0 := by
  have h := allNonzeroLt_eq_true_iff.mp deltaCoeffs_128_nonvanishing (n - 1) (by omega)
  change tauOf (n - 1) ≠ 0
  rw [tauOf_eq_getD 128 (n - 1) (by omega)]
  exact h

/-- `τ p ≠ 0` for every prime `p ≤ 128` (the first 31 primes). -/
theorem tau_prime_ne_zero_of_le_128 {p : ℕ} (hp : p.Prime) (hle : p ≤ 128) :
    tau p ≠ 0 :=
  tau_ne_zero_of_le_128 (Nat.Prime.pos hp) hle

end Ramanujan
