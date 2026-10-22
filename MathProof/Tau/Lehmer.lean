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
`τ n` for `1 ≤ n ≤ 256` is nonzero, where each value is evaluated by Lean's
kernel (`decide`), so the result does not rely on any external computer algebra
system or on the Lean compiler being correct — only on Lean's small trusted
kernel and the axioms of Mathlib.  (All 256 values were also cross-checked
against OEIS A000594.)

## Main statements

* `Ramanujan.deltaCoeffs_256_nonvanishing` : the kernel-level computation.
* `Ramanujan.tau_ne_zero_of_le_256` : `tau n ≠ 0` for `1 ≤ n ≤ 256`.
* `Ramanujan.tau_prime_ne_zero_of_le_256` : in particular `τ p ≠ 0` for every
  prime `p ≤ 256` — i.e. for the first 54 primes.

## Tags

Lehmer's conjecture, Ramanujan tau function, non-vanishing
-/

namespace Ramanujan

/-- Check that all entries of a list at indices `< N` are nonzero. -/
def allNonzeroLt : ℕ → List ℤ → Bool
  | 0, _ => true
  | d + 1, l => (l.getD d 0 != 0) && allNonzeroLt d l

theorem allNonzeroLt_eq_true_iff {N : ℕ} {l : List ℤ} :
    allNonzeroLt N l = true ↔ ∀ i < N, l.getD i 0 ≠ 0 := by
  induction N with
  | zero => simp [allNonzeroLt]
  | succ N ih =>
      simp only [allNonzeroLt, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hN, h⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
        · exact h i h'
        · subst h'; exact hN
      · intro h
        exact ⟨h N (Nat.lt_succ_self N), fun i hi ↦ h i (Nat.lt_succ_of_lt hi)⟩

/-- **Verified non-vanishing of `τ` up to 256.** Every coefficient `τ n` for
`1 ≤ n ≤ 256` is nonzero.  This is checked by Lean's kernel via `decide`,
evaluating the verified list `deltaCoeffs 256`; no external computation is
trusted. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem deltaCoeffs_256_nonvanishing : allNonzeroLt 256 (deltaCoeffs 256) = true := by
  decide

/-- **Lehmer's conjecture** (1947): the Ramanujan tau function never vanishes. -/
def LehmerConjecture : Prop := ∀ n : ℕ, 1 ≤ n → tau n ≠ 0

/-- Every value `τ n` with `1 ≤ n ≤ 256` is nonzero: a formally verified partial
result toward Lehmer's conjecture. -/
theorem tau_ne_zero_of_le_256 {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 256) : tau n ≠ 0 := by
  have h := allNonzeroLt_eq_true_iff.mp deltaCoeffs_256_nonvanishing (n - 1) (by omega)
  change tauOf (n - 1) ≠ 0
  rw [tauOf_eq_getD 256 (n - 1) (by omega)]
  exact h

/-- `τ p ≠ 0` for every prime `p ≤ 256` (the first 54 primes). -/
theorem tau_prime_ne_zero_of_le_256 {p : ℕ} (hp : p.Prime) (hle : p ≤ 256) :
    tau p ≠ 0 :=
  tau_ne_zero_of_le_256 (Nat.Prime.pos hp) hle

end Ramanujan
