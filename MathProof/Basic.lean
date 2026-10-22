import Mathlib.Tactic

/-!
# MathProof

A Lean 4 + Mathlib playground for math proofs.
-/

def hello := "world"

-- Algebraic identities, proved by Mathlib's `ring` tactic
example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring

-- Arithmetic evaluation via `norm_num`
theorem two_plus_two : 2 + 2 = 4 := by norm_num

-- Inequality reasoning via `linarith`
example (a b : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ 3) : a + 1 < 5 := by linarith
