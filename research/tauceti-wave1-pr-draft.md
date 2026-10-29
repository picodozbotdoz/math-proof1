# Wave 1 PR draft (NOT submitted) — `ramanujanTau` and the q-expansion of Δ

Local branch: `~/zcode-workdir/tauceti`, `tauceti/wave1-tau-bridge`, one commit, **unpushed**.
File: `TauCeti/NumberTheory/ModularForms/LevelOne/DiscriminantTau.lean` (≈590 lines).

Verified locally (TauCeti pin, Lean v4.36.0-rc1): `lake build` of the module succeeds with the
full linter set, no `set_option`, no `sorry`; both headline theorems depend only on
`propext, Classical.choice, Quot.sound`.  `tauceti-review` has NOT been run (needs a PR number).

## Content
- `ramanujanTau : ℕ → ℤ` — coefficient of `X^(n-1)` in `(∏_{m≤n}(1−X^m))^24 ∈ ℤ[X]` (+ stability lemma `etaPow24_stable`).
- `qExpansion_discriminant_coeff_of_ne_zero`: `(qExpansion 1 Δ).coeff n = ramanujanTau n` (n ≠ 0), `…_coeff_zero`.
- `ramanujanTau_two = -24`, `ramanujanTau_three = 252` (via existing `discriminant_qExpansion_coeff_two/three`).
- Method: Mathlib `discriminant_cuspFunction_eqOn` + exponential coefficient bound (1-norm on ℤ[X]) + power-series uniqueness. Helpers private.

## Suggested PR body
Adds the integer-valued Ramanujan tau function and proves it equals the q-expansion coefficients of
Mathlib's `Δ`, completing the algebraic description of Δ used by the level-one examples in the
ModularForms roadmap (Δ at level one; τ(p) as Hecke eigenvalues).  Complements
`LevelOne/QExpansion` (coefficients 2, 3 via E₄³−E₆²) and `LevelOne/DiscriminantEigenform`.
Ported from the author's standalone project (math-proof1, Apache-2.0-compatible), reworked: list/kernel
machinery dropped, all `set_option` removed.

Roadmap: ModularForms
<!--tauceti-target:v1 {"focus":"ModularForms","id":"LevelOne/DiscriminantTau"}-->

## Before submitting (HUMAN)
1. Intention + claim (roadmap repo issue) — not done.
2. Decide license/attribution wording (math-proof1 licence vs Apache-2.0) and the `Authors` header.
3. `scope`/`reuse` risk: roadmap does not list "integer τ" explicitly; may need roadmap hook.
4. Possibly reduce: public `etaPoly` + stability lemmas could be private.

---
# Wave 2 PR draft (NOT submitted) — Ramanujan's weight-12 identity

Branch `tauceti/wave2-e12-identity` (from `main`, independent of Wave 1), file
`TauCeti/NumberTheory/ModularForms/LevelOne/Weight12Identity.lean` (~150 lines), unpushed.
Content: `E₁₂ := E (k = 12)`, `E₁₂_qExpansion_coeff` (coefficient `(65520/691) σ₁₁(n)`), `E₁₂_rel`:
`691 • E₁₂ = 441 • E₄³ + 250 • E₆²` via Mathlib's `sturm_bound_levelOne_nat`; `bernoulli_twelve` by `decide +kernel`
(the 100-line `bernoulli'` recurrence chain of math-proof1 is not needed).  Linters clean, no `set_option`, axioms
`propext, Classical.choice, Quot.sound`.
Possible overlap check before submit: Mathlib's own PRs on `E₁₂`/Bernoulli evaluations (none in the local master `312e0b7a8e`).
Roadmap: ModularForms (weak fit — Eisenstein congruence example; may hit `scope`).
