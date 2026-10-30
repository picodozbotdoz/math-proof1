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

---
# Wave 3 PR draft (NOT submitted) — Ramanujan's congruence

Branch `tauceti/wave3-tau-congruence-691` (merge of Wave 1 + Wave 2 + commit), file
`TauCeti/NumberTheory/ModularForms/LevelOne/CongruenceMod691.lean`.  **Cannot be opened until Waves 1 and 2 are merged
into TauCeti `main`** (stacked PRs are forbidden); then rebase onto `main` and open standalone.
Content: `ramanujanTau_modEq_sigma : ramanujanTau n ≡ σ₁₁ n [ZMOD 691]` (n ≥ 1) from `E₁₂_qExpansion_rel`
(Wave 2, which now also exports the power-series form of the identity) and TauCeti's existing
`qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq`.  Uses `norm_num` for `Prime 691` (no `set_option`).
Roadmap: ModularForms.

---
# Wave 4 PR drafts (NOT submitted) — Lehmer reduction and sieve

Branch `tauceti/wave4-lehmer` (stack: wave1 → wave3(wave2) → 3 commits).  Real PR order, each standalone on `main`:
1. `LevelOne/TauMultiplicative.lean` (needs W1): `ramanujanTau_one`, `_mul_of_coprime` (Mordell), `_prime_pow_add_two`,
   `_ne_zero_of_prime_pows` — derived from `discriminantEigenform` (no Hecke code ported).  Roadmap: ModularForms (Δ at level one, Prop 5.8.5).
2. `LevelOne/LehmerReduction.lean`: `ramanujanTau_prime_pow_ne_zero` (Lehmer 1947), `ramanujanTau_ne_zero_of_prime_factors`,
   `LehmerConjecture`, `lehmerConjecture_iff_primes`.  **Not on the roadmap**: expect `scope` block unless a human adds a hook.
3. `LevelOne/LehmerSieve691.lean` (needs W3 + 2): sieve `691 ∤ σ₁₁ n → τ n ≠ 0`, `prime_dvd_sigma_iff`,
   `ramanujanTau_prime_ne_zero_of_mod`, all-exponent sieve, root-of-unity classification, `τ(65537^a) ≠ 0`.  Off-roadmap too.
Header/licence/authorship: human decision (see Wave 1 notes).

---
# Wave 5 drafts (NOT submitted) — Bernoulli values, rank-one Lehmer toolkit, weights 16–26

Branch `tauceti/wave5-weights`.  PR order (each standalone on `main` after prerequisites):
1. `NumberTheory/Bernoulli/Values.lean` (independent, ~700 lines of `norm_num` chain — likely `proof-quality` feedback; a shorter generic computation of `bernoulli n` for concrete n would be a worthwhile *Mathlib-level* improvement, `decide +kernel` takes >10 min at n=16).
2. `LevelOne/HeckeRecurrence.lean` + fold into LehmerReduction/TauMultiplicative (wave 4).
3. `LevelOne/RankOneEigenform.lean` (needs only TauCeti `Eigenform`; independent of τ) — natural ModularForms-roadmap fit (generalizes `discriminantEigenform`).
4. `LevelOne/RankOneLehmer.lean` (needs 2, 3).
5. `LevelOne/LehmerWeight{16,18,20,22,26}.lean` — five PRs (or one per weight); need 1, 4, wave 3 (congruence helpers), wave 1/4 (τ).
Roadmap fit: only (3) is plausibly on the ModularForms roadmap; the rest need a hook (H3).

## Audit status (2026-10-30)
Branches `pr01 … pr14` in the local TauCeti clone correspond one-to-one to the drafts above and all pass the Modal audit (build + linters, header, forbidden constructs, axioms). Open PRs strictly sequentially (no stacking).
