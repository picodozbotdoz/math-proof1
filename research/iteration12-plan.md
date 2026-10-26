# Iteration 12 plan — Lehmer's reduction to primes (resumable state)

Crash-resilience: this file is the checkpoint.  Each stage lists its status;
a resumed run continues from the first stage not marked DONE.

## Problem

Iterations 8–11 reduce Lehmer nonvanishing to *prime powers* `τ(p^a) ≠ 0`,
covered by chains only up to `p^a ≤ 2^32` (LehmerPow32, 144 GiB).  Lehmer
(1947) showed the minimal counterexample is prime: `τ p ≠ 0 → τ (p^a) ≠ 0`.
Formalizing that removes the exponent cap everywhere and makes the conjecture
a statement about primes only.

## Proof sketch (no Deligne needed)

`u a = τ(p^a)`, `u (a+2) = t u (a+1) − p^11 u a`, `t = τ p ≠ 0`.
* If `p^6 ∤ t`: `t = p^v s`, `v ≤ 5`, `p ∤ s`.  Induction:
  `u a = p^(a v) w`, `w ≡ s^a [ZMOD p]` (since `11 − 2v ≥ 1`), so `u a ≠ 0`.
* If `p^6 ∣ t`: `p ≥ 5` (τ 2 = −24, τ 3 = 252), so `t² ≥ p^12 ≥ 4 p^11`, and
  the sequence is sign-monotone: `0 < u a`, `t u a ≤ 2 u (a+1)` (t > 0;
  t < 0 via `(−1)^a u a`).

## Stages

1. [DONE] `MathProof/Tau/LehmerPrimeReduction.lean` (light): recurrence lemmas,
   `tau_prime_pow_ne_zero`, `tau_ne_zero_of_prime_factors`,
   `lehmerConjecture_iff_primes`, sieve upgrade
   (`p % 691 ≠ 690` for all prime factors ⇒ `τ n ≠ 0`, any exponents),
   parametric initial-segment lemma.  Register as light (lakefile, root, CI).
2. [DONE: 481 s / 62.85 GiB] `MathProof/Tau/LehmerPrimeGrand.lean` (heavy, needs LehmerPacked
   ~63 GiB): every `n` whose prime factors are `≤ 65536` or `≢ −1 [MOD 691]`;
   initial segment `τ n ≠ 0` for all `0 < n < 70481` (70481 = least prime
   `> 65536` with `p ≡ −1 [MOD 691]`; candidates 65644 … 69790 composite).
3. [ ] (decided → next iteration) Generalized Lehmer for the other
   one-dimensional level-one eigenforms `Δ·E_{k−12}`, k ∈ {16,18,20,22,26}:
   `HeckeLevelOne` is weight-generic; Mathlib has `discriminantEquiv`
   (`S_k ≃ M_{k−12}`), rank-one `M_4`, `M_6`, `dimension_level_one`, and
   `sturm_bound_levelOne` at any weight.  Plan: integer coefficients
   `τ_k = τ ⋆ e_{k−12}`, eigen recursion with `p^(k−1)`, generalized prime
   lemma (exponent `k−1` odd), sieve mod the `B_k` numerator primes
   (3617, 43867, 283·617, 131·593, 657931), small kernel bound.
   (Extra τ sieves mod 2,3,5,7 from pure Eisenstein identities only reach
   τ mod 4 — checked: `1800 τ = 691σ₃ + 1382σ₇ − 273σ₁₁ + 331680 S₃₇`;
   the deep ones need Ramanujan's θ, now in Mathlib's `RamanujanFormula`.)
4. [DONE] Log / README / docs / AGENTS.md layout; commit.
