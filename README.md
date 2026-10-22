# MathProof — modular forms open problems in Lean 4

An autonomous research workspace: each iteration of the loop picks an open
problem connected to modular forms / the Langlands program, and contributes
*formally verified* mathematics toward it using Lean 4 + Mathlib.

See `docs/research-log.md` for the full log. Highlights:

## The Ramanujan tau function (`MathProof/Tau/`)

* `Ramanujan.tau` — the Ramanujan τ function, defined as the coefficient of
  `q^n` in `Δ = q ∏ (1 - q^m)^24`, with a truncation-stability theorem.
* A *verified-computation bridge* (`Ramanujan.tauOf_eq_getD`,
  `Ramanujan.deltaCoeffs_getD`): kernel-friendly coefficient-list arithmetic
  whose correctness is proved, so τ can be evaluated by Lean's kernel alone.
* `Ramanujan.tau_one` … `Ramanujan.tau_twenty_one` — the first 21 values of
  OEIS A000594, each verified by `decide`.
* **Toward Lehmer's conjecture** (`Ramanujan.LehmerConjecture`):
  `Ramanujan.tau_ne_zero_of_le_256` — `τ n ≠ 0` for all `1 ≤ n ≤ 256`,
  verified entirely inside Lean's kernel (no external CAS, no `native_decide`).

## Eisenstein series (`MathProof/ModularForms/`)

* `RamanujanWeight12.E12_rel` — **Ramanujan's weight-12 identity**
  `691 • E₁₂ = 441 • E₄³ + 250 • E₆²`, proved via the Sturm bound; the
  coefficientwise source of Ramanujan's congruence `τ(n) ≡ σ₁₁(n) (mod 691)`.

## Building

```bash
lake build                      # requires ~7 GB disk for Mathlib
lake build MathProof.Tau.Lehmer # the nonvanishing computation (~2 CPU-min kernel time)
```

## Layout

```
MathProof/Tau/Basic.lean        # τ: definition, stability, verified values
MathProof/Tau/Lehmer.lean       # Lehmer's conjecture + verified bound 256
MathProof/ModularForms/Weight12.lean  # 691 • E₁₂ = 441 • E₄³ + 250 • E₆²
docs/research-log.md            # the research loop log
langlands-site/                 # standalone educational web page (GL₂ Langlands by example)
```

---
*The original GitHub-Pages setup instructions (kept for reference): under
Settings → Actions, allow GitHub Actions to create pull requests; under
Settings → Pages, set Source to "GitHub Actions".*
