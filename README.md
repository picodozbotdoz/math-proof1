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
  `Ramanujan.tau_ne_zero_of_le_128` (over `ℤ`), `Ramanujan.tau_ne_zero_of_le_512`
  (mod `P = 999999937`, kernel `decide`), and
  `Ramanujan.tau_ne_zero_of_le_16384` (packed-bignum arithmetic: each
  coefficient list packed into one `Nat` in base `2^80`, one GMP `Nat.mul`
  per dense product, entries from Euler's pentagonal number theorem;
  `decide +kernel`) — `τ n ≠ 0` for all `1 ≤ n ≤ 16384`, verified entirely
  inside Lean's kernel (no external CAS, no `native_decide`); the 16384
  check needs ~16 GiB of kernel heap, so it is built on Modal, not in CI.
* **Small-prime congruences** (`Ramanujan.tau_even_of_ne_one_mod_eight`,
  `Ramanujan.tau_zero_mod_three_of_ne_one_mod_three`): `τ n` is even unless
  `n ≡ 1 [MOD 8]`, and divisible by 3 unless `n ≡ 1 [MOD 3]` — by the
  freshman's dream collapse of the Euler product mod 2 and mod 3.

## Eisenstein series and the 691 congruence (`MathProof/ModularForms/`)

* `RamanujanWeight12.E12_rel` — **Ramanujan's weight-12 identity**
  `691 • E₁₂ = 441 • E₄³ + 250 • E₆²`, proved via the Sturm bound.
* `Ramanujan.qExpansion_discriminant_coeff` (in `MathProof/Tau/Bridge.lean`) —
  **the Fourier coefficients of the modular discriminant are the Ramanujan τ
  numbers**: `(qExpansion 1 Δ).coeff n = τ(n)`, connecting the algebraic
  definition to Mathlib's analytic Δ.
* `RamanujanCongruence.tau_modEq_sigma` — **Ramanujan's congruence**
  `τ(n) ≡ σ₁₁(n) [ZMOD 691]` for all `n ≥ 1`, combining the weight-12
  identity, Jacobi's identity `E₄³ − E₆² = 1728 Δ`, integrality of the
  Eisenstein coefficients, and the bridge.

## Building

```bash
lake build                      # requires ~7 GB disk for Mathlib
lake build MathProof.Tau.Lehmer # the nonvanishing computation (~2 CPU-min kernel time)
```

On a small machine, build remotely instead (see `AGENTS.md`):
```bash
/home/doz/dozenv/bin/modal run lean_build.py --target ''   # full project on Modal
```

## Layout

```
MathProof/Tau/Basic.lean        # τ: definition, stability, verified values
MathProof/Tau/Lehmer.lean       # Lehmer's conjecture + verified bound 128
MathProof/Tau/LehmerMod.lean    # mod-P arithmetic: verified bound 512
MathProof/Tau/LehmerPacked.lean # packed-bignum mod-P arithmetic: verified bound 16384
MathProof/Tau/CongruenceSmall.lean  # τ mod 2 and mod 3 gap congruences
MathProof/Tau/Bridge.lean       # (qExpansion Δ).coeff n = τ(n)
MathProof/ModularForms/Weight12.lean       # 691 • E₁₂ = 441 • E₄³ + 250 • E₆²
MathProof/ModularForms/Congruence691.lean  # τ(n) ≡ σ₁₁(n) mod 691
docs/research-log.md            # the research loop log
langlands-site/                 # standalone educational web page (GL₂ Langlands by example)
```

---
*The original GitHub-Pages setup instructions (kept for reference): under
Settings → Actions, allow GitHub Actions to create pull requests; under
Settings → Pages, set Source to "GitHub Actions".*
