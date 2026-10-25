# MathProof — modular forms open problems in Lean 4

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23636675.svg)](https://doi.org/10.5281/zenodo.23636675)

An autonomous research workspace: each iteration of the loop picks an open
problem connected to modular forms / the Langlands program, and contributes
*formally verified* mathematics toward it using Lean 4 + Mathlib.

See `research/research-log.md` for the full log. Highlights:

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
  `Ramanujan.tau_ne_zero_of_le_65536` (packed-bignum arithmetic: each
  coefficient list packed into one `Nat` in base `2^80`, one GMP `Nat.mul`
  per dense product, entries from Euler's pentagonal number theorem;
  `decide +kernel`) — `τ n ≠ 0` for all `1 ≤ n ≤ 65536`, verified entirely
  inside Lean's kernel (no external CAS, no `native_decide`); the 65536
  check needs ~63 GiB of kernel heap, so it is built on Modal, not in CI.
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

## Hecke operators and Mordell's theorem (`MathProof/ModularForms/HeckeLevelOne.lean`, `MathProof/Tau/Mordell.lean`)

* `HeckeLevelOne.heckeTP` — **the Hecke operator `T_p` on level-one cusp
  forms**, constructed from scratch (`T_p f = p⁻¹ Σ_{j<p} f((τ+j)/p) +
  p^{k-1} f(pτ)`): T- and S-invariance (via an explicit coset factorization
  through the `ZMod p` involution `j ↦ −j⁻¹`), holomorphy, vanishing at the
  cusps, and the q-expansion coefficient formula
  `(T_p f)_m = f_{pm} + p^{k-1} [p ∣ m] f_{m/p}`.
* `Ramanujan.heckeTP_discriminant_eq` — **the eigenform equation**
  `T_p Δ = τ(p) · Δ`: Δ is a Hecke eigenform and its eigenvalue is the
  Ramanujan τ function itself (one-dimensionality of `S₁₂(SL(2, ℤ))` + the
  coefficient bridge).
* `Ramanujan.tau_mul_coprime` — **Mordell's theorem (1917)**
  `τ(mn) = τ(m)τ(n)` for coprime `m, n ≥ 1`, with the companions
  `tau_prime_mul_of_not_dvd`, `tau_prime_pow_succ`
  (`τ(p^{r+2}) = τ(p)τ(p^{r+1}) − p^11 τ(p^r)`), `tau_prime_pow_mul`, and
  the eigenvalue identity `hecke_eigen_identity`.

## Building

```bash
lake build                      # requires ~7 GB disk for Mathlib
lake build MathProof.Tau.Lehmer # the nonvanishing computation (~2 CPU-min kernel time)
```

On a small machine, build remotely instead (see `AGENTS.md`):
```bash
/home/doz/dozenv/bin/modal run lean_build.py --target ''   # light defaults on Modal; heavy modules need explicit --target
```

## Using this library

To use it from another Lean 4 project, require it pinned to a tag (the API
is research code — no stability guarantee between versions):

```toml
# lakefile.toml
[[require]]
name = "MathProof"
git = "https://github.com/picodozbotdoz/math-proof1"
rev = "v0.1.0"
```

```lean
-- or, in a lakefile.lean
require MathProof from git "https://github.com/picodozbotdoz/math-proof1" @ "v0.1.0"
```

A plain `lake build` builds only the light modules, by design — import what
you need: `import MathProof.ModularForms.Congruence691` gives
`RamanujanCongruence.tau_modEq_sigma`, `import MathProof.Tau.Bridge` the
τ↔Δ bridge, and `import MathProof` the whole light set. The heavy
kernel-computation modules (`MathProof.Tau.LehmerMod` ≈ 6 GB,
`MathProof.Tau.LehmerPacked` ≈ 63 GiB of kernel heap) are excluded from the
default targets on purpose — import them directly only on a machine with
the memory to spare.

## Layout

```
MathProof/Tau/Basic.lean        # τ: definition, stability, verified values
MathProof/Tau/Lehmer.lean       # Lehmer's conjecture + verified bound 128
MathProof/Tau/LehmerMod.lean    # mod-P arithmetic: verified bound 512
MathProof/Tau/LehmerPacked.lean # packed-bignum mod-P arithmetic: verified bound 65536
MathProof/Tau/CongruenceSmall.lean  # τ mod 2 and mod 3 gap congruences
MathProof/Tau/Bridge.lean       # (qExpansion Δ).coeff n = τ(n)
MathProof/ModularForms/Weight12.lean       # 691 • E₁₂ = 441 • E₄³ + 250 • E₆²
MathProof/ModularForms/Congruence691.lean  # τ(n) ≡ σ₁₁(n) mod 691
research/research-log.md        # the research loop log
docs/                           # GitHub Pages root: project landing page + interactive Langlands page
research/outreach-kit/          # making this work discoverable: GitHub metadata, Reservoir, Zenodo, Zulip post
```

## License and citation

Released under the Apache License 2.0 (the same license as Mathlib), see
[LICENSE](LICENSE). Citation metadata lives in [CITATION.cff](CITATION.cff)
(rendered by GitHub under "Cite this repository"); connecting the repository
to Zenodo turns each release tag into a versioned DOI.

