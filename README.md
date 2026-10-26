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
* **Toward Lehmer's conjecture** (`Ramanujan.LehmerConjecture`) — now on an
  **unbounded index set** with the **prime-power frontier at 2³²**
  (`Ramanujan.tau_prime_pow_ne_zero_of_le_two_pow_32`,
  `Ramanujan.tau_ne_zero_of_prime_pow_le_two_pow_32`: `τ (p ^ a) ≠ 0` for all
  primes `p ≤ 65536` with `p ^ a ≤ 2 ^ 32`, by kernel-verified Mordell
  recursion chains over `ZMod P` — e.g. `τ 4294967296 = τ(2 ^ 32) ≠ 0`) (`Ramanujan.tau_ne_zero_of_forall_prime_pow`,
  `Ramanujan.tau_ne_zero_of_prime_pow_le_65536`): `τ n ≠ 0` for every `n`
  whose prime-power divisors are all `≤ 65536` — an infinite family
  including all squarefree products of the 6542 primes up to 65536 (indices
  of up to 28 305 digits; e.g. `τ(65519·65521) = τ 4292870399 ≠ 0`), via
  Mordell multiplicativity layered on the kernel-verified bound.
  The kernel-decide bound itself:
  `Ramanujan.tau_ne_zero_of_le_128` (over `ℤ`), `Ramanujan.tau_ne_zero_of_le_512`
  (mod `P = 999999937`, kernel `decide`), and
  `Ramanujan.tau_ne_zero_of_le_65536` (packed-bignum arithmetic: each
  coefficient list packed into one `Nat` in base `2^80`, one GMP `Nat.mul`
  per dense product, entries from Euler's pentagonal number theorem;
  `decide +kernel`) — `τ n ≠ 0` for all `1 ≤ n ≤ 65536`, verified entirely
  inside Lean's kernel (no external CAS, no `native_decide`); the 65536
  check needs ~63 GiB of kernel heap, so it is built on Modal, not in CI.
* **Lehmer's reduction to primes** (`Ramanujan.lehmerConjecture_iff_primes`,
  `Ramanujan.tau_prime_pow_ne_zero`, in `MathProof/Tau/LehmerPrimeReduction.lean`):
  `τ p ≠ 0 → τ (p ^ a) ≠ 0` for every exponent (Lehmer 1947, elementary
  proof — no Deligne bound), so **Lehmer's conjecture is equivalent to
  `τ p ≠ 0` for all primes `p`**.  Consequences: `τ n ≠ 0` for every `n`
  whose prime factors are each `≤ 65536` or `≢ −1 [MOD 691]`, **any
  exponents** (`Ramanujan.tau_ne_zero_of_prime_factors_le_65536_or_mod`;
  e.g. `τ (2 ^ a) ≠ 0` for all `a`), and **`τ n ≠ 0` for every
  `0 < n < 70481`** (`Ramanujan.tau_ne_zero_of_lt_70481`, in
  `MathProof/Tau/LehmerPrimeGrand.lean`) — the first unconditional initial
  segment past the dense bound; `70481` is the least prime `> 65536` with
  `p ≡ −1 [MOD 691]`.
* **The grand fusion** (`Ramanujan.tau_ne_zero_grand`,
  `Ramanujan.tau_ne_zero_of_lt_two_pow_32`, in `MathProof/Tau/LehmerGrand.lean`):
  one theorem consuming every route — `τ n ≠ 0` for every `n` (unbounded)
  whose prime-power divisors are chain-covered (`p ≤ 65536`,
  `p ^ a ≤ 2 ^ 32`) or sieve-covered (`691 ∤ σ₁₁ (p^a)`); in particular
  **every `n < 2 ^ 32` whose prime factors above 65536 avoid the single
  class `−1 [MOD 691]`** (e.g. `τ (2 ^ 32 − 1) ≠ 0`).
* **The mod-691 Lehmer sieve** (`Ramanujan.tau_prime_ne_zero_of_mod`,
  `Ramanujan.tau_ne_zero_of_not_dvd_sigma`): `τ n ≠ 0` whenever
  `691 ∤ σ₁₁ n` — in particular **every prime `p ≢ −1 [MOD 691]` of
  arbitrary size** has `τ p ≠ 0` (e.g. `τ 65537 ≠ 0`, `τ(2³¹ − 1) ≠ 0`),
  `τ(2 ^ a) ≠ 0` for all `a ≤ 64`, and any Lehmer counterexample `n` must
  satisfy `691 ∣ σ₁₁ n`.
* **Small-prime congruences** (`Ramanujan.tau_even_of_ne_one_mod_eight`,
  `Ramanujan.tau_zero_mod_three_of_ne_one_mod_three`): `τ n` is even unless
  `n ≡ 1 [MOD 8]`, and divisible by 3 unless `n ≡ 1 [MOD 3]` — by the
  freshman's dream collapse of the Euler product mod 2 and mod 3.

## Lehmer's question beyond weight 12 (`MathProof/ModularForms/LehmerWeight*.lean`)

`S_k(SL(2, ℤ))` is one-dimensional for `k = 12, 16, 18, 20, 22, 26`.  For each
higher-weight eigenform the whole Lehmer toolkit is formalized once
(`MathProof/ModularForms/EigenLevelOne.lean`: Hecke eigenform, Mordell, Lehmer
reduction to primes), together with a new **formal Ramanujan-type
congruence** and an unconditional initial segment — with no dense
computation:

| eigenform | congruence | coefficient `≠ 0` for all `0 < n <` |
|-----------|------------|--------------------------------------|
| `Δ E₄` (16) | `a ≡ σ₁₅ [ZMOD 3617]` | 21701 (`LehmerWeight16.a16_ne_zero_of_lt_21701`) |
| `Δ E₆` (18) | `a ≡ σ₁₇ [ZMOD 43867]` | 263201 |
| `Δ E₄²` (20) | `a ≡ σ₁₉ [ZMOD 283·617]` | 1746109 |
| `Δ E₄ E₆` (22) | `a ≡ σ₂₁ [ZMOD 131·593]` | 1087561 |
| `Δ E₄² E₆` (26) | `a ≡ σ₂₅ [ZMOD 657931]` | 1315861 |

## Maeda's conjecture (`MathProof/ModularForms/Maeda*.lean`)

Maeda's conjecture (open) says the characteristic polynomial of the Hecke
operator `T₂` on `S_k(SL(2, ℤ))` is irreducible over `ℚ` (with full symmetric
Galois group).  It is now **formally verified, from the Hecke operator itself,
for every level-one weight with `dim S_k ∈ {2, 3}`**: `k = 24, 28, 30, 32, 34,
38` and `36, 40, 42, 44, 46, 50` (`MaedaWeightK.charpoly_T2`,
`MaedaWeightK.maeda`), **including the Galois group** (`S₃` for the cubic weights,
`MaedaGalois.maeda_galoisK`).  E.g. on `S₂₄`, `T₂` has characteristic polynomial
`X² − 1080 X − 20468736`, irreducible (Hecke field `ℚ(√144169)`).  The
weight-generic machinery (`MaedaLevelOne.lean`) reads the matrix of `T₂` off
kernel-computed q-coefficients of the basis `Δ^i E₄^a E₆^b`.

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
MathProof/Tau/LehmerPrimeReduction.lean  # Lehmer's lemma: τ p ≠ 0 → τ(p^a) ≠ 0; conjecture ⇔ primes
MathProof/Tau/LehmerPrimeGrand.lean      # (heavy) τ n ≠ 0 for all n < 70481; any-exponent sieve
MathProof/Tau/CongruenceSmall.lean  # τ mod 2 and mod 3 gap congruences
MathProof/Tau/Bridge.lean       # (qExpansion Δ).coeff n = τ(n)
MathProof/ModularForms/Weight12.lean       # 691 • E₁₂ = 441 • E₄³ + 250 • E₆²
MathProof/ModularForms/EigenLevelOne.lean  # Mordell + Lehmer for any rank-one S_k
MathProof/ModularForms/LehmerWeight*.lean  # weights 16–26: congruences, sieves, initial segments
MathProof/ModularForms/Maeda*.lean         # Maeda's conjecture for dim S_k ≤ 3 (weights 24–50)
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

