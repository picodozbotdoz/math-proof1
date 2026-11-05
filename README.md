# MathProof — modular forms open problems in Lean 4

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23636675.svg)](https://doi.org/10.5281/zenodo.23636675)

An autonomous research workspace: each iteration of the loop picks an open
problem connected to modular forms / the Langlands program, and contributes
*formally verified* mathematics toward it using Lean 4 + Mathlib.

See `research/research-log.md` for the full log, and the
[Discoveries articles](https://picodozbotdoz.github.io/math-proof1/articles/index.html)
(`docs/articles/`) for readable accounts of what was found, what is proved
and what is classical. Highlights:

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
* **Exact verified coverage** (`Ramanujan.uncovered_2p18`,
  `Ramanujan.covered_count_2p18`, in `MathProof/Tau/LehmerCoverageCount.lean`;
  exact study in `research/iteration22/lehmer-coverage/STUDY.md`): counted
  exactly, **`τ n ≠ 0` is verified for 4 291 072 962 of the 4 294 967 295
  indices `1 ≤ n < 2 ^ 32` — 99.9093 %** — the uncovered 3 894 333 indices
  are exactly the multiples (below 2³², each index of at most one) of the
  294 618 primes `≡ −1 [MOD 691]` above 65536, none below 70481 (exactness:
  `70481 ^ 2 > 2 ^ 32`).  The first kernel-verified *count* anchors:
  `badPrimes2p18_filter` kernel-decides the census (285 AP candidates → the
  17 bad primes; the 2²⁰ twin filters 1 423 → 98), and the no-overlap count
  identity is proved structurally (`card_uncoveredSet`), giving
  `uncovered_2p18 = 23` / `covered_count_2p18 = 262 120` of 262 143 and the
  2²⁰ twins 227 / 1 048 348 of 1 048 575.
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
for every level-one weight with `2 ≤ dim S_k ≤ 10`** — `k = 24, 28, 30, 32, 34,
38` (dim 2), `36, 40, 42, 44, 46, 50` (dim 3), `48, 52, 54, 56, 58, 62` (dim 4),
`60, 64, 66, 68, 70, 74` (dim 5) and — via the dimension-generic pipeline of
Iteration 20 (`CharpolyDimN.lean` + `CharpolyEngine` determinant interpolation
+ Rabin certificates, emitted by `tools/gen_maedan.py`) — the 30 further
weights `72 ≤ k ≤ 134` with `6 ≤ dim S_k ≤ 10` (`MaedaDim{6..10}Weights.lean`,
all light modules)
(`MaedaWeightK.charpoly_T2`, `MaedaWeightK.maeda`).  The weights with
`dim S_k ≤ 5` carry the **full symmetric Galois group** (`S₃`, `S₄` and `S₅` for
the cubic, quartic and quintic weights: `MaedaGalois.maeda_galoisK`), and
Iteration 21 extends this to every weight `72 ≤ k ≤ 134`
(`MaedaGaloisDim{6..10}Weights.lean`, `MaedaWeightK.maeda_galois_full`): Dedekind's
theorem in cycle-type form (`FrobeniusCycleType.lean`, through Mathlib's
`IsArithFrobAt` on the root order) turns a factorization mod `ℓ₁` into an
`(n−1)`-cycle and one mod `ℓ₂` into a transposition, and `JordanPrimitive.lean`
gives `Sₙ`.  The quintic `S₅` criterion
(`galActionHom_bijective_of_quintic`: non-square discriminant + rootless `F₂₀`
sextic resolvent) rests on degree-24 polynomial identities in the five roots
that are out of reach for `ring`; they are certified instead by the kernel on
canonical sparse polynomials (`Poly5.lean`, `MaedaGalois5Id*.lean`; heavy,
built on Modal).  E.g. on `S₂₄`, `T₂` has characteristic polynomial
`X² − 1080 X − 20468736`, irreducible (Hecke field `ℚ(√144169)`).  The
weight-generic machinery (`MaedaLevelOne.lean`) reads the matrix of `T₂` off
kernel-computed q-coefficients of the basis `Δ^i E₄^a E₆^b`.

**The `T₃` twin (Iteration 21).**  Maeda's conjecture concerns the Hecke
algebra, not `T₂` specifically.  The Iteration-20 pipeline is
operator-generic (`heckeTPₗ` takes any prime; `charpoly_dimN` any
endomorphism), and Iteration 21 re-ran it for the Hecke operator `T₃`:
`Irreducible (charpoly (T₃ | S_k))` for the same 54 level-one weights —
`MaedaT3Dim{6..10}Weights.lean` for the 30 weights `72 ≤ k ≤ 134` with
`6 ≤ dim S_k ≤ 10` (`MaedaT3WeightK.charpoly_T3`, `MaedaT3WeightK.maeda`;
emitted by `tools/gen_maedan.py --prime 3` from the T₃ coefficient formula
`(T₃ f)_m = f_{3 m} + 3^(k−1) [3 ∣ m] f_{m/3}`, with the extended
coefficient lists of `MaedaCertCExt.lean` — T₃ reads basis coefficients up
to index `3n`), and the stretch file `MaedaT3SmallWeights.lean` for the 24
weights `k ≤ 74` with `2 ≤ dim S_k ≤ 5` through the same dimension-generic
engine.  The census data (`research/iteration20/data/maeda_t3_dim6_10.json`)
cross-checks every T₃ matrix against the Lean-proved T₂ charpolys via
`[M₂, M₃] = 0` per weight.  E.g. on `S₂₄`, `T₃` has characteristic polynomial
`X² − 339480 X − 19020146544`, irreducible.

**The `T₃` Galois twin (Iteration 22).**  `Gal = Sₙ` for the `T₃`
characteristic polynomials too, at every level-one weight with
`2 ≤ dim S_k ≤ 10` — all 54: `MaedaT3GaloisDim{6..10}Weights.lean` for the
30 weights `72 ≤ k ≤ 134` with `6 ≤ dim S_k ≤ 10`
(`tools/gen_galoisfull.py --prime 3`) and `MaedaT3GaloisSmallWeights.lean`
for the 24 weights `k ≤ 74` with `2 ≤ dim S_k ≤ 5` (`--prime 3 --small`;
certificates in both runs pinned to the kernel-verified `P` literals of the
T₃ dim/small files) — all `MaedaT3WeightK.maeda_galois_full`.  The dims 3–5
weights reuse the Iteration-21 assembly unchanged — Frobenius `(n−1)`-cycle
+ transposition certificates with Bézout witnesses (all ℓ ≤ 89 in the small
range; up to ℓ ≈ 8.7·10⁶ in the dim-6…10 range) finished by
`MaedaGaloisFull.bijective_of_frobenius`; the six dim-2 weights carry no
certificate at all — an irreducible quadratic already has `Gal = S₂`
(`MaedaGaloisQuad.bijective_of_quadratic`).  Maeda's conjecture is
thus verified *in full* — irreducibility **and** `Gal = Sₙ` — for both `T₂`
and `T₃` across every level-one weight with `2 ≤ dim S_k ≤ 10`.

### The Hecke algebra is generated by `T₂` (`MathProof/ModularForms/HeckeCommute.lean`, `HeckeGeneratedByT2*.lean`)

* `HeckeCommute.heckeTP_commute` — **the Hecke operators commute at level
  one**: `T_p (T_q f) = T_q (T_p f)` for all primes `p q`, all cusp forms of
  any weight, by twice-unrolling the q-coefficient formula and q-expansion
  injectivity;
* `HeckeGeneratedByT2Weights.heckeTP_mem_spanT2_weightKK` (54 weights,
  every even `24 ≤ k ≤ 134`) — **`T_p` is a polynomial in `T₂`**: for every
  prime `p` there is `Q : ℂ[X]` with `T_p = aeval T₂ Q` on `S_k(SL(2, ℤ))`.
  Over `ℂ` the charpoly is never irreducible, so the upgrade goes through
  cyclicity: `minpoly ℂ T₂ = charpoly T₂` (separability + eigenvalues) and a
  cyclic vector from the PID structure theorem on the `ℂ[X]`-module
  `Module.AEval' T₂`.  **The level-one Hecke algebra is generated by `T₂`
  alone in all 54 verified weights.**

### The witnesses are rational: `T₃ ∈ ℚ[T₂]` (`MathProof/ModularForms/HeckeRational*.lean`)

* `HeckeRational.represents_dimN` — the representation sibling of
  `charpoly_dimN`: the action of any endomorphism `T` on the echelon basis
  is the back-substitution of its q-coefficient table, coordinate by
  coordinate;
* `HeckeRationalWeights.heckeT3_eq_aeval_rat_weightKK` (30 weights,
  `72 ≤ k ≤ 134`) + `HeckeRationalSmallWeights` (24 weights, `k ≤ 74`,
  dims 2–5) — **`T₃` is a polynomial in `T₂` with *rational*
  coefficients**: `∃ Q : ℚ[X], T₃ = aeval T₂ (Q.map (algebraMap ℚ ℂ))` for
  all 54 verified weights, constructively — no cyclicity, no commutativity
  input; an exact integer certificate `∑_{j<n} N_j • M₂^j = D • M₃`
  (kernel-decided entrywise) is the whole proof.  At several small weights
  (24, 28, 30, 32, 34, 38) the witness is an *integer* polynomial
  (e.g. `Q = 195660 − 48·X` at weight 24).  The number-theoretic payoff —
  `T₃`-eigenvalues lie in `ℚ(λ₂)` — is a one-line corollary.

### The Hecke ring `𝕋` (Iteration 23: `HeckeTM`, `HeckeIndex*`, `HeckeField*`)

* `HeckeTM.heckeTM` — `T_m` for **every** `m` (recursive route), with the
  coefficient formula `(T_m f)_n = ∑_{d ∣ (m,n)} d^{k−1} f_{mn/d²}`,
  `heckeTM_one` (`a₁(T_m f) = a_m(f)`), commutation and the full
  multiplicativity `T_m T_n = ∑_{d ∣ (m,n)} d^{k−1} T_{mn/d²}`;
* `HeckeIndex.hecke_dual` — **duality** `T_m = ∑_j a_m(g_j) • T_{j+1}` over
  the Miller basis (proved pointwise from the symmetry
  `a_l(T_m f) = a_m(T_l f)`), `hecke_independent` (`T_1 … T_n` independent),
  and the Hecke ring `heckeRing = span_ℤ {T_1 … T_n}` ⊇ `ℤ[T₂]`;
* `HeckeIndex{Small,}Weights` (54 weights) — the **index**
  `I_k = |det (a_{2^i}(f_j))|` by a certified Bareiss determinant, the
  integer certificate `∑ w′_j T₂^j = I_k • T₃`, and `D ∣ I_k` for the
  reduced denominator `D` of the Iteration-22 witness (48 weights; `D = 1`
  at the six dim-2 weights);
* `HeckeFieldRat.heckeTM_eq_aeval_rat` + `HeckeFieldWeights` — **every
  `T_m ∈ ℚ[T₂]`** at all 54 weights, no per-`m` certificate (Miller-basis
  integrality + Cramer over the integer coordinates of `T₂^i` in `𝕋`), hence
  every `T_m`-eigenvalue of a `T₂`-eigenform lies in `ℚ(λ₂)`
  (`eigen_TM_mem_adjoin_weightKK`);
* `HeckeFieldDim2` — **dim-2 integrality**: at `k = 24, 28, 30, 32, 34, 38`,
  `T_m = a_m(g₁) • 1 + a_m(g₂) • T₂` for every `m ≥ 1`, with the coefficients
  explicit integers (`seqP` values) at 28–38; `MaedaT2GaloisSmallWeights`
  closes `Gal = S₂` for the six dim-2 `T₂` charpolys.

### The Hecke index and ring generators (Iteration 24: `HeckeLatticeIndex`, `HeckeIndexCard*`, `HeckeCyclic*`, `HeckeRingGens*`)

* `HeckeLatticeIndex.relIndex_t2_eq_det` + `HeckeIndexCard{Small,}Weights`
  — the index as an honest **lattice index**: at all 54 weights,
  `[𝕋 : ℤ[T₂]] = |I_k|` (`index_card`, as `AddSubgroup.relIndex`, and
  `index_card_natCard`, as `Nat.card (𝕋 ⧸ ℤ[T₂])`), from the coordinates
  `C i j = a₁(T₂^i g_j)` and `|det C| = |I_k|` (certified `eval_det`);
* `HeckeCyclic` + `HeckeCyclicWeights` — at dims ≤ 4 the quotient
  `𝕋 / ℤ[T₂]` is **cyclic**, so the Iteration-22 denominator is the whole
  index: `D = I_k` at the 12 dims-3–4 weights, hence `𝕋 ≠ ℤ[T₂]` there,
  and `𝕋 = ℤ[T₂]` at the six dim-2 weights;
* `HeckeRingGens` + `HeckeRingGens{Small,}Weights` — **ring generators**:
  `ℤ[T_p : p ∈ ps]` contains every `ps`-smooth `T_m`, so
  `𝕋 = ℤ[T₂, T₃, T₅, T₇]` at every weight with `dim S_k ≤ 10` (all 54,
  certificate-free); `𝕋 = ℤ[T₂, T₃, T₅]` at the 22 weights where it holds
  (free at dims 5–6, one `T₇` row certificate each at ten dims-7–9
  weights); `ℤ[T₂, T₃]` at dims ≤ 4, `ℤ[T₂]` at dim 2.

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
MathProof/Tau/LehmerCoverageCount.lean  # exact coverage: kernel bad-prime census 2^18/2^20 + first kernel-verified counts (23, 227)
MathProof/Tau/CongruenceSmall.lean  # τ mod 2 and mod 3 gap congruences
MathProof/Tau/Bridge.lean       # (qExpansion Δ).coeff n = τ(n)
MathProof/ModularForms/Weight12.lean       # 691 • E₁₂ = 441 • E₄³ + 250 • E₆²
MathProof/ModularForms/EigenLevelOne.lean  # Mordell + Lehmer for any rank-one S_k
MathProof/ModularForms/LehmerWeight*.lean  # weights 16–26: congruences, sieves, initial segments
MathProof/ModularForms/Maeda*.lean         # Maeda's conjecture for 2 ≤ dim S_k ≤ 10 (weights 24–134): irreducibility and full Galois group Sₙ
MathProof/ModularForms/HeckeCommute.lean, HeckeGeneratedByT2*.lean
                                            # Hecke operators commute; T_p is a polynomial in T₂ (Hecke algebra generated by T₂, 54 weights)
MathProof/ModularForms/Poly5.lean          # kernel-checkable sparse polynomials in 5 variables
MathProof/ModularForms/Congruence691.lean  # τ(n) ≡ σ₁₁(n) mod 691
research/research-log.md        # the research loop log
docs/                           # GitHub Pages root: landing page, interactive Langlands page, articles/ (discoveries)
research/outreach-kit/          # making this work discoverable: GitHub metadata, Reservoir, Zenodo, Zulip post
```

## License and citation

Released under the Apache License 2.0 (the same license as Mathlib), see
[LICENSE](LICENSE). Citation metadata lives in [CITATION.cff](CITATION.cff)
(rendered by GitHub under "Cite this repository"); connecting the repository
to Zenodo turns each release tag into a versioned DOI.

