# TauCeti port — review report

Status as of 2026-10-30. For human review; companion to the working checklist
[`tauceti-port-plan.md`](tauceti-port-plan.md).  Nothing has been sent, posted, filed or pushed anywhere:
no Zulip post, no `[Intention]` issue, no roadmap PR, no TauCeti PR (all **HUMAN** steps are untouched).

Sources examined (local clones, read-only): TauCeti `821b7239` (Lean `v4.36.0-rc1`),
TauCetiRoadmap, Mathlib `312e0b7a8e` (Lean `v4.36.0-rc2`, `module`-system files),
TauCeti `AGENTS.md`, `COORDINATION.md`, TauCetiReview `rubrics/README.md`.

## 1. What we have (math-proof1, 56 modules, ≈70 k lines)

| Group | Modules | Content |
|---|---|---|
| Algebraic τ | `Tau/Basic` | τ as coefficients of `q∏(1−qᵐ)²⁴`, kernel-friendly list arithmetic, `tau_one … tau_twenty_one` |
| Analytic bridge | `Tau/Bridge` | `(qExpansion 1 Δ).coeff n = τ n` for Mathlib's Δ |
| Weight 12 / 691 | `Weight12`, `Congruence691` | `691•E₁₂ = 441•E₄³ + 250•E₆²` (Sturm bound), `τ n ≡ σ₁₁ n [ZMOD 691]` |
| Hecke theory | `HeckeLevelOne`, `Mordell`, `EigenLevelOne` | `T_p` built from scratch on level one, Δ eigenform, Mordell multiplicativity and `τ(p^{r+1})` recurrence, weight-generic rank-one eigenforms |
| Lehmer (light) | `LehmerPrimeReduction`, `LehmerUnbounded`, `LehmerSieve691`, `CongruenceSmall`, `PowChain`, `Lehmer` | τ(p)≠0 ⇒ τ(p^a)≠0, reduction to primes, mod-691 sieve, gaps mod 2/3, τ≠0 for n ≤ 128 |
| Lehmer (heavy) | `LehmerMod`, `LehmerPacked`, `LehmerPow32`, `LehmerPrimePower`, `LehmerGrand`, `LehmerPrimeGrand` | τ≠0 for n ≤ 65536 and every n < 2³² avoiding −1 mod 691, by kernel `decide` (≤143 GiB) |
| Other weights | `BernoulliHigh`, `LehmerWeight{16,18,20,22,26}` | B₁₃…B₂₆, Lehmer-type results for Δ·E_{k−12} |
| Maeda | `MaedaWeight24`, `MaedaLevelOne`, `MaedaSmallWeights`, `MaedaGalois`, `MaedaDim{4,5}(+Weights)`, `MaedaGalois4`, `MaedaCertC`, `HornerCert`, `Poly5`, `MaedaGalois5*` (9 modules) | Maeda's conjecture for all level-one weights with dim S_k ∈ {2,3,4,5}, Galois groups S₃/S₄/S₅ via kernel certificates |
| Audit | `AxCheck*`, `MaedaGalois5AxCheck` | `#print axioms` / decide-certificate audits |

All proofs are `sorry`-free, no `native_decide`, computational facts propext-only.

## 2. What TauCeti / Mathlib already cover

| Our item | Upstream status | Where |
|---|---|---|
| Δ definition, product formula, `qExpansion Δ` coeff 1 | **In Mathlib** | `Mathlib/NumberTheory/ModularForms/Discriminant.lean` (`discriminant_eq_q_prod`, `discriminant_qExpansion_coeff_one`) |
| Level-one dimension formula, `S₁₂` rank 1, `Δ·M_{k−12}` | **In Mathlib** | `ModularForms/LevelOne/DimensionFormula.lean`, `GradedRing.lean` |
| Δ coefficients τ(2)=−24, τ(3)=252 (via `(E₄³−E₆²)/1728`) | **In TauCeti** | `NumberTheory/ModularForms/LevelOne/QExpansion.lean` |
| Hecke operators `T_n` at **all levels**, diamond operators, `U_p`, recurrence | **In TauCeti** (supersedes `HeckeLevelOne`) | `NumberTheory/ModularForms/HeckeSlash/*`, `DiamondOperators.lean`, `HeckeRing/*` |
| Eigenforms / newforms, multiplicativity of coefficients | **In TauCeti** (supersedes `EigenLevelOne`) | `Eigenform.lean`, `Newforms/Coefficient.lean` |
| Δ is a Hecke eigenform; `a_{mn}=a_m a_n` coprime; `a_{p^{r+2}}` recurrence; `T₂Δ=−24Δ` | **In TauCeti** (supersedes `Mordell`) | `LevelOne/DiscriminantEigenform.lean` (`discriminant_qExpansion_coeff_mul`, `…_prime_pow_add_two`, `heckeTCuspNat_discriminant_two`) |
| Sturm bound | **In TauCeti**; level one also in Mathlib | `SturmBound.lean` |
| Valence formula, Atkin–Lehner–Li, Euler product, coefficient field is a number field, modular symbols, level-one trace formula (partial) | In TauCeti (roadmap targets) | `ModularForms/*` — not part of our work |
| `bernoulli 4`, `bernoulli 6` by `decide +kernel` | TauCeti has them **privately**; Mathlib does same inline | `LevelOne/QExpansion.lean`, `DimensionFormula.lean` |

Duplicated work to retire (none of it should be PR'd): `HeckeLevelOne` (938 lines), `Mordell` (239),
`EigenLevelOne` (270).  Local value is only as an independent cross-check (the project's proofs were
built from scratch rather than via Mathlib's modular-form API).

## 3. What is not covered upstream (candidate content)

Verified by grepping both trees for τ, Ramanujan, 691, E₁₂, Lehmer, Maeda, `bernoulli 8…26`: **no hits** beyond the table above.

| Item | Novelty | Port difficulty | Roadmap fit |
|---|---|---|---|
| **A2/A3** integer-valued `τ`, full product-expansion coefficients ⇒ `(qExpansion 1 Δ).coeff n = τ n` | New (TauCeti only has coeffs 2, 3 via `E₄³−E₆²`) | Medium; list/kernel part is not needed upstream, the clean version is `ℤ[[q]]` product ↔ `qExpansion` | Plausible (ModularForms roadmap names "Δ at level one … τ(p) are its Hecke eigenvalues" and the coefficient field as ℚ) |
| **A4** `691•E₁₂ = 441•E₄³+250•E₆²` | New | Low–medium; can be redone via Mathlib dimension formula (dim M₁₂=2) instead of our Sturm argument | Weak — nothing in roadmap on Eisenstein congruences |
| **A5** `τ n ≡ σ₁₁ n [ZMOD 691]` | New | Low once A3/A4 land | Weak–medium (classical Eisenstein-congruence example, D–S) |
| **A9–A11** Lehmer prime reduction, any-exponent sieve, mod-691 sieve | New | Low (mostly arithmetic of a recurrence); re-base on `discriminantEigenform` | **Off-roadmap** |
| **A12** `BernoulliHigh` (B₁₃…B₂₆) | New | Medium; the `decide` on WF `bernoulli` is the known pain | Off-roadmap unless a consumer needs it |
| **B** `LehmerWeight*` | New | Medium; need A8-equivalent for rank-one `S_k` (TauCeti `Eigenform` may suffice) | Off-roadmap |
| **B** Maeda family, Galois S₃/S₄/S₅ | New | High; heavy kernel certificates, generated files | Off-roadmap; incompatible with the "no `set_option`" rule as built |
| **C** `LehmerMod/Packed/Pow32/Grand/PrimeGrand/PrimePower`, `MaedaGalois5*` | New | Cannot port | Violates the `maxHeartbeats`/resource rules |

## 4. Rules that shape the merge plan

From `AGENTS.md`/`COORDINATION.md`/TauCetiReview:
- **Scope gate.** Rubric `scope` ("is the PR on the roadmap and limited to a single topic?") **can block**.  New mathematics must advance a roadmap target or supply a prerequisite; improvements to existing code are always in scope.  Hence Lehmer/Maeda/691 are at real risk of `block` unless a human gets them added to a roadmap.
- Other blocking rubrics: `correctness`, `reuse` (outright duplication — directly relevant to Hecke/Mordell), `attribution` (credit sources).  Non-blocking: api-design, generality, placement, naming, documentation, proof-quality.
- **No** `set_option` (kills our 69 `maxHeartbeats`, 12 `maxRecDepth`), no `#eval`/`native_decide`/`sorry`, no direct Lean/Lake/Std imports, linters on, no compat shims.
- One topic per PR; **no stacked PRs** (wait for merge, rebase); PR body line `Roadmap: <Area>`; agents never open PRs/issues in TauCetiRoadmap.
- Coordination (cooperative): register `[Intention]` in the roadmap repo's issue tracker (or project-intentions), comment `claim` (30-day default TTL, 90 max); PR with `Closes #<issue>` refreshes the claim.  Authoring marker `<!--tauceti-target:v1 {"focus":"ModularForms","id":"…"}-->` in the PR body.  Branch updates only with `--force-with-lease`.
- Mathlib: TauCeti tracks `master`; local `master` is already `rc2` + `module` syntax — ports must follow the `module` / `public import` style used in TauCeti files.

## 5. Merge / PR plan

**Principle.** Port only what is both *new* and *defensible under `scope`*; everything else stays in math-proof1 and is linked, not upstreamed.

| Wave | PR (one topic each, sequential, no stacking) | Roadmap line | Gate |
|---|---|---|---|
| 0 (human) | Zulip question + `[Intention]` + `claim` for the narrow target set below | — | Human answers; if roadmap owners decline Lehmer/691, skip Waves 2+ |
| 1 | **τ and the Δ coefficient bridge**: define `τ : ℕ → ℤ` (or reuse `discriminant_qExpansion_coeff`), prove `(qExpansion 1 Δ).coeff n = τ n` from the product, τ(1..N) examples; replace our list machinery by `PowerSeries ℤ` product | `Roadmap: ModularForms` | Needs Mathlib-style rewrite of Basic/Bridge, ~700 lines → likely 2 PRs (integers/product; bridge) |
| 2 | **E₁₂ identity** (via Mathlib dim formula) | `ModularForms` | Wave 1 merged |
| 3 | **τ ≡ σ₁₁ mod 691** | `ModularForms` | Wave 2 merged |
| 4 | **Lehmer prime reduction + sieve** on top of `discriminantEigenform` | `none` is not allowed for new math → needs a roadmap hook | Human-approved roadmap item (else drop) |
| 5 | Optional: `BernoulliHigh`, `LehmerWeight*` | needs hook | Same |
| — | Maeda, heavy Lehmer, `MaedaGalois5*` | not upstreamed | Stay in math-proof1; README cross-links |

Wave 1–3 code must be rebuilt against TauCeti's Mathlib pin; the machine here (7 GiB RAM, 4 cores) can build single light modules once the Mathlib cache is fetched, but Modal runs can only target this repo (no new Modal plumbing is allowed), so the compile-check of ported code is **local**.  Needs your approval to `lake exe cache get` in `~/zcode-workdir/tauceti` (≈7 GB download).

## 6. Risks and decisions for you

1. **Scope blocks.** Biggest risk; only a human can fix it (roadmap PR/Zulip).
2. **Duplicate retirement.** Confirm you accept dropping `HeckeLevelOne`/`Mordell`/`EigenLevelOne` from the upstream plan.
3. **Mathlib drift.** `rc2` + `module` files; our code uses the older style; ports are rewrites more than copies.
4. **Local build.** OK to download the Mathlib cache (≈7 GB) into the TauCeti clone?
5. **Keep math-proof1 frozen** while porting: ancestor edits retrigger the ≈33 min heavy chain.

## 7. Audit of the PR branch chain (2026-10-30)

Fourteen cumulative local branches `pr01 … pr14` in the TauCeti clone (Bernoulli values, weight-12 identity, τ bridge, mod-691, multiplicativity, Lehmer reduction, sieve, rank-one eigenform, rank-one Lehmer, weights 16/18/20/22/26). Each file passes, on Modal image `tauceti-check` (TauCeti `821b723`): build with all linters, header style, forbidden-construct greps, ≤1000 lines, standard axioms only. Open for you: `Authors:` placeholder, scope risk (see §4), and that TauCeti's own CI scripts were not run locally. Nothing pushed.
