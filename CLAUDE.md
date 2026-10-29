# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

@AGENTS.md

`AGENTS.md` (imported above) is the single source of truth for build commands,
the Modal resource policy, the module layout and conventions — update it, not
this file, when those change. The notes below only add cross-file context.

## Proof standard (non-negotiable)

No `sorry`, no `native_decide`, no external CAS. Computational facts are
certified by the kernel alone (`decide` / `decide +kernel`). Computational
theorems must depend on `propext` only; analytic ones may use the standard
three axioms. Audit with:

```bash
tools/modal_run.sh --target MathProof.AxCheck   # Modal account: see AGENTS.md (xyz)
```

Heavy modules (`LehmerPacked`, `LehmerPow32`, `LehmerGrand`) carry their own
`#print axioms` lines at the end of the file instead.

## How the pieces fit together

The results form a pipeline that crosses files:

1. **Algebraic τ** (`Tau/Basic.lean`): τ as coefficients of `q ∏ (1 − q^m)^24`,
   plus kernel-reducible list arithmetic with proven soundness lemmas.
2. **Computation layers**, each a faster kernel-checkable model of the same
   coefficients, proved equal to it: `Lehmer` (over ℤ) → `LehmerMod` (mod
   `P = 999999937`, transported via `ZMod P`) → `LehmerPacked` (base-`2^80`
   packed `Nat`s, pentagonal-number entries; soundness through Mathlib's
   `Pentagonal.PowerSeries`).
3. **Analytic bridge** (`Tau/Bridge.lean`): the algebraic τ equals the
   q-expansion of Mathlib's analytic `Δ`, which unlocks modular-forms theory.
4. **Modular forms** (`ModularForms/`): Weight-12 Eisenstein identity →
   691 congruence; Hecke `T_p` built from scratch → `Tau/Mordell.lean`
   (multiplicativity + prime-power recursion).
5. **Lifting finite checks to infinite families**: `LehmerUnbounded` (Mordell
   lift from prime-power blocks), `PowChain`/`LehmerPow32` (recursion chains
   seeded by `LehmerPacked.tauResList`), `LehmerSieve691` (mod-691 sieve),
   all fused in `LehmerGrand`.

## Light vs heavy modules

A module is *heavy* if it (transitively) imports a large kernel decide:
`LehmerMod`, `LehmerPacked`, `LehmerPow32`, `LehmerPrimePower`, `LehmerGrand`,
`LehmerPrimeGrand`, the `MaedaGalois5` identity chain (`IdBase … Identities`,
`MaedaGalois5`, `MaedaGalois5Weights`; up to ~200 GiB per module) and
`AxCheck` (imports `LehmerMod`).  `Poly5` and `MaedaGalois5Defs` are light. Everything else is light.

When adding a module:
- **light** → add it to all three of `defaultTargets` in `lakefile.toml`,
  the imports in `MathProof.lean`, and `build-args` in
  `.github/workflows/lean_action_ci.yml` (these lists must stay in sync);
- **heavy** → add it to none of them; verify with `lean_check.py --file …`
  (raise `LEAN_CHECK_MEMORY_MIB` if needed) and set `maxHeartbeats` for long
  kernel decides.

## Completing a research iteration

Record it in `research/research-log.md`, update the highlights in
`README.md`, and keep `docs/index.html` in sync (verified τ values must match
`tau_one` … `tau_twenty_one` in `Basic.lean`). `docs/langlands.html` must stay
fully self-contained (no network requests, no CDN).
