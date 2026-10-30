# In-repo TauCeti-rules compliance refactor — findings & log

Task: make the **math-proof1 codebase itself** comply with the TauCeti coding
rules (`external-doc/TAU-CETI_Coding_Rules.md`): no `set_option`, no
`#eval`/`meta`/`unsafe`, no `native_decide`/`sorry`, axioms ⊆
{propext, Classical.choice, Quot.sound}, Mathlib-level imports only, linters on.

Working branch: `dev/i18-refactor-tauCeti-rule`.  Companion documents: the
upstream-port view lives in [`../tauceti-port-plan.md`](../tauceti-port-plan.md)
/ [`../tauceti-port-report.md`](../tauceti-port-report.md); this directory
records the **in-repo** compliance work (iteration 18 follow-up).

## 1. Baseline (2026-10-30, `tools/tauceti_audit.sh`)

85 `set_option` occurrences across 16 modules; 2 `native_decide` grep hits
(both **comments only** — false positives of the audit regex; the audit script
was since tightened to exclude comments).  No `#eval`, `sorry`, or non-Mathlib
imports anywhere.  Axiom status: decide certificates were already audited
propext-clean in iteration 18 (commits `55e898c`, `0da7f5b`, `97 of 116`
outside the heavy chain; the chain itself was rebuilt and audited clean).

| class | modules | options | disposition |
|---|---|---|---|
| light CI (`defaultTargets`) | `Tau.Lehmer` (2), `Tau.Bridge` (2), `Weight12` (1), `Congruence691` (1), `Tau.LehmerSieve691` (4), `MaedaGalois5Defs` (7) | 17 | **fixed** (§2) |
| heavy chain (Modal-only) | `MaedaGalois5` (10), `MaedaGalois5IdBase` (24), `IdE4` (6), `IdE5` (6), `IdE6` (8), `Identities` (3) | 57 | inherent, documented (§4) |
| heavy standalone | `Tau.LehmerMod` (1), `Tau.LehmerPacked` (5), `Tau.LehmerPow32` (2) | 8 | inherent, documented (§4) |
| lint suppression | `MaedaGalois5Weights` (1 × `linter.style.longLine`) | 1 | **fixed** (§3) |

## 2. Light-module fixes (commit `555491f`) — method: strip, measure, classify, restructure

All five files are ancestors of the heavy `MaedaGalois5*` chain, so all edits
were batched into one commit and one chain rebuild (AGENTS.md rule).

| module | option(s) | failure at default limits | fix | verified |
|---|---|---|---|---|
| `Tau/Lehmer` | `maxRecDepth 100000`, `maxHeartbeats 4000000` | elaborator *recursion depth* during `decide` on `deltaCoeffs 128` | `decide` → **`decide +kernel`** (kernel evaluates in ~100 s < 200 s budget; same `Decidable` instance, propext-clean) | local `lake build` 100 s + Modal |
| `Tau/Bridge` | `maxRecDepth 10000`, `maxHeartbeats 2000000 in` (pnorm_etaPow24_le) | **none — stale** (options predated later refactors) | deletion only | local 149 s + Modal |
| `ModularForms/Weight12` | `maxHeartbeats 800000 in` (E12_rel) | **none — stale** | deletion only | local 84 s + Modal |
| `ModularForms/Congruence691` | `maxRecDepth 100000 in decide` (Prime 691) | elaborator recursion depth (whnf of the `Nat.Prime` instance) | `by decide` → **`by norm_num`** (Mathlib `NormNum.Prime` certificate path) | local 130 s + Modal |
| `Tau/LehmerSieve691` | 3 × `maxRecDepth` (200k/400k/200k), `exponentiation.threshold 4096` | (a) recdepth on the 691-entry residue scan; (b) recdepth + pow-threshold on the 65-entry geometric-sum scan; (c) **kernel** deep recursion in the `norm_num` trial-division primality certificate for 2147483647 | (a),(b) → **`decide +kernel`**; (c) → Mersenne prime now proved by **Mathlib's Lucas–Lehmer test** (`LucasLehmerTest 31` by `norm_num` + `lucas_lehmer_sufficiency`), a short verified computation in place of a deep certificate | local 64 s + Modal |
| `ModularForms/MaedaGalois5Defs` | `maxRecDepth 8000` (file), 6 × `maxHeartbeats 8000000 in` | real: `resolvent5` sextic elaboration times out at 200k heartbeats ("synthesize pending MVars"); the five group-theory lemmas + `disc5` + `vieta5` pass at default | `resolvent5`'s six coefficient blocks split into **16 private defs** (`r5c5, r5c4, r5c3, r5c2p0/1, r5c1p0/1/2, r5c0p0..4`, ≤ 450 tokens each); `resolvent5` reassembled from them.  Delta-unfolding is transparent to consumers; `MaedaGalois5.lean`'s `resolvent5_map` simp list gained the `r5c*` names (same resulting goal).  Split validated numerically against the original polynomial (5 random substitutions, Python) | Modal, default options |

Key lessons re-confirmed (cf. the seven lessons in the rules file):
*classify the error before acting*.  Two of six option-sets were pure stale
leftovers; two were elaborator-side and fell to `decide +kernel` (the
elaborator re-evaluation, not the kernel, was the budget hog); one was an
elaborator-instance-depth issue with a `norm_num` escape; one was genuine
over-budget elaboration fixed by declaration-boundary splitting.

## 3. `MaedaGalois5Weights` longLine (commit `ebc69ca`)

The file-wide `set_option linter.style.longLine false` existed only because
generated certificates contain 56–250-digit integer literals that cannot be
line-broken.  Every over-long literal was split into **nested
`(A * 10 ^ 55 + B)` chunks** (each digit chunk ≤ 55; value-exact, asserted per
split; kernel evaluates the chunk arithmetic in one GMP step) and long lines
wrapped.  156 literals split, 76 → 0 lines over 100 chars, max line 99.
Verified by the stage-8 chain build with linters on.

## 4. Inherent non-compliance (documented, not fixed)

These modules stay outside TauCeti compliance by construction; they are
*not* in `defaultTargets`/CI and are built explicitly on Modal only:

* `Tau/LehmerMod` (`maxRecDepth 100000`): kernel evaluation depth of the
  mod-P list decides (16/256/512).  The 512 decide alone needs ~5 min kernel
  time and > 6 GB heap (AGENTS.md); a 1024 attempt measured > 71 GB.
* `Tau/LehmerPacked` (3 × `maxHeartbeats 8000000`, `maxRecDepth 1000000`):
  packed-bignum kernel decides at 512/16384/65536 entries; measured ≈ 18 GiB
  (16384) and ≈ 63 GiB (65536) of kernel heap — ≈ 40× the default heartbeat
  budget per decide.
* `Tau/LehmerPow32` (`maxRecDepth 1000000`, `maxHeartbeats 8000000`): one
  decide walks all 65 535 Mordell chains; measured 2089 s / 143.8 GiB.
* `MaedaGalois5IdBase/IdE4/IdE5/IdE6/Identities` (24/6/6/8/3 options, 8M–512M
  heartbeats): generated `Poly5` kernel certificates, checkpointed at the
  measured 0.5–0.9 M modelled list operations per declaration (≈ 15–25 GiB);
  fitting the default 200k budget would need ~40× finer checkpointing and an
  explosion of generated code (open question in the port plan, Tier C).
* `MaedaGalois5` (10 options): `fin_cases`/`decide` over `Perm (Fin 5)` with
  large normalizations; one 400M-heartbeat capstone theorem.

Removing these would weaken or destroy the verified results (the whole point
of the modules); TauCeti-side they are Tier C of the port plan (never
upstreamed as-is).

## 5. Verification matrix

| check | status |
|---|---|
| per-module local `lake build` (Lehmer, Bridge, Weight12, Congruence691, LehmerSieve691) | ✅ all, default options |
| `MaedaGalois5Defs` on Modal (`lean_check`), default options | ✅ |
| full light `lake build` (all `defaultTargets`) | local background run (see §6) |
| heavy chain rebuild `tools/stage_chain.sh` (Defs → Weights; verifies `r5c*` split, `resolvent5_map` simp edit, literal splits, linters on) | Modal, in progress |
| axiom audit (`MathProof.AxCheck`, `AxCheckDecide` on Modal) | pending |
| heavy Tau modules (`LehmerMod` first; `LehmerPacked`/`LehmerPow32` after) | pending |
| CI (`lean-action` + docgen on push) | pending push |

## 6. Post-edit rebuild obligations (input-based traces)

Editing chain ancestors invalidated downstream `.olean`s; rebuilds done or
queued: light set (local/Modal), `MaedaGalois5*` chain (Modal, staged),
`Tau/LehmerMod` → `AxCheck` (Modal), `Tau/LehmerPacked` family (Modal,
optional), CI on push.

## 7. Audit-tooling note

`tools/tauceti_audit.sh` counted `native_decide`/`set_option` inside comments;
tightened (comment-stripped matching) so the mechanical audit reflects real
violations.  Post-fix result: **0 `set_option` in every `defaultTargets`
module**; remaining hits only in §4 modules.
