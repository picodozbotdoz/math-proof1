# Iteration 24 review — closing the Hecke index

Trunk `dev/iteration24-hecke-index` (from `dev/zai` 229e326).  Theme:
iteration23-review §6.1–6.3 / §7.2 — turn the 54 index certificates into a
description of the Hecke ring 𝕋 at each weight.  Three blueprints
(`research/iteration24/FINDINGS.md`, probes 1–3), one wave, one mid-wave
session handoff.

## 1. What was delivered, and why it matters

| blueprint | branch tip | result |
|---|---|---|
| b1 index-card | 43d6df5 | `HeckeLatticeIndex.relIndex_t2_eq_det` / `natCard_quot_eq_det` (generic) and, at **all 54 weights**, `HeckeIndexCardWeightKK.index_card`: `[𝕋 : ℤ[T₂]] = |I_k|` as `AddSubgroup.relIndex` and as `Nat.card (𝕋 ⧸ ℤ[T₂])` — §6.1 closed |
| b2 index-cyclic | bbcd288 | `HeckeCyclic`: 𝕋 / ℤ[T₂] cyclic at `n ≤ 4` (`T₁, T₂, T₄ ∈ ℤ[T₂]`), the iff `𝕋 = ℤ[T₂] ↔ I_k = 1`; `HeckeCyclicWeights`: `D_eq_Ik` + `heckeLattice_ne_t2Span` (unconditional) at the 12 dims-3–4 weights, `heckeLattice_eq_t2Span` at the six dim-2 weights — §6.2, §6.3 closed for dims ≤ 4 |
| b3 hecke-ring-gens | 2d27221 | `HeckeRingGens`: `ℤ[T_p : p ∈ ps] ∋` every `ps`-smooth `T_m`, hence **𝕋 = ℤ[T₂,T₃,T₅,T₇] for every `dim S_k ≤ 10`** (certificate-free); per weight `heckeRing_eq_gens2357` (54), `heckeRing_eq_gens235` (the 22 `{3,5}`-weights; ten `T₇` row certificates at dims 7–9), `…gens23` (n ≤ 4), `…gens2` (n = 2) — answers §7.2's "which `T_m` carry the rest of `I_k`" as a ring statement |

Together: at every level-one weight with `2 ≤ dim S_k ≤ 10`, 𝕋 is pinned
down as a lattice (index over ℤ[T₂]) and as a ring (explicit prime
generators), and for dims ≤ 4 the Iteration-22 denominator is the whole
index.

**Audit infrastructure (integration).** `AxCheckDecide` gained a nested
pass, `#audit_decide_certs_nested`, over the internal auxiliary lemmas that
`decide +kernel` creates *inside* tactic proofs (`ext; fin_cases <;> decide
+kernel`, `show … by decide +kernel`) — invisible to the top-level pass
since it was written.  `MathProof/ModularForms/Iteration24AxCheck.lean`
(opt-in) prints the axioms of every new per-weight theorem.

## 2. Timeline as it happened

* 2026-11-04: INIT 8a8c9e0 (recon: stay at `v4.36.0-rc1`; CI push tier
  2.0 min), probes + blueprints f7628f6, wave spawned 9357338 (~17:30).
* ~22:15: operator ended the orchestrator session; all three workers
  terminated, salvage-committed (9e518e1, cbfc588; index-cyclic clean at
  1875fca).  Not stalls — stall counts stayed 0.
* 2026-11-05: fresh orchestrator, cold resume from WAVE-TRACKING.  index-card
  and hecke-ring-gens respawned from their salvage commits; index-cyclic
  respawned once b1's small file was green (G3p2 only).  hecke-ring-gens'
  36-weight G1 run had finished after the salvage — recorded, not rerun.
* All three gates green and merged (113dd34, 4a08d1a, 3cf4d7b).
* Integration audit found the nested-decide gap (§4); the iteration-24 part
  (2304 `hcard` cells) went back to index-card — fixed (43d6df5, merged
  013cd06).

## 3. What worked

* **Salvage → cold respawn.** Each respawn re-entered from WORKLOG + branch
  tip with no redone work; the §6 protocol's first real use (operator
  wrap-up, not a stall) cost one briefing per worker.
* **Deviation protocol.** Both b1 (dual-coordinate certificate instead of the
  blueprint's `Q·A` star certificate — no `p/q` literals) and b3
  (smooth-closure theorem instead of index certificates — no `relIndex`, no
  Cayley–Hamilton, ≤ 66-digit certificates instead of the probe's
  ≤ 32 489) found strictly cheaper routes than their blueprints and
  recorded the evidence.
* **Serial dependency handled by staged respawn**: b2 was only respawned when
  b1's exported shape existed; its plug-in recipe needed no adaptation.
* **Memory**: every module ≤ 7.4 GiB at the default 8 GiB request, no
  escalation, no 16 GiB alert.  b1's fix also cut the dims-6–10 card file
  from 286 s to 47 s.

## 4. What didn't work / was forced

* **The audit had a blind spot.**  `#audit_decide_certs` skipped internal
  names, so entrywise certificates (the pattern AGENTS.md itself
  *recommends* against the `decidablePiFintype` trap) were never audited.
  The nested pass audited 9256 such lemmas: **7600 depended on more than
  `propext`** — 2304 new (b1's `hcard` cells), 5296 in files landed
  before Iteration 24 (per-module counts: `research/iteration24/nested-decide-audit.txt`).
* **Three distinct causes** (b1's `#axiom_path` work): (i) `Finset` sums /
  `Matrix` products in the decided proposition; (ii) `==` on ℤ — `BEq ℤ`
  routes through `Int.instLinearOrderPackage` → `Classical.choice` (use
  `Int.decEq`); (iii) any `!![…]` `Matrix` literal in the statement pulls
  `Quot.sound`, and `^` on ℤ numerals goes through `Monoid.npow`.  The fix
  shape: integer pattern-match tables bridged to the matrices by `rfl`, one
  `List`-based Bool `decide` per weight, one generic bridge lemma.
* **b3 (ii) descoped**: `[𝕋 : ℤ[T₂,T₃]] = idx3` and the `≠` statements at
  the 14 `{3,5,7}`-weights need ℤ[T₂,T₃] pinned to a finite lattice
  (closure-under-×T₂/×T₃ certificates measured at 42–32 489 digits) — not a
  session-sized certificate.

## 5. Metrics

| item | value |
|---|---|
| new light modules | 9: 3 generic CI (`HeckeLatticeIndex`, `HeckeCyclic`, `HeckeRingGens`) + 5 root-only generated (`HeckeIndexCard{Small,}Weights`, `HeckeCyclicWeights`, `HeckeRingGens{Small,}Weights`) + opt-in `Iteration24AxCheck` |
| new / extended generators | `gen_hecke_index.py --card`, `gen_hecke_cyclic.py`, `gen_hecke_ring_gens.py` — all `--check` byte-identical |
| per-module cost (Modal) | 11–65 s, ≤ 7.39 GiB module peak; default 8 GiB request throughout |
| decide certificates (combined trunk) | top-level 1 424 / 0 beyond `propext` (was 1 360); nested 7 006 audited / 5 296 beyond — all in pre-24 files, 0 in iteration-24 modules (light root 8 527 jobs, 0 err / 0 warn, 58 s / 11.28 GiB tree) |
| axioms of new theorems | `Iteration24AxCheck`: 836 `#print axioms` — 64 `[propext]`, 772 the standard three, 0 `sorryAx` (40 s / 6.75 GiB) |
| CI | push tier +3 generic modules (`ci_targets.py --report` exit 0) |

## 6. Gaps left open

1. **Legacy nested certificates (5296)** in `HeckeIndex{Small,}Weights`,
   `HeckeRational{Small,}Weights`, `Maeda{Small,Dim6–10}Weights`,
   `MaedaT3{Small,Dim6–10}Weights`, `LehmerSieve691` — kernel-checked, but
   not on `propext` alone as CLAUDE.md asks.  `MaedaSmallWeights` is an
   import ancestor of the heavy `MaedaGalois5` chain (fix ⇒ ≈ 33 min /
   35 GiB chain rebuild).  **Operator decision.**
2. `[𝕋 : ℤ[T₂,T₃]]` at dims 5–10 and the `≠ ℤ[T₂,T₃,T₅]` statements at the
   14 `{3,5,7}`-weights (b3 (ii) descope).
3. `D` vs `I_k` at dims 5–10 (quotient non-cyclic; only `D ∣ I_k`).
4. Unchanged: 131072 Lehmer (descoped in Iteration 22).

## 7. Recommendations for Iteration 25

1. **Retrofit the legacy nested certificates** with b1's recipe (tables +
   one `List` Bool decide + generic bridge), generator by generator; batch
   the `MaedaSmallWeights` edit with an approved heavy-chain rebuild, or
   put its certificates in a new non-ancestor module.  Make the nested pass
   part of every close-out (it is now in `AxCheckDecide`).
2. If (1) is not wanted, record the exception explicitly in CLAUDE.md
   (entrywise certificates on the standard three axioms) so the audit's
   nested pass has a stated baseline.
3. b3 (ii): a structure-constant route (ℤ[T₂,T₃] as the ℤ-span of
   `T₂^a T₃^b`, closure certified by multiplication tables in Miller
   coordinates) — probe the certificate sizes first.
