# Memory alerts

Policy (AGENTS.md, "Memory alerts"): every Lean build whose `lake` tree
reaches **64 GiB** RSS is investigated.  `tools/modal_run.sh` appends each
`[memory-alert]` here as an **OPEN** entry; the investigation runs
`LEAN_CHECK_PROFILE=<Module> tools/modal_run.sh`, records the top
declarations (`[profile]` lines) and the cause, and marks the entry
**CLOSED** with the fix or the reason the cost is inherent.

Entries are newest last.

## Backlog (measured before the policy) — OPEN

Builds that crossed 64 GiB before the tooling existed; numbers from
`research/research-log.md` and `research/iteration18-review.md`.

| module | peak RSS (measured) | known so far |
|---|---|---|
| `MaedaGalois5IdE4` | 202 GiB | first guess (elaboration of `*_eval` / `theta_e4`) was wrong — it is the kernel `decide`; see below |
| `MaedaGalois5IdE6` | 172 GiB | as above |
| `MaedaGalois5IdE5` | 137 GiB | as above |
| `LehmerPow32` | 143.8 GiB | one kernel `decide` over 65,535 recursion chains (AGENTS.md) |
| `LehmerPacked` (65536 bound) | ~63 GiB | just under the threshold; kernel decide heap |

- investigation (2026-10-29), **CLOSED for the `MaedaGalois5Id*` rows** —
  `research/poly5-memory-study/README.md`.  Cause: the kernel `decide`
  certificates (`e3dec` +18.5 of 24.5 GiB in `IdBase`; bridge lemmas ≈ 0);
  kernel memory ≈ 27 GiB per million `Poly5` list operations in one
  declaration (fits e2…e6 and δ² within 21–32).  E4 is worst because its
  left side is 15 brute-force products.  Fix (prototyped, measured): left
  side by the e_k recurrence + LHS/RHS checked against one literal in
  separate declarations — E4 202 → 19.0 GiB (2343 → 221 s), E6 172 →
  63.2 GiB (2207 → 1414 s; ≈ 35 GiB expected after one more RHS split).
  **Rolled out 2026-10-29** (chain regenerated and rebuilt): IdBase 8.1,
  IdE4 13.5, IdE5 22.0, IdE6 34.7, Identities 17.6 GiB — every module below
  the threshold.
- `LehmerPow32` / `LehmerPacked`: not yet investigated (same tooling).
## 2026-10-31T15:04Z — OPEN

- command: `tools/modal_run.sh --file MathProof/ModularForms/MaedaDim8Weights.lean` (rc=0)
- log: `/home/doz/tmp/math-proof1-temp/mathproof-runs/run-20261031-225645-100459-m8192.log`
- alert:

  ```
  [memory] request 8192 MiB (soft; escalation ladder 8192/16384/32768 on OOM)
  [memory] per-module peak RSS (GiB, t of peak):
  [memory]      8.01  t=    304s  /tmp/repo/MathProof/ModularForms/MaedaDim8Weights.lean
  [memory]      5.66  t=     81s  /tmp/repo/MathProof/Tau/Lehmer.lean
  [memory]      4.82  t=    128s  /tmp/repo/MathProof/ModularForms/MaedaDim4.lean
  [memory]      4.77  t=    109s  /tmp/repo/MathProof/ModularForms/LehmerWeight16.lean
  [memory]      4.76  t=     79s  /tmp/repo/MathProof/ModularForms/Congruence691.lean
  [memory]      4.76  t=    117s  /tmp/repo/MathProof/ModularForms/MaedaLevelOne.lean
  [memory]      4.75  t=     72s  /tmp/repo/MathProof/Tau/Bridge.lean
  [memory]      4.74  t=     95s  /tmp/repo/MathProof/Tau/LehmerPrimeReduction.lean
  [memory]      4.74  t=    102s  /tmp/repo/MathProof/ModularForms/EigenLevelOne.lean
  [memory]      4.73  t=     78s  /tmp/repo/MathProof/Tau/Mordell.lean
  [memory]      4.73  t=    124s  /tmp/repo/MathProof/ModularForms/CharpolyDimN.lean
  [memory]      4.72  t=     88s  /tmp/repo/MathProof/Tau/LehmerSieve691.lean
  [memory]      4.67  t=    134s  /tmp/repo/MathProof/ModularForms/MaedaCertC.lean
  [memory]      4.65  t=     82s  /tmp/repo/MathProof/Tau/LehmerUnbounded.lean
  [memory]      4.36  t=     72s  /tmp/repo/MathProof/ModularForms/BernoulliHigh.lean
  [memory-alert] peak tree RSS 20.1 GiB >= 16 GiB — investigation required (AGENTS.md, Memory alerts)
  [memory-alert]   .tmp.repo.MathProof.ModularForms.MaedaDim8Weights: 8.0 GiB  →  per-declaration profile: LEAN_CHECK_PROFILE=.tmp.repo.MathProof.ModularForms.MaedaDim8Weights tools/modal_run.sh
  ```

- investigation (CLOSED 2026-10-31): **no-cache cold build of
  `MaedaDim8Weights`** (`LEAN_CHECK_NO_CACHE=1`, the memory-right-sizing
  validation V2, `research/iteration21/MEMORY-RIGHTSIZING.md`).  Cause: with
  the module cache off, lake rebuilt the WHOLE import closure with 7 lean
  processes in parallel — the 20.1 GiB *tree* peak is the SUM of concurrent
  processes (Weight12 12.5 GiB, Tau/Basic ≈ 17 GiB …), while the biggest
  single process peaked at 8.0 GiB (the target module itself, consistent
  with the 9.3 GiB cached-run measurement minus shared pages).  Verdict:
  cost inherent to no-cache cold builds; single-module peak (what request
  sizing keys on) is 8.0 GiB.  No action; the request ladder and the 16 GiB
  alert behaved exactly as designed.


## 2026-11-05 — `MathProof.AxCheckDecide` (iteration 25, maeda-small worker)

- alert: `[memory-alert] peak tree RSS 25.6 GiB >= 16 GiB` (wall 81 s,
  run log `agent-work/maeda-small/runs/axcheck.out`).  Per-module peaks:
  max 5.67 GiB (`MaedaGalois4`), then `AxCheckDecide` 5.61, `MathProof`
  5.55, `HeckeFieldWeights` 5.45, … `MaedaGalois` 4.80 — no module above
  6 GiB.
- investigation (CLOSED 2026-11-05): editing `MaedaSmallWeights`
  (q-cells now via `seqPLc`) invalidated its light descendants
  (`MaedaGalois`, `MaedaGalois4`, `MaedaGalois5Defs`, `HeckeIndexSmallWeights`,
  `HeckeField*`, `HeckeGeneratedByT2*`, `MaedaT2GaloisSmallWeights`, …), and
  lake rebuilt ≈ 13 of them with up to 4–5 `lean` processes in parallel,
  each at its ≈ 5 GiB import floor.  The 25.6 GiB *tree* peak is that sum;
  the largest single process is 5.67 GiB (what request sizing keys on).
  Same pattern as the 2026-10-31 `MaedaDim8Weights` entry.  Cost inherent to
  a multi-descendant rebuild; no action.  The edited module itself:
  4.92 GiB (25 s) in its `--file` run.
## 2026-11-05 — scaled-certs (iteration 25) `--target MathProof.AxCheckDecide` — CLOSED

- alert: `[memory-alert] peak tree RSS 22.2 GiB >= 16 GiB` (wall 396 s,
  8 GiB request, no OOM).  Log:
  `/home/doz/tmp/math-proof1-temp/agent-work/scaled-certs/runs/g4-axcheck.out`.
- investigation (CLOSED 2026-11-05): tree peak = SUM of concurrent lean
  processes (lake rebuilt everything downstream of the regenerated
  HeckeRational files in parallel).  Largest single module: 7.99 GiB
  (`HeckeRationalWeights`, was 8.4 GiB before the retrofit), then
  `MaedaSmallWeights` 7.66, `HeckeIndexCardWeights` 7.40, `HeckeIndexWeights`
  6.17 GiB.  No single declaration to profile; inherent to parallel rebuilds
  (same verdict as the 2026-10-31 no-cache entry).  No action.
## 2026-11-05T03:32Z — CLOSED

- command: `tools/modal_run.sh --target MathProof.ModularForms.MaedaGalois5AxCheck` (rc=0)
- log: `/home/doz/tmp/math-proof1-temp/mathproof-runs/run-20261105-110453-536570-m49152.log`
- alert:

  ```
  [memory] request 8192 MiB (soft; escalation ladder 8192/16384/32768 on OOM)
  [memory] per-module peak RSS (GiB, t of peak):
  [memory]     33.46  t=   1137s  /tmp/repo/MathProof/ModularForms/MaedaGalois5IdE6.lean
  [memory]     20.77  t=    551s  /tmp/repo/MathProof/ModularForms/MaedaGalois5IdE5.lean
  [memory]     16.24  t=   1453s  /tmp/repo/MathProof/ModularForms/MaedaGalois5Identities.lean
  [memory]     12.30  t=    273s  /tmp/repo/MathProof/ModularForms/MaedaGalois5IdE4.lean
  [memory]      6.84  t=    122s  /tmp/repo/MathProof/ModularForms/MaedaGalois5IdBase.lean
  [memory]      5.38  t=   1563s  /tmp/repo/MathProof/ModularForms/MaedaGalois5.lean
  [memory]      4.98  t=   1574s  /tmp/repo/MathProof/ModularForms/MaedaGalois5Weights.lean
  [memory]      4.81  t=     65s  /tmp/repo/MathProof/ModularForms/MaedaGalois5Defs.lean
  [memory]      4.78  t=   1578s  /tmp/repo/MathProof/ModularForms/MaedaGalois5AxCheck.lean
  [memory]      4.77  t=     29s  /tmp/repo/MathProof/ModularForms/MaedaGalois.lean
  [memory-alert] peak tree RSS 34.8 GiB >= 16 GiB — investigation required (AGENTS.md, Memory alerts)
  [memory-alert]   .tmp.repo.MathProof.ModularForms.MaedaGalois5IdE6: 33.5 GiB  →  per-declaration profile: LEAN_CHECK_PROFILE=.tmp.repo.MathProof.ModularForms.MaedaGalois5IdE6 tools/modal_run.sh
  [memory-alert]   .tmp.repo.MathProof.ModularForms.MaedaGalois5IdE5: 20.8 GiB  →  per-declaration profile: LEAN_CHECK_PROFILE=.tmp.repo.MathProof.ModularForms.MaedaGalois5IdE5 tools/modal_run.sh
  [memory-alert]   .tmp.repo.MathProof.ModularForms.MaedaGalois5Identities: 16.2 GiB  →  per-declaration profile: LEAN_CHECK_PROFILE=.tmp.repo.MathProof.ModularForms.MaedaGalois5Identities tools/modal_run.sh
  [memory-alert]   .tmp.repo.MathProof.ModularForms.MaedaGalois5IdE4: 12.3 GiB  →  per-declaration profile: LEAN_CHECK_PROFILE=.tmp.repo.MathProof.ModularForms.MaedaGalois5IdE4 tools/modal_run.sh
  ```

- investigation (CLOSED 2026-11-05, iteration-25 orchestrator): the approved
  heavy-chain rebuild forced by the `MaedaSmallWeights` retrofit (an import
  ancestor; the chain's own sources are unchanged).  Per-module peaks
  reproduce the budgeted, already-profiled chain costs within 1.3 GiB
  (`tools/stage_chain.sh` header, measured 2026-10-29: IdE4 13.5, IdE5 22.0,
  IdE6 34.7, Identities 17.6 GiB; cause and per-declaration budget in
  `research/poly5-memory-study/` — ≈ 27 GiB per M `Poly5` list operations,
  checkpointed at ≈ 0.5–0.9 M).  Inherent; no new profile needed (inputs
  identical to the profiled run).  Note: `LEAN_CHECK_MEMORY_MIB=49152` was
  not reflected in the `[memory] request` line (8192) — the request is soft
  and the run was granted ≥ 35 GiB; check the env passthrough of
  `tools/modal_run.sh` before relying on explicit requests.

