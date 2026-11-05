# Iteration 25 wave — tracking (nested-certificate retrofit, 3 workers)

Operator decision 2026-11-05: retrofit the 5296 pre-24 nested certificates
(iteration24-review §7.1), heavy-chain rebuild approved.  Trunk
`dev/iteration25-nested-certs` from 825e5a6; see `NOTES.md`.

| branch | blueprint | status | result |
|---|---|---|---|
| impl/iteration25/scaled-certs | blueprint/scaled-certs/BLUEPRINT.md | SPAWNED | |
| impl/iteration25/zmod-casts | blueprint/zmod-casts/BLUEPRINT.md | SPAWNED | |
| impl/iteration25/maeda-small | blueprint/maeda-small/BLUEPRINT.md | SPAWNED | |

Watchdog (§6 defaults: HUNG 60 min, LOOPING 90 min, run-overdue 3×):

| worker | task id | spawned | stalls | parked? |
|---|---|---|---|---|
| scaled-certs | a7cb6e0ce98ab6967 | 2026-11-05 | 0 | no |
| zmod-casts | a00cbff21497cae73 | 2026-11-05 | 0 | no |
| maeda-small | a6c7e884782c7cf88 | 2026-11-05 | 0 | no |

## Incident log

## Integration plan
Merge order scaled-certs → zmod-casts → maeda-small (registration files
union-resolved).  Then, serialized: light root + AxCheckDecide (target
nested 0), `tools/stage_chain.sh` + `MaedaGalois5AxCheck`, `LehmerGrand`,
`LehmerPrimeGrand` (memory per AGENTS.md).
Thu Nov  5 11:04:46 AM +08 2026 chain rebuild start (MaedaGalois5AxCheck, 48 GiB, expected ~35-45 min)
- chain rebuild DONE: MaedaGalois5AxCheck green, 1580 s lake wall, peak 34.75 GiB (IdE6 33.46), 30 `#print axioms` = 19 [propext] + 11 std-3, 0 sorryAx; memory alert CLOSED (budgeted chain cost).
- maeda-small merged e36b288; scaled-certs merged 0217f9a (statement text verified identical, `:= by` → `:=` only).

### 2026-11-05 — session paused (usage limit)
State for a cold resume: maeda-small + scaled-certs merged; MaedaGalois5
chain re-verified (4ff195c).  zmod-casts (task a00cbff21497cae73) still
running its sequential dims-8–10 / T3Dim7–10 builds (runs/seq.sh,
per-file logs runs/g4-<Module>.out); when done: verify statements
unchanged, merge, combined light root + AxCheckDecide (target nested 0),
then review/log/README.  OPEN operator question: re-verify LehmerGrand /
LehmerPrimeGrand (LehmerPacked + LehmerPow32 NOT in the build cache →
~63 GiB + ~144 GiB rebuilds) or skip with recorded rationale (proof-only
change to two private lemmas of LehmerSieve691).
