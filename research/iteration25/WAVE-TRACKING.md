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
