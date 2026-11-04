# Iteration 24 wave — tracking (3 blueprint implementations in parallel)

Operator instruction (2026-11-04, T2 submission): standing loop — close the
Hecke index gaps (iteration23-review §6.1–6.3 → §7.2); priorities normal,
exclusions none, budgets standard.  Trunk `dev/iteration24-hecke-index`
from `dev/zai` 229e326 (INIT 8a8c9e0; recon: stay at rc1; CI push tier
measured 2.0 min — see `NOTES.md`).  Blueprints from
`research/iteration24/FINDINGS.md` (probes 1–3, 0 anchor failures).

Status per branch (branch = impl/iteration24/<slug>, base = <commit>):

| branch | blueprint | status | result |
|---|---|---|---|
| impl/iteration24/index-card | blueprint/index-card/BLUEPRINT.md | PENDING | — |
| impl/iteration24/index-cyclic | blueprint/index-cyclic/BLUEPRINT.md | PENDING | — |
| impl/iteration24/hecke-ring-gens | blueprint/hecke-ring-gens/BLUEPRINT.md | PENDING | — |

Watchdog (§6 stuck-worker protocol; thresholds = §6 defaults — HUNG 60 min,
LOOPING 90 min, run-overdue 3× stated wall-clock; heartbeat convention in
every spawn briefing):

| worker | task id | spawned | stalls (branch × gate) | parked? |
|---|---|---|---|---|
| index-card | — | — | 0 | no |
| index-cyclic | — | — | 0 | no |
| hecke-ring-gens | — | — | 0 | no |

## Incident log
(dated; reboots, stalls, terminations/respawns with signals, escalations)

## Cross-cutting lessons
(to be promoted to AGENTS.md)

## Integration plan
merge order: index-card first (b2/b3 import its module), then index-cyclic,
then hecke-ring-gens; registration lists union-resolved (append-shaped);
combined light root build 0/0 + combined AxCheckDecide + tauceti on Modal
before handover; memory pass at merge (import floor + literals lesson).
