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
| impl/iteration24/index-card | blueprint/index-card/BLUEPRINT.md | SALVAGED mid-G2 (tip 9e518e1) | G1 CLOSED green (audit 54/54, star-certificate design `C = Q*A` committed 2f400f4); G2 (HeckeLatticeIndex.lean) in progress at wrap-up |
| impl/iteration24/index-cyclic | blueprint/index-cyclic/BLUEPRINT.md | PAUSED clean, G1+G2+G3p1 done (tip 1875fca) | G1 green (18 weights, D=Ik dims 3–4, D=Ik=1 dim 2; witnesses already reduced); HeckeCyclic.lean G2 green (own t2Span, defeq t2Lattice); HeckeCyclicWeights.lean G3p1 green (80s/6.2GiB, root 68s/6.7GiB, AxCheckDecide 1360/0, tauceti clean; `hcard` hypothesis PENDING b1); CORRECTIONS note in place |
| impl/iteration24/hecke-ring-gens | blueprint/hecke-ring-gens/BLUEPRINT.md | SALVAGED mid-G1 (tip cbfc588) | G1 measurement nearly done: w64-audit 14 s/wt; route decision = smooth-{2,3}-monomial rows (tiny dets; det ±1 subsets exist at {3,5}-weights — w60: 5 rows, no coefficients needed); full 36-weight table (`g1_ring_gens.py all`) was mid-run at wrap-up, output at agent-work hecke-ring-gens/g1_table2.log |

Watchdog (§6 stuck-worker protocol; thresholds = §6 defaults — HUNG 60 min,
LOOPING 90 min, run-overdue 3× stated wall-clock; heartbeat convention in
every spawn briefing):

| worker | task id | spawned | stalls (branch × gate) | parked? |
|---|---|---|---|---|
| index-card | agent_c7cc1c8f — TERMINATED (session wrap-up 2026-11-04 ~22:15) | 2026-11-04 | 0 (operator wrap-up, not a stall) | no |
| index-cyclic | agent_c2624ee1 — TERMINATED (session wrap-up, clean tip) | 2026-11-04 | 0 (operator wrap-up, not a stall) | no |
| hecke-ring-gens | agent_d9d751ff — TERMINATED (session wrap-up 2026-11-04 ~22:15) | 2026-11-04 | 0 (operator wrap-up, not a stall) | no |

## Incident log
(dated; reboots, stalls, terminations/respawns with signals, escalations)

### 2026-11-04 ~17:30 — wave spawned
3 workers from base f7628f6 (worktrees + WORKLOGs + seeded mrun.sh runners
under /home/doz/tmp/math-proof1-temp/agent-work/<slug>/runs/).  Note: the
three iteration-23 worktrees (hecke-tm/index/field) remain under
worktree/mp1/ — clean, to be removed at this iteration's close-out
(§4f leftover).

## Cross-cutting lessons
(to be promoted to AGENTS.md)

## Integration plan
merge order: index-card first (b2/b3 import its module), then index-cyclic,
then hecke-ring-gens; registration lists union-resolved (append-shaped);
combined light root build 0/0 + combined AxCheckDecide + tauceti on Modal
before handover; memory pass at merge (import floor + literals lesson).

### 2026-11-04 ~22:15 — operator wrap-up: session handoff to a fresh orchestrator
All three workers terminated by the operator's session wrap-up (task IDs
unresolvable after the interrupt — treated as DEAD per §6; NOT stall
escalations, stall counts stay 0).  Watchdog was LIVE for all three at the
final pass (~21:55).  Salvage: index-card 9e518e1, hecke-ring-gens cbfc588;
index-cyclic clean at 1875fca.  Worktrees preserved.

**Fresh-session resume (cold)**: re-enter at stage (d) WAVE.  Read
WAVE-TRACKING (this file), each worktree's `blueprint/<slug>/WORKLOG.md`
last dated entry, and the branch tips above.  Then fresh-respawn each
unfinished worker per §6: briefing = worktree + branch + base + salvage
commit + WORKLOG resume point + why terminated (session end, not a stall —
do-not-redo lists live in each WORKLOG).  index-cyclic's remaining work is
G3p2 (plug the `hcard` per-weight facts once b1's index-card lands G2–G4);
its WORKLOG records the exact plug-in recipe.  Modal runners (mrun.sh) live
under /home/doz/tmp/math-proof1-temp/agent-work/<slug>/runs/ (persistent).
