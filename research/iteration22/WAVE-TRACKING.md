# Iteration 22 wave — tracking (3 blueprint implementations in parallel) — **CLOSED 2026-11-02**

Operator instruction (2026-11-02 T2 submission): Task A = the T3-Galois T1
(CLOSED — see research/iteration22-t3-galois/WORKLOG.md; its commits are the
trunk's baseline by the operator's own naming). Task AA = self-directed
iteration per §4b→§4f with standing steering: 1) ℚ-rationality of
T_p ∈ ℂ[T₂] (§9.2); 2) Lehmer coverage quantification below 2³², then the
131072 packed attempt if budget allows; 3) orchestrator's choice. No
dims ≥ 11; no Mathlib bump mid-iteration.

## INIT (a) — 2026-11-02

* Trunk `dev/iteration22-maeda-lehmer` from T1 head `6e6db14` (T1 branch
  `dev/iteration22-t3-galois` remains independently mergeable).
* **Recon (Mathlib pin)**: no `v4.36.0` stable tag yet; newest is `rc2`
  (we are on `rc1`). Decision: **stay on rc1** — none of the candidate
  blueprints needs API from rc2, generated-file stability outweighs
  kernel-fix upside; re-check at the next boundary
  (research/mathlib-version-strategy.md "First action" followed).
* Probes launched (parallel fact-gathering; blueprint AUTHORING stays
  serial b1→b3 so later blueprints deepen on earlier findings — deviation
  from §4b's letter recorded here): probe1 ℚ-rationality, probe2 Lehmer
  coverage, probe3 T₃-Galois dims 2–5.

Status per branch (branch = impl/iteration22/<slug>, base = 569bcf0):
| branch | blueprint | status | result |
|---|---|---|---|
| impl/iteration22/hecke-rational | blueprint/hecke-rational | RUNNING | |
| impl/iteration22/hecke-rational | blueprint/hecke-rational | **COMPLETE** | T₃ ∈ ℚ[T₂] at ALL 54 weights, constructive witnesses (integer polys at dims 2); HeckeRational + HeckeRationalWeights (trio+CI ≈4.5 min) + HeckeRationalSmallWeights (root-only); entrywise decides keep AxCheckDecide 0 > propext (matrix-level decides pulled Classical — fixed, CORRECTIONS filed); Modal 37/234/67 s, ≤ 8.4 GiB; no descope; lineage 50.1 M tokens (near cap, finished clean) |
| impl/iteration22/lehmer-coverage | blueprint/lehmer-coverage | **COMPLETE** | STUDY exact (99.9093% below 2³², U=3,894,333, bad primes 294,618, regen-matched; 2 probe cells corrected: 2³⁰ census 78,715, 2¹⁸ candidates 285); LehmerCoverageCount light module (structural noFactorFrom cert — Nat.Prime NOT kernel-decidable; kernel census 2¹⁸ AND 2²⁰, uncovered 23/227) green 0/0 32 s/5.8 GiB, trio-registered, +4 certs 0>propext; **131072 DESCOPE memo** (110–125 GiB ≈ 1.8× stop-rule, +0.0053 pp) — surfaced to operator |
| impl/iteration22/t3-galois-small | blueprint/t3-galois-small | **COMPLETE** | Gal = Sₙ for T₃ at ALL 54 weights; MaedaGaloisQuad (trio) + MaedaT3GaloisSmallWeights (root-only, 24 wts) green 0/0 (34 s/3.84 GiB; AxCheck 83 s); certs reproduce probe table; byte-identity kept; 1310 decide certs combined, 0 > propext; no descopes/deviations |

Blueprints committed 569bcf0 (from probe FINDINGS in research/iteration22/).
Worktrees ready with WORKLOG seeds + standalone-mirror `mrun.sh` (each
committed on its impl branch); mirrors under /home/xyz/<slug>.

## Incident log
- 2026-11-02: probe-1 agent spawn rejected by operator → orchestrator ran the
  ℚ-rationality probe inline (FINDINGS committed all the same).  Worker spawns
  proceed normally.

## Cross-cutting lessons
## Integration plan
- Merge order: t3-galois-small (no shared files with others beyond root
  import) → lehmer-coverage (research dirs + optional new module) →
  hecke-rational (new module + generated file + registrations).  Root
  `MathProof.lean` / lakefile / CI list union-resolved append-shaped.
- Combined light build + combined AxCheckDecide green on Modal before the
  operator handover.

## CLOSE (2026-11-02)
Wave completed: 3/3 branches landed, ZERO descopes.  Union-merged via
`integration/iteration22-wave` (per-worktree `mrun.sh` dropped from the
integrated tree).  Combined verification on Modal: root target green
(10 s / 6.69 GiB, 0 err / 0 warn); combined `AxCheckDecide` **1 312 decide
certificates, 0 beyond `propext`**; `tauceti_audit.sh` clean on all six new
light modules.  44 Modal check-runs total (budget ≤ ~80); no memory alerts.
Review: `research/iteration22-review.md`.  Master merge = the operator's.

## NEXT SESSION (cold-start pointer)
Iteration 22 is CLOSED; the T2 loop continues with **Iteration 23 INIT** from
a fresh session.  Read: research/iteration22-review.md §6–7 (open gaps +
ranked recommendations: ℚ-rationality corollaries incl. integrality of
witnesses, composite T_m, CI selective targets BEFORE any new trio
registration), research/research-log.md tail, external-doc/RESEARCH-WORKFLOW.md
§4.  Merge state: `integration/iteration22-wave` (tip 08263fe) is
merge-ready for master (operator's action); `dev/iteration22-t3-galois` (T1)
is independently mergeable but already contained in the integration branch
via the trunk.  CI bill after this iteration ≈ +9–11 min/push.
