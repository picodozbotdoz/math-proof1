# Iteration 22 wave — tracking (3 blueprint implementations in parallel)

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
| impl/iteration22/lehmer-coverage | blueprint/lehmer-coverage | RUNNING | |
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
