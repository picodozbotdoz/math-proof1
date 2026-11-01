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

Status per branch (branch = impl/iteration22/<slug>, base = <TBD>):
| branch | blueprint | status | result |
|---|---|---|---|
| (probe1) | HeckeRational (steering 1) | probing | |
| (probe2) | LehmerCoverage (steering 2) | probing | |
| (probe3) | T3GaloisSmall (orchestrator choice) | probing | |
| impl/iteration22/t3-galois-small | T3GaloisSmall (base 569bcf0) | **COMPLETE** | `MaedaT3WeightK.maeda_galois_full` × 24 (dims 2–5, k ≤ 74): dims 3–5 via Frobenius certs (ℓ ≤ 89, Bézout), dim 2 via new `MaedaGaloisQuad.bijective_of_quadratic`; T₃ Maeda in full at all 54 weights. All Modal builds 0/0 (galois file 34 s / 6.62 GiB tree; axcheck 83 s; AxCheckDecide 1 310 certs, 0 > propext). Inbox polled every gate: empty throughout. WORKLOG: blueprint/t3-galois-small/WORKLOG.md |

## Incident log
## Cross-cutting lessons
## Integration plan
