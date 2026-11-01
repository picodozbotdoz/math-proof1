# Draft — Iteration 20 research-log entry (S6; numbers finalized after the S4 queue)

## Iteration 20 — Maeda's conjecture for dims 6–10 (weights 72–134)

Branch `dev/iteration20-maeda-dim6-10`, implementing the `dev/blueprint`
blueprint `iteration19-maeda-generic` (engines landed in the blueprint wave).
**Maeda's conjecture (irreducibility half) is now formally verified, from the
Hecke operator itself, for every level-one weight with `2 ≤ dim S_k ≤ 10`** —
30 new weights `72 ≤ k ≤ 134`, on top of the 24 weights `24–74` of Iterations
14–16.

Stages (plan: `research/iteration20-plan.md`):

* **S1 `CharpolyDimN.lean`** (commit `57656b0` → ℕ-indexed restructure
  `eb94f4d`): the dimension-generic echelon extraction `charpoly_dimN` —
  matrix of any endomorphism from q-coefficient tables by downward
  back-substitution (`coordN`/`coordsAux`).  ℕ-indexed hypotheses; the first
  Fin-indexed shape died on `omega`-opaque cast chains (S3-handoff gotchas).
* **S2 `tools/gen_maedan.py`**: emits one file per dim from
  `research/iteration20/data/maeda_dim6_10.json` (census probe re-runs
  byte-identically; matrices/charpolys regression-asserted against the proved
  k = 24/48).
* **S3 dim 6** (commit `838fc35`, handoff `research/iteration20/S3-handoff.md`):
  8174 lines, Modal green 130 s / 6.6 GiB, zero style warnings.  The 66-error
  hunt produced the pipeline's working idioms (per-entry theorems for
  heartbeats, the hmap simp+rw chain, `C (1) * X ^ n` leading term).
* **S4 dims 7–10** (this entry): three new failure classes, all fixed in the
  generator:
  1. *Statement lines > 100 chars* (dims 8–10): q/t lemma statements now wrap
     the RHS to a continuation line (`coeff_stmt`).
  2. *Chunked determinant literals*: `eval_det` reduces `det (t·1 − M)` to a
     flat numeral but cannot close `flat = c0 * 10 ^ e0 + c1 …` — chunked
     `det_t`s get `norm_num` after `eval_det` (validated locally on the exact
     goal shapes, incl. 4-chunk dim-10 size).
  3. *`simp only [coordsAux]` heartbeat exhaustion at the deepest
     back-substitution rows* (dim 9: `entry_8_{4..8}`, 30× "(deterministic)
     timeout at simp/transform/whnf"): the entries are now STAGED — per
     (column, row-count) `Lv{a}_{j} : coordsAux … j = [literal list]`, each
     proved from the previous stage by a ONE-step unfold (`change`, never
     `show` — linter.style.show) + `rw` + tuned simp set; every
     `entry_{c}_{a}` is then `simp only [coordN]; rw [Lv{a}_{c+1}]; rfl`.
     Dim 9: 931 s failed cascade → 603 s staged, 9.3 GiB.
  Big literals (charpoly coefficients past 80 digits) are emitted as chunked
  `c0 * 10 ^ e0 + c1` with the SAME token sequence inside `P` and the hmap
  rewrites (rw matches syntactically).

  Verification matrix (Modal `lean_check --file`, linters on, all zero
  warnings):

  | module | lines | build | peak RSS |
  |---|---|---|---|
  | `MaedaDim6Weights` | 10579 | ~N6 s | ~M6 GiB |
  | `MaedaDim7Weights` | 14199 | ~N7 s | ~M7 GiB |
  | `MaedaDim8Weights` | 18389 | ~N8 s | ~M8 GiB |
  | `MaedaDim9Weights` | 23257 | ~N9 s | ~M9 GiB |
  | `MaedaDim10Weights` | 28900 | ~N10 s | ~M10 GiB |

* **S5 registration + audit**: all six modules (incl. `CharpolyDimN`) in
  `MathProof.lean`, `defaultTargets`, CI list.  `tauceti_audit.sh` clean
  (no `set_option`/`#eval`/`meta`/`native_decide`).  `AxCheckDecide` on
  Modal: RESULT.

* **S6 bookkeeping**: README results section + layout line, docs landing
  page (24–134, 54 weights), AGENTS.md layout, this entry.

Invariants kept: no heavy-chain ancestors touched; generated files never
hand-edited (`gen_maedan.py --check` byte-identical); every certificate is
`decide +kernel` or `norm_num`/`eval_det`, propext-clean per AxCheckDecide.
