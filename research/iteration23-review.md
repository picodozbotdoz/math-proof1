# Iteration 23 review — the level-one Hecke ring 𝕋

Orchestrator review, 2026-11-03 (§4f).  Trunk `dev/iteration23-hecke-ring`
(wave merge cc3e5fa, close-out c2c7c25, tip 8e79a91 before this document);
base `master` 51a5eb1.  Combined light build + combined `AxCheckDecide`
green on the merged trunk before this document.

## 1. What was delivered, and why it matters

Theme: the Hecke *ring*, not just the algebra over ℚ.  Iteration 22 proved
`T₃ ∈ ℚ[T₂]`; Iteration 23 builds every `T_m`, the integral structure they
span, and pushes rationality to all of them.  All kernel-verified, at all 54
level-one weights with `2 ≤ dim S_k ≤ 10` unless stated.

1. **`T_m` for every `m`** (b1, `HeckeTM`): the recursive operator, its
   q-expansion coefficient formula, `a₁(T_m f) = a_m(f)`, `T_1 = id`, full
   multiplicativity `T_m T_n = ∑_{d ∣ (m,n)} d^{k−1} T_{mn/d²}` and
   commutativity.  Closes iteration22-review §7.2.
2. **The Hecke ring 𝕋** (b2, `HeckeIndex`): duality
   `T_m = ∑_j a_m(g_j) T_{j+1}` over the Miller basis, linear independence
   of `T_1 … T_n`, `𝕋 = span_ℤ{T_j}` a subring containing `ℤ[T₂]`.
3. **Index certificates** (b2, `HeckeIndex{Small,}Weights`): per weight
   `I_k = |det A|`, the integer identity `∑ w′_j T₂^j = I_k T₃`, and
   `D ∣ I_k` for the reduced denominator of the Iteration-22 witness
   (48 weights with `D ≠ 1`).
4. **Every `T_m ∈ ℚ[T₂]` with no per-`m` certificate** (b3,
   `HeckeFieldRat` + `HeckeFieldWeights`): Miller-basis integrality + Cramer
   on the integer coordinates of `T₂^i` in 𝕋.  Corollary: every
   `T_m`-eigenvalue of a `T₂`-eigenform lies in `ℚ(λ₂)` (closes
   iteration22-review §6.1–6.2).
5. **Dim-2 integrality** (b3, `HeckeFieldDim2`): `T_m = a_m(g₁) + a_m(g₂) T₂`
   for every `m` at the six dim-2 weights, explicit integers at 28–38
   (weight 24 operator form only) — the hecke-denominators article's
   "worth formalizing" item.
6. **`Gal = S₂` for the six dim-2 `T₂` charpolys** (b3,
   `MaedaT2GaloisSmallWeights`) — closes iteration22-review §6.3; `T₂`
   Maeda (irreducible + `Gal = Sₙ`) now covers dims 2–10 like `T₃`.

## 2. Timeline as it happened

INIT 2026-11-02 (trunk from master 51a5eb1; recon: no v4.36.0 stable, scan
rc1..master over the candidate areas found 0 commits → stay rc1) →
blueprints de3e387 → wave of three worktrees → hecke-tm and hecke-index
workers found **dead** at 00:25 with no completion notice (hecke-tm had not
written its WORKLOG) → respawn with reconstruction briefings: hecke-tm
SALVAGE, 34 errors fixed in 3 passes, all 4 gates (082a98a); hecke-index G1 +
G2-generic → **operator HALT** ("stop execution"), workers killed with WIP on
disk → **operator GO** ("iteration 23 stuck, help them continue") → one
resume session compiled both checkpoints before planning: HeckeFieldDim2
green in 4 runs (25c58b8), HeckeIndexWeights green in 2 (1f98976), then the
Hecke-specific quarter (duality/independence/ring f8b412b), T-Rat every `m`
(7da668a), registration → merge-step memory pass + audit → wave merge
cc3e5fa → close-out docs c2c7c25.

## 3. What worked

- **Compile-before-planning (§4d) on every inherited checkpoint.**  All
  three salvages (hecke-tm respawn, both post-halt checkpoints) turned out
  to be mechanical API mismatches; compiling first sized each in minutes
  and nothing was rewritten from scratch.
- **Pointwise duality instead of the planned induction**: `hecke_dual`
  follows from `a₁(T_m f) = a_m(f)` plus Miller-coefficient extensionality,
  far shorter than the blueprint's route.
- **Rationality for every `m` without per-`m` data**: the Cramer route on
  𝕋-coordinates replaced the Iteration-22 recipe (one integer matrix per
  prime) — `T₃` is now a special case of the generic theorem.
- **Deferring the memory pass to the merge step** (operator option): one
  profiling pass over the final files instead of re-optimizing moving WIP.
- **The audit at the merge**: combined `AxCheckDecide` caught what the
  per-branch builds could not see (§4).

## 4. What didn't work / was forced

- **Silent worker death** (twice, no notification) and one operator halt:
  the wave cost a respawn and a resume session.  The respawn briefing now
  mandates a first-session WORKLOG entry; the hecke-tm worker had none.
- **`Finset` sums inside `decide`**: 48 `hbez` Bézout certificates decided
  a `Finset.range` sum and pulled `Classical.choice` / `Quot.sound`; fixed
  by a `List`-sum kernel certificate (`hbezL`) + `finset_sum_range_eq_list`.
  The rule already existed (`MaedaCertC`); the generator did not follow it.
  Promoted to AGENTS.md as a generator lesson.
- **`Polynomial.natDegree_map` needs `IsSimpleRing`** — false for `ℤ`;
  use `natDegree_map_eq_of_injective (RingHom.injective_int _)` (48 errors,
  one cause).  AGENTS.md.
- **Memory headroom**: the unsplit `HeckeIndexWeights` tripped the 8 GiB
  OOM flag (8.07 GiB tree, exit 42) and needed 16 GiB per run.  Profiling
  found no hot declaration — import floor ≈ 4.7 GiB + ≤ 0.08 GiB retained
  per declaration — so the fix was a split by dimension.
- **Descoped (blueprint-provisioned)**: `index_eq_det`, the index as a
  `Nat.card` of `𝕋 / ℤ[T₂]`.  `I_k` is proved as `|det A|` with its
  certificate identity, not as a lattice cardinality.

## 5. Metrics

| item | value |
|---|---|
| Modal check-runs | 63 run logs in the wave mirrors (hecke-tm 17, hecke-index 25, hecke-field 21) + the trunk merge/audit runs |
| peak memory | ≤ 6.84 GiB per module (`HeckeIndexWeights` before the split); after the merge pass: 6.56 / 5.14 / 5.44 GiB for the three per-weight files; build tree 7.79 GiB at the default 8 GiB request — no 16 GiB alerts, no escalation |
| decide certificates (combined) | 1 360, 0 beyond `propext` (was 1 312) |
| new light modules | 9: 6 trio/CI (`HeckeTM`, `HeckeIndex`, `HeckeField`, `HeckeFieldDim2`, `HeckeFieldRat`, `MaedaT2GaloisSmallWeights`) + 3 root-only (`HeckeIndexSmallWeights`, `HeckeIndexWeights`, `HeckeFieldWeights`) |
| new generators | `tools/gen_hecke_index.py`, `tools/gen_hecke_field.py` (both `--check` byte-identical) |
| CI bill added | six trio modules (11–140 s each on Modal); the per-push bill is now bounded by the selective push tier (§8) |
| lines added | ≈ 24.9 k vs master (14.4 k Lean + tools, of which ≈ 11 k generated) |
| light root | 8 499 jobs, green, 0 err / 0 warn; tauceti audit clean |

## 6. Gaps left open

1. **`[𝕋 : ℤ[T₂]] = I_k` as a lattice index** (`index_eq_det`, descoped).
2. **`D = I_k` for dims 3–4** — only `D ∣ I_k` is proved.  The equality
   has a short classical proof up to dim 4 (`ℤ[T₂] ∋ 1, T₂, T₄`, so the
   quotient is cyclic, generated by `T₃` — hecke-denominators article) and
   matches the data there; from weight 60 on it fails in general (checked
   against the generated literals: `I_k / D` = 38080 at 60, 320 at 64, …,
   ≈ 1.8·10¹⁴ at 78), so `T₃` alone does not see the index.
3. **Integrality beyond dim 2**: at dim 2, `I_k = 1` and every `T_m` is an
   integer polynomial in `T₂` (`HeckeFieldDim2`); the general statement
   `𝕋 = ℤ[T₂] ⟺ I_k = 1` is not formalized.
4. ~~**CI selective targets**~~ — [open] since Iteration 21; **resolved in
   this review** (§8).
5. 131072 Lehmer (descoped in Iteration 22; unchanged).
6. Worker liveness: no completion/failure signal for dead workers.

## 7. Recommendations for Iteration 24

1. **Watch the first master pushes under §8**: the iteration-23 merge push
   (push tier) and the first weekly full run give the measured numbers the
   estimates in §8 lack; move a family into `ci-full-only.txt` if a push
   tier run exceeds ~15 min.
2. **Close the index** (§6.1–6.3): with the duality and independence now
   in Lean, `index_eq_det` is a `Submodule`/`Basis` index computation; with
   it, `D = I_k` at dims 3–4 and `𝕋 = ℤ[T₂] ⟺ I_k = 1` would turn the 54
   certificates into a description of 𝕋 at each weight.  From dim 5 on,
   `I_k / D > 1` at most weights: the denominators of `T₃` alone
   under-count the index, so a dims-5–10 probe of which `T_m` carry the
   rest of `I_k` is the natural design step.
3. **Liveness protocol**: workers write a WORKLOG entry per gate and the
   orchestrator checks run-log timestamps rather than waiting for a
   notification.
4. Keep the merge-step memory pass + combined `AxCheckDecide` in the
   standard close-out; both earned their place this iteration.

## 8. CI selective targets (resolved in this review, 2026-11-03)

Operator steering: "resolve CI selective targets as part of current
Iteration 23 review.  we can't have CI run for too long."

**Diagnosis** (public GitHub API, `lean_action_ci.yml` run history).  The
`.lake` cache (lean-action's GitHub cache, ≈ 2.1 GiB) already makes CI
incremental: runs on a warm cache take **1 min 25 s – 2 min 09 s** (seven
measured, e.g. 4eaf528, 5760f02, 46f4e4d, b5380e9).  The long runs had two
causes, neither of them "too many targets":

1. **Overlapping pushes restore a stale cache.**  51a5eb1 (docs only)
   started at 03:56, while cb7dbba's build was still running (cache saved
   04:15); it restored the Oct-31 cache and rebuilt all of Iteration 22:
   **51 min for a docs commit**.  Several Nov-1 runs were cancelled the
   same way.
2. **Ancestor edits invalidate the expensive certificate families.**  The
   generated dim-6–10 Maeda files (T₂ and T₃, 88–1227 s each on Modal) and
   their 13 dependents rebuild whenever an ancestor changes: cb7dbba (the
   Iteration-22 merge) took **77 min**; earlier cold runs 1 h 03 – 1 h 56.

**Design** (`.github/workflows/lean_action_ci.yml`, `tools/ci_targets.py`,
`.github/ci-full-only.txt`):

* `concurrency` group per ref, `cancel-in-progress: false` — a newer push
  queues behind the running build and restores *its* cache (fixes 1).
* `paths` filter — pushes touching no Lean build input (`*.lean`,
  lakefile, manifest, toolchain, the CI files) do not run at all.
* Two tiers derived from `defaultTargets` (single source; the hand-kept
  CI copy, which had drifted into two duplicate entries, is gone):
  **push** = default targets minus the ten full-only roots and every
  target whose import closure reaches one (computed: 23 of 75 excluded —
  the ten roots, their ten Galois twins, `HeckeGeneratedByT2Weights`,
  `HeckeRationalWeights`, `HeckeFieldDim2`); **full** = all 75, on a
  weekly schedule (Mondays 03:00 UTC — a ~2 min no-op on a warm cache) and
  on `workflow_dispatch` (default).  This bounds 2: an ancestor edit costs
  the push tier only, and the expensive families are rebuilt by the full
  tier off the push path.  They stay Modal-verified at every wave merge
  and audited by `AxCheckDecide`.
* `ci_targets.py --report` is a sanity gate (fails the run on a full-only
  root outside `defaultTargets` or a default target unreachable from
  `MathProof.lean`).

**Verified locally**: the selector on this tree (75 / 52 / 23, exit 0),
both tier invocations as the workflow step runs them, a deliberate bad
root (step fails, exit 1), and the workflow YAML parsed (js-yaml).
**Not measured yet**: a GitHub run of the new workflow — it fires on the
operator's next master push.  Expected: the iteration-23 merge push builds
five new push-tier modules on a warm cache (≈ 4–6 min by Modal times);
a cold push-tier run is unmeasured (the expensive part of the old cold
runs is exactly the excluded families).

**Trade-off, stated**: between a push that edits an ancestor and the next
full run (≤ 1 week, or a manual dispatch), CI does not re-check the 23
full-only targets.  Wave merges re-verify them on Modal before the
operator merges, so a regression there needs a master push that bypassed
the wave close-out.  `HeckeFieldDim2` is full-only only because it imports
the 54-weight `HeckeGeneratedByT2Weights` for six dim-2 facts; splitting
that import would return it to the push tier (small follow-up).
