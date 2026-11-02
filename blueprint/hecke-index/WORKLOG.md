# Worklog — impl/iteration23/hecke-index

Base: de3e387 (trunk `dev/iteration23-hecke-ring`, blueprints commit).
Blueprint: `blueprint/hecke-index/BLUEPRINT.md` — a STARTING POINT, not a
contract: G1-audit it, deviate per the §4d deviation protocol when facts
disagree (evidence here; corrections to the trunk).

Append dated entries as you go (gates passed/failed, mrun.sh Modal runs with
time + peak RSS, decisions, deviations).  This file is the inter-session
resume point: make it possible to continue cold.

## Entries

### 2026-11-02 — G1 data audit CLOSED (Miller strategy (a) chosen)

* **Probe re-run**: `research/iteration23/probe2-hecke-index/probe_index.py`
  regenerates cleanly at the pin (3 m 12 s, all F1–F7 pass, 54/54).
* **G1 audit script**: `research/iteration23/hecke-index/g1_audit.py` (new,
  self-contained like iteration-22's `g1_audit.py`); writes
  `research/iteration23/hecke-index/index_data.json`.  3 m 12 s, 0 failures.
  Checks C1–C6 at all 54 weights, re-pinned DIRECTLY to Lean literals (no
  g1_data.json intermediary):
  - C1 fb re-pin: Lean `Atab` + `q{i}_{m}` lemmas == raw prodForm rows
    (q-lemma coverage to 3n) — fb IS the raw basis, 54/54.
  - C2 Lean `M` literals == re-derived fb-coordinate matrices of T₂/T₃:
    dims 6–10 from `MaedaDim{d}`/`MaedaT3Dim{d}Weights`; dims 2–5: M3 from
    `MaedaT3SmallWeights`, M2 from `HeckeRationalSmallWeights` (landed
    literal, kernel-pinned by its entryT2 lemmas).  54/54.
  - C3 Miller: normalization, `Tmat` integer upper-unitriangular, |det| = 1,
    conjugation bridge `Tmatᵀ·M2m = M2r·Tmatᵀ`.  54/54.
  - C4 `|det A| = |det C| = I_k ≠ 0`; C5 Cramer certificate
    `∑ w'_i·M2Lean^i = I_k·M3Lean` entrywise ON THE LEAN-PARSED literals;
    C6 committed (N, D) parsed from the landed `cert`/`scaled_id` literals
    (new plain/flat/Horner integer-expression parser): D ∣ I_k and
    `w' = (I_k/D)·N`.  54/54.
* **Sizing** (matches probe F7; worst dim 10): A ≤ 180d, I_k ≤ 462d,
  w' ≤ 494d, M2^i ≤ 248d → Horner base-10^74 chunks as planned.
* **Data findings**:
  1. The landed HeckeRational `D` is ALREADY reduced at all 54 weights
     (`norm_certificate` divides out the gcd) — `Dred == D` everywhere;
     reuse it as "the" D, no re-reduction layer needed.
  2. `Ik/D == 1` exactly at dims 2–4 (44 weights... precisely: every weight
     with n ≤ 4), proper divisor from dim 5 — the article's prediction,
     re-confirmed on Lean-pinned data.
  3. Bézout witnesses for `gcd(D, N) = 1` (needed by `den_dvd_index`):
     naive sequential extgcd reaches 2677d at dim 10; a tree-ordered
     combination (N's first, then D once) should stay ≈ 400d — emission
     strategy to be measured at G4; descope provision: per-weight `D ∣ I_k`
     only for dims 2–5 (witness ≤ 89d) if the dim-10 witness fights.
* **Miller-strategy DECISION (a)** (blueprint recommendation, confirmed by
  C3/C5): build the Miller basis in Lean as the unit-triangular reduction of
  `fb` — well-founded recursion `miller f A n j = f j − ∑_{s} A j (n−1−s) •
  miller (n−1−s)` (analytic module, no kernel decides on it, so WF is
  acceptable; CODING_STANDARDS' structural rule targets decided content);
  the per-weight certificates stay in fb coordinates (basis-independent
  operator identities — C5 verifies them on the landed fb literals), so no
  fb↔Miller bridge is needed inside any certificate.
* Commit: `research/iteration23/hecke-index/{g1_audit.py,index_data.json}`.

### 2026-11-03 — respawn recovery: inherited WIP compiled GREEN (SALVAGE)

* Session start ~00:20 UTC. The predecessor died ~2026-11-02 20:04 with no
  completion notification; inherited: committed G1 (a8a2412) + untracked WIP
  `MathProof/ModularForms/HeckeIndex.lean` (the G2 generic layer, never
  Modal-compiled).
* Inbox polled at session start: empty (no STEER files).
* b1 (hecke-tm) checked per recovery procedure: branch still at seed 4154d33,
  untracked WIP `HeckeTM.lean`/`HeckeTMScratch.lean`, its last run BUILD
  FAILED — G3 NOT landed. Per blueprint §4 sequencing: NOT blocking; G2's
  HeckeTM-dependent quarter (hecke_dual, hecke_independent, the subring, the
  adjugate Cramer inverse at the operator level) is deferred until b1's G3
  lands and the merge happens.
* **WIP verdict: SALVAGE** — the architecture is sound; 15 mechanical
  proof-side errors, no structural rewrites needed. Fixes applied:
  - `miller_coeff`: two IH calls had wrong argument order (the `r ≤ n` and
    the `m` slots).
  - `Fin.val_eq_val` does not exist at the pin → `Fin.val_inj`.
  - `Polynomial.finset_sum_coeff` → `Polynomial.finsetSum_coeff` (renamed).
  - `Polynomial.natDegree_sum_le` now takes the Finset as its first explicit
    arg; switched to `natDegree_sum_le_of_forall_le` with a stated bound.
  - `if_pos`/`if_neg` deprecated → `ite_eq_left`/`ite_eq_right` (warnings are
    blockers); note `ite_eq_left (h : c)` = if_pos, `ite_eq_right (h : ¬c)` =
    if_neg.
  - `Finset.sum_comm'` demands a membership-iff side hypothesis at the pin →
    plain `Finset.sum_comm` everywhere.
  - `rw` with Matrix-application patterns inside `rw`-congr term-blocks fails
    pattern elaboration ("function expected") → restructured into typed
    have-steps (`hper`, `hstep`, `hcoef`).
  - **Gotcha for the log**: plain `rw` CANNOT instantiate a first-order
    pattern (e.g. `mul_assoc`'s `?a * ?b * ?c`) at a match under a GOAL
    binder when the instantiation contains the bound variable — the match is
    rejected (capture) and rw silently moves on, then reports "did not find".
    Higher-order/Miller matches (the `?f x` of `Int.cast_sum`/`sum_congr`)
    DO work under binders, and everything works on tactic-context locals
    (inside `fun j _ => by ...`).  Workaround used in `den_dvd_index`:
    split into a bare-sum `sum_congr` step (`hB`) + binder-free ground
    rewrites (`mul_assoc c D Ik`).
* Modal runs (`./mrun.sh --file MathProof/ModularForms/HeckeIndex.lean`):
  - 00:26 run 1 (inherited WIP verbatim): BUILD FAILED, 15 errors;
    lake wall 49 s, peak 6.01 GiB.
  - 00:40 run 2: BUILD FAILED, 9 errors; 50 s, 6.00 GiB.
  - 00:47 run 3: BUILD FAILED, 1 error (stuck `AddCommMonoid ?m`: `sum_congr`
    refined against an HAdd-headed goal — its β never gets assigned); 64 s,
    5.99 GiB.
  - 00:55 run 4: **GREEN — 0 err / 0 warn**, 51 s, 6.01 GiB (below the 16 GiB
    alert line). 630 lines, analytic-only, no kernel decides; tauceti audit
    clean (0 sopt/eval/nat/sorry/bad-imports).
* Compiling now (all weight-generic, no HeckeTM dependency):
  `millerTop`/`miller` + `miller_coeff`/`miller_coeff'` (G1 Miller strategy
  (a)), `miller_linearIndependent`, public `pow_rep`, `int_poly_of_rep` /
  `int_poly_of_dimN` (integer Cramer certificate glue), `cramer_scale`
  (abstract Cramer inversion), `aeval_inj_of_minpoly`, `den_dvd_index`
  (reduced-denominator divisibility).
* Next: G2 remainder — abstract Cramer inverse over a u-family + the
  Hecke-specific duality/independence/ring layer against b1's names
  (compiled only after the merge).
