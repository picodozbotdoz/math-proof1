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

### 2026-11-03 — G2 (generic layer, HeckeTM-free part) CLOSED

* Added to `HeckeIndex.lean` (all weight-generic, still zero HeckeTM
  dependency — per blueprint §4 descope: the Hecke-specific quarter waits for
  b1's G3):
  - `cramer_inverse` — the blueprint's Cramer inverse in signed-det form:
    `C.det • u j = ∑_i (C.adjugate j i) • P i` from the expansion hypothesis
    alone (Kronecker row through `cramer_scale`; no det ≠ 0 needed — the
    |det|-packaging is the data side's business, G1 pinned the sign there).
  - `aeval_rat_witness` — `aeval T ((∑ C (r j) X^j).map (algebraMap ℚ ℂ)) =
    ∑ (r j) • T^j`: the entrywise-certificate → operator bridge.
  - `aeval_div_witness` — `d • T₃ = ∑ (r j) • T₂^j → T₃ = aeval T₂
    (∑ C (r j / d) X^j).map`: the packaging that turns BOTH per-weight
    integer certificates (the G1-pinned `∑ w'_i M₂^i = I_k M₃` and
    HeckeRational's `∑ N_j M₂^j = D • M₃`) into the two `aeval`
    representations `den_dvd_index` consumes.  With these, the G4 composite
    `D ∣ I_k` is fully wired generically.
* Pin gotchas discovered (for the log):
  - `map_sum`/`map_pow` are HomClass-based at the pin — `rw` with them bare
    leaves an instance metavariable in the pattern and the match silently
    fails ("did not find"); pass the function argument explicitly
    (`map_sum (Polynomial.aeval T) _ _`, `map_pow (Polynomial.aeval T) X j`).
    For polynomial.map itself use the dedicated `Polynomial.map_sum`.
  - `algebraMap ℚ ℂ ≠ Rat.cast` syntactically (both appear); bridge:
    `DivisionRing.toRatAlgebra`'s algebraMap is `Rat.castHom`, and
    `Rat.coe_castHom` is `rfl` — captured as the private
    `algebraMap_rat_eq_cast (x : ℚ) : algebraMap ℚ ℂ x = (x : ℂ) := rfl`.
  - `smul_eq_mul` does not fire for `c • (T : Module.End ℂ V)` (algebra-smul,
    not the mul-derived instance) — use `Algebra.smul_def` (as `←`).
  - `Finset.sum_eq_single` subgoal hygiene: the pos-branch needs
    `ite_eq_left rfl` + `Int.cast_one` + `one_smul` (not `smul_eq_mul`), and
    the ℤ-coefficient variant needs `one_mul` (not `mul_one`).
* Modal runs: 01:12 run 5 (3 errors + 4 warnings), 01:24 run 6 (1 error),
  01:33 run 7 (1 error), 01:44 run 8: **GREEN — 0 err / 0 warn**, 41 s,
  6.02 GiB.  715 lines; tauceti audit clean.
* Commit: the G2-generic closure.

### 2026-11-03 — G3 CLOSED (eval_det route measured and decided)

* Inbox re-polled: still empty.
* Route measurement (throwaway emitter
  `/home/doz/tmp/math-proof1-temp/agent-work/hecke-index/emit_scratch_det.py`,
  conventions lifted from `gen_hecke_rat.py`: Horner base 10^74, lines ≤ 98,
  plain literals ≤ 80 digits): untracked scratch
  `MathProof/ModularForms/HeckeIndexScratch.lean` with the WORST weight 134
  (dim 10, A-entries ≤ 180 digits chunked, det = +462 digits chunked;
  det(A₁₃₄) computed exactly in Python for the statement) and
  `theorem det_A134 : A134.det = … := by simp only [A134]; eval_det; norm_num`.
* Modal run 9 (01:57): **GREEN**, 37 s wall, peak 5.95 GiB — `eval_det`
  (NormDet's Bareiss simp-proc) fires on the 10×10 chunked-entry literal and
  `norm_num` closes the 462-digit Horner in seconds.  The route is CHEAP at
  the worst case; **decision: primary `eval_det`, no CharpolyEngine
  fallback, no det-avoiding route needed** (blueprint G3 fallbacks moot).
* Emission facts pinned for the generator: the matrix literal needs
  `simp only [A_def]` before `eval_det` (the simproc needs the literal);
  entries as parenthesized Horner chunks are accepted; det-literals use the
  nested Horner form (all exponents 74 ≤ 256); `norm_num` closes the chunked
  RHS.  Sign: det(A) computed exactly per weight and emitted signed.
* `den_dvd_index` (G3's second half) is already generic in `HeckeIndex.lean`
  (G2 closure); the per-weight instantiations are G4 emissions.
* Scratch kept untracked as the generator's reference emission; deleted at
  G4 close.

### 2026-11-03 — operator resume: G4 weights file GREEN

* Resumed after the OPERATOR HALT on the operator's go.  Compile-before-
  planning: the inherited uncommitted generator + regenerated
  `HeckeIndexWeights.lean` (the predecessor's in-flight fixes for the
  minpoly_nd rw-chain / dim-2 det_A / T2 names / imports) were built
  verbatim first.
* Run 1 (8 GiB request): 48 errors, ONE cause — `Polynomial.natDegree_map`
  needs `[IsSimpleRing R]` at the pin, and ℤ is not; every other inherited
  fix held.  (Peak tree 7.99 GiB tripped the OOM flag, exit 42; module
  itself 6.74 GiB.)  488 s.
* Fix (generator): `Polynomial.natDegree_map_eq_of_injective
  (RingHom.injective_int _)`; regenerated, `--check` byte-identical,
  48-line diff.
* Run 2 (16 GiB request): **GREEN — 0 err / 0 warn**, 340 s, module peak
  6.84 GiB (tree 8.07 GiB; below the 16 GiB alert line).  54 weights,
  48 full `D ∣ I_k` composites.  tauceti audit clean.
* Scratch `HeckeIndexScratch.lean` deleted (G3 reference emission, absorbed).
* Remaining for G4: combined `AxCheckDecide` on the merged root; research-log
  draft.

### 2026-11-03 — G2 Hecke-specific quarter CLOSED (b1 merged)

* Added to `HeckeIndex.lean` (imports `HeckeTM` now; 3 Modal runs, run 3
  **GREEN 0 err / 0 warn**, 44 s, module peak 4.80 GiB = the import floor):
  - `coeff_heckeTM_symm` — `a_l(T_m f) = a_m(T_l f)` straight from the
    symmetric coefficient formula (`gcd_comm`, `mul_comm`);
  - `miller_expand` / `eq_of_miller_coeff` — a normalized independent family
    of `dim S_k` forms is a basis; forms are determined by `a_1 … a_n`;
  - `hecke_dual` — `T_m = ∑_j a_m(g_j) • T_{j+1}` for every `m ≥ 1`.
    DEVIATION (simplification): proved POINTWISE, not by strong induction on
    `m` — compare Miller coordinates; `a_{l+1}(T_m f) = a_m(T_{l+1} f)` turns
    both sides into the Miller expansion of `T_{l+1} f` read at `q^m`;
  - `hecke_independent` — dual functionals `T ↦ a₁(T g_i)` (`heckeTM_one`);
  - `heckeLattice` (`span_ℤ {T_1…T_n}`), `heckeTM_mem_lattice`,
    `heckeLattice_mul_mem` (closure from `heckeTM_mul`; needs `k ≥ 1`),
    `heckeRing : Subring (End S_k)`, `T2_pow_mem_heckeRing` (ℤ[T₂] ⊆ 𝕋).
    The ring layer takes an integrality hypothesis `hint` on the Miller
    coefficients (all `m`) — generic; per-weight discharge is not part of G4.
* DESCOPE (blueprint-provisioned, G2): `index_eq_det` (the `Nat.card`
  lattice-index packaging) not formalized; the mathematical content stands
  as `I_k = |det A| ≠ 0` (per-weight `det_A`) + the two spanning families
  (`hecke_dual`, Cramer certificates).  CORRECTIONS-noted follow-up.
* Pin gotchas: `LinearMap.coeFn_sum` does not exist — use
  `LinearMap.sum_apply`; `haveI` for a Prop triggers `linter.style.haveILetI`.

### 2026-11-03 — combined AxCheckDecide: 48 violations found and fixed

* Run 1 (`--target MathProof.AxCheckDecide`, 16 GiB, 464 s): **1360
  certificates audited, 48 depend on more than propext** — every one a
  per-weight `hbez` (`∑ j ∈ Finset.range n, bez j * cert j + bezc * Dn = 1 :=
  by decide +kernel`): the `Finset` sum goes through `Multiset`'s quotient,
  pulling `Classical.choice` + `Quot.sound` (the CLAUDE.md "List, not
  Finset, inside certificates" rule — the G4 generator broke it).
* Fix (generator): the decide is now `hbezL` over
  `((List.range n).map fun j => bez j * cert j).sum`, and `hbez` is derived
  from it by `MaedaLevelOne.finset_sum_range_eq_list` (no decide).
  Regenerated, `--check` byte-identical.
* Run 2: **1360 audited, 0 depend on more than propext**; build 345 s,
  HeckeIndexWeights module peak 6.83 GiB.  G4 audits CLOSED.

### 2026-11-03 — merge-step memory pass: weights file split by dimension

* Profile (`LEAN_CHECK_PROFILE=…HeckeIndexWeights`, run from the merged
  hecke-field tree): NO hot declaration — the largest per-command growth is
  +0.08 GiB (the dim-10 `scaled` entrywise decides, ~19 s each); the cost is
  the import floor (~5.4 GiB for the lean process once HeckeRationalWeights
  + small/dim4/dim5 parents are loaded) plus ~1.1 GiB of retained literals
  accumulating over the 54 blocks.  The lake tree peaked at 8.07 GiB —
  over 97 % of the default 8 GiB request, so every run was OOM-flagged and
  escalated to 16 GiB.
* Fix: `gen_hecke_index.py` now emits two files with disjoint imports —
  `HeckeIndexSmallWeights` (dims 2–5, 24 weights) and `HeckeIndexWeights`
  (dims 6–10, 30 weights); `--check` covers both.  Root-only registration
  for both (lakefile note updated).
* Measured at the DEFAULT 8 GiB request: small 69 s, module 5.14 GiB (tree
  6.38); big 336 s, module 6.56 GiB (tree 7.79, was 8.07) — no escalation.
  Margin on the big file is thin (0.16 GiB under the 97 % line); the floor
  is HeckeRationalWeights' own closure, which this file genuinely needs
  (its `cert`/`hM2`/`hM3`).
