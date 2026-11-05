# Worklog — impl/iteration24/index-card
Append dated entries as you go (stage gates passed/failed, Modal runs with
build time + peak RSS, decisions, deviations from the blueprint).  This file
is the inter-session resume point: make it possible to continue cold.
## Entries

### 2026-11-04 — session 1 start: read docs, plan, G1 beginning
- Read (in order): worktree AGENTS.md (byte-identical to main tree's), CODING_STANDARDS.md
  (main tree — worktree has no external-doc/), RESEARCH-WORKFLOW §4d/§5/§6/§9,
  blueprint/index-card/BLUEPRINT.md, research/iteration24/FINDINGS.md.
- Inbox poll (checkpoint: session start): no STEER-index-card-* / STEER-all-* files in
  /home/doz/claude-workdir/math-proof1_2/external-doc/inbox/ (only README.md + empty done/).
- Worktree state: branch impl/iteration24/index-card at f7628f6 (= briefed base), clean
  except untracked WORKLOG (this file).  Seeded runner
  /home/doz/tmp/math-proof1-temp/agent-work/index-card/runs/mrun.sh present and read.
- Plan (mirrors BLUEPRINT §4):
  - G1: audit script under research/iteration24/index-card/ re-deriving C per weight
    from prodForm arithmetic (probe machinery), |det C| = landed Ik for all 54 (parse
    the Lean files, not index_data.json), pin per-weight minpoly-degree fact names.
    Commit script + data.
  - G2: MathProof/ModularForms/HeckeLatticeIndex.lean (light, generic): t2Lattice,
    ℤ-bases of t2Lattice/heckeLattice, relIndex_t2_eq_det via
    AddSubgroup.relIndex_eq_natAbs_det with ambient = 𝕋's own additive group (F6
    caveat), corollary index_eq_natCard.  Modal green via mrun.sh.
  - G3: extend tools/gen_hecke_index.py (all --check modes byte-identical), generate
    HeckeIndexCardSmallWeights.lean (dims 2–5) green.
  - G4: HeckeIndexCardWeights.lean (dims 6–10) + registration (root + defaultTargets
    for light small file; big file root-only) + audits (light root 0/0, AxCheckDecide,
    tauceti_audit.sh).
- Heartbeat convention understood; entry before/after any >10 min run.

### 2026-11-04 — G1 CLOSED (audit green, 0 failures / 54 weights)

Script: `research/iteration24/index-card/g1_audit.py` (+ `g1_data.json`), imports
the iteration-23 machinery (`research/iteration23/hecke-index/g1_audit.py`) —
imported, not copied, per the FINDINGS convention.  All checks pass for all 54
weights:

- **D1** landed `Atab`/`M2` literals == re-derived prodForm tables (imported
  iteration-23 checks, re-run fresh).
- **D2** μ (the fb-coefficients of the Miller basis, `mu[j][c] = coeff of f_c in
  g_j`) computed two ways — (a) probe-style from raw prodForm rows, (b)
  Lean-def-style from the LANDED `Atab` literal alone (the accumulator shape the
  planned `millerTopC` Lean def will kernel-reduce to) — agree, and `μ·rrows ==
  miller rows` on the nose (q^1..q^{4n}).
- **D3** *design-correcting check*: the landed `A` literal holds the
  **single-operator** coordinates `A i j = a_{2^i}(g_j)` (T_{2^i}); the
  **composition-power** coordinates (row 0 of `M2m^i`, what `t2Lattice` is
  spanned by) are `Q·A` row i, where Q is the q-transform (`T₂^i = ∑_s q_{i,s}
  T_{2^s}`, `q_{i+1,s} = q_{i,s-1} + 2^{k-1} q_{i,s+1}`, unit triangular).
  Verified: `row0(M2m^i) == (Q A) row i` ENTRYWISE for all 54.  (The iteration-23
  audit had only checked `|det A| = |det C|`; the blueprint's "C" IS `Q·A`, not
  `A` itself — the design below absorbs this with a per-weight `Qw` literal and
  `det Qw = 1`.)
- **D4** p/q transforms (`T_{2^i} = ∑_s p_{i,s} T₂^s`, two-term recurrence from
  the LANDED `heckeTM_two_mul_even`) are an inverse pair, `det Q = 1`,
  `|det (Q·A)| = Ik` for all 54.
- **D5** **THE STAR CERTIFICATE** — the identity each per-weight Lean file will
  `decide +kernel` — holds on the LANDED literals for all 54 weights:
  `A[i][j] = ∑_s p[i][s] · ∑_c μ[j][c] · (M2^s)[0][c]` with p from k, μ from the
  landed Atab, M2 the landed literal.
- **D6** inventory: `minpoly_nd` landed at exactly the 48 weights with `D ≠ 1`
  (all dims 3–10); the six dim-2 weights need a fresh emission (route:
  `MaedaWeightK.charpoly_heckeT2` + `maeda_weightK` + `MaedaT3WeightK.finrank_eq`
  + `HeckeGeneratedByT2.minpoly_eq_charpoly_of_map_of_irreducible`, the
  `HeckeFieldWeights.hmin` shape).  c-lemma count = n everywhere (hfi route).
  det_A signs pinned per weight (mixed ±).

Data sizes (maxima): μ entries ≤ 24 digits; p/q coefficients ≤ 161 digits
(powers of `2^{k-1}`, k ≤ 134); `Ik` ≤ 462 digits (w134, dim 10).

**G2 design validated by the audit** (recorded here since it corrects the
blueprint's step (i) at the design level, §4d — no Lean code contradicted):
- `C` in `relIndex_t2_eq_det` = `Qw * A` (per-weight `Qw` literal, det 1); the
  final index statement still lands on the landed `Ik` via
  `det_mul → det Qw = 1 (eval_det) → det_A (landed)`.
- Per-weight kernel certificate: ONE entrywise matrix identity
  `Sterm = A` (`ext i j; fin_cases …; decide +kernel`, the landed `scaled`
  shape) where `Sterm i j = ∑ s ∈ range n, pfn c i s * ∑ c' ∈ range n,
  millerCoeff atabZ n j c' * (M2 ^ s) 0 c'`.
- Generic bridge lemmas needed (all landed-hypothesis-shaped): μ-bridge
  (`miller f A n j = ∑ ((millerCoeff …):ℤ):ℂ) • f c`), p/q-transform operator
  lemmas (`heckeTM_two_mul_even` is LANDED and gives exactly the two-term
  recurrence), the ⋆-transport to `T_{2^i} = ∑ A i j • T_{j+1}` (via
  `hecke_dual` + `coeff_heckeTM_symm` + `pow_rep` + `a_1(fb l) = δ`), and the
  `relIndex` core on `AddSubgroup.relIndex_eq_natAbs_det` with the
  `Submodule.toAddSubgroup_toIntSubmodule` round trip.

No Modal run needed for G1 (pure python audit; ground truth = landed Lean
literals).  Inbox: clean at this checkpoint.
- Read (in order): worktree AGENTS.md (byte-identical to main tree's), CODING_STANDARDS.md
  (main tree — worktree has no external-doc/), RESEARCH-WORKFLOW §4d/§5/§6/§9,
  blueprint/index-card/BLUEPRINT.md, research/iteration24/FINDINGS.md.
- Inbox poll (checkpoint: session start): no STEER-index-card-* / STEER-all-* files in
  /home/doz/claude-workdir/math-proof1_2/external-doc/inbox/ (only README.md + empty done/).
- Worktree state: branch impl/iteration24/index-card at f7628f6 (= briefed base), clean
  except untracked WORKLOG (this file).  Seeded runner
  /home/doz/tmp/math-proof1-temp/agent-work/index-card/runs/mrun.sh present and read.
- Plan (mirrors BLUEPRINT §4):
  - G1: audit script under research/iteration24/index-card/ re-deriving C per weight
    from prodForm arithmetic (probe machinery), |det C| = landed Ik for all 54 (parse
    the Lean files, not index_data.json), pin per-weight minpoly-degree fact names.
    Commit script + data.
  - G2: MathProof/ModularForms/HeckeLatticeIndex.lean (light, generic): t2Lattice,
    ℤ-bases of t2Lattice/heckeLattice, relIndex_t2_eq_det via
    AddSubgroup.relIndex_eq_natAbs_det with ambient = 𝕋's own additive group (F6
    caveat), corollary index_eq_natCard.  Modal green via mrun.sh.
  - G3: extend tools/gen_hecke_index.py (all --check modes byte-identical), generate
    HeckeIndexCardSmallWeights.lean (dims 2–5) green.
  - G4: HeckeIndexCardWeights.lean (dims 6–10) + registration (root + defaultTargets
    for light small file; big file root-only) + audits (light root 0/0, AxCheckDecide,
    tauceti_audit.sh).
- Heartbeat convention understood; entry before/after any >10 min run.

### 2026-11-05 — session 2 start (fresh respawn after operator wrap-up 2026-11-04 ~22:15)
- Resume point: G1 CLOSED (do-not-redo).  Branch tip 9e518e1 = salvage of WIP
  `MathProof/ModularForms/HeckeLatticeIndex.lean` (582 lines, correctness not asserted).
- Plan: build the salvage on Modal first to learn its state (G2), then G3, G4.

### 2026-11-05 — G2 CLOSED: HeckeLatticeIndex.lean green 0 err / 0 warn
- Salvage build (run 1): 2 errors + 1 unused-variable warning only — the WIP was
  essentially complete.  Fixes: (a) `det_eq_of_expansions` section variable
  `[Module ℤ M]` removed (instance diamond with `AddCommGroup.toIntModule` on the
  span); (b) `hmem` now rewrites with the ℤ-smul expansion `hw` (ℂ-smul cast form
  fails `Submodule.smul_mem` over ℤ); (c) `Finsupp.finsetSum_apply` + `smul_eq_mul`
  + `simp [Matrix.transpose_apply]` in the toMatrix computation; (d) dropped the
  unused `hA` binder of `coeff_one_t2_pow`.
- Modal (mrun.sh --file, warm cache): wall 54 s, peak tree 6.01 GiB, module 4.77 GiB.
  tauceti_audit: 0/0/0/0, imports OK.  No relIndex/toIntSubmodule defeq wall — the
  `relIndex_eq_natAbs_det` route went through as designed; no Nat.card descope.
- DESIGN DEVIATION from G1's "star certificate" plan (recorded per §4d): the WIP
  uses the simpler DUAL route — `C i j = a_1(T₂^i g_j) = ∑_c μ_{jc} (M2^i)_{0c}`
  (`hcard : Matrix.of (fun i j => ∑ c, millerCoeff a n j c * (M2^i) 0 c) = C`),
  so no p/q transforms or Q literal are needed; `T₂^i = ∑_j C i j • T_{j+1}` by
  duality (`op_eq_zero_of_dual_zero`).  |det C| = I_k by G1 D3 (C = Q·A, det Q = 1);
  the generator re-checks |det C| = |Ik| per weight in Python.
- Exported generic API (shape kept for index-cyclic): `t2Lattice`,
  `relIndex_t2_eq_det`, `natCard_quot_eq_det`, `millerTopC`/`millerCoeff`,
  `miller_eq_fb_sum`, `coeff_one_heckeTM`, `op_eq_zero_of_dual_zero`,
  `coeff_one_t2_pow`, `t2_pow_eq_smul_heckeTM`, `index_card_hecke`,
  `index_card_hecke_natCard` (binder list unchanged except `coeff_one_t2_pow`).
- Inbox poll: no STEER-index-card-* / STEER-all-*.

### 2026-11-05 — G3 in flight: generator `--card` mode + first small-file build
- HeckeLatticeIndex.lean: added the per-weight entry points `heckeTM_two_rep_of_dimN`
  (hrep2 from the landed coordN data), `index_card_dimN`, `index_card_natCard_dimN`
  (signed literal `I` with `hdet : C.det.natAbs = I.natAbs`).
- tools/gen_hecke_index.py: new `--card` mode (CARD_PARTS: HeckeIndexCardSmallWeights
  dims 2–5 / HeckeIndexCardWeights dims 6–10); `--check` now covers all four files
  (legacy two still byte-identical).  Data = landed literals via the i23/i24 G1 parsers;
  generator asserts |det C| = Ik for all 54 (passed) and μ == i24 audit accumulator.
- Starting Modal build of HeckeIndexCardSmallWeights (expected 5–15 min: parents may
  be cold in the build cache).

### 2026-11-05 — G3 CLOSED: HeckeIndexCardSmallWeights.lean green 0 err / 0 warn
- Modal (mrun.sh --file, warm): wall 55 s, peak tree 6.44 GiB, module 5.20 GiB
  (elaboration 23 s for the 24 weights).  Two fix rounds: `omit [NeZero n] in` on
  `heckeTM_two_rep_of_dimN` (unusedSectionVars), and dim-2 `hAeq` via
  `obtain rfl : j = 1 / i = 0 := by omega` (`<;>` on one goal tripped unusedTactic;
  a bare `interval_cases i` after `interval_cases j` left the goal unsolved).
- `python3 -I tools/gen_hecke_index.py --check`: all 4 files byte-identical.
  tauceti_audit: 0/0/0/0 on both Lean files.
- Exported per-weight facts (namespace `HeckeIndexCardWeightKK`, all 24 weights k ≤ 74):
  `index_card : (t2Lattice (heckeTM ((k:ℕ):ℤ) 2) n).toAddSubgroup.relIndex
     (heckeLattice ((k:ℕ):ℤ) n).toAddSubgroup = HeckeIndexWeightKK.Ik.natAbs`
  `index_card_natCard : Nat.card (↥(heckeLattice ((k:ℕ):ℤ) n).toAddSubgroup ⧸
     (t2Lattice (heckeTM ((k:ℕ):ℤ) 2) n).toAddSubgroup.addSubgroupOf
     (heckeLattice ((k:ℕ):ℤ) n).toAddSubgroup) = HeckeIndexWeightKK.Ik.natAbs`
  (+ helpers atab, hAeq, hfi, hmin, C, hcard, det_C).  For index-cyclic: the
  `t2Lattice` operator is `heckeTM k 2` (bridge to `HeckeRatWeightKK.T2` by
  `HeckeTM.heckeTM_prime`, as in the recipe).
- Registration deviation (to apply in G4): the small file's parent
  `HeckeIndexSmallWeights` is root-only (imports the non-CI `MaedaT3SmallWeights`),
  so the card small file must be root-only too — NOT defaultTargets (blueprint §2
  said defaultTargets; that would pull a non-CI parent into CI).  HeckeLatticeIndex
  itself → root + defaultTargets.
