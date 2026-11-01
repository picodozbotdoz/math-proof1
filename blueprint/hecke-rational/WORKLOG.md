# Worklog — impl/iteration22/hecke-rational

Append dated entries as you go (stage gates passed/failed, Modal runs with
build time + peak RSS, decisions, deviations from the blueprint).  This file
is the inter-session resume point: make it possible to continue cold.

Blueprint: blueprint/hecke-rational/BLUEPRINT.md (in this worktree) — a STARTING
POINT, not a contract: run its G1 audit, then deviate per the deviation
protocol (RESEARCH-WORKFLOW §4d) whenever facts disagree, with evidence here.
Base commit: 569bcf0 (trunk dev/iteration22-maeda-lehmer).

## Entries

### 2026-11-02 (worker hecke-rational, session 1) — G1 data audit PASSED

Inbox polled: empty (only README + empty done/). No STEER for me.

Ran `research/iteration22/hecke-rational/g1_audit.py` (python3 -I, committed):
ground truth = Lean literals; census JSONs demoted to cross-checks.

- **54 weights enumerated** (24 small in MaedaT3SmallWeights = weights
  24..74 with dim 2..5; 30 big in MaedaT3Dim{6..10}Weights). NOTE: weight 74
  is dim 5 (small) — routing must use the T₃ source file, not `k ≥ 72`
  (first audit bug, fixed).
- **M₃** parsed from all 54 T₃ sections == census (maeda_t3_dim6_10 /
  maeda_t3_small). **M₂** parsed from 30 T₂ dim sections == census
  (maeda_dim6_10). charpoly(M) == the files' `P` literals (my Faddeev–
  LeVerrier + P-parser; both had bugs, fixed — parser validated against
  Lean-proved data).
- **M₂ re-derived for all 24 small weights** from the T₃ file's q-lemma
  values + the heckeT2_coeff formula `(T₂f)_m = f_{2m} + 2^{k-1}[2|m]f_{m/2}`
  + coordN back-substitution. Cross-checks: derived Xtab2 == the T₂ files'
  t-lemma values (dims 2–5, 23 weights); charpoly(M₂) == the T₂ files' `P`
  literals; weight 24 M₂ == the `toMatrix_heckeT2` literal
  `[[696,1],[20736000,384]]` (MaedaWeight24's basis ΔE₄³,Δ² is the same
  echelon basis as the T₃ file's prodForm basis).
- **Alignment audit (load-bearing for the defeq bridge)**: for all 30 big
  weights, the T₂ and T₃ dim-file sections have *syntactically identical*
  `fb`, `Atab`, and `f{i}` def bodies → `MaedaWeight{K}.fb/Atab` are defeq
  to `MaedaT3Weight{K}.fb/Atab`, so the T₂ file's `hX`/`entry_*` lemmas
  apply verbatim against the T₃ file's basis.
- **Small-weight T₂ inventory (blueprint G1 ask)**: NO literal M + Xtab in
  the T₂ small files (dims 2–5 use charpoly_dim2/3/4/5 directly) — but the
  t-lemma coefficient data is complete, and the re-derivation above closes
  the gap. **No descope: all 54 weights in scope.**
- `[M₂,M₃]=0` verified at every weight; ℚ-solve of `∑_j q_j M₂^j = M₃`
  unique + exact (rank n; scaled identity `∑ N_j M₂^j = D·M₃` asserted
  cellwise). Certificate magnitudes: dim 2: N ≤ 6 digits, D = 1 (integer
  polynomials at w24/28/30/32/34/38!); dim 10 w134: N ≤ 381 digits,
  D = 349 digits, identity cells ≤ 430 digits (inside kernel-decide range;
  the existing dim-10 decides handle comparable magnitudes).

Data: `research/iteration22/hecke-rational/g1_data.json` (per weight:
M2, M3, Atab, N, D, q-lemma values, stats).

**Route decision (matches blueprint §2, refined):**
- generic module `HeckeRational.lean`: `represents_dimN` (echelon→
  representation, sibling of charpoly_dimN internals) + `exists_aeval_rat…`
  (representations + scaled integer matrix identity ⇒ ∃ Q : ℚ[X]); the ∃
  witness is BUILT inside as `∑ C (N j / D) * X^j` — no ℚ-coefficient
  literals needed, only chunked ℤ literals for N_j, D.
- dims 6–10: reuse the T₂ dim files' Xtab/hX/M/entry verbatim (defeq bridge,
  audited above). small weights: generate Xtab2 + hX2 (heckeT2_coeff + the
  T₃ file's q-lemmas, mirroring the T₃ file's own t-lemma pattern) + Lv/entry
  lemmas + M₂ literal fresh (n ≤ 5, cheap).
- No commutation hypothesis needed anywhere (the identity IS the proof).

Next: G2 generic module.
