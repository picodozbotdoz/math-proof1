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

### 2026-11-02 — G2 PASSED: generic module green + weight-24 test drive green

Inbox polled: still empty.

`MathProof/ModularForms/HeckeRational.lean` (new light module, imports only
`CharpolyDimN`):

- `linearIndependent_dimN`, `represents_dimN` — echelon bundle →
  representation (sibling of `charpoly_dimN`, internals copied/adapted);
- `exists_aeval_rat_of_rep` (V-generic) + `exists_aeval_rat_dimN`
  (CuspForm echelon bundle master, the single lemma the generated files
  consume); witness built internally as `ratWitness c D =
  ∑ j < n, C (c j / D) * X ^ j` — only ℤ literals `c j`, `D` enter the
  generated files; no commutativity hypothesis anywhere.

Modal runs (`./mrun.sh --file ...`): 7 iterations to green (details: missing
`hn` for the `Nonempty (Fin n)` instance; `M2 ^ j l i` precedence bug;
`map_div` is the *group* lemma — ring version is `map_div₀`;
`Finset.sum_smul`/`smul_sum` swapped in this Mathlib; `sum_eq_single`
has signature (a) (h₀) (h₁ : a ∉ s → f a = _), conclusion `∑ = f a`;
higher-order `rw` with cast-of-sum inside matrices fails ("function
expected") — fixed by fully-typed term applications (`Int.cast_sum _ _`,
`Finset.mul_sum _ _ _`, `Finset.sum_smul`); `rw [← b.sum_repr x]` loops on
`x` — use a calc; `if_pos/if_neg` deprecated → `ite_eq_left/ite_eq_right`).

- **HeckeRational.lean green: 0 err / 0 warn, wall 37 s, peak tree RSS
  5.95 GiB.**
- **Weight-24 test drive (scratch, deleted): 0 err / 0 warn, wall 79 s,
  peak 6.00 GiB.** The scratch exercised the full per-weight recipe:
  Xtab2 + hX2 (via `heckeT2_coeff` + the T₃ file's q-lemmas), LvT2 staged
  lemmas, entryT2 lemmas, `M2` literal (= `MaedaWeight24.toMatrix_heckeT2`
  literal, confirming the re-derivation), hM2/hM3 Fin-∀ bridges
  (`fin_cases` + `exact`, defeq on literals), `cert : ℕ → ℤ`,
  `scaled_id` by `decide +kernel` (D = 1 at weight 24: Q = 195660 − 48·X ∈
  ℤ[X]!), and the one-line master application. First try green.

Next: G3 generator + dims 6–10 (reuse T₂ dim files via the audited defeq
bridge; small weights get the scratch's recipe).

### 2026-11-02 — G3 + G4 + G5 PASSED: all 54 weights landed, audited, registered

Inbox polled at each checkpoint: empty throughout.

**G3** — `tools/gen_hecke_rat.py` (self-contained: re-parses all Lean
literals, re-derives M₂ for small weights, re-asserts alignment /
t-lemmas / charpoly / commutation / exact ℚ-solve, emits, `--check`
byte-identity).  CORRECTION to G1's evidence: `def_bodies` in the audit
missed match-style defs (`fb`, `Atab` have no `:=`), so the G1 fb/Atab
alignment check had been VACUOUS (the f-defs check was real).  Fixed in
the generator (whole-block capture); the fb/Atab bodies are indeed
syntactically identical for all 30 big weights — the defeq bridge stands
(now checked for real, every regeneration).

Emission wrinkles (all fixed, --check green, 0 lines > 98 chars):
chunked literals past 341 digits don't fit any line in the flat
gen_maedan scheme (certificates reach 381 digits; D 349), so those are
emitted in Horner form base `10 ^ 74` (all explicit powers ≤ 256, all
numerals ≤ 80 digits — norm_num in `hD` and the kernel both handle it).

- `HeckeRationalWeights.lean` (30 weights, dims 6–10): green FIRST build
  with matrix-level decides — 130 s / 8.27 GiB (commit 761e870).
- `HeckeRationalSmallWeights.lean` (24 weights): 84 unused-simp-arg
  warnings (`List.getD_cons_succ` unused at j=2) — generator now includes
  it only for j ≥ 3; green 40 s / 6.81 GiB.

**G5 audit red flag and fix** — `AxCheckDecide` flagged exactly the 54
`scaled_id` decides: `[propext, Classical.choice, Quot.sound]`.  Root
cause: `Matrix.decidableEq` = `Fintype.decidablePiFintype` is built via
`decidable_of_iff` with a simp-proved Iff — the axiom baggage lives in the
instance itself.  Fix: state the scaled identities ENTRYWISE
(`ext a b; fin_cases a <;> fin_cases b <;> decide +kernel` — Int equality,
clean instance).  Aftermath: `HeckeRationalWeights` 234 s / 8.40 GiB,
`HeckeRationalSmallWeights` 67 s / 6.95 GiB (both 0/0);
**AxCheckDecide: 1 202 decide certificates, 0 > propext** (was 1 256
audited / 54 violations).

**Registration** — lakefile `defaultTargets` + CI list + root:
`HeckeRational`, `HeckeRationalWeights` (CI add ≈ 37 s + 234 s ≈ 4.5 min,
inside the ~10 min budget); `HeckeRationalSmallWeights` ROOT-ONLY with a
note, following its parent `MaedaT3SmallWeights` (a trio registration
would drag that non-CI module — "a few min" per lakefile note — into CI;
this mirrors the established treatment; flagged to the operator in the
final report).  Root target `MathProof` green (46 s / 6.64 GiB); full
`defaultTargets` build green (35 s warm).

**Audits** — tauceti_audit.sh: 0 set_option / #eval / native_decide /
sorry / bad-imports on all three new files.  No memory alerts (peaks
≤ 8.4 GiB).  No ancestor of the heavy MaedaGalois5 chain touched (the new
modules import CharpolyDimN + the dim files + MaedaT3SmallWeights only).

**Bookkeeping** — README (results section), AGENTS.md (layout + the
matrix-decide Classical gotcha), research-log.md (iteration-22 entry),
this WORKLOG.
