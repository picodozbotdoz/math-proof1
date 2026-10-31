# Worklog — impl/iteration21/maeda-t3

Append dated entries as you go (stage gates passed/failed, Modal runs with
build time + peak RSS, decisions, deviations from the blueprint).  This file
is the inter-session resume point: make it possible to continue cold.

## Entries

### 2026-10-31 — G1 audit: the blueprint's k=24 anchor is FALSE; corrected anchor set

Before writing any code I checked the blueprint's "CRITICAL ANCHOR": it claims
`charpoly(T₃ | S₂₄) = X² − 252·X + 3²³` "since S₂₄ is spanned by Δ".  That is
mathematically wrong: Δ ∈ S₁₂, S₂₄ ⊄ span(Δ); τ(3) = 252 is an eigenvalue of
T₃ on **S₁₂**, not S₂₄.  Numerically (probe engine, itself anchored by the
Lean-proved T₂ charpolys at k=24/48):

* `charpoly(T₃ | S₂₄) = X² − 339480·X − 19020146544` — confirmed by TWO
  independent routes: (i) echelon basis + integer back-substitution (the
  pipeline route), (ii) non-echelon basis (ΔE₄³, ΔE₆²) + Cramer solve +
  trace/det, with the T₃-image linearity verified on coefficients q³..q⁵.
* The TRUE τ(3)-anchor: `charpoly(T₃ | S₁₂) = X − 252` with 252 =
  `Ramanujan.tau 3` (kernel-verified in Tau/Basic.lean).  Pipeline gives
  matrix [[252]], charpoly [1, −252].  ✓
* Dim-1 scalars at k = 16, 18, 20, 22 (T₃ = a₃·id on S_k, hand-derived from
  τ × Eisenstein convolutions): a₃ = −3348, −4284, 50652, −128844.  All ✓.
  (k = 14 is the dim-0 exception — no cusp forms of weight 14.)
* Commutation `[M₂, M₃] = 0` holds for all 30 census weights, against the T₂
  matrices of `research/iteration20/data/maeda_dim6_10.json` — whose charpolys
  are Lean-proved in `MaedaDim{6..10}Weights.lean`.  This ties the whole T₃
  census to kernel-verified data.  ✓

R1 audit (T₂-specialization): `heckeTP_qExpansion_coeff` in HeckeLevelOne.lean
is p-generic for any prime (QFormula *section*, so `open HeckeLevelOne`
resolves it).  Only the wrapper `heckeT2_coeff` (MaedaLevelOne.lean) is
T₂-specific.  Since MaedaLevelOne is an ancestor of the heavy MaedaGalois5
chain, the p-generic twin `heckeTP_coeff` goes in a NEW light module
`MathProof/ModularForms/HeckeTPCoeff.lean` (no heavy-chain contact).

N-cap discovery: T₃ needs basis coefficients up to index 3n (30 for dim 10),
i.e. `N = 3n+1 = 31`, but `MaedaCertC.seqPLc_eq` caps `N ≤ 22` (tauTable has
τ(0..21)).  Dims 8–10 exceed the cap.  Fix (new light module
`MaedaCertCExt.lean`): extend the table to τ(30) and mirror `seqPLc/seqPLc_eq`
with cap `N ≤ 31`.  τ(22..30) cross-checked in Python via the Lean-proved
Mordell relations (tau_mul_coprime / tau_prime_pow_succ) — all 7 derivable
values agree with the Euler-product engine (τ(23), τ(29) are prime-indexed,
certified by the Lean `decide` at build time).

Numerics measured (Python): dim-10/weight-134 f-coefficients ≤ 76 digits,
T₃-image coefficients ≤ 74, matrix entries ≤ 82, charpoly coefficients ≤ 317
digits; `3^(k−1)` ≤ 64 digits.  All within the generator's existing chunking
infrastructure; statement lines stay ≤ 91 chars (limit 100).

### 2026-10-31 — G1 done, G1.5 done, G2 in flight

* `research/iteration21/maeda_t3_probe.py` → `research/iteration20/data/
  maeda_t3_dim6_10.json` (3.3 s; 30 weights, all anchors + reflected-engine
  sanity asserts + commutation with the T₂ matrices) and, for the stretch,
  `maeda_t3_small.json` (dims 2–5, 24 weights, k ≤ 74).  Census: cp coeffs ≤
  317 digits (dim 10), Rabin ℓ ≤ 349 (k=88), zmuls ≤ 27 950 (k=120) — cost
  model identical to T₂ (depends only on ℓ and n).
* `MathProof/ModularForms/HeckeTPCoeff.lean` (new, light, 37 lines):
  `heckeTP_coeff` — the p-generic twin of `heckeT2_coeff`, one `rw` from
  `heckeTP_qExpansion_coeff`.  Compiles clean locally.
* `MathProof/ModularForms/MaedaCertCExt.lean` (new, light, 121 lines):
  `tau22 … tau30` (each `rw [tauOf_eq_getD]; decide`, ~8 s for the whole
  module), `tauTableX`, `dCc3`, `seqPLc3`, `seqPLc3_eq` (cap N ≤ 31).
  Compiles clean locally.
* `tools/gen_maedan.py --prime 3`: separate `emit_weight_t3` (the T₂ emitter
  untouched — byte-identity `--check` verified for all five T₂ files AFTER
  the change).  T₃ mode: N = 3n+1, seqPLc3 lists, q-lemmas to 3n,
  `T3 := heckeTPₗ k Nat.prime_three` + `heckeTP_coeff`, namespaces
  `MaedaT3Weight{k}`, files `MaedaT3Dim{6..10}Weights.lean`
  (11 980 / 16 128 / 21 130 / 26 916 / 33 643 lines vs T₂'s 8 174…~22 k).
* Local `lake env lean MaedaT3Dim6Weights.lean`: 0 errors, 0 warnings,
  2m46s wall.  `--prime 3 --only 6 --check` byte-identical.
* Modal plumbing gotcha (worktree): `tools/modal_run.sh`'s rsync mirror
  carries the worktree's `.git` *file* (gitdir pointer into /home/doz,
  unreadable for xyz) → `git status` in the mirror fails.  Driving the same
  plumbing manually (/tmp/maetat3_modal.sh): mirror minus .git as a
  standalone repo whose `origin/master` ref is an EMPTY-TREE commit, so
  `git status` is clean while `git diff --name-only origin/master` lists
  every file — lean_check then overlays the complete current state onto its
  fresh clone (GitHub master is still at 4eaf528 = iteration 19; iteration
  20 lives on the dev branch).

### 2026-10-31 — G2 PASSED (k=72 end-to-end on Modal)

`MaedaT3Dim6Weights` (all six dim-6 weights incl. k=72: `MaedaT3Weight72.maeda`)
**green on Modal, zero errors/warnings**: lake wall 165 s, peak tree RSS
10.57 GiB, per-module peaks — MaedaT3Dim6Weights 6.50 GiB, MaedaCertCExt
4.84 GiB, HeckeTPCoeff 4.66 GiB.  (T₂ dim 6 was 130 s / 6.6 GiB → ×1.27.)
Extrapolated dim 10 ≈ 25 min — watch it; if >20 min, blueprint says re-search
ℓ (already minimal: ascending search) then split per-weight.

Stretch generator mode added meanwhile: `--prime 3 --small` emits
`MaedaT3SmallWeights.lean` (24 weights, dims 2–5, k ≤ 74; 20 276 lines) from
`research/iteration20/data/maeda_t3_small.json`; `charpoly_dimN` is
dimension-generic so no engine change was needed (blueprint R4 resolved the
preferred way).  Byte-identical `--check` for the small mode; T₂ `--check`
still byte-identical after every generator edit.

### 2026-10-31 — G3 progress (Modal, one file at a time; tauceti clean)

| file | wall | peak tree RSS | module peak | errors/warnings |
|---|---|---|---|---|
| MaedaT3Dim6Weights | 165 s | 10.57 GiB | 6.50 GiB | 0 / 0 |
| MaedaT3Dim7Weights | 209 s | 8.49 GiB | 7.25 GiB | 0 / 0 |
| MaedaT3Dim8Weights | 527 s | 9.53 GiB | — | 0 / 0 |

`tools/tauceti_audit.sh`: all new modules (HeckeTPCoeff, MaedaCertCExt, the
five per-dim T₃ files, MaedaT3SmallWeights) clean — 0 set_option / #eval /
native_decide / sorry / bad imports.  Stretch file
`MaedaT3SmallWeights.lean` compiles locally 0 err / 0 warn.
