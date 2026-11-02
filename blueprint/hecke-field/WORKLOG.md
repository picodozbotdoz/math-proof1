# Worklog — impl/iteration23/hecke-field

Base: de3e387 (trunk `dev/iteration23-hecke-ring`, blueprints commit).
Blueprint: `blueprint/hecke-field/BLUEPRINT.md` — a STARTING POINT, not a
contract: G1-audit it, deviate per the §4d deviation protocol when facts
disagree (evidence here; corrections to the trunk).

Append dated entries as you go (gates passed/failed, mrun.sh Modal runs with
time + peak RSS, decisions, deviations).  This file is the inter-session
resume point: make it possible to continue cold.

## Entries

### 2026-11-02 (session 1) — G1 CLOSED (audits + T-Gal landed green) + HeckeField generic layer

**G1 audits** (all pass, no blueprint deviations needed):

* *Charpoly re-derivation*: re-ran `probe_field.py` from the repo root
  (`research/iteration23/probe3-hecke-field/`, needs cwd = repo root for its
  `research/iteration22/hecke-rational/g1_data.json` input).  All six T₂
  charpolys match the landed literals bit for bit:
  k=24 `X²−1080X−20468736` (= `MaedaWeight24.P24`), k=28 `X²+8280X−195250176`,
  k=30 `X²−8640X−454569984`, k=32 `X²−39960X−2235350016`,
  k=34 `X²+121680X−8513040384`, k=38 `X²+194400X−137403408384`
  (= `MaedaSmallWeights.MaedaWeight{28,30,32,34,38}.P`).
* *Input-location nuance* (audit note, not a correction): the six dim-2
  inputs live in TWO files — weight 24 in `MaedaWeight24.lean` with its own
  naming (`P24`, `charpoly_heckeT2`, `maeda_weight24`, `P24_monic`), weights
  28–38 in `MaedaSmallWeights.lean` (`P`, `charpoly_T2`, `maeda`).  The new
  T-Gal file reopens the six `MaedaWeightKK` namespaces directly, so the
  instances are literally `MaedaWeightKK.maeda_galois_full`.
* *Registration status*: `MaedaWeight24`, `MaedaSmallWeights`,
  `MaedaGaloisQuad` are ALL defaultTargets + root + CI items → the T-Gal
  file is a trio item (only its own ~11 s elaboration added), not root-only.
* *Eigenvector API pinned* (for G3): `Module.End.aeval_apply_of_hasEigenvector`
  and `Module.End.aeval_apply_of_mem_apply_eq_smul` at
  `Mathlib/LinearAlgebra/Eigenspace/Minpoly.lean:51,62`;
  `Module.End.mem_eigenspace_iff` in `Eigenspace/Basic.lean:467`.
  Adjoin membership via `IntermediateField.mem_adjoin_simple_iff`
  (`Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`):
  `x ∈ adjoin F {α} ↔ ∃ r s : F[X], x = aeval α r / aeval α s`.
  Eval/aeval bridge: `Polynomial.eval_map` + `Polynomial.aeval_def`
  (hypothesis-free; `aeval_eq_aeval_map` carries a RingHom hypothesis —
  don't use).  GOTCHA: pure-algebra imports do NOT register ℂ's instances —
  import `Mathlib.Analysis.Complex.Polynomial.Basic` (or similar) first.

**T-Gal landed** (commit 1f0bd2c): new file
`MathProof/ModularForms/MaedaT2GaloisSmallWeights.lean` — six
`maeda_galois_full : Function.Bijective (Gal.galActionHom (P.map
(Int.castRingHom ℚ)) ℂ)` instances via
`MaedaGaloisQuad.bijective_of_quadratic` + per-namespace one-line
`P_monic`/`P_natDegree` (`monic!`/`compute_degree!` after `unfold`).
Needs `attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ`
(`galActionHom` carries `[Fact (... Splits)]`).  ZERO new kernel decides.
tauceti_audit clean (123 lines, 0 everything).
Modal `mrun.sh --file ...`: first-run green, module 11 s / 4.66 GiB,
tree peak 5.91 GiB.  After trio registration (lakefile defaultTargets,
root `MathProof.lean`, CI build-args) `mrun.sh --target MathProof`:
root green, 61 s / 5.44 GiB.  Closes iteration22-review §6.3 (T₂ Gal = Sₙ
now includes dim 2 at all 54 verified weights).

**HeckeField generic layer landed** (G3 prep, de-risks blueprint §5
"Eigenvector API friction"; needs neither b1 nor b2): new file
`MathProof/ModularForms/HeckeField.lean` (77 lines), namespace `HeckeField`,
module-generic over `[AddCommGroup V] [Module ℂ V]`:
`eval_map_eq_aeval` (ℚ/ℂ eval bridge), `eval_map_mem_adjoin`
(Q(μ) ∈ adjoin ℚ {μ}), `apply_eq_eval_smul` (aeval T₂ (Q.map ℚ→ℂ) v =
Q(μ) • v on eigenvectors), `eigenvalue_mem_adjoin` (operator-level: if
`T = aeval T₂ (Q.map ℚ→ℂ)` then every nonzero T₂-eigenvector is a
T-eigenvector with eigenvalue in `adjoin ℚ {μ}`).  One failed Modal run on
the way (missing ℂ instances from too-generic imports + `λ` is not a legal
binder name); fixed, green: 28 s / 3.86 GiB module, tree 5.09 GiB.
Trio-registered.  The per-weight G3 instances now need only the T-Rat
rationality input (b2) — the Mathlib algebra is DONE.

**Upstream status**: b1 (`hecke-tm`) and b2 (`hecke-index`) WORKLOGs both
EMPTY at session close (~20:00) — nothing landed, nothing to merge.  So
T-Rat waits on b2's G2/G3, and the dim-2 integrality track (needs b1's
`heckeTM`) did not start: defining `heckeTM` here would duplicate b1's
assignment.

**Inbox polls** (session start + gate close): empty both times.

**Modal runs this session**: 4 (T-Gal file, root, HeckeField fail, HeckeField
green) + this counts against the ≤20 budget.

**Next session resume point**:
1. If b2 landed its generic layer: merge `impl/iteration23/hecke-index`
   (WORKLOG the merge), then G2 = `∀ m ≥ 1, ∃ Q : ℚ[X], heckeTM m = aeval T₂
   (Q.map (algebraMap ℚ ℂ))` per weight — the witness assembly pattern is
   `HeckeRational.exists_aeval_rat_of_rep`; the G3 eigen-containment
   instances then consume `HeckeField.eigenvalue_mem_adjoin` + the G2
   theorem (nothing else needed — the algebra layer is landed).
2. If b1 landed `heckeTM`: the dim-2 integrality per weight
   `∀ m ≥ 1, heckeTM m = (a_m(f₁) : ℂ) • 1 + (a_m(f₂) : ℂ) • T₂`
   (probe-3 G1 anchors m ≤ 60; at dim 2 the a_m(f_j) are read off the Miller
   basis via `heckeTM`'s q-coefficient formula — needs a per-weight
   coeff lemma `a_m(f_j) = ...` that is integer-valued; audit which shape
   b1 exports first).
3. G4: AxCheckDecide run over the enlarged root + research-log draft.

**Bonus landed same session (T-Field m = 3 slice)** (commits follow): the
realization that the m-generic eigen-containment is NOT needed for a first
T-Field deliverable — the m = 3 rationality input is already landed at all
54 weights (`heckeT3_eq_aeval_rat_weightKK`).  New generated file
`MathProof/ModularForms/HeckeFieldWeights.lean` +
`tools/gen_hecke_field.py` (`--check` byte-identity; asserts its weight
tables against the landed `HeckeRatWeightKK` sections and the canonical-T2
defeq bridge): 54 instances
`HeckeFieldWeightKK.eigen_T3_mem_adjoin_weightKK : {v}
(hv : v ≠ 0) (hμ : heckeTPₗ k 2 v = μ • v) → ∃ w ∈ adjoin ℚ {μ},
heckeTPₗ k 3 v = w • v`.  ZERO decides, no literal tables (only weight
numbers).  Root-only registration (parent HeckeRationalSmallWeights is
deliberately non-CI — same policy note in the root import).  Two failed
Modal runs on the way (`𝒮ℒ` is `scoped[MatrixGroups]` — needs
`open scoped MatrixGroups`; the generator's section regex needed
`\(dim (\d+)\)` for dim 10).  Modal: file 116 s / 5.29 GiB; enlarged root
rebuild 97 s / 5.46 GiB.  tauceti_audit clean (729 lines).
Modal runs so far: 7.

With this, the T-Field track's *statement* exists at all 54 weights for
m = 3; upgrading to generic m is a one-line swap per weight once b2's
rationality lands (consume the m-generic ∃ Q instead of the m = 3 one).

### 2026-11-03 (session 2) — b1 merged; G3 dim-2 integrality in flight

**Session start / inbox poll**: inbox empty (only `done/` + README).

**Upstream dependency merged** (commit f501431):
`git merge impl/iteration23/hecke-tm` (082a98a, b1 G4-complete) into
`impl/iteration23/hecke-field`.  Conflict: `mrun.sh` only (per-worktree
paths — kept ours).  b1's exports audited on the merged tip
(`MathProof/ModularForms/HeckeTM.lean`): `heckeTM k m` (recursive route),
`heckeTM_zero/id/ge_two/ge_two'` (recursion), `heckeTM_qExpansion_coeff`
(`(T_m f)_n = ∑_{d ∣ gcd m n} d^(k-1) f_{mn/d²}`), `heckeTM_one`
(`a₁(T_m f) = a_m(f)`), `heckeTM_prime` (`T_p = heckeTPₗ k p`),
`heckeTM_commute`/`comp_commute`, `heckeTM_mul*`.  Trio-registered upstream;
AxCheckDecide 1312 certs / 0 > propext (b1's report).  This unblocks the
dim-2 INTEGRALITY track (blueprint G3 pull-forward) — no b2 needed.

**G3 route pinned** (audit of landed inputs, all on merged tip):
* Span: `HeckeGeneratedByT2.heckeTP_mem_spanT2` (weight-generic, hchar/hirr)
  → landed per weight in `HeckeGeneratedByT2Weights` (54 instances; weight 24
  via the hand-rolled `MaedaWeight24.heckeT2` — POINTWISE `heckeTP 2` by
  `rfl`, so a one-line bridge to `heckeTPₗ 24 2` suffices);
  `Module.End`'s Mul IS `LinearMap.comp` definitionally (Mathlib
  `Algebra/Module/LinearMap/End.lean:49`), so `ℂ[T₂]` is closed under ∘ₗ by
  `map_mul` + rfl.
* Generic-m: strong induction on `HeckeTM.heckeTM_ge_two` (b1's recursion);
  n/n.minFac and n/minFac² < n both via `Nat.div_lt_self` — the SAME bounds
  the def's `decreasing_by` uses.
* Degree < 2: Cayley–Hamilton `LinearMap.aeval_self_charpoly` +
  `Polynomial.modByMonic_add_div`/`natDegree_modByMonic_lt` +
  `LinearMap.charpoly_natDegree` (= finrank; `Module.Free ℂ V` is automatic
  via `Module.Free.of_divisionRing`).
* Identification α = a_m(f₁ − a₂(f₁)•f₂), β = a_m(f₂): apply at the echelon
  basis forms and read the FIRST q-coefficient — `heckeTM_one` (b1!) turns
  `a₁(T_m f_j)` into `a_m(f_j)`, so the δ-values (`q1_1/q2_1/q2_2`, landed in
  `MaedaSmallWeights`; `f1_coeff/f2_coeff` conjunctions in `MaedaWeight24`)
  determine everything.  NO eigenforms, NO b2 duality needed.
* Miller g₁ := f₁ − a₂(f₁)•f₂ stays SYMBOLIC (coefficient `a₂(f₁)` never
  needed numerically for the operator theorem).  Integer corollaries ride the
  all-m bridges `c1/c2` (`MaedaLevelOne.prodForm_coeff`, seqP ∈ ℤ) landed in
  `MaedaSmallWeights` for 28/30/32/34/38; a₂(f₁) ∈ {936, 192, 1176, 432,
  672}.
* DEVIATION (minor, recorded): weight-24 gets NO all-m integer corollary —
  `MaedaWeight24` has no seqP bridge, and bridging its basis to
  `prodForm 24 0 3 0` (or `MaedaT3Weight24`, root-only) is disproportionate;
  the six OPERATOR theorems (the session objective) are unaffected.
* Registration: all imports trio/CI (`HeckeTM`, `HeckeGeneratedByT2Weights`,
  `MaedaWeight24`, `MaedaSmallWeights`) → new file `HeckeFieldDim2.lean`
  trio-eligible; NO `MaedaT3SmallWeights` import (stays clear of the
  root-only parent chain).

New module `MathProof/ModularForms/HeckeFieldDim2.lean` written (~460 lines):
generic `coeff_sub_smul(_int)`, `heckeTM_mem_spanT2`,
`exists_smul_pair_of_finrank_two`, `heckeTM_dim2` + per weight
`dim2_weightKK` / `aM1_int_weightKK` / `aM2_int_weightKK` / `int_weightKK`.
Zero decides, no set_option.  First Modal run next.

### 2026-11-03 (session 3, operator resume) — HeckeFieldDim2 GREEN

* Resumed after the OPERATOR HALT on the operator's go ("help them continue
  iteration 23").  Compile-before-planning: the inherited unbuilt
  `HeckeFieldDim2.lean` was Modal-compiled verbatim first.
* Run 1 (verbatim WIP): BUILD FAILED, 12 errors (67 s, 6.31 GiB).  Causes,
  all mechanical: `heckeTPₗ k hp` takes the PRIMALITY PROOF, not `p`
  (hspan binders → `∀ (q) (hq : q.Prime), … heckeTPₗ k hq …`);
  `qL k` takes the cusp form, not its coercion; `PowerSeries.coeff n P`
  (index first) at the pin; `modByMonic_add_div` is `r + p * q = Q`
  (rewrite with `nth_rewrite 1 [← …]` so only the LHS `Q` moves);
  the Cayley–Hamilton remainder must be `generalize`d before `rw [hRm]`
  or the witnesses get rewritten too; `LinearMap.id = 1` and
  `A ∘ₗ B = A * B` close by `rfl` (Module.End mul is comp).
* Run 2: 5 errors (`LinearMap.mul_eq_comp` does not exist at the pin —
  use `rfl`; `rw [← h5]` direction) + unused-`q` warnings.
* Run 3: 0 errors, 3 `linter.flexible` warnings (non-terminal `simp at`)
  → replaced by stated `have … := by simpa … using …`.
* Run 4: **GREEN — 0 err / 0 warn**, 45 s, 6.33 GiB.  tauceti audit clean.
* Next: G4 registration (trio candidate — all imports are trio/CI), then
  G2 T-Rat once b2 (hecke-index) G4 is green.

### 2026-11-03 (session 3, cont.) — G2 T-Rat + G3 T-Field (all m) + G4 CLOSED

* Merged b2 (`impl/iteration23/hecke-index`, e3f1e55 then a32ebd9 for its
  audit fix) — the documented upstream dependency (blueprint G2).
  Conflicts: `mrun.sh` (ours), `MathProof.lean` (union).
* NEW `HeckeFieldRat.lean` (generic, 230 lines; 3 runs → GREEN 0/0, 46 s,
  4.74 GiB): `millerTop_int`/`miller_int` (integer echelon coefficients ⇒
  integer Miller coefficients; the reduction table is read off the family
  via `hA`, so no separate table integrality), `heckeTM_eq_aeval_rat`
  (every `T_m ∈ ℚ[T₂]`, NO per-m certificate) and the echelon wrapper.
  Route (DEVIATION from the blueprint's "Cramer assembly" wording only in
  how `det Z ≠ 0` is obtained): `T₂^i ∈ 𝕋` gives an integer `Z`; the spans
  of `{T₂^i}` and `{T_j}` coincide by dimension (`linearIndependent_pow` +
  `hecke_independent`), so `Z` has a complex left inverse ⇒ `det Z ≠ 0`;
  then `cramer_inverse` + `hecke_dual` + `aeval_div_witness`.
  Pin notes: after `choose`, a `Fin n → Fin n → ℤ` has no `.det` — wrap as
  `Matrix.of`; `dif_pos` deprecated → `dite_eq_left`.
* `gen_hecke_field.py` extended (the blueprint's "one-line swap", done as
  four theorems per weight): `hfi` (from the landed `c_i` seqP bridges),
  `hmin` (charpoly + Maeda names parsed from `HeckeGeneratedByT2Weights`,
  `charpoly_natDegree` = `finrank_eq` — uniform for all 54, no dependency on
  `HeckeIndexWeights`), `heckeTM_rat_weightKK`, `eigen_TM_mem_adjoin_weightKK`.
  The m = 3 slice is kept.  `--check` byte-identical.  Build run 1 GREEN
  0/0, 45 s, 5.50 GiB.
* G4 registration: `HeckeFieldDim2`, `HeckeFieldRat` → trio;
  `HeckeFieldWeights` stays root-only.  tauceti audit clean (3 files);
  combined `AxCheckDecide`: 1360 certs, 0 beyond propext (8497 jobs).
* Blueprint objectives: T-Gal ✓ (G1), T-Rat ✓ all 54, T-Field ✓ all 54
  (every m), dim-2 integrality ✓ (six weights; weight 24 operator form).
  Field-equality packaging: not attempted (blueprint stretch).
