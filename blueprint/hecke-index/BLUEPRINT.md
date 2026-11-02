# BLUEPRINT 2 — hecke-index: the Hecke ring 𝕋 and the index [𝕋 : ℤ[T₂]]

Iteration 23, b2 (the wave's centerpiece).  Authored by the orchestrator
2026-11-02 from `research/iteration23/probe2-hecke-index/FINDINGS.md` and
`docs/articles/hecke-denominators.html` (read both first — the FINDINGS carry
the validated certificates, the conventions and the refuted candidates).
Provenance: T2 submission 2026-11-02; trunk `dev/iteration23-hecke-ring`.
Upstream: b1 (`hecke-tm`) — import its module from this branch as soon as b1's
branch lands its G3 (see §4 sequencing).

## 0. Objective / non-objectives

**Objective.**  For every level-one weight `24 ≤ k ≤ 134` with
`2 ≤ dim S_k ≤ 10` (54 weights), the formalization of the Hecke-index
observation (iteration-22 research log; the article's "WHAT IS NOT IN LEAN"
half), in two layers:

**(i) Generic module** `MathProof/ModularForms/HeckeIndex.lean` (light,
weight-generic; `n = dim S_k`, Miller-type basis `f_1..f_n` as hypotheses or
per-weight data):

* `hecke_dual`: `∀ m ≥ 1, heckeTM m = ∑_{j≤n} a_m(f_j) • T_j` — the duality
  (strong induction on `m` via the two-term prime recursion; base `m ≤ n`
  trivial by the Miller normalization `a_m(f_j) = δ_mj`; probe-1 check D /
  probe-2 anchor the mechanism);
* `hecke_independent`: `T_1, …, T_n` ℂ-linearly independent — one line from
  the dual basis `φ_i(T) := a₁(T f_i)`, `φ_i(T_j) = a_j(f_i) = δ_ij`
  (b1's `heckeTM_one`); NO Petersson symmetry (refuted, probe-2 F6);
* `heckeRing` subring: `𝕋 := Submodule.span ℤ {T_j}` is a subRING of
  `Module.End ℂ (S_k)` (closure: `heckeTM_mul`), contains `ℤ[T₂]`, and
  `span ℂ {T_j} = 𝕋 ⊗ ℂ`;
* the Cramer inverse: with `C := (φ_j(T₂^i))_{i,j}` (per-weight integer
  matrix), `I_k := |det C| ≠ 0` implies `∀ j, I_k • T_j = ∑_i adj(C)_{ji} • T₂^i`
  (integer coefficients — `Matrix.adjugateMul`);
* `index_eq_det` (STAGED, see gates): `[𝕋 : ℤ[T₂]] = I_k` where `A :=
  (a_{2^i}(f_j))` and `|det A| = |det C|` by the unitriangular bridge
  (`T₂^i` vs honest `T_{2^i}`, b1's recurrence; probe-1 check E / probe-2 F3);
* `den_dvd_index`: if `aeval T₂ Q = T` with `Q ∈ ℚ[X]` of reduced denominator
  `D`, and `D' • Q ∈ ℤ[X]` represents `D' • T`, then `D ∣ D'` (uniqueness of
  representing polynomials of degree `< n` from minpoly = charpoly — the
  landed per-weight `maeda` theorems).

**(ii) Per-weight certificates** (generated light file
`MathProof/ModularForms/HeckeIndexWeights.lean`, 54 weights): per weight, on
the LANDED literals (fb-basis coordinate matrices `M₂`, `M₃` of the dim
files — probe-2 F2 pinned the convention):

* `det_A : A.det = I_k` by Mathlib's `eval_det` (Bareiss; entries ≤ 180
  digits, dets ≤ 462 digits at dim 10 — measured territory via
  `CharpolyEngine`), `I_k ≠ 0`;
* the entrywise kernel certificate `∑_i w'_i • M₂^i = I_k • M₃` (the
  HeckeRational pattern verbatim — `ext`/`fin_cases` + `decide +kernel`,
  NEVER matrix-level decide; w′ ≤ 494 digits at dim 10 → Horner base-10^74
  chunks like `gen_hecke_rat.py`);
* the composite: `D ∣ I_k` per weight (committed `(N, D)` witness +
  `den_dvd_index` + the new certificate);
* dim-3 bonus where cheap: the closed form
  `T₃ = (T₂² − 2^(k-1) − a₄(f₁) − a₄(f₂)T₂)/a₄(f₃)` as the certificate's
  rearrangement (six weights).

**Non-objectives.**  Hecke fields (b3); eigenform theory; `𝕋` at level `N`;
Smith normal form; dims ≥ 11; Mathlib bump; ancestor edits (`HeckeLevelOne`
is on the heavy-chain ancestor list; `HeckeTM.lean` (b1), `HeckeRational`,
`CharpolyEngine`, `MaedaCertC*` are NOT — import freely).

## 1. Reuse map (two columns)

**Mathlib-at-pin**: `Matrix.adjugate`, `Matrix.adjugateMul` (Cramer),
`Matrix.det` + `Mathlib.Tactic.NormDet` (`eval_det`), `Submodule.span`,
`Submodule.prod_le`, `Submodule.card_eq_card_quotient_mul_card`,
`AddSubgroup.index` (partial packaging for the card route);
`Polynomial.aeval` uniqueness (degree < natDegree of a nonzero annihilator).
NOT present (checked, probe-2 §3): any "lattice index = |det|" bridge, any
Hecke-ring content.

**TauCeti** (study-only): `heckeTCuspAlgebra_finite` (𝕋 finite over ℤ —
validates the shape, gives no basis/index), `LinearMap.finite_adjoin_of_
injective_pairing` (the abstract duality).  The index/denominator statement
is new formalization (not in Mathlib, not in TauCeti).

**Own library**: b1's `HeckeTM` calculus (definition + `heckeTM_mul` +
`heckeTM_one`); `HeckeRational.exists_aeval_rat_of_rep` + `aeval_pow_rep`
(operator-power ↔ matrix-power — the certificate glue), its generator
`gen_hecke_rat.py` (chunked-literal emitter, `--check` discipline,
Lean-literal parsing — extend, don't fork); `CharpolyEngine` (det option);
the per-weight `M`/`Xtab`/`Atab`/q-lemma literals + `coordsAux`/`coordN`
machinery in `MaedaDim{6..10}Weights`, `MaedaT3Dim{6..10}Weights`,
`MaedaT3SmallWeights` (the fb-coordinate convention probe-2 F2 pinned);
`HeckeCommute.qExpansion_coeff_ext`; `research/iteration22/hecke-rational/
g1_data.json` + `index_check.py` (I_k ground truth); probe-2's
`probe_index.py` (regenerable certificate data + the exact w′ recipe).

## 2. Module layout

* `MathProof/ModularForms/HeckeIndex.lean` — generic layer (~400–700 lines):
  duality, independence, ring, Cramer inverse, reducedness; per-weight data
  consumed via a hypothesis bundle (shape: the `charpoly_dimN`/
  `exists_aeval_rat_dimN` style — explicit `fb`/coefficient-function
  hypotheses, no file-specific hacks).
* `tools/gen_hecke_index.py` — NEW generator (extend `gen_hecke_rat.py`'s
  infrastructure: copy its parsing/chunking utilities, keep byte-identity
  discipline for UNCHANGED existing outputs — b2 adds files, never rewrites
  landed ones): per weight emits `A`, the det lemma, `w'` (Horner-chunked),
  the entrywise identity, the divisibility composite.
* `MathProof/ModularForms/HeckeIndexWeights.lean` — generated, 54 weights
  (root-ONLY registration by default — the CI-bill discipline; trio
  promotion only if measured < ~5 min and the operator's selective-targets
  concern is addressed).

## 3. Verification plan

* Standalone-mirror Modal runs per gate (worktrees cannot use
  `tools/modal_run.sh` directly); 0 err / 0 warn; tauceti audit; no
  `set_option`; entrywise decides only (matrix-level decide pulls
  `Classical.choice` — AGENTS.md trap).
* G1 data audit BEFORE code: regenerate ALL 54 (A, C, I_k, w′) from probe-2's
  script and re-pin the M₂/M₃ literals per weight (parse the Lean dim files
  — the g1-anchor pattern; do NOT trust g1_data.json un-verified: it is
  committed data, i.e. probe-tier in the evidence hierarchy).
* Combined `AxCheckDecide` at close (expect +54-ish entrywise certificates,
  0 > propext); `#print axioms` nothing heavy (all light).
* Registration: `HeckeIndex` trio; `HeckeIndexWeights` root-only (+ flag).

## 4. Stage gates (each ≈ one green-commit session; descope provisions inline)

* **G1 — data audit + conventions**: re-derive (A, C, I_k, w′) at all 54
  weights; pin the fb-literal conventions against the actual Lean files
  (probe-2 F2: coordinate matrices, columns = images); DECIDE the Miller-basis
  strategy: (a) build the Miller basis in Lean as the unit-triangular
  reduction of `fb` (integer transition, `|det| = 1`) and state the generic
  layer with it, or (b) state everything in fb coordinates and carry the
  transition `Tmat` as per-weight data.  Recommended: (a) — the duality and
  `A` are cleanest in Miller form; the certificates stay in fb form
  (basis-independent operator identities).  Commit the audited data +
  decision to WORKLOG.  *Descope*: dims 2–5 can follow the same fb sources
  via `MaedaT3SmallWeights` (its T₂ side may need re-derivation as in
  HeckeRationalSmallWeights — reuse that recipe verbatim).
* **G2 — generic layer**: duality + independence + ring + Cramer inverse
  green on Modal (rides b1's module: MERGE `impl/iteration23/hecke-tm` into
  this branch once its G3 is landed — record the merge in the WORKLOG as a
  documented upstream dependency; if b1 is mid-flight, prove G2's statements
  against b1's blueprint-stated names and defer the merge).  *Descope*: the
  subRING packaging can shrink to "closed under ∘" as two lemmas if
  `Submodule.prod_le` fights; `index_eq_det` (the card route) may descope
  to `I_k ≠ 0 ∧ |det A| = |det C|` + the two spanning families — the
  mathematical content — with the `Nat.card` packaging as a CORRECTIONS-
  noted follow-up (the bridge lemma is ~100–150 lines of ℤ-module
  cardinality work; do not let it eat the session).
* **G3 — det + reducedness**: `eval_det` certificates at all 54 (a det
  lemma per weight; measure dim-10 cost first with ONE weight);
  `den_dvd_index`.  *Descope*: if `eval_det` at dim 10 exceeds ~10 min or
  hearts out, fall back to `CharpolyEngine` interpolation (det = ± constant
  coefficient of the charpoly — an extra `eval` per weight but reuses the
  measured engine); if BOTH fight, certify `I_k` via the probe-2 identity
  `w'·C = |det C|·v` + an entrywise product decide (det-avoiding route —
  G1 should pre-check its cost).
* **G4 — certificates + registration**: generator + 54-weight file green;
  root-only registration; combined audits; WORKLOG + research-log draft.
  *Descope*: 30 weights (dims 6–10) first; dims 2–5 as a follow-up commit
  if the session runs long (their I_k are tiny — trivially cheap, likely
  no descope needed).

**Sequencing**: G2 needs b1's G3 output (the `heckeTM` calculus).  If b1
lands on schedule (its own G1–G2 are independent), merge and proceed; if b1
stalls, G2's first half (independence, ring, Cramer) only needs the LANDED
prime theory (`heckeTP`/`heckeTP_commute`) + `heckeTM` for `m = 2^i`
(b1's G2 output) — descope the duality's general-m statement to the
`m = 2^i, 3` instances and proceed (CORRECTIONS note; b2's certificates do
not depend on general-m duality).

## 5. Risks / fallbacks

* **Miller-basis construction in Lean** (main design risk): the
  unit-triangular reduction of `fb` over ℂ with integer coefficients —
  state the reduction as an explicit recursive definition + prove
  `a_i(f_j^M) = δ_ij` by the triangular structure.  If the analytic
  coefficient bookkeeping fights, the fb-coordinate route (G1 option (b))
  carries everything with the `Tmat` literals as data.
* **Integrality of coefficients**: `a_m(f_j) ∈ ℤ` for the ℤ-span statements
  — the prodForm integrality (E₄/E₆/Δ have integral q-expansions; Mathlib's
  coefficient lemmas give explicit σ-sums).  If a clean "integral
  q-expansion" lemma does not exist at the pin, carry `a_m(f_j) ∈ ℤ` as a
  hypothesis bundle instantiated per weight by finite certificates up to the
  needed m-range (the duality only ever reads `a_m(f_j)` for the theorem's
  fixed `m`; the ℤ-module statements need it for the fixed finite table).
* **Certificate size**: w′ ≤ 494 digits — Horner chunks handle it
  (HeckeRational measured 381 + Horner; verify with the first dim-10
  emission before generating all 54).
* **`eval_det` cost at 10×10 with 180-digit entries**: measure one weight at
  G3 before committing to the route (fallbacks in the gate).
* Proof standard: entrywise decides; AxCheckDecide combined run at close.

## 6. Lessons learnt (brought in)

From probe 2: the certificates go on the LANDED fb literals (no bridge
inside the certificate — operator identities are basis-independent); the
reduced-denominator convention is `D // gcd(D, all N_j)`; det-sign — w′ is
`|det|·w` (the helper that returns `det·w` flips sign at odd permutations of
the basis order).  From iteration 22: entrywise decides, never matrix-level
(`Fintype.decidablePiFintype` pulls Classical); generated files regenerated
(`--check`), never edited.
