# BLUEPRINT 3 — hecke-field: Hecke fields ℚ(λ₂) and dim-2 integrality

Iteration 23, b3 (the wave's corollary layer).  Authored by the orchestrator
2026-11-02 from `research/iteration23/probe3-hecke-field/FINDINGS.md` (read
it first).  Provenance: T2 submission 2026-11-02; trunk
`dev/iteration23-hecke-ring`.  Upstream: b2 (`hecke-index`) for the
generic-m machinery; the Gal = S₂ track is INDEPENDENT of b2 (landed inputs
only) and is this blueprint's no-wait starter.

## 0. Objective / non-objectives

**Objective.**  Three tracks, in dependency order:

* **T-Gal (independent, start first)**: `Gal = S₂` for the T₂ charpolys at
  the six dim-2 weights — closing iteration22-review §6.3.  A small generated
  (or hand-written) file `MathProof/ModularForms/MaedaT2GaloisSmallWeights.lean`:
  per weight `MaedaWeightKK.maeda_galois_full`-shaped instances consuming
  `MaedaGaloisQuad.bijective_of_quadratic` + the LANDED
  `MaedaSmallWeights.MaedaWeightKK.{P, charpoly_T2, maeda}` (probe-3 G3
  confirmed the inputs; the charpolys re-derived there with non-square
  discriminants).  With T₂ done, Maeda's `Gal = Sₙ` holds at every verified
  weight for BOTH generators (T₂ now including dim 2 — previously the T₂
  Galois files started at dim 3).
* **T-Rat (needs b2)**: the generic-m rationality theorem per weight —
  `∀ m ≥ 1, ∃ Q : ℚ[X], heckeTM k m = aeval T₂ (Q.map (algebraMap ℚ ℂ))`
  at all 54 weights — from b2's duality + Cramer inverse (the witness Q is
  the generic Cramer assembly; NO per-m certificates).  This subsumes
  `heckeT3_eq_aeval_rat` (m = 3) and closes iteration22-review §6.1
  (T_p ∈ ℚ[T₂] for all p at once, rationally).
* **T-Field (needs T-Rat)**: the eigenvalue containment per weight — every
  T₂-eigenvector `v ≠ 0` with eigenvalue `λ₂` is a `T_m`-eigenvector with
  eigenvalue in `IntermediateField.adjoin ℚ ({λ₂} : Set ℂ)`; plus the
  dim-2 INTEGRALITY theorem (probe-3 G1): at each dim-2 weight, the single
  generic-in-m statement
  `∀ m ≥ 1, heckeTM m = (a_m(f₁) : ℂ) • 1 + (a_m(f₂) : ℂ) • T₂`
  (every T_m an INTEGER polynomial in T₂ — the theorem the
  hecke-denominators article flagged as "worth formalizing").

**Non-objectives.**  The full Hecke-field-equality packaging
(`HeckeField = ℚ(λ₂)` as an adjoin-equality over the eigenform's coefficient
field — needs an eigenform structure; the eigenvalue-containment statement
is the faithful core; field-equality is a stretch, see gates); newspace /
level-N theory; Galois for T_p at p > 3; dims ≥ 11; Mathlib bump; ancestor
edits (b3 adds new modules only).

## 1. Reuse map (two columns)

**Mathlib-at-pin**: `Module.End.HasEigenvector`/`HasEigenvalue` +
`Module.End.aeval_apply_of_hasEigenvector`-shaped lemmas (exact names pinned
at G1 — the `Module.End` eigen-API; search
`Mathlib/LinearAlgebra/Eigenspace/`), `IntermediateField.adjoin`,
`Polynomial.aeval_algHom_apply`, `algebraMap` transports; for T-Gal:
`MaedaGaloisQuad` (own).  Mathlib has NO Hecke-eigenform content (fine —
eigenvectors suffice).

**TauCeti** (study-only): `Newform.heckeTDiamondCuspNewAlgebraEquiv` (the
ℂ-split shape — not needed); `qExpansion_coeff_one_heckeTCuspLevelOne`
(b1's).  No ℚ(λ₂) statement anywhere.

**Own library**: b2's `HeckeIndex` generic layer (duality + Cramer +
reducedness), b1's `heckeTM`; `HeckeRational.exists_aeval_rat_dimN` (the
ℚ-witness assembly pattern to generalize); `HeckeGeneratedByT2Weights`
(the ℂ[X] upgrade — T-Rat supersedes its statement; do NOT edit it);
`MaedaGaloisQuad.bijective_of_quadratic`, `MaedaSmallWeights` (T-Gal
inputs); `MaedaGaloisFullAxCheck`-style opt-in audit patterns;
probe-3's `probe_field.py` (anchors: dim-2 identities m ≤ 60, charpoly
table).

## 2. Module layout

* `MathProof/ModularForms/HeckeField.lean` — generic layer (~300–500 lines):
  the eigenvector-application lemma (`aeval T₂ Q v = Q(λ₂) • v` in the
  adjoin), the generic-m ℚ-witness assembly (consuming b2's exports),
  the dim-2 integrality statement (generic in m, per weight instantiated).
* `MathProof/ModularForms/HeckeFieldWeights.lean` — generated (or
  hand-written if tiny): 54 instantiations of T-Rat/T-Field + 6 dim-2
  integrality instances.
* `MathProof/ModularForms/MaedaT2GaloisSmallWeights.lean` — generated, the
  six Gal = S₂ instances (T-Gal; root-only if it must import non-CI
  parents — check: `MaedaSmallWeights` IS in defaultTargets? — G1 verifies;
  the T₃ small-weights Galois file was root-only because its PARENT was;
  here the parent `MaedaSmallWeights` is a default target, so trio may be
  affordable if the file is cheap).
* Optional generator `tools/gen_hecke_field.py` (only if the instantiations
  exceed hand-writing comfort — the pattern is 6 + 54 small blocks; likely
  hand-writable with a checklist, but generated + `--check` is the safer
  discipline if any literal table is involved).

## 3. Verification plan

* Standalone-mirror Modal runs per gate; 0 err / 0 warn; tauceti audit; no
  `set_option`; AxCheckDecide combined at close (b3 should add ZERO new
  decides — all generic; if the Gal instances need `decide +kernel`, keep
  them entrywise-clean).
* G1 audits: pin the eigenvector-apply lemma name at the pin; verify
  `MaedaSmallWeights` registration status (defaultTargets membership —
  AGENTS.md says trio for it); re-derive the six dim-2 charpolys against
  `probe_field.py` output; audit b2's actual export names once merged.
* Registration: `HeckeField` + `HeckeFieldWeights` per measured cost
  (expected cheap; trio if < ~2 min CI); T-Gal file per its parent's policy.

## 4. Stage gates (each ≈ one green-commit session; descope provisions inline)

* **G1 — audits + T-Gal**: pin the API names; land the six Gal = S₂
  instances green (independent track — no b1/b2 dependency); commit.
  *Descope*: if the quad-lemma application fights the `P.map
  (Int.castRingHom ℚ)` irreducibility shape, a tiny adapter lemma in the new
  file is fine (never edit the landed files).
* **G2 — T-Rat (needs b2's generic layer)**: the generic-m theorem at all
  54 weights (merge `impl/iteration23/hecke-index` when its G2+G3 land —
  WORKLOG the merge as the documented upstream dependency).  *Descope*: if
  b2 descopes its general-m duality, T-Rat falls back to prime-m statements
  via per-p Cramer (the a_p(f_j) tables) for `p ≤ 31`-sweeps at three
  weights (24, 36, 48) — a CORRECTIONS-noted partial result; if b2 is fully
  stalled, T-Rat waits (T-Gal + T-Field-dim2 still land — see below).
* **G3 — T-Field + dim-2 integrality**: the eigenvalue containment per
  weight; the six dim-2 integrality theorems (these need only b1 + the
  Miller data — they can be pulled FORWARD into G2's session if b2 stalls,
  since at dim 2 the duality is trivial: `a_m(f_j) = δ`-reduction).
  *Descope*: the field-equality packaging (stretch) drops without
  ceremony; eigen-containment at dims 2–5 can follow dims 6–10 if needed.
* **G4 — registration + audits**: trio/root-only decisions per measured
  cost; combined `AxCheckDecide`; WORKLOG + research-log draft.

## 5. Risks / fallbacks

* **b2 dependency slip** (the main schedule risk): mitigated by T-Gal's
  independence and the dim-2 integrality's shallow dependency (b1 + Miller
  data only); worst case b3 lands T-Gal + dim-2 integrality and T-Rat/
  T-Field carry to a follow-up session with the merge staged.
* **Eigenvector API friction**: the `Module.End` eigen-lemmas are stated
  over the scalar ring ℂ; the ℚ-polynomial map composition
  (`Q.map (algebraMap ℚ ℂ)` applied at λ₂ landing in `adjoin ℚ {λ₂}`)
  needs `Polynomial.aeval` over `ℂ` + `adjoin` membership — a bounded but
  real algebra layer (~50–100 lines); if `aeval_apply_of_hasEigenvector`
  does not exist in the needed shape, prove the two-step composition
  (`X` and `+`/`•` congruences) — monomial induction.
* **Integrality of a_m(f_j) for the dim-2 statements** (same issue as
  b2's risk): at dim 2 the theorem's coefficients ARE the statement (the
  identity holds over ℂ with integer-valued coefficients); integrality as a
  ℤ-polynomial statement needs the coefficient-integrality input — same G1
  audit as b2, share findings.
* Proof standard: no decides expected anywhere in b3 (generic proofs +
  tiny instances); any decide stays entrywise/propext-clean.

## 6. Lessons learnt (brought in)

Eigen-containment is the spectral reading of a matrix identity (probe-3 G2)
— state it operator-level, derive matrix corollaries, never the reverse.
The Gal = S₂ route was vetted by probe-3 G3: all six discriminants are
non-squares, all inputs landed.  Do not state Hecke-field equality without
an eigenform definition — containment is the faithful formalizable core
(the article's ℚ(λ₂) claim included).
