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
