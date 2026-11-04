# BLUEPRINT 1 — index-card: the lattice index [𝕋 : ℤ[T₂]] = I_k, all 54 weights

Iteration 24, b1 (the wave's foundation; b2 and b3 build on its module).
Authored by the orchestrator 2026-11-04 from
`research/iteration24/FINDINGS.md` (read it first — anchors, API citations,
refuted candidates).  Provenance: T2 submission 2026-11-04; trunk
`dev/iteration24-hecke-index` (base 8a8c9e0+).  Closes
iteration23-review §6.1 (the descoped `index_eq_det`).

## 0. Objective / non-objectives

**Objective.**  For every level-one weight `24 ≤ k ≤ 134` with
`2 ≤ dim S_k ≤ 10` (54 weights), prove the Hecke index as an honest lattice
index:

* **(i) Generic module** `MathProof/ModularForms/HeckeLatticeIndex.lean`
  (light, NEW module — never edit `HeckeIndex.lean`'s import ancestors):
  - `t2Lattice T2 n : Submodule ℤ (Module.End ℂ V) := span ℤ {T₂^j : j < n}`;
  - `basis_t2Lattice`: from `minpoly ℂ T₂` degree `n`, the powers
    `T₂^j, j < n` are a **ℤ-basis** of `t2Lattice`
    (ℂ-independence `aeval_inj_of_minpoly`-style or
    `LinearIndependent.pow_of_natDegree_minpoly`-style, then
    `LinearIndependent.restrict_scalars` for ℤ, then `Basis.mk`
    on the span);
  - `basis_heckeLattice`: from `hecke_independent`-hypotheses, the family
    `T_{j+1}, j < n` is a ℤ-basis of `heckeLattice k n` (same route);
  - **the core theorem** (`relIndex_t2_eq_det`): under the hypotheses of
    `HeckeIndex` plus `ℤ[T₂] ⊆ 𝕋` (`T2_pow_mem_heckeRing` / submodule
    version), with `C : Matrix (Fin n) (Fin n) ℤ` the coordinates of the
    powers (`C i j = φ_j(T₂^i)`, row `i` = Miller-coordinate row of
    `T₂^i`, FINDINGS F6 orientation),
    `(t2Lattice).toAddSubgroup.relIndex (heckeLattice k n).toAddSubgroup
      = C.det.natAbs`
    via `AddSubgroup.relIndex_eq_natAbs_det` applied with `E := 𝕋`'s own
    additive group (`L₂ = ⊤`, basis = T-family; see F6 caveat — do NOT
    apply it inside `End ℂ S_k` directly), bridged with
    `Submodule.span_int_eq_addSubgroupClosure`.
* **(ii) Generated instances** `HeckeIndexCardSmallWeights.lean` (dims 2–5,
  push tier) / `HeckeIndexCardWeights.lean` (dims 6–10, root-only — split at
  the CI full-only boundary, the `HeckeGeneratedByT2` precedent):
  extend `tools/gen_hecke_index.py` (new flag/mode; `--check` byte-identity
  for ALL modes must stay green) to emit per weight: the `C` literal
  (`= matpow(M2m, i)[0][:]` in probe terms — RE-DERIVE in a G1 audit, never
  trust `index_data.json` blindly), `det_C : C.det = Ikc` (`eval_det`;
  `Ikc` the signed literal), and
  `index_card : relIndex … = Ik.natAbs` where `Ik` is the LANDED
  `HeckeIndexWeightK.Ik` literal — connect `C.det` to it by
  `natAbs` congruence plus a per-weight sign `decide`.
* **(iii) Corollary** `index_eq_natCard`: `Nat.card (𝕋 ⧸ ℤ[T₂]) = Ik.natAbs`
  from the `relIndex` unfolding (one generic lemma).

**Non-objectives.**  `D = I_k` (b2's cyclicity work); ring-generator
statements (b3); `index_eq_det` in the det-of-A (not C) orientation beyond
the sign bridge; dims ≥ 11; any `Nat.card`-of-cokernel generalities beyond
what `relIndex` needs.

## 1. Reuse map (two columns)

| need | Mathlib at pin (`.lake/packages/mathlib`) | TauCeti (study-only) |
|---|---|---|
| index = \|det\| | `Submodule.natAbs_det_basis_change`, `AddSubgroup.relIndex_eq_natAbs_det`, `relIndex_eq_abs_det` (`LinearAlgebra/FreeModule/Finite/CardQuotient.lean`) — read 2026-11-04 | `Submodule.IsLattice.relIndex_span_eq_abs_det_mul` (`Algebra/Module/Lattice.lean`) — same content, no port |
| ℤ-basis from ℂ-independence | `LinearIndependent.restrict_scalars` (`LinearAlgebra/LinearIndependent/Basic.lean:72`), `Basis.mk`, `Submodule.mem_span_range_iff_exists_fun` | — |
| span ↔ closure | `Submodule.span_int_eq_addSubgroupClosure` (`LinearAlgebra/Span/Defs.lean:233`), `Submodule.toAddSubgroup` | — |
| power independence | `minpoly` degree route as in `HeckeIndex.aeval_inj_of_minpoly` (ours) | — |
| landed per-weight data | `HeckeIndexWeightK` (A, `det_A`, `Ik`, `hIkq/hIkc`), `HeckeRatWeightK.hmin`-style minpoly facts, `MaedaT3WeightK.fb/Atab/hA` | — |
| generator | `tools/gen_hecke_index.py` (extend; keep `--check` green), probe machinery `research/iteration23/hecke-index/g1_audit.py` | — |

## 2. Module layout

```
MathProof/ModularForms/HeckeLatticeIndex.lean   (light; generic; no data)
MathProof/ModularForms/HeckeIndexCardSmallWeights.lean  (generated, dims 2–5)
MathProof/ModularForms/HeckeIndexCardWeights.lean       (generated, dims 6–10)
tools/gen_hecke_index.py  (extended, --check covers old+new modes)
research/iteration24/index-card/  (G1 audit script + data + WORKLOG)
```
Registration: `HeckeLatticeIndex` + small file → `MathProof.lean` +
`defaultTargets`; big file root-only (NOT defaultTargets — CI bill), same
split as `HeckeGeneratedByT2{Small,}Weights`.

## 3. Verification plan

Everything light: `tools/modal_run.sh --file MathProof/ModularForms/HeckeLatticeIndex.lean`
then the two generated files (Modal; ~1 min each on warm cache); final:
light root target 0 err/0 warn + `AxCheckDecide` (expect new decides only
in generated files, all `propext`-clean — entrywise, never matrix-level
decides); `tools/tauceti_audit.sh`.  No heavy modules.

## 4. Stage gates (each ≈ one green-commit session; descope provisions)

* **G1 — audit.**  Re-derive `C` per weight from prodForm arithmetic
  (extend `g1_audit.py` usage as in `probe_index.py`); check `|det C| = Ik`
  for all 54 against the LANDED `Ik` literals (parse the Lean files, not
  the json); check the landed minpoly-degree facts' exact names per weight
  (the wiring hypothesis).  Commit audit script + data.
* **G2 — generic module green.**  `HeckeLatticeIndex.lean` compiles 0/0 on
  Modal with the core `relIndex_t2_eq_det` + corollary.  Descope: if the
  `relIndex_eq_natAbs_det` route hits an unforenable defeq wall at the
  `toIntSubmodule` boundaries, fall back to `Nat.card (M ⧸ N)` phrasing via
  `natAbs_det_basis_change` with `Module.Free/Finite` instances derived
  from the basis (both are Mathlib theorems; pick whichever transports
  cleanly).  Commit.
* **G3 — generator + small file green** (24 weights, dims 2–5): Modal
  green, `--check` byte-identical, per-weight `index_card` theorems.
* **G4 — big file green** (30 weights, dims 6–10) + registration (root,
  defaultTargets, ci-targets report) + audits (`AxCheckDecide`, tauceti).
  Descope (pre-authorized): if a dims-6–10 file exceeds ~10 min Modal or
  8 GiB (import floor + literals), split by dimension like
  `HeckeIndex{Small,}Weights` did — statement set unchanged.

## 5. Risks / fallbacks

* `relIndex`/`toIntSubmodule` defeq friction (the top risk): the F6 caveat
  (ambient = 𝕋's own group) is the designed answer; G2 must not burn more
  than one session on it — if both phrasings resist, descope G2 to the
  `Nat.card` form and record the wall (CORRECTIONS note).
* `Ik` sign: literals may be signed (`det_A : A.det = Ik`); everything
  goes through `.natAbs`; never `norm_num`-assume positivity — per-weight
  sign decided from the parsed `det_C`.
* Generated-literal style rules: chunked literals keep exponents ≤ 256;
  `Ik`/`det` values ≤ ~341 d plain, larger chunked (generator already does
  this — reuse, don't reinvent).
* Memory: expect import floor ≈ 5 GiB + literals; watch the `[memory]`
  table; the 16 GiB alert policy applies.

## 6. Lessons learnt (brought in)

Entrywise decides only (`Fintype.decidablePiFintype` trap); `List` sums
not `Finset` inside decides; compile-inherited-state-before-planning;
commit at every green milestone; WORKLOG heartbeat before/after any >10 min
run; poll `external-doc/inbox/` at every checkpoint; blueprint = starting
point — record deviations with evidence (§4d protocol).
