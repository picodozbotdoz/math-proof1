# Blueprint implementation wave — tracking (2026-10-31)

Operator instruction (`AGENT_NEW_INSTRUCTIONS_1.md`): implement the blueprints
from `dev/blueprint` (`blueprint/` directory) as branches
`impl/blueprint/[title]`, forked from `dev/i18-refactor-tauCeti-rule`, under
TauCeti coding rules.  One git worktree per item (outside the main tree, so
`lean_check`'s untracked-file overlay never sees them).

| branch | worktree | blueprint | status |
|---|---|---|---|
| `impl/blueprint/dedekind-frobenius` | `~/claude-workdir/wt-dedekind-frobenius` | `dedekind-frobenius/BLUEPRINT.md` §4 stages 1–2 | **committed `f54534a`**, `MaedaPermCriterion.lean` (118 lines) builds clean on Modal (linters on, audit-clean); registered in root/defaultTargets/CI |
| `impl/blueprint/hecke-algebra-upgrade` | `~/claude-workdir/wt-hecke-algebra-upgrade` | `hecke-algebra-upgrade/BLUEPRINT.md` | **landed+verified**: `HeckeAlgebraQT2.lean` — `minpoly_eq_charpoly_of_irreducible_charpoly` + `exists_aeval_of_commute_of_irreducible_charpoly` (generic; via T₂-cyclicity/Bézout instead of the blueprint's Module-descent).  Modal build clean (0 errors / 0 warnings).  Two fix rounds: (1) section-variable restructure + pin-correct `exists_ne`; (2) the API-grep had targeted Mathlib **master@rc2** instead of the pinned rc1 — `IsOneApplyEqSelf`/`IsMulApplyEqComp` don't exist at the pin, reverted to `Module.End.one_apply`/`mul_apply`.  **Lesson: grep the pinned source at `.lake/packages/mathlib`, never a checkout of another ref.**  `HeckeCommute.lean` = open TODO (needs general `T_m`) |
| `impl/blueprint/iteration19-maeda-generic` | `~/claude-workdir/wt-iteration19-maeda-generic` | `iteration19-maeda-generic/BLUEPRINT.md` §2–3 (engines only; generated weight files later) | committed `c37db53`: `CharpolyEngine.lean` (47 lines, `charpoly_of_eval_eq`) + `RabinCert.lean` (769 lines) — **`irreducible_of_rabin` fully proved** (blueprint's main risk void: `Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X` + converse already at the pin, `FieldTheory/Finite/Extension.lean`); packaged `irreducible_of_rabin_cert` / `irreducible_of_rabin_int` for the generator; k=72 smoke decides [propext]-only.  Modal build OK exit 0; 12 `show`-tactic style warnings → fix loop in flight |

## Findings so far (dedekind-frobenius)

* **The blueprint's §1 variant is false.**  "Transitive + transposition +
  p-cycle (`p ≤ n−3`) ⟹ Sₙ" fails: `S₃ ≀ S₂` in `S₆` (setwise stabilizer of
  `{{0,1,2},{3,4,5}}`) is transitive, contains a transposition and a
  `{3,1,1,1}` 3-cycle with `p = 3 = n−3`, yet has order 72 < 360 = |A₆|
  (verified computationally).  The correct classical statements need
  **primitivity** (Wielandt 13.9: primitive + p-cycle ⟹ Aₙ; a p-cycle with
  `n/2 < p ≤ n−3` forces primitivity) or the elementary
  transposition + **(n−1)-cycle** ⟹ Sₙ.  Documented in the `JordanFor`
  docstring; `blueprint/dedekind-frobenius/BLUEPRINT.md` §1/§4-stage-4 needs
  the same correction upstream.
* **Mathlib inventory update**: the pin *has* partial Jordan content in
  `GroupTheory/GroupAction/Jordan.lean`
  (`eq_top_of_isPreprimitive_of_isSwap_mem`,
  `alternatingGroup_le_of_isPreprimitive_of_isThreeCycleMem`); the general
  prime-cycle form is an explicit Mathlib TODO.
* Validated API (pin): `alternatingGroup`, `Equiv.Perm.mem_alternatingGroup`,
  `Subgroup.eq_top_iff'`, `Equiv.Perm.sign_mul/sign_inv`, `Int.units_eq_one_or`,
  `Equiv.Perm.cycleType/cycleType_conj`, `Polynomial.Gal.galActionHom`,
  `Polynomial.Gal.splits_ℚ_ℂ`.

## Open

* Stages 3–4 of the dedekind blueprint (Dedekind's theorem proper; Jordan's
  primitive prime-cycle theorem) — future cycles; the interfaces
  (`FrobHasCycleType`, corrected `JordanFor`) are now in place to receive them.
* Verification: all three branches pass `tools/modal_run.sh --file` per new
  module (linters on) and are pushed (dedekind `f54534a`, iteration19
  `3de75de`, hecke `5c56cbe`); GitHub CI (lean-action + docgen) runs on each.
* Next main-loop work (not this wave): Iteration 19 generated weight files
  (per the RabinCert report's exact call list), `HeckeCommute.lean`,
  Dedekind stages 3–4.
