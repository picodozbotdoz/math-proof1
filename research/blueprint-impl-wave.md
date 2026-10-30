# Blueprint implementation wave — tracking (2026-10-31)

Operator instruction (`AGENT_NEW_INSTRUCTIONS_1.md`): implement the blueprints
from `dev/blueprint` (`blueprint/` directory) as branches
`impl/blueprint/[title]`, forked from `dev/i18-refactor-tauCeti-rule`, under
TauCeti coding rules.  One git worktree per item (outside the main tree, so
`lean_check`'s untracked-file overlay never sees them).

| branch | worktree | blueprint | status |
|---|---|---|---|
| `impl/blueprint/dedekind-frobenius` | `~/claude-workdir/wt-dedekind-frobenius` | `dedekind-frobenius/BLUEPRINT.md` §4 stages 1–2 | **committed `f54534a`**, `MaedaPermCriterion.lean` (118 lines) builds clean on Modal (linters on, audit-clean); registered in root/defaultTargets/CI |
| `impl/blueprint/hecke-algebra-upgrade` | `~/claude-workdir/wt-hecke-algebra-upgrade` | `hecke-algebra-upgrade/BLUEPRINT.md` | committed `15699be`: `HeckeAlgebraQT2.lean` (210 lines) — `minpoly_eq_charpoly_of_irreducible_charpoly` + the deliverable `exists_aeval_of_commute_of_irreducible_charpoly` (generic over endomorphisms; proved via T₂-cyclicity/Bézout instead of the blueprint's Module-descent — simpler and instance-free).  `HeckeCommute.lean` = open TODO.  First Modal build failed (2 unknown constants + section-variable `include` semantics) → fix loop in flight |
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
* Verification queue: each agent branch gets `tools/tauceti_audit.sh` + one
  Modal `lean_check --file` per new module (the dedekind one already passed).
