# Blueprint implementation wave — tracking (2026-10-31, CLOSED)

Operator instruction (`AGENT_NEW_INSTRUCTIONS_1.md`): implement the blueprints
from `dev/blueprint` (`blueprint/` directory) as branches
`impl/blueprint/[title]`, forked from `dev/i18-refactor-tauCeti-rule`, under
TauCeti coding rules.  One git worktree per item (outside the main tree, so
`lean_check`'s untracked-file overlay never sees them).

**Status: complete.**  All three branches landed, were Modal-verified
(linters on), and are **merged into `master`** (`b5d033e`, via the
`integration/blueprint-wave` branch with union-resolved registration files;
the combined light build passes locally, 8107 jobs).  The worktrees are
removed and the integration branch deleted; the three `impl/blueprint/*`
branches remain pushed on GitHub for reference.  Follow-up CI fix: `46f4e4d`
removed the docgen-action step (it rebuilt doc-gen4 + Mathlib from source and
risked clobbering the hand-maintained `docs/` Pages site) — CI is now the
single lean-action step (~2 min, project targets only, Mathlib oleans from
the CDN cache); see the workflow file's NOTE comment.

| branch | blueprint | result (merged commits) |
|---|---|---|
| `impl/blueprint/dedekind-frobenius` | `dedekind-frobenius/BLUEPRINT.md` §4 stages 1–2 | `MaedaPermCriterion.lean` (118 lines): parity finish `eq_top_of_sup_alternating_of_odd`, the `JordanFor` hypothesis interface, the `FrobHasCycleType` Dedekind interface.  Built clean on Modal; registered in root/defaultTargets/CI |
| `impl/blueprint/hecke-algebra-upgrade` | `hecke-algebra-upgrade/BLUEPRINT.md` | `HeckeAlgebraQT2.lean`: `minpoly_eq_charpoly_of_irreducible_charpoly` + `exists_aeval_of_commute_of_irreducible_charpoly` (generic over endomorphisms; proved via T₂-cyclicity/Bézout instead of the blueprint's Module-descent).  Two fix rounds before the clean Modal build: (1) section-variable restructure + pin-correct root `exists_ne`; (2) the API-grep had targeted Mathlib **master@rc2** instead of the pinned rc1 — `IsOneApplyEqSelf`/`IsMulApplyEqComp` don't exist at the pin, reverted to `Module.End.one_apply`/`Module.End.mul_apply` (`End.lean:56/59`).  **Lesson: grep the pinned source at `.lake/packages/mathlib`, never a checkout of another ref; `lake env lean <file>` reproduces lake semantics locally and beats Modal round trips for this error class.**  `HeckeCommute.lean` = open TODO (needs general `T_m`) |
| `impl/blueprint/iteration19-maeda-generic` | `iteration19-maeda-generic/BLUEPRINT.md` §2–3 (engines only) | `CharpolyEngine.lean` (47 lines, `charpoly_of_eval_eq`) + `RabinCert.lean` (769 lines) — **`irreducible_of_rabin` fully proved** (the blueprint's main risk was void: `Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X` ± converse already at the pin, `FieldTheory/Finite/Extension.lean`); packaged `irreducible_of_rabin_cert` / `irreducible_of_rabin_int` for the generator; k=72 smoke decides [propext]-only, Modal build warning-free (14 `show`-tactic style warnings fixed with `change`) |

## Findings (dedekind-frobenius)

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

## Open (future cycles, not this wave)

**Pickup pointer for the next session (Iteration 20).**  The source
blueprints, the exploration findings and the certificate-prime census
(`maeda_dim6_10.json`, all 30 dim-6–10 weights) live **only on the
`dev/blueprint` branch** (`blueprint/` directory — not merged to master):

```bash
git show dev/blueprint:blueprint/iteration19-maeda-generic/BLUEPRINT.md   # generator + module plan
git show dev/blueprint:blueprint/exploration/FINDINGS-maeda-dim6-10.md    # cost model, Rabin primes
git show dev/blueprint:blueprint/exploration/data/maeda_dim6_10.json      # the census data
git show dev/blueprint:blueprint/lean/gen_sketch_charpoly.py              # validated pilot generator
```

(`git checkout dev/blueprint blueprint/` puts the whole directory in the
working tree without switching branches.)  The engine this file's §Open
recipe calls into — `MathProof/ModularForms/{CharpolyEngine,RabinCert}.lean`
— is on `master` since this wave.

* Iteration 19 generated weight files: per weight `f̄ : List ℤ` (charpoly
  coeffs mod `ℓ`), `n = dim S_k`, fuel `F` with `ℓ ^ n < 2 ^ F`:
  `hmon`/`hnd` by `simp only [RabinCert.toPoly]; monicity!` /
  `compute_degree!`; `h1 : zpxw ℓ f̄ (bitsOf F (ℓ ^ n)) [1] = [0, 1]` by
  `decide +kernel`; per prime `q ∣ n`, `h2 q : ∃ w, zpgcd ℓ W f̄
  (zpxwsubX ℓ f̄ F (ℓ ^ (n / q))) = [1]` as `⟨W, by decide +kernel⟩`
  (`W ≈ f̄.length + 4`); then `RabinCert.irreducible_of_rabin_int`.  Needs
  `tools/gen_maedan.py` (byte-identical re-runs) + `MaedaCertC.seqPLc`
  basis data + τ through 50 (dim ≤ 10 needs `tauTable` ≤ 50; 21 verified).
* `HeckeCommute.lean` (general `T_m`, coefficient formula, q-expansion
  injectivity) — unlocks `exists_aeval_of_commute_of_irreducible_charpoly`
  for the level-one Hecke algebra, upgrading all Maeda statements to
  `Tₙ ∈ ℚ[T₂]`.
* Dedekind stages 3–4: Dedekind's theorem proper (discharges
  `FrobHasCycleType`) and Jordan's primitive prime-cycle theorem
  (discharges a *corrected* `JordanFor`).
