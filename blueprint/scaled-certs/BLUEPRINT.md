# BLUEPRINT i25-1 — scaled-certs: propext-only `scaled` / `scaled_id`

Objective: every nested certificate in `HeckeIndex{Small,}Weights`
(`HeckeIndexWeightKK.scaled`) and `HeckeRational{Small,}Weights`
(`HeckeRatWeightKK.scaled_id`) depends on `propext` only; the theorem
statements stay byte-identical (downstream: HeckeIndexCard*, HeckeCyclic*,
HeckeField*).

Design (iteration-24 recipe, `HeckeLatticeIndex.hcard_of_check`, AGENTS.md
"Entrywise certificates are audited too"):
* NEW light module (e.g. `MathProof/ModularForms/ListMatCert.lean`; do not
  edit landed ancestors): `List`-based matrices (`List (List ℤ)` or
  `ℕ → ℕ → ℤ` tables), list matrix product / power, `List.range` sums,
  `Int.decEq` comparisons, a Bool `scaledCheck`, and ONE generic bridge
  `scaled_of_check : scaledCheck … = true → (hM : ∀ i j, M i j = m i j) →
  (∑ j ∈ range n, w j • M ^ j) = c • N` (and the `(1 : ℤ) •` variant).
* Per weight (generators `tools/gen_hecke_index.py`, `tools/gen_hecke_rat.py`
  — regenerate, `--check` byte-identical for every mode incl. `--card`):
  integer tables for the matrices, `fin_cases <;> rfl` table bridges (no
  decide), one `decide +kernel` on the Bool check, then the bridge.
  No `!![…]`, no `==` on ℤ, no `^` on numerals inside the decided term.
* Reuse whatever of `HeckeLatticeIndex` (`rowPowL`, `cellL`,
  `list_sum_eq_fin_sum`) fits — import it rather than copy if no cycle.

Gates: G1 audit (which defs the scaled cells unfold; `#axiom_path` on one
cell per file family); G2 generic module green; G3 small files green +
nested audit 0 on them; G4 big files green + nested 0 + full light root +
both AxCheckDecide passes (nested count for these 4 modules = 0) +
tauceti + ci_targets.  Memory: 8 GiB request; split rather than raise.
