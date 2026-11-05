# BLUEPRINT i25-3 — maeda-small: propext-only `MaedaSmallWeights` q-lemmas

Objective: every nested certificate in
`MathProof/ModularForms/MaedaSmallWeights.lean` (the `q{i}_{j}` lemmas,
120) depends on `propext` only; all statements unchanged.

Context: the cells are `show seqP a b c m = v by decide +kernel` —
`seqP` goes through `Finset`/`ArithmeticFunction`/`Ramanujan.tau`.
`MaedaCertC` (`seqPLc`, `seqPLc_eq`) is exactly the propext-clean twin
(used by `MaedaDim{4,5}Weights`); `MaedaCertCExt` extends the cap.  Route:
`rw [← seqPLc_eq …]` (or the existing `seqPL`/`seqP_getD` path) then decide
the `seqPLc` value.  Check import order: `MaedaCertC` imports `MaedaDim4`;
`MaedaSmallWeights` must not create a cycle — if it would, add the needed
bridge in a NEW module imported by `MaedaSmallWeights` instead.
Generator: `tools/gen_maeda.py` — regenerate, never hand-edit; byte-check.

**Heavy-chain warning**: `MaedaSmallWeights` is an import ancestor of the
`MaedaGalois5` chain.  Build ONLY the light modules (`--file` the edited
file + light root); NEVER run `tools/stage_chain.sh` or any heavy module —
the orchestrator does the single approved chain rebuild at integration.
Keep the edit to `MaedaSmallWeights` (+ new module) so the chain rebuilds
once.

Gates: G1 audit (which seqP calls; `#axiom_path` on one cell); G2 file
green + nested 0 for it; G3 light root + both AxCheckDecide passes +
tauceti + ci_targets.
