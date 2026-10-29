import MathProof.ModularForms.MaedaGalois5Weights

/-!
# Axiom audit for Iteration 18 (Galois group `S₅`)

Heavy (imports the `MaedaGalois5` identity chain): not in `defaultTargets`,
`MathProof.lean` or CI.  Build on Modal with
`tools/modal_run.sh --target MathProof.ModularForms.MaedaGalois5AxCheck`;
with the chain cached only this file elaborates.

The proof standard (CLAUDE.md) asks computational facts — the
`decide +kernel` certificates below — to depend on `propext` only; the
analytic and Galois-theoretic theorems may use the standard three axioms.
-/

/-! ### Computational certificates: expect `[propext]` or no axioms -/

-- `Poly5` kernel certificates (resolvent coefficients `e₁ … e₆`, `δ² = disc5`)
#print axioms MaedaGalois.e1dec
#print axioms MaedaGalois.e2dec
#print axioms MaedaGalois.e3dec
#print axioms MaedaGalois.e4dec
#print axioms MaedaGalois.e5dec
#print axioms MaedaGalois.e6dec
#print axioms MaedaGalois.ddec

-- per-weight residue certificates
#print axioms MaedaGalois.Weight60.nonsquare
#print axioms MaedaGalois.Weight60.noRootR
#print axioms MaedaGalois.Weight64.nonsquare
#print axioms MaedaGalois.Weight64.noRootR
#print axioms MaedaGalois.Weight66.nonsquare
#print axioms MaedaGalois.Weight66.noRootR
#print axioms MaedaGalois.Weight68.nonsquare
#print axioms MaedaGalois.Weight68.noRootR
#print axioms MaedaGalois.Weight70.nonsquare
#print axioms MaedaGalois.Weight70.noRootR
#print axioms MaedaGalois.Weight74.nonsquare
#print axioms MaedaGalois.Weight74.noRootR

/-! ### Transport and criterion: the standard three axioms are allowed -/

#print axioms MaedaGalois.theta_e6
#print axioms MaedaGalois.resolvent_eval_theta
#print axioms MaedaGalois.galActionHom_bijective_of_quintic
#print axioms MaedaGalois.Weight60.maeda_galois60
#print axioms MaedaGalois.Weight74.maeda_galois74
