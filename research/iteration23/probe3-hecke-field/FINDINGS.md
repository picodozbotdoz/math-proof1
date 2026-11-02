# Probe 3 FINDINGS — Hecke-field corollaries and dim-2 integrality

Probe: `probe_field.py` (this directory; pure Python, ~1 min).  ALL CHECKS
PASSED (2026-11-02).

## 1. Checks

* **G1 — dim-2 integrality, generic m**: `T_m = a_m(f₁)·1 + a_m(f₂)·T₂` for
  all m ≤ 60 at all six dim-2 weights (24, 28, 30, 32, 34, 38), as exact
  matrix identities in the Miller basis.  This is b3's dim-2 theorem: at dim 2
  the Hecke ring IS `ℤ[T₂]` and every `T_m` is an integer polynomial in `T₂`
  with coefficients read off the Miller q-expansions — a single generic-in-m
  statement per weight, no per-m certificates.
* **G2 — spectral sanity at k=36**: `N(M₂) = D·M₃` exactly (the committed
  certificate re-verified).  The eigenvalue containment `λ₃ = Q(λ₂)` is the
  spectral reading of this matrix identity.
* **G3 — Gal = S₂ wiring input**: the T₂ charpolys at the six dim-2 weights
  (re-derived here) all have NON-SQUARE discriminant
  (e.g. k=24: X² − 1080X − 20468736, disc = 83041344) — and the landed
  `MaedaSmallWeights.MaedaWeightKK.{P, charpoly_T2, maeda}` (11 `maeda`
  theorems in the file) already provide: monic quadratic + irreducible over ℚ
  = exactly the hypotheses of `MaedaGaloisQuad.bijective_of_quadratic`.
  The T₂-Gal-dim-2 gap (iteration22-review §6.3) is a small generated
  add-on consuming only landed pieces.

## 2. b3 shape (the corollary module)

Core generic-m statement per weight (all 54), riding b1+b2 with ZERO new
kernel-decide load beyond b2's det certificates:

    ∀ m ≥ 1, ∃ Q : ℚ[X], heckeTM m = aeval T₂ (Q.map (algebraMap ℚ ℂ))

Proof route (generic in m): duality `T_m = Σ_j a_m(f_j)T_j` (b2) + the Cramer
inverse `I_k • T_j = Σ_i adj(C)_{ji} • T₂^i` (generic; C, adj(C), I_k are
per-weight constants) + integrality of `a_m(f_j)` (from E₄/E₆/Δ integrality —
the coefficient functions are honest q-expansion coefficients; the G1 audit
must pin the Lean-integrality lemmas for the prodForm basis).  Subsumes
`heckeT3_eq_aeval_rat` (m = 3) and closes iteration22-review §6.1
(`T_p ∈ ℚ[T₂]` for ALL p at once).

Eigenfield corollary (per weight): every `T₂`-eigenvector `v` with eigenvalue
`λ₂` is a `T_m`-eigenvector with eigenvalue `Q_m(λ₂) ∈ ℚ(λ₂) =
IntermediateField.adjoin ℚ {λ₂}` — via `aeval`-application on eigenvectors
(Mathlib `Module.End` eigenvector API; exact lemma names to pin at G1).
Full "Hecke field = ℚ(λ₂)" field-equality packaging (needs the eigenform
coefficient-field definition) is a stretch goal with its own gate — the
eigenvalue-containment statement is the faithful core.

Dim-2 track (generic m, per the six weights): `T_m = a_m(f₁)•1 + a_m(f₂)•T₂`
with INTEGER coefficients — the integrality theorem the
hecke-denominators article flagged ("worth formalizing"); plus the
Gal = S₂ instances (G3).

## 3. Two-column reuse map (b3)

**Mathlib-at-pin**: `Module.End.HasEigenvector`/`HasEigenvalue` +
`aeval`-on-eigenvector lemmas (name pin at G1), `IntermediateField.adjoin`,
`Polynomial.aeval` composition; no Hecke-eigenform content (fine — we do not
need an eigenform structure, eigenvectors suffice).

**TauCeti** (study-only): `Newform.heckeTDiamondCuspNewAlgebraEquiv` (the
ℂ-split shape — not needed), `qExpansion_coeff_one_heckeTCuspLevelOne`
(the a₁-formula, b1's job).  No ℚ(λ₂) statement there.

**Own library**: `HeckeRational.exists_aeval_rat_of_rep` (the ℚ-witness
assembly pattern — b3 generalizes it to generic m), `MaedaGaloisQuad` (dim-2
Galois), `MaedaSmallWeights` (charpoly_T2/maeda inputs), the Miller-basis
coefficient machinery of the dim files (fb/Atab/q-lemmas), b1's T_m calculus
+ b2's index module.
