import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# HeckeField: eigenvalue containment for rational polynomials in an operator

The generic spectral half of the Hecke-field corollary: if an operator `T` is
a *rational* polynomial in an operator `T₂` over a complex vector space,
then every `T₂`-eigenline is `T`-stable and the `T`-eigenvalue is a rational
polynomial in the `T₂`-eigenvalue — in particular it lies in the eigenfield
`IntermediateField.adjoin ℚ {μ}` (read: `ℚ(μ)`).

* `eval_map_eq_aeval` — the ℚ/ℂ evaluation bridge (evaluating the ℂ-image of
  a rational polynomial is evaluating it through `ℚ →ₐ ℂ`);
* `eval_map_mem_adjoin` — the values of rational polynomials in `μ` land in
  `ℚ(μ)` (via `IntermediateField.mem_adjoin_simple_iff`);
* `apply_eq_eval_smul` — the eigenvector application
  `(aeval T₂ (Q.map ℚ→ℂ)) v = Q(μ) • v` (via Mathlib's
  `Module.End.aeval_apply_of_hasEigenvector`);
* `eigenvalue_mem_adjoin` — the operator-level containment: every nonzero
  `T₂`-eigenvector with eigenvalue `μ` is a `T`-eigenvector with eigenvalue
  in `ℚ(μ)`.

The statements are module-generic (no Hecke content, no finite dimension);
the per-weight instances (T₂ = `heckeTPₗ k 2`, T = `heckeTM k m`, the
rationality input from `heckeT3_eq_aeval_rat`'s generic-m sibling) are
consumed from the generated weights file.  Everything here is light and
imports only Mathlib; nothing is an ancestor of the heavy `MaedaGalois5Defs`
chain.
-/

namespace HeckeField

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The ℚ/ℂ evaluation bridge: evaluating the ℂ-image of a rational
polynomial at `μ : ℂ` is evaluating the rational polynomial at `μ` through
the structure map `ℚ →+* ℂ`. -/
theorem eval_map_eq_aeval (Q : ℚ[X]) (μ : ℂ) :
    (Q.map (algebraMap ℚ ℂ)).eval μ = aeval μ Q := by
  rw [eval_map, aeval_def]

/-- Rational polynomials in `μ` land in the eigenfield `ℚ(μ)`. -/
theorem eval_map_mem_adjoin (Q : ℚ[X]) (μ : ℂ) :
    (Q.map (algebraMap ℚ ℂ)).eval μ ∈ IntermediateField.adjoin ℚ ({μ} : Set ℂ) := by
  rw [IntermediateField.mem_adjoin_simple_iff]
  refine ⟨Q, 1, ?_⟩
  simp only [map_one, div_one]
  exact eval_map_eq_aeval Q μ

/-- **Eigenvector application.**  A polynomial in `T₂` (with ℂ coefficients)
acts on a `T₂`-eigenvector as its eigenvalue times the vector; stated for
the ℂ-image of a rational polynomial. -/
theorem apply_eq_eval_smul {T2 : V →ₗ[ℂ] V} {Q : ℚ[X]} {v : V} {μ : ℂ}
    (hv : v ≠ 0) (hμ : T2 v = μ • v) :
    (aeval T2 (Q.map (algebraMap ℚ ℂ))) v = (Q.map (algebraMap ℚ ℂ)).eval μ • v :=
  Module.End.aeval_apply_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hμ, hv⟩

/-- **Eigenvalue containment, generic form.**  If `T` is a rational
polynomial in `T₂`, then every nonzero `T₂`-eigenvector with eigenvalue `μ`
is a `T`-eigenvector whose eigenvalue lies in `ℚ(μ) =
IntermediateField.adjoin ℚ {μ}` — the spectral reading of the rational
polynomial identity, and the faithful formalizable core of the Hecke-field
claim `K_f ⊆ ℚ(λ₂)`. -/
theorem eigenvalue_mem_adjoin {T2 T : V →ₗ[ℂ] V}
    (hT : ∃ Q : ℚ[X], T = aeval T2 (Q.map (algebraMap ℚ ℂ)))
    {v : V} (hv : v ≠ 0) {μ : ℂ} (hμ : T2 v = μ • v) :
    ∃ w ∈ IntermediateField.adjoin ℚ ({μ} : Set ℂ), T v = w • v := by
  obtain ⟨Q, hQ⟩ := hT
  refine ⟨(Q.map (algebraMap ℚ ℂ)).eval μ, eval_map_mem_adjoin Q μ, ?_⟩
  rw [hQ]
  exact apply_eq_eval_smul hv hμ

end HeckeField
