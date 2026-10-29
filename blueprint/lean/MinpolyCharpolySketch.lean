/-
Blueprint scratchpad (Task AA cycle 3): step 1 of the Maeda-statement
upgrade (`blueprint/hecke-algebra-upgrade/BLUEPRINT.md` §1.1) — an
irreducible characteristic polynomial *is* the minimal polynomial.

API at the pin: `LinearMap.charpoly` / `LinearMap.charpoly_monic` /
`LinearMap.isIntegral` / `LinearMap.minpoly_dvd_charpoly`
(`Mathlib/LinearAlgebra/Charpoly/Basic.lean`), `Polynomial.eq_of_monic_of_associated`
(`Mathlib/Algebra/Polynomial/Monic.lean:224`), `associated_of_dvd_dvd`,
`minpoly.monic`, `minpoly.aeval`, `Polynomial.isUnit_iff`.

Consequence (the upgrade's engine): with `minpoly = charpoly` of degree
`n = finrank`, `V` becomes a vector space over the field `AdjoinRoot f`
(`AdjoinRoot.instField`), of dimension 1 — every operator commuting with
`T` is a polynomial in `T`.  See the blueprint for steps 2–6.

Check-only file: `lake env lean blueprint/lean/MinpolyCharpolySketch.lean`.
-/
import Mathlib.LinearAlgebra.Charpoly.Basic

open Polynomial

/-- If the characteristic polynomial of `T` is irreducible (and `V ≠ 0`),
it already is the minimal polynomial: `minpoly ∣ charpoly`, both are monic,
and irreducibility leaves no other associate. -/
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Nontrivial V] (T : V →ₗ[K] V) (h : Irreducible T.charpoly) :
    minpoly K T = T.charpoly := by
  have hmon : (minpoly K T).Monic := minpoly.monic (LinearMap.isIntegral T)
  obtain ⟨F, hF⟩ := LinearMap.minpoly_dvd_charpoly T
  rcases h.isUnit_or_isUnit hF with hu | hu
  · exfalso
    rcases Polynomial.isUnit_iff.mp hu with ⟨c, -, hC⟩
    have hc1 : c = 1 := by
      have : (C c).Monic := by rw [hC]; exact hmon
      simpa [Monic, Polynomial.leadingCoeff_C] using this
    have hz : Polynomial.aeval T (minpoly K T) = 0 := minpoly.aeval K T
    rw [← hC, hc1] at hz
    simp at hz
  · obtain ⟨u, rfl⟩ : ∃ u : K[X]ˣ, (u : K[X]) = F := ⟨hu.unit, hu.unit_spec⟩
    refine eq_of_monic_of_associated hmon (LinearMap.charpoly_monic T)
      ⟨u, hF.symm⟩
