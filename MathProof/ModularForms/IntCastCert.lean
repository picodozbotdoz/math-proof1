import Mathlib.Data.ZMod.Basic

/-!
# `propext`-only certificates for integer casts into `ZMod ℓ`

A rewrite `((n : ℤ) : ZMod ℓ) = (r : ZMod ℓ)` decided directly in `ZMod ℓ`
(`decide +kernel` on the `ZMod` equality) depends on `Classical.choice` and
`Quot.sound` through the `ZMod`/`DecidableEq` instances.  The same fact
decided over `ℤ` — `n % ℓ = r`, an `Int.decEq` comparison of `Int.emod`
literals — depends on no axioms at all; `intCast_eq_of_emod` turns it into
the cast equation (a non-computational step, standard axioms allowed).

Measured (2026-11-05): the decided residue stays `propext`-only also for
the chunked literals `c₀ * 10 ^ e₀ + …` of the generated Maeda files (`^` on
`ℤ` numerals), so one lemma serves every cell.
-/

namespace IntCastCert

/-- A residue computed over `ℤ` gives the cast equation in `ZMod ℓ`. -/
theorem intCast_eq_of_emod {ℓ : ℕ} {n r : ℤ} (h : n % (ℓ : ℤ) = r) :
    ((n : ℤ) : ZMod ℓ) = ((r : ℤ) : ZMod ℓ) := by
  rw [← ZMod.intCast_mod n ℓ, h]

end IntCastCert
