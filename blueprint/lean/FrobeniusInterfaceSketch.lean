/-
Blueprint scratchpad (Task AA cycle 2): the group-theory stage (§4.1) and
the Frobenius hypothesis interface (§4.2) of
`blueprint/dedekind-frobenius/BLUEPRINT.md`, at the pinned Mathlib
(v4.36.0-rc1).  All names below verified at the pin:
`mem_alternatingGroup` (SpecificGroups/Alternating.lean:90), `sign_mul` /
`sign_symm` (GroupTheory/Perm/Sign.lean:366,386), `Int.units_eq_one_or`,
`Equiv.Perm.cycleType` / `cycleType_conj` (GroupTheory/Perm/Cycle/Type.lean:50,136),
`Polynomial.Gal.galActionHom` (FieldTheory/PolynomialGaloisGroup.lean:204).

Proved outright (no `sorry`):

* **parity-covering**: a subgroup of `Sₙ` containing `Aₙ` and one odd
  permutation is `Sₙ` — the "disc non-square ⟹ odd element" finish;
* **composition**: Jordan (as the hypothesis interface `JordanFor`, the
  future group-theory work) + odd element ⟹ `G = ⊤`.

Stated as interfaces (to be discharged by Dedekind's theorem / Jordan
respectively — the two workstreams of the blueprint):
`FrobHasCycleType`, `JordanFor`.

Check-only file: `lake env lean blueprint/lean/FrobeniusInterfaceSketch.lean`.
-/
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Analysis.Complex.Polynomial.Basic

open Equiv Polynomial

variable {n : ℕ} [NeZero n]

/-! ### Stage 1 (group theory): the parity finish — proved -/

omit [NeZero n] in
/-- A subgroup of `Sₙ` that contains `Aₙ` and one odd permutation is all of
`Sₙ`: with `g` odd in `G`, any odd `s` factors as `(s · g⁻¹) · g` with
`s · g⁻¹` even, hence in `Aₙ ≤ G`. -/
theorem eq_top_of_sup_alternating_of_odd
    (G : Subgroup (Equiv.Perm (Fin n))) (hA : alternatingGroup (Fin n) ≤ G)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ G) (hodd : Equiv.Perm.sign g ≠ 1) :
    G = ⊤ := by
  refine (Subgroup.eq_top_iff' G).mpr fun s => ?_
  rcases Int.units_eq_one_or s.sign with hs | hs
  · exact hA (Equiv.Perm.mem_alternatingGroup.mpr hs)
  · rcases Int.units_eq_one_or g.sign with h1 | h1
    · exact absurd h1 hodd
    · have he : (s * g⁻¹).sign = 1 := by
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, h1, hs]
        norm_num
      have hrw : s = s * g⁻¹ * g := by rw [mul_assoc, inv_mul_cancel, mul_one]
      rw [hrw]
      exact G.mul_mem (hA (Equiv.Perm.mem_alternatingGroup.mpr he)) hg

/-! ### The Jordan stage as an interface (future work, blueprint §4 stage 4) -/

/-- **Jordan interface.**  A transitive subgroup of `Sₙ` containing a
p-cycle (`cycleType = {p} + 1 ··· 1`) for a prime `p ≤ n − 3` contains `Aₙ`.
Everything downstream takes this as a hypothesis; the classical proof
(primitivity from the p-cycle, then Jordan 1871) is blueprint §4 stage 4. -/
def JordanFor (n : ℕ) : Prop :=
  ∀ G : Subgroup (Equiv.Perm (Fin n)),
    (∀ a b : Fin n, ∃ g ∈ G, g a = b) →
    (∃ p : ℕ, ∃ c : Equiv.Perm (Fin n),
      p.Prime ∧ p + 3 ≤ n ∧ c ∈ G ∧ c.cycleType = {p} + Multiset.replicate (n - p) 1) →
    alternatingGroup (Fin n) ≤ G

omit [NeZero n] in
/-- **The `Sₙ` criterion in interface form.**  Transitivity (from
irreducibility, `galAction_isPretransitive` after transporting to `Fin n`),
a Frobenius p-cycle (from the census + Dedekind, via `FrobHasCycleType`),
and an odd element (a transposition via Frobenius, or a non-square
discriminant) give `G = Sₙ`.  Only the two interface facts are unproved. -/
theorem eq_top_of_transitive_of_jordan_of_odd (hJ : JordanFor n)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (htrans : ∀ a b : Fin n, ∃ g ∈ G, g a = b)
    {p : ℕ} {c : Equiv.Perm (Fin n)}
    (hp : p.Prime) (hle : p + 3 ≤ n) (hc : c ∈ G)
    (hct : c.cycleType = {p} + Multiset.replicate (n - p) 1)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ G) (hodd : Equiv.Perm.sign g ≠ 1) :
    G = ⊤ :=
  eq_top_of_sup_alternating_of_odd G (hJ G htrans ⟨p, c, hp, hle, hc, hct⟩) hg hodd

/-! ### Stage 2: the Frobenius (Dedekind) interface over `Gal` -/

section Frobenius

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

variable {q : ℚ[X]}

/-- **Dedekind/Frobenius interface.**  "The Galois group of `q` contains an
element of cycle type `types`" — the exact proposition Dedekind's theorem
discharges for the factorization degrees of `q̄ mod ℓ` at squarefree primes
`ℓ`.  `galActionHom` embeds `q.Gal` into `Equiv.Perm (rootSet …)` (of card
`q.natDegree`), and `cycleType` is conjugation-invariant
(`cycleType_conj`), so the type is independent of the root ordering; the
census data in `blueprint/exploration/data/maeda_dim6_10.json` supplies
`(ℓ, types)` per weight. -/
def FrobHasCycleType (q : ℚ[X]) (types : Multiset ℕ) : Prop :=
  ∃ σ : q.Gal, (Gal.galActionHom q ℂ σ).cycleType = types

end Frobenius
