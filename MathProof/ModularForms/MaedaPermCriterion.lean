import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Permutation-group criteria for `Sₙ` and the Frobenius cycle-type interface

Blueprint `dedekind-frobenius` §4 stages 1–2: the group-theoretic side of the
Maeda `Sₙ` program, no number theory.  Two criteria are proved outright and
two facts are packaged as hypothesis-interfaces, so `Gal = Sₙ` theorems can be
stated *modulo* them while Dedekind's theorem (stage 3) and Jordan's theorem
(stage 4) are being formalized.

* `MaedaGalois.eq_top_of_sup_alternating_of_odd` — the parity finish: a
  subgroup of `Sₙ` containing `Aₙ` and one odd permutation is `Sₙ`.  The odd
  element is what a non-square discriminant (the `MaedaGalois*` files) or a
  Frobenius transposition supplies.
* `MaedaGalois.eq_top_of_transitive_of_jordan_of_odd` — the full `Sₙ`
  criterion (transitivity + Frobenius p-cycle + odd element) modulo the two
  interfaces below.
* `MaedaGalois.JordanFor` — Jordan's theorem in hypothesis-interface form
  (stage 4).
* `MaedaGalois.FrobHasCycleType` — the Dedekind/Frobenius interface:
  "`q.Gal` contains an element of cycle type `types`", the exact proposition
  Dedekind's theorem discharges from the factorization degrees of `q mod ℓ`
  at squarefree primes (stage 3).

All statements and proofs are ported verbatim from the validated sketch
`blueprint/lean/FrobeniusInterfaceSketch.lean` (Task AA cycle 2; elaborates
clean, zero warnings, at the pinned Mathlib v4.36.0-rc1).
-/

open Equiv Polynomial

namespace MaedaGalois

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

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
(primitivity from the p-cycle, then Jordan 1871) is blueprint §4 stage 4.

Caveat for stage 4 (statement kept verbatim from the validated sketch): in
this *transitive* form the bound `p ≤ n − 3` is too weak.  The imprimitive
group `S₃ ≀ S₂ ≤ S₆` (setwise stabilizer of `{{0, 1, 2}, {3, 4, 5}}`) is
transitive, contains the 3-cycle `(0 1 2)` of cycle type `{3, 1, 1, 1}`
(`p = 3 = n − 3`), and does not contain `A₆` (`|G| = 72 < 360`).  The
classical theorem is the *primitive* form (Wielandt 13.9, still a Mathlib
TODO; the swap and 3-cycle cases are in `Mathlib.GroupTheory.GroupAction.Jordan`),
usable transitively for `n/2 < p ≤ n − 3`, since a p-cycle with `p > n/2`
forces primitivity.  Stage 4 should discharge that corrected form and adjust
this interface (and blueprint §1) accordingly. -/
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

end MaedaGalois
