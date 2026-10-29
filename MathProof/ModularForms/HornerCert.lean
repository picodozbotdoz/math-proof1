import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# `propext`-free residue certificates

The proof standard asks computational facts to depend on `propext` only.
Certificates stated over `ZMod ℓ` do not: `∀ x : ZMod ℓ, …` decided by
`decide +kernel` depends on `[propext, Classical.choice, Quot.sound]` (the
`Fintype`/`ZMod` instances), and even evaluating a `ZMod` function pulls in
`Quot.sound`.  Plain `ℤ` arithmetic on a structural list and a bounded `ℕ`
quantifier (`Nat.decidableBallLT`) depends on no axioms at all.

So a residue certificate is stated as
`∀ y : ℕ, y < q → hornerZ cs y % q ≠ 0` (decided by the kernel) and turned
into "no integer root" by `no_root_of_cert` — a separate, non-computational
lemma, which may use the standard axioms.  A non-square certificate for `D`
is the special case `cs = [D, 0, -1]` (`D - y²`).

For a certificate about a polynomial expression in several `ZMod ℓ`
variables, state it over bounded `ℕ` with `ℤ` arithmetic and `% ℓ`
(`decide +kernel`, no axioms), then derive the `ZMod` statement:
`exists_natCast_eq` writes each variable as a cast `(y : ZMod ℓ)`,
`emod_eq_zero_of_cast` turns `((E : ℤ) : ZMod ℓ) = 0` into `E % ℓ = 0`, and
`push_cast; linear_combination h` matches the two sides.
-/

namespace HornerCert

/-- Horner evaluation of the integer polynomial with coefficient list `cs`
(constant term first): `hornerZ [c₀, c₁, …] y = c₀ + y * (c₁ + y * …)`.
Structural, so the kernel evaluates it. -/
def hornerZ : List ℤ → ℤ → ℤ
  | [], _ => 0
  | c :: cs, y => c + y * hornerZ cs y

lemma hornerZ_modEq (cs : List ℤ) {q a b : ℤ} (h : a ≡ b [ZMOD q]) :
    hornerZ cs a ≡ hornerZ cs b [ZMOD q] := by
  induction cs with
  | nil => rfl
  | cons c cs ih => exact (h.mul ih).add_left c

/-- A polynomial with no root mod `q` has no integer root. -/
lemma no_root_of_cert {cs : List ℤ} {q : ℕ} (hq : 0 < q)
    (h : ∀ y : ℕ, y < q → hornerZ cs y % q ≠ 0) (n : ℤ) : hornerZ cs n ≠ 0 := by
  intro hn
  have hpos : (0 : ℤ) < q := by exact_mod_cast hq
  have hy : ((n % q).toNat : ℤ) = n % q := Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne')
  have hlt : (n % q).toNat < q := by
    have := Int.emod_lt_of_pos n hpos
    omega
  refine h (n % q).toNat hlt ?_
  rw [hy]
  have hm := hornerZ_modEq cs (Int.mod_modEq n q)
  rw [hn] at hm
  simpa [Int.ModEq] using hm

/-- A non-square certificate: `D` is not a square mod `q`, hence not a square. -/
lemma ne_sq_of_cert {D : ℤ} {q : ℕ} (hq : 0 < q)
    (h : ∀ y : ℕ, y < q → hornerZ [D, 0, -1] y % q ≠ 0) (n : ℤ) : D ≠ n * n := by
  intro hD
  refine no_root_of_cert hq h n ?_
  simp only [hornerZ]
  rw [hD]
  ring

/-- Every element of `ZMod q` is the cast of a natural number `< q`. -/
lemma exists_natCast_eq {q : ℕ} [NeZero q] (x : ZMod q) : ∃ y : ℕ, y < q ∧ (y : ZMod q) = x :=
  ⟨x.val, x.val_lt, ZMod.natCast_zmod_val x⟩

/-- An integer that vanishes in `ZMod q` is `0` mod `q`. -/
lemma emod_eq_zero_of_cast {q : ℕ} {E : ℤ} (h : (E : ZMod q) = 0) : E % q = 0 :=
  Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd E q).mp h)

end HornerCert
