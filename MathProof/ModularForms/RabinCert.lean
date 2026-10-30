import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Rabin irreducibility certificates over `ZMod ℓ`

The mathematical core of iteration 19: Rabin's irreducibility test in the
direction needed for the Maeda weights, together with a kernel-friendly
*reflected* certificate language over `List ℤ` (the `LehmerMod` mirror
pattern: all arithmetic on integer lists reduced `% ℓ`, every loop
structural or fuelled, so kernel `decide` evaluates it).

The generated weight files (dimensions 6-10) will decide, for the charpoly
`f̄` of `T₂` reduced mod a certificate prime `ℓ` and `n = dim S_k`:

* `RabinCert.zpxw ℓ f̄ (RabinCert.bitsOf F (ℓ ^ n)) [1] = [0, 1]` — i.e.
  `X ^ (ℓ ^ n) ≡ X [MOD f̄]`;
* for each prime `q ∣ n`,
  `RabinCert.zpgcd ℓ W f̄ (RabinCert.zpxwsubX ℓ f̄ F (ℓ ^ (n / q))) = [1]`
  — the reflected gcd of `f̄` with `X ^ (ℓ ^ (n / q)) − X` (reduced mod `f̄`
  first, since the exponent is far too large for a dense list) is a unit,

and then conclude with `RabinCert.irreducible_of_rabin_int` that the
characteristic polynomial of `T₂` is irreducible over `ℚ`.

Mathematical content:

* the reflected engine `ztrim / znorm / zadd / zpmul / zprem / bitsOf / zpxw`
  (validated in the iteration-19 sketch), plus `zlast / zspow / zscale /
  znorm1 / zpgcd / zpowX / zpsubX / zpxwsubX`;
* the transport `RabinCert.toPoly : List ℤ → (ZMod ℓ)[X]` with homomorphism
  lemmas — every congruence holds *unconditionally* (in particular for every
  fuel), so no fuel-sufficiency proof is ever needed: a certificate that
  fails to decide simply fails, it cannot be unsound;
* `RabinCert.common_divisor_zpgcd`: every common divisor of the transported
  inputs divides the reflected gcd result — this turns `zpgcd … = [1]` into
  coprimality (`RabinCert.isCoprime_of_zpgcd`);
* `RabinCert.irreducible_of_rabin`, the one new mathematical lemma: a monic
  `f` of degree `n ≥ 1` over `ZMod ℓ` with `f ∣ X ^ (ℓ ^ n) − X` that is
  coprime to every `X ^ (ℓ ^ (n / q)) − X`, `q` ranging over the primes
  dividing `n`, is irreducible.  (The degree-divisibility sublemma the
  blueprint flagged as the main risk — the subfield lattice of finite
  fields — is already in Mathlib at this pin:
  `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X` and its converse
  `Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X` in
  `Mathlib/FieldTheory/Finite/Extension.lean`; only the assembly was new.)
* `RabinCert.irreducible_of_rabin_int`: the lift to `P : ℤ[X]` monic and
  irreducibility of `P.map (Int.castRingHom ℚ)` (Gauss, as in
  `MaedaDim4.irreducible_quartic_of_mod`).

Design notes (kernel rules, cf. `AGENTS.md`):

* every recursive definition below is structural in a subterm (lists, bits)
  or in an explicit fuel argument — no well-founded recursion, so the kernel
  can evaluate everything;
* the two loops whose progress is not a structural subterm (long division in
  `zprem`, bit generation in `bitsOf`) carry the fuel; the Euclid loop in
  `zpgcd` is fuelled too.  An exhausted fuel returns junk (`[0]`), which the
  transport lemmas handle soundly: `common_divisor_zpgcd` holds for *all*
  fuel values;
* `zpgcd` divides by the *normalized* previous remainder (`znorm1`: scaled by
  the Fermat inverse `(top entry) ^ (ℓ - 2) % ℓ`), so every long division
  cancels; the normalization multiplies by a unit scalar and the
  divisibility transport is insensitive to that.
-/

namespace RabinCert

open Polynomial

/-! ### The reflected mod-`ℓ` polynomial engine -/

/-- Little-endian coefficient lists over `ℤ`: drop trailing (high) zeros so
the length carries the degree. -/
def ztrim : List ℤ → List ℤ
  | [] => []
  | [a] => if a = 0 then [] else [a]
  | a :: t =>
      if ztrim t = [] then if a = 0 then [] else [a] else a :: ztrim t

def znorm (l : ℕ) (p : List ℤ) : List ℤ := ztrim (p.map fun x => x % l)

/-- Entrywise addition (pads with zeros), reduced mod `l`. -/
def zadd (l : ℕ) : List ℤ → List ℤ → List ℤ
  | [], r => r.map fun x => x % l
  | p, [] => p.map fun x => x % l
  | a :: p', b :: q' => (a + b) % l :: zadd l p' q'

/-- Dense product, structural in the first factor (keep it the shorter one). -/
def zpmul (l : ℕ) : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p', q =>
      znorm l (zadd l (q.map fun x => a * x % l) (0 :: zpmul l p' q))

/-- Last entry (the coefficient of the highest degree present); `0` for `[]`. -/
def zlast : List ℤ → ℤ
  | [] => 0
  | [a] => a
  | _ :: t => zlast t

/-- Remainder of `a` modulo a polynomial whose top entry is `≡ 1` mod `l`,
by fuelled long division: each cancellation step drops the length of `a` by
at least one, so a fuel of `a.length` suffices for a divisor that really is
monic mod `l` (an empty `a` with an empty `f` just burns fuel).  NOT
structural in `a` — the fuel is what makes this kernel-evaluable.  The
congruence lemma below holds for *every* fuel. -/
def zprem (l : ℕ) (f : List ℤ) : ℕ → List ℤ → List ℤ
  | 0, a => a
  | fuel + 1, a =>
      if a.length < f.length then znorm l a
      else
        zprem l f fuel
          (znorm l (zadd l a
            (List.replicate (a.length - f.length) 0 ++
              f.map fun x => -(zlast a) * x % l)))

/-- Bits of `n`, most-significant first; fuel = an upper bound on the bit
length (structural in the fuel). -/
def bitsOf : ℕ → ℕ → List Bool
  | 0, _ => []
  | _fuel + 1, 0 => []
  | fuel + 1, n => bitsOf fuel (n / 2) ++ [decide (n % 2 == 1)]

/-- `X ^ e mod f` by MSB-first square-and-multiply, structural in the bit
list: each step squares and, on a set bit, multiplies by `X`.  `X ^ e mod f`
is `zpxw l f (bitsOf F e) [1]` (with `2 ^ F` above the bit length of `e`). -/
def zpxw (l : ℕ) (f : List ℤ) : List Bool → List ℤ → List ℤ
  | [], r => znorm l r
  | bt :: bits, r =>
      let s := zprem l f (2 * f.length) (zpmul l r r)
      zpxw l f bits (zprem l f (2 * f.length) (if bt then zpmul l [0, 1] s else s))

/-- `t ^ e % l` by iterated multiplication (structural in the fuel). -/
def zspow (l : ℕ) : ℕ → ℤ → ℤ
  | 0, _ => 1
  | e + 1, t => t * zspow l e t % l

/-- Entrywise scaling by `s % l`. -/
def zscale (l : ℕ) (s : ℤ) : List ℤ → List ℤ
  | [] => []
  | x :: t => (x * s % l) :: zscale l s t

/-- Normalize: reduce mod `l`, then scale by the Fermat inverse
`(top entry) ^ (l - 2) % l` of the top entry, so the result is `≡` monic
mod `l` whenever it is nonzero (this is what lets `zprem` cancel).  Zero
stays zero. -/
def znorm1 (l : ℕ) (p : List ℤ) : List ℤ :=
  if znorm l p = [] then []
  else zscale l (zspow l (l - 2) (zlast (znorm l p))) (znorm l p)

/-- Euclid's algorithm on reflected polynomials, with explicit fuel: each
step replaces `(a, b)` by `(b, a mod b')` where `b'` is the normalized `b`,
so every long division cancels and the degree of the second argument
strictly decreases — a fuel of about the sum of the input lengths is
generous.  An exhausted fuel returns `[0]`, which the transport lemmas
handle soundly (`common_divisor_zpgcd` holds for all fuel). -/
def zpgcd (l : ℕ) : ℕ → List ℤ → List ℤ → List ℤ
  | 0, _, _ => [0]
  | fuel + 1, a, b =>
      match znorm1 l b with
      | [] => znorm l a
      | b' => zpgcd l fuel b' (zprem l b' (2 * a.length + 2) a)

/-- The dense coefficient list of `X ^ k` (little-endian; only for small `k`,
e.g. in toy checks — real Rabin exponents go through `zpxw`). -/
def zpowX (l : ℕ) : ℕ → List ℤ
  | 0 => [1]
  | k + 1 => 0 :: zpowX l k

/-- The dense coefficient list of `X ^ k - c` reduced mod `l` (small `k`). -/
def zpsubX (l : ℕ) (k : ℕ) (c : ℤ) : List ℤ :=
  znorm l (zadd l (zpowX l k) [(-c) % l])

/-- `X ^ e - X` reduced modulo `f` for *huge* `e`: run `zpxw` first (the
exponent never appears as a dense list), then subtract `X` and reduce again.
This is the second Rabin argument `X ^ (ℓ ^ (n / q)) − X` in reflected form. -/
def zpxwsubX (l : ℕ) (f : List ℤ) (F e : ℕ) : List ℤ :=
  zprem l f (2 * f.length)
    (zadd l (zpxw l f (bitsOf F e) [1]) [0, (-1 : ℤ) % l])

/-! ### Transport: `List ℤ` → `(ZMod ℓ)[X]` -/

/-- Little-endian interpretation of a coefficient list over `ZMod l`
(constant term first). -/
noncomputable def toPoly (l : ℕ) : List ℤ → (ZMod l)[X]
  | [] => 0
  | a :: t => C (a : ZMod l) + X * toPoly l t

theorem toPoly_nil (l : ℕ) : toPoly l ([] : List ℤ) = 0 := rfl

theorem toPoly_cons (l : ℕ) (a : ℤ) (t : List ℤ) :
    toPoly l (a :: t) = C (a : ZMod l) + X * toPoly l t := rfl

theorem toPoly_one (l : ℕ) : toPoly l [1] = 1 := by
  simp [toPoly, Polynomial.C_1]

/-- An integer reduced mod `l` casts to the same element of `ZMod l`. -/
theorem intCast_mod_cast {l : ℕ} (x : ℤ) : ((x % l : ℤ) : ZMod l) = (x : ZMod l) :=
  (ZMod.intCast_eq_intCast_iff (x % l) x l).mpr (Int.mod_modEq x l)

theorem toPoly_map_mod (l : ℕ) : ∀ p : List ℤ,
    toPoly l (p.map fun x => x % l) = toPoly l p := by
  intro p
  induction p with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, toPoly_cons, ih, intCast_mod_cast]

theorem toPoly_ztrim (l : ℕ) : ∀ p : List ℤ, toPoly l (ztrim p) = toPoly l p := by
  intro p
  induction p with
  | nil => rfl
  | cons a t ih =>
      cases t with
      | nil =>
          by_cases h : a = 0
          · have hz : ztrim [a] = [] := by simp only [ztrim, ite_eq_left h]
            rw [hz, h]
            simp [toPoly, Polynomial.C_0]
          · have hz : ztrim [a] = [a] := by simp only [ztrim, ite_eq_right h]
            rw [hz]
      | cons b t' =>
          by_cases hzt : ztrim (b :: t') = []
          · by_cases h : a = 0
            · have hz : ztrim (a :: b :: t') = [] := by
                simp only [ztrim, ite_eq_left hzt, ite_eq_left h]
              rw [hz, h, toPoly_cons, ← ih, hzt, toPoly_nil]
              simp [Polynomial.C_0, mul_zero]
            · have hz : ztrim (a :: b :: t') = [a] := by
                simp only [ztrim, ite_eq_left hzt, ite_eq_right h]
              rw [hz, toPoly_cons, toPoly_cons, ← ih, hzt, toPoly_nil]
          · have hz : ztrim (a :: b :: t') = a :: ztrim (b :: t') := by
              simp only [ztrim, ite_eq_right hzt]
            rw [hz, toPoly_cons, toPoly_cons, ih]

theorem toPoly_znorm (l : ℕ) (p : List ℤ) : toPoly l (znorm l p) = toPoly l p := by
  simp only [znorm, toPoly_map_mod, toPoly_ztrim]

theorem toPoly_zadd (l : ℕ) : ∀ p q : List ℤ,
    toPoly l (zadd l p q) = toPoly l p + toPoly l q := by
  intro p
  induction p with
  | nil =>
      intro q
      change toPoly l (q.map fun x => x % l) = 0 + toPoly l q
      rw [toPoly_map_mod, zero_add]
  | cons a p' ih =>
      intro q
      cases q with
      | nil =>
          change toPoly l ((a :: p').map fun x => x % l) = _
          rw [toPoly_map_mod, toPoly_cons, toPoly_nil, add_zero]
      | cons b q' =>
          change toPoly l ((a + b) % l :: zadd l p' q') = _
          rw [toPoly_cons, toPoly_cons, toPoly_cons, ih, intCast_mod_cast, Int.cast_add,
            Polynomial.C_add]
          ring

theorem toPoly_map_smul (l : ℕ) (s : ℤ) : ∀ p : List ℤ,
    toPoly l (p.map fun x => s * x % l) = C ((s : ℤ) : ZMod l) * toPoly l p := by
  intro p
  induction p with
  | nil => simp [toPoly]
  | cons x t ih =>
      change toPoly l ((s * x % l) :: (t.map fun x => s * x % l)) = _
      rw [toPoly_cons, ih, toPoly_cons, intCast_mod_cast, Int.cast_mul, Polynomial.C_mul]
      ring

theorem toPoly_zpmul (l : ℕ) : ∀ p q : List ℤ,
    toPoly l (zpmul l p q) = toPoly l p * toPoly l q := by
  intro p
  induction p with
  | nil => intro q; simp [zpmul, toPoly]
  | cons a p' ih =>
      intro q
      change toPoly l (znorm l (zadd l (q.map fun x => a * x % l) (0 :: zpmul l p' q))) = _
      rw [toPoly_znorm, toPoly_zadd, toPoly_map_smul, toPoly_cons, ih, toPoly_cons]
      simp only [Int.cast_zero, Polynomial.C_0, zero_add]
      ring

theorem toPoly_replicate_zero (l k : ℕ) : toPoly l (List.replicate k (0 : ℤ)) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, toPoly_cons, ih, Int.cast_zero, Polynomial.C_0,
        mul_zero, add_zero]

theorem toPoly_append (l : ℕ) : ∀ p q : List ℤ,
    toPoly l (p ++ q) = toPoly l p + X ^ p.length * toPoly l q := by
  intro p
  induction p with
  | nil => intro q; simp [toPoly]
  | cons a p' ih =>
      intro q
      rw [List.cons_append, toPoly_cons, ih, toPoly_cons, List.length_cons, pow_succ]
      ring

theorem exists_mul_add_pow_two_pow {R : Type*} [CommRing R] (k : ℕ) (u v w : R) :
    ∃ z : R, (w * u + v) ^ (2 ^ k) = z * w + v ^ (2 ^ k) := by
  induction k with
  | zero => exact ⟨u, by rw [pow_zero, pow_one, pow_one]; ring⟩
  | succ k ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨z * z * w + 2 * z * v ^ (2 ^ k), ?_⟩
      rw [pow_succ' 2 k, show ((2 : ℕ) * 2 ^ k) = 2 ^ k * 2 from by ring, pow_mul, hz,
        pow_two, show ((2 : ℕ) ^ k * 2) = 2 ^ k + 2 ^ k from by ring, pow_add]
      ring

/-- **The long-division congruence.**  `toPoly (zprem l f F a)` is congruent
to `toPoly a` modulo `toPoly f` — for *every* fuel `F` and every divisor
list `f` (monic or not): the fuel only controls how far the reduction is
carried, never the congruence. -/
theorem toPoly_zprem (l : ℕ) (f : List ℤ) : ∀ (F : ℕ) (a : List ℤ),
    ∃ q : (ZMod l)[X],
      toPoly l a = q * toPoly l f + toPoly l (zprem l f F a) := by
  intro F
  induction F with
  | zero =>
      intro a
      exact ⟨0, by change toPoly l a = 0 * toPoly l f + toPoly l a; rw [zero_mul, zero_add]⟩
  | succ F ih =>
      intro a
      by_cases hlt : a.length < f.length
      · have hz : zprem l f (F + 1) a = znorm l a := by
          change (if a.length < f.length then znorm l a
            else
              zprem l f F
                (znorm l (zadd l a
                  (List.replicate (a.length - f.length) 0 ++
                    f.map fun x => -(zlast a) * x % l)))) = znorm l a
          rw [ite_eq_left hlt]
        rw [hz]
        exact ⟨0, by rw [zero_mul, zero_add, toPoly_znorm]⟩
      · have hz : zprem l f (F + 1) a =
            zprem l f F
              (znorm l (zadd l a
                (List.replicate (a.length - f.length) 0 ++
                  f.map fun x => -(zlast a) * x % l))) := by
          change (if a.length < f.length then znorm l a
            else
              zprem l f F
                (znorm l (zadd l a
                  (List.replicate (a.length - f.length) 0 ++
                    f.map fun x => -(zlast a) * x % l)))) = zprem l f F
            (znorm l (zadd l a
              (List.replicate (a.length - f.length) 0 ++
                f.map fun x => -(zlast a) * x % l)))
          rw [ite_eq_right hlt]
        obtain ⟨q', hq'⟩ := ih
          (znorm l (zadd l a
            (List.replicate (a.length - f.length) 0 ++
              f.map fun x => -(zlast a) * x % l)))
        have hA : toPoly l (znorm l (zadd l a
              (List.replicate (a.length - f.length) 0 ++
                f.map fun x => -(zlast a) * x % l)))
            = toPoly l a
              + X ^ (a.length - f.length)
                * (C ((-(zlast a) : ℤ) : ZMod l) * toPoly l f) := by
          rw [toPoly_znorm, toPoly_zadd, toPoly_append, toPoly_replicate_zero,
            List.length_replicate, zero_add, toPoly_map_smul]
        refine ⟨q' - X ^ (a.length - f.length) * C ((-(zlast a) : ℤ) : ZMod l), ?_⟩
        rw [hz]
        linear_combination hq' - hA

/-- The value of an MSB-first bit list. -/
def bval : List Bool → ℕ
  | [] => 0
  | b :: t => 2 ^ t.length * (if b then 1 else 0) + bval t

theorem bval_singleton (b : Bool) : bval [b] = if b then 1 else 0 := by
  cases b <;> rfl

theorem bval_append : ∀ p q : List Bool,
    bval (p ++ q) = bval p * 2 ^ q.length + bval q := by
  intro p
  induction p with
  | nil => intro q; simp [bval]
  | cons b t ih =>
      intro q
      change bval (b :: (t ++ q)) = _
      rw [bval, ih, bval, List.length_append, pow_add]
      ring

theorem bval_bitsOf : ∀ F n : ℕ, n < 2 ^ F → bval (bitsOf F n) = n := by
  intro F
  induction F with
  | zero =>
      intro n hn
      have h1 : (2 : ℕ) ^ 0 = 1 := pow_zero _
      rw [h1] at hn
      have hn0 : n = 0 := by omega
      rw [hn0]
      rfl
  | succ F ih =>
      intro n hn
      cases n with
      | zero => rfl
      | succ m =>
          have hlt : (m + 1) / 2 < 2 ^ F := by
            have hp : (2 : ℕ) ^ (F + 1) = 2 * 2 ^ F := by rw [pow_succ]; ring
            omega
          have hbit : (if decide ((m + 1) % 2 == 1) then (1 : ℕ) else 0) = (m + 1) % 2 := by
            rcases Nat.mod_two_eq_zero_or_one (m + 1) with hm | hm
            · simp [hm]
            · simp [hm]
          change bval (bitsOf F ((m + 1) / 2) ++ [decide ((m + 1) % 2 == 1)]) = m + 1
          rw [bval_append, bval_singleton, ih ((m + 1) / 2) hlt, hbit,
            List.length_singleton, pow_one]
          rw [Nat.mul_comm ((m + 1) / 2) 2]
          exact Nat.div_add_mod (m + 1) 2

/-- **The square-and-multiply congruence.**  `toPoly (zpxw l f bits r)` is
`toPoly r` raised to `2 ^ (bits length)` times `X` to the bit value, modulo
`toPoly f` — for every `f` and every fuel inside. -/
theorem toPoly_zpxw (l : ℕ) (f : List ℤ) : ∀ (bits : List Bool) (r : List ℤ),
    ∃ q : (ZMod l)[X],
      toPoly l (zpxw l f bits r)
        = q * toPoly l f + (toPoly l r) ^ (2 ^ bits.length) * X ^ (bval bits) := by
  intro bits
  induction bits with
  | nil =>
      intro r
      refine ⟨0, ?_⟩
      simp only [zpxw, toPoly_znorm, bval, List.length_nil, pow_zero, pow_one, mul_one,
        zero_mul, zero_add]
  | cons bt bits ih =>
      intro r
      have hstep : zpxw l f (bt :: bits) r =
          zpxw l f bits
            (zprem l f (2 * f.length)
              (if bt then zpmul l [0, 1] (zprem l f (2 * f.length) (zpmul l r r))
                else zprem l f (2 * f.length) (zpmul l r r))) := rfl
      obtain ⟨q1, hq1⟩ := toPoly_zprem l f (2 * f.length) (zpmul l r r)
      rw [toPoly_zpmul] at hq1
      rw [hstep]
      split
      · next hbt =>
          obtain ⟨q2, hq2⟩ := toPoly_zprem l f (2 * f.length)
            (zpmul l [0, 1] (zprem l f (2 * f.length) (zpmul l r r)))
          rw [toPoly_zpmul] at hq2
          have hX01 : toPoly l [0, 1] = X := by
            simp [toPoly, Polynomial.C_0, Polynomial.C_1]
          rw [hX01] at hq2
          obtain ⟨q3, hq3⟩ := ih (zprem l f (2 * f.length)
            (zpmul l [0, 1] (zprem l f (2 * f.length) (zpmul l r r))))
          have hR2 : toPoly l (zprem l f (2 * f.length)
              (zpmul l [0, 1] (zprem l f (2 * f.length) (zpmul l r r))))
              = toPoly l f * (-(q2))
                + X * toPoly l (zprem l f (2 * f.length) (zpmul l r r)) := by
            linear_combination hq2.symm
          have hS : toPoly l (zprem l f (2 * f.length) (zpmul l r r))
              = toPoly l f * (-(q1)) + toPoly l r * toPoly l r := by
            linear_combination hq1.symm
          rw [hR2] at hq3
          obtain ⟨zA, hzA⟩ := exists_mul_add_pow_two_pow bits.length (-(q2))
            (X * toPoly l (zprem l f (2 * f.length) (zpmul l r r))) (toPoly l f)
          rw [hzA] at hq3
          rw [hS] at hq3
          rw [mul_pow] at hq3
          obtain ⟨zB, hzB⟩ := exists_mul_add_pow_two_pow bits.length (-(q1))
            (toPoly l r * toPoly l r) (toPoly l f)
          rw [hzB] at hq3
          rw [← pow_two, ← pow_mul] at hq3
          refine ⟨q3 + (zA + X ^ (2 ^ bits.length) * zB) * X ^ (bval bits), ?_⟩
          simp only [List.length_cons, bval, ite_eq_left hbt, mul_one, pow_succ']
          linear_combination hq3
      · next hbt =>
          obtain ⟨q2, hq2⟩ := toPoly_zprem l f (2 * f.length)
            (zprem l f (2 * f.length) (zpmul l r r))
          obtain ⟨q3, hq3⟩ := ih (zprem l f (2 * f.length)
            (zprem l f (2 * f.length) (zpmul l r r)))
          have hR2 : toPoly l (zprem l f (2 * f.length)
              (zprem l f (2 * f.length) (zpmul l r r)))
              = toPoly l f * (-(q2))
                + toPoly l (zprem l f (2 * f.length) (zpmul l r r)) := by
            linear_combination hq2.symm
          have hS : toPoly l (zprem l f (2 * f.length) (zpmul l r r))
              = toPoly l f * (-(q1)) + toPoly l r * toPoly l r := by
            linear_combination hq1.symm
          rw [hR2] at hq3
          obtain ⟨zA, hzA⟩ := exists_mul_add_pow_two_pow bits.length (-(q2))
            (toPoly l (zprem l f (2 * f.length) (zpmul l r r))) (toPoly l f)
          rw [hzA] at hq3
          rw [hS] at hq3
          obtain ⟨zB, hzB⟩ := exists_mul_add_pow_two_pow bits.length (-(q1))
            (toPoly l r * toPoly l r) (toPoly l f)
          rw [hzB] at hq3
          rw [← pow_two, ← pow_mul] at hq3
          refine ⟨q3 + (zA + zB) * X ^ (bval bits), ?_⟩
          simp only [List.length_cons, bval, ite_eq_right hbt, pow_succ']
          linear_combination hq3

/-- From the first Rabin certificate to divisibility: if the reflected
square-and-multiply reduces `X ^ e` to `X` modulo `f`, then
`toPoly l f ∣ X ^ e - X`. -/
theorem dvd_of_zpxw {l : ℕ} {f : List ℤ} {F e : ℕ} (hbits : e < 2 ^ F)
    (h : zpxw l f (bitsOf F e) [1] = [0, 1]) :
    toPoly l f ∣ (X ^ e - X : (ZMod l)[X]) := by
  obtain ⟨q0, hq0⟩ := toPoly_zpxw l f (bitsOf F e) [1]
  have h1 : (toPoly l [1] : (ZMod l)[X]) = 1 := toPoly_one l
  rw [h1, one_pow, one_mul, bval_bitsOf F e hbits] at hq0
  have hX : (toPoly l [0, 1] : (ZMod l)[X]) = X := by
    simp [toPoly, Polynomial.C_1]
  rw [h, hX] at hq0
  exact ⟨-q0, by linear_combination hq0.symm⟩

theorem toPoly_zscale (l : ℕ) (s : ℤ) : ∀ q : List ℤ,
    toPoly l (zscale l s q) = C ((s : ℤ) : ZMod l) * toPoly l q := by
  intro q
  induction q with
  | nil => simp [zscale, toPoly]
  | cons x t ih =>
      change toPoly l ((x * s % l) :: zscale l s t) = _
      rw [toPoly_cons, ih, toPoly_cons, intCast_mod_cast, Int.cast_mul, Polynomial.C_mul]
      ring

theorem toPoly_znorm1 (l : ℕ) (p : List ℤ) :
    toPoly l (znorm1 l p) = C ((zspow l (l - 2) (zlast (znorm l p)) : ℤ) : ZMod l)
      * toPoly l p := by
  unfold znorm1
  split
  · next h =>
      have hp0 : toPoly l p = 0 := by rw [← toPoly_znorm, h, toPoly_nil]
      rw [hp0, mul_zero, toPoly_nil]
  · next h =>
      rw [toPoly_zscale, toPoly_znorm]

/-- **The reflected gcd divides like the gcd.**  Every common divisor `D` of
the *transported* inputs divides the reflected gcd result — for every fuel.
(In particular the exhausted-fuel junk `[0]` is harmless.) -/
theorem common_divisor_zpgcd (l : ℕ) : ∀ (F : ℕ) (a b : List ℤ) (D : (ZMod l)[X]),
    D ∣ toPoly l a → D ∣ toPoly l b → D ∣ toPoly l (zpgcd l F a b) := by
  intro F
  induction F with
  | zero =>
      intro a b D _ _
      have hz : toPoly l (zpgcd l 0 a b) = 0 := by simp [zpgcd, toPoly]
      rw [hz]
      exact dvd_zero _
  | succ F ih =>
      intro a b D hda hdb
      cases hzl : znorm1 l b with
      | nil =>
          have hzmatch : zpgcd l (F + 1) a b =
              (match znorm1 l b with
                | [] => znorm l a
                | b' => zpgcd l F b' (zprem l b' (2 * a.length + 2) a)) := rfl
          have hzb : zpgcd l (F + 1) a b = znorm l a := by rw [hzmatch, hzl]
          rw [hzb, toPoly_znorm]
          exact hda
      | cons w ws =>
          have hzmatch : zpgcd l (F + 1) a b =
              (match znorm1 l b with
                | [] => znorm l a
                | b' => zpgcd l F b' (zprem l b' (2 * a.length + 2) a)) := rfl
          have hzb : zpgcd l (F + 1) a b =
              zpgcd l F (w :: ws) (zprem l (w :: ws) (2 * a.length + 2) a) := by
            rw [hzmatch, hzl]
          have hdB : D ∣ toPoly l (w :: ws) := by
            have h1 : toPoly l (w :: ws)
                = C ((zspow l (l - 2) (zlast (znorm l b)) : ℤ) : ZMod l) * toPoly l b := by
              rw [← hzl, toPoly_znorm1]
            obtain ⟨e, he⟩ := hdb
            exact ⟨C ((zspow l (l - 2) (zlast (znorm l b)) : ℤ) : ZMod l) * e,
              by rw [h1, he]; ring⟩
          obtain ⟨q, hq⟩ := toPoly_zprem l (w :: ws) (2 * a.length + 2) a
          have hsub : toPoly l a - q * toPoly l (w :: ws)
              = toPoly l (zprem l (w :: ws) (2 * a.length + 2) a) := by
            linear_combination hq
          have hdq : D ∣ q * toPoly l (w :: ws) := by
            obtain ⟨e, he⟩ := hdB
            exact ⟨q * e, by rw [he]; ring⟩
          have hdR : D ∣ toPoly l (zprem l (w :: ws) (2 * a.length + 2) a) := by
            rw [← hsub]
            obtain ⟨e1, he1⟩ := hda
            obtain ⟨e2, he2⟩ := hdq
            exact ⟨e1 - e2, by rw [he1, he2]; ring⟩
          rw [hzb]
          exact ih (w :: ws) (zprem l (w :: ws) (2 * a.length + 2) a) D hdB hdR

/-- `zpgcd … = [1]` certifies coprimality of the transported polynomials. -/
theorem isCoprime_of_zpgcd {l : ℕ} [Fact l.Prime] {F : ℕ} {a b : List ℤ}
    (h : zpgcd l F a b = [1]) : IsCoprime (toPoly l a) (toPoly l b) := by
  have h1 := common_divisor_zpgcd l F a b
    (EuclideanDomain.gcd (toPoly l a) (toPoly l b))
    (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _)
  rw [h, toPoly_one] at h1
  obtain ⟨c, hc⟩ := (h1 : ∃ c, (1 : (ZMod l)[X])
    = EuclideanDomain.gcd (toPoly l a) (toPoly l b) * c)
  exact (EuclideanDomain.gcd_isUnit_iff).mp
    (isUnit_iff_exists_inv.mpr ⟨c, hc.symm⟩)

/-- The congruence behind `zpxwsubX`: `X ^ e - X` equals the transported
`zpxwsubX` value up to a multiple of `toPoly l f`. -/
theorem toPoly_zpxwsubX {l : ℕ} {f : List ℤ} {F e : ℕ} (hbits : e < 2 ^ F) :
    ∃ q : (ZMod l)[X],
      (X ^ e - X : (ZMod l)[X]) = q * toPoly l f + toPoly l (zpxwsubX l f F e) := by
  obtain ⟨q0, hq0⟩ := toPoly_zpxw l f (bitsOf F e) [1]
  have h1 : (toPoly l [1] : (ZMod l)[X]) = 1 := toPoly_one l
  rw [h1, one_pow, one_mul, bval_bitsOf F e hbits] at hq0
  obtain ⟨q1, hq1⟩ := toPoly_zprem l f (2 * f.length)
    (zadd l (zpxw l f (bitsOf F e) [1]) [0, (-1 : ℤ) % l])
  have hx : toPoly l [0, (-1 : ℤ) % l] = -X := by
    change C ((0 : ℤ) : ZMod l)
      + X * (C (((-1 : ℤ) % l : ℤ) : ZMod l) + X * toPoly l ([] : List ℤ)) = -X
    simp only [Int.cast_zero, Polynomial.C_0, intCast_mod_cast, Int.cast_neg, Int.cast_one,
      toPoly_nil, Polynomial.C_neg, Polynomial.C_1, mul_zero, add_zero, zero_add, mul_neg,
      mul_one]
  rw [toPoly_zadd, hx, hq0] at hq1
  refine ⟨q1 - q0, ?_⟩
  rw [zpxwsubX]
  linear_combination hq1

/-- The second Rabin certificate: if the reflected gcd of `f` with
`X ^ e - X` (reduced mod `f` by `zpxwsubX`) is `[1]`, then `toPoly l f` is
coprime to `X ^ e - X`. -/
theorem isCoprime_of_zpgcd_subX {l : ℕ} [Fact l.Prime] {f : List ℤ} {F e w : ℕ}
    (hbits : e < 2 ^ F) (h : zpgcd l w f (zpxwsubX l f F e) = [1]) :
    IsCoprime (toPoly l f) (X ^ e - X : (ZMod l)[X]) := by
  obtain ⟨u, v, huv⟩ := isCoprime_of_zpgcd h
  obtain ⟨q, hq⟩ := toPoly_zpxwsubX hbits
  refine ⟨u - v * q, v, ?_⟩
  linear_combination huv + v * hq

theorem zspow_cast (l : ℕ) :
    ∀ e : ℕ, ∀ t : ℤ, ((zspow l e t : ℤ) : ZMod l) = (t : ZMod l) ^ e := by
  intro e
  induction e with
  | zero => intro t; change ((1 : ℤ) : ZMod l) = (t : ZMod l) ^ 0; rw [Int.cast_one, pow_zero]
  | succ e ih =>
      intro t
      change ((t * zspow l e t % l : ℤ) : ZMod l) = _
      rw [intCast_mod_cast, Int.cast_mul, ih, pow_succ, mul_comm]

private theorem natCard_ZMod {l : ℕ} [Fact l.Prime] : Nat.card (ZMod l) = l := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  rw [Nat.card_eq_fintype_card, ZMod.card]

/-! ### Rabin's test -/

/-- **Rabin's irreducibility test (the direction needed here).**  A monic
polynomial `f` of degree `n ≥ 1` over `ZMod ℓ` (`ℓ` prime) that divides
`X ^ (ℓ ^ n) - X` and is coprime to `X ^ (ℓ ^ (n / q)) - X` for every prime
`q ∣ n` is irreducible.

An irreducible factor `g` of degree `m` divides `X ^ (ℓ ^ n) - X`, hence
`m ∣ n` (`Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`).  Either
`g` is associated to `f` (and `f` is irreducible), or `m < n`, so `m ∣ n / q`
for some prime `q ∣ n` and the converse Mathlib lemma gives
`g ∣ X ^ (ℓ ^ (n / q)) - X`; coprimality then forces `g` to be a unit. -/
theorem irreducible_of_rabin {l : ℕ} [Fact l.Prime] {f : (ZMod l)[X]}
    (hf : f.Monic) {n : ℕ} (hn : f.natDegree = n) (hn1 : 0 < n)
    (h1 : f ∣ X ^ (l ^ n) - X)
    (h2 : ∀ q : ℕ, q.Prime → q ∣ n → IsCoprime f (X ^ (l ^ (n / q)) - X)) :
    Irreducible f := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hf0 : f ≠ 0 := fun h => by rw [h] at hf; simp at hf
  have hf1 : ¬ IsUnit f := by
    intro hu
    obtain ⟨u, rfl⟩ := hu
    have h1u : (u : (ZMod l)[X]) * (↑u⁻¹ : (ZMod l)[X]) = 1 := u.mul_inv
    have h2u := congrArg Polynomial.natDegree h1u
    rw [Polynomial.natDegree_mul u.ne_zero u⁻¹.ne_zero, Polynomial.natDegree_one] at h2u
    omega
  obtain ⟨g, -, hgirr, hgdiv⟩ := Polynomial.exists_monic_irreducible_factor f hf1
  obtain ⟨c, hc⟩ := id hgdiv
  have hc0 : c ≠ 0 := fun h => hf0 (by rw [hc, h, mul_zero])
  have hnd : g.natDegree + c.natDegree = n := by
    rw [← hn, hc, Polynomial.natDegree_mul hgirr.ne_zero hc0]
  have hgnX : g ∣ X ^ (Nat.card (ZMod l) ^ n) - X := by
    rw [natCard_ZMod]
    exact hgdiv.trans h1
  have hmn : g.natDegree ∣ n := hgirr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hgnX
  rcases (by omega : g.natDegree = n ∨ g.natDegree < n) with heq | hlt
  · -- `g` is associated to `f`, which is therefore irreducible
    have hcnd : c.natDegree = 0 := by omega
    have hlc : c.leadingCoeff = c.coeff 0 := by simp only [Polynomial.leadingCoeff, hcnd]
    have hne : c.coeff 0 ≠ 0 := by
      rw [← hlc]
      exact Polynomial.leadingCoeff_ne_zero.mpr hc0
    have hcunit : IsUnit c := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hcnd, Polynomial.isUnit_C]
      exact (isUnit_iff_ne_zero).mpr hne
    have hass : Associated g f := by
      have h0 : Associated g (g * c) := associated_mul_unit_right g c hcunit
      rwa [← hc] at h0
    exact hass.irreducible_iff.mp hgirr
  · -- a proper irreducible factor would be a forbidden common divisor
    obtain ⟨t, ht⟩ := hmn
    have ht0 : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · rw [h, Nat.mul_zero] at ht; omega
      · exact h
    have ht2 : 2 ≤ t := by
      rcases Nat.lt_or_ge t 2 with h | h
      · have ht1 : t = 1 := by omega
        rw [ht1, Nat.mul_one] at ht
        omega
      · exact h
    obtain ⟨q, hqp, hqt⟩ := Nat.exists_prime_and_dvd (by omega : t ≠ 1)
    have hqn : q ∣ n := by
      obtain ⟨s, hs⟩ := hqt
      refine ⟨g.natDegree * s, ?_⟩
      rw [ht, hs, mul_comm q s]
      ring
    have hmq : g.natDegree ∣ n / q := by
      rw [ht, Nat.mul_div_assoc g.natDegree hqt]
      exact ⟨t / q, rfl⟩
    have hgS : g ∣ X ^ (l ^ (n / q)) - X := by
      have h9 := (hgirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X).mp hmq
      rwa [natCard_ZMod] at h9
    exact absurd (IsCoprime.isUnit_of_dvd' (h2 q hqp hqn) hgdiv hgS) hgirr.not_isUnit

/-! ### The packaged certificates -/

/-- **The packaged reflected Rabin certificate.**  With `f` the coefficient
list of the charpoly reduced mod `ℓ` (so that `toPoly l f` is monic of degree
`n`), the two reflected decisions — `zpxw … (ℓ ^ n) … = [0, 1]` and, for each
prime `q ∣ n`, `zpgcd … (zpxwsubX … (ℓ ^ (n / q))) … = [1]` (any fuel `w`) —
prove `toPoly l f` irreducible over `ZMod ℓ`. -/
theorem irreducible_of_rabin_cert {l : ℕ} [Fact l.Prime] {f : List ℤ} {n F : ℕ}
    (hmon : (toPoly l f).Monic) (hnd : (toPoly l f).natDegree = n) (hn1 : 0 < n)
    (hF : l ^ n < 2 ^ F)
    (h1 : zpxw l f (bitsOf F (l ^ n)) [1] = [0, 1])
    (h2 : ∀ q : ℕ, q.Prime → q ∣ n → ∃ w : ℕ,
      zpgcd l w f (zpxwsubX l f F (l ^ (n / q))) = [1]) :
    Irreducible (toPoly l f) := by
  refine irreducible_of_rabin hmon hnd hn1 (dvd_of_zpxw hF h1) ?_
  intro q hqp hqn
  obtain ⟨w, hw⟩ := h2 q hqp hqn
  refine isCoprime_of_zpgcd_subX ?_ hw
  calc l ^ (n / q) ≤ l ^ n :=
    Nat.pow_le_pow_right (show 0 < l from (Fact.out : l.Prime).pos) (Nat.div_le_self n q)
    _ < 2 ^ F := hF

/-- **The lift to `ℚ`.**  A monic integer polynomial whose reduction mod the
prime `ℓ` passes the reflected Rabin test is irreducible over `ℚ` (Gauss, as
in `MaedaLevelOne.irreducible_quartic_of_mod`). -/
theorem irreducible_of_rabin_int {P : ℤ[X]} (hmon : P.Monic) {l : ℕ} [Fact l.Prime]
    {f : List ℤ} {n F : ℕ} (hmap : P.map (Int.castRingHom (ZMod l)) = toPoly l f)
    (hmon' : (toPoly l f).Monic) (hnd : (toPoly l f).natDegree = n) (hn1 : 0 < n)
    (hF : l ^ n < 2 ^ F)
    (h1 : zpxw l f (bitsOf F (l ^ n)) [1] = [0, 1])
    (h2 : ∀ q : ℕ, q.Prime → q ∣ n → ∃ w : ℕ,
      zpgcd l w f (zpxwsubX l f F (l ^ (n / q))) = [1]) :
    Irreducible (P.map (Int.castRingHom ℚ)) := by
  have hZ : Irreducible P :=
    Polynomial.Monic.irreducible_of_irreducible_map (φ := Int.castRingHom (ZMod l)) P hmon
      (by rw [hmap]; exact irreducible_of_rabin_cert hmon' hnd hn1 hF h1 h2)
  have hQ := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ) hmon).mp hZ
  simpa [algebraMap_int_eq] using hQ

/-! ### Smoke tests (tiny kernel decides, cf. the validated sketch) -/

-- `X ^ 25 mod (X² + 2) = X` over `F₅`  (25 = 5²: the first Rabin condition).
example : zpxw 5 [2, 0, 1] (bitsOf 5 25) [1] = [0, 1] := by decide

-- The reflected gcd of `X² + 2` with `X ^ 12 − X` over `F₅` is `1`
-- (12 = 25 / 2: the `q = 2` coprimality condition for `n = 2`).
example : zpgcd 5 5 [2, 0, 1] (zpxwsubX 5 [2, 0, 1] 5 12) = [1] := by decide

end RabinCert
