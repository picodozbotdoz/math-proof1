import Mathlib.Tactic

/-!
# Kernel-verified sparse polynomials in five variables

A minimal, *structurally recursive* library for verifying large polynomial
identities by `decide +kernel` (the `LehmerPacked` methodology applied to
multivariate algebra).  A `Poly5` is a sparse list of `(monomial, coefficient)`
pairs kept in strictly ascending monomial order (lexicographic on the exponent
5-tuple, `x 0` major).

* `Mon` — exponent 5-tuples with componentwise addition.
* `pAdd`/`pScale`/`pMul`/`pPow` — merge-based arithmetic; every definition is
  structural (the `q`-recursion of the merge goes through the trampoline
  `pMerge`, which takes `pAdd ts` as an explicit function argument), so the
  kernel can evaluate everything on literals.  No well-founded recursion.
  Kernel stack depth is driven by the *left* operand of `pMul`, so put the
  smaller factor first.
* `pBeq` / `eq_of_pBeq` — the certificate check: a tail-recursive equality
  scan, so `decide +kernel` on `pBeq p q = true` needs constant stack for
  lists of any length.
* `PEval` — evaluation into any commutative ring, with unconditional
  homomorphism lemmas (`PEval_pAdd`, `PEval_pMul`, `PEval_pPow`): soundness
  never depends on sortedness.  Sortedness only matters for the *canonicality*
  of the representation, which the final `decide` checks explicitly — if an
  intermediate were non-canonical the `decide` fails loudly; it can never
  prove a false identity.
-/

/-- Monomials in `x 0, …, x 4`: exponent tuples. -/
abbrev Mon : Type := ℕ × ℕ × ℕ × ℕ × ℕ

namespace Mon

/-- The constant monomial `1`. -/
def one : Mon := (0, (0, (0, (0, 0))))

/-- Lexicographic order on monomials (the canonical list order). -/
protected def lt (a b : Mon) : Prop :=
  a.1 < b.1 ∨ a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ a.2.1 = b.2.1 ∧
    (a.2.2.1 < b.2.2.1 ∨ a.2.2.1 = b.2.2.1 ∧
      (a.2.2.2.1 < b.2.2.2.1 ∨ a.2.2.2.1 = b.2.2.2.1 ∧ a.2.2.2.2 < b.2.2.2.2)))

instance : DecidableRel Mon.lt := fun a b => by
  simp only [Mon.lt]
  infer_instance

/-- Trichotomy, the only order property the merge proofs need. -/
theorem lt_trichotomy (a b : Mon) : Mon.lt a b ∨ a = b ∨ Mon.lt b a := by
  simp only [Mon.lt]
  rcases Nat.lt_trichotomy a.1 b.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases Nat.lt_trichotomy a.2.1 b.2.1 with h2 | h2 | h2
    · exact Or.inl (Or.inr ⟨h, Or.inl h2⟩)
    · rcases Nat.lt_trichotomy a.2.2.1 b.2.2.1 with h3 | h3 | h3
      · exact Or.inl (Or.inr ⟨h, Or.inr ⟨h2, Or.inl h3⟩⟩)
      · rcases Nat.lt_trichotomy a.2.2.2.1 b.2.2.2.1 with h4 | h4 | h4
        · exact Or.inl (Or.inr ⟨h, Or.inr ⟨h2, Or.inr ⟨h3, Or.inl h4⟩⟩⟩)
        · rcases Nat.lt_trichotomy a.2.2.2.2 b.2.2.2.2 with h5 | h5 | h5
          · exact Or.inl (Or.inr ⟨h, Or.inr ⟨h2, Or.inr ⟨h3, Or.inr ⟨h4, h5⟩⟩⟩⟩)
          · exact Or.inr (Or.inl
              (Prod.ext h (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 h5)))))
          · exact Or.inr (Or.inr
              (Or.inr ⟨h.symm, Or.inr ⟨h2.symm, Or.inr ⟨h3.symm, Or.inr ⟨h4.symm, h5⟩⟩⟩⟩))
        · exact Or.inr (Or.inr
            (Or.inr ⟨h.symm, Or.inr ⟨h2.symm, Or.inr ⟨h3.symm, Or.inl h4⟩⟩⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h.symm, Or.inr ⟨h2.symm, Or.inl h3⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, Or.inl h2⟩))
  · exact Or.inr (Or.inr (Or.inl h))

/-- The equal case of the order trichotomy. -/
lemma eq_of_not_lt (a b : Mon) (h1 : ¬ Mon.lt a b) (h2 : ¬ Mon.lt b a) : a = b := by
  rcases Mon.lt_trichotomy a b with h | h | h
  · exact absurd h h1
  · exact h
  · exact absurd h h2

end Mon

open Mon

/-- Sparse polynomials: `(monomial, coefficient)` pairs, canonically strictly
sorted ascending (enforced by the data, never as proof obligations). -/
abbrev Poly5 : Type := List (Mon × ℤ)

namespace Poly5

/-- Multiply through by one term `c · m`. -/
def pScale (t : Mon × ℤ) : Poly5 → Poly5
  | [] => []
  | (m, c) :: ts => (m + t.1, c * t.2) :: pScale t ts

/-- The merge trampoline: merge `q` into `t :: ts`, with `rec = pAdd ts`
passed as an explicit function so that every recursion stays structural. -/
def pMerge (t : Mon × ℤ) (ts : Poly5) (rec : Poly5 → Poly5) : Poly5 → Poly5
  | [] => t :: ts
  | (m', c') :: ts' =>
      if Mon.lt t.1 m' then t :: rec ((m', c') :: ts')
      else if Mon.lt m' t.1 then (m', c') :: pMerge t ts rec ts'
      else if t.2 + c' = 0 then rec ts'
      else (t.1, t.2 + c') :: rec ts'

/-- Merge addition of two canonically sorted lists. -/
def pAdd : Poly5 → Poly5 → Poly5
  | [], q => q
  | t :: ts, q => pMerge t ts (pAdd ts) q

/-- Product (each term of `p` scaled through `q`, merged). -/
def pMul : Poly5 → Poly5 → Poly5
  | [], _ => []
  | t :: ts, q => pAdd (pScale t q) (pMul ts q)

/-- Equality test by a *tail-recursive* scan: `&&` reduces to its second
argument once the head comparison is `true`, so the kernel walks the list in
its whnf loop with constant native stack.  (`List`'s `DecidableEq` matches on
the recursive call's result instead, costing one kernel stack frame per
element — "deep recursion" past a few thousand terms.) -/
def pBeq : Poly5 → Poly5 → Bool
  | [], [] => true
  | t :: ts, t' :: ts' => decide (t = t') && pBeq ts ts'
  | _, _ => false

lemma eq_of_pBeq : ∀ {p q : Poly5}, pBeq p q = true → p = q
  | [], [], _ => rfl
  | t :: ts, t' :: ts', h => by
      simp only [pBeq, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, eq_of_pBeq h.2]
  | [], _ :: _, h => by simp [pBeq] at h
  | _ :: _, [], h => by simp [pBeq] at h

/-- Powers by iterated multiplication (structural in the exponent). -/
def pPow : ℕ → Poly5 → Poly5
  | 0, _ => [(Mon.one, 1)]
  | n + 1, p => pMul p (pPow n p)

section Eval

variable {K : Type*} [CommRing K]

/-- Evaluate a monomial. -/
def mEval (m : Mon) (x : Fin 5 → K) : K :=
  x 0 ^ m.1 * x 1 ^ m.2.1 * x 2 ^ m.2.2.1 * x 3 ^ m.2.2.2.1 * x 4 ^ m.2.2.2.2

/-- Monomial evaluation is multiplicative. -/
lemma mEval_add (m n : Mon) (x : Fin 5 → K) :
    mEval (m + n) x = mEval m x * mEval n x := by
  have e0 : (m + n).1 = m.1 + n.1 := rfl
  have e1 : (m + n).2.1 = m.2.1 + n.2.1 := rfl
  have e2 : (m + n).2.2.1 = m.2.2.1 + n.2.2.1 := rfl
  have e3 : (m + n).2.2.2.1 = m.2.2.2.1 + n.2.2.2.1 := rfl
  have e4 : (m + n).2.2.2.2 = m.2.2.2.2 + n.2.2.2.2 := rfl
  simp only [mEval, e0, e1, e2, e3, e4, pow_add]
  ring

/-- Evaluate a polynomial. -/
def PEval : Poly5 → (Fin 5 → K) → K
  | [], _ => 0
  | t :: ts, x => t.2 * mEval t.1 x + PEval ts x

@[simp] lemma PEval_nil (x : Fin 5 → K) : PEval [] x = 0 := rfl

@[simp] lemma PEval_cons (t : Mon × ℤ) (p : Poly5) (x : Fin 5 → K) :
    PEval (t :: p) x = t.2 * mEval t.1 x + PEval p x := rfl

lemma PEval_pScale (t : Mon × ℤ) (p : Poly5) (x : Fin 5 → K) :
    PEval (pScale t p) x = t.2 * mEval t.1 x * PEval p x := by
  induction p with
  | nil => simp [pScale]
  | cons h ts ih =>
      obtain ⟨m, c⟩ := h
      change PEval ((m + t.1, c * t.2) :: pScale t ts) x
        = t.2 * mEval t.1 x * PEval ((m, c) :: ts) x
      rw [PEval_cons, PEval_cons, ih, mEval_add]
      push_cast
      ring

lemma PEval_pMerge (t : Mon × ℤ) (ts : Poly5) (rec : Poly5 → Poly5)
    (x : Fin 5 → K)
    (ihrec : ∀ q, PEval (rec q) x = PEval ts x + PEval q x) :
    ∀ q, PEval (pMerge t ts rec q) x
      = t.2 * mEval t.1 x + PEval ts x + PEval q x := by
  intro q
  induction q with
  | nil =>
      simp only [pMerge, PEval_cons, PEval_nil]
      ring
  | cons hq ts' ih =>
      obtain ⟨m', c'⟩ := hq
      show PEval (pMerge t ts rec ((m', c') :: ts')) x = _
      simp only [pMerge]
      by_cases h1 : Mon.lt t.1 m'
      · simp only [h1, ↓reduceIte]
        simp only [PEval_cons, ihrec]
        ring
      · simp only [h1, ↓reduceIte]
        by_cases h2 : Mon.lt m' t.1
        · simp only [h2, ↓reduceIte]
          simp only [PEval_cons, ih]
          ring
        · simp only [h2, ↓reduceIte]
          have heq : t.1 = m' := eq_of_not_lt t.1 m' h1 h2
          by_cases h3 : t.2 + c' = 0
          · simp only [h3, ↓reduceIte]
            simp only [PEval_cons, ihrec, heq]
            rw [show t.2 = -c' from by omega]
            push_cast
            ring_nf
          · simp only [h3, ↓reduceIte]
            simp only [PEval_cons, ihrec, heq]
            push_cast
            ring

lemma PEval_pAdd (p q : Poly5) (x : Fin 5 → K) :
    PEval (pAdd p q) x = PEval p x + PEval q x := by
  induction p generalizing q with
  | nil => simp [pAdd]
  | cons t ts ih =>
      simp only [pAdd, PEval_cons]
      rw [PEval_pMerge t ts (pAdd ts) x ih]

lemma PEval_pMul (p q : Poly5) (x : Fin 5 → K) :
    PEval (pMul p q) x = PEval p x * PEval q x := by
  induction p with
  | nil => simp [pMul]
  | cons t ts ih =>
      simp only [pMul, PEval_cons, PEval_pAdd, PEval_pScale, ih]
      ring

lemma PEval_pPow (n : ℕ) (p : Poly5) (x : Fin 5 → K) :
    PEval (pPow n p) x = (PEval p x) ^ n := by
  induction n with
  | zero => simp [pPow, PEval_cons, mEval, Mon.one]
  | succ n ih => simp only [pPow, PEval_pMul, ih]; ring

end Eval

end Poly5
