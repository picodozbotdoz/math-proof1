/-
Blueprint scratchpad (Iteration 19): the reflected mod-ℓ polynomial
arithmetic for Rabin irreducibility certificates, with two kernel `decide`s:
a hand-checkable toy (X² + 2 over F₅) and the real first Rabin condition for
k = 72 (charpoly of T₂ on S₇₂, certificate prime ℓ = 107, exponent ℓ⁶ =
1 500 730 351 849).

Kernel rules honored (research-log Iteration 18 / AGENTS.md):
  * every function is structurally recursive — well-founded recursion
    (`Acc.rec`) would silently kill kernel evaluation; the two loops whose
    "progress" is not a structural subterm (long division, nat→bits) carry an
    explicit fuel argument supplied as a literal by the generator;
  * all arithmetic is over `ℤ` lists with `% ℓ` reduction after each step
    (the `LehmerMod` pattern), never over `ZMod ℓ` structures — `decide`
    statements stay axiom-clean (the `HornerCert` lesson);
  * the multiplication's *left* operand stays the shorter one (`pMul` stack
    lesson) — not load-bearing at degree ≤ 10, but kept.

What is deliberately NOT here: the reflected gcd and the Rabin theorem
itself (`f̄ | X^(ℓⁿ) − X` + coprimality ⟹ `Irreducible f̄` over `ZMod ℓ`,
then `Polynomial.Monic.irreducible_of_irreducible_map` + Gauss to ℚ) — the
one new mathematical lemma of Iteration 19; see
blueprint/iteration19-maeda-generic/BLUEPRINT.md §4.

Data: blueprint/exploration/data/maeda_dim6_10.json (k = 72, cert ℓ = 107).

Check-only file: `lake env lean blueprint/lean/RabinCertSketch.lean`.
-/
import Mathlib.Tactic.NormDet

/-- Little-endian coefficient lists over ℤ: drop trailing (high) zeros so the
length carries the degree. -/
def ztrim : List ℤ → List ℤ
  | [] => []
  | [a] => if a = 0 then [] else [a]
  | a :: t =>
      match ztrim t with
      | [] => if a = 0 then [] else [a]
      | t' => a :: t'

def znorm (l : ℕ) (p : List ℤ) : List ℤ := ztrim (p.map fun x => x % l)

/-- Entrywise addition (pads with zeros), reduced mod `ℓ`. -/
def zadd (l : ℕ) : List ℤ → List ℤ → List ℤ
  | [], r => r.map fun x => x % l
  | p, [] => p.map fun x => x % l
  | a :: p', b :: q' => (a + b) % l :: zadd l p' q'

/-- Dense product, structural in the first factor (keep it the shorter one). -/
def zpmul (l : ℕ) : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p', q =>
      znorm l (zadd l (q.map fun x => a * x % l) (0 :: zpmul l p' q))

/-- Remainder of `a` modulo a monic mod `ℓ` polynomial `f` (top entry ≡ 1),
by fuelled long division: each cancellation step drops the length of `a` by
at least one, so a fuel of `a.length` suffices (the generator passes
`2 * f.length` for products of two reduced polynomials).  NOT structural in
`a` — the fuel is what makes this kernel-evaluable. -/
def zprem (l : ℕ) (f : List ℤ) : ℕ → List ℤ → List ℤ
  | 0, a => a
  | fuel + 1, a =>
      if a.length < f.length then znorm l a
      else
        match a.getLast? with
        | none => []
        | some c =>
            zprem l f fuel
              (znorm l (zadd l a
                (List.replicate (a.length - f.length) 0 ++ f.map fun x => -c * x % l)))

/-- Bits of `n`, most-significant first; fuel = an upper bound on the bit
length (structural in the fuel). -/
def bitsOf : ℕ → ℕ → List Bool
  | 0, _ => []
  | _fuel + 1, 0 => []
  | fuel + 1, n => bitsOf fuel (n / 2) ++ [decide (n % 2 == 1)]

/-- `X ^ e mod f` by MSB-first square-and-multiply, structural in the bit
list: each step squares and, on a set bit, multiplies by `X`.  `X ^ e mod f`
is `zpxw l f (bitsOf F e) [1]` (with `F ≥ bit length of e`). -/
def zpxw (l : ℕ) (f : List ℤ) : List Bool → List ℤ → List ℤ
  | [], r => znorm l r
  | bt :: bits, r =>
      let s := zprem l f (2 * f.length) (zpmul l r r)
      zpxw l f bits (zprem l f (2 * f.length) (if bt then zpmul l [0, 1] s else s))

/-! ### Toy: X² + 2 over F₅ (irreducible; both Rabin data points) -/

-- X ^ 25 mod (X² + 2) = X over F₅   (25 = 5² : f̄ ∣ X^(ℓⁿ) − X)
example : zpxw 5 [2, 0, 1] (bitsOf 5 25) [1] = [0, 1] := by decide

-- X ^ 5 mod (X² + 2) = 4X over F₅  (so X⁵ − X ≢ 0; hand gcd = 1, the q = 2
-- coprimality condition)
example : zpxw 5 [2, 0, 1] (bitsOf 3 5) [1] = [0, 4] := by decide

/-! ### Real data: the charpoly of T₂ on S₇₂, reduced mod ℓ = 107

`charpoly = X⁶ − 66157336440·X⁵ − ⋯` (blueprint/exploration/data), ℓ = 107,
n = 6, e = ℓ⁶ = 1500730351849 (41 bits).  First Rabin condition:
X^e mod f̄ = X, i.e. f̄ ∣ X^(ℓⁿ) − X. -/
def f107 : List ℤ := [90, 23, 4, 83, 94, 8, 1]

set_option maxRecDepth 1000000 in
theorem rabin72_step1 : zpxw 107 f107 (bitsOf 41 1500730351849) [1] = [0, 1] := by
  decide

#print axioms rabin72_step1
