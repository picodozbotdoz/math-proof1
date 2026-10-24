import Mathlib.Tactic

/-!
# Bench: strict-forced list arithmetic at 1024  (scaling-study artifact)

Hypothesis under test (`docs/lehmer-mod-scaling-study.md`): the 71 GB kernel
heap of `MathProof/Tau/LehmerMod.lean` at `d = 1024` comes from the lazy kernel
evaluator retaining the whole Θ(d²) suspension DAG of the list computation
(nothing forces the intermediate lists until the final scan).  This file
re-runs the *identical* arithmetic with a `forceN` gate (`List.all` + `Nat.ble`
force every element to a literal) after every `Pbuild` step and every `pmulM`
of the 24th power, and checks whether the kernel heap stays flat at
`d = 1024`.

Benchmark only — soundness of the underlying arithmetic is already established
in `LehmerMod.lean`; the definitions here are verbatim copies.
-/

namespace BenchList

local notation "P" => 999999937

private def paddM : List ℕ → List ℕ → List ℕ
  | [], l => l
  | l, [] => l
  | a :: as, b :: bs => (a + b) :: paddM as bs

private def pscaleM (x : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: as => ((x * a) % P) :: pscaleM x as

private def pshiftM (l : List ℕ) : List ℕ := 0 :: l

private def psubM : List ℕ → List ℕ → List ℕ
  | [], l => List.map (fun b => (P - b % P) % P) l
  | a :: as, [] => a :: psubM as []
  | a :: as, b :: bs => ((a + (P - b % P)) % P) :: psubM as bs

private def pmulM : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: as, b => paddM (pscaleM a b) (pshiftM (pmulM as b))

private def shiftByM : ℕ → List ℕ → List ℕ
  | 0, l => l
  | m + 1, l => 0 :: shiftByM m l

/-- Force every element of the list to a literal: `List.all` short-circuits
through `Bool.and`, and `Nat.ble` is a kernel binary operation, so whnf-ing
the `if` descends into every element. -/
private def forceN (l : List ℕ) : List ℕ :=
  if l.all (fun x => Nat.ble (x % P) (P - 1)) then l else l

private def PbuildF (d : ℕ) : ℕ → List ℕ
  | 0 => List.take d [1]
  | N + 1 => forceN (List.take d (psubM (PbuildF d N) (shiftByM (N + 1) (PbuildF d N))))

private def pow24F (l : List ℕ) : List ℕ :=
  let s2 := forceN (pmulM l l)
  let s4 := forceN (pmulM s2 s2)
  let s8 := forceN (pmulM s4 s4)
  let s16 := forceN (pmulM s8 s8)
  forceN (pmulM s16 s8)

private def allNonzeroModLt : ℕ → List ℕ → Bool
  | 0, _ => true
  | d + 1, l => (l.getD d 0 % P != 0) && allNonzeroModLt d l

set_option maxRecDepth 1000000 -- kernel evaluation depth for the check below

/-- Same statement as `deltaCoeffsMod_1024_nonvanishing` would be, computed by
strict-forced list arithmetic. -/
theorem forced_1024 :
    allNonzeroModLt 1024 (List.take 1024 (pow24F (PbuildF 1024 1024))) = true := by
  decide +kernel

end BenchList
