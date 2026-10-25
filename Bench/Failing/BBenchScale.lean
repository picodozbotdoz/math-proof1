import Mathlib.Tactic

/-!
# Bench: unforced list arithmetic at 768  (scaling-study artifact)

One measurement point for the memory-scaling curve of the naive kernel
evaluation (`research/lehmer-mod-scaling-study.md`): 512 needs > 6 GB, 1024 was
observed at > 71 GB; this file measures 768 with the exact `LehmerMod`
definitions (verbatim copies) to pin down the growth exponent between the two.

Benchmark only — soundness of the arithmetic is already established in
`MathProof/Tau/LehmerMod.lean`.
-/

namespace BenchScale

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

private def PbuildM (d : ℕ) : ℕ → List ℕ
  | 0 => List.take d [1]
  | N + 1 => List.take d (psubM (PbuildM d N) (shiftByM (N + 1) (PbuildM d N)))

private def pow24M (l : List ℕ) : List ℕ :=
  let s2 := pmulM l l
  let s4 := pmulM s2 s2
  let s8 := pmulM s4 s4
  let s16 := pmulM s8 s8
  pmulM s16 s8

private def deltaCoeffsMod (d : ℕ) : List ℕ := List.take d (pow24M (PbuildM d d))

private def allNonzeroModLt : ℕ → List ℕ → Bool
  | 0, _ => true
  | d + 1, l => (l.getD d 0 % P != 0) && allNonzeroModLt d l

set_option maxRecDepth 1000000 -- kernel evaluation depth for the check below

/-- Scaling point between the 512 (> 6 GB) and 1024 (> 71 GB) observations. -/
theorem unforced_768 : allNonzeroModLt 768 (deltaCoeffsMod 768) = true := by
  decide +kernel

end BenchScale
