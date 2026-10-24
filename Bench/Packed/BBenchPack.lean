/-!
# Probe: linear vs balanced packing, isolated single calls  (study artifact)

One `decide +kernel` per theorem, each forcing exactly one pack of
`countDown n` (entries `n % P, …, 1 % P`, ascending) reduced mod `P`:
linear `packAsc` vs balanced `packBal` at the same size, plus a linear point
at half size.  `% P` forces the whole packed bignum to a literal first.
-/

namespace BenchPack

private def P : Nat := 999999937
private def twoW : Nat := 1 <<< 80

private def packAsc : List Nat → Nat
  | [] => 0
  | c :: cs => c + twoW * packAsc cs

private def takeF : Nat → List Nat → List Nat
  | _, [] => []
  | 0, _ => []
  | k + 1, c :: cs => c :: takeF k cs

private def dropF : Nat → List Nat → List Nat
  | 0, l => l
  | _, [] => []
  | k + 1, _ :: cs => dropF k cs

private def packBal : Nat → List Nat → Nat
  | 0, _ => 0
  | F + 1, l =>
      let n := l.length
      if n ≤ 64 then
        packAsc l
      else
        let h := n / 2
        packBal F (takeF h l) + (1 <<< (80 * h)) * packBal F (dropF h l)

private def countDown : Nat → List Nat
  | 0 => []
  | n + 1 => (n % P) :: countDown n

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

example : packAsc (countDown 8192) % P = 637709074 := by decide +kernel

example : packAsc (countDown 16384) % P = 927105924 := by decide +kernel

example : packBal 64 (countDown 16384) % P = 927105924 := by decide +kernel

end BenchPack
