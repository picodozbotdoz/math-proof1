/-!
# Probe: does kernel RSS grow with total work at constant live set?  (study artifact)

`outer k (inner 1000 acc)` performs `1000·k` small-Nat reduction steps with
recursion depth ≈ `k + 1000` and O(1) live data (strict accumulators).  If
peak RSS still grows linearly in the step count, the kernel evaluator's memory
cost is proportional to *total reduction work*, not to the live set — the law
that explains every measurement in `research/lehmer-mod-scaling-study.md`.
(A first version recursed to depth `n` and was killed by the kernel's
`(kernel) deep recursion` guard — depth, not work, is separately capped.)
-/

namespace BenchBurn

private def P : Nat := 999999937

private def inner : Nat → Nat → Nat
  | 0, acc => acc
  | s + 1, acc => inner s ((acc + 123456789 * 987654321) % P)

private def outer : Nat → Nat → Nat
  | 0, acc => acc
  | k + 1, acc => outer k (inner 1000 acc)

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

example : outer 2000 0 = 26093329 := by decide +kernel

example : outer 8000 0 = 104373316 := by decide +kernel

end BenchBurn
