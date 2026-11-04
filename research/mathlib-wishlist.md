# Mathlib wishlist (maintained per research/mathlib-version-strategy.md)

Checked against the pin (`.lake/packages/mathlib` @ `v4.36.0-rc1`) and the
prospective mirror (`~/zcode-workdir/encore-mathlib/repo/mathlib4`, master)
at every iteration's recon step.  Status legend: **have** (at pin),
**master** (exists on master, arrives at the next bump), **wish** (neither
— candidate to contribute or route around).

| item | status | notes |
|---|---|---|
| Level-one Hecke operators `T_m` on cusp forms | have (ours) | `MathProof/ModularForms/HeckeTM.lean` — ours, not Mathlib's; a Mathlib PR is a separate decision |
| q-expansion injectivity for cusp forms | have (ours) | `HeckeCommute.qExpansion_coeff_ext`; Mathlib master recheck worthwhile |
| Lattice index = \|det base change\| | **have (pin)** | `Mathlib/LinearAlgebra/FreeModule/Finite/CardQuotient.lean` (`relIndex_eq_natAbs_det`, `relIndex_eq_abs_det`) — found by the iteration-24 concept pass after being suspected missing; TauCeti has a twin (`Submodule.IsLattice.relIndex_span_eq_abs_det_mul`) |
| Primitive Jordan / Wielandt 13.9 ((n−1)-cycle + transposition ⟹ Sₙ) | have (ours, weaker form) | `JordanPrimitive` — ours proves transitive+(n−1)-cycle ⟹ primitive + swap ⟹ Sₙ; a general Wielandt entry could still be upstreamed |
| Dedekind's theorem / Frobenius cycle type | have (ours) | `FrobeniusCycleType` (also present in TauCeti under cycle-type names — the iteration-22 lesson) |
| `exponentiation.threshold` configurability | wish | light modules cannot raise it; chunked-literal workarounds everywhere (AGENTS.md gotcha).  An upstream `set_option`-free norm_num path for `10 ^ 257` would delete real complexity |
| Faster `ZMod` polynomial arithmetic (kernel) | wish | Maeda/Rabin certificate costs are dominated by big `ZMod` muls in kernel `decide` |
| Smith normal form of integer matrices (computational) | wish (partial) | pin has `smithNormalFormCoeffs` (existence, FreeModule/PID) — noncomputational; a kernel-friendly SNF would formalize 𝕋/ℤ[T₂] structure directly (iteration-24 F1/F2 data) |
| Cyclic-group classification for quotient card divisibility | have (pin, pieces) | Lagrange + kernel-of-surjection route assembled in Iteration 24 b2 |

Update this file at every recon step; move items to **have** with the exact
file/lemma when they land (a "Mathlib lacks X" claim that would cost > 200
lines requires a concept-search pass first — RESEARCH-WORKFLOW §4b).
