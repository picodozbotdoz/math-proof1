# Research log — modular forms open problems

This repository is the working log of an autonomous research loop on open
problems connected to the Langlands program, using Lean 4 + Mathlib.  Each
iteration picks one open problem, makes a concrete *verifiable* contribution
(theorems formalized in Lean, kernel-verified computations, or both), and
records what was achieved and what remains.

---

## Iteration 1 — Lehmer's conjecture (non-vanishing of the Ramanujan τ function)

**Status: partial result formalized.  2026-10-23.**

### The problem

**Lehmer's conjecture (1947).** The Ramanujan tau function `τ : ℕ → ℤ`, defined
by

    q ∏_{m ≥ 1} (1 - q^m)^24 = Σ_{n ≥ 1} τ(n) q^n,
    τ(1), τ(2), … = 1, −24, 252, −1472, 4830, −6048, … (OEIS A000594)

never vanishes: `τ(n) ≠ 0` for every `n ≥ 1`.  It is one of the oldest open
problems in the arithmetic theory of modular forms (`τ` is the Fourier
coefficient sequence of the weight-12 cusp form `Δ` for `SL(2, ℤ)`).

### State of the art (literature)

* D. H. Lehmer (1947) verified `τ(n) ≠ 0` for small `n` and posed the conjecture.
* Computer-assisted searches over the decades have never produced a zero;
  non-vanishing has been verified in the literature up to very large bounds
  (well beyond `10^9`, by computations outside any proof assistant).
* On the theoretical side, Serre showed (assuming the Sato–Tate conjecture,
  which is now a theorem) that `{n : τ(n) = 0}` has natural density `0`;
  nevertheless not a single zero is known to be impossible beyond computation,
  and the conjecture itself is wide open.

### What this iteration contributes

A formally verified treatment of `τ` in Lean 4 / Mathlib
(`MathProof/Tau/Basic.lean`, `MathProof/Tau/Lehmer.lean`):

1. **A rigorous algebraic definition of `τ`** (`Ramanujan.tau`): the coefficient
   of `X^i` in `(∏_{m ≤ i+1} (1 − X^m))^24 ∈ ℤ[X]`, with the truncation-stability
   theorem `etaPow24_stable` proving that low coefficients do not depend on the
   truncation point of the infinite product.  To our knowledge this is the first
   formalization of the Ramanujan tau function in Lean 4 / Mathlib (Mathlib has
   the analytic discriminant `Δ = η^24` with its q-expansion product formula, but
   no arithmetic theory of its coefficients).

2. **A verified-computation bridge** (`tauOf_eq_getD`): a hand-rolled,
   kernel-friendly coefficient-list arithmetic (`psub`, `shiftBy`, `pmul`,
   binary-exponentiation `pow24`) whose correctness is *proved*
   (`deltaCoeffs_getD`), so that `τ` can be evaluated by Lean's kernel alone.
   A key engineering point: naive structural definitions can silently compile
   to well-founded recursion (`Acc.rec`), which the kernel cannot reduce — all
   list functions here are structured to remain kernel-reducible.

3. **Kernel-verified values**: `τ(1) = 1, τ(2) = −24, …, τ(21) = −4219488`,
   each proved equal to the OEIS A000594 value by `decide` (`tau_one` …
   `tau_twenty_one`) — an independent confirmation, inside the proof checker,
   of the classical values.

4. **A verified non-vanishing bound** toward Lehmer's conjecture:
   `tau_ne_zero_of_le_256 : 1 ≤ n ≤ 256 → τ n ≠ 0`, with the kernel-level
   computation `deltaCoeffs_256_nonvanishing` checked by `decide` (no external
   CAS, no compiler-trusting `native_decide`, no unproved `sorry`).  In
   particular `τ(p) ≠ 0` for the first 54 primes (`tau_prime_ne_zero_of_le_256`).
   The literature's computational bounds are far larger, but they are not
   machine-checked; to our knowledge this is the first formally verified
   non-vanishing statement for `τ`.

### What remains / next steps

* **Raise the bound.**  The current bottleneck is kernel evaluation speed
  (~2 CPU-minutes for 256 coefficients).  A reflected verification scheme
  (compute with compiled code, check a certificate — e.g. the defining
  convolution identities — inside the kernel) could push the verified bound to
  `10^4`–`10^6` at negligible kernel cost.
* **Bridge to Mathlib's analytic Δ** (`ModularForm.discriminant`): prove that
  the partial sums `Σ_{n ≤ N} τ(n) e^{2πi n z}` converge to `Δ(z)`, making the
  formal coefficients literally *the* Fourier coefficients of Mathlib's
  discriminant.  The estimate needed is that a geometric tail dominates the
  polynomial growth of truncated-product coefficients.
* **Multiplicativity (Mordell 1917).** `τ(mn) = τ(m)τ(n)` for coprime `m, n`,
  and `τ(p^{r+1}) = τ(p)τ(p^r) − p^{11} τ(p^{r-1})`.  This requires Hecke
  operators acting on q-expansions; would also immediately give the structure
  of the non-vanishing problem for prime powers.
* **Ramanujan congruences** (see Iteration 2 below for the 691 congruence).

---

## Iteration 2 — (in progress)

Candidate: the **Ramanujan congruence `τ(n) ≡ σ₁₁(n) (mod 691)`** — a *theorem*,
not an open problem, but unformalized in Mathlib; proving it rigorously
requires exactly the Eisenstein-series / dimension-formula / Sturm-bound
machinery that Mathlib now has, and is the natural next building block toward
open congruence questions for `τ` (e.g. distribution of `τ(n) mod m`).
