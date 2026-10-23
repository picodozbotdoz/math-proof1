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

## Iteration 2 — Ramanujan's congruence `τ(n) ≡ σ₁₁(n) (mod 691)`

**Status: complete (theorem formalized end-to-end).  2026-10-23.**

### The problem

Ramanujan's congruence (1916): `τ(n) ≡ σ₁₁(n) (mod 691)` for all `n ≥ 1`,
where `σ₁₁(n) = Σ_{d|n} d¹¹`.  It is the prototypical congruence between
Fourier coefficients of a cusp form and a divisor sum, the starting point of
the theory of congruences for modular forms (Serre's `Λ`-adic families,
Hida theory).  It was **not formalized in Mathlib**; neither was any
identification of the algebraically-defined `τ` with the Fourier coefficients
of the analytic discriminant `Δ`.

### What this iteration contributes

1. **Ramanujan's weight-12 identity** (`MathProof/ModularForms/Weight12.lean`,
   `E12_rel`): `691 • E₁₂ = 441 • E₄³ + 250 • E₆²` in `M₁₂(SL(2, ℤ))`,
   proved via the Sturm bound (`sturm_bound_levelOne_nat`).  The coefficient
   formula `E12_qExpansion_coeff` (`(E₁₂)_n = (65520/691) σ₁₁(n)`) and the
   Bernoulli evaluations `B₄ = −1/30`, `B₆ = 1/42`, `B₁₂ = −691/2730`
   (computed by chaining the defining recurrence, since `decide` and
   `norm_num [bernoulli]` on the well-founded definition time out) are
   exported for reuse.

2. **The analytic-to-algebraic bridge** (`MathProof/Tau/Bridge.lean`):
   `(qExpansion 1 Δ).coeff n = τ(n)` for `n ≥ 1` (and `= 0` for `n = 0`),
   where `Δ` is *Mathlib's* modular discriminant (defined analytically
   through the Dedekind η product).  This makes Iteration 1's algebraic τ
   literally the sequence of Fourier coefficients of the analytic Δ.  Proof
   skeleton: a coefficient 1-norm on `ℤ[X]` with submultiplicativity (via a
   triangle-antidiagonal ≤ section-products inequality); the exponential
   bound `|τ(n)| ≤ 2^{24n}`; a quantitative estimate
   (`dist_poly_sum_le`) placing the `M`-th partial τ-sum within
   `2^{24M}‖z‖^{M+1}/(1−‖z‖)` of the `M`-th partial product of Δ's Euler
   product on `|z| < 1`; convergence of both to identify the series value
   on `2^{24}|z| < 1`; and uniqueness of power-series representations
   (`HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually`) to match
   Taylor coefficients at `0`.

3. **The congruence** (`MathProof/ModularForms/Congruence691.lean`,
   `tau_modEq_sigma`): `τ n ≡ σ₁₁(n) [ZMOD 691]` for all `n ≥ 1`.
   Ingredients: the coefficient forms of Ramanujan's identity and of
   **Jacobi's identity** `E₄³ − E₆² = 1728 Δ` (the latter derived from
   Mathlib's `discriminant_eq_E₄_cube_sub_E₆_sq`, transported to
   q-expansions and combined with the bridge), integrality of `(E₄³)ₙ`,
   `(E₆²)ₙ` (convolution of the integer sequences `240σ₃`, `−504σ₅`),
   elimination of the two integer unknowns, and cancellation of the
   prime-to-691 factor 125 (691's primality by kernel `decide`).

To our knowledge this is the first formalization of Ramanujan's 691
congruence in any proof assistant, and the first formal identification of
the Ramanujan τ numbers with the Fourier coefficients of Δ.

### What remains / next steps

* **Other classical congruences**: `τ(n) ≡ σ₁₁(n)` holds mod 691; the
  companion congruences mod 2 (`τ(n) ≡ σ₁₁(n) mod 2`) and mod 3 follow
  from the same weight-12 identities and would be easy additions.
* **Mordell multiplicativity** `τ(mn) = τ(m)τ(n)` for coprime `m, n` —
  the natural next theorem toward Lehmer's conjecture (Iteration 1).
* **Higher level**: congruences for coefficients of `Δ` mod other primes
  involve level-1 Hecke theory; the q-expansion infrastructure built here
  (form-level `qExpansion_smul/sub/add`, integrality lemmas) generalizes.
* **Lehmer's conjecture** (Iteration 1): the bridge now connects the
  kernel-verified nonvanishing bound `τ(n) ≠ 0, n ≤ 256` to the analytic
  Δ; raising the bound via reflected certificates remains open.
