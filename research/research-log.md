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

* **Other classical congruences**: 691 is the only prime for which
  `τ(n) ≡ σ₁₁(n)` holds identically — the naive mod-2 and mod-3 companions
  are *false* (`τ(4) = −1472` is even while `σ₁₁(4) = 1 + 4¹¹` is odd;
  `τ(3) = 252 ≡ 0 [MOD 3]` while `σ₁₁(3) = 1 + 3¹¹ ≡ 1 [MOD 3]`).  The
  correct small-prime statements are the gap congruences of Iteration 4,
  which supersede this item.
* **Mordell multiplicativity** `τ(mn) = τ(m)τ(n)` for coprime `m, n` —
  the natural next theorem toward Lehmer's conjecture (Iteration 1).
* **Higher level**: congruences for coefficients of `Δ` mod other primes
  involve level-1 Hecke theory; the q-expansion infrastructure built here
  (form-level `qExpansion_smul/sub/add`, integrality lemmas) generalizes.
* **Lehmer's conjecture** (Iteration 1): the bridge connects the
  kernel-verified nonvanishing bound (see Iteration 3, now `n ≤ 512`) to
  the analytic Δ.

---

## Iteration 3 — Lehmer's conjecture: the verified bound raised 128 → 512 by mod-p arithmetic

**Status: complete; bound extended 256 → 512 after moving builds to Modal.
2026-10-24.**

### The problem

Iteration 1 verified `τ n ≠ 0` for `n ≤ 128` by kernel evaluation of the
integer coefficient list of `Δ = q ∏ (1 − q^m)^24`.  Over `ℤ`, the
intermediates grow to the true values of `τ` (≈ n^6), and the kernel's
per-operation overhead makes the cost of `decide` grow quadratically with
the bound; pushing much past 128 exhausted a 7 GB machine.

### What this iteration contributes

`MathProof/Tau/LehmerMod.lean`: the same kernel-friendly list arithmetic
performed **modulo the word-sized prime** `P = 999999937` (`paddM`, `psubM`,
`pmulM`, `pow24M`, `deltaCoeffsMod`), every operation reduced below `2^62`
so intermediates never grow.  Soundness (`deltaCoeffsMod_eq`) is proved by
transporting the computation into `(ZMod P)[X]` (the mirror `L2PMod` of
Iteration 1's `L2P`), and `tauOf_ne_zero_of_mod` formalizes the certificate
principle: *a nonzero residue mod a prime certifies the integer coefficient
is nonzero* — no magnitude bound on `τ` is needed.

* `deltaCoeffsMod_512_nonvanishing`, checked by `decide +kernel` (the
  kernel-only variant: the default elaborator-side re-evaluation of `decide`
  degrades pathologically under GC pressure at this size).  Smaller bounds
  (16 / 256) are kept as fast smoke checks and derived consequences.
* `tau_ne_zero_of_le_512` / `tau_prime_ne_zero_of_le_512` (the first 97
  primes): the formally verified nonvanishing bound for `τ` is now **512**,
  a 4× improvement over Iteration 1's integer-arithmetic bound of 128.

### Resource history (why the bound moved)

* 128 over `ℤ` (Iteration 1): local machine, ~2 CPU-min kernel time.
* 256 mod `P` (this iteration, local): a 512 attempt died there — the
  kernel evaluation holds a heap of shared subterms growing superquadratically
  in the bound, and a 7 GB machine collapses into GC thrash around 6 GB.
* 512 (~5 min) on a 4-core / 32 GiB Modal container: same code, no changes —
  only the execution environment moved.
* 1024 was attempted and **abandoned with a measurement**: the kernel heap
  exceeded 71 GB (>2× the container budget), and the run was preempted.
  The naive kernel evaluation therefore tops out at 512 on a 32 GiB budget.
* `tau_ne_zero_of_le_256` (local run) was confirmed by `#print axioms` to
  depend on `[propext]` alone.

### What remains / next steps

* The next hard wall is time/memory of the naive kernel evaluation
  (~quadratic in the bound).  A reflected certificate scheme (check
  convolution identities inside the kernel instead of recomputing them)
  is the route to 10^4+; the Modal image removes the memory constraint but
  not the asymptotics.
* Literature computational bounds are far beyond 10^10 (unverified);
  formal verification at that scale needs the certificate approach.

---

## Iteration 4 — Congruence restrictions on τ modulo 2 and 3

**Status: complete.  2026-10-24.**

### The problem

Ramanujan's congruence describes `τ` mod 691 (Iteration 2).  Modulo the
*small* primes the structure is different and elementary in one direction:
mod 2, `(1 − T)^24 = ((1 − T)^8)^3 = (1 − T^8)^3` (freshman's dream), so
`Δ` reduces to a power series in `q^8`; mod 3 likewise to `q^3`.  These
"gap" congruences were not in Mathlib.

### What this iteration contributes

`MathProof/Tau/CongruenceSmall.lean`, all proofs synthetic (no computation):

* `one_sub_pow_eight` / `one_sub_pow_three`: the freshman's dream via the
  iterated Frobenius homomorphism (`iterateFrobenius_def` is `rfl`),
  characteristic 2 resp. 3.
* A support lemma (`coeff_prod_one_sub_pow_eq_zero`): products of powers
  `(1 − X^(c·m))^r` have no coefficients at indices not divisible by `c`.
* The reductions of the truncated Euler product mod 2 and mod 3
  (`map_etaPow24_mod_two/three`) and the shared transport
  (`tau_dvd_of_coeff_map_eq_zero`) giving:
  * **`tau_even_of_ne_one_mod_eight`**: `τ n` is even unless `n ≡ 1 [MOD 8]`;
  * **`tau_zero_mod_three_of_ne_one_mod_three`**: `3 ∣ τ n` unless `n ≡ 1 [MOD 3]`;
  * `tau_div_two_and_three_of`: both at once (hence `6 ∣ τ n` off the two
    exceptional classes, since 2 and 3 are coprime).

### What remains / next steps

* The full parity characterization "`τ n` odd ⟺ `n` is an odd square" needs
  Jacobi's two-square/triple-product identity
  `∏ (1 − q^m)^3 = Σ (2k+1) q^{k(k+1)/2}` — the natural next formalization
  target (Mathlib's 2025 pentagonal-number-theorem machinery is the model).
* These congruences give the density-zero obstruction inputs for Lehmer's
  conjecture searches (most residue classes mod 24 are forced divisible by 2
  or 3, but divisibility does not force vanishing — they are search filters,
  not nonvanishing evidence).

---

## Iteration 5 (study) — Why LehmerMod dies at 1024, and the packed-bignum route to 65536

**Status: study + kernel benchmarks complete; no new theorems landed yet.
2026-10-24.**  Full write-up: `research/lehmer-mod-scaling-study.md`.

### The problem

Iteration 3's kernel-verified nonvanishing bound (`τ n ≠ 0` for `n ≤ 512`,
`decide +kernel` on mod-`P` list arithmetic) could not be pushed to 1024: the
kernel heap exceeded 71 GB on a 32 GiB container.  This iteration measured
*why*, evaluated the externally suggested fixes, benchmarked two alternatives,
and specified the next iteration's design.

### What this iteration contributes

* **Build telemetry** for the Modal scripts (`lean_check.py`, `lean_build.py`):
  live `[telemetry]` peak-RSS/CPU milestones and a final summary for the `lake`
  process tree (std-lib-only; no Modal resources added; image untouched).
  Also: `--file X.lean` now builds module `X` (previously it silently built the
  default target).
* **Root cause, measured** (2 CPU / 32 GiB-request containers):
  * 512 (current code): **24.1 GiB peak**, 186 s module build — already at 75 %
    of budget.
  * 768 (unforced): dead at **> 39.5 GiB / > 363 s** with `(kernel)
    deterministic timeout`.
  * 1024 with strict-forcing gates: dead at **> 34.6 GiB / > 305 s** — forcing
    helps ~2–3× relatively but cannot rescue the list representation: the
    kernel's lazy evaluator retains every unevaluated suspension (a
    constant-live-set probe, `BBenchBurn.lean`, confirmed RSS ∝ total
    reduction steps — ~0.6–4 KB/step — released only at declaration
    boundaries), and multi-minute `decide +kernel`s additionally hit the
    default `maxHeartbeats` kernel cap (200000 ≈ 200 s; `Lean/CoreM.lean`,
    `addDeclCore`).
* **Verdicts on the external commentary**: `native_decide` rejected (project
  rule, and unnecessary); truncation/tail-recursion ineffective (lazy kernel —
  it's retention, not stack); `UInt64` misdiagnosed (kernel fast path is
  GMP-`Nat`, values already single-limb); external poly libs moot.  One more
  negative result: **point-evaluation certificates are unsound** for truncated
  series identities (evaluation aliases coefficients mod d; would certify
  `Σ_k f_{i+kd}`, not `f_i`).
* **The fix, benchmarked**: *packed-bignum arithmetic* — one `Nat` per
  coefficient list in base `2^80`, one GMP `Nat.mul` per dense convolution,
  η's entry list from Euler's pentagonal number theorem (in Mathlib,
  coefficient-wise).  v1 (linear pack/unpack) verified **1024 + 4096 + 16384
  in 174 s** of kernel time, peak 41.3 GiB (soft-cap overage; linear
  recursions still retain Θ(d²) bits).  v2 (balanced-tree pack/unpack,
  `BBenchPackedBal.lean`; isolated packing is 3.4× lighter at 16384 — 1.0 GiB
  vs 3.4 GiB, `BBenchPack.lean`) verified **16384 + 65536 in 662 s**, peak
  60.1 GiB: 65536 is kernel-verifiable but needs > 64 GiB; the landable bound
  on the current 32 GiB budget is **16384** (a 32× improvement over 512).
* **Certificate data**: `tools/gen_packed_bench.py` (dependency-free numpy,
  exact 15-bit-split convolutions) generates the η residues and cross-checks
  τ against the 21 kernel-verified values of `Basic.lean`; it audits that all
  τ residues mod `P` are nonzero through **n = 65536** — the bound the next
  iteration can certify.

### What remains / next steps

* Formalize `MathProof/Tau/LehmerPacked.lean` per study §6: packing lemmas
  (digits of a product = convolutions, slot bound 2^76 < 2^80), balanced
  pack/unpack correctness (fuel induction), pentagonal entry list via
  `Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries`, transport into
  `ZMod P` mirroring `L2PMod`, and `tau_ne_zero_of_le_65536` (or 16384 first).
  All elementary; no analysis.
* Housekeeping: lift `maxHeartbeats` in any file with multi-minute kernel
  decides; keep `LehmerMod.lean` (512) as the CI smoke check.

## Iteration 6 — Lehmer's conjecture: the verified bound raised 512 → 65536 by packed-bignum kernel arithmetic

**Status: complete. 2026-10-24.**  Implements the route specified by the
Iteration 5 study (§6); development notes in `research/lehmerpacked-plan.md`.

### What this iteration contributes

* `MathProof/Tau/LehmerPacked.lean` — **`Ramanujan.tau_ne_zero_of_le_65536`**:
  `τ n ≠ 0` for all `1 ≤ n ≤ 65536`, verified entirely inside Lean's kernel
  (`decide +kernel`; no `native_decide`, no external CAS).  A 128× improvement
  over Iteration 3's bound of 512, and the first bound past the naive mod-P
  list-arithmetic wall (>71 GiB at 1024).  (The 16384 intermediate
  `tau_ne_zero_of_le_16384` is landed alongside.)
* The packed-bignum pipeline, fully proved:
  * `etaList d` — the coefficients of `∏ (1 - X ^ m)` mod `P`, computed
    coefficient-wise from Euler's pentagonal number theorem: each entry is
    decided by the square test `24 i + 1 = (6 k ∓ 1)²` using `isqrtNew`, a
    *structurally recursive* Newton integer square root (the core `Nat.sqrt`
    is well-founded and not kernel-reducible).  Soundness `pentRes_eq`: each
    entry is the reduction of `(pentagonalSeries ℤ).coeff i` (Mathlib's
    pentagonal number theorem), via `pentRes_of_pent` (pentagonal indices give
    ±1 with the parity of `k`) and `pentRes_zero_of_not` (non-square gives 0).
  * packing (`packAsc`/`packBal`, `digitsLin`/`digitsBal` — balanced trees,
    fuel-structural so the kernel can reduce them): every dense
    multiplication is one GMP-backed `Nat.mul` plus O(d) digit extractions.
    `packedMul_getD`: the digits of the packed product are the convolution
    slots, given the slot bound `d · (P - 1)² < 2^76 < 2^80` (`convSum_lt`);
    supporting lemmas `digit_extract`, `mod_mul_div`, `packBal_eq`,
    `packAsc_convL`, `digitsLin_split`.
  * the bridge: `etaPoly_coeff_pent` — the low coefficients of the truncated
    Euler product `etaPoly N` are the pentagonal-series coefficients
    (extracted from `PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq` via
    `Filter.eventually_atTop` on `Finset ℕ`); `deltaPacked_eq` transports the
    24th-power chain into `ZMod P` against `(etaPoly d) ^ 24`; and
    `tauOf_ne_zero_of_packed`: a nonzero residue mod the prime `P` certifies
    `tauOf i ≠ 0`.
* Engineering notes for future kernel-decide work (all confirmed the hard
  way): `beq_iff_eq` turns the `==`-tests of kernel-decidable branch trees
  into `=`-conditions; `omega` treats only *plain* atom products as linear —
  nested-nonlinear (`g * (2*s - g)`) and variable-divisor (`n / g`)
  hypotheses are opaque, so restructure via explicit div/mod lemmas;
  `Nat.pow_succ` in this toolchain orients as `a^(n+1) = a^n * a` (watch
  multiplication-order atoms); equation lemmas are only usable when match
  patterns don't overlap (`takeF`, `convL` pattern orders matter).

### Results

* Modal kernel decides, measured: 512+16384 module build = **149 s wall,
  17.46 GiB peak tree RSS** (4 CPU / 32 GiB-request); adding the 65536
  decide = **570 s wall, 62.85 GiB peak** (2 CPU / 96 GiB-request via the
  new `LEAN_CHECK_MEMORY_MIB` override in `lean_check.py`) — the packed
  pipeline scales where the naive list arithmetic was already at 24 GiB for
  512 alone.
* Local (7 GiB machine): the whole file minus the 16384 decide elaborates and
  kernel-checks (the 512 decide included) in a few minutes.
* The module joins `LehmerMod` outside the CI target list (kernel decides
  need more RAM than a GitHub runner offers); it is verified on Modal via
  `lean_check.py --file MathProof/Tau/LehmerPacked.lean`.

### What remains / next steps

* Past 65536: the slot base `2^80` saturates (`convSum_lt` is stated exactly
  for `length ≤ 65536`); the next doubling needs wider slots (the digit-bound
  lemma is parametric) or a two-level packing — plus ~128 GiB containers.
* Lehmer's conjecture itself remains open (no zero of τ is known at any
  index); literature verifications go far past 65536, but they trust CAS
  output — the point of this stack is that every step is checked by Lean's
  kernel alone.
