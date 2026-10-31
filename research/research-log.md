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

## Iteration 7 — Hecke operators on S₁₂(SL(2, ℤ)) and Mordell's theorem

**Status: complete (theorem formalized end-to-end).  2026-10-26.**
HeckeLevelOne parts 1–3 (this iteration's operator-level groundwork) landed in
three earlier commits; this entry records the iteration as a whole, completed
by `MathProof/Tau/Mordell.lean`.

### The problem

Mordell's theorem (1917): the Ramanujan τ function is multiplicative on
coprime arguments, `τ(mn) = τ(m)τ(n)` whenever `gcd(m, n) = 1`, together with
the prime-power recursion `τ(p^{r+2}) = τ(p)·τ(p^{r+1}) − p^11·τ(p^r)`.  It is
the structural backbone behind every statistical statement about τ (Lehmer's
conjecture reduces to prime powers once it is in hand), and its proof — the
Hecke operator T_p acting on the one-dimensional space S₁₂(SL(2, ℤ)) — is the
embodiment of the Langlands philosophy in its simplest instance: *eigenvalues
of an operator = arithmetic of coefficients*.

### What this iteration contributes

* `MathProof/ModularForms/HeckeLevelOne.lean` — the Hecke operator `T_p` at
  level one, from scratch on top of Mathlib's `CuspForm` API:
  * `heckeTPFun` on functions: `T_p f = p^{-1} Σ_{j<p} f((τ+j)/p) + p^{k-1} f(pτ)`;
    T-invariance by a summation-periodicity argument, S-invariance via an
    explicit coset factorization `σ_j = T^{j'} S T^{j''} ... ` built on the
    `ZMod p` involution `phiInv p j = (p - j⁻¹) % p` (Euler's theorem in
    `ZMod p`), holomorphy and vanishing at the cusps transported through the
    `shiftDivP`/`mulP` maps.
  * `heckeTP hp f : CuspForm 𝒮ℒ k` — the bundled operator, and
    `heckeTP_qExpansion_coeff`: the coefficient formula
    `(T_p f)_m = f_{pm} + p^{k-1} [p ∣ m] f_{m/p}`, proved by HasSum
    uniqueness (root-of-unity filter `Σ_j ζ^{jn} = p·[p ∣ n]`).
* `MathProof/Tau/Mordell.lean` — the payoff:
  * `heckeTP_discriminant_eq`: the **eigenform equation** `T_p Δ = τ(p) · Δ`
    (one-dimensionality of `S₁₂` from Mathlib's dimension formula + the
    Iteration-2 coefficient bridge identifying the eigenvalue as `τ p`);
  * `hecke_eigen_identity`: `τ(pm) + p^11 [p ∣ m] τ(m/p) = τ(p) τ(m)`;
  * `tau_prime_mul_of_not_dvd`, `tau_prime_pow_succ`, `tau_prime_pow_mul`;
  * **`tau_mul_coprime`: `τ(mn) = τ(m)τ(n)` for coprime `m, n ≥ 1`**
    (strong induction on `m`, peeling the smallest prime factor via
    `m.minFac` and a verified `q^a ∥ m` decomposition).
  All theorems rest only on `propext, Classical.choice, Quot.sound`
    (audited with `#print axioms`), no `sorry`, no `native_decide`.

### Engineering notes (for future operator-level work)

* For bundled `CuspForm`s, `qExpansion 1 f` elaborates through the `⇑`
  coercion: coefficient-level rewriting must first push the coercion through
  the scalar (`FunLike.coe_smul : ⇑(c • f) = c • ⇑f`) before
  `ModularForm.qExpansion_smul` can fire — the smul patterns
  `⇑(c • f)` vs `c • ⇑f` are not interchangeable.
* Mathlib's coefficient formula writes the exponent as `(12 - 1 : ℤ)` — a
  *zpow*; normalizing to `(p : ℂ) ^ 11` needs
  `rw [(show (12 - 1 : ℤ) = ((11 : ℕ) : ℤ) from rfl), zpow_natCast]` (the
  `rfl` re-expresses the `OfNat` literal as a `Nat.cast` so `zpow_natCast`
  can match syntactically).
* This toolchain's arithmetic API: `dvd_pow_self` now requires `n ≠ 0`;
  `Nat.mul_div_cancel' (h : n ∣ m) : n * (m / n) = m` (multiplier first);
  `Nat.one_lt_pow (h : n ≠ 0) (h' : 1 < a) : 1 < a ^ n`; `Nat.eq_one_or_pos`
  does not exist (split with two `rcases` instead).  `if_pos`/`if_neg` are
  deprecated in favor of `ite_eq_left/right` but still function.
* Iteration-7's HeckeLevelOne commits had never been **pushed**, so
  `lean_check.py` fresh clones lacked them ("bad import"); pushing is part
  of every milestone now.

### Results

* Local (this 7 GB machine): HeckeLevelOne elaborates in ~90 s, Mordell in
  ~35 s; whole light target builds clean.
* Modal (`lean_check.py`, fresh clone): verified after push.
* CI list extended: `MathProof.ModularForms.HeckeLevelOne`,
  `MathProof.Tau.Mordell` join the default (light) targets and the root
  `MathProof.lean`.

### What remains / next steps

* **Lehmer's conjecture** now reduces, via Mordell + the prime-power
  recursion, to `τ(p^a) ≠ 0` for prime powers — connecting Iterations 6 and 7
  (e.g. a certified nonvanishing bound over prime-power indices only).
* Deligne's bound |τ(p)| ≤ 2p^{11/2} (Ramanujan conjecture) — the natural
  next structural theorem; needs more analytic machinery (trace formula or
  ℓ-adic input is out of reach, but the weight-12 Sturm-bound machinery of
  Iteration 2 + eigenform identities give cheap numerical verifications
  `|τ(p)| ≤ 2p^{5.5}` for small p).
* Congruence properties of Hecke eigenvalues modulo primes (level-one
  Hecke theory is now available in-repo for this).

## Iteration 8 — Lehmer's conjecture on an unbounded index set: Mordell breaks the 65536 wall

**Status: complete (theorems formalized end-to-end).  2026-10-26.**

### The problem

Iteration 6 ended at a hard ceiling: kernel-verified `τ n ≠ 0` for `n ≤ 65536`,
with no path upward (the packed slot base `2^80` saturates; the 65536 decide
already costs ~63 GiB of kernel heap / 570 s).  Every past-the-wall statement
seemed to need bigger kernel computes.  The observation this iteration
formalizes: **Mordell's theorem (Iteration 7) makes the wall irrelevant**.
Nonvanishing of τ is multiplicative over coprime factors, so the finite set
of kernel-verified values certifies `τ n ≠ 0` on the entire multiplicative
semigroup generated by the verified prime powers — an infinite, unbounded
family of indices.

### What this iteration contributes

* `MathProof/Tau/LehmerUnbounded.lean` (light, in CI):
  **`tau_ne_zero_of_forall_prime_pow`** — parametric in a nonvanishing
  bound `B`: if `τ m ≠ 0` for all `1 ≤ m ≤ B` (by any verification route),
  then `τ n ≠ 0` for every `n ≥ 1` whose every prime-power divisor `p ^ a`
  (`p` prime, `a ≥ 1`) satisfies `p ^ a ≤ B`.  Proof: strong induction on
  `n`, peeling the minimal prime factor via `exists_prime_pow_decomp`
  (exported from Iteration 7) and applying `tau_prime_pow_mul`.
* `MathProof/Tau/LehmerPrimePower.lean` (heavy, verified on Modal like
  `LehmerPacked`): the one-line instantiation at `B = 65536` —
  `tau_ne_zero_of_prime_pow_le_65536` — plus the first concrete index past
  the wall: **`tau_of_65519_mul_65521_ne_zero : τ 4292870399 ≠ 0`**, where
  `4292870399 = 65519 · 65521` is 65 000 beyond the old bound, unreachable
  by direct kernel computation at this slot base.

### Results

* The certified nonvanishing set now includes all squarefree products of the
  6542 primes up to 65536 — indices of up to **28 305 decimal digits** (the
  primorial) — plus every `n` built from prime-power blocks `≤ 65536`.  This
  is a *qualitative* change: from a finite initial segment to an infinite
  multiplicative family, at zero additional kernel cost.
* Lehmer's conjecture is thereby reduced, inside the verified stack, to the
  *prime-power indices alone*: `τ(p ^ a) ≠ 0` for `p ^ a > 65536` is all
  that remains uncovered.

### What remains / next steps

* Push the *prime-power* frontier: the recursion `τ(p^{r+2}) = τ(p)·τ(p^{r+1})
  − p^11·τ(p^r)` (Iteration 7) computes `τ(p^a)` for `p^a` far past 65536 at
  small prime `p` cheaply — e.g. `τ(2^a)` for `a ≤ 30`-plus via one
  `LinCong`-style mod-P verification of the recursion chain (2-adic size
  growth `2^{11a}` stays single-limb-ish mod P).  This would extend the
  covered set to all `2^a · (coprime verified part)` with `2^a ≤ 2^{30}`.
* Deligne's bound `|τ(p)| ≤ 2 p^{11/2}` for verified small `p` (numerical,
  via the eigenvalue identity and kernel decides on the packed pipeline).

## Iteration 9 — Prime-power chains: the Lehmer frontier moves from 65536 to 2³²

**Status: complete (theorems formalized end-to-end, kernel decides on Modal).  2026-10-26.**

### The problem

After Iteration 8, the nonvanishing set was "all `n` whose prime-power divisors
are `≤ 65536`" — prime-power *values* above 65536 remained uncovered, and no
dense kernel computation can reach them (slot saturation, ~63 GiB already at
65536).  But Iteration 7's prime-power recursion
`τ(p^{r+2}) = τ(p)·τ(p^{r+1}) − p^11·τ(p^r)` is a *linear two-term recurrence*:
once the seeds `τ p mod P` are known, each `τ(p^a)` costs O(1) state per step —
a chain, not a convolution.

### What this iteration contributes

* `MathProof/Tau/PowChain.lean` (light, in CI) — the chain machinery:
  * `ppowAt` (chain value, structural recursion) and `ppowAux` (linear
    kernel-time runner, O(1) state);
  * `ppowAt_eq_tau`: chain soundness — for `p` prime, the chain seeded at
    `τ p` with coefficient `p^11` computes `τ (p ^ a)` in `ZMod P` for every
    `a` (by `tau_prime_pow_succ`);
  * `ppowOK_iff` / `chainsOK_iff`: the runner and the bulk walker are correct;
  * `tau_prime_pow_ne_zero_of_chains`: the parametric nonvanishing theorem
    (seed list + bridge + chain check as hypotheses).
* `MathProof/Tau/LehmerPacked.lean` (+ public accessor): `tauResList d` — the
  packed residue list as public API — and `tauResList_eq_tauZMod`: entry `i`
  is `τ (i+1)` mod `P` (the seed datum).
* `MathProof/Tau/LehmerUnbounded.lean` (refactor): the new primitive
  `tau_ne_zero_of_prime_pows` — `τ n ≠ 0` if `τ (p^a) ≠ 0` for every
  prime-power *divisor* of `n` (no explicit bound parameter needed);
  `tau_ne_zero_of_forall_prime_pow` becomes a corollary.
* `MathProof/Tau/LehmerPow32.lean` (heavy, verified on Modal like
  `LehmerPacked`, measured **2089 s wall / 143.8 GiB peak tree RSS** — the
  chain fold retains the live packed list plus per-step thunks, ~2× the
  packed evaluation alone): `chains_nonvanishing_65536` — ONE kernel decide
  walking all 65 535 chains (seeds `τ m`, `m = 2..65536`) of 32 steps each, ~2.1 M small
  `ZMod` operations (~3 ms per chain measured locally) on top of the
  packed-list evaluation — and the theorems:
  * `tau_prime_pow_ne_zero_of_le_two_pow_32`: `τ (p^a) ≠ 0` for every prime
    `p ≤ 65536` with `p^a ≤ 2^32`;
  * `tau_ne_zero_of_prime_pow_le_two_pow_32`: `τ n ≠ 0` for every `n` whose
    prime-power divisors all satisfy those bounds — in particular **every
    65536-smooth `n ≤ 2^32`** (4 294 967 296);
  * concrete: `tau_of_131072_ne_zero` (`τ(2^17)`, first power of two past the
    old wall), `tau_of_two_pow_32_ne_zero` (`τ 4294967296 ≠ 0`).

### Results

* The **prime-power frontier** moves 65536 → 2^32 (a factor of 65 536) at a
  kernel cost of ~2.1 M O(1) `ZMod` operations (2089 s / 143.8 GiB measured,
  incl. the seed-list evaluation) — versus ~dense-coefficient
  work that is provably out of reach at this slot base.  Lehmer's conjecture
  is now verified (kernel-only) for: all `n ≤ 65536` (Iteration 6), all
  coprime-composites of verified blocks (Iteration 8), and all prime-power
  blocks `p^a ≤ 2^32` with `p ≤ 65536` (this iteration).
* Combined statement: `τ n ≠ 0` for every `n ≥ 1` whose every prime-power
  divisor `p^a` has `p ≤ 65536` and `p^a ≤ 2^32` — e.g. `n = 2^32`, `3^20`,
  any 65536-smooth number below `2^32`, or any product of such blocks with
  pairwise-coprime parts.

### Engineering notes

* Lean 4 offset arithmetic: `m + 1 + i` and `m + (i + 1)` are **not**
  definitionally equal (nor `rfl`-provable) — every such transfer needs an
  explicit `omega`-rewrite; relying on defeq sends the elaborator into a
  whnf spiral that survives even `maxHeartbeats 1000000`.  (`i + 1 + 1 = i + 2`
  on the other hand *is* handled by rw's closing rfl.)
* `decide +kernel` (kernel-side evaluation) is ~100× faster than elaborator
  `decide` for `ZMod` chains — a 32-step chain costs ~3 ms kernel time; the
  elaborator variant is unusable at this scale.
* Composite-seed chains are mathematically garbage (the recursion is valid
  only for prime `p`) but **numerically harmless**: a Python audit over all
  65 535 seeds × 32 steps found zero residues hitting 0 mod P, so the
  all-seeds decide passes; soundness only ever consumes the prime seeds.

### What remains / next steps

* The uncovered set is now exactly: primes `p ∈ (65536, ∞)` with `p ∣ n`, and
  prime powers `p^a > 2^32`.  For the former, no seed exists — extending needs
  either a wider dense computation (different prime `P`, two-level packing) or
  an analytic route (Deligne's bound would give |τ(p)| ≥ 1 trivially but needs
  the Ramanujan conjecture machinery).
* Deligne verification for small `p`: the eigenvalue identity plus the packed
  residues give `|τ(p)| mod P` for `p ≤ 65536` — a numeric audit of
  `2 p^{11/2}` against reconstructed `|τ(p)|` is a light-verification
  candidate (needs exact reconstruction, i.e. magnitude bounds — a Sturm-type
  bound on |τ| could make this formal).

## Iteration 10 — The mod-691 Lehmer sieve: unbounded primes, necessary conditions

**Status: complete (light theorems, kernel-decided finite facts, CI).  2026-10-26.**

### The problem

After Iterations 6–9, the nonvanishing set covers: all `n ≤ 65536` (dense),
all coprime composites of verified blocks (Mordell), and all prime-power
blocks `p^a ≤ 2^32` with `p ≤ 65536` (chains).  The one structural hole:
**primes `p > 65536`** — no seed exists for them anywhere in the stack.  The
observation: Ramanujan's congruence `τ n ≡ σ₁₁ n [ZMOD 691]` (Iteration 2)
is itself a nonvanishing certificate — `691 ∤ σ₁₁ n` forces `τ n ≠ 0` —
and σ₁₁ is *multiplicative*, so the test is a sieve that runs on residue
classes, with no bound on `n` at all.

### What this iteration contributes

* `MathProof/Tau/LehmerSieve691.lean` (light, in CI):
  * `tau_ne_zero_of_not_dvd_sigma` — the sieve: `691 ∤ σ₁₁ n → τ n ≠ 0`
    (two lines on top of Iteration 2, but the payoff is unbounded);
  * `lehmer_zero_dvd_sigma` — the contrapositive: any Lehmer counterexample
    `n` must satisfy `691 ∣ σ₁₁ n` (a formalized necessary condition);
  * `prime_dvd_sigma_iff` — for `p` prime, `691 ∣ σ₁₁ p ↔ p ≡ −1 [MOD 691]`,
    the finite fact kernel-decided over the 691 residues (the unique
    solution of `x ^ 11 ≡ −1` is `x = 690`);
  * **`tau_prime_ne_zero_of_mod`** — every prime `p ≢ 690 [MOD 691]`, of
    *arbitrary size*, has `τ p ≠ 0` — the first unbounded-prime coverage in
    the stack: 690 of 691 residue classes, all primes to infinity;
  * `tau_ne_zero_of_sigma_prime_pows` — the divisor-indexed combination with
    `tau_ne_zero_of_prime_pows` (the sieve need only run on prime-power
    blocks);
  * `tau_two_pow_ne_zero_sieve` — `τ (2 ^ a) ≠ 0` for all `a ≤ 64`
    (geometric sums kernel-decided mod 691): the power-of-two tower now
    reaches index `2 ^ 64`, `2 ^ 32` beyond the chain bound;
  * showcases: `tau_of_65537_ne_zero` (the first prime past the wall),
    `tau_of_2147483647_ne_zero` (the Mersenne prime `2³¹ − 1`).

### Results

* Combined coverage after this iteration: `τ n ≠ 0` is verified for every
  `n ≥ 1` (unbounded) such that every prime-power divisor `p ^ a ∥ n`
  satisfies at least one of: (a) `p ≤ 65536` and `p ^ a ≤ 2 ^ 32` (chains),
  or (b) `691 ∤ σ₁₁ (p ^ a)` (sieve — e.g. all primes `p ≢ −1 [MOD 691]`,
  all `2 ^ a`, `a ≤ 64`).  The remaining uncovered set: primes
  `p ≡ −1 [MOD 691]` above 65536, and large prime powers past `2 ^ 32`
  whose σ₁₁-residue vanishes.
* All theorems: `propext, Classical.choice, Quot.sound` only; the finite
  facts are kernel-decided (`bad_residues`, `two_pow_sigma_nonzero`);
  the module is in the CI target list (13.9 GiB peak on the Modal fresh
  clone, 64 s wall).

### Engineering notes

* `Nat.pow_mod (a b n) : a ^ b % n = (a % n) ^ b % n` is the whole bridge
  between "divisibility by 691" and "a fact about the 691 residues".
* Bare `set_option` cannot sit between a docstring and its declaration —
  place it above the doc comment (`set_option ... in` likewise fails before
  `private` in this toolchain).
* Literal exponent evaluation cuts off at `2 ^ 256`:
  `exponentiation.threshold` must be raised for the `2 ^ 704`-scale
  geometric sums of the kernel decide.

### What remains / next steps

* Fuse the sieve with the chain coverage into one grand nonvanishing theorem
  (the union of hypotheses (a)/(b) above) — pure glue, `LehmerPow32`-side.
* The order-based classification of bad prime-power classes
  (`ord_{691}(p) ∣ 11 (a+1)`): 73 residue classes admit some bad exponent;
  a complete `(p mod 691, a mod ord)` table is kernel-decidable and would
  make the sieve unconditional per residue class pair.
* Multi-modulus: the same sieve at other primes `ℓ` with a
  `τ ≡ σ_{k}`-type congruence (691 is the only classical one at weight 12,
  but level-raising and ℓ-adic congruences exist).

## Iteration 11 — The grand fusion: chains ⊕ sieve, and the complete bad-class classification

**Status: complete (grand theorem kernel-verified on Modal; classification light).  2026-10-26.**

### The problem

Iterations 6–10 built three independent nonvanishing routes (dense kernel
compute, Mordell recursion chains, mod-691 sieve) but no single theorem
consumed them together.  Also missing: *which* prime powers `p ^ a` actually
fail the sieve — a finite classification question (691 residue classes ×
order-periodic exponents) that had only been answered numerically for the
seed prime `p = 2`.

### What this iteration contributes

* `MathProof/Tau/LehmerSieve691.lean` (light, extended):
  * `sigma_prime_pow_zmod` — `σ₁₁ (p ^ a)` as a geometric sum in `ZMod 691`;
  * **`prime_pow_dvd_sigma_iff`** — for `p ^ 11 ≢ 1 [MOD 691]`:
    `691 ∣ σ₁₁ (p ^ (a+1)) ↔ (p ^ 11) ^ (a+2) ≡ 1 [MOD 691]` — the bad
    prime-power classes are exactly the root-of-unity conditions on `p ^ 11`
    (period = its multiplicative order); proved by a one-line geometric
    telescoping in the field `ZMod 691`.
* `MathProof/Tau/LehmerGrand.lean` (heavy, Modal-verified: **1759 s wall /
  143.8 GiB peak tree RSS** — it imports the chain module, whose decides
  dominate):
  * **`tau_ne_zero_grand`** — `τ n ≠ 0` for every `n ≥ 1` (unbounded) such
    that each prime-power divisor `p ^ a` is chain-covered
    (`p ≤ 65536`, `p ^ a ≤ 2 ^ 32`) or sieve-covered (`691 ∤ σ₁₁ (p ^ a)`);
  * **`tau_ne_zero_of_lt_two_pow_32`** — `τ n ≠ 0` for **every `0 < n < 2^32`
    whose prime factors above 65536 avoid the single class `−1 [MOD 691]`**
    (a factor `p > 2 ^ 16` occurs to the first power only, then the sieve
    applies; small-prime powers are chain-covered).  This is the first
    *all-of-an-initial-segment* statement at the 2³² scale in the stack;
  * `tau_of_4294967295_ne_zero` — `τ (2 ^ 32 − 1) ≠ 0`: the largest 32-bit
    index, via its Fermat factorization `3 · 5 · 17 · 257 · 65537` (the only
    large factor 65537 satisfies `65537 % 691 = 583 ≠ 690`).

### Results

* The stack's nonvanishing theorem is now a *single* consumable statement
  (`tau_ne_zero_grand`) with three interchangeable coverage routes, and the
  cleanest consequence: all 32-bit indices except a measure-zero residue
  condition on their large prime factors.
* The bad-class question is closed structurally: a prime power fails the
  sieve iff `p ^ 11 ≡ 1` with `691 ∣ (a+1)` (σ = a+1 case) or
  `(p ^ 11)^(a+1) ≡ 1` (root-of-unity case) — both readable off
  `prime_pow_dvd_sigma_iff` and the `p ^ 11 ≡ 1` edge.

### What remains / next steps

* A kernel-decided *table* `∀ x ∈ range 691, ∀ a ∈ range 690, ...` turning
  the root-of-unity condition into a literal lookup (period 690 suffices)
  would make the sieve checkable by `decide` for any concrete `(p, a)`.
* Primes `p ≡ −1 [MOD 691]` above 65536 remain the only unreachable primes;
  the next tool for them is analytic (Deligne-type bounds), not modular.

## Iteration 12 — Lehmer's reduction: the conjecture is a statement about primes

**Status: complete (reduction light; instantiation Modal-verified).  2026-10-26.**

### The problem

Iterations 8–11 reduced nonvanishing of `τ n` to the prime-power blocks
`τ (p ^ a)`, but the blocks themselves were only reachable by
kernel-decided Mordell chains (`p ≤ 65536`, `p ^ a ≤ 2 ^ 32`, ~144 GiB) or
block-by-block sieve conditions `691 ∤ σ₁₁ (p ^ a)`.  Lehmer (1947) showed
that the exponent is irrelevant: **`τ p ≠ 0` implies `τ (p ^ a) ≠ 0` for all
`a`**, so a minimal zero of `τ` is a prime.  This classical reduction had not
been formalized.

### What this iteration contributes

* `MathProof/Tau/LehmerPrimeReduction.lean` (light, in CI):
  * `rec_ne_zero_of_valuation`, `rec_ne_zero_of_sq_ge` — nonvanishing of the
    two-term recurrence `u (a+2) = t u (a+1) − p ^ 11 u a` in its two
    regimes, by elementary arguments (no Deligne bound):
    *p-adic dominance* when `p ^ 6 ∤ t` (`t = p ^ v s`, `v ≤ 5`: then
    `u a = p ^ (a v) w` with `w ≡ s ^ a [ZMOD p]`) and *archimedean
    dominance* when `p ^ 6 ∣ t` (then `p ≥ 5`, `t ² ≥ 4 p ^ 11`, and the
    sequence is sign-monotone);
  * **`tau_prime_pow_ne_zero`** — Lehmer's lemma `τ p ≠ 0 → τ (p ^ a) ≠ 0`;
  * **`lehmerConjecture_iff_primes`** — `LehmerConjecture ↔ ∀ p prime, τ p ≠ 0`;
  * `tau_ne_zero_of_prime_factors`, `tau_ne_zero_of_prime_factors_mod`
    (the 691 sieve with no exponent restriction: `τ n ≠ 0` whenever no prime
    factor of `n` is `≡ −1 [MOD 691]`), `tau_ne_zero_of_primes_le_or_mod`,
    the parametric initial-segment lemma `tau_ne_zero_of_lt_of_prime_gap`;
  * showcases `tau_two_pow_ne_zero` (`τ (2 ^ a) ≠ 0` for **every** `a`),
    `tau_65537_pow_ne_zero`.
* `MathProof/Tau/LehmerPrimeGrand.lean` (heavy, Modal):
  * `tau_ne_zero_of_prime_factors_le_65536_or_mod` — `τ n ≠ 0` for every `n`
    whose prime factors are each `≤ 65536` or `≢ −1 [MOD 691]`, **any
    exponents**: strictly stronger than Iteration 11's `tau_ne_zero_grand`,
    and it needs only the packed decide (~63 GiB), not the chains (~144 GiB);
  * **`tau_ne_zero_of_lt_70481`** — `τ n ≠ 0` for **every** `0 < n < 70481`:
    the first unconditional initial segment beyond the dense bound 65536.
    `70481` is the least prime `> 65536` in the class `−1 [MOD 691]`
    (`prime_gap_691_65536_70481`: the candidates `691 k + 690`,
    `94 ≤ k ≤ 100`, are composite — `norm_num`).

### Results

* `LehmerPrimeReduction` (light): Modal `lean_check` clean, no warnings.
* `LehmerPrimeGrand` (heavy): Modal `lean_check` **481 s wall / 62.85 GiB
  peak tree RSS** (the packed 65536 decide dominates); axioms of
  `tau_ne_zero_of_lt_70481` and
  `tau_ne_zero_of_prime_factors_le_65536_or_mod`: `propext`,
  `Classical.choice`, `Quot.sound` only.  Compare Iteration 11's
  `LehmerGrand`: 1759 s / 143.8 GiB for a strictly weaker statement.
* Lehmer's conjecture is now formally *equivalent* to a statement about
  primes, and every exponent restriction in the stack is gone.

### What remains / next steps

* The unconditional initial segment now grows exactly with sieve strength:
  it ends at the least prime `> 65536` lying in *every* bad class.  Lehmer's
  own 1947 bound came from the moduli `2^11 · 3^7 · 5^3 · 7^2 · 23 · 691`.
  Pure Eisenstein identities only reach `τ` mod 4 at 2 (checked:
  `1800 τ = 691 σ₃ + 1382 σ₇ − 273 σ₁₁ + 331680 Σ σ₃ σ₇`); the deeper
  congruences need Ramanujan's θ-operator, whose formulas
  (`∂E₄ = −E₆/3`, …) Mathlib now has (`RamanujanFormula.lean`).
* Generalized Lehmer for the other one-dimensional level-one eigenforms
  `Δ E₄, Δ E₆, Δ E₈, Δ E₁₀, Δ E₁₄` (weights 16–26): `HeckeLevelOne` is
  weight-generic and Mathlib supplies `S_k ≃ M_{k−12}`; the prime lemma
  generalizes verbatim (odd exponent `k − 1`).
* The Iteration-9/11 chain modules are superseded mathematically; they
  remain as the record of the computational route.

## Iteration 13 — Lehmer's question for every one-dimensional level-one eigenform

**Status: complete (all light, in CI).  2026-10-26.**

### The problem

`S_k(SL(2, ℤ))` is one-dimensional exactly for `k = 12, 16, 18, 20, 22, 26`,
spanned by the normalized Hecke eigenforms `Δ, Δ E₄, Δ E₆, Δ E₄², Δ E₄ E₆,
Δ E₄² E₆`.  Lehmer's question — do the Fourier coefficients ever vanish? — is
open for every one of them, not only for `τ`.  Iterations 2–12 built the
toolkit only for `Δ`.

### What this iteration contributes

* `MathProof/ModularForms/EigenLevelOne.lean` — the toolkit once, for any
  weight: if `f` spans a rank-one `S_k` with integer coefficients `a n`,
  `a 1 = 1` (`IsNormalizedRankOne`), then `f` is a Hecke eigenform
  (`heckeTP_eq`), `a (p m) + p^(k−1) [p ∣ m] a (m/p) = a p a m`, the
  prime-power recursion, **Mordell multiplicativity** (`mul_coprime`),
  **Lehmer's prime-power lemma** (`prime_pow_ne_zero`, for even `k`, via the
  Iteration-12 recurrence lemmas generalized to exponent `p^K`), and
  nonvanishing-iff-on-primes; plus `eq_smul` (every cusp form is
  `(coeff 1) • f`).
* `MathProof/ModularForms/BernoulliHigh.lean` — `B₁₃ … B₂₆` by the recurrence
  chain (`B₁₆ = −3617/510`, `B₁₈ = 43867/798`, `B₂₀ = −174611/330`,
  `B₂₂ = 854513/138`, `B₂₆ = 8553103/6`).
* `LehmerWeight{16,18,20,22,26}.lean` — for each eigenform: integer
  coefficients `a_k = τ ⋆ (coefficients of E_{k−12})`, the analytic identity
  `qExpansion f_k = qExpansion Δ · qExpansion E_{k−12}`, rank one via Mathlib's
  `S_k ≃ M_{k−12}`, and

  | k  | eigenform   | congruence (new, formal)            | sieve-free primes | all `0 < n <` |
  |----|-------------|-------------------------------------|-------------------|---------------|
  | 16 | `Δ E₄`      | `a ≡ σ₁₅ [ZMOD 3617]`               | `p ≢ −1`          | **21701**     |
  | 18 | `Δ E₆`      | `a ≡ σ₁₇ [ZMOD 43867]`              | `p ≢ −1`          | **263201**    |
  | 20 | `Δ E₄²`     | `a ≡ σ₁₉ [ZMOD 174611 = 283·617]`   | `p ≢ −1`          | **1746109**   |
  | 22 | `Δ E₄ E₆`   | `a ≡ σ₂₁ [ZMOD 77683 = 131·593]`    | `p ≢ −1`          | **1087561**   |
  | 26 | `Δ E₄² E₆`  | `a ≡ σ₂₅ [ZMOD 657931]`             | 5 classes `−ζ`    | **1315861**   |

  Each congruence comes from one rank-one argument: `E_k − H ∈ S_k` for an
  integral product `H` of `E₄, E₆` (constant terms cancel), hence
  `E_k − H = (β − h₁) f_k`; clearing the Bernoulli denominator and cancelling
  a unit gives the congruence — no Sturm bound and no dense computation.
  Each initial segment ends at the least prime in a bad class; all smaller
  candidates are composite (`norm_num`).  In weight 26,
  `gcd(25, 657930) = 5`, so the bad classes are the five `−ζ` with
  `ζ⁵ = 1`; they are pinned down by factoring `X⁵ − 1` explicitly in
  `ZMod 657931` (elementary symmetric functions checked by `decide`).

### Results

* Five new formally verified Lehmer-type theorems, each **unconditional on an
  initial segment** (up to 1.7 million for `Δ E₄²`) and **unbounded on the
  sieve-free multiplicative semigroup**, with zero kernel-heavy computation:
  every module is light (each Modal check ≈ 1–2 min, zero warnings).
* The formal weight-`k` Ramanujan congruences mod the reduced `B_k` numerators
  `num B_k / gcd(num B_k, 2k·den B_k)` (Ramanujan/Swinnerton-Dyer) for
  `k = 16 … 26` — exactly 3617, 43867, 283·617, 131·593 (= `num B₂₂ / 11`)
  and 657931 (= `num B₂₆ / 13`).
* Contrast with weight 12: there the 691 class is the only sieve, so the
  initial segment needs the dense 65536 computation; in higher weight the
  large congruence primes make the sieve alone reach far further.

### What remains / next steps

* Weights with `dim S_k ≥ 2` (24, 28, …): the Hecke algebra is no longer
  scalar; the eigenforms have coefficients in a real quadratic (or larger)
  field — Maeda's conjecture territory.  `EigenLevelOne` would need a
  Hecke-stable-basis version.
* Push the weight-12 initial segment with the derivative-based congruences
  (mod 5, 7, 23 …), now that Mathlib has Ramanujan's θ-formulas.

## Iteration 14 — Maeda's conjecture, formally, for every level-one weight with `dim S_k ≤ 3`

**Status: complete (all light, in CI).  2026-10-26.**

### The problem

**Maeda's conjecture** (1997): for every weight `k`, the Hecke algebra of
`S_k(SL(2, ℤ))` is as large as possible — the characteristic polynomial of
`T₂` on `S_k` is irreducible over `ℚ` with Galois group the full symmetric
group.  It is open in general (verified numerically to weight ~14000 by
Ghitza–McAndrew and others), and had no formal verification at all.  The first
nontrivial weight is 24 (`dim S₂₄ = 2`).

### Decision record

The planned follow-up of Iteration 12 (τ congruences mod 5, 7 through
Mathlib's new Ramanujan θ-formulas) was evaluated first and deferred: the
combined `691·5·7` sieve only lifts τ's unconditional bound from 70481 to
96739, while requiring a q-expansion lemma for the derivative `D`.

### What this iteration contributes

* `MathProof/ModularForms/MaedaWeight24.lean` — the first case by hand: basis
  `(Δ E₄³, Δ²)` (Sturm bound), `T₂` as a linear map with matrix
  `[[696, 1], [20736000, 384]]`, `LinearMap.charpoly = X² − 1080 X − 20468736`
  (Hecke field `ℚ(√144169)`), irreducible over `ℚ`.
* `MathProof/ModularForms/MaedaLevelOne.lean` — the machinery, weight-generic:
  * `prodForm k i a b` = `Δ^(i+1) E₄^a E₆^b` with q-coefficients `seqP i a b n`
    given by integer Cauchy products (`conv`, `cpow`) of `σ`-sequences and a
    τ lookup table tied to the verified `tau_one … tau_twenty_one` — so
    concrete coefficients are evaluated by `decide +kernel`;
  * `heckeTPₗ` (T_p as a linear map), `heckeT2_coeff`;
  * **`charpoly_dim2` / `charpoly_dim3`**: for a triangular family in a space
    of dimension 2 / 3, the characteristic polynomial of any endomorphism is
    read off the first q-coefficients of the images (basis from the dimension
    formula + linear independence — no Sturm bound, so `k ≡ 2 (mod 12)` works);
  * `charpoly_fin_three`; `irreducible_of_noRoot` (monic degree ≤ 3, no root
    mod a prime ⇒ irreducible over `ℚ`, via Gauss's lemma).
* `MathProof/ModularForms/MaedaSmallWeights.lean` — generated by
  `tools/gen_maeda.py` (which only produces certificates; Lean re-checks
  everything): the remaining 11 weights.

### Results

  | k  | dim | charpoly of `T₂` on `S_k` (proved) | no root mod |
  |----|-----|-------------------------------------|-------------|
  | 24 | 2 | `X^2 − 1080X − 20468736` | 23 |
  | 28 | 2 | `X^2 + 8280X − 195250176` | 29 |
  | 30 | 2 | `X^2 − 8640X − 454569984` | 29 |
  | 32 | 2 | `X^2 − 39960X − 2235350016` | 29 |
  | 34 | 2 | `X^2 + 121680X − 8513040384` | 31 |
  | 38 | 2 | `X^2 + 194400X − 137403408384` | 41 |
  | 36 | 3 | `X^3 − 139656X^2 − 59208339456X − 1467625047588864` | 37 |
  | 40 | 3 | `X^3 − 548856X^2 − 810051757056X + 213542160549543936` | 37 |
  | 42 | 3 | `X^3 + 344688X^2 − 6374982426624X − 520435526440845312` | 41 |
  | 44 | 3 | `X^3 + 2209944X^2 − 15663522502656X − 19976984434430705664` | 61 |
  | 46 | 3 | `X^3 − 3814272X^2 − 44544640241664X + 135250282417024401408` | 53 |
  | 50 | 3 | `X^3 + 24225168X^2 − 566746931810304X − 13634883228742736412672` | 53 |

For each weight: `MaedaWeightK.charpoly_T2` (the characteristic polynomial of
the linear map `T₂ : S_k → S_k`) and `MaedaWeightK.maeda` (irreducible over
`ℚ`).  This is **every level-one weight with `dim S_k ∈ {2, 3}`**.  For
`dim = 2` irreducibility is the whole of Maeda (Galois group `S₂`).  Whole
instance file: 167 s on Modal, zero warnings; no `sorry`, no `native_decide`.

* **Galois group (full Maeda).** `MathProof/ModularForms/MaedaGalois.lean`:
  `galActionHom_bijective_of_cubic` — an irreducible cubic over `ℚ` with
  non-square discriminant has Galois group `S₃` (proved from scratch: in the
  splitting field `δ = (x−y)(x−z)(y−z)` has `δ² = disc`, so `2 · 3 ∣ |Gal|`,
  and `Gal ↪ S₃`).  Mathlib's prime-degree criterion needs two non-real roots,
  which Hecke polynomials never have (their roots are real).  Instances
  `maeda_galois36 … maeda_galois50`: the six discriminants are non-squares
  (non-residues mod 29, 41, 43, 41, 23, 41).  **Maeda's conjecture — irreducible
  charpoly and full symmetric Galois group — is therefore formally verified for
  every level-one weight with `dim S_k ≤ 3`** (for `dim 2`, `S₂` is automatic).

### What remains / next steps

* `dim S_k ≥ 4` (k = 48, 52, …): a `charpoly_dimN` via triangular bases in
  general `Fin n`, and irreducibility of quartics+ mod ℓ (degree > 3 needs
  more than "no roots": e.g. a Rabin/Berlekamp-style certificate).
* `T_p` for other `p` (Maeda is often stated for all `T_n`; the algebra is
  generated by `T₂` exactly when its charpoly is irreducible, which is now
  proved in these weights).

## Iteration 15 — Maeda's conjecture (irreducibility) in dimension 4: weights 48–62

**Status: complete (all light, in CI).  2026-10-26.**

### The problem

Iteration 14 settled every level-one weight with `dim S_k ≤ 3`.  The next six
weights `k = 48, 52, 54, 56, 58, 62` have `dim S_k = 4`, where two things break:
the coefficient computation (indices up to 8 with `E₄` powers up to 11 timed
out the kernel: the nested Cauchy products of `seqP` recompute subterms
exponentially), and irreducibility certificates (for degree 4, "no root mod ℓ"
does not imply irreducibility).

### What this iteration contributes

`MathProof/ModularForms/MaedaDim4.lean`:
* **memoized coefficients** — `seqPL` computes the first `N` coefficients of
  `Δ^(i+1) E₄^a E₆^b` as lists (each product `O(N²)`), with `seqP_getD`
  transferring to `seqP` (proof via `convL_lst`, `cpowL_eq`); weight 48 went
  from a kernel timeout at 30 GiB to seconds;
* `charpoly_dim4` (four-row back-substitution) and `charpoly_fin_four`
  (explicit principal-minor / Laplace formula);
* **quartic irreducibility certificate** — `irreducible_quartic`: a monic
  quartic over a field with no root and no factorization into monic quadratics
  `(X² + uX + v)(X² + sX + t)` is irreducible (via
  `Monic.irreducible_iff_natDegree'`); solving `s, t` from `u, v` makes the
  quadratic check a scan over `ℓ²` pairs; `irreducible_quartic_of_mod` lifts it
  to `ℚ` (mod-ℓ reduction + Gauss).

`MathProof/ModularForms/MaedaDim4Weights.lean` (generated by
`tools/gen_maeda.py`, now dimension-aware; the dims-2/3 file regenerates
byte-identically): the six weights.

### Results

  | k  | charpoly of `T₂` on `S_k` (proved) | irreducible mod |
  |----|-------------------------------------|-----------------|
  | 48 | `X^4 − 5785560X^3 − 467142374034432X^2 + 1426830562183253852160X + 3297913828840214320807673856` | 53 |
  | 52 | `X^4 − 32756040X^3 − 7956172284567552X^2 + 269568678949709508771840X + 4615876968087578049834569957376` | 67 |
  | 54 | `X^4 + 68476320X^3 − 19584715019010048X^2 − 1083312724663489297121280X + 39446133467662904714689328971776` | 83 |
  | 56 | `X^4 − 208622520X^3 − 69659795501724672X^2 + 11031882363768735132549120X − 255678332805518077225389998997504` | 71 |
  | 58 | `X^4 + 217744560X^3 − 411086477602603008X^2 − 42515907658957794091991040X + 18678231666950985607375948785647616` | 61 |
  | 62 | `X^4 − 1146312000X^3 − 6156169255669690368X^2 + 2540887466526178560442368000X + 3583176547297492565952659077522784256` | 71 |

`MaedaWeightK.charpoly_T2` and `MaedaWeightK.maeda` for each.  With Iteration 14:
**irreducibility of the `T₂` characteristic polynomial (the core of Maeda's
conjecture) is formally verified for all 18 level-one weights with
`dim S_k ≤ 4`** (k = 24–62 except 26, dim 1, and 60, dim 5); the full symmetric
Galois group is verified for `dim ≤ 3`.  Whole dimension-4 file: 145 s on
Modal, zero warnings.

### What remains / next steps

* Galois group `S₄` in dimension 4: irreducible quartic with irreducible
  resolvent cubic and non-square discriminant (classical criterion, not in
  Mathlib), or Dedekind-type cycle certificates.
* `dim S_k ≥ 5` (k = 60, 64, …): a `Fin n`-generic `charpoly_dimN` and a
  general irreducibility certificate (degree-`n` factor search mod ℓ, or a
  Rabin-test certificate) — the list-based coefficient engine already scales.

## Iteration 16 — Maeda's conjecture in full through dimension 4: Galois group `S₄`

**Status: complete (light, in CI).  2026-10-26.**

`MathProof/ModularForms/MaedaGalois4.lean`:

* **`galActionHom_bijective_of_quartic`** — an irreducible monic quartic
  `X⁴ + aX³ + bX² + cX + d` over `ℚ` whose resolvent cubic
  `Y³ − bY² + (ac − 4d)Y − (a²d − 4bd + c²)` is irreducible and whose
  discriminant is not a square has Galois group `S₄` (the action on the four
  complex roots is all of `Perm`).  Mathlib has no quartic Galois criterion;
  the proof is by degree counting plus one fact about `A₄`:
  * Vieta in the splitting field `K` (`vieta4`), then two `ring` identities —
    `θ = x₀x₁ + x₂x₃` is a root of the resolvent, and
    `δ = ∏_{i<j}(x_i − x_j)` has `δ² = disc4 a b c d` (a degree-12 identity);
  * `4 ∣ [K:ℚ]` (root of `P`), `3 ∣ [K:ℚ]` (`θ`), `Gal ↪ S₄`: `|Gal| ∈ {12, 24}`;
  * if `|Gal| = 12`, its image is the index-2 subgroup `A₄`
    (`eq_alternatingGroup_of_index_eq_two`); `ℚ(δ)` is quadratic, so its
    fixing subgroup has index 2 (Galois correspondence:
    `card_fixingSubgroup_eq_finrank`); an index-2 subgroup contains all
    squares, each 3-cycle is `(c²)²`, and 3-cycles generate `A₄`
    (`closure_three_cycles_eq_alternating`) — contradiction.
* Instances `maeda_galois48 … maeda_galois62`: resolvent cubics irreducible
  mod 43, 53, 47, 47, 53, 53; discriminants non-residues mod 23, 29, 29, 29,
  31, 29.

### Results

**Maeda's conjecture — irreducibility of the `T₂` characteristic polynomial
and full symmetric Galois group — is formally verified for all 18 level-one
weights with `dim S_k ≤ 4`** (`k = 24 … 62`, `k ∉ {26, 60}`): `S₂` (6 weights),
`S₃` (6), `S₄` (6).  Modal: 261 s, zero warnings.

### What remains / next steps

* `dim S_k ≥ 5` (k = 60, 64, …): needs a `Fin n`-generic `charpoly_dimN`, an
  irreducibility certificate for degree ≥ 5, and — for the Galois group — a
  criterion beyond resolvents (e.g. irreducible + a transposition + an
  `(n−1)`-cycle via Dedekind's theorem, which Mathlib lacks).

## Iteration 17 — Maeda's conjecture (irreducibility) in dimension 5: weights 60–74

**Status: complete (light, in CI).  2026-10-27.**

### The problem

Iterations 14–16 settled Maeda's conjecture for every level-one weight with
`dim S_k ≤ 4`.  The next six weights `k = 60, 64, 66, 68, 70, 74` have
`dim S_k = 5` (completing *all* weights `k ≤ 74` except the dim-1 ones), where
the same two walls appear one dimension higher: a five-row back-substitution
matrix, and irreducibility certificates for degree 5.  The pre-iteration
scaling study (`research/maeda-scaling-study.md`, probe
`research/maeda-scaling-probe.py`) measured the whole `dim ≤ 25` axis and
recommended this as the next ratchet step.

### What this iteration contributes

`MathProof/ModularForms/MaedaDim5.lean`:

* **`charpoly_dim5`** — the five-basis-element extension of the triangular
  back-substitution (`charpoly_dim2/3/4`): linear independence by five
  q-coefficient equations, the basis repr characterization `hb`, and the
  25-entry matrix read off `T f_j`;
* **`charpoly_fin_five`** — the `5 × 5` characteristic polynomial as its
  principal-minor sums (`X⁵ − e₁X⁴ + e₂X³ − e₃X² + e₄X − det`, 5/10/10/5/1
  minors, e₅ = 120 terms), proved by two rounds of `Matrix.det_succ_row_zero`
  down to `det_fin_three` + `ring`;
* **`irreducible_quintic` / `irreducible_quintic_of_mod`** — the quintic
  certificate: a reducible monic quintic still has a factor of degree ≤ 2
  (`Monic.irreducible_iff_natDegree'` gives `g.natDegree ≤ 5/2 = 2`), so "no
  root + no factorization into monic quadratic × monic cubic" suffices; the
  cubic's `r, s, t` are forced by `u, v` (`r = a − u`,
  `s = b − v − ur`, `t = c − vr − us`), leaving two residual equations scanned
  over `ℓ²` pairs — the same `decide +kernel` shape as the quartic.

`MathProof/ModularForms/MaedaDim5Weights.lean` (generated by
`tools/gen_maeda.py`, dimension-aware now up to 5; dims 2–4 regenerate
byte-identically): the six weights.

### Results

| k  | charpoly of `T₂` on `S_k` (proved) | irreducible mod |
|----|-------------------------------------|-----------------|
| 60 | `X⁵ + 449691864X⁴ − 2209450184054433792X³ − 736010060393513697870348288X² + 810634763334812972416233648439689216X + 263222216157060824115203098902237248565018624` | 83 |
| 64 | `X⁵ − 507315096X⁴ − 26316207229657439232X³ + 7816999697067374824780726272X² + 93356730870958242939964792647614201856X + 59899702063757157544982491709928053576589901824` | 73 |
| 66 | `X⁵ + 3959709648X⁴ − 142850166119005483008X³ − 339986038308627409973683421184X² + 4888759358323485530147825225712235708416X + 6737365607750178848535412403321340119893376237568` | 79 |
| 68 | `X⁵ − 5554901256X⁴ − 528742419683384143872X³ + 1360506199877236618906967212032X² + 50978026392314038029857853615859298205696X − 224135116306806567372209572838489759238644853374976` | 97 |
| 70 | `X⁵ + 18005734368X⁴ − 1942747456996431618048X³ − 14539211744046993293953166475264X² + 613518461067953168654246762332094963122176X + 4169744246282611427836654706819235757668276180615168` | 79 |
| 74 | `X⁵ + 92089333488X⁴ − 19817164982845968703488X³ − 1377989142595747748686715833810944X² + 11802708847432637761332792635527627366465536X + 113628227457643966226006850359168010340399423074336768` | 79 |

With Iterations 14–16: **the irreducibility half of Maeda's conjecture is
formally verified for all 24 level-one weights `k ≤ 74` with `dim S_k ≥ 2`**
(`k = 24 … 74`, `k ∉ {26}`), and the full conjecture (Galois group) for all
with `dim S_k ≤ 4`.  Whole `MaedaDim5Weights` file: 214 s on Modal, zero
warnings, 14.9 GiB peak (light module, in CI).

### What remains / next steps

* Galois group `S₅` (Iteration 18, per the scaling study): the sextic resolvent
  route — 5 ∣ |Gal| from irreducibility, 6 ∣ |Gal| from an irreducible sextic
  resolvent (pentagon-sum θ_P), exclude 30 and 60 (A₅ ⇒ square discriminant),
  conclude S₅.  Design step: probe the resolvent numerically first.
* Dims 6+ (Iteration 19, the generic engine): `Fin n`-structural
  `charpoly_dimN`, reflected Bareiss + interpolation, Rabin certificates — the
  study's route to `k ≤ 314` (`dim S_k ≤ 25`).

## Iteration 18 — Maeda's conjecture in full for dimension 5: Galois group `S₅`

**Status: complete (heavy, Modal — not in CI).  2026-10-29.**

### The problem

Iteration 17 proved the `T₂` characteristic polynomial irreducible for the six
weights with `dim S_k = 5` (`k = 60, 64, 66, 68, 70, 74`).  Maeda's conjecture
also asserts the full symmetric Galois group.  Mathlib has no quintic Galois
criterion, and the textbook one (Cayley's `F₂₀` sextic resolvent) rests on
polynomial identities of degree up to 24 in the five roots — far beyond `ring`
(measured: 323 GiB OOM monolithic; per-coefficient `ring` OOMs from `e₃` on).

### What this iteration contributes

**The criterion** (`MaedaGalois5.lean`, `galActionHom_bijective_of_quintic`): an
irreducible monic quintic over `ℚ` with non-square discriminant `disc5` and a
sextic resolvent `resolvent5` without rational root has Galois group `S₅`.
Proof by degree counting on `G = Gal ↪ S₅` (`ρ`, injective via `Gal.ext`):

* `5 ∣ |G|` (root of the irreducible quintic), `2 ∣ |G|` (`ℚ(δ)`, `δ² = disc5`
  non-square) — so `|G| ∈ {10, 20, 30, 40, 60, 120}`;
* `60`: `ρ(G) = A₅` (index 2), but `ℚ(δ)` fixes an index-2 subgroup containing
  all squares, and 3-cycles are squares of squares and generate `A₅`;
* `30, 40`: `S₅` has no subgroup of index 4 or 3 (`perm_no_index_three_four`,
  Iteration 18 part 1: normal core + `A₅` simple);
* `10, 20`: the Sylow normalizer congruence makes the 5-Sylow `⟨c⟩` normal
  (`perm_order_5_normal_of_card`), so every Galois element normalizes `⟨c⟩` and
  fixes the pentagon-pentagram product `θ(c)·θ(c²)` (`gal_fixes_theta`) — a
  rational number, and a root of the resolvent (`resolvent_eval_theta`):
  contradiction with `hres`.

**The identities** (`Poly5.lean` + the generated chain `MaedaGalois5IdBase →
IdE4 → IdE5 → IdE6 → MaedaGalois5Identities`, `tools/gen_poly5.py`): the six
resolvent coefficients `e₁ … e₆` of the products `θ_j` (35 … 10 780 monomials in
`x₀ … x₄`) and `δ² = disc5` (2 961 monomials) are certified by `decide +kernel`
on canonical sparse-polynomial lists (the `LehmerPacked` methodology, now
multivariate) and transported to every commutative ring by `PEval`
homomorphism lemmas; the coefficient side is a Horner scheme over `va … ve`.
`sextic_vieta` + `linear_combination theta_eₖ` turn them into
`resolvent_eval_theta`.  Two kernel lessons, now in the `Poly5` docs:

* `List`'s `DecidableEq` recurses non-tail (one kernel frame per element):
  "deep recursion" past a few thousand terms.  `pBeq` (`decide (t = t') &&
  pBeq ts ts'`) is tail-recursive in the kernel's whnf loop — constant stack;
* the kernel stack while forcing `pMul p q` grows with `len p`: the generator
  puts the smaller factor on the left (2445-term left factors fail, 218 pass).

**The instances** (`MaedaGalois5Weights.lean`, `tools/gen_galois5.py` from
`research/s5_certs.json`): `maeda_galois60 … maeda_galois74`.  The resolvent is
an explicit integer polynomial `R` (coefficients re-derived from `resolvent5`
by `norm_num`, `hRint`); its reduction `Rmod` is a computable function, so
`noRootR` is a plain `decide +kernel`; a rational root would be integral
(monic) and hence a root mod `ℓ`.

### Results

**Maeda's conjecture — irreducibility and full symmetric Galois group — is
formally verified for all 24 level-one weights with `2 ≤ dim S_k ≤ 5`**
(`k = 24 … 74`, `k ≠ 26`): `S₂, S₃, S₄` (Iterations 14–16) and now `S₅`.

| k  | disc non-residue mod | resolvent rootless mod |
|----|----------------------|------------------------|
| 60 | 37 | 41 |
| 64 | 29 | 31 |
| 66 | 29 | 29 |
| 68 | 23 | 23 |
| 70 | 41 | 41 |
| 74 | 41 | 37 |

All six depend only on `[propext, Classical.choice, Quot.sound]` (in-file
`#print axioms`).  Modal build (lake, per module): `Defs` 461 s, `IdBase`
209 s, `IdE4` 2343 s / 202 GiB peak, `IdE5` 1498 s / 137 GiB, `IdE6` 2207 s /
172 GiB, `Identities` 170 s / 23 GiB, `MaedaGalois5` and `Weights` < 1 min /
7 GiB.  `lean_check.py` now keeps a rolling build cache on the `lean-cache`
volume (saved even after a failed build), so the chain is paid for once.

### What remains / next steps

* Style lint in the generated identity modules (long lines, uncommented
  heartbeat bumps) and in `MaedaGalois5Defs` — fixing them means regenerating
  and rebuilding the chain (~2 h, ~200 GiB), so batch it with the next change
  that touches them.
* Dims 6+ (Iteration 19, the generic engine): `Fin n`-structural
  `charpoly_dimN`, reflected Bareiss + interpolation, Rabin certificates; for
  the Galois group beyond `S₅`, a criterion via Frobenius cycle types
  (irreducible + transposition + `(n−1)`-cycle), which needs Dedekind's
  theorem — not in Mathlib.

### Axiom audit of the certificates (follow-up, 2026-10-29)

`MathProof/ModularForms/MaedaGalois5AxCheck.lean` (heavy: imports the chain;
~48 s / 6 GiB on Modal with the chain cached, nothing rebuilt) prints the
axioms of every Iteration 18 certificate:

* `e1dec … e6dec`, `ddec` (the `Poly5` kernel certificates): `[propext]`.
* `Weight{60,…,74}.nonsquare`, `.noRootR`: first audited at
  `[propext, Classical.choice, Quot.sound]` — they were stated over `ZMod ℓ`.
  A local probe pinned the cause: `∀ x : ZMod 37, …` by `decide` → all three
  axioms; over `Fin 37` → `[propext]`; over bounded `ℕ` with `ℤ` arithmetic →
  none; merely evaluating a `ZMod` function → `[propext, Quot.sound]`.
  **Fixed**: new light module `HornerCert` (`hornerZ`, structural Horner over
  `ℤ`; `no_root_of_cert`, `ne_sq_of_cert` transport the certificate to "no
  integer root / not a square").  `tools/gen_galois5.py` now emits
  `nonsquare : ∀ y : ℕ, y < q → hornerZ [Dlit, 0, -1] y % q ≠ 0` (with
  `Dval_eq : Dval = Dlit`) and `noRootR : ∀ y : ℕ, y < ℓ → hornerZ Rcs y % ℓ
  ≠ 0` (with `R_eval_eq`).  All twelve now **depend on no axioms**; the six
  `maeda_galois*` theorems are unchanged (standard three).  `Weights` rebuilt
  in 13 s, zero warnings.
* `theta_e6`, `resolvent_eval_theta`, `galActionHom_bijective_of_quintic`,
  `maeda_galois60 … 74`: the standard three axioms (allowed for these).

**Project-wide audit.**  `MathProof/AxCheckDecide.lean` (`#audit_decide_certs`,
opt-in) walks every `decide` certificate of the light library; `#axiom_path ax
n` prints the dependency path that pulls an axiom in.  First run: **116
audited, all 116 depend on `[propext, Classical.choice, Quot.sound]`** — the
propext-only rule of CLAUDE.md had never been met by the light library's
`decide` facts.  The traced causes:

* `∀ x : ZMod ℓ` decided through `Fintype.decidableForallFintype` (Finset /
  Multiset: `Classical.choice`), and `ZMod`'s ring instance (`funext` →
  `Quot.sound`);
* `seqPL` built from `Finset.sum` / `Finset.range` and
  `ArithmeticFunction.sigma` (`Finset.Ico`, `LocallyFiniteOrder`);
* `Ramanujan.allNonzeroLt` uses `!=` on `ℤ`, i.e. `Int.instLinearOrderPackage`.

**Fixed (97):** `MaedaCertC` (new, light) — `seqPLc`, the same coefficient
lists from `List` sums, trial-division `sigmaL` and `tauTable`, with
`seqPLc_eq` (via `sigmaL_eq`, `convLc_eq`); `tools/gen_maeda.py` (dims 4–5)
now emits `L{j}c : seqPLc … = […]` (decided) and derives `L{j}`, and for
`noRoot` / `noQuad` an `ℤ`-over-bounded-`ℕ` certificate `*_cert` with the
`ZMod` statement derived by `HornerCert.exists_natCast_eq` +
`emod_eq_zero_of_cast` + `push_cast; linear_combination` (downstream proofs
unchanged).  Same hand-written pattern in `MaedaGalois4` (12) and
`MaedaWeight24` (1); the `σ_k(2)` values in `LehmerWeight18–26` (6) are now
`simp` facts (`Nat.Prime.divisors`), not `decide` certificates.  Re-audit:
**110 certificates, 91 propext-clean, 19 remaining.**

**The 19 heavy-chain ancestors** (`MaedaSmallWeights` 11, `MaedaGalois` 6,
`LehmerWeight16` 1, `Tau.Lehmer` 1) were first deferred — they are
transitive imports of `MaedaGalois5Defs`, and lake's traces are input-based,
so editing them rebuilds the identity chain (measured: a `MaedaLevelOne`
edit made `IdBase` rebuild) — and then fixed together with the chain rebuild
below: `gen_maeda.py` dims 2–3 emit `noRoot_raw_cert`, `MaedaGalois` gets
`nonsquare{k}_cert`, `σ₃(2)` by `simp`, and `Ramanujan.allNonzeroLt` tests
with `Int.decEq` explicitly.  **Final audit: 109 light-library `decide`
certificates, 0 depending on more than `propext`.**

### Identity chain rebuilt for memory (2026-10-29)

Investigation and design: `research/poly5-memory-study/README.md`.  Kernel
`decide` memory ≈ 27 GiB per million `Poly5` list operations within one
declaration; the old chain computed e_k(Θ) as C(6,k) brute-force products.
`tools/gen_poly5.py` now (1) computes e_k by the recurrence
`E_{j,k} = E_{j−1,k} + Θ_j·E_{j−1,k−1}` with every node a literal certified by
its own `decide`, (2) checkpoints the Horner side into literals at ≈ 0.5 M
modelled operations, (3) keeps `e{k}dec` / `ddec` as derived theorems (so
`MaedaGalois5`/`Weights` are unchanged), and (4) emits lint-clean code (the
P2-1 debt; `MaedaGalois5Defs` lint fixed by hand: scoped budgets, `omit`,
`have`, `change`).  Measured with `tools/stage_chain.sh`:

| module | before | after |
|---|---|---|
| `IdBase` | 24.5 GiB, 209 s | **8.1 GiB, 93 s** |
| `IdE4` | 202 GiB, 2343 s | **13.5 GiB, 207 s** |
| `IdE5` | 137 GiB, 1498 s | **22.0 GiB, 434 s** |
| `IdE6` | 172 GiB, 2207 s | **34.7 GiB, 977 s** |
| `Identities` | 23 GiB, 170 s | 17.6 GiB, 273 s |
| `MaedaGalois5` / `Weights` | ≈ 7 GiB | 6.6 / 6.3 GiB |

Whole chain ≈ 33 min instead of ≈ 2 h; every module below the 64 GiB alert
threshold (largest 34.7 GiB vs 202).

**Memory-alert tooling** (policy: any build ≥ 64 GiB is investigated,
AGENTS.md "Memory alerts", `research/memory-alerts.md`): `lean_check.py` now
prints per-module peak RSS (`[memory]`), raises `[memory-alert]` at 64 GiB,
and `LEAN_CHECK_PROFILE=<Module>` attributes memory to declarations (marks
before every top-level command, RSS bucketed between them).  Validation on
`MaedaGalois5Identities` (19.5 GiB peak): `ddec`'s kernel decide accounts for
+14.6 GiB of growth (116 s); `delta2_identity` for 100 s at +0.5 GiB.

## Iteration 18b — TauCeti coding-rules compliance refactor (in-repo)

Branch `dev/i18-refactor-tauCeti-rule`, commits `555491f` + `ebc69ca`
(2026-10-30).  Goal: the light library complies with
`external-doc/CODING_STANDARDS.md` — **zero `set_option`** in every
`defaultTargets` module, comment-aware mechanical audit, options in Tier C
modules documented with measured reasons.

Method per the "classify before raising a limit" lesson: strip the option,
rebuild, read the actual error, then restructure.

| fix | class of failure | resolution |
|---|---|---|
| `Tau/Lehmer` 128-decide | elaborator recursion depth | `decide +kernel` (~100 s kernel < 200 s budget) |
| `Tau/Bridge` (2), `Weight12` (1) | none — **stale options** | delete |
| `Congruence691` `Prime 691` | elaborator recdepth (instance whnf) | `by norm_num` |
| `LehmerSieve691` residue + geom scans | elaborator recdepth; pow threshold | `decide +kernel` ×2 |
| `LehmerSieve691` Mersenne prime | **kernel** deep recursion in trial-division cert | Mathlib Lucas–Lehmer (`LucasLehmerTest 31`) |
| `MaedaGalois5Defs` `resolvent5` | genuine elaboration timeout (200k) | sextic split into 16 private defs `r5c*` (≤450 tokens each), identity numerically validated; `resolvent5_map` simp list extended |
| `MaedaGalois5Weights` | `linter.style.longLine` | 156 literals split `(A * 10 ^ 55 + B)`, wrapped ≤ 99 chars |

Result (comment-aware `tools/tauceti_audit.sh`): 0 `set_option` in all
default targets; 65 remaining in the 9 Tier C modules (LehmerMod/Packed/Pow32,
MaedaGalois5, Id-chain) with measured justifications
(`research/refactor-i18-tauceti/README.md` §4).  Heavy chain rebuilt end-to-end
via `stage_chain.sh` after the ancestor edits; `AxCheck`/`AxCheckDecide`
re-run on Modal; full details and verification matrix in the README above.

## Blueprint implementation wave (2026-10-31, same branch follow-on)

Per operator instruction, the three `dev/blueprint` items were implemented on
`impl/blueprint/*` branches (worktrees outside the main tree), each
Modal-verified (linters on) and pushed:

* **`impl/blueprint/iteration19-maeda-generic`** (`3de75de`) — the Iteration 19
  engines: `CharpolyEngine.charpoly_of_eval_eq` (certified `eval_det`
  interpolation) and `RabinCert.lean` (769 lines) with **`irreducible_of_rabin`
  fully proved** — the blueprint's "one new mathematical lemma" turned out to
  need only assembly, since
  `Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X` (± converse)
  already exists at the pin.  Reflected `List ℤ` engine (structural/fuelled
  only) + transport + `irreducible_of_rabin_cert`/`_int` packaging; k=72
  smoke decides [propext]-only.  Generated dim-6..10 weight files are the
  follow-up (exact per-weight call list in the agent report /
  `research/blueprint-impl-wave.md`).
* **`impl/blueprint/hecke-algebra-upgrade`** (`5c56cbe`) —
  `HeckeAlgebraQT2.lean`: `minpoly = charpoly` from irreducibility plus the
  Maeda-statement upgrade `exists_aeval_of_commute_of_irreducible_charpoly`
  (generic over endomorphisms), proved via T₂-cyclicity (Bézout) instead of
  the blueprint's `Module (AdjoinRoot f)` descent.  `HeckeCommute.lean`
  (general `T_m`) is the open prerequisite for feeding it the level-one
  commutation input.
* **`impl/blueprint/dedekind-frobenius`** (`f54534a`) — `MaedaPermCriterion.lean`
  (stages 1–2): parity finish, `JordanFor` hypothesis interface,
  `FrobHasCycleType` Dedekind interface.  **Mathematical correction**: the
  blueprint's "transitive + transposition + p-cycle (p ≤ n−3) ⟹ Sₙ" variant is
  false (`S₃ ≀ S₂ ⊂ S₆`, order 72 < 360); the correct forms need primitivity
  (Wielandt) or a (n−1)-cycle — documented in the docstrings and the blueprint
  needs the same fix.  Bonus: the pin already has partial Jordan content
  (`GroupTheory/GroupAction/Jordan.lean`).

Process lesson (recorded in the wave doc): an agent that API-greps against a
Mathlib checkout of a *different ref* (master@rc2 vs the pinned rc1) produces
code that fails the real build — the pinned source lives at
`.lake/packages/mathlib` and is the only valid grep target; local
`lake env lean <file>` reproduces lake semantics exactly and beats Modal
round trips for this class of error.

## Merge to master + CI fix (2026-10-31, closes the 18b cycle)

* `dev/i18-refactor-tauCeti-rule` fast-forwarded into `master`; the three
  `impl/blueprint/*` branches merged via `integration/blueprint-wave`
  (union-resolved registration files).  Combined light build green
  (8107 jobs) before the push; master at `b5d033e`, worktrees removed.
* CI fix `46f4e4d`: dropped the `docgen-action` step — it re-ran the whole
  build a second time and built doc-gen4 + Mathlib **from source** (30+ min
  per push), and its deploy would overwrite the hand-maintained `docs/`
  Pages site.  CI is now the single `lean-action` step (~2 min: Mathlib
  oleans from the CDN cache, project targets only); the Pages site remains
  the branch-deployed `docs/` folder.  The leftover docgen run on `b5d033e`
  was cancelled in the Actions UI.

## Iteration 20 — Maeda's conjecture for dims 6–10 (weights 72–134)

Branch `dev/iteration20-maeda-dim6-10`, implementing the `dev/blueprint`
blueprint `iteration19-maeda-generic` (whose engines — `CharpolyEngine`,
`RabinCert` — landed in the 2026-10-31 blueprint wave).  **Maeda's
conjecture (the irreducibility half) is now formally verified, from the
Hecke operator itself, for every level-one weight with `2 ≤ dim S_k ≤ 10`**:
30 new weights `72 ≤ k ≤ 134` (`MaedaDim{6..10}Weights.lean`) on top of the
24 weights `24–74` of Iterations 14–16.  With it, `S_k(SL(2,ℤ))` has a
verified-irreducible `T₂` charpoly for all 54 weights `k ≤ 134` with
`dim S_k ≥ 2` (every such weight except 26 and 132).

Stages (plan `research/iteration20-plan.md`, handoff
`research/iteration20/S3-handoff.md`):

* **S1 `CharpolyDimN.lean`** (`57656b0`, ℕ-restructure `eb94f4d`): the
  dimension-generic echelon extraction `charpoly_dimN` — the matrix of any
  endomorphism from q-coefficient tables by downward back-substitution
  (`coordN`/`coordsAux`).  The first, Fin-indexed shape died on
  `omega`-opaque cast chains; ℕ-indexed hypotheses compiled first-try.
* **S2 `tools/gen_maedan.py`**: emits one file per dim from
  `research/iteration20/data/maeda_dim6_10.json` (census regenerates
  byte-identically; matrices/charpolys regression-asserted against the
  proved k = 24/48 ones).
* **S3 dim 6** (`838fc35`): the 66-error pipeline bring-up; its 25 gotchas
  are in the handoff and remain the reference for the hmap simp+rw chain,
  per-entry theorems and `C (1) * X ^ n` leading-term idiom.
* **S4 dims 7–10** (this entry): three new failure classes, all fixed in the
  generator, never in the generated files:
  1. *q/t statement lines over 100 chars* (dims 8–10): the RHS value now
     wraps to a continuation line (`coeff_stmt`).
  2. *Chunked determinant literals*: `eval_det` reduces `det (t·1 − M)` to a
     flat numeral but cannot close `flat = c0 * 10 ^ e0 + c1 …`; chunked
     `det_t`s get `norm_num` after `eval_det` (validated locally on the
     exact goal shapes, incl. 4-chunk dim-10 size, before the Modal run).
     Charpoly coefficients past 80 digits are chunked with the SAME token
     sequence inside `P` and the hmap rewrites (`rw` matches syntactically).
  3. *`simp only [coordsAux]` heartbeat exhaustion at the deepest
     back-substitution rows* (dim 9: `entry_8_{4..8}`, 30 deterministic
     timeouts): the entries are now STAGED — per (column, row-count)
     `Lv{a}_{j} : coordsAux … j = [literal list]`, each proved from the
     previous stage by a ONE-step unfold (`change`, never `show` —
     `linter.style.show` rejects goal-changing `show`s) + `rw` + a
     j-tuned simp set (j = 1: the empty sum kills `Atab`; j = 2: a
     1-element prefix uses no `getD_cons_succ`); entries are then
     `simp only [coordN]; rw [Lv{a}_{c+1}]; rfl`.  Staging also made every
     file faster (dim 9: 931 s failed cascade → 413 s staged).

  Verification matrix (Modal `lean_check --file`, linters on, all green with
  ZERO warnings; build time / per-module peak RSS):

  | module | lines | build | peak |
  |---|---|---|---|
  | `MaedaDim6Weights` | 10587 | 88 s | 6.4 GiB |
  | `MaedaDim7Weights` | 14199 | 138 s | 7.1 GiB |
  | `MaedaDim8Weights` | 18389 | 333 s | 8.1 GiB |
  | `MaedaDim9Weights` | 23257 | 413 s | 9.3 GiB |
  | `MaedaDim10Weights` | 28922 | 1167 s | 11.6 GiB |

  The flagged kernel-time risk (k = 120: ~28k ZMod-muls in the Rabin block)
  passed inside the 200 s-per-declaration kernel budget; cold full pass of
  the five files ≈ 36 min, which CI now pays on every push.

* **S5 registration + audit**: `CharpolyDimN` and the five weight files in
  `MathProof.lean`, `defaultTargets`, CI list; `tools/tauceti_audit.sh`
  clean (no `set_option`/`#eval`/`meta`/`native_decide` anywhere in the new
  modules); `MathProof/AxCheckDecide.lean` on Modal: **409 decide certificates
  audited, 0 depending on more than `propext`** (up from 109 — the five new
  files add ~300 propext-clean certificates).

* **S6 bookkeeping**: README (Maeda section: `2 ≤ dim ≤ 10`, 54 weights,
  dims ≤ 5 keep the Galois-group statements; layout line), docs landing
  page (card retitled "weights 24–134"), AGENTS.md layout entry with the
  measured costs, this entry.

Invariants kept: no ancestor of the heavy `MaedaGalois5Defs` chain touched;
generated files never hand-edited (`gen_maedan.py --check` byte-identical);
every certificate is `decide +kernel` / `norm_num` / `eval_det`, and the
audit target stays propext-only.  Natural follow-ups, recorded as the next
blueprints: the Galois-group half for dims 6–10 (Frobenius cycle types +
`MaedaPermCriterion`), Hecke commutativity → "T_m is a polynomial in T₂"
(uses these 54 irreducibilities), and the T₃ twin run.
