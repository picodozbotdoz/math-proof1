# Probe 2 — Lehmer coverage below 2³²: exact sets, exact counts, 131072 projection

Status: fact-finding complete, 2026-11-01.  Everything below is measured or
read from Lean source; the counting scripts and data live in
`/home/doz/tmp/math-proof1-temp/probe2/` (`bad_prime_sieve.py`,
`bad_primes_2p32.npy`, `run_full.log`).  All counts are **exact** (integer
arithmetic, triple cross-checked), not Monte Carlo.

---

## 1. Exact verified sets (read from the Lean, not comments)

Definitions.  `bad prime` := prime `p > 65536` with `p % 691 = 690` (the sole
escape class of the mod-691 sieve above the dense kernel bound 65536).

### 1.1 The covered set C (kernel-verified, unbounded)

`MathProof/Tau/LehmerPrimeGrand.lean:29` (heavy, Modal-verified, `#print axioms`
clean — printed at build):

```lean
theorem tau_ne_zero_of_prime_factors_le_65536_or_mod {n : ℕ} (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ 65536 ∨ p % 691 ≠ 690) : tau n ≠ 0
```

So the covered set is **C = {n ≥ 1 : every prime factor p of n satisfies
(p ≤ 65536) ∨ (p % 691 ≠ 690)}** — no bound on n, no condition on exponents
(Lehmer's prime-power lemma `tau_prime_pow_ne_zero`,
`MathProof/Tau/LehmerPrimeReduction.lean:125`, removes exponents).  Its kernel
anchors are `LehmerPacked.tau_prime_ne_zero_of_le_65536` (packed decide,
~63 GiB) and `LehmerSieve691.tau_prime_ne_zero_of_mod`.

Uncovered (still-open-to-conjecture) set: n divisible by at least one bad
prime.  Complement within [1, B): `U(B) = #{n < B : ∃ bad p, p ∣ n}`.

### 1.2 `LehmerGrand.lean` (iteration 11 — superseded but equal on [1, 2³²))

- `tau_ne_zero_grand` (line 36): divisor-indexed fusion, `∀ p a, p.Prime →
  0 < a → p^a ∣ n → (p ≤ 65536 ∧ p^a ≤ 2^32) ∨ ¬ 691 ∣ σ₁₁ (p^a)` ⇒ `τ n ≠ 0`.
- `tau_ne_zero_of_lt_two_pow_32` (line 50): `0 < n < 2^32`, every prime factor
  `p > 65536` has `p % 691 ≠ 690` ⇒ `τ n ≠ 0`.  Proof shows internally that a
  factor `p > 65536 = 2^16` appears to exponent 1 in any `n < 2^32`.
- `tau_of_4294967295_ne_zero`: `τ (2^32 − 1) ≠ 0`.
- Needs the ~144 GiB `LehmerPow32` chain; `LehmerPrimeGrand` reaches the same
  coverage below 2^32 (and beyond) at less than half the cost — it is the
  statement to quote.

### 1.3 `LehmerSieve691.lean` (light, CI) — the sieve classes

- `tau_ne_zero_of_not_dvd_sigma`: `691 ∤ σ₁₁ n → τ n ≠ 0` (line 44).
- `lehmer_zero_dvd_sigma`: any counterexample n has `691 ∣ σ₁₁ n` (necessary
  condition, line 55).
- `prime_dvd_sigma_iff` (line 73): for p prime, `691 ∣ σ₁₁ p ↔ p % 691 = 690`
  (kernel decide `bad_residues`: x = 690 is the **only** residue < 691 with
  `1 + x^11 ≡ 0 [MOD 691]`).
- `tau_prime_ne_zero_of_mod` (line 94): every prime `p ≢ 690 [MOD 691]` of
  arbitrary size has `τ p ≠ 0`.
- `prime_pow_dvd_sigma_iff` (line 187): for p^11 ≢ 1 [MOD 691], badness of
  `p^(a+1)` is periodic in a — root-of-unity classification (not needed below
  2^32: bad p appears only to the first power there).
- Showcases in Lean: `tau_two_pow_ne_zero_sieve` (a ≤ 64),
  `tau_of_65537_ne_zero`, `tau_of_2147483647_ne_zero` (Lucas–Lehmer).

### 1.4 `LehmerUnbounded.lean` (light)

- `tau_ne_zero_of_prime_pows` (Mordell lift: prime-power blocks suffice),
- `tau_ne_zero_of_forall_prime_pow {B}` (parametric: nonvanishing on
  `{1..B}` ⇒ all n whose prime-power divisors are ≤ B; unbounded family).

### 1.5 `LehmerPacked.lean` (heavy, Modal) — the dense bound

- `tau_ne_zero_of_le_16384`, `tau_ne_zero_of_le_65536` (lines 1252, 1275):
  `1 ≤ n ≤ 65536 → τ n ≠ 0`, by `decide +kernel` on the packed-bignum
  pipeline mod `P = 999999937`.
- `tau_prime_ne_zero_of_le_65536` (line 1283) — the prime seed used by
  `LehmerPrimeGrand`.
- Options on the decides: 16384 needs `set_option maxRecDepth 1000000` +
  `maxHeartbeats 8000000` (lines 1242–1243); 65536 needs
  `maxHeartbeats 8000000` (line 1267).  **Yes, the 65536 decide needed the
  heartbeat lift** (default 200000 ≈ 200 s kernel; measured kernel wall of
  the 65536 decide ≈ 421 s = 570 s module − 149 s for the 512+16384 part;
  8,000,000 is ~19× headroom over that).
- `prime_gap_691_65536_70481` is in `LehmerPrimeGrand.lean` (line 35): no
  prime in (65536, 70481) is ≡ −1 [MOD 691] (7 candidates k = 94..100,
  `interval_cases <;> norm_num` — elaborator, not kernel-decide, but
  `norm_num`-verified).  `tau_ne_zero_of_lt_70481` (line 47): unconditional
  `τ n ≠ 0` for `0 < n < 70481`.

### 1.6 In Lean vs in comments

Everything quoted above (sets, sieve class, bounds 16384/65536/70481, the
gap) is *proved in Lean* on this branch.  Comments-only claims: the "~18 GiB /
~63 GiB" cost annotations (measured numbers, not theorems), and the
`LehmerUnbounded` docstring's "28 305-digit primorial" remark.  **The counted
coverage numbers in §2–§3 of this file are Python, not Lean** — §3.3 proposes
the small kernel anchors that would change that.

---

## 2. Exact counts (computed, cross-checked)

### 2.1 The no-overlap identity (why exact counting is easy)

Smallest bad prime = **70481** (kernel-consistent: exactly the bound of the
Lean gap theorem; my independent sieve agrees).  `70481² = 4,967,571,361 >
2^32 = 4,294,967,296`.  Hence **every n < 2^32 has at most one bad prime
factor, to the first power**, and for any B ≤ 2^32:

    U(B) = #{n < B : divisible by a bad prime} = Σ_{bad p < B} ⌊(B−1)/p⌋   (EXACT)

Verified empirically: formula vs direct multiple-marking agree at
B = 2^24 (8,055), 2^25 (18,158), 2^26 (40,226).  **No SPF sieve is needed
below 2^32**; the requested 2^26 segmented-SPF route reduces to marking
multiples of the 5,694 bad primes below 2^26 (40,226 marks total).

### 2.2 Headline numbers (exact)

| B | bad primes in (65536, B] | uncovered U(B) | covered | coverage |
|---|---|---|---|---|
| 2^18 | 17 | 23 | 262,120 | 99.991226% |
| 2^20 | 98 | 227 | 1,048,348 | 99.978352% |
| 2^21 | 204 | 599 | 2,096,552 | 99.971437% |
| **2^26** | **5,694** | **40,226** | **67,068,637 / 67,108,863** | **99.940059%** |
| 2^28 | 21,125 | 190,208 | 268,245,247 | 99.929142% |
| 2^30 | 116,788 | 870,897 | 1,072,870,926 | 99.918891% |
| **2^32** | **294,618** | **3,894,333** | **4,291,072,962 / 4,294,967,295** | **99.909328%** |

First bad primes: 70481, 92593, 96739, 105031, 120233, 134053, 145109,
167221, 179659, 182423, 186569, 187951 …; largest ≤ 2^32 is 4,294,967,161.
Top contributors to U(2^32): 70481 alone accounts for 60,937 n; the first 5
for 228,333 (5.9%); the first 1,000 for 53.0%.

### 2.3 Primes in the progression (asked: exact ≤ 2^28 + asymptotic for 2^32)

- Exact `π(2^28; 691, 690) − π(65536; 691, 690)` = **21,125** bad primes in
  (65536, 2^28].  (`π(65536; 691, 690) = 14`: primes 1381, 5527, 8291,
  12437, 22111, 29021, 30403, 34549, 37313, 42841, 51133, 53897, 58043,
  62189 — harmless, covered by the dense 65536 verification.)
- Exact in (65536, 2^32]: **294,618**; full `π(2^32; 691, 690)` = 294,632.
- Asymptotic `li(x)/φ(691)` = `li(x)/690`: li(2^28)/690 = 21,205 (ratio
  0.9962), **li(2^32)/690 = 294,615 vs exact 294,632 (ratio 1.00006)**.

### 2.4 Densities

- Exact uncovered density at 2^26: 0.0599414%; at 2^32: **0.0906720%**.
- `Σ 1/p` over bad primes: (65536, 2^28] = 0.00074227; (65536, 2^32] =
  0.00093598 (vs U(2^32)/2^32 = 0.00090672 — the ⌊⌋ sum is the exact one).
- First-order Mertens-AP estimate `(ln ln x − ln ln 65536)/690` at 2^32 gives
  0.1005% — right order, off by the AP-constant; always quote the exact count.
- The uncovered density grows only double-logarithmically: analytically
  ≈ 0.133% at 2^40, ≈ 0.201% at 2^64 (context only).

### 2.5 Validation summary

1. First bad prime 70481 = the Lean-proven gap bound (independent agreement).
2. Formula vs marking cross-check at 2^24/2^25/2^26: exact match (after fixing
   a start-index bug in my first sieve version — the cross-check caught it;
   negative numpy slice indices wrap silently, cf. "a red build under-reports").
3. Miller–Rabin (deterministic 12-base) audit: all 98 bad primes < 2^20 and a
   random 3,000-sample of the 294,618: zero false primes; all ≡ 690, all
   > 65536; endpoints prime.
4. `li(x)/690` agreement to 6·10⁻⁵ relative at 2^32.

---

## 3. Feasibility of the exact count (and small kernel anchors)

### 3.1 Measured throughput (this machine, single thread, numpy 2.2.4)

Segmented AP sieve of the **whole range (65536, 2^32]** — 6.22 M candidates
swept by the 6,542 primes ≤ 65536 in 9 segments: **0.2 s** (~31 M
candidate-prime-tests/s; ~2.2·10^10 values/s of range).  The entire script
(cross-checks at 2^24–2^26 + full 2^32 enumeration + all counts + saves)
ran in **0.57 s** wall, < 300 MB RSS.  A pure-Python fallback would be
~10^3× slower (≈ 10 min) — still trivial.

### 3.2 Modal extrapolation

At the measured rate, even 2^40 (1.58 B candidates, 9.2·10^36… practically:
segments of 2^29, ~2–3 min numpy single-thread) fits a 4-CPU lean_check-style
container with >100× margin.  **Recommendation: run the exact count at 2^32
locally (already done, above); no Modal run is needed at all.**  If a Modal
provenance run is desired, use 2^36 (seconds) — anything up to 2^40 fits the
≤ 2 h budget by orders of magnitude.  This is a study computation; the
artifact to keep is the script + the .npy list + the log, referenced from the
study note.

### 3.3 Small kernel-verified anchors (what could make counts Lean-checked)

The counting identity needs three Lean ingredients, two of which are cheap:

1. **Bad-prime list literal** (the sieve, kernel-decided).  Candidates
   `691k+690`, k = 94..1516 for the range (65536, 2^20]:
   `(List.range 1423).filter (fun k => (691*k+690).Prime) = [<98 literals>]`
   as one `decide +kernel`.  Cost estimate: 1,423 `Nat.Prime` kernel trial
   divisions at ≤ 1020 divisors each ≈ 10^6–10^7 small steps — my estimate
   **1–5 min kernel, few GiB** (uncertain; the project's light budget is
   ~200 s kernel / few GiB, and light modules may not lift heartbeats — see
   gate below).  A 2^18 version (284 candidates, 17 primes) is certainly
   light and is the natural first rung.
2. **No-overlap lemma** (light, no decide): `70481² > 2^32` (or > 2^20 for
   the anchor bound) ⇒ the sum formula — `omega`/`norm_num` arithmetic +
   the §2.1 argument formalized over a literal list.
3. **Count statement**: `∑ p ∈ badPrimes, (2^20−1)/p = 227` — 98 divisions
   of ≤ 7-digit literals, trivially kernel-decidable; then
   `covered_2p20 = 2^20 − 1 − 227` as the first kernel-verified coverage
   **count** in the project (uncovered 227 of 1,048,575).

Gate: measure the filter-decide cost first in a Bench-style module (or on
Modal via `lean_check.py --file` with an unregistered scratch module); if it
exceeds the default heartbeat budget, **descope to 2^18** (284 candidates,
certainly light) or split the k-range across declarations.  Alternative
cheaper anchor that reuses an existing pattern: a `prime_gap_691_*` theorem
for (2^20, next) style bounds via `interval_cases <;> norm_num` — elaborator
cost only.

---

## 4. 131072 packed attempt — projection

### 4.1 What the source actually allows (two surprises, both favorable)

- **No slot widening needed.**  `convSum_lt` (`LehmerPacked.lean:869`) is
  *stated* for `length ≤ 65536` with the numeric decide
  `65536 * P * P < 2^80`, but the arithmetic holds far beyond:
  `131072·(P−1)² ≈ 1.31·10^23 < 2^80 ≈ 1.209·10^24` (9.2× margin; width 80
  actually saturates near d = 2^20).  The 131072 extension needs only the
  hypothesis relaxed (65536 → 131072) in `convSum_lt`, `packedMul_getD`,
  `deltaPacked_eq`, `tauOf_ne_zero_of_packed`, `tauResList_eq_tauZMod` plus
  one new numeric decide `131072 * P * P < twoW`.  (The research log's
  "slot base saturates at 65536" remark is about the lemma statement, not
  the arithmetic.)
- **`etaList` already has the capacity**: the pentagonal entry machinery is
  proved for indices ≤ 174762 ≥ 131071 (`sqrt_bound_174762`,
  `pentRes_eq`), i.e. iteration 6 left exactly this headroom.

### 4.2 Memory projection (the stop-rule verdict)

Measured calibration points (research log iteration 6, Modal):
- module with 512+16384 decides: 149 s wall, **17.46 GiB** peak;
- adding the 65536 decide: 570 s wall, **62.85 GiB** peak (2 CPU / 96 GiB
  request).  Bench corroboration: 60.1 GiB (`BBenchPackedBal`).

Incremental slope: (62.85 − 17.46) GiB / 49,152 entries ≈ **0.92 MiB per
entry** beyond the 16384 plateau.  Projection for a single monolithic
`packed_nonvanishing_131072` decide:

- linear-in-d model: 62.85 + 0.92 MiB · 65,536 ≈ **120 GiB**;
- d·log d model: ≈ 112 GiB.  Either way ≈ **110–125 GiB**.

**This is ~1.8× over the steering stop-rule (> 64 GiB per single decide) —
SURFACED.**  Note the infra could physically do it (Modal memory is soft;
`LehmerPow32` ran at 143.8 GiB), so this is a policy stop, not an infra one.
Also relevant: `research/memory-alerts.md` still lists the 65536 decide
(~63 GiB) as an OPEN, uninvestigated backlog entry.

### 4.3 Kernel wall-clock projection

65536 decide ≈ 421 s kernel (570 − 149).  Scaling roughly linear in d
(16384→65536 is 4× d for ~3.5–4× time): 131072 ≈ **850–950 s** kernel.
`maxHeartbeats 8000000` (≈ 8,000 s) likely still suffices (the 65536 usage
was ≈ 421 s ≈ 421k heartbeats); 16,000,000 for safety.  `maxRecDepth`
lift probably not needed (65536 didn't need it).

### 4.4 What 131072 would buy (the descope evidence)

Raising the dense bound 65536 → 131072 eliminates exactly the **5** bad
primes ≤ 131072 (70481, 92593, 96739, 105031, 120233):

- U(2^32): 3,894,333 → 3,666,000; coverage 99.90933% → **99.91464%**
  (+0.0053 percentage points);
- new unconditional initial segment 70481 → **134053** (first bad prime
  above 131072; needs a light 3-composite gap decide, k = 190..192 —
  same `interval_cases <;> norm_num` pattern as the existing gap theorem).

Cost side: ~120 GiB × ~15 min kernel + editing a heavy module and rebuilding
its 4 heavy descendants (`PowChain`, `LehmerPrimePower`, `LehmerGrand`,
`LehmerPrimeGrand` — note `LehmerPacked` is **not** an ancestor of the
MaedaGalois5 chain, so no 33-min chain rebuild).  **Recommendation:
DESCOPE the monolithic 131072 attempt** — the coverage lever below 2^32 is
no longer the dense bound (the uncovered mass is spread over 294,613 bad
 primes above 131072); the honest route past 64 GiB is a *staged-split
prototype in Bench/ first* (poly5 methodology: checkpoint each of the five
packed products and the nonzero check into separate declarations with literal
certificates, target < 64 GiB per declaration; one ~30–60 min Modal run to
measure) — attempt only if steering explicitly accepts the > 64 GiB surface
or the prototype lands under it.  Caveat for the prototype design: the
pipeline's intermediates are *single bignums* (10.5 Mbit ≈ 3.2 M decimal
digits at d = 131072), and a `term = literal` checkpoint still forces the
whole bignum in one declaration — the split must be at the *digit-list* level
(chunked `digitsBal` extraction, ~32 declarations), which is unproven
territory for the kernel evaluator's retention; that is exactly what the
Bench prototype must measure before any MathProof module is touched.

---

## 5. TauCeti survey (~/zcode-workdir/tauceti)

**No Lehmer / τ-nonvanishing / sieve-coverage content.**  Hits:

- `TauCeti/NumberTheory/ModularForms/LevelOne/DiscriminantEigenform.lean` — Δ
  as a normalized full Hecke eigenform; has `discriminant_qExpansion_coeff_mul`
  (coprime multiplicativity = Mordell structure) and
  `discriminant_qExpansion_coeff_prime_pow_add_two` (the prime-power
  recurrence) — the *structure* math-proof1's `Mordell.lean` exploits, but no
  nonvanishing program, no congruence mod 691, no τ computations.
- `LevelOne/QExpansion.lean` — only τ(2) = −24, τ(3) = 252 as explicit values.
- `Newforms/Satake.lean` — every "Ramanujan" hit is the Ramanujan–Deligne
  bound on Satake parameters (different topic).

Two-column verdict: nothing to port in either direction for Lehmer coverage;
TauCeti's `DiscriminantEigenform` is the natural *destination* if the project
ever wants its Mordell/Lehmer stack expressed against TauCeti's eigenform
API, but that is out of scope for iteration 22.

---

## 6. Blueprint shape (for the iteration-22 blueprint author)

**Objective.** Turn the verified-coverage story from folklore numbers into
(exact, reproducible) quantified results: (i) a study note with the exact
covered/uncovered counts and bad-prime census below 2^32 (done in this
probe — port into the repo), (ii) small kernel-verified count anchors, and
(iii) a documented, evidence-backed decision on 131072 (default: descope).

**Non-objectives.**  No monolithic 131072 decide without a measured < 64 GiB
Bench prototype and explicit steering sign-off (stop-rule §4.2); no Mathlib
bump; no changes to the MaedaGalois5 chain (untouched — `LehmerPacked` is
not its ancestor, but keep it that way); no new Modal resources (existing
`lean_check.py` only); counts beyond 2^40 out of scope.

**Module layout.**

- `research/iteration22/lehmer-coverage/` — study note (`STUDY.md`) +
  `bad_prime_sieve.py` + `bad_primes_2p32.npy` (294,618 entries) + run log.
  Copy from `/home/doz/tmp/math-proof1-temp/probe2/` (note /tmp wipe risk —
  AGENTS 2026-10-31: keep artifacts under the repo or the persistent temp).
- Optional new **light** module `MathProof/Tau/LehmerCoverageCount.lean`
  (imports only `LehmerSieve691`/`LehmerPrimeReduction`-level light deps —
  NOT `LehmerPacked`): the bad-prime filter decide + no-overlap lemma +
  `covered_2p20` count.  Add to `defaultTargets` + `MathProof.lean` + CI
  list only after the cost gate passes.  Follows CODING_STANDARDS (no
  `set_option`; decide +kernel style; run `tools/tauceti_audit.sh`).
- Nothing heavy in CI.  If the 131072 prototype ever proceeds: new
  `Bench/Packed/BBenchPackedBal131.lean` (generated, never imported), then a
  heavy `LehmerPacked` edit gated on its measurement.

**Stage gates (each ≈ one green-commit session).**

- G1 — Study note + data landed (port §2 tables, script, npy, validation
  section; update `research-log.md` iteration 22).  Trivially green.
- G2 — Count anchors: (a) light gap-decide rehearsal at 2^18 (284 candidates
  → 17 primes, `U(2^18) = 23`); (b) if (a) < ~120 s kernel, the 2^20 anchor
  (1,423 candidates → 98 primes, `U(2^20) = 227`, `covered_2p20` theorem).
  Descope: stop at 2^18 if the 2^20 filter-decide exceeds the default
  heartbeat budget (light modules cannot lift it); never import heavy deps.
- G3 — 131072 decision memo only (§4 numbers + this recommendation),
  unless steering explicitly re-opens it with the > 64 GiB surface accepted;
  in that case G3a = Bench prototype (chunked digit-list split, one Modal
  run, ≤ 96 GiB request), G3b = promote only if every declaration < 64 GiB.
- Final — research-log + README/docs sync: headline "τ n ≠ 0 verified for
  4,291,072,962 of the 4,294,967,295 indices below 2^32 (99.9093%), exactly
  counted; uncovered = multiples of the 294,618 primes ≡ −1 (mod 691) above
  65536, none below 70481".

**Key risks / gotchas for the implementer.**

- The AP sieve start-index bug (§2.5) is the classic silent-failure mode:
  always cross-check the formula against direct marking, and check the first
  bad prime equals 70481 (kernel-known) before trusting any list.
- Light-module decide budget: the 2^20 filter-decide cost is an *estimate*;
  measure before registering in `defaultTargets`.
- numpy negative-slice wraparound hides off-by-one starts; assert
  `0 ≤ start − lo_k < m`.
- Keep the `.npy` under 5 MB (294,618 × 8 B ≈ 2.4 MB — fine) and gzip the
  decimal list for the repo if preferred.
