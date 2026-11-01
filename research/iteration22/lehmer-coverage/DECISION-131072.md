# Decision memo: the monolithic 131072 LehmerPacked attempt

Iteration 22, blueprint `lehmer-coverage`, gate G3.  **Decision: DESCOPE the
monolithic 131072 `decide`** (default; surfaced to the operator per the
steering stop-rule).  This memo records the evidence; no code was written.

## 1. What "131072" means

Raise the dense kernel-verified nonvanishing bound of
`MathProof/Tau/LehmerPacked.lean` from 65536 to 131072 via one monolithic
`decide +kernel` (`tau_ne_zero_of_le_131072` in the packed-bignum pipeline,
mod `P = 999999937`, base 2⁸⁰).

## 2. What it would buy (exact, from the census in `STUDY.md` §3)

There are exactly **5 bad primes ≤ 131072** (70481, 92593, 96739, 105031,
120233); eliminating them:

- `U(2³²)`: 3,894,333 → **3,666,000**; coverage 99.90933 % → **99.91464 %**
  (+0.0053 percentage points);
- the unconditional initial segment `tau_ne_zero_of_lt_70481` extends
  70481 → **134053** (the first bad prime above 131072; the gap (131072,
  134053) contains only the AP candidates k = 190..192 = 131980, 132671,
  133362, all composite — a light `interval_cases <;> norm_num` gap theorem
  in the existing style).

## 3. Cost projection (measured calibration, research log iteration 6)

- Calibration: the module with the 512+16384 decides peaks at **17.46 GiB**
  (149 s wall); adding the 65536 decide raises it to **62.85 GiB**
  (570 s wall, ~421 s of it the 65536 kernel decide).  Bench corroboration:
  60.1 GiB (`BBenchPackedBal`).
- Incremental slope ≈ **0.92 MiB per entry** beyond the 16384 plateau ⇒ a
  monolithic 131072 decide projects to **~112–120 GiB** (linear and d·log d
  models bracket 110–125 GiB) — **≈ 1.8× the 64 GiB steering stop-rule**
  (> 64 GiB per single decide requires explicit operator sign-off).
- Kernel wall-clock ≈ **850–950 s**; `maxHeartbeats 8,000,000` likely
  suffices (65536 used ≈ 421 s ≈ 421k heartbeats).  Editing `LehmerPacked`
  also rebuilds its 4 heavy descendants (`PowChain`, `LehmerPrimePower`,
  `LehmerGrand`, `LehmerPrimeGrand`) — `LehmerPacked` is *not* an ancestor
  of the MaedaGalois5 chain, so no 33-min chain rebuild.
- Not an infra stop: Modal memory is soft (`LehmerPow32` ran at 143.8 GiB).
  This is a **policy stop**.
- Source feasibility is NOT the obstacle (probe-2 §4.1): `convSum_lt`'s
  width-80 arithmetic holds to d ≈ 2²⁰ (131072·(P−1)² ≈ 1.31·10²³ < 2⁸⁰ ≈
  1.209·10²⁴, 9.2× margin) and `etaList` already covers indices ≤ 174762 —
  the extension needs only hypothesis relaxations plus one new numeric
  decide `131072 * P * P < twoW`.

## 4. Why descope is the right default

The coverage lever below 2³² is no longer the dense bound: the uncovered
mass is spread over the 294,613 bad primes *above* 131072 (the first 5 carry
only 5.9 % of U(2³²)).  ~120 GiB × ~15 min of kernel for +0.0053 pp fails
any cost-benefit test against the stop-rule.

## 5. Reopen conditions (what a future attempt must do first)

1. Explicit steering sign-off accepting the > 64 GiB per-decide surface, OR
2. a **staged-split prototype in `Bench/` first** (poly5 methodology):
   checkpoint each of the five packed products and the nonzero check into
   separate declarations with literal certificates, target < 64 GiB per
   declaration; one ~30–60 min Modal run to measure.  Design caveat: the
   pipeline's intermediates are *single bignums* (10.5 Mbit ≈ 3.2 M decimal
   digits at d = 131072), so a `term = literal` checkpoint still forces the
   whole bignum into one declaration — the split must be at the *digit-list*
   level (chunked `digitsBal` extraction, ~32 declarations), which is
   unproven territory for the kernel evaluator's retention.  That
   measurement is exactly what the Bench prototype exists to make, before
   any MathProof module is touched.

Related backlog: `research/memory-alerts.md` still lists the 65536 decide
(~63 GiB) as an OPEN entry.
