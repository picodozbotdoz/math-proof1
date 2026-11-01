# BLUEPRINT 2 — LehmerCoverage: exact verified coverage below 2³² + the 131072 decision

Iteration 22, steering priority 2.  Authored by the orchestrator 2026-11-02
from `research/iteration22/probe2-lehmer-coverage/FINDINGS.md` — read it
first; it holds every number cited below, the script, and the cross-check
methodology.  This blueprint DEEPENS on BP1 only in process (same gate
discipline), not in content.

## 0. Objective / non-objectives

**Objective.**  Turn Lehmer-axis folklore into exact, reproducible, partly
kernel-verified numbers:

1. `research/iteration22/lehmer-coverage/STUDY.md` — the exact coverage study:
   `U(B) = #{n < B : ∃ bad prime p ∣ n}` with `bad := prime, p > 65536,
   p % 691 = 690`; exactness via `70481² > 2³²` (every `n < 2³²` carries a
   bad factor at most once ⇒ `U(B) = Σ_{bad p < B} ⌊(B−1)/p⌋` below 2³²);
   headline (measured, exact): **uncovered(2³²) = 3 894 333 ⇒
   τ n ≠ 0 verified for 4 291 072 962 of 4 294 967 295 indices below 2³²
   (99.9093 %)**; bad primes in (65536, 2³²] number exactly 294 618
   (li(2³²)/690 = 294 615, ratio 1.00006); first bad prime 70481
   (Lean-known).
2. Small **kernel-verified anchors** in a new light module
   `MathProof/Tau/LehmerCoverageCount.lean`: the bad-prime filter at 2¹⁸
   (284 candidates → 17 primes → `U(2¹⁸) = 23`), optionally 2²⁰
   (1 423 → 98 → `U(2²⁰) = 227`) — `decide +kernel`, no `set_option`,
   light deps only.
3. The **131072 decision memo**: monolithic decide projects ~110–125 GiB
   (~1.8× the 64 GiB stop-rule) and ~850–950 s kernel; gain only
   +0.0053 pp coverage (5 bad primes eliminated) + segment 70481→134053.
   Default decision: **descope** (surface to operator); reopen only on
   explicit steering with a Bench-staged prototype (< 64 GiB/declaration).

**Non-objectives.**  No monolithic 131072 attempt inside this iteration; no
Mathlib bump; no heavy-module edits (`LehmerPacked` untouched); no new Modal
resources; counts beyond 2⁴⁰; no change to registered heavy statements.

## 1. Reuse map (two columns)

**Mathlib-at-pin**: nothing needed beyond what `LehmerSieve691` already uses
(`Nat.Prime` decides, `Nat.Prime.modEq`…; the module already contains
`bad_residues`-style kernel decides to imitate).

**TauCeti**: no Lehmer/nonvanishing/sieve content (FINDINGS §5) — nothing.

**Own library**: `LehmerSieve691.prime_dvd_sigma_iff` (the `p % 691 = 690`
characterization), `LehmerPrimeGrand` statement (the covered set's exact
shape), `LehmerPrimeReduction` prime-power lemma; probe artifacts at
`/home/doz/tmp/math-proof1-temp/probe2/` (script, npy, log — copy into the
repo at G1: /tmp is wipe-prone).

## 2. Module layout

* `research/iteration22/lehmer-coverage/` — STUDY.md, `bad_prime_sieve.py`,
  `bad_primes_2p32.npy` (2.4 MB), run log.
* `MathProof/Tau/LehmerCoverageCount.lean` (light, imports only
  `MathProof.Tau.LehmerSieve691`-tier light deps): per-bound theorems
  `bad_primes_le_2p18 : {p | p.Prime ∧ p ≤ 2^18 ∧ p % 691 = 690} = {…17
  literals…}` (list equality by `decide +kernel` over a candidate filter —
  candidates = numbers ≡ 690 [MOD 691] in (65536, 2¹⁸]), plus
  `uncovered_2p18 = 23` (Σ ⌊(2¹⁸−1)/p⌋ decide), optional 2²⁰ twin.
  Statement style: plain `Nat` arithmetic; the count statement phrased as an
  explicit integer equality, NOT a `Finset.card` over a predicate (kernel
  cost).
* Registration: trio only if the 2¹⁸/2²⁰ decides measure < ~2 min each on
  Modal; else root-only + note.

## 3. Verification plan

Modal `--file` green per artifact; `tauceti_audit.sh`; combined AxCheckDecide
(+2 decides, 0 > propext); the STUDY numbers must regenerate byte-identically
from the committed script (rerun in G1; log both outputs in the STUDY).

## 4. Stage gates (one green-commit session each)

* **G1 study port + regeneration** (script + npy + STUDY.md committed; rerun
  log matches; first-bad-prime sanity = 70481 = Lean-known gap).
* **G2 anchor decides**: 2¹⁸ (then 2²⁰ if < ~120 s kernel — measured, not
  assumed; descope to 2¹⁸ otherwise).
* **G3 131072 memo** (numbers + recommendation; SURFACE to operator via
  WAVE-TRACKING + session summary — steering stop-rule honored).
* **G4 bookkeeping** (research-log entry; README Lehmer paragraph update
  with the 99.9093 % headline; docs landing page if it states coverage).

## 5. Risks / fallbacks

* AP-sieve off-by-one (the probe's own start-index bug, caught by
  cross-check): keep the triple cross-check (formula vs direct marking vs
  70481 anchor) as a committed test in the script.
* Filter-decide kernel cost at 2²⁰ unknown until measured: G2's descope.
* npy binary in repo: 2.4 MB is fine; also gzip the decimal list as text.

## 6. Provenance (cold-executable)

This file; `research/iteration22/probe2-lehmer-coverage/FINDINGS.md`;
`MathProof/Tau/LehmerSieve691.lean` (statement shapes + decide style);
`MathProof/Tau/LehmerPrimeGrand.lean:29` (covered set); AGENTS.md +
CODING_STANDARDS.md.  Base commit in WAVE-TRACKING.md.

## Lessons learnt

Same binding set as BP1 (audit before code; exact-integer cross-checks;
commit green; WORKLOG; inbox polls).  Plus the probe's own: never trust a
sieve's first output — cross-check against an independently known anchor
(here: 70481).

## CORRECTIONS (implementer, 2026-11-01, evidence: G1 regeneration)

- §0/§2 candidate count at 2^18 is **285** (k = 94..378), not 284; the
  downstream numbers (17 primes, U(2^18) = 23) are unchanged.
- FINDINGS §2.2 census cell "2^30 → 116,788 bad primes" is wrong: exact
  **78,715** (li(2^30)/690 ≈ 78,843).  All U(B) values were and remain
  correct; the census table in `research/iteration22/lehmer-coverage/STUDY.md`
  §3 supersedes.
