# Exact verified Lehmer coverage below 2³²

Iteration 22, blueprint `lehmer-coverage`, gate G1.  Status: **complete
(2026-11-01)**.  All numbers are exact (integer arithmetic, no Monte Carlo),
regenerated from the committed script `bad_prime_sieve.py` in this directory
(runtime ≈ 1.5 s, < 300 MB RSS); the full regeneration log is `run_full.log`,
the original probe run `run_probe.log`.  Every number below appears verbatim
in `run_full.log`.

Artifacts in this directory:

| file | content |
|---|---|
| `bad_prime_sieve.py` | the committed script (sieve + counts + audits) |
| `bad_primes_2p32.npy` | all 294,618 bad primes in (65536, 2³²] (int64, 2.3 MB) |
| `bad_primes_2p32.txt.gz` | the same list, one decimal prime per line |
| `run_full.log` | regeneration log (this study's numbers) |
| `run_probe.log` | the original probe-2 run log |
| `DECISION-131072.md` | the 131072 decision memo (gate G3) |

## 1. What is covered (the Lean statements)

`Ramanujan.tau_ne_zero_of_prime_factors_le_65536_or_mod`
(`MathProof/Tau/LehmerPrimeGrand.lean:29`, heavy, kernel-verified) states

```lean
theorem tau_ne_zero_of_prime_factors_le_65536_or_mod {n : ℕ} (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ 65536 ∨ p % 691 ≠ 690) : tau n ≠ 0
```

so the **covered set** is `C = {n ≥ 1 : every prime factor p of n satisfies
(p ≤ 65536) ∨ (p % 691 ≠ 690)}` — with *no bound on n* (Lehmer's prime-power
lemma `tau_prime_pow_ne_zero` removes the exponents).  Call a prime **bad**
when it fails both: `p > 65536` and `p % 691 = 690`.  The escape class is
exactly the residue 690 by `LehmerSieve691.prime_dvd_sigma_iff` (kernel
decide `bad_residues`: 690 is the only `x < 691` with `1 + x ^ 11 ≡ 0`).

The **uncovered count** below `B` is `U(B) = #{1 ≤ n < B : ∃ bad p ∣ n}`;
covered `= B − 1 − U(B)`.

## 2. The no-overlap identity (why counting is exact and easy)

The smallest bad prime is **70481** — independently kernel-known: it is
exactly the bound of `Ramanujan.tau_ne_zero_of_lt_70481` (the Lean gap
theorem; `prime_gap_691_65536_70481` proves no bad prime exists in
(65536, 70481)).  This script's sieve agrees (asserted in `run_full.log`).

Since `70481² = 4,967,571,361 > 2³² = 4,294,967,296`, **every `n < 2³²`
carries at most one bad prime factor, and only to the first power**.  Hence
for every `B ≤ 2³²`:

    U(B) = Σ_{bad p < B} ⌊(B−1)/p⌋        (EXACT — no inclusion-exclusion)

Cross-checked by direct multiple-marking at `B = 2²⁴, 2²⁵, 2²⁶` (formula =
marking at each: 8,055 / 18,158 / 40,226 — `match=True` in the log).  No
smallest-prime-factor sieve is needed below 2³².

## 3. Headline table (exact)

| B | bad primes in (65536, B] | uncovered U(B) | covered | coverage |
|---|---|---|---|---|
| 2¹⁸ | 17 | 23 | 262,120 | 99.991226 % |
| 2²⁰ | 98 | 227 | 1,048,348 | 99.978352 % |
| 2²¹ | 204 | 599 | 2,096,552 | 99.971437 % |
| 2²⁴ | 1,520 | 8,055 | 16,769,160 | 99.951988 % |
| 2²⁵ | 2,967 | 18,158 | 33,536,273 | 99.945885 % |
| 2²⁶ | 5,694 | 40,226 | 67,068,637 | 99.940059 % |
| 2²⁷ | 10,923 | 87,869 | 134,129,858 | 99.934532 % |
| 2²⁸ | 21,125 | 190,208 | 268,245,247 | 99.929142 % |
| 2²⁹ | 40,919 | 408,563 | 536,462,348 | 99.923899 % |
| 2³⁰ | 78,715 | 870,897 | 1,072,870,926 | 99.918891 % |
| 2³¹ | 152,290 | 1,846,162 | 2,145,637,485 | 99.914031 % |
| **2³²** | **294,618** | **3,894,333** | **4,291,072,962 / 4,294,967,295** | **99.909328 %** |

**Headline.**  `τ n ≠ 0` is verified for **4,291,072,962 of the 4,294,967,295
indices `1 ≤ n < 2³²` — 99.9093 %** — exactly counted.  The uncovered 3,894,333
indices are exactly the multiples (below 2³², each such n of exactly one) of
the 294,618 bad primes; the first bad prime is 70481, the last below 2³² is
4,294,967,161.

First bad primes: 70481, 92593, 96739, 105031, 120233, 134053, 145109,
167221, 179659, 182423, 186569, 187951, 192097, 194861, 212827, 216973,
233557, … (all 294,618 in `bad_primes_2p32.txt.gz`).  Contribution skew at
2³²: 70481 alone covers 60,937 uncovered n; the first 5 bad primes account
for 228,333 (5.9 % of U); the first 1,000 for 2,062,978 (53.0 %).

**Corrections vs the probe FINDINGS** (`../probe2-lehmer-coverage/FINDINGS.md`
§2.2 — regeneration caught two table cells): the 2³⁰ census cell said
116,788; the exact count is **78,715** (consistent with `li(2³⁰)/690 ≈
78,843`, ratio 0.9984; every U(B) cell and the 2²⁸/2³² census cells match).
The blueprint's "284 candidates" at 2¹⁸ is **285** (k = 94..378, §5 below).
The data files are unaffected (npy byte-identical to the probe's).

## 4. The bad-prime census and its asymptotics

- Exact bad primes in (65536, 2³²]: **294,618**; full `π(2³²; 691, 690)` =
  294,632 (the 14 below 65536 — 1381, 5527, 8291, 12437, 22111, 29021,
  30403, 34549, 37313, 42841, 51133, 53897, 58043, 62189 — are harmless:
  they are inside the dense kernel-verified bound).
- Dirichlet: `π(x; 691, 690) ~ li(x)/690`: at 2²⁸, 21,206 predicted vs
  21,125 exact (ratio 0.9962); at 2³², **294,616 predicted vs 294,632 full
  (ratio 1.00006)**.
- `Σ 1/p` over bad primes: (65536, 2²⁸] = 0.00074227; (65536, 2³²] =
  0.00093598 (vs exact uncovered density 0.00090672 — the ⌊·⌋ sum is the
  exact one; first-order Mertens-AP `(ln ln x − ln ln 65536)/690` at 2³²
  gives 0.1005 %, right order but off by the AP constant — always quote the
  exact count).  The uncovered density grows only double-logarithmically
  (analytically ≈ 0.133 % at 2⁴⁰, ≈ 0.201 % at 2⁶⁴; context only).

## 5. Small kernel-verified anchors (gate G2 data)

The AP candidates in (65536, B] are `v = 691·k + 690`:

- **2¹⁸**: k = 94..378 (**285 candidates**) → filter `(691*k+690).Prime`
  leaves exactly **17 primes**: 70481, 92593, 96739, 105031, 120233,
  134053, 145109, 167221, 179659, 182423, 186569, 187951, 192097, 194861,
  212827, 216973, 233557; `Σ ⌊(2¹⁸−1)/p⌋ = 3+2+2+2+2+12·1 = 23 = U(2¹⁸)`.
- **2²⁰**: k = 94..1516 (**1,423 candidates**) → **98 primes**,
  `U(2²⁰) = 227`.

These are the anchors formalized in `MathProof/Tau/LehmerCoverageCount.lean`
(bad-prime filter as a `decide +kernel` list equality over the candidate
range, the count as an explicit integer sum).

## 6. Validation summary (all committed in the script)

1. **70481 anchor**: first bad prime asserted equal to 70481, the Lean-proven
   gap bound — independent agreement between sieve and kernel.
2. **Formula vs direct marking** at 2²⁴/2²⁵/2²⁶: exact match (the probe's
   first sieve version had a numpy negative-slice start-index bug; this
   cross-check caught it, and the committed script asserts the start offset
   in range).
3. **Miller–Rabin audit** (deterministic 12-base, valid < 3.3·10²⁴): all 98
   bad primes < 2²⁰, a 3,000-random sample of the 294,618, and the last
   entry — zero failures; residue/size spot-checks pass.
4. **`li(x)/690`** agreement to 6·10⁻⁵ relative at 2³².
5. **Byte-identical regeneration**: `bad_primes_2p32.npy` regenerated by the
   committed script equals the probe's array (asserted at G1; log above).

## 7. Scope and non-goals

Counts are exact for every `B ≤ 70481²` (the identity needs no overlap;
beyond that a proper inclusion-exclusion or SPF sieve would be needed).
This study is Python-verified; the Lean-verified part is the small-anchor
module of §5 plus the pre-existing Lean theorems cited in §1.  The 131072
question (raising the dense bound past the 5 bad primes ≤ 131072) is decided
in `DECISION-131072.md` (gate G3): descope by default.
