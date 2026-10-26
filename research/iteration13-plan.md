# Iteration 13 plan — Lehmer's question for the weight-16…22 eigenforms (resumable)

Checkpoint file: resume at the first stage not marked DONE.

## Problem

`S_k(SL(2,ℤ))` is one-dimensional for k = 12, 16, 18, 20, 22, 26, spanned by
`Δ·E_{k−12}`.  Nonvanishing of the coefficients ("Lehmer's question") is open
for every one of them.  Toolkit: generic Mordell + Lehmer reduction
(`EigenLevelOne`), congruence `a_k ≡ σ_{k−1} [MOD num(B_k)]` from
`E_k − H ∈ S_k` (H = product of E₄, E₆ of weight k, rank-one ⇒ multiple of f),
sieve on primes, initial segment up to the least prime in the bad class.

| k  | G = E_{k−12} | H        | ℓ (mod)        | β = −2k/B_k        | first bad prime |
|----|--------------|----------|----------------|--------------------|-----------------|
| 16 | E₄           | E₄⁴      | 3617           | 16320/3617         | 21701           |
| 18 | E₆           | E₄³E₆    | 43867          | −28728/43867       | 263201          |
| 20 | E₄²          | E₄⁵      | 174611=283·617 | 13200/174611       | 1746109         |
| 22 | E₄E₆         | E₄⁴E₆    | 77683=131·593  | −552/77683 (11 cancels) | 1087561    |

## Stages

1. [DONE] `EigenLevelOne.lean` (generic Mordell/Lehmer, `eq_smul`).
2. [DONE] `BernoulliHigh.lean` (B₁₃…B₂₂ by recurrence chain; 49 s).
3. [DONE] `LehmerWeight16.lean`: congruence mod 3617, sieve,
   `a16_ne_zero_of_lt_21701`.
4. [DONE] `LehmerWeight18.lean` (template of 16).
5. [DONE] `LehmerWeight20.lean`, `LehmerWeight22.lean` (G is a product; two-prime
   moduli; congruence via ℤ-divisibility + coprime cancel).
6. [DONE] Weight 26 (gcd(25, 657930) = 5: five bad classes) — optional.
7. [DONE] Log / README / docs / AGENTS; commit.
