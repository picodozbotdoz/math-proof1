# Lean Zulip post — ready to paste

Post in stream **#maths** (topic suggestion: *Ramanujan τ: kernel-decided
nonvanishing to 65536*). Copy everything below the line. The claims are
calibrated: it leads with the kernel-engineering result (the genuinely new
part for this audience), states the classical results as classical, and
invites corrections on prior art rather than claiming "first".

---

**Formalizing Ramanujan's τ in Lean 4: τ(n) ≠ 0 for n ≤ 65536, decided inside the kernel**

I'd like to share a small Lean 4 + Mathlib project formalizing the Ramanujan
tau function: https://github.com/picodozbotdoz/math-proof1

The headline I'm most curious to hear reactions to: **the project certifies
`τ n ≠ 0` for all `1 ≤ n ≤ 65536` by `decide +kernel` — no `native_decide`,
no external CAS, no `sorry`** — with an axiom audit (`#print axioms`) showing
the computational theorems depend on `propext` alone. To my knowledge this is
the furthest kernel-`decide` nonvanishing computation for τ; the 65536-level
check peaks around 63 GiB of kernel heap and ~570 s of wall time, so it is
built outside CI (the default build stays lean).

What's in the repo:

- `Ramanujan.tau` defined from the Euler product `Δ = q ∏ (1 - q^m)^24`, with
  truncation-stability lemmas and a hand-rolled, structurally-recursive
  coefficient-list arithmetic the kernel can actually reduce;
- the analytic bridge `(qExpansion 1 Δ).coeff n = τ n` to Mathlib's modular
  discriminant (via a submultiplicative polynomial 1-norm and summability on
  a disc), so Mathlib's analytic Δ and our algebraic τ agree;
- **Ramanujan's weight-12 identity** `691 • E₁₂ = 441 • E₄³ + 250 • E₆²` via
  the Sturm bound, and from it **Ramanujan's congruence**
  `τ n ≡ σ₁₁ n [ZMOD 691]` for all `n ≥ 1`;
- the small-modulus congruences: `τ n` even unless `n ≡ 1 [MOD 8]`, and
  `3 ∣ τ n` unless `n ≡ 1 [MOD 3]` (Frobenius collapse of the Euler product);
- first 21 values of OEIS A000594, each verified by `decide`.

On the engineering side, getting past n = 512 (which costs ~5 min / 6 GB and
was the previous ceiling) required packing each coefficient list into a
single `Nat` in base `2^80`, so a dense product becomes one GMP `Nat.mul`
inside the kernel, with soundness proved against Mathlib's
`Pentagonal.PowerSeries`. I wrote up a measured scaling study of *why* the
naive route dies (kernel suspension retention plus the `maxHeartbeats`
deterministic-timeout cap) and what the packed route costs at each size:

- study: `research/lehmer-mod-scaling-study.md` in the repo;
- research log: `research/research-log.md`.

Since the congruences are classical mathematics, I make no novelty claim
there — I'd genuinely welcome pointers to earlier formalizations (I did not
find a prior Lean formalization of the 691 congruence, but would be happy to
be corrected). Feedback very welcome, in particular on whether any of the
general lemmas (the 1-norm estimates, the Sturm-bound workflow, the
kernel-friendliness patterns) would be worth upstreaming to mathlib. And of
course: if you find the project useful, a GitHub star helps it get indexed
by Reservoir.

Thanks to the mathlib community — the project leans on Mathlib's
`Pentagonal.PowerSeries`, Eisenstein series, and modular-form infrastructure
throughout.
