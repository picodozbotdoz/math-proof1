# Code review — `dev/claude_review_1` vs `master` (iterations 12–16)

**Scope.** 11 commits (2026-10-26), 30 files, +8,110 / −10 lines, branched from
`master` = `36ae64f`. The branch is pushed as `origin/dev/claude` at the same tip
(`43e97f3`). It contains research-loop iterations 12–16: Lehmer's prime-power
lemma and the unbounded prime sieve (12), the weight-generic eigenform toolkit
and Lehmer sieves in weights 16–26 (13), and the full Maeda-conjecture line —
irreducibility of the `T₂` characteristic polynomial for every level-one weight
with `dim S_k ≤ 3`, then `dim S_k = 4`, then the Galois group `S₃`/`S₄` (14–16).

| commit | content |
|---|---|
| `3230d23` | Iter 12 m1: `LehmerPrimeReduction` (prime-power lemma, iff-reduction) |
| `59b5edc` | docs: `CLAUDE.md` |
| `90472d9` | Iter 12: `LehmerPrimeGrand` (`τ n ≠ 0` for `n < 70481`) + `lean_check.py` overlay fix |
| `38b83d3` | Iter 13 m1: `EigenLevelOne`, `BernoulliHigh`, `LehmerWeight16`; un-private B₅–B₁₂ |
| `f23b5e4` | Iter 13 m2: `LehmerWeight18/20/22` |
| `d6bffea` | Iter 13: `LehmerWeight26` |
| `e2c69c3` | Iter 14 m1: `MaedaWeight24` |
| `272229f` | Iter 14: `MaedaLevelOne`, `MaedaSmallWeights`, `tools/gen_maeda.py` |
| `8debca0` | Iter 14: `MaedaGalois` (S₃) |
| `a7c2a8e` | Iter 15: `MaedaDim4`, `MaedaDim4Weights` |
| `43e97f3` | Iter 16: `MaedaGalois4` (S₄) |

**Review method.** Every new Lean file was read in full and re-verified
independently of the research log: fresh builds against the pinned toolchain
(Lean `v4.36.0-rc1`), `#print axioms` audits, regeneration of the generated
files from `tools/gen_maeda.py`, and from-scratch numeric recomputation of every
baked-in constant (q-expansion coefficients, Hecke matrices, charpolys,
discriminants, resolvents, Bernoulli numbers, sieve residue classes, the 70481
prime gap). Docs and the research log were cross-checked theorem-name by
theorem-name. Details under *Verification evidence* below.

## Verdict

**Approve with minor doc fixes.** No blockers, no soundness concerns, not a
single `[MINOR]`-or-worse finding in any Lean proof file. Every new module is
**SOUND** (a few **SOUND-WITH-NOTES** for docstring/cosmetic reasons only). The
one item worth fixing before merge is the stale heavy-module list in
`CLAUDE.md` (`[1]` below); everything else is polish.

## What the branch establishes (mathematical summary)

1. **Lehmer reduction (iter 12).** `tau_prime_pow_ne_zero` — Lehmer's lemma
   `τ p ≠ 0 → τ (p^a) ≠ 0` for *all* a — proved elementarily by p-adic vs.
   archimedean dominance of the Mordell recurrence (if `p^6 ∤ τp`, carry the
   valuation `v ≤ 5` through `u a = p^{av}·w` with `w ≡ s^a [ZMOD p]`; if
   `p^6 ∣ τp` then `p ∈ {2,3}` is killed by the kernel-verified `τ 2 = −24`,
   `τ 3 = 252`, and for `p ≥ 5`, `τp² ≥ p¹² ≥ 4·p¹¹` wins archimedeanly).
   `lehmerConjecture_iff_primes` then reduces the full conjecture exactly to
   primes (correct iff-quantifier over all primes, no bound). On top:
   the any-exponent sieve `tau_ne_zero_of_prime_factors_le_65536_or_mod`
   (unbounded `n`, arbitrary exponents) and `tau_ne_zero_of_lt_70481` —
   **τ(n) ≠ 0 for every 0 < n < 70481**, past the dense 65536 kernel bound.
2. **Generic one-dimensional eigenform toolkit (iter 13).**
   `IsNormalizedRankOne k f a` *derives* the Hecke-eigenform property from
   rank-one spanning (`finrank_eq_one_iff_of_nonzero'` + the from-scratch
   `heckeTP_qExpansion_coeff` of `HeckeLevelOne.lean`) rather than assuming it,
   and lifts the whole Mordell/Lehmer apparatus weight-generically
   (`prime_pow_succ`, `mul_coprime`, `prime_pow_ne_zero` with the honest
   sharp side conditions `2^(k/2) ∤ a 2`, `3^(k/2) ∣ a 3` negated, `eq_smul`).
3. **Lehmer's question in weights 16–26 (iter 13).** For `f = Δ·E_{k−12}`
   (k = 16, 18, 20, 22, 26): coefficients *equal* a cast of an explicit ℤ
   convolution (strongest form of integrality), Ramanujan-type congruence
   `a n ≡ σ_{k−1} n` mod 3617 / 43867 / 283·617 / 131·593 / 657931, prime
   sieves (`a_p = 0` forces `p` into an explicit finite bad-class set — for
   weight 26, five classes via a kernel-verified `X⁵ − 1 = ∏(X − ζᵢ)`
   factorization in `ZMod 657931`), and unconditional initial segments
   (`a_k n ≠ 0` for all `n` below 21701 / 263201 / 1746109 / 1087561 /
   1315861). Composite moduli handled by per-prime sieving + coprime
   recombination; the weight-22/26 *reduced* moduli (numerator/11, /13) are
   not a shortcut but exactly the maximal ones — the full-numerator
   congruence is provably false there (e.g. `a26 2 ≡ 4 [MOD 13]` but
   `σ₂₅ 2 ≡ 3 [MOD 13]`), and the files prove only the true statement.
4. **Maeda's conjecture through dim 4 (iters 14–16).** For all 18 level-one
   weights with `2 ≤ dim S_k ≤ 4` — precisely {24, 28, 30, 32, 34, 38} (dim 2),
   {36, 40, 42, 44, 46, 50} (dim 3), and {48, 52, 54, 56, 58, 62} (dim 4; 26
   is dim 1 and 60 is dim 5, both correctly absent) — the
   characteristic polynomial of `T₂` (as `LinearMap.charpoly` of the actual
   operator, on a *proven* basis) is irreducible over ℚ; and for the six
   dim-3 and six dim-4 weights the Galois group of that polynomial is the
   full symmetric group (S₃, S₄): `galActionHom_bijective_of_cubic` (irreducible cubic
   + non-square discriminant ⟹ |G| divisible by 2 and 3, `≤ 6`, hence `= 6`)
   and `galActionHom_bijective_of_quartic` (irreducible quartic + irreducible
   resolvent cubic + non-square discriminant ⟹ `12 | |G| ≤ 24`, and the
   order-12 case is killed by an `A₄ = ⟨3-cycles⟩ ≤ f(F)` cardinality
   contradiction). Both are honestly stated as bijectivity of
   `galActionHom : Gal ⟶ Perm (rootSet ℂ)`, i.e. G ≅ S_n on the roots —
   exactly Maeda's claim, derived, not assumed.

## Area-by-area findings

### Build wiring, infra (clean)

- `lakefile.toml` `defaultTargets`, `MathProof.lean`, and the CI `build-args`
  list are in perfect sync: all 15 new light modules in all three; the one new
  heavy module (`LehmerPrimeGrand`, imports `LehmerPacked`) in none. This
  follows the AGENTS.md light/heavy rule exactly.
- `Weight12.lean`: pure un-`private`ing of the B₅–B₁₂ chain so `BernoulliHigh`
  can extend it; same namespace, no collision, no proof changes.
- `lean_check.py`: now also overlays files committed locally but unpushed
  (`git diff --name-only origin/master`, returncode-guarded, dedup via
  `dict.fromkeys`). Correct and needed for the Modal iterate-without-push loop.
- `tools/gen_maeda.py` → `MaedaSmallWeights.lean` / `MaedaDim4Weights.lean`:
  **regeneration is byte-identical** for both files (invocation for dim 4 —
  `python3 tools/gen_maeda.py 48 52 54 56 58 62` — inferred and confirmed).
  Trust architecture is right: Python only *proposes* numerals; every one of
  them lands inside a Lean obligation that recomputes it (`decide +kernel`
  against `seqP`/`seqPL`, `ring`-closed charpoly identifications, `simpa [P]`
  mod-ℓ reductions), so a Python bug breaks the build loudly rather than
  producing a verified-but-unrelated theorem. Weight enters at the type level,
  dimension is pinned by Mathlib's dimension formula, not by the generator.

### Iteration 12 (`LehmerPrimeReduction`, `LehmerPrimeGrand`) — SOUND

The three weight-generic recurrence lemmas are factored once and reused by both
the τ-specific and the generic-eigenform versions. `rec_ne_zero_of_valuation`
correctly needs no `t ≠ 0` hypothesis (`p ∤ s` forces it), covers `a = 0, 1`
uniformly (so `tau_prime_pow_ne_zero` at exponent 1 degenerates to the
hypothesis itself — no hidden assumption). The `70481` prime gap is
kernel-airtight: `interval_cases k` over exactly the seven `k ∈ [94, 100]`
with each candidate's compositeness by `norm_num`; independently reconfirmed
here (65644, 66335, 67026, 67717, 68408, 69099, 69790 all composite;
70481 = 691·101 + 690 prime). Notes: `LehmerPrimeGrand.lean:33` says "the
eight candidates" — the range 94 ≤ k ≤ 100 contains **seven** (proof
unaffected); the file's trailing `#print axioms` lines are informational.

### Iteration 13 (`EigenLevelOne`, `BernoulliHigh`, `LehmerWeight16–26`) — SOUND (some notes)

- `EigenLevelOne`: the eigenform property is *derived* via spanning — no
  assumption smuggled in. The ℤ↔ℕ power conversion at `heckeTP_qExpansion_coeff`
  (`cpow_sub_one` guarded by `weight_pos`) was checked for truncation traps:
  none. The `k ≥ 1` and rank-one hypotheses are non-vacuous exactly for
  k ∈ {12, 16, 18, 20, 22, 26}, matching the intended use.
- `BernoulliHigh`: all 14 values B₁₃…B₂₆ recomputed exactly from the
  recurrence in Python `Fraction` — all match (B₁₄ = 7/6, B₁₆ = −3617/510,
  B₁₈ = 43867/798, B₂₀ = −174611/330, B₂₂ = 854513/138,
  B₂₄ = −236364091/2730, B₂₆ = 8553103/6, odd ones 0). The chain is genuinely
  linear (each theorem uses only strictly smaller indices — no circularity).
- Weights 16–26: independently verified — all modulus factorizations and
  primality (3617, 43867, 283, 617, 131, 593, 657931 prime), the unit
  cancellations (16320, 28728, 13200, 552, 24 all coprime to their moduli),
  every Bézout-style exponent identity used to force `x = −1` (or the five
  fifth roots of unity for weight 26), that the five ζᵢ are *exactly* the
  solutions of `x⁵ = 1 [MOD 657931]` and the bad classes *exactly* the
  solutions of `x²⁵ ≡ −1`, `∏(X − ζᵢ) = X⁵ − 1` as polynomials, and that each
  segment bound is the least prime in its bad class. The congruence route is
  honestly Sturm-free (constant-term cancellation → cusp form; rank-one
  scalar pinned at the q¹ coefficient).
- Cosmetic notes: `LehmerWeight26.lean:10` docstring cites itself ("Same
  toolkit as … LehmerWeight26" — should be 16); `LehmerWeight20/22.lean:8`
  say "S₁₆…₂₆ are one-dimensional", false at k = 24 (harmless — each file only
  proves its own weight's rank); `LehmerWeight20` carries dead template code
  (`e6`, `e6_coeff`, `E6_coeff_zero'`, `E6_coeff_one'` unused there).

### Iterations 14–16 (Maeda line) — SOUND

- **Basis question handled correctly** — the subtle trap. The product family
  `Δ^{i+1}E₄^aE₆^b` is *linearly dependent* in weights k ≡ 2 (mod 12) (e.g.
  weight 38: three products, dim 2). The files never assume the family is a
  basis: `charpoly_dim2/3/4` re-derive linear independence from triangular
  q-expansions at every dimension, take spanning from a `hdim : finrank = d`
  hypothesis (discharged per-weight by Mathlib's dimension formula — weight 38
  picks the genuinely independent pair and drops the redundant third form),
  and compute `LinearMap.charpoly` of the operator itself via
  `charpoly_toMatrix`. So "the charpoly of T₂ on S_k" is at full strength, not
  a matrix caveat.
- **`seqP`/`seqPL` kernel-friendliness**: plain structural recursions
  (`List.map`, structural `conv`/`cpow`), no well-founded recursion anywhere;
  `seqP_getD` proves memo = recomputation for n < N. All kernel evaluates in
  the shipped files stay at indices ≤ 6 (inside the 21-entry proven τ table);
  the working `decide +kernel`s in the generated files are the operational
  proof of kernel-reducibility.
- **S₃/S₄ arguments complete.** Cubic: separable (char 0) → G ↪ S₃;
  3 ∣ |G| (prime degree); 2 ∣ |G| via `[ℚ(δ):ℚ] = 2` from δ² = nonsquare discr;
  coprime → 6 ∣ |G| ≤ 6. Quartic: 4 ∣ |G| (root), 3 ∣ |G| via θ = x₀x₁+x₂x₃
  root of the resolvent (minpoly = resolvent, `natDegree_dvd_finrank`),
  12 ∣ |G| ≤ 24; the order-12 (A₄) case is eliminated by `A₄ = ⟨3-cycles⟩ ⊆
  f(F)` with `|f(F)| = 6 < 12` — every 3-cycle is `f(g⁴)`, `g⁴ ∈ F` since F
  contains all squares. All Mathlib lemmas used (`Cubic.discr_eq_prod_three_roots`,
  `Equiv.Perm.eq_alternatingGroup_of_index_eq_two`, `Subgroup.sq_mem_of_index_two`,
  `Monic.irreducible_iff_natDegree'`, …) verified to exist with the needed
  shapes. `vieta4`/`disc4`/`resolvent` are the standard formulas, `ring`-proved
  internally.
- **Quartic irreducibility certificate** (`irreducible_quartic`): no-root +
  no-(u,v)-solution of the quadratic-factor equations, complete over
  `Ioc 0 (n/2)` factor degrees via `Monic.irreducible_iff_natDegree'`; the
  `omega` degree case-split at `MaedaDim4.lean:85` looks under-analyzed (dg = 3
  seems possible from `df + dg = 4` alone) but is complete because the Mathlib
  iff restricts `g.natDegree ≤ n/2` — worth a source comment for future
  readers.
- **All baked numbers independently reproduced from scratch** (Δ via the
  Euler product, E₄/E₆ via divisor sums, T₂ formula, exact triangular linear
  algebra, Leibniz determinant): **all 18 charpolys, all 12 discriminants, all
  6 resolvents, and every mod-ℓ certificate (irreducibility primes and
  non-residue witnesses) match the Lean literals exactly.**
- Note: `maeda_weight24` states irreducibility of `P24` over ℚ while the
  operator-charpoly identification lives in the adjacent
  `charpoly_heckeT2`; jointly full-strength, but there is no single fused
  "charpoly of T₂ on S₂₄ is irreducible" theorem. Acceptable.

### Docs — mostly accurate, one [MAJOR] and a few [MINOR]s

1. **[MAJOR] `CLAUDE.md` lines 48–50 (and line 22): stale heavy-module
   list.** "Heavy: `LehmerMod`, `LehmerPacked`, `LehmerPow32`,
   `LehmerPrimePower`, `LehmerGrand`, `AxCheck` — everything else is light"
   **omits `LehmerPrimeGrand`**, which this very branch adds as heavy
   (imports `LehmerPacked`; ~63 GiB decide; AGENTS.md correctly says "heavy,
   Modal"). Taken literally, an agent following CLAUDE.md could add it to
   `defaultTargets`/CI and break CI. Root cause is ordering: CLAUDE.md landed
   in `59b5edc`, one commit *before* `LehmerPrimeGrand` (`90472d9`), and was
   never refreshed. One-line fix; also update the line-22 "`#print axioms`"
   list.
2. **[MINOR] `docs/index.html`** ("Lehmer's question in weights 16–26" card):
   the moduli 283·617, 131·593 and 657931 are *not* "the numerators of
   B₁₆…B₂₆" — the proven (and maximal possible) moduli for k = 22, 26 are
   num(B₂₂)/11 = 77683 and num(B₂₆)/13 = 657931. Say "B_k numerators with the
   common factor cancelled". Same looseness in AGENTS.md's LehmerWeight
   paragraph ("congruence mod the `B_k` numerator … coprime cancel" covers 20
   and 22 but not 26) and Iteration-13 log prose (the table there is correct).
3. **[MINOR] `research/research-log.md`** iterations 15/16: "`k = 24–62
   except the one-dimensional 26`" — weight 60 (dim 5) is also excluded;
   as written the parenthetical implies 19 weights, not the (correct) "18".
4. **[MINOR] `tools/gen_maeda.py`**: docstring documents only the dim-2/3
   invocation (the dim-4 `48 52 54 56 58 62` invocation appears nowhere);
   no argparse (`--help` crashes with a traceback); 12-entry hard-coded τ
   table duplicating Lean's proven 22-entry `tauTable` (drift would fail
   loudly at `decide +kernel`, but it is the one duplicated data table);
   no self-validation — the external Lean build is the sole validator.
5. Notes: `README.md`'s `MaedaWeightK.charpoly_T2` / `maeda` / `maeda_galoisK`
   are pattern names — weight 24's actuals are `charpoly_heckeT2` /
   `maeda_weight24` (README's own weight-24 lines get this right); README's
   "Maeda*.lean (weights 24–62)" glosses over the 26/60 exclusions that the
   dim ≤ 4 qualifier carries; `docs/index.html` headline "65,536 — largest n
   certified by decide" now sits above the new n < 70481 card (defensible:
   dense decide vs derived segment, but reads stale); `EigenLevelOne` header
   result-list omits `eq_smul`; `MaedaWeight24`/`MaedaLevelOne` duplicate the
   `qL`/`qe_smul`/T₂-wrapper pair (deliberate — weight-24 predates the generic
   file); iteration13-plan says "B₁₃…B₂₂" where the delivered file has B₂₆.

Everything else in the docs checks out: all cited theorem names resolve; all
five segment bounds and five moduli match the Lean statements verbatim; the
18 charpolys in the log match the Lean `P` definitions digit-for-digit; every
irreducibility prime, non-residue witness and resolvent prime matches; the τ
table on the web page matches `tau_one…tau_twenty_one` exactly; cost figures
(481 s / 62.85 GiB for `LehmerPrimeGrand` vs 1759 s / 143.8 GiB for the
superseded `LehmerGrand`) are internally consistent with iterations 9–11;
the light/heavy wiring claims match `lakefile.toml`/CI reality; no overclaims
("Lehmer's conjecture" is always stated conditionally/bounded; Maeda never
claims weight 60 or "all weights ≤ 62").

## Verification evidence

- **Proof hygiene**: grep over all new files — zero `sorry`, zero
  `native_decide`, zero `axiom`, zero `set_option` overrides. `#print axioms`
  on ~20 headline theorems across the new modules: only
  `[propext, Classical.choice, Quot.sound]`.
- **Builds (pinned toolchain, fresh state)**: `EigenLevelOne` +
  `LehmerPrimeReduction` green on a Modal fresh-clone check; `BernoulliHigh`,
  `LehmerWeight16/18/20/22/26` (6–29 s each), `MaedaWeight24`,
  `MaedaLevelOne`, `MaedaGalois` (17 s), `MaedaDim4` (28 s), `MaedaGalois4`
  (25 s) + deps `MaedaSmallWeights` (201 s), `MaedaDim4Weights` (54 s) built
  clean locally against the warm Mathlib cache — confirming genuine
  light-module cost.
- **Independent numeric audit (Python, from scratch)**: all 18 T₂-charpolys
  recomputed two ways (triangular solve + Leibniz/Faddeev–LeVerrier, anchored
  on the hand-proven weight-24 ground truth) — match; all Bernoulli B₁₃–B₂₆ —
  match; all weight-16–26 sieve data (bad classes exactly, ζ₅ roots, least
  segment primes, factorizations, unit gcds) — match; 70481 gap — verified.
- **Generator**: regeneration byte-identical for both generated files;
  no hand-edits; deterministic.
- **Heavy module**: `LehmerPrimeGrand` re-verified on Modal during this review
  (fresh clone, 98304 MiB container): `Built MathProof.Tau.LehmerPrimeGrand`,
  both `#print axioms` clean (`[propext, Classical.choice, Quot.sound]`),
  wall 761 s with peak tree RSS 62.81 GiB (LehmerPacked decide 700 s of it) —
  consistent with the log's recorded 481 s decide / 62.85 GiB. CI cannot
  cover this module by design.
- **CI**: the run for the tip `43e97f3` (pushed as `dev/claude`) was still in
  progress at review time; the last completed run on the branch (iteration 13,
  `d6bffea`) passed in 1h 19m. The intermediate commits were never run through
  CI individually — the tip run covers their final state.

## Suggested follow-ups (non-blocking)

1. Fix `CLAUDE.md`'s heavy-module list (add `LehmerPrimeGrand`) — the only
   merge-relevant item.
2. Reword the two "numerators of B₁₆…B₂₆" phrasings (`docs/index.html`,
   AGENTS.md, iteration-13 log prose) to "B_k numerators with the common
   factor cancelled".
3. In the iteration-15/16 log entries, say "k = 24–62 except 26 (dim 1) and
   60 (dim 5)".
4. `gen_maeda.py`: document the dim-4 invocation; add a τ-table assert or
   read the values from Lean's table; optional argparse.
5. Cosmetic: "eight candidates" → "seven" (`LehmerPrimeGrand.lean:33`);
   `LehmerWeight26.lean:10` self-reference; drop dead `e6` code in
   `LehmerWeight20`; a comment at `MaedaDim4.lean:85` explaining the
   `Ioc 0 (n/2)` completeness.
