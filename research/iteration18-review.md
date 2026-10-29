# Iteration 18 review — engineering lessons for Lean 4 + Mathlib

**Iteration 18**: Maeda's conjecture in full for `dim S_k = 5` — Galois group
`S₅` for weights 60, 64, 66, 68, 70, 74 (commit `3362d60`).  The mathematics
(quintic `S₅` criterion via the `F₂₀` sextic resolvent + discriminant) was in
place from part 1; this session was spent almost entirely on one engineering
problem: **how to certify two huge polynomial identities in Lean's kernel** —
the six `e_k(Θ)` coefficient identities of the resolvent (up to 10,780
monomials, degree 24) and the quintic discriminant identity (2,961 monomials).

What follows is the measured failure catalog, the method that worked, and the
transferable Lean/Mathlib lessons.

---

## 1. The `ring` tactic wall (measured)

The identities were first attacked with `ring`.  All variants died:

| attempt | atoms | granularity | outcome |
|---|---|---|---|
| monolithic resolvent identity | `Fin 5 → K` function applications | whole sextic | OOM, **323 GiB** (Modal runner killed) |
| monolithic product identity `∏(X − Θᵢ) = resolvent5 …` | same | whole sextic | `whnf` deterministic timeout even at **64 M heartbeats** |
| per-coefficient (`e₄` alone, 2,545 terms) | same | one Y-degree | > 85 GiB, killed |
| per-coefficient (`e₁`–`e₃`) | scalar `x0 … x4 : K` | one Y-degree | **passed** (2.5 GB, ~6 min each) |
| `e₄` (2,545 terms), scalar | scalar | one Y-degree | > 85 GiB, killed |
| discriminant identity (2,961 terms) | both | whole | > 46 GiB, killed |
| `MvPolynomial` + `decide` | Mathlib | trivial probe | **never terminates** (kernel-irreducible; 600 s timeout on a toy product) |

Conclusions:

* `ring`'s cost is **not** proportional to the expanded term count.  It is the
  normalization of deeply nested *products of large sums* that explodes; the
  same identity re-associated (Horner-style) is orders of magnitude cheaper.
* Heartbeat limits do not help — the failure mode is **memory**, not time.
* The scalars-vs-`Fin`-atom distinction matters at the margin (e₁/e₂ passed
  only in the scalar world) but does not remove the wall.
* Mathlib's `MvPolynomial` is *not* kernel-reducible: its arithmetic compiles
  to machinery `decide` cannot evaluate.  Do not reach for it to certify
  identities by `decide`.

**Rule of thumb**: `ring` is fine up to roughly **250 expanded terms / degree 8**
in the goal (measured ~2.5 GB); beyond that, plan a kernel-certificate route.

## 2. The method that worked (`Poly5` + Horner + `decide` certificates)

The final architecture (files `Poly5.lean`, `MaedaGalois5Id*.lean`, generator
`tools/gen_poly5.py`, splicer `tools/split_gal5.py`):

1. **Hand-rolled structural sparse polynomials** (`Poly5.lean`): a `Poly5` is
   a `List (Mon × ℤ)` in ascending monomial order; `Mon` is the exponent
   5-tuple.  Every operation is *structurally* recursive — the merge's second
   recursion axis goes through a trampoline `pMerge t ts (pAdd ts) q` that
   receives the continuation as an explicit function.  No well-founded
   recursion anywhere, so the kernel can evaluate it.
2. **Evaluation is homomorphic, unconditionally**: `PEval_pAdd`, `PEval_pMul`,
   `PEval_pPow` hold *without* sortedness hypotheses.  Sortedness is only
   needed for the `decide` to *succeed*; a non-canonical chain fails loudly
   and can never prove a false identity.
3. **Python verifies the math first**: the generator parses the Lean
   `resolvent5`/`disc5` text (regex over signed chunks and `k * a ^ 2 * b`
   factors), expands both sides to canonical dicts, and compares.  All math
   errors are caught in seconds in Python; only Lean plumbing errors remain.
4. **Certificates**: each side is rebuilt as a chain of `def`s over small
   literals (`e6LHS`, `e6RHS`), and `theorem e6dec : e6LHS = e6RHS :=
   eq_of_pBeq (by decide +kernel)` (with per-theorem `set_option
   maxHeartbeats`, scaled 8 M → 512 M by identity size) does the work.
   Transport to arbitrary `CommRing K` is a short `calc` through the hom
   lemmas plus a small `ring`.
   * **The decisive detail is `pBeq`**: deciding `p = q` on 10,780-term lists
     with `List`'s `DecidableEq` dies of kernel-stack "deep recursion" (one
     stack frame per element — it matches on the recursive call's *result*).
     `pBeq : Poly5 → Poly5 → Bool` is a *tail-recursive* scan — `&&` reduces
     to its second argument once the head comparison is `true`, so the
     kernel's whnf loop walks the list with constant native stack — and
     `eq_of_pBeq : pBeq p q = true → p = q` converts the boolean back into
     the equation.  This one lemma is what made `e₅`/`e₆` (5,621 / 10,780
     terms) decidable at all.
5. **Multivariate Horner for the composed side**: expanding the degree-24
   block term-by-term costs ~10⁹ kernel reductions; a Horner scheme over
   `va, vb, vc, vd, ve` is ~100× cheaper.  Each Horner node gets its own
   `def` + `eval` lemma, and the K-eval text accumulates as a nested
   expression.
6. **One heavy identity per module**:
   `MaedaGalois5IdBase → IdE4 → IdE5 → IdE6 → MaedaGalois5Identities`.
   Elaboration memory is *process-local*; module boundaries free it.  A single
   800 KB file holding everything could not elaborate even in 128 GiB.
   Light modules (`MaedaGalois5Defs`, `MaedaGalois5`, `MaedaGalois5Weights`)
   stay in CI; the heavy chain is Modal-only.

## 3. Definitions: gotchas that cost hours

* **Pair patterns block definitional reduction.**  `def PEval : … | (m, c) ::
  ts, x => c * mEval m x + PEval ts x` cannot unfold when the list head is a
  *variable* — the compiler does not know the cons cell is a pair.  Write
  `| t :: ts, x => t.2 * mEval t.1 x + PEval ts x` (projections) instead.
  Same for induction: `induction p with | cons h ts ih => obtain ⟨m, c⟩ := h`
  rather than `| cons (m, c) ts ih`.
* **A false goal in a "trivial" base case is a bug detector.**  `pMerge`'s
  base case was originally `[t]`, silently dropping the remaining input
  `ts`.  The proof then failed on `t.2 * mEval t.1 x = t.2 * mEval t.1 x +
  PEval ts x` — unsolvable *because false*.  When a base case of an eval
  lemma won't close, suspect the definition, not the tactic.
* **`match` on computed `Int` values is hard to rewrite against.**  Use
  `if t.2 + c' = 0 then … else …` (plain `if`, decidable prop) and drive it
  with `rw [if_pos h]` / `rw [if_neg h]`; cancellation of the negative
  coefficient then goes through `push_cast; ring_nf` or an explicit
  `have hcancel : … + … = … := by push_cast; ring`.
* **Dot-notation needs the head symbol's namespace.**  `((m, c) :: ts).PEval
  x` fails ("environment does not contain `List.PEval`"); write
  `PEval ((m, c) :: ts) x`.
* **Ordering instances**: a lexicographic order on nested pairs needs only
  trichotomy for the merge proofs.  Build the `DecidableRel` in tactic mode
  (`instance : DecidableRel Mon.lt := fun a b => by simp only [Mon.lt];
  infer_instance`) and prove the equal case with `Prod.ext h1 h2` /
  `Prod.ext_iff`.

## 4. Tactics: what actually worked

* **`simp only` beats `rw` chains on multi-instance goals.**  `rw` rewrites
  the first matching instance; after a `show`, the goal shape must match
  exactly.  `simp only [myDef, PEval_pAdd, PEval_pMul]` unfolds the def and
  applies every instance at once.  When a `show … = PEval a x * PEval b x`
  was phrased in "multiplied-out" form, `simp only [def, PEval_pMul]` closed
  the show-part even though `rw` had failed on the same content.
* **Trailing `ring` after every `simp` bridge, as `try ring` when some
  branches close fully.**  `simp` leaves pure associativity residuals
  (`a + (b + c) = a + b + c`); one `ring` cleans them.  But when *some* simp
  sets close the goal entirely, a bare `ring` errors with "no goals" —
  `try ring` is the robust emission for generated proofs.
* **`ring_nf` "made no progress" on a ring-shaped goal means the goal is
  already normal and false.**  This diagnosed the unused-simp-argument bug:
  the simp set contained both the `Theta` *defs* and the `Theta_eval`
  *lemmas*; the defs won, unfolding past the lemmas and leaving a wrong
  residual.  Generated simp sets must list defs and eval lemmas so that the
  lemmas fire first (or drop the defs).
* **`decide +kernel` is the only `decide` that matters for certificates**;
  plain `decide` uses the elaborator's evaluator and its result is not
  independently kernel-checked.  Wrap each in `set_option maxHeartbeats N in`
  sized to the identity (8 M for e₁ … 512 M for e₆).
* **`omega` eats `Nat.ModEq`** (the Sylow normalizer congruence case): after
  `rw [h] at hmod hNle` the hypotheses `Nat.card N ≡ 10 [MOD 25]`, `Nat.card
  N ≤ 10` close by `omega` directly.
* **`push_cast` whenever ℤ literals flow into `K`** — e.g. cancelling
  `(-c') * z + c' * z` after `rw [show t.2 = -c' from by omega]`.
* **`simp only [Mon.lt]` vs `unfold Mon.lt`**: `unfold` follows the projection
  chain into `ℕ` and breaks hypothesis types (`(↑a.1).lt ↑b.1` vs `a.1 <
  b.1`); `simp only` unfolds exactly the one layer.

## 5. Names: shadowing and Mathlib API drift

* **Inside `Mon.lt_trichotomy`, a recursive-looking call `lt_trichotomy a.1
  b.1` resolves to the theorem being defined**, not `Nat.lt_trichotomy`.
  The resulting error (argument type `(↑a.1).lt ↑b.1` vs `a.1 < b.1`) hides
  the cause.  Always qualify Nat-level lemmas inside order proofs.
* **Or-nesting bookkeeping**: proving `A ∨ B ∨ C` by nested `rcases` — the
  middle case is `Or.inr (Or.inl …)`, the right `Or.inr (Or.inr …)`; when
  branches swap the argument order, every hypothesis needs `.symm`.  An
  "invalid ⟨…⟩ notation: expected type could not be determined" error almost
  always means the `Or` depth is wrong, not the anonymous constructor.
* **API present in this Mathlib (v4.36.0-rc1)** — everything below was
  looked up the hard way; reuse:
  * Sylow/normalizer route: `Sylow.card_normalizer_modEq_card (p := 5)
    (n := 1) hzc` needs `[Finite G]` and `hzc : Nat.card ↥H = 5 ^ 1`;
    `Subgroup.card_le_of_le`, `le_normalizer`, `Subgroup.mem_normalizer_iff`.
    There is **no** `Subgroup.card`, **no** `Subgroup.index_ne_zero`, **no**
    top-level `Sylow.card_sylow_modEq_one`.  `index ≠ 0` is one line from
    `H.index_mul_card` + `Nat.card_pos`; `N = ⊤` from matching cards is a
    short hand-rolled lemma (`Fintype.bijective_of_injective_and_card` +
    `Subgroup.eq_top_iff'`).
  * `Nat.pow_le_pow_right` (core) takes the positivity argument *first*:
    `Nat.pow_le_pow_right (hx : n > 0) : i ≤ j → n ^ i ≤ n ^ j`.
  * `orderOf_dvd_iff_pow_eq_one`, `orderOf_eq_one_iff`,
    `exists_prime_orderOf_dvd_card'`,
    `Equiv.Perm.eq_alternatingGroup_of_index_eq_two`,
    `Equiv.Perm.closure_three_cycles_eq_alternating`,
    `Subgroup.sq_mem_of_index_two`,
    `IsGalois.card_fixingSubgroup_eq_finrank`, `IsGalois.mem_bot_iff_fixed`,
    `Gal.card_of_separable`, `IsGalois.of_separable_splitting_field`,
    `card_rootSet_eq_natDegree`, `Polynomial.mem_rootSet'`,
    `map_aeval_eq_aeval_map`, `Polynomial.coe_aeval_eq_eval`,
    `Rat.isSquare_intCast_iff`, `exists_integer_of_is_root_of_monic`
    (integral root theorem), `Fintype.equivFinOfCardEq`,
    `minpoly.eq_of_irreducible_of_monic`, `adjoin.finrank`,
    `irreducible_of_degree_le_three_of_not_isRoot`.
  * Tuple machinery: `Matrix.cons_val_zero/one/two/three/four` (in
    `Mathlib/Data/Fin/VecNotation.lean`) — **no `cons_val_five`**; extract a
    6-vector's component with `have h : ThetaVals x j = … := rfl` + `rw [h]`
    instead of simp lemmas.  To unroll `∏ i : Fin 6`, chain
    `Fin.prod_univ_castSucc` five times and close with `rfl` (there is no
    `Fin.prod_univ_six`).
  * `Prod.ext h1 h2` and `Prod.ext_iff` are core; `Equiv.sum_comp` reindexes
    sums under permutations (the theta-invariance arguments).

## 6. Generated-Lean hygiene

* **Lint generated Lean before full builds.**  The weights generator once
  emitted `disc5 ((a : ℚ) (b : ℚ) …)` — one extra paren wrapping *all five*
  arguments, parsing as application of a rational literal.  A paren-balance
  check (or a 30 s `lake env lean` on one section) catches this class
  instantly; a full Modal round trip does not.
* **Two variable conventions, two names.**  Generators that address both
  `x : Fin 5 → K` (write `x 0`) and scalar worlds (write `x0`) should carry
  both spellings as explicit lists (`VF` vs `V`); mixing them produced
  "unknown identifier / has type ?m" errors that looked like type-class
  failures.
* **Sign handling lives in the generator, not in Lean.**  `e_k = (−1)^k ·
  block`: scale the Horner terms by `(−1)^k` when emitting literals.  A
  wrong sign makes `decide` fail loudly (good) but costs a full Modal round
  trip to discover (bad).
* **Markers + regenerate**: heavy generated regions live between
  `/- BEGIN … -/` / `/- END … -/` markers with "regenerate, don't hand-edit"
  docstrings, and the splicer replaces marker-to-marker.  Never splice by
  searching for tactic text that also exists elsewhere in the file.

* **Nested-pair arithmetic is `rfl` but not simp-normal.**  Proving
  `mEval (m + n) x = mEval m x * mEval n x` starts with five explicit
  `have e0 : (m + n).1 = m.1 + n.1 := rfl` … `e4` component equations and
  then `simp only [mEval, e0, …, e4, pow_add]; ring`.  `simp` alone gets
  lost in `Prod.add` projections of 5-deep right-nested tuples.
* **`Bool`-returning comparators beat `DecidableEq` at kernel scale.**  This
  is the `pBeq` lesson generalized: anything that must be evaluated by
  `decide +kernel` on lists of thousands of elements should be a
  tail-recursive `Bool` scan + an `eq_of_…`/`of_…_eq_true` bridge lemma,
  never a direct `DecidableEq` instance.
* **Keep the assembly light.**  `MaedaGalois5Identities.lean` holds only the
  cheap assembly (`prod_six_expand`, `resolvent_prod_identity`,
  `resolvent_eval_theta`) and stays CI-able; every heavy `decide` lives in
  its own module of the `IdBase → IdE4 → IdE5 → IdE6` chain.  The
  light/heavy separation follows the repo's `defaultTargets` rule: heavy
  modules are in none of `defaultTargets`/`MathProof.lean`/CI.

## 7. Process: validation and compute

* **Read the previous session's logs first.**  `/tmp/maeda5/*.log` recorded
  the 323 GiB OOM and the whnf timeouts; without them we would have re-run
  multi-hour jobs to rediscover each failure.
* **Modal telemetry is the OOM predictor.**  `[telemetry] rss=` lines that
  double per interval with steady single-core CPU mean "dead end" — kill the
  run early instead of waiting for the runner to die at 300 GiB.
* **Local (4 CPU / 7 GB) is for probes ≤ ~5 GB; everything else is Modal.**
  Four parallel local Lean processes thrash the page cache and make even
  small probes look like hangs.  `LEAN_CHECK_MEMORY_MIB=131072` exists for
  the heavy identity modules.
* **Kill stale background chains.**  An orphaned `lake env lean` from a
  pre-fix file burned 30 CPU-minutes and its log file was read twice by
  mistake, confusing two consecutive diagnoses.  Track PIDs; kill by exact
  pattern; prefer `run_in_background` tool calls over `&` inside compound
  shell commands (which this harness may swallow).
* **Bisection works**: defs-only / no-decide / one-identity prefixes
  isolated the cost to the identity section itself and justified the module
  split.  A cheap decisive probe (the `MvPolynomial` toy `decide`) ruled out
  an entire library in 10 minutes.

## 8. Recommendations carried into Iteration 19+ (dim ≥ 6)

* Budget new identities with the measured `ring` threshold (~250 terms);
  anything larger goes straight to the `Poly5` certificate route.
* The Horner emitter and `chunks_to_terms` parser in `tools/gen_poly5.py`
  are dimension-agnostic in spirit but hard-code 5 variables; generalizing
  `Mon` to `Fin n → ℕ` (or per-dimension instantiations) is the cheap next
  step before `dim S_k = 6` work (weights 76…, `charpoly_dimN`).
* Keep the one-heavy-identity-per-module chain pattern; the identity chain
  order must match the import order, and the generator must emit the whole
  chain, not just the leaf.
* The `Sₙ` criterion scaffolding (`perm_normal_cases`, index lemmas,
  normalizer congruence) in `MaedaGalois5Defs.lean` is written for
  `Fintype.card α = 5` but most proofs only use 5 through cardinal
  arithmetic; check what generalizes to n = 6/7 before re-deriving.
