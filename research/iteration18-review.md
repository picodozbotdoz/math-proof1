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

---

# Part II — review of the τ / Lehmer / Weight-12 kernel-computation session

Source: the working session that produced `MathProof/Tau/Basic.lean`
(Ramanujan τ + verified list arithmetic), `MathProof/Tau/Lehmer.lean`
(kernel-verified nonvanishing to 128) and `MathProof/ModularForms/Weight12.lean`
(`691 • E₁₂ = 441 • E₄³ + 250 • E₆²` via the Sturm bound).  Part I's theme was
*certificate scale*; this session's theme is *kernel reducibility and API
reconnaissance*: every failure below was a `decide`/`rfl` that could not
evaluate, a name that does not exist in this Mathlib, or a definition that
compiled into something the kernel cannot unfold.

## 9. Definitions: structural recursion is a kernel contract (the `Acc.rec` trap)

* **Multi-pattern recursion on *different* arguments compiles to well-founded
  recursion, silently.**  `psub` was first written with four patterns —
  `psub [] (b :: bs) = (-b) :: psub [] bs` (recursing on arg 2) alongside
  `psub (a :: as) [] = a :: psub as []` (recursing on arg 1).  No structural
  decrease exists on a single argument, so the equation compiler emitted
  `Acc.rec`.  `#eval` still produced the *correct* values (the compiler
  evaluates fine); every `decide`/`rfl` failed with the signature

  > `reduction got stuck at match (deltaCoeffs 1).getD 0 0, 1 with | Int.ofNat a, Int.ofNat b => match decEq a b …`

  That message is *the* Acc.rec symptom: a wrong value would also get stuck,
  so the failure mode is silent — correct math, broken kernel.
* **Diagnostics that pinpoint it, in order of cost:** `#print psub` (body
  starts with `Acc.rec`), `example : psub [1] [0] = [1] := by rfl` (fails),
  `#reduce psub [1] [0]` (prints the explosion).  Bisection over subterms
  (`shiftBy` ok → `pneg` ok → `psub` stuck) found the culprit in minutes.
* **Fix: recurse structurally on exactly one argument.**  The asymmetric
  case moved into a helper — `pneg : List ℤ → List ℤ` (negation, structural)
  — so `psub [] l => pneg l` no longer recurses on `l`.  Every list function
  in the τ pipeline (`padd`, `pscale`, `pshift`, `pmul`, `psub`, `shiftBy`,
  `pow24`) is now structural; this is the rule AGENTS.md records as
  "Kernel-reducibility is the central engineering constraint".
  Part I's `pBeq` lesson (tail-recursive `Bool` scan) is the same contract at
  larger scale; here it bites even at 3-element lists.
* **Probe every kernel-target function immediately after defining it.**  The
  trap was caught only after ~600 lines of proofs depended on `psub`.  A
  two-line probe — `example : psub [1] [0] = [1] := by rfl` — belongs in the
  same edit that writes the `def`.  (Keep the probes out of the committed
  file, or in a comment.)

## 10. Type classes: the computable / noncomputable boundary

* `ℤ[X]` (`Polynomial`) carries **noncomputable** `Zero`/`Semiring`/`CommRing`
  instances in this Mathlib; any `def` that even mentions polynomial
  arithmetic fails with "failed to compile definition, consider marking it as
  'noncomputable' because it depends on 'instZero' / 'commRing' / 'semiring'".
  Same for `ModularForm.E` and everything built on it (`tauOf`, `tau`, `E₁₂`).
* **Keep two worlds and one bridge.**  All *computation* lives in `List ℤ`
  (`Pbuild`, `pow24`, `deltaCoeffs` — computable, kernel-reducible); all
  *mathematical meaning* lives in `ℤ[X]` / `ModularForm` (noncomputable,
  proof-only).  The bridge is a single pair: `L2P : List ℤ → ℤ[X]` (itself
  `noncomputable`) with `coeff_L2P : (L2P l).coeff i = l.getD i 0`, plus
  congruence lemmas (`coeff_mul_congr`, `coeff_pow_congr`) that transport
  prefix-coefficient agreement through `*` and `^`.  After the bridge, each
  τ value theorem is `change tauOf k = v; rw [tauOf_eq_getD …]; decide`.
* Prefer **stdlib `List` operations when they exist**: the custom `ptrunc`
  became plain `List.take` and the custom index theorems became `getD_take`
  — stdlib comes with the simp lemmas (`List.getD_cons_succ/zero`,
  `List.getD_nil`, `List.take_succ_cons`) and kernel-reduces fine.  Hand-roll
  only what stdlib lacks (`pmul`, `psub`, `shiftBy`).
* `let`-chains inside a `def` (`pow24` as five squarings) are kernel-friendly
  and keep the squaring structure explicit for the soundness proof.

## 11. Mathlib API reconnaissance (v4.36.0-rc1): names checked the hard way

Everything below was tried, failed, and re-looked-up; reuse the right column.

| wanted (stale/imagined) | actual in this Mathlib |
|---|---|
| `Polynomial.coeff_mul'` | `Polynomial.coeff_mul` — antidiagonal: `(p*q).coeff n = ∑ x ∈ Finset.antidiagonal n, p.coeff x.1 * q.coeff x.2` |
| `Polynomial.coeff_X_mul_succ` | `Polynomial.coeff_X_mul : (X * p).coeff (n+1) = p.coeff n` |
| `p * X^n` coeff lemmas | `Polynomial.coeff_mul_X_pow' : (p * X^n).coeff d = if n ≤ d then p.coeff (d-n) else 0` |
| `Nat.antidiagonal` | `Finset.antidiagonal`; for `norm_num` expansions: `Finset.Nat.antidiagonal_succ` (the form Mathlib's own `GradedRing.lean` uses) |
| `List.take_succ` (deprecated) | `List.take_add_one`; cons-shape: `List.take_succ_cons : take (i+1) (a::as) = a :: take i as` |
| `if_pos`/`if_neg` | deprecated for `ite_eq_left`/`ite_eq_right` (still work; rewrite fine) |
| old `Finset.sum_eq_single` | takes the non-membership side condition as a second explicit argument |
| `bernoulli 12` by `decide` | dies (deep recursion); `norm_num [bernoulli, bernoulli']` under `maxRecDepth 8000` + raised heartbeats |

* **Reconnaissance workflow that pays for itself:** a scratch file run
  directly against the built packages —
  `LEAN_PATH=$(ls -d .lake/packages/*/.lake/build/lib/lean | tr '\n' ':').lake/build/lib/lean lean /tmp/probe.lean`
  — gives `#check`/`#eval`/tactic experiments in seconds, no `lake build`.
  `#check` every name a proof will lean on *before* writing the proof.
* **Read Mathlib's own proofs first.**  `LevelOne/GradedRing.lean` already
  solves the exact Weight-12 shape (`E₄³ − E₆²` as a weight-12 form): the
  `ModularForm.mcast (by decide)` weight cast, `.pow`, `qExpansion_pow`,
  `FunLike.coe_sub`, `coe_mcast`, and `Finset.Nat.antidiagonal_succ` inside
  `norm_num` all came from mirroring that file instead of inventing lemmas.
  The search path that finds such files: `grep -rn <theorem> Mathlib/` for
  an external usage, then read its source.

## 12. `omega`/`subst`/`match`: the arithmetic-tactic boundary

* **`omega` treats `List.getD` and `length` applications as opaque atoms.**
  It cannot see `(a :: as).getD (i+1) 0 = as.getD i 0` or
  `length (a::as) = length as + 1`; the error prints them as atoms
  (`where b := (a :: as).getD 0 0`).  Order matters: `simp only
  [List.getD_cons_succ, …]` *first* to expose the `ℕ` arithmetic, then
  `omega`/`split_ifs`.  Inside `getD` statements, subtract-index rewrites
  come before `omega`: `rw [show i + 1 - (m + 1) = i - m from by omega]`.
* **`subst` refuses non-variable equalities** (`h : b.2 = 0`,
  `b : ℕ × ℕ` — "invalid equality proof").  Route through
  `Prod.ext_iff` + `omega`, or restate the hypothesis about components
  before `subst`.
* **`match i with | 0 => … | i+1 => …` beats `cases i`** inside cons-case
  proofs: the match gives clean successor contexts without
  `Nat.succ_eq_add_one` cleanup, and pairs naturally with
  `induction l generalizing i`.
* Impossible index cases close by **contradiction to `omega`**: after
  `rcases d with _ | d`, the branch with `hi : i + 1 < 0 + 1` but `i + 1 ≥ 1`
  is one `omega`.

## 13. Tactics: what worked, what misfired

* **`simp only` with *named, fully applied* proof terms.**  Rewrite rules
  like `ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL` fire
  syntactically; passing the raw lemma name relies on elaboration guessing
  the same instance arguments later.  Same trick for the Eisenstein
  hypotheses: define `def hk12 : 3 ≤ 12 := by norm_num` and `def hk12even :
  Even 12` once, use them in *every* statement — ad-hoc `by norm_num`
  creates distinct proof terms that block `rw`/`change` matches.
* **`rw` cannot unfold a `def`.**  `rw [etaPoly]` fails (not an equation).
  Bridge with an explicit rfl-equation: `rw [show Pbuild (d+1) 0 =
  List.take (d+1) [1] from rfl, h0]`, or use `simp [defName]` /
  `simp only [defName, lemmaA, lemmaB]`.
* **Eta-expansion when passing induction hypotheses to congruence lemmas:**
  "Application type mismatch … expected ∀ j_1 ≤ j" — wrap: `(fun n hn ↦ ih n
  (le_trans hn hj))` instead of `ih` bare.
* **Bool-vs-Prop bridging in `decide`-feeding predicates:** the goal
  `(l.getD i 0 != 0) = true` is not `l.getD i 0 ≠ 0` by `exact`; drive with
  `Bool.and_eq_true` in `simp only`, close residue with `simpa`.  (Same
  family as Part I's `eq_of_pBeq`: keep the Bool world and convert at the
  edge.)
* **`change`, not goal-altering `show`.**  The style linter flags `show` that
  changes the goal ("Please use `change` instead"); `change tauOf 0 = 1` is
  also self-documenting for computation theorems.
* **`try ring` for generated/mixed-depth tails** (Part I's lesson, re-earned
  here): some `simp only` sets close fully, leaving `ring` with "no goals".
* Unused-simp-argument warnings ("This simp argument is unused: ih") are real
  diagnostics — they usually mean an earlier simp lemma consumed the term and
  the intended one never fired.
* Dead ends happen: one interim version had a `linear_combination` placeholder
  with `sorry` (caught by grep before commit).  Never commit a proof sketch;
  `grep -c sorry` is part of the pre-commit check (CI enforces it too).

## 14. `set_option`, docstrings, and the style linter

* **Order is `set_option … in` *before* the docstring.**
  `/-- doc -/ set_option maxHeartbeats … in theorem` fails with the confusing
  "unexpected token 'set_option'; expected 'lemma'" — the docstring glues to
  nothing.  Working form:
  ```lean
  set_option maxRecDepth 100000 -- kernel evaluation depth for the checks below
  set_option maxHeartbeats 4000000 in
  -- reason: `decide` below evaluates 128 coefficients inside the kernel
  /-- docstring -/
  theorem …
  ```
* **`linter.mathlibStandardSet` *requires* a comment explaining any
  `maxHeartbeats` raise** ("Please, add a comment explaining the need for
  modifying the maxHeartbeats limit").  Budget one comment per raise.
* `decide` on the nonvanishing check needed `maxRecDepth 10000` already at
  N=64 ("maximum recursion depth has been reached") and
  `maxHeartbeats 4000000` at N=256.  A bare `set_option X v` (no `in`) scopes
  to the rest of the file — fine for a leaf module, avoid in library files.

## 15. Weight-12 / Sturm-bound idioms (Weight12.lean)

* **Modular forms of different weights are different types.**  `E₄.pow 3 :
  ModularForm 𝒮ℒ (4*3)`; view at weight 12 via `ModularForm.mcast (by decide)`.
  Define the linear combination once (`combo`) plus one bridge lemma
  (`combo_qExpansion_eq`) through `FunLike.coe_sub`, `coe_mcast`,
  `qExpansion_sub/smul/pow`; then the coefficient lemmas are pure
  `PowerSeries` arithmetic and close by `norm_num` (with
  `Finset.Nat.antidiagonal_succ`).
* **Sturm-bound application pattern:**
  `PowerSeries.nat_le_order _ 2 (fun i hi ↦ coeff_i)` → `lt_of_lt_of_le
  (by norm_num)` → `ModularForm.sturm_bound_levelOne_nat (k := 12) h` →
  `rw [sub_sub] at h0; exact eq_of_sub_eq_zero h0`.  The Sturm bound at
  weight `k` is `k/12`; coefficients `0..k/12` vanishing ⇒ form is zero.
* **Eisenstein coefficients are already in Mathlib:**
  `EisensteinSeries.E_qExpansion_coeff : (qExpansion 1 (E hk)).coeff m =
  if m = 0 then 1 else -(2k/B_k) * σ_{k-1}(m)` — no need to re-derive ζ/B
  plumbing.  Only `bernoulli 12` needs evaluating (`norm_num` + limits, §11).
* **Notation scopes:** `𝒮ℒ` needs `open scoped MatrixGroups`; `qExpansion`
  resolves under `open UpperHalfPlane ModularForm`.  Missing opens surface as
  "Unknown identifier `𝒮ℒ` / `qExpansion` … not possible to treat as
  implicitly bound variable" (because `relaxedAutoImplicit = false` — the
  lakefile option doing its job).
* **Product coefficient 1:** with `Finset.antidiagonal 1 = {(0,1),(1,0)}` by
  `decide`, `(A*B).coeff 1 = A.coeff 0 * B.coeff 1 + A.coeff 1 * B.coeff 0`
  is a two-line helper (`coeff_mul_one`); coefficient 0 is
  `A.coeff 0 * B.coeff 0` by `simp [PowerSeries.coeff_mul]`.

## 16. Kernel-cost budgeting and process

* Measured `decide` costs for the τ nonvanishing check (this machine, idle):
  N=64 ≈ 9 s (needs `maxRecDepth 10000`); N=128 ≈ 34 s — the shipped,
  CI-safe bound; N=256 ≈ 2 CPU-min standalone but > 5 GB RSS, and under a
  concurrently loaded 8 GB desktop it swap-thrashes (4 % CPU, TIME frozen,
  hours of wall clock).  **Ship the bound that builds reliably in CI, not
  the largest bound that ever verified once** — and record the larger
  verification in a comment (done: "The kernel computation for 256
  coefficients was verified locally but is kept out of the build").
* Thrash signature for kill-decisions: RSS grows past physical RAM, CPU % in
  single digits, accumulated CPU TIME barely advancing between `ps` polls.
  Kill early; re-run serialized later.  Never run two heavy `lean`
  processes concurrently on this machine.
* **`#eval` first, `decide` second.**  `#eval deltaCoeffs 20` (compiler,
  milliseconds) confirmed all τ values against OEIS A000594 *before* any
  kernel work; the `decide` failures were then provably plumbing, not math.
  The generator-verify pattern of Part I (`Python first`) in Lean-native
  form.
* Background `lake build` + `TaskOutput` polling works; check progress with
  `ps aux | grep <module>.lean` (RSS / CPU-TIME) rather than tailing logs the
  build only writes at the end.
* Commit granularity: the definition module (τ + 21 values) and the
  nonvanishing bound were separate commits (`b060851`, `8b4e954`) so a
  broken heavy `decide` never blocks the light history.

---

# Part III — the MaedaGalois5 debugging campaign (group theory, Main, Criterion)

*Lessons from the session that built `perm_normal_cases`,
`perm_no_index_three_four`, `alternating_no_index_two`, the quintic `S₅`
criterion (`galActionHom_bijective_of_quintic`), the permutation
representation `ρ`, the Sylow argument, and the six Galois instances —
roughly ten Modal verification rounds, each 8–17 minutes, before green.*

Part I documented the *kernel* wall (ring/`decide` on the identities).
This part documents everything *around* it: name resolution, tactic-level
matching, syntax ordering, generator bugs, and the verification workflow
that finally converged.

## 17. Name resolution: the misses, and what they cost

Every bullet below cost a full Modal round trip.  The pattern: a name that
*should* exist, doesn't (or lives elsewhere), and the cascade of follow-on
errors buries the root cause.

| tried (this session) | outcome | what actually worked |
|---|---|---|
| `Equiv.apply_inv_apply` | unknown constant | `Equiv.symm_apply_apply σ v : σ⁻¹ (σ v) = v` — as a *term*, not a rewrite (see §19) |
| `Finset.prod_univ_succ` / `Finset.prod_univ_zero` | unknown constant | **`Fin.`** `prod_univ_succ` / `prod_univ_zero` (`Mathlib/Algebra/BigOperators/Fin.lean`) |
| `orderOf_dvd_iff_pow_eq_one _ 5` | "Function expected" — the lemma has **all-implicit** binders (`variable {x} {n}`) | named args: `(orderOf_dvd_iff_pow_eq_one (n := 5)).mpr h` |
| `adjoin.finrank` / `ℚ⟮δ⟯` unknown | namespace not open | `open Module IntermediateField` (MaedaGalois4 already had it — diff the opens of the file you are mirroring) |
| `Algebra.algebraMap_injective` | unknown constant | `FaithfulSMul.algebraMap_injective R A` |
| `Subgroup.coe_injective` | unknown constant | `Subgroup.subtype_injective` (on `SubgroupClass.subtype`) or `Subtype.ext` |
| `Subgroup.val` | unknown constant | `Subgroup.subtype H` (or `congrArg (Subgroup.subtype H) h`) |
| `Subgroup.card_subgroup_dvd` | unknown constant | `Subgroup.card_subgroup_dvd_card` |
| `Fintype.bijective_iff_injective_and_card` **and** `Finite.…` and `Function.…` | all unknown in this Mathlib's module build | avoid: construct the `Equiv` directly with `match` + `Equiv.ofBijective ![…] (by decide)` on concrete tables |
| `Subgroup.index_ne_zero` | unknown constant | one line: `H.index_mul_card` + `Nat.card_pos` (as part II found) |
| `Sylow.card_sylow_modEq_one` as a top-level name | unknown constant (it lives in `namespace Sylow`, and `Nat.ModEq` unfolds to `%`) | `Sylow.card_sylow_modEq_one (p := p) (G := G)` used *directly as* `… % p = 1` |
| `Polynomial.map_ne_zero hφinj hne` | argument order: first explicit is `p ≠ 0` | `Polynomial.map_ne_zero hmon.ne_zero hφinj` |
| `hsep.map (algebraMap ℚ K)` | `Separable.map`'s `f` is **implicit** — passing it makes "Function expected" | `have hsepK : Separable (p.map f) := hsep.map` |
| `Subgroup.val` in `congrArg Subgroup.val h5H` | unknown | `congrArg (Subgroup.subtype H) h5H` |

**Meta-lesson.**  When mirroring an existing file (here `MaedaGalois4.lean`),
diff four things up front: the `open` line, the local attribute line
(`attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ` — needed for anything
touching `Gal.galActionHom p ℂ`), the section variables, and the exact
argument orders (`Separable.map`, `map_ne_zero`).  Every one of these bit us.

## 18. `rw` is keyed and syntactic: the failure catalog

`rw` matches on the head symbol of the lemma's LHS with *reducible* defeq.
Consequences, each observed here:

* **Associativity**: pattern `c ^ 3 * (c * c)` never matches a goal term
  `c ^ 3 * c * c` (left-assoc).  Write the `have hc` in the *same
  association* as the goal, or prove it `by group` and let `group` close.
* **Instance unfolding**: `σ⁻¹` elaborates to `Inv.inv σ`, the rewrite key of
  `Equiv.symm_apply_apply` is `Equiv.symm σ` — keys differ, `rw` fails even
  though the terms are definitionally equal.  Use the lemma as a *term*
  (`show σ⁻¹ (σ v) = v from Equiv.symm_apply_apply σ v` — `rfl` also fails
  here, do not try it) or `simp only` first.
* **Function-vs-multiset**: `rw [h6]` where `h6 : ∏ i : Fin 6, g i = …` does
  not fire against `Multiset.prod (Multiset.map g …)` (`Finset.prod` is a
  definition, not reducible).  Keep both sides in the same representation.
* **Numeral abstraction**: `rw [← hc]` with `hc : orderOf c = 5` inside a goal
  `(c ^ 5 : ↥H) = 1` abstracts the literal `5` **everywhere**, including
  `Fin 5` in `H : Subgroup (Perm (Fin 5))` — motive error
  `Subgroup (Perm (Fin _a))`.  Use `congrArg (fun n : ℕ => (c ^ n : ↥H)) hc`
  (typed exponent, no literal abstraction) or `.symm.trans` chains.
* **`simp only [lemma]` recursion with arith lemmas**: `simp only
  [Fin.prod_univ_succ]` on a six-factor product recursed into simp's internal
  polynomial normalizer (`evalMulProd`/`evalAdd`) and died at 8 M heartbeats.
  Unroll products with the *castSucc chain* + `rfl` instead
  (`Fin.prod_univ_castSucc` ×5 + `rfl`; no sixth step, no `prod_univ_zero`).
* **rw-at with bundled lists**: `rw [lem] at h4 h3 h2 h1 h0` (and the same for
  `simp only … at`) can fail part-way and poison the branch.  One hypothesis
  per call.  (Re-learned from iteration 15; the generator must emit it that
  way from the start.)

## 19. `set_option`, docstrings, and the parser

* `set_option a v in set_option b w in decl` **does not parse** at command
  level ("unexpected token 'set_option'; expected 'lemma'").  A *single*
  multi-option command does: `set_option maxHeartbeats 8000000 maxRecDepth 8000 in`.
* A docstring attaches to the *next command*: `/-- doc -/ set_option … in
  theorem …` fails with "expected 'lemma'".  Order must be
  `set_option … in /-- doc -/ theorem …` (and de-duplicate when a script
  inserts options — double docstrings also produce "unterminated comment").
* File-level `set_option maxHeartbeats 8000000` feeds *every* tactic: the
  same proof that OOM'd at file-level 8 M heartbeats ran in a fraction of the
  memory with the budget scoped to the two declarations that need it, plus a
  modest file-level default.  Scope budgets per declaration; keep
  `maxRecDepth` separate from `maxHeartbeats` in the same command.

## 20. Identity shape: ∏-form vs eval-form (elaboration-level, not kernel)

The `∏ i : Fin 6, (X - C (Θᵢ))`-form of the resolvent factorization never
elaborated: `whnf` deterministic timeouts at **64 M heartbeats**, even before
`ring` ran (the simp-only prelude expanding `resolvent5` and Vieta is itself
the bomb).  The fix that worked is *mathematically trivial*: restate as the
**eval form**, one factor at a time —

```lean
theorem resolvent_eval_theta (x : Fin 5 → K) (j : Fin 6) :
    (resolvent5 (va x) (vb x) (vc x) (vd x) (ve x)).eval (ThetaVals x j) = 0 := by
  fin_cases j
  all_goals simp only [resolvent5]; rw [eval_add, eval_mul, eval_pow, eval_X, eval_C]
    simp only [va, vb, vc, vd, ve, …]; ring
```

Six small `ring` goals instead of one 10,780-monomial one.  Downstream, the
resolvent root is transferred with `eval_mul`/`prod_eq_zero` (or, as landed,
`rw [← hRmap, ← hr, htv]; exact resolvent_eval_theta x j`).  Corollary of
Part I §1, but at the *elaboration* level: the same "many small goals beat
one big one" rule applies before the kernel is ever involved.

## 21. Tactics: fin_cases/decide, omega, and the free-variable wall

* **`decide` cannot prove goals with free variables** ("Expected type must not
  contain free variables").  `fin_cases σ` on `σ : Perm (Fin 5)` enumerates all
  120 cases, *then* each case is decidable.  But decide will also *refute*
  cases where the ∃-goal is false (e.g. `σ = 1`): filter with the hypotheses
  in a `first` cascade —

  ```lean
  fin_cases σ
  all_goals first
    | exact absurd (by decide) h1   -- σ = 1 case, decided off-line
    | exact absurd h5 (by decide)   -- wrong torsion, decided off-line
    | decide                        -- genuine case
  ```

* **`fin_cases` + `simp_all [table]`** proves injectivity of concrete lookup
  tables; but wrapping it in `Equiv.ofBijective f (by …)` with `f` mentioning
  a free `j` fails — build the six `Equiv`s by `match` on the index instead,
  each with a concrete table (`decide` closes each `Bijective`).
* **`decide` in a `def` body via `match`** keeps `cycPerm j` reducible on
  concrete indices, which is exactly what downstream `decide`s need.
* **`omega` and `∣`**: `t ∣ 5` with an atom `t` is within omega's reach, but
  `5 ^ n` is not.  Bounds like `125 ≤ 5 ^ n` + `5 ^ n ≤ 120` must be combined
  by `Nat.le_trans` + `exact absurd … (by norm_num)`, not omega.
* **`interval_cases n`** rewrites `n` everywhere *including inside `5 ^ n`* —
  pair each case with the right `pow_zero`/`pow_two` rewrites, or use the
  `Nat.lt_or_ge` + explicit cases structure.
* **`rcases … with h | h` name collisions**: reusing `h1` (a hypothesis) as an
  rcases binder name silently shadows it; later `rw [h1]` then hits the wrong
  term ("Unknown identifier" / wrong-shape rewrites downstream).
* **`Subgroup.coe_pow` has `H` explicit**: `Subgroup.coe_pow H c 5` — an
  `.symm` projection on `Subgroup.coe_pow c 5` fails with "Invalid field
  `symm`: The environment does not contain `Function.symm`" (the under-applied
  term is a ∀-function, so dot-notation resolves into it).

## 22. Definitions: the quintic Vieta sign, and C-atom hygiene

* **Quintic Vieta sign**: for `∏ i, (X − x i) = X⁵ + aX⁴ + … + e`, the
  constant coefficient is `e = −x₀x₁x₂x₃x₄` — **minus**, unlike the quartic
  (even degree).  Defining `ve x := x 0 * … * x 4` (plus) made `vieta5`'s
  hprod *mathematically false*, and `ring` failed with a residual that looked
  like a tactic bug.  `ring` failing on an identity you "know" is true is a
  sign-flip hunt, not a tactic hunt.
* **`C`-atoms**: `ring` treats `C (x 0 * x 1)` and `C (x 0) * C (x 1)` as
  unrelated atoms.  After unfolding coefficient-functions under `C`, push the
  map through with `simp only […, map_neg, map_add, map_mul, map_pow]` *before*
  `ring` (mirrors `vieta4`'s `simp only [map_add, map_mul]; ring`).
* **Bundled `simp only … at h₁ h₂ …` fails part-way** (the `d0` case here);
  per-hypothesis `have h : … := by …; simp only […]; norm_num; exact h` blocks
  are verbose but survive.
* **`noncomputable` is contagious through `@[no_expose]` instances**: in this
  Mathlib, `instance : Add R[X]` is `@[no_expose]`, so *any* def that builds a
  polynomial by `+` (here `resolvent5`) must be `noncomputable` — the error
  ("failed to compile definition … depends on 'instAdd'") otherwise takes a
  round trip to decode.  `decide`-proofs downstream are unaffected.
* **`set s := p.rootSet K` + `Fintype.equivFinOfCardEq`** is the clean way to
  get an indexed root tuple `x : Fin 5 → K` with `hx : ∀ i, x i ∈ s`,
  injectivity, and a roots-multiset conversion
  (`Multiset.count_eq_one_of_mem hnd …` on both sides).

## 23. Generated-Lean bugs (emitter class)

* **Missing commas in emitted lists**: `rw [q1_1 q1_2 q1_3 …]` — space-joined
  hypothesis names parse as *application* (`h11 h12` = `h11 applied to h12`),
  producing "Function expected" far from the real bug.  Emitters must `", ".join`.
* **Orphan docstring fragments** after scripted insertion: the "unterminated
  comment" error with balanced-looking text — scan comment depth
  programmatically (`/-` vs `-/` counting) before uploading.
* **Python-level shadowing**: two `def wrap` in the same emitter — the later
  definition silently wins and emits sign-less lines (a dropped `+` produces
  `e 6` juxtaposition = application errors inside Lean defs).  Keep one
  canonical helper; assert single definitions in the emitter.
* **JSON round-trip**: monomial keys come back as *strings* — normalize
  `tuple(int(d) for d in m)` at load, and remember the e↔(a,b,c,d,e) sign map
  `e1=−a, e2=b, e3=−c, e4=d, e5=−e` lives in the *emitter*, not the data.
* Regression discipline pays: dims 2–4 regenerating **byte-identically** after
  every emitter change caught two of these before any Modal round trip.

## 24. Process: the Modal verification loop

* **Bisection by scratch carving** (S5 / Resolvent / Main / Criterion
  sections, then B1/B2/C, then P1…P2m): each scratch keeps the same imports +
  file-level options so parse-level errors surface in ~2 min and the real
  errors localize to one section.  Ten rounds, each 8–17 min wall — the
  error maps, not the compute, are the bottleneck; batch *all* fixes per
  round instead of one-per-round.
* **Stub the expensive proofs** (`sorry` on the two big `ring`s) to get the
  rest of the file checked in the same round trip; run the expensive proofs
  in dedicated high-RAM runs (`LEAN_CHECK_MEMORY_MIB=98304`).
* **Memory signature of error recovery**: a run that elborates with unknown
  identifiers thrashes to 90–160 GiB RSS and produces garbage cascade errors;
  a clean run of the *same content* stays at 15–30 GiB.  Kill thrashing runs
  early (the file has a parse error you haven't seen yet), fix, re-run.
* **Build cache** (user-requested): `lean_check.py` now saves `.lake/build`
  as one tarball on the existing `lean-cache` volume keyed by local git HEAD
  and restores it before building — lake's own traces keep restores safe, a
  single sequential volume read/write avoids the many-tiny-writes stall, and
  `LEAN_CHECK_NO_CACHE=1` opts out.  First run still rebuilds (`[cache]
  empty`); every later run skips unchanged modules.
* **This host has 7 GB RAM**: never elaborate anything locally; grep Mathlib
  sources locally (cheap), compile on Modal only.

## 25. Carry-forwards

1. The eval-form identity pattern (§20) is the template for the dim ≥ 6
   resolvent/Dedekind work: state root-certificates per factor, never as
   product identities.
2. Emitter lint pass before upload: comma-join audit, comment-depth check,
   docstring/set_option order, single-definition check, and byte-identical
   regression of already-committed generated files.
3. The `first | exact absurd (by decide) h1 | exact absurd h5 (by decide) |
   decide` cascade is the reusable shape for any finite-case lemma with
   side conditions (e.g. future Dedekind/Frobenius cycle tables).
4. Keep `MaedaGalois5`-style files out of `defaultTargets` until the heavy
   identities are verified; the light group-theory + criterion layer
   (everything except the two rings) is CI-cheap and was reviewed first.

---

# Part IV — the closing session: identity chain, criterion port, weight certificates

*Lessons from the session that turned the Part I–III material into commit
`3362d60`: the five-module identity chain (`IdBase → IdE4 → IdE5 → IdE6 →
Identities`), the first successful compile of the `S₅` criterion
(`MaedaGalois5.lean`), the generated weight instances
(`MaedaGalois5Weights.lean`) and the `lean_check.py` build cache.  Every
error class below is quoted from the session's build logs; each fix is
what actually landed in the committed file.*

## 26. Corrections to Parts I–III (verified against the committed code)

Several earlier notes were written mid-campaign and turned out wrong or
superseded.  In each case the committed file is the evidence.

| earlier claim | what is actually true in this Mathlib / repo |
|---|---|
| §5: "there is no `Fin.prod_univ_six`" | **It exists**: `resolvent_eval_theta` opens with `rw [Fin.prod_univ_six]` and compiles.  The castSucc chain is not needed. |
| §5 / §17: "no `Subgroup.index_ne_zero`; hand-roll `N = ⊤` with `Fintype.bijective_of_injective_and_card`" | `Fintype.bijective_of_injective_and_card` is unknown, but you don't need it.  Mathlib has **`Subgroup.index_ne_zero_of_finite`** and **`Subgroup.eq_top_of_card_eq N hcard`**, and both hand-rolled wrappers were deleted. |
| §19: "`set_option a v in set_option b w in decl` does not parse" | It parses.  `MaedaGalois5IdE6.theta_e6` is `set_option maxRecDepth 100000 in set_option maxHeartbeats 512000000 in theorem …`.  The real culprit was a **docstring between** the two `set_option … in` lines, or before the first one. |
| §3: "drive `if` with `rw [if_pos h]` / `rw [if_neg h]`" | `if_pos`/`if_neg` are deprecated (§11).  The committed `Poly5` uses **`simp only [h, ↓reduceIte]`**, which also closes the `¬h` branch without naming the lemma. |
| §2: "splicer `tools/split_gal5.py`" | Deleted.  `tools/gen_poly5.py` writes the whole module chain directly, splitting on `@@CUT:…@@` markers. |
| §24: build cache "keyed by local git HEAD", saved after success | Superseded by one **rolling** `/cache/buildcache/latest.tar.gz`, saved after **every** run, including failed ones (see §33). |
| §17: Sylow congruence "used directly as `… % p = 1`" | For the normalizer version, `Sylow.card_normalizer_modEq_card (p := 5) (n := 1) hzc` has type `… ≡ … [MOD 5 ^ (1 + 1)]`.  It typechecks **as a term** against `Nat.card ↥N % 25 = Nat.card ↥H % 25`, because `Nat.ModEq` is `%`-equality and `5 ^ (1+1)` whnf-reduces to `25`.  State the target in the `% 25` form so that `omega` can use it. |

## 27. Kernel-certificate failures, and which knob fixes each

The first full `Identities` build (4225 s) failed with six errors.  Each
error class needs a *different* fix, so read the message before raising any
limit:

| message | real cause | fix |
|---|---|---|
| `(kernel) deep recursion detected` on `e5dec`/`e6dec` | (a) `List` `DecidableEq` uses one native stack frame per element (Part I §2); (b) **forcing `pMul p q` uses stack proportional to `len p`**.  The generator put the 2,445-term partial product on the left. | `pBeq` + `eq_of_pBeq`, and **`balanced_mul` always puts the smaller factor on the left**.  e5/e6 then had 25- and 218-term left factors (e4, which had passed, already had 218).  Raising `maxRecDepth` does not help: this is the kernel's native stack, not the elaborator's counter. |
| `(deterministic) timeout at «synthesize pending MVars», maximum number of heartbeats (200000)` on `e5lhs_eval` | Elaborating a ~100-factor product statement at the default budget. | A per-declaration `set_option maxHeartbeats N in`.  The generator now emits one for every `*_eval` / `theta_eK` lemma. |
| `failed to synthesize HPow K ?m.5128 ?m.7508 … maximum recursion depth has been reached` (×100, then `maxErrors`) on `theta_e6` | **Not a type-class problem.**  The 140-term, deeply right-nested statement exhausts the *elaborator's* `maxRecDepth` while unifying `binop%` trees; instance synthesis is simply where it ran out. | `set_option maxRecDepth 100000 in` on that one theorem, and only for k = 6, so the cached E4/E5 modules stay byte-identical (§33). |
| `Tactic decide proved that the proposition DLHS2 = dRHS is false` | **A math bug in the generator.**  It compared Δ = ∏(xᵢ − xⱼ) with the discriminant instead of Δ². | `theorem ddec : pMul DLHS2 DLHS2 = dRHS`.  This message is the best one in the catalog: it is definitive and costs nothing to read.  Never raise a limit in response to it. |
| `No goals to be solved` after `simp only […]` in `e1lhs_eval` | The `simp` set closed the k = 1 goal by itself. | The generator omits the trailing `ring` for k = 1 (or emits `try ring`, Part I §4). |
| `unexpected token 'end'; expected ']'` | Python string-building dropped a `]`. | The disc step became `simp only [disc5]; ring`.  Paren-balance-check generated text (§6). |
| ``rewrite failed: pattern (pMul ?p ?q).PEval ?x`` in the disc assembly | `rw [PEval_pMul]` in the wrong direction: the goal already had `PEval a x * PEval a x`. | `rw [h1, ← PEval_pMul]`.  When a hom lemma "does not fire", check the direction before the shape. |

**Rule.**  *Kernel* deep recursion means restructuring the data or
algorithm.  *Elaborator* recursion means `maxRecDepth`.  Heartbeats means
budget.  "decide proved … is false" means the math or the generator is wrong.
The four look alike in a 2,000-line log; classify each one before fixing anything.

## 28. Type classes and computability: the weight-certificate redesign

* **`decide` cannot evaluate anything built from `Polynomial`.**  The first
  `MaedaGalois5Weights` defined the resolvent certificate as `R := resolvent5
  a b c d e` and decided `∀ y : ZMod 41, (R.map …).eval y ≠ 0`.  Result:
  `failed to compile definition, consider marking it as 'noncomputable'
  because it depends on 'resolvent5'`, then `Tactic decide failed to
  reduce`.  The working shape has three parts:
  ```lean
  noncomputable def R : ℤ[X] := X ^ 6 + C (…) * X ^ 5 + … + C (…) * X ^ 0
  lemma hRint : resolvent5 … = R := by unfold resolvent5 R; norm_num
  lemma R_monic : R.Monic := by unfold R; monicity!
  def Rmod (y : ZMod 41) : ZMod 41 := y ^ 6 + ((… : ℤ) : ZMod 41) * y ^ 5 + …
  lemma noRootR : ∀ y : ZMod 41, Rmod y ≠ 0 := by decide +kernel
  lemma R_eval_cast (n : ℤ) : ((R.eval n : ℤ) : ZMod 41) = Rmod n := by simp [R, Rmod]
  ```
  The parts are an explicit noncomputable `ℤ[X]` (the proof world), a
  computable mirror function over `ZMod ℓ` (the kernel world), and a
  `simp` bridge.  This is Part II §10's "two worlds, one bridge", applied to
  a single certificate.  It is the same pattern the discriminant certificate
  (`Dval` + `nonsquare`) already used; copy the working sibling's shape
  before inventing a new one.
* **200-digit `ℤ` literals cast into `ZMod 41` are cheap for `decide
  +kernel`**: the kernel's GMP-accelerated `Nat`/`Int` literals reduce `%`
  natively.  You don't need to pre-reduce the literals in the generator.
* **`attribute [local instance]` does not travel.**  `MaedaGalois5.lean`
  declares `attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ`.  The
  Weights file, which imports it, failed with `failed to synthesize instance
  of type class Fact (Splits …)` at every `Gal.galActionHom … ℂ`.  Each file
  that mentions `galActionHom p ℂ` must re-declare the local instance.  The
  generator header now emits it.
* **Integer → rational root transport** (`exists_integer_of_is_root_of_monic`
  wants `aeval r R = 0` over `ℤ[X]`, while the hypothesis is over `ℚ[X]`):
  `rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, ← hR]`.  The cast lemma
  `aeval (m : ℚ) R = ((R.eval m : ℤ) : ℚ)` goes through
  `induction R using Polynomial.induction_on'` with `| add … => simp [ihp,
  ihq]` / `| monomial … => simp`.  Then `rw [hn, algebraMap_int_eq,
  eq_intCast, hE n] at hr'; exact_mod_cast hr'`.  Get the direction of `hn`
  from `obtain ⟨n, hn, -⟩` right first (`algebraMap ℤ ℚ n = r`).
* **Subtype vs `Set`**: `set s := p.rootSet K` must be typed as `Set K`
  where the API expects it.  `{w // w ∈ s}` and `↥(p.rootSet K)` are
  different *syntactic* types for `rw`, even though they are defeq.  Name the
  `Fintype.equivFinOfCardEq` result once (`ι : ↥s ≃ Fin 5`) and go through
  `congrArg Subtype.val (Equiv.symm_apply_apply ι ⟨z, hz⟩)` rather than
  rewriting under the coercion.

## 29. Mathlib API (pinned v4.36.0-rc1): this session's lookup table

Each entry was grepped in `.lake/packages/mathlib`.  The local checkout
matches the manifest revision, so reading the source *before* the next
Modal round trip is free and exact.

| tried | error | what compiles |
|---|---|---|
| `Multiset.count_eq_zero_of_not_mem` | unknown constant | `Multiset.count_eq_zero_of_notMem` (Mathlib-wide `not_mem` → `notMem` rename) |
| `Multiset.mem_roots'.mp` | unknown constant | `Polynomial.mem_roots'` (`.mp` gives `p ≠ 0 ∧ IsRoot p a`) |
| `MonoidHom.mem_range_self` | unknown constant | `MonoidHom.mem_range.mpr ⟨g, rfl⟩` |
| `galActionHom_injective` | unknown identifier | `Gal.galActionHom_injective p ℂ` (namespace `Polynomial.Gal`) |
| `card_rootSet_eq_natDegree (S := K) …` | invalid argument name `S` (hint: `F`, `K`) | positional: `card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _)`.  When the error suggests parameter names, use them or drop the name. |
| `AlgEquiv.commutes g r` to push `g` through a root equation | type mismatch: lands in `p.SplittingField`, not `K` | `Polynomial.aeval_algHom_apply : aeval (g y) p = g (aeval y p)`, then `rw [Polynomial.aeval_algHom_apply, hxi, map_zero]` |
| ext for Galois automorphisms | (hand-rolled `AlgEquiv.ext` over roots) | `Polynomial.Gal.ext p fun z hz => …` (agree on the roots of `p`) |
| `Subgroup.mem_top` as a proof | "argument `Subgroup.mem_top` has type `∀ x, x ∈ ⊤`" | apply it: `Subgroup.mem_top x` |
| `card_le_of_le le_top` for `|N| ≤ |H|` | `Nat.card {x // x ∈ ⊤}` vs `Nat.card ↥H` mismatch | `Subgroup.card_le_card_group N` |
| `(IsGalois.mem_bot_iff_fixed t).mpr fun σ _ => …` | binder count mismatch | the statement is `∀ f, f t = t` (no membership binder): `fun σ => hfixt σ` |
| `Nat.card ↥(zpowers c)` | — | `Nat.card_zpowers : Nat.card (zpowers c) = orderOf c` |
| bijection from injection plus `Nat.card` | — | `Nat.bijective_iff_injective_and_card` |
| ℤ ↔ ℚ root transport | — | `aeval_map_algebraMap`, `algebraMap_int_eq`, `eq_intCast`, `exists_integer_of_is_root_of_monic`, `Rat.isSquare_intCast_iff` |
| `perm_no_index_three_four rfl (Or.inr …)` | `don't know how to synthesize implicit argument H` (and `a`, `b` of `Or.inr`) | named implicit plus a concrete card proof: `perm_no_index_three_four (H := MonoidHom.range ρ) (Fintype.card_fin 5) (Or.inr ?_)`.  `rfl` leaves the `Fintype` instance as a metavariable, and everything downstream fails to unify. |

**Meta-lesson.**  Across Parts III and IV, the most common failure was not
a missing lemma but a **rename** (`not_mem` → `notMem`), a **namespace
move** (`Multiset.` → `Polynomial.`, top-level → `Gal.`) or a **binder
change** (implicit ↔ explicit, a dropped membership binder).  Before
writing `Foo.bar`, run `grep -rn "theorem bar\|lemma bar" .lake/packages/mathlib/Mathlib`.
It takes seconds; a Modal round trip takes 3–15 minutes.

## 30. Tactics: what failed here, and the replacement that compiled

* **`rw` motive errors when the rewritten term occurs inside a type.**
  `N := normalizer (zpowers (c : ↥H))` has `H` in its *type*, so `rw [h] at
  hmod` (with `h : Nat.card H = 10`) failed with `motive is not type correct:
  fun _a ↦ _a ≤ Nat.card ↥N`.  You don't need the rewrite.  `rcases hH with
  h | h <;> omega` feeds `h` to `omega` as a linear fact.  The same motive
  error recurred for `rw [← hco5]` in `c ^ 5 = 1` with `Perm (Fin 5)` in
  scope (§18's numeral abstraction) and for `cycPerm j ^ _a`.  **When `rw`
  reports a motive error, pass the equation to `omega`/`linarith`/`congrArg`
  instead of rewriting.**
* **Conjugation identities: rewrite `sq`, then `group`.**
  `σ * (c * c) * σ⁻¹ = (σ * c * σ⁻¹) ^ 2 := by rw [sq]; group`.  The
  original proof rewrote with `pow_one` / `c ^ 2` patterns that did not
  occur ("did not find `c ^ 1` in `σ * (c * c) * σ⁻¹ = c ^ 2`").  `group`
  normalizes free-group words including `⁻¹`, but expose the `^` as products
  first.  Then do the case split on `k % 5` with explicit `(c ^ a) ^ 2 = c ^
  b` lemmas (`rw [← pow_mul, show 3 * 2 = 5 + 1 from rfl, pow_succ, hc5,
  one_mul]`).
* **`rfl` cannot see through a symbolic `Fin` index.**  `htv : t =
  ThetaVals x j` by `rfl` failed ("not definitionally equal") because `j` is
  a variable.  Split it off into a lemma that *cases first*:
  ```lean
  lemma thetaVals_cyc … (j : Fin 6) : ThetaVals x j = theta x ⇑(cycPerm j) * … := by
    fin_cases j <;>
    · change theta x _ * theta x _ = _
      congr 2; funext i; fin_cases i <;> rfl
  ```
  The 5-cycle power independence (`T ^ n` for `n = 1..4`) is a separate
  `theta_pair_pow` proved by `interval_cases n`.
* **`interval_cases v` generates exactly the cases in `[lo, hi]`; count the
  bullets.**  With `0 < v` and `v ≤ 12` there are 12 cases (`v = 1 … 12`).
  An extra leading `· omega` (written for a nonexistent `v = 0` case) shifted
  every bullet by one, producing "No goals", "omega could not prove the goal"
  and type mismatches in *every* case.  One misalignment looked like a dozen
  independent bugs.
* **`linear_combination h` as the transport from a certified identity.**
  `resolvent_eval_theta` reduces to `sextic_vieta` (six coefficient
  hypotheses), each closed by `linear_combination theta_eK x`.  That is a
  single `ring` check of `goal − h = 0`.  Degree-24 normal forms needed
  `maxHeartbeats 400000000` on that one theorem.
* **`obtain rfl : c5 = -(…) := by rw [h1, neg_neg]` turns hypotheses into
  substitutions.**  In `sextic_vieta`, eliminating every coefficient variable
  by `obtain rfl` before `simp only [map_add, map_mul, map_neg]; ring` leaves
  a pure identity.  `ring` cannot *use* hypotheses; `subst`/`obtain rfl` and
  `linear_combination` are how you feed them in.
* **Error signatures that mean "under-applied term":**
  * ``rcases failed: `x✝ : c ≠ 1 → ∃ j m, …` is not an inductive datatype``:
    the lemma (`cycles_complete κ hκ5`) still needed the `hκ1` argument.
  * `Function expected at h1 c, but this term has type c ∈ zpowers c ↔ …`:
    `Subgroup.mem_normalizer_iff` yields an `Iff`; use `(h1 c).mp`.
  * `Function expected at ↑m + 1 : ℕ`: `cycPerm j ^ (↑m + 1) i` parsed the
    index `i` as an argument of the exponent.  Write `(cycPerm j ^ (m + 1)) i`
    (also `Equiv.ext hm` to go from pointwise equality to `κ = …`).
* **Term-mode replacements need `exact` inside `by`.**  Swapping a tactic
  proof for a Mathlib term (`Subgroup.eq_top_of_card_eq N hNcard`) inside a
  tactic block gave `unknown tactic`.  Use `exact <term>`, or move the term to
  the `:=` position.
* **Mechanical lint fixes must respect the syntactic position.**  A regex
  turning `show` into `change` (linter: "use `change`") also hit a *term-mode*
  `show T from e` and produced `unexpected token 'from'; Unknown identifier
  change`.  Only tactic-position `show` may become `change`.

## 31. Variables and naming: shadowing against the main statement's binders

The criterion's statement binds the quintic's coefficients `a b c d e : ℚ`.
The original proof also used `c` for the 5-cycle and `e` for the root
enumeration `Equiv`, which gave errors far from the cause:

* `Application type mismatch: The argument c : Perm (Fin 5) … expected ℚ`
  inside `resolvent5 a b c d e`.
* Goals displaying `a b c d e✝ : ℚ`.  **The `✝` (inaccessible) suffix on a
  statement binder is the telltale** that a later local of the same name
  shadowed it.

Fix: the 5-cycle became `κ`, the enumeration `ι`.  **Convention:** in a
file whose headline statement binds `a … e` (or `x`, `p`), keep proof-local
group elements and equivalences in Greek (`σ κ ρ ι`) and never reuse a
statement binder.  The same applies to generator output: the Weights
generator emits `n` / `hn` / `hr'` only inside fresh `have` scopes.

Also: **`set N := <big term> with hNdef`** gave the normalizer an atom-sized
name, so `omega` and `Subgroup.card_le_card_group N` saw `Nat.card ↥N`
instead of a 3-line expression, and the coercion `(zpowers (c : ↥H) :
Set ↥H)` was elaborated exactly once instead of in each hypothesis.

## 32. Lint and options

* The `maxHeartbeats` justification comment belongs **on the line after**
  `set_option maxHeartbeats N in`, before the docstring.  The linter accepts
  that position, and the parser is happy because a line comment is not a
  docstring.
* Scope every budget per declaration.  A file-level `set_option
  maxHeartbeats` leaks into every tactic, and the linter flags it.
  Deleting a wrapper lemma also deleted the `set_option … in` line in front
  of its *neighbour* (`perm_order_5_normal_of_card` then timed out).  When
  you delete a declaration, check what the preceding line was attached to.
* `haveI` → `have` and `show` → `change` (tactic position only) are
  mechanical.  Also remove unused `simp` arguments and an unnecessary `<;>`
  (the linter names each).  Generated files with 200-digit literals take
  `set_option linter.style.longLine false` in the header, with a comment
  saying why.
* Style warnings remain in the generated `Id*` modules and in
  `MaedaGalois5Defs`.  Fixing them means regenerating and rebuilding the
  whole heavy chain (about 2 h, 200 GiB), so they are deferred.  Lint
  generated output **before** the first heavy build, when it is free.

## 33. Build infrastructure: what made the iteration loop affordable

* **Rolling build cache (`lean_check.py`)**: one
  `/cache/buildcache/latest.tar.gz` holds `.lake/build`.
  * It is restored before `lake build` and saved after *every* run.  Lake
    only records a module once it compiles, and its traces re-hash sources
    and imports, so restoring the cache of a failed run is safe.
  * The tarball is written with `tar -I "gzip -1"` to a temp file, then
    `os.replace`d, so a concurrent run never reads a half-written file.
    `Volume.commit()` follows.
  * Measured: a second identical run rebuilds **0** MathProof modules (62 s
    vs 198 s).
  * The earlier per-HEAD draft had never actually run: every logged run set
    `LEAN_CHECK_NO_CACHE=1`.  Check the logs to see whether a feature was
    ever exercised.
* **Staged chain + cache = resumable proofs.**
  * Run one `lean_check` per heavy module (`Defs → IdBase → IdE4 → IdE5 →
    IdE6 → Identities → MaedaGalois5 → Weights`).  Stage times: 461 / 209 /
    2343 / 1498 / 2207 / 170 s, then under a minute each.  Peak RSS was 202
    GiB (E4), well above the 128 GiB request, because Modal memory is soft.
  * Fixing E6 then reused the cached E4/E5 (≈ 65 min saved per round).
  * **This only works if the generator emits unchanged modules
    byte-identically.**  That is why the E6-only `maxRecDepth` was made
    conditional on `k == 6` instead of being emitted everywhere.
* **Account migration without recomputation.**  When the doz workspace ran
  disabled mid-E6, the cache tarball was copied to a new `lean-cache`
  volume in the xyz account.  Creating that volume was explicitly approved
  by the user, as the AGENTS.md policy requires.  The first xyz run
  restored it and rebuilt nothing.  Policy discipline: a `kill` the
  permission classifier blocked was not worked around.  It went to the user
  as a command to run.
* **Inherited never-compiled code is the biggest hidden cost.**
  `MaedaGalois5.lean` arrived having never compiled.  It called
  `resolvent_eval_theta`, which was **never defined**, and that `Unknown
  identifier` sat among ~40 API-drift errors.  Before porting an inherited
  file:
  * grep every referenced project lemma for its definition;
  * check the generated certificate data is in the repo (`s5_certs.json`
    had lived in `/tmp/maeda5`; it is now under `research/`, and
    regeneration is byte-identical);
  * compile the light parts first.
  The criterion layer, once the identities were cached, iterated at about
  3 min / 7 GiB per round.
* **Batch fixes per round** (Part III §24, re-confirmed): the criterion went
  from ~40 errors to green in six rounds.  Each round fixed every error whose
  cause was understood, read from the pinned Mathlib source.

## 34. Carry-forwards from Part IV

1. Error triage table (§27) before touching any limit: kernel stack →
   restructure; elaborator recursion → `maxRecDepth`; heartbeats → budget;
   "decide proved … false" → math or generator bug.
2. Every certificate over a noncomputable structure gets the three-piece
   shape: explicit noncomputable object, computable `ZMod ℓ` mirror, `simp`
   bridge (§28).
3. Generators: put the smaller operand on the left of every kernel-evaluated
   product; emit per-declaration budgets; keep unchanged modules
   byte-identical so the staged cache keeps paying.
4. Reserve Greek names for proof-local objects in files whose statements
   bind Latin coefficients (§31).
5. The `MaedaGalois5Weights` module docstring still says `R` is "defined as
   `resolvent5` applied to the coefficients".  Since the redesign, `R` is an
   explicit integer polynomial and `hRint` links it to `resolvent5`.  Fix
   this in `tools/gen_galois5.py` at the next regeneration (a light module,
   so the fix is cheap).
