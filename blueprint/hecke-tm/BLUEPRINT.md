# BLUEPRINT 1 — hecke-tm: the Hecke operators T_m for all m at level one

Iteration 23, b1 (the wave's foundation).  Authored by the orchestrator
2026-11-02 from `research/iteration23/probe1-hecke-tm/FINDINGS.md` (read it
first — it carries the validated numerics and the definition-route decision).
Provenance: T2 submission 2026-11-02; trunk `dev/iteration23-hecke-ring`.
Downstream consumers: b2 (`hecke-index`), b3 (`hecke-field`).

## 0. Objective / non-objectives

**Objective.**  A new light module `MathProof/ModularForms/HeckeTM.lean`
defining, for every `m ≥ 1` and weight `k : ℤ`, the level-one Hecke operator
`heckeTM` on `CuspForm 𝒮ℒ k` — by the RECURSIVE ROUTE (probe-1 §2):
`heckeTM 1 = id`; `heckeTM (p^(r+1)) = heckeTP ∘ heckeTM (p^r) −
(p^(k-1) : ℂ) • heckeTM (p^(r-1))` for `p` prime; `heckeTM m` for general `m`
the composition over the prime powers of `m` (order-free — primes commute,
`heckeTPₗ_commute`) — and proving the complete algebraic Hecke calculus:

* `heckeTM_qExpansion_coeff`: `(T_m f)_n = ∑_{d ∈ Nat.divisors (gcd m n)}
  (d^(k-1) : ℂ) * f_{m*n/d²}` (the general-m coefficient formula; for prime
  `m` it must specialize definitionally or by a one-line rewrite to the
  landed `heckeTP_qExpansion_coeff`);
* `heckeTM_mul`: `T_m ∘ T_n = ∑_{d | gcd(m,n)} d^(k-1) • T_{m*n/d²}` (the
  T-calculus multiplicativity — probe-1 check B);
* `heckeTM_one`: `a₁(T_m f) = a_m f` (the duality ingredient — feeds b2);
* `heckeTM_two_mul_even` (the two-term recurrence `T₂ ∘ T_m = T_{2m} +
  2^(k-1) • T_{m/2}` for even `m`, as an instance of `heckeTM_mul`);
* `heckeTM_commute`: `T_m` commutes with `heckeTP p` for all primes `p`, all
  `m` (and `Commute` for the `Module.End`/linear-map forms);
* linear-map packaging `heckeTMₗ : ℕ → (CuspForm 𝒮ℒ k) →ₗ[ℂ] …` suitable for
  b2/b3 to treat the family as operators (`Module.End ℂ`).

**Non-objectives.**  The coset-sum definition of T_m (classical honesty —
probe-1 §2 records that our operator coincides with it on cusp forms via the
shared coefficient formula; TauCeti's `heckeTCuspLevelOne` is the reference
shape, study-only); operators on non-cusp forms; `T_m` at level `N > 1`;
dims ≥ 11; Mathlib bump; ANY edit to `HeckeLevelOne.lean` or any other
ancestor of the heavy `MaedaGalois5` chain (check the AGENTS.md list —
`HeckeLevelOne` IS on it; the new module only imports it).

## 1. Reuse map (two columns)

**Mathlib-at-pin** (verified at the pin): `Finset.sum_subset` /
`Finset.sum_congr` + `Nat.divisors` (`Nat.divisors_filter`, `Nat.mem_divisors`,
`Nat.Prime.dvd_mul`, `Nat.dvd_divisors_*`), `Nat.gcd` lattice lemmas,
`Nat.mul_div_cancel_leftₓ`-style division lemmas (the HeckeCommute proof's
arithmetic toolkit); `Module.End` algebra.  Nothing else — Mathlib has NO
Hecke operators on modular forms (probe-1 §4; the only "Hecke" hits are the
abstract `NumberTheory/HeckeRing/Defs.lean` and category-theory names).

**TauCeti** (study-only): `heckeTCuspLevelOne` + `qExpansion_coeff_heckeTCuspLevelOne`
(the general-n coefficient formula — confirms our recursive T_m ≡ classical
T_n on cusp forms; the definition shape if the worker ever needs the coset
route) and `qExpansion_coeff_one_heckeTCuspLevelOne` (the a₁-formula).  Their
`FixedDetMatrices` dependency is absent from Mathlib — the recursive route
avoids that whole surface.  Nothing to port.

**Own library**: `HeckeLevelOne.heckeTP` + `heckeTP_qExpansion_coeff` (the
prime case: both the definition seed and the base step of every induction);
`HeckeCommute.heckeTP2_qExpansion_coeff` (one unrolled composition — the
prime-step pattern), `HeckeCommute.qExpansion_coeff_ext` (coefficient identity
⟹ operator equality — the module's workhorse), `heckeTP_commute`/
`heckeTPₗ_commute`; probe-1's `probe_tm.py` (anchors: the multiplicativity
grid, the Δ/τ eigenform check, the duality matrix identity).

## 2. Module layout

One new light module `MathProof/ModularForms/HeckeTM.lean` (est. 400–700
lines), namespace `HeckeTM`, importing `MathProof.ModularForms.HeckeLevelOne`
and `MathProof.ModularForms.HeckeCommute`.  Suggested internal order:
(1) the prime-power family `heckeTPow : ℕ → ℕ → CuspForm … →ₗ …` by recursion
on `r` (structure: `Nat.rec` on the exponent; keep it STRUCTURAL — kernel
reducibility is not at stake here, but elaboration cost is);
(2) `heckeTM` via prime factorization (`Nat.factorization`/`Nat.factors`);
well-definedness of the composition order from prime commutativity;
(3) `heckeTM_qExpansion_coeff` by strong induction on `m` (base `m ≤ 1`;
step through the prime recursion — the induction step IS probe-1 check B at
prime-first composition);
(4) `heckeTM_mul` by double induction (or: derive both compositions'
coefficient formulas from (3) and match — the HeckeCommute pattern, generalized);
(5) the corollaries (`heckeTM_one` = (3) at `n = 1`; the recurrence; commutation).
A `Module.End`-valued `heckeTME` (or direct `Module.End` defs throughout) is
welcome if it saves coercion glue downstream — b2/b3 need operator
composition and ℤ-span membership, so expose BOTH `ℂ`-linear-map and
`Module.End` forms if cheap.

## 3. Verification plan

* Every gate: standalone-mirror Modal run (the worktree cannot use
  `tools/modal_run.sh` directly — AGENTS.md gotcha) of the touched module,
  0 err / 0 warn; `tools/tauceti_audit.sh` clean; no `set_option`.
* Anchors inside the module's tests where cheap: e.g. a `T_m Δ` spot-check
  against verified τ values is NOT needed in Lean (the Mordell file already
  carries the prime theory) — the module is analytic/algebraic; its decided
  content is nil (no kernel decides expected!).  If the worker adds any
  `decide`, AxCheckDecide must stay `propext`-clean.
* Registration: trio (root `MathProof.lean` + `defaultTargets` + CI list) —
  the module is cheap (pure proofs, Mathlib-level imports).
* Byte-discipline: no generated files in b1 (hand-written module only).

## 4. Stage gates (each ≈ one green-commit session; descope provisions inline)

* **G1 — audit + skeleton**: re-verify the probe-1 anchors at the pin (rerun
  `probe_tm.py` — it is committed, cold-executable); pin the exact form of
  `heckeTP_qExpansion_coeff` and `heckeTP2_qExpansion_coeff` (read the files,
  not the blueprint's paraphrase); check `Nat.factorization`-based
  well-definedness route (the composition-order lemma from
  `heckeTPₗ_commute`); commit the module skeleton + WORKLOG.  *Descope*: if
  the order-free composition proof fights, define `heckeTM` by a FIXED
  factorization order (`Nat.factors` sorted ascending, fold left) and prove
  order-independence only as far as `heckeTM_mul` needs it.
* **G2 — prime powers**: `heckeTPow` + `heckeTPow_qExpansion_coeff` for
  `m = p^r` (the two-term recursion unrolled; base `r = 1` is the landed
  formula).  Green on Modal.  *Descope*: none expected; if the r-induction
  needs the composed formula in an awkward shape, take `r = 2` (`T_{p²}`,
  reads `f_{p²n}, f_{pn/p}, f_{n/p²}`-coefficients) as an intermediate
  lemma set — the prime-power staircase is what b2 actually consumes
  (`T_{2^i}`, i ≤ 9).
* **G3 — general m + multiplicativity**: `heckeTM` +
  `heckeTM_qExpansion_coeff` (strong induction) + `heckeTM_mul`.  THE
  technical gate: the divisor-lattice reindexing
  `∑_{d | gcd(pm,n)} d^{k-1} f_{pmn/d²} = f-side + p-side` (two cases
  `p ∣ m`, `p ∤ m`; each a Finset bijection on `Nat.divisors`).  Green on
  Modal.  *Descope*: if the FULL `heckeTM_mul` exceeds the session, land
  `heckeTM_qExpansion_coeff` + the special cases b2 needs (`T_p ∘ T_m` for
  prime `p`; `T₂ ∘ T_{2^i}` recurrence) and descope the all-pairs
  multiplicativity to a CORRECTIONS-noted follow-up.
* **G4 — corollaries + registration**: `heckeTM_one`, recurrence packaging,
  commutation, linear-map/End forms, trio registration, combined audits
  (`AxCheckDecide` on the branch's light set), WORKLOG + research-log draft
  entry.  *Descope*: End-form packaging can drop to a coercion lemma.

## 5. Risks / fallbacks

* **Divisor reindexing complexity** (main risk): Lean Finset bijections on
  `Nat.divisors` with the `d²` map are fiddly (`d ↦ p·d` injectivity,
  `Nat.divisors (gcd …)` filtering).  Fallback: state sums over
  `Finset.filter (fun d => d ∣ gcd m n) (Nat.divisors (m*n))` if the
  `gcd`-divisor shape fights, and transport — b2/b3 consume the FORMULA
  shape `∑_{d | gcd}`, so keep the final statement in that shape and fight
  only internally.
* **Elaboration cost of factorization-indexed recursion**: split declarations
  per the r5c* pattern if any single proof trips heartbeats (never raise
  them — CODING_STANDARDS).
* **Well-definedness (composition order)**: consume `heckeTPₗ_commute` fresh
  (it is stated for the linear-map forms); if the Module.End coercion glue
  is heavy, do everything in `ℂ`-linear-map land and export one `Module.End`
  bridge at the end.
* Proof standard: no decides expected; if any sneak in, entrywise/`propext`
  hygiene per AGENTS.md (matrix-level `decide` on `Fin n` pulls
  `Classical.choice`).

## 6. Lessons learnt (brought in)

HeckeCommute's case-split arithmetic (`p ∣ m` branches with explicit
`Nat.mul_div_cancel_left` rewrites) is the local idiom — copy it, don't
reinvent.  The T₁…Tₙ duality does NOT need Petersson symmetry (refuted in
probe-2 F6) — only `a₁(T_m f) = a_m f`, which is (3) at `n = 1`.
