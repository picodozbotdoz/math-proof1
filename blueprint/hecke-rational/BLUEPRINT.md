# BLUEPRINT 1 — HeckeRational: `T₃ ∈ ℚ[T₂]`, constructive rational witnesses

Iteration 22, steering priority 1 (iteration21-review §9.2).  Authored by the
orchestrator 2026-11-02 from `research/iteration22/probe1-q-rationality/FINDINGS.md`
(read it first — it carries the measured numbers and the exact current-state
audit).  Provenance: T2 submission 2026-11-02; trunk
`dev/iteration22-maeda-lehmer` (includes the T3-Galois T1 baseline).

## 0. Objective / non-objectives

**Objective.**  For every level-one weight `24 ≤ K ≤ 134` with
`2 ≤ dim S_K ≤ 10` (54 weights), a light kernel-certified theorem

```lean
theorem heckeT3_eq_aeval_rat_weightKK :
    ∃ Q : ℚ[X], heckeTPₗ ((K : ℕ) : ℤ) Nat.prime_three
      = Polynomial.aeval (T₂ | S_K) (Q.map (algebraMap ℚ ℂ))
```

(name shape negotiable; the `T₂` reference is whatever the weight's dim file
exports — see FINDINGS §4).  This closes §9.2: the representing polynomial is
*rational* — the Hecke algebra over ℚ is `ℚ[T₂]` at these weights; the
number-theoretic payoff (T₃-eigenvalues ∈ ℚ(λ₂)) is a one-line corollary for
a later iteration.

**Non-objectives.**  Primes `p ∉ {3}` (the route needs the operator's integer
matrix per weight; only T₂/T₃ matrices exist — record the recipe, don't build
new matrices); any ℚ-vector-space/`⊗` formalization; dims ≥ 11; Mathlib bump
(stay rc1); edits to any ancestor of the heavy `MaedaGalois5` chain; CI bill
> ~10 min (else root-only + flag to operator).

## 1. Reuse map (two columns)

**Mathlib-at-pin** (verified): `Polynomial.map_aeval_eq_aeval_map`
(`Mathlib/Algebra/Polynomial/AlgebraMap.lean:497`); `LinearMap.ext` +
spanning-set equality lemmas; `Module.AEval'`/cyclicity (NOT needed by the
constructive route — we bypass `exists_aeval…` entirely).

**TauCeti** (study-only): no Hecke-over-ℚ content (FINDINGS §5).  Nothing to
port.

**Own library**: `CharpolyDimN.charpoly_dimN` hypothesis bundle
(`hzero/hone/hA/hX`, CharpolyDimN.lean:194) and its internal elimination
pattern — the representation sibling copies its shape; per-weight `M`/`MT`/`Xtab`
literals in `MaedaDim{6..10}Weights`, `MaedaT3Dim{6..10}Weights`,
`MaedaT3SmallWeights` (+ small-weight T₂ sources to be audited at G1);
`g1_anchor.py`-style Lean-literal parsing for the generator's data pinning;
`gen_maedan.term_chunks`/`chunk_expr_tokens` for chunked literals;
`HeckeCommute.qExpansion_coeff_ext` if a vanishing argument is ever needed
(the triangular route avoids it).

## 2. Module layout

* NEW light `MathProof/ModularForms/HeckeRational.lean` (generic, ~120 lines):
  - `represents_dimN` — same hypotheses as `charpoly_dimN` plus
    triangular-independence + `finrank = n`; concludes
    `∀ i < n, T (f i) = ∑ j, (coordN A (X i) j : ℂ) • f j`.  Independence of
    triangular families: leading-term argument (a nontrivial ℂ-combination
    has a lowest-order nonzero term).  Spanning: `finrank_eq` + n independent.
  - `aeval_pow_rep : (aeval T₂ (X ^ j)) (fb i) = ∑ l, (M₂^j)ₗᵢ • fb l`
    (induction on j via `represents_dimN` twice + linearity).
  - `op_eq_of_matrix : (∑ j, (N j : ℤ) • M₂^j = D • M₃) → aeval T₂
    (Q.map (algebraMap ℚ ℂ)) = T₃` glue (operator equality from basis
    agreement), where `Q = ∑ C (N j / D) * X^j` is assembled from the
    certificate parts.
* NEW generator `tools/gen_hecke_rat.py`: per weight, load (M₂, M₃)
  (T₂ from the dim-file literals where available — parse like `g1_anchor.py`;
  T₃ likewise), assert commutation, solve `∑ q_j M₂^j = M₃` over ℚ
  (fraction-free Gaussian elimination; assert exact verification; assert
  uniqueness via nonsingular system), emit the `Q` chunked literal
  (numerators/denominators ≤ 349 digits ⇒ chunks; exponents ≤ 256) + the
  scaled integer identity `∑ N_j • M₂^j = D • M₃` as `decide +kernel`
  (matrix equality over ℤ on `Fin n` literals; measured ceiling ~600-digit
  entries at dim 10 — FINDINGS §3).
* Generated `MathProof/ModularForms/HeckeRationalWeights.lean` (54 weights,
  est. 1.5–3 k lines) or per-dim split if G3 measures the single file slow.

## 3. Verification plan

* G1 data audit BEFORE any code: parse every (M₂, M₃) from the Lean files
  (ground truth), cross-check census JSONs; audit the small-weight T₂ matrix
  situation (dims 2–5: `MaedaLevelOne`/`MaedaDim{4,5}Weights`/`MaedaSmallWeights`
  — FINDINGS §4 flags the namespace/shape differences).
* Every gate: `tools/modal_run.sh --file <module>` green 0 err / 0 warn;
  `--check` byte-identity discipline for the generator; `tauceti_audit.sh`
  clean; combined `AxCheckDecide` at close (expect +54 decide certs,
  0 > propext).
* Registration by measured CI add: < ~10 min → trio; else root-only + flag.
* No `set_option` anywhere; no ancestor edits; new modules only.

## 4. Stage gates (each = one green-commit session; descope provisions inline)

* **G1 audit + data**: all (M₂, M₃) pairs re-derived and pinned to Lean
  literals; small-weight T₂ matrix inventory.  *Descope*: if dims 2–5 T₂
  matrices are missing/inconvenient, restrict to the 30 weights 72–134
  (statement stays uniform; record in WORKLOG + blueprint CORRECTIONS).
* **G2 generic module**: `HeckeRational.lean` green on Modal (prove
  `represents_dimN`/`aeval_pow_rep`/`op_eq_of_matrix`; test-drive on ONE
  weight inline in scratch first).
* **G3 generator + dims 6–10** (30 weights): file(s) green; commit.
* **G4 small weights** (24) or recorded descope from G1.
* **G5 registration + audits + bookkeeping** (README/docs/AGENTS.md/research-log).

## 5. Risks / fallbacks

* R1 dim-10 scaled-identity decide slower than projected (est. seconds;
  worst case minutes): split the identity per power `M₂^j` into staged
  lemmas (the `Lv{a}_{j}` pattern), or per-weight files.
* R2 `ring_nf`/`hcP`-style matching on chunked `Q` literals: reuse
  `term_chunks` decisions identical to the `cP` pattern (T2-Galois proof).
* R3 heartbeat on a 54-weight single file: split per-dim (D3 pattern from
  the T₃-Galois wave).
* R4 matrix-parse drift: the generator re-asserts equality against the
  census each run; Lean is the truth (evidence hierarchy §5).

## 6. Provenance (cold-executable)

Read, in order: this file; `research/iteration22/probe1-q-rationality/FINDINGS.md`;
`MathProof/ModularForms/CharpolyDimN.lean` (the `charpoly_dimN` internals you
will mirror); one generated dim file's `hX`/`Xtab`/`M` block
(`MaedaT3Dim6Weights.lean` around its `namespace MaedaT3Weight72`);
`tools/gen_galoisfull.py` (`coeff_expr`/`clist` chunking);
`research/iteration22-t3-galois/g1_anchor.py` (Lean-literal parsing);
`external-doc/CODING_STANDARDS.md`; AGENTS.md conventions.  Base commit of
the trunk is recorded in WAVE-TRACKING.md.

## Lessons learnt (binding, from the iteration-21/22 record)

Blueprints are hypotheses — audit G1 before code (the false k=24 T₃ anchor);
census data untrusted until re-derived; commit at every green milestone;
WORKLOG everything; poll the inbox at every checkpoint; `decide +kernel`
first when the elaborator budget trips; chunk exponents ≤ 256.
