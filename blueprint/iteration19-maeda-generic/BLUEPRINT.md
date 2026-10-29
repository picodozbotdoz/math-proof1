# Iteration 19 blueprint — Maeda's conjecture, the generic engine (dims 6–10)

**Status: blueprint (Task AA cycle 1).  Nothing in `MathProof/` is touched.**
Owner decision per `research/iteration18-improvements.md` P1-4: scope =
**irreducibility for dims 6–10**; Galois groups stay at dim ≤ 5 until the
Dedekind–Frobenius bridge exists (`blueprint/dedekind-frobenius/`).

Evidence base: `blueprint/exploration/FINDINGS-maeda-dim6-10.md` (+ the JSON,
the two elaborated Lean sketches).  Headline: the pinned Mathlib already
ships a certified determinant tactic, so the study's "main new engineering"
(reflected Bareiss + Sylvester correctness) **collapses to a one-line tactic
call per evaluation point**; the measured k=72 pilot runs in ~5 s locally.

## 1. Objective

`theorem maedaNNN_k : Irreducible (charpoly (T₂ | S_k)  over ℚ)` for all 30
level-one weights with `dim S_k ∈ [6, 10]` — i.e. **every weight
k ≤ 134 except k = 26, 132** gets Maeda's conjecture (irreducibility half),
through one dimension-generic engine.  End state of the ratchet started at
Iteration 14.

## 2. Module layout (all light; none is an ancestor of `MaedaGalois5Defs`)

| module | content | size |
|---|---|---|
| `MathProof/ModularForms/CharpolyEngine.lean` (new) | `charpoly_of_eval_eq` (validated shape, sketch lines 33–46), the symbolic `scalar_sub_…` bridge helper pattern, `Matrix.charpoly_natDegree_eq_dim` packaging | ~60 lines, Mathlib-only imports |
| `MathProof/ModularForms/RabinCert.lean` (new) | reflected engine: `ztrim/znorm/zadd/zpmul/zprem/zpgcd/zpxw/bitsOf` (validated in the sketch; add the fuelled `zpgcd`), transport lemmas `List ℤ → (ZMod ℓ)[X]` (the `LehmerMod` mirror pattern), **`irreducible_of_rabin`** (§3), `irreducible_of_rabin_int : P.Monic → (certificates) → Irreducible (P.map (cast : ℤ →+* ℚ))` via `Monic.irreducible_of_irreducible_map` + Gauss | ~400 lines, the mathematical core |
| `MathProof/ModularForms/CharpolyDimN.lean` (new) | `charpoly_dimN` — abstract, Fin n-structural back-substitution (generalizes `charpoly_dim2/3/4`; hypothesis bundle = triangular-basis coefficients + T-coefficient data as functions `Fin n → …`; induction peels the top vector) | ~300 lines, the proof-engineering core |
| `MathProof/ModularForms/MaedaDimNWeights.lean` ×5 (generated) | one file per dim (6,7,8,9,10), six weights each: basis coefficients (`MaedaCertC.seqPLc`; τ through 20 ≤ 21 already verified), literal matrix + bridge, n+1 `eval_det` dets, `zpxw`/`zpgcd` decides, `monic`/`degree` by `monicity!`/`compute_degree!`, assembly | ~150–250 KB each |
| `tools/gen_maedan.py` (new) | the generator; emits byte-identically on re-run (chain-cache rule) | ~400 lines |

Add the light modules to `MathProof.lean`, `defaultTargets`, CI (per
AGENTS.md).  **Do not** touch `MaedaSmallWeights` / `MaedaDim{4,5}Weights` /
`MaedaGalois*` — regenerating dims 2–5 through the engine is an optional
later batch (it would rebuild the heavy chain, ~33 min / 35 GiB).

## 3. The one new mathematical lemma: Rabin's test, the direction we need

```
theorem irreducible_of_rabin {l : ℕ} [Fact l.Prime] {f : (ZMod l)[X]}
    (hf : f.Monic) {n : ℕ} (hn : f.natDegree = n)
    (h1 : zpxw-side: f ∣ X^(l^n) − X)                       -- X^(l^n) ≡ X [MOD f]
    (h2 : ∀ q ∈ primeDivisors n, IsCoprime f (X^(l^(n/q)) − X)) :
    Irreducible f
```

Contrapositive, two sublemmas (over `F = ZMod l`, `l` prime):

* **(A) degree-divisibility.**  `g` monic irreducible, `deg g = m`,
  `g ∣ X^(l^d) − X` ⟹ `m ∣ d`.
  Proof: pick a root α of g (in some extension); `g` irreducible ⟹
  `[F(α) : F] = m` and α generates `F_{l^m}`.  α is a root of
  `X^(l^d) − X` ⟹ `α^(l^d) = α` ⟹ α ∈ F_{l^d} (the fixed field of
  Frobenius^d).  Finite-field subfield lattice ⟹ m ∣ d.
  Mathlib entry points: `FiniteField.roots_X_pow_card_sub_X` (roots of
  X^q − X in F), `Polynomial.splits_iff_card` /
  `Polynomial.card_rootSet_eq_natDegree` (over the splitting field),
  `FiniteField` extension-degree facts — grep
  `Mathlib/FieldTheory/Finite/Extension.lean`,
  `Mathlib/FieldTheory/Finite/GaloisField.lean` first; the subfield-lattice
  fact may itself be missing and become a small sub-PR (worth checking
  `FiniteField.instCharPoly...` too).
* **(B) assemble.**  f reducible ⟹ f = ḡ·h̄ with ḡ monic irreducible of
  degree m < n.  By (A) applied to each irreducible factor (using h1),
  every factor degree divides n; m < n ⟹ m ∣ n/q for some prime q ∣ n
  ⟹ ḡ ∣ gcd(f, X^(l^(n/q)) − X) ⟹ the gcd is nonconstant — contradiction
  with h2.  (Also derives squarefreeness from h1 + `natDegree` counting.)

Then `irreducible_of_rabin_int` composes with
`Polynomial.Monic.irreducible_of_irreducible_map (φ := Int.castRingHom (ZMod ℓ))`
(`Mathlib/Algebra/Polynomial/Eval/Irreducible.lean:39`, the project's
existing pattern) and Gauss to ℚ.

**Certificates, reflected side** (all `List ℤ`, entries reduced `% ℓ`,
structural recursion + fuel for the non-structural loops — validated in
`RabinCertSketch.lean`, axioms `[propext]`):

* `f ∣ X^(ℓⁿ) − X` ⟺ `zpxw ℓ f̄ (bitsOf F (ℓ^n)) [1] = [0, 1]`;
* coprimality ⟺ fuelled `zpgcd ℓ f̄ (zpxw … (ℓ^(n/q)) minus X)` is `[1]`
  (i.e. a nonzero constant) — implement `zpsubX` (validated shape in the
  parent probe) + `zpgcd` (Euclid with fuel = degree bound; each step
  recurses through `zprem`).
* Transport: define `toPoly : List ℤ → (ZMod l)[X]` (Horner over the list),
  prove `zpmul/zadd/zprem/zpxw/zpgcd` homomorphism lemmas
  (`LehmerMod`-style; `pBeq`-based equality decision if the lists get long —
  they stay ≤ 2n entries here, plain `decide` suffices).

Cost (measured model, §2 of the findings): ≤ 28 K ZMod-muls per weight at
dim 10 — the largest kernel `decide` is the k=120 Rabin step at ℓ = 293
(exponent 293^10 ≈ 4.7 × 10²⁴, 82 bits); expect seconds per weight.

## 4. `charpoly_dimN` (the abstract matrix-extraction lemma)

Generalize `MaedaDim4.charpoly_dim4` from a 16-hypothesis bundle to
`Fin n`-functions, keeping its proof skeleton:

* basis data `A : Fin n → Fin n → ℤ` (strictly triangular: `a i j` for
  j > i is the coefficient of q^j in f_i, `a i i = 1`, zeros below),
  T-data `X : Fin n → Fin n → ℤ`;
* statement: `(T : S_k →ₗ S_k).charpoly = Matrix.charpoly (backsub A X)`
  where `backsub` is the reflected back-substitution (structural in the
  row index — the same triangular solve as `coords` in the probe);
* proof: the dim-4 proof is literally the n=4 instance of an induction on
  the echelon structure (linear independence from the first q-coefficient,
  coordinate solve by downward substitution).  The induction hypothesis
  must be phrased on *truncated* data — plan the statement so the IH
  closes (this is the main proof-design task; budget 2–3 rounds).
* Per weight, the hypotheses `hij`/`hxij` are discharged by `seqPLc`
  coefficient lemmas (`MaedaCertC`), as in the committed dim-4/5 files.

## 5. Assembly per weight (exactly the validated pilot)

```
charpoly_dimN (basis data from seqPLc)          -- T.charpoly = Matrix.charpoly Mₖ
charpoly_of_eval_eq Mₖ Pₖ hdeg                  -- = Pₖ, by n+1 eval_det dets
monic/degree by monicity!/compute_degree!
Rabin certificates at ℓ (and the 2nd prime as a sanity decide)
irreducible_of_rabin_int                        -- Irreducible over ℚ
```

## 6. Verification plan, budget, risks

* **Local first** (`lake env lean` per generated file; ~5–10 s per weight
  measured at dim 6 — spot-check dim 10 locally before any Modal run);
  then `tools/modal_run.sh --file` for the five files; then CI.
* Everything is light: no `Modal`-only modules, no heavy chain contact.
  CI cost ≈ 5 files × 1–3 min.
* Axiom audit: run `MathProof/AxCheckDecide.lean` after landing; target
  `propext`-only for every new `decide` (the sketch already meets it;
  watch the `zpgcd` fuel decisions and the `Fin`/`List` equality instances).
* Risks: (i) sublemma (A) may need a missing finite-field subfield-lattice
  fact — then factor it out as a stated-and-proved small lemma in
  `RabinCert.lean` (candidate Mathlib upstream); (ii) `charpoly_dimN` IH
  design could take an extra round — fallback: per-dim abstract lemmas
  generated for n = 6…10 from the dim-4 template (mechanical, larger files,
  zero proof risk); (iii) `eval_det` on 61-digit entries: measured fine at
  dim 6; if dim 9–10 elaboration spikes, split each weight into its own
  file (module boundaries free elaboration memory — Iteration 18 lesson).

## 7. Stretch (same trajectory, cheap after the engine exists)

* **The Maeda-statement upgrade**: `charpoly(T₂)` irreducible ⟹
  `ℚ[T₂] = Hecke algebra` ⟹ every `Tₙ` is a polynomial in `T₂` (the *usual*
  statement of Maeda's conjecture).  Needs Hecke commutativity
  `T_m T_n = T_n T_m` on level-one cusp forms (from the coefficient formula
  + q-expansion injectivity — `HeckeLevelOne` already has the formula) and
  the field-module counting argument (a `CuspForm`-side lemma, light).
  One blueprint-level session; high statement value.
* Dims 11–25 ratchet (τ-table extension at dim 11, `tauTable` through 50):
  unchanged from `maeda-scaling-study.md`; the engine above is the
  dimension-generic piece it lacked.
