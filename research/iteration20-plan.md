# Iteration 20 plan — Maeda's conjecture, dims 6–10: the generated weight files (resumable)

Checkpoint file: resume at the first stage not marked DONE.

This document consolidates everything Iteration 20 needs into one place.  The
source material was scattered across the `dev/blueprint` branch
(`blueprint/iteration19-maeda-generic/BLUEPRINT.md`,
`blueprint/exploration/FINDINGS-maeda-dim6-10.md`, the census JSON and the two
validated pilots); the load-bearing parts are merged here, the data artifacts
now live in `research/iteration20/`, and the two planning errors found during
consolidation are recorded below.  `dev/blueprint` stays as provenance.

## Objective and significance

`Irreducible (charpoly (T₂ | S_k))` over ℚ for all 30 level-one weights with
`dim S_k ∈ [6, 10]` — k ∈ {72, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98,
100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 128,
130, 134} (six per dim, one per residue class of k mod 12).

After it, **every weight k ≤ 134 except k = 26 (dim S₂₆ = 1, trivial) and
k = 132 (dim 11)** has the irreducibility half of Maeda's conjecture — the
ratchet started at Iteration 14 (dims ≤ 3), 15/17 (dim 4, then 5) jumps six
dimensions at once through one dimension-generic engine.

Why it is cheap now (the blueprint-wave engines, merged `b5d033e`):

* irreducibility comes from **Rabin's test** (`RabinCert.irreducible_of_rabin_int`,
  fully proved) instead of per-dimension factorization scans: 1–3 × 10⁴
  `ZMod ℓ` multiplications per weight vs 10⁵–10⁶ for the dim-5 ℓ²-scan
  certificates (one to two orders cheaper);
* the charpoly comes from **`CharpolyEngine.charpoly_of_eval_eq`** (certified
  `eval_det` determinants + interpolation, Mathlib at the pin) instead of a
  hand `charpoly_dimN` matrix formula per dimension;
* both engines are light modules on master, axiom-clean (`propext`-only smoke
  decides), TauCeti-compliant.

Deliberately **not** this iteration (kept out of scope): Gal = Sₙ for these
weights (Frobenius census already in hand; blocked on Dedekind stages 3–4 +
Jordan), the Maeda upgrade `Tₙ ∈ ℚ[T₂]` (blocked on `HeckeCommute`), dims
11–25, and regenerating dims 2–5 through the engine (would rebuild the heavy
chain for no statement gain).

## State at pickup (master `4eaf528`, branch `dev/iteration20-maeda-dim6-10`)

Landed on master and reused as-is:

* `MathProof/ModularForms/CharpolyEngine.lean` — `charpoly_of_eval_eq (M P hdeg h) :
  M.charpoly = P` from `hdeg : P.natDegree = n` and `n+1` evaluation points
  `h : ∀ i : Fin (n+1), P.eval i = (Matrix.scalar (Fin n) i - M).det`.
* `MathProof/ModularForms/RabinCert.lean` (769 lines) — reflected `List ℤ`
  engine (`zpxw`, `zpgcd`, `zpxwsubX`, `bitsOf`, `zprem`), transport `toPoly`,
  `irreducible_of_rabin`, and the packaging
  `irreducible_of_rabin_int (hmon : P.Monic) (hmap : P.map (Int.castRingHom (ZMod ℓ))
  = toPoly ℓ f) (hmon' : (toPoly ℓ f).Monic) (hnd : natDegree = n) (hn1 : 0 < n)
  (hF : ℓ^n < 2^F) (h1 : zpxw ℓ f (bitsOf F (ℓ^n)) [1] = [0, 1])
  (h2 : ∀ q Prime, q ∣ n → ∃ w, zpgcd ℓ w f (zpxwsubX ℓ f F (ℓ^(n/q))) = [1]) :
  Irreducible (P.map (Int.castRingHom ℚ))`.
* Templates: the generated `MaedaDim4Weights` / `MaedaDim5Weights`
  (`tools/gen_maeda.py`) supply the weight-file skeleton (basis coefficient
  lemmas via `MaedaCertC.seqPLc`, `charpoly_dimN` hypothesis discharge, literal
  charpoly assembly); dims 6–10 differ in the engine calls, not the skeleton.

Missing (this iteration builds it):

* `MathProof/ModularForms/CharpolyDimN.lean` — the abstract `Fin n`
  back-substitution lemma generalizing `charpoly_dim2/3/4`;
* `tools/gen_maedan.py` — the generator (byte-identical re-runs, chain-cache rule);
* the five generated files `MaedaDim{6,7,8,9,10}Weights.lean`.

## Planning corrections (found while consolidating — do not carry the old text forward)

1. **No τ-table extension is needed.**  The wave doc's §Open said "dim ≤ 10
   needs `tauTable` ≤ 50; 21 verified".  That conflates the dim-25 headroom
   note in `maeda-scaling-study.md` ("Dim ≥ 11 needs τ(22 … 2d)").  The
   templates show the real requirement: a dim-d weight file reads basis
   coefficients up to 2d (the T₂-image coefficient formula `(T₂f)_m =
   f_{2m} + 2^{k−1} f_{m/2}` for m ≤ d), i.e. truncation `N = 2d+1` (dim 4
   used N=9, dim 5 used N=11).  Dim 10 needs **N = 21**, inside both the
   verified `tauTable` (τ ≤ 21) and the `MaedaCertC.seqPLc_eq` cap
   (`hN : N ≤ 22`).  Consequence: **no edit to `MaedaLevelOne`/`MaedaCertC`,
   and no heavy-chain ancestor is touched anywhere in this iteration.**
2. **The Frobenius census claim "(n−1)-cycle prime ≤ 199 for every weight" is
   false.**  Verified entry-by-entry against the JSON census: k = 110 (dim 8),
   112 (dim 9) and 128 (dim 10) have no `[1, n−1]` factorization type in the
   ≤ 400 scan.  The other 27 weights all have one (max ℓ = 173).  Recorded for
   the *future* Sₙ route only — irrelevant to irreducibility — but the
   dedekind-frobenius blueprint inherits this gap and needs a wider scan (or
   the primitivity route) for these three weights.
3. (`cert_ell` semantics, confirmed: it is the smallest prime with charpoly
   irreducible mod ℓ — the n-cycle class; wherever the census recorded an
   `n_cycle` field it equals `cert_ell`.)

## Consolidated data (`research/iteration20/`)

* `data/maeda_dim6_10.json` (116 KB) — 30 entries
  `{k, dim, charpoly (n+1 ints, descending, the exact ℤ[X] literals),
  matrix (n×n ints, the back-substituted T₂ matrix), cert_ell, cert2_ell,
  rabin_zmuls, frobenius {…}, frobenius_census [[ℓ, degrees]…]}`.
  Regression anchors: the machinery reproduces the **proved** k=24
  (`MaedaWeight24`) and k=48 (`MaedaDim4Weights`) charpolys exactly.
* `maeda_dim6_10_probe.py` — regenerates the JSON **byte-identically**
  (verified 2026-10-31 at this location; imports
  `research/maeda-scaling-probe.py`, 3.7 s).
* `gen_sketch_charpoly.py` — the validated k=72 pilot generator (JSON path
  adjusted; the only change).  Note its emitted sketch is *not*
  byte-identical to the committed `CharpolyInterpSketch.lean`: the committed
  pilot's `simp only` list was hand-extended during debug (one `Matrix.head_cons`
  line).  The real generator (S3) must be byte-identical; the pilot is a
  reference, not a build input.
* `CharpolyInterpSketch.lean` — the elaborated k=72 pilot (~5 s local),
  copied as-is.

### Census (charpoly coefficients, Rabin primes, kernel cost)

| dim | weights (k) | matrix entries | charpoly coeffs | Rabin ℓ (max) | 2nd ℓ (max) | ZMod-muls (max) |
|----|--------------|----------------|-----------------|---------------|-------------|-----------------|
| 6  | 72 76 78 80 82 86 | ≤ 37 digits | ≤ 75 | 139 | 241 | 5 756 |
| 7  | 84 88 90 92 94 98 | ≤ 43 | ≤ 100 | 349 | 409 | 6 752 |
| 8  | 96 100 102 104 106 110 | ≤ 49 | ≤ 130 | 179 | 313 | 10 732 |
| 9  | 108 112 114 116 118 122 | ≤ 55 | ≤ 164 | 263 | 313 | 15 584 |
| 10 | 120 124 126 128 130 134 | ≤ 61 | ≤ 200 | 293 | 313 | 27 950 |

Frobenius per weight (for the future Sₙ route; see JSON for the full census):
`disc_nonres` prime ≤ 61 for all; Jordan p-cycle (p ≤ n−3) for all but
k = 134 in the ≤ 400 scan (k = 130 at ℓ = 109, p = 7 = n−3; k = 134 found at
ℓ = 557 in a wide scan, not in the JSON); transposition for all but
k = 116, 130, 134; (n−1)-cycle for all but k = 110, 112, 128 (correction 2).
`n_cycle` = `cert_ell` for every weight.

## Module plan and invariants

| module | content | kind |
|---|---|---|
| `MathProof/ModularForms/CharpolyDimN.lean` (new) | `charpoly_dimN` — abstract Fin n-structural back-substitution, the dim-4 proof skeleton with `Fin n` hypothesis functions (basis `a i j`, T-data `x i j`); IH phrased on truncated data so it closes | proof-engineering core |
| `tools/gen_maedan.py` (new) | emits the five files byte-identically; reads `research/iteration20/data/maeda_dim6_10.json`; recomputes basis tuples + T₂ matrices via `maeda-scaling-probe.py` and **asserts equality with the JSON matrix** (regression) | generator |
| `MathProof/ModularForms/MaedaDim{6..10}Weights.lean` (generated) | six weights each: basis/T₂-image coefficient lemmas (`MaedaCertC.seqPLc`, N = 2d+1 ≤ 21), literal matrix + bridge, n+1 `eval_det` dets, Rabin decides, assembly | generated, light |

Invariants (per AGENTS.md):

* Everything is light.  **No heavy-chain contact**: `CharpolyDimN` and the
  weight files are new modules; nothing in the `MaedaGalois5Defs` ancestor set
  (`Tau/Basic`, `MaedaLevelOne`, `MaedaDim4/5`, …) is edited, so no 33-min
  chain rebuild is triggered.
* TauCeti rules: no `set_option` of any kind in the new light modules — all
  kernel decides go through `decide +kernel` (which also sidesteps the
  elaborator `maxRecDepth` issue the pilot measured), and any elaboration that
  genuinely doesn't fit is **split**, not given a budget (the `r5c*` pattern).
* Registration: all six modules go into `MathProof.lean`, `defaultTargets`
  (`lakefile.toml`) and the CI target list.  Do **not** touch
  `MaedaSmallWeights`/`MaedaDim{4,5}Weights`/`MaedaGalois*`.

## Assembly recipe per weight (exactly the validated pilot, against the landed APIs)

For weight k, n = dim, from the JSON: matrix `Mₖ`, charpoly literal `Pₖ`,
certificate prime `ℓ` (and `ℓ₂` as the sanity decide), `q = prime divisors of n`.

```
-- 1. the abstract extraction (CharpolyDimN, discharged by seqPLc coefficient lemmas):
charpoly_dimN … : (T₂|S_k).charpoly = Matrix.charpoly Mₖ
-- 2. the engine (n+1 certified `eval_det` determinants + interpolation):
CharpolyEngine.charpoly_of_eval_eq Mₖ Pₖ hdeg hevals : Matrix.charpoly Mₖ = Pₖ
-- 3. degree/monicity of the literal (elaborator-side tactics):
hmon : Pₖ.Monic by monicity!;  hdeg : Pₖ.natDegree = n by compute_degree!
-- 4. Rabin certificates at ℓ (f̄ = Pₖ coeffs mod ℓ as a List ℤ literal):
hmap : Pₖ.map (Int.castRingHom (ZMod ℓ)) = RabinCert.toPoly ℓ f̄   (simp)
hmon'/hnd : monicity!/compute_degree! after `simp only [RabinCert.toPoly]`
h1 : zpxw ℓ f̄ (bitsOf F (ℓ ^ n)) [1] = [0, 1]                     (decide +kernel)
h2 q : ∃ w, zpgcd ℓ w f̄ (zpxwsubX ℓ f̄ F (ℓ ^ (n / q))) = [1]       (⟨W, by decide +kernel⟩,
                                                                    W ≈ f̄.length + 4)
hF : ℓ ^ n < 2 ^ F  (F from the generator; ℓ^n ≤ 293^10 ≈ 4.7·10²⁴, 82 bits)
-- 5. assembly:
RabinCert.irreducible_of_rabin_int  :  Irreducible (Pₖ.map (Int.castRingHom ℚ))
```

The largest kernel decide is the k=120 Rabin step at ℓ = 293 (n = 10);
measured cost model says ~28 000 ZMod-muls — seconds to tens of seconds,
comfortably inside the default kernel budget (Lehmer's 128-decide runs ~100 s
under the same budget).

## Stages

1. [ ] **S1 — `CharpolyDimN.lean`.**  Abstract the `charpoly_dim4` skeleton to
   `Fin n` (basis `a : Fin n → Fin n → ℤ` strictly triangular, T-data
   `x : Fin n → Fin n → ℤ`, statement `T.charpoly = Matrix.charpoly (backsub A X)`).
   Main design task: phrase the induction so the IH closes on truncated data.
   Local `lake env lean` checks; ~300 lines expected.
2. [ ] **S2 — `tools/gen_maedan.py`.**  Emits one file per dim; byte-identical
   re-runs; asserts its recomputed matrices against the JSON; pulls basis
   coefficients via `seqPLc` (N = 2n+1) and all numerals from the JSON.
3. [ ] **S3 — dim 6 first** (`MaedaDim6Weights.lean`): local `lake env lean`
   (~5–10 s/weight measured at dim 6), then `tools/modal_run.sh --file`
   (linters on).  This validates the whole pipeline cheaply.
4. [ ] **S4 — dims 7–10**, one file at a time (spot-check dim 10 locally
   before its Modal run); Modal build per file, never two heavy stages
   concurrently.
5. [ ] **S5 — registration + audit + CI**: root/lakefile/CI lists;
   `MathProof/AxCheckDecide.lean` on Modal — target `propext`-only for every
   new `decide` (watch the `zpgcd` fuel decisions and `Fin`/`List` equality
   instances); `tools/tauceti_audit.sh` clean.
6. [ ] **S6 — bookkeeping**: research log entry, README results table,
   AGENTS.md layout section, docs landing page if warranted; merge to master.

## Risks and fallbacks

* **`charpoly_dimN` IH design** (main proof risk): if the `Fin n` induction
  takes more than 2–3 rounds, fall back to per-dim abstract lemmas generated
  for n = 6…10 from the dim-4 template — mechanical, larger files, zero proof
  risk (blueprint §6).
* **`eval_det` elaboration at dim 9–10** (61-digit entries): measured fine at
  dim 6; if dim 9–10 spikes, split each weight into its own file (module
  boundaries free elaboration memory — Iteration 18 lesson).
* **Kernel decide budget**: `decide +kernel` keeps the elaborator out of the
  loop; if a dim-10 decide still trips the kernel's deterministic timeout,
  split the certificate into per-condition lemmas (`h1`, `h2 q` are already
  separate decides) rather than raising any option.
* **`hmap` simp proof**: the Horner evaluation of the literal `Pₖ` against the
  coefficient list `f̄` — lists stay ≤ 2n+1 entries, plain `simp` expected to
  close it; if not, emit a `HornerCert`-style structural certificate.
* **Generator correctness**: regression-assert matrix equality against the
  JSON (which regressed against the proved k=24/48 charpolys), and emit the
  `cert2_ℓ` sanity decide so every weight carries two independent Rabin runs.

## Provenance

* Blueprint: `dev/blueprint:blueprint/iteration19-maeda-generic/BLUEPRINT.md`
  (§4 `charpoly_dimN` design, §5 assembly, §6 verification plan/risks — §2–3
  engines landed in the blueprint wave, `impl/blueprint/iteration19-maeda-generic`,
  merged `b5d033e`).
* Findings: `dev/blueprint:blueprint/exploration/FINDINGS-maeda-dim6-10.md`
  (cost model §2, Mathlib-tools table §1, scratchpad lessons §5 — superseded
  here where corrected above).
* Pickup pointer: master `4eaf528` (`research/blueprint-impl-wave.md` §Open).
