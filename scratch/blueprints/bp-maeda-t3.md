# Blueprint — Maeda's conjecture for T₃ (dims 2–10): the pipeline is operator-generic

**Status: blueprint.  Nothing in `MathProof/` is touched until stage gates pass.**
Base: `dev/iteration20-maeda-dim6-10` after Iteration 20 S6.

## 0. Objective

`Irreducible (charpoly (T₃ | S_k))` for level-one weights — first pass the 30
weights `72 ≤ k ≤ 134` with `6 ≤ dim S_k ≤ 10` (files `MaedaT3Dim{6..10}Weights.lean`),
stretch pass `k = 24…74` (dims 2–5) through the same dimension-generic engine.
Maeda's conjecture is about the Hecke algebra, not T₂ specifically: this run
doubles the verified evidence base and stress-tests the Iteration-20 pipeline's
claim of operator-genericity (`heckeTPₗ` takes any prime).

## 1. Reuse map (nearly everything)

| existing asset | where | role |
|---|---|---|
| `heckeTPₗ k hp` (operator for ANY prime with a `Nat.Prime` proof) | `MaedaLevelOne.lean` | T₃ operator, `hp := Nat.Prime.three`-style |
| `heckeT2_coeff`-shaped coefficient formula — check whether it is stated for T₂ only or for `heckeTPₗ p` | `HeckeLevelOne.lean` vs `MaedaLevelOne.lean` | the q-coefficient bridge; if T₂-specialized, prove the p-generic twin once (the proof is p-uniform) |
| `CharpolyDimN.charpoly_dimN` | `CharpolyDimN.lean` | operator-generic (any endomorphism) — zero changes |
| `CharpolyEngine.charpoly_of_eval_eq` + `eval_det` | `CharpolyEngine.lean` / Mathlib | determinant interpolation — zero changes |
| `RabinCert.irreducible_of_rabin_int` + reflected engine | `RabinCert.lean` | zero changes |
| `tools/gen_maedan.py` | tools | add a `--prime 3` mode: T-data from the T₃ coefficient formula, census from a new probe run; keep byte-identical regeneration + regression asserts |
| `research/iteration20/maeda_dim6_10_probe.py` | research/iteration20 | extend to emit `maeda_t3_dim6_10.json` (T₃ matrices, charpolys, Rabin cert primes + reflected sanity checks); the probe's Mathlib-side anchors (k=24/48 T₂) get T₃ twins validated against `#eval` |
| `MaedaCertC.seqPLc` + `HornerCert` | `MaedaCertC.lean`, `HornerCert.lean` | coefficient lists, clean certificates — zero changes |

## 2. What is genuinely new

1. **T₃ coefficient data**: for basis `Δ^i E₄^a E₆^b`, the T₃-tracks
   `(T₃ f)_m = f_{3m} + 3^{k−1} [3 ∣ m] f_{m/3}` — the generator's `tdata`
   computation swaps prime 2 → 3 (one function, well-isolated in
   `gen_maedan.py`).
2. **Numerics scale**: `3^{k−1}` for k ≤ 134 is a 63-digit factor; matrix
   entries/charpoly coefficients grow ~1.6× vs T₂.  Consequences to MEASURE
   at G2: literal sizes (the chunking infra already handles >80 digits),
   Rabin `zpxw` bit-width `F = bits(ℓ^n)` for the T₃ certificate primes, and
   kernel time of the largest decide.
3. **Certificate-prime search**: re-run per weight for the T₃ charpolys
   (h1/h2 conditions); prefer SMALL ℓ to keep F down (the probe already
   searches ascending).

## 3. Module layout

| module | content |
|---|---|
| `research/iteration20/data/maeda_t3_dim6_10.json` | census (probe-generated) |
| `tools/gen_maedan.py` (`--prime 3 --out MaedaT3Dim{n}Weights.lean`) | generator mode; T₂ default keeps Iteration-20 files byte-identical (regression `--check` MUST pass unchanged for prime 2) |
| `MathProof/ModularForms/MaedaT3Dim{6..10}Weights.lean` (generated) | same per-weight shape: basis → T₃ tables → M/MT → dets/interpolation → Rabin → `maeda_t3` |
| (stretch) `MaedaT3SmallWeights.lean` for k = 24…74 via the SAME generator in dim 2–5 mode | requires the generator's `charpoly_dim2/3/4` legacy path or `charpoly_dimN` for n < 6 (it is dimension-generic — verify) |

All light; register per AGENTS.md; never hand-edit generated files.

## 4. Stage gates

* G1: probe extension produces the JSON; Python-side regression asserts
  (T₂ columns unchanged; T₃ spot-checked against an independent q-expansion
  computation for k=24 dim 2 — and, decisively, against the T₃ charpoly of
  weight 24 known in the literature: `x² − a₃ x + 3^{23}` shape with
  `a₃ = τ(3) = 252` for Δ — use `Ramanujan.tau 3` from `Tau/Basic.lean` as
  the anchor: T₃ on S₂₄ is τ(3)·Δ, so charpoly(T₃ | S₂₄) = X² − 252·X + 3²³.
  THIS is the cheap, airtight regression the whole T₃ census hangs on).
* G2: one weight end-to-end (k=72): `maeda_t3_72` green on Modal; record
  build time / peak RSS / biggest decide.  If the kernel decides exceed
  ~10 min per file, re-search certificate primes for smaller ℓ BEFORE
  scaling; if still bad, split per-weight into per-file modules (module
  boundaries free memory) — never raise options.
* G3: dims 6–10 files green on Modal (queue, one at a time); `--check`
  byte-identical; `tauceti_audit.sh`, `AxCheckDecide` clean.
* G4: registration, research-log entry, README table column, docs page
  sentence; stretch: dims 2–5.

## 5. Risks

* **R1 hidden T₂-specialization**: `heckeT2_coeff` or the generator's
  T₂-formula folding may be hard-wired.  Audit first (grep `heckeT2` vs
  `heckeTPₗ`); the fix is one p-generic lemma, proof identical.
* **R2 kernel time**: T₂'s largest decide (k=120, ℓ=293, 28k ZMod-muls) took
  ~[S4-measured]; T₃ scales entries ~1.6×, so watch G2.  Mitigations in
  order: smaller certificate ℓ; per-weight files; per-condition lemma
  splits.  Do NOT touch `set_option`.
* **R3 elaborator heartbeats**: the staged `Lv` back-substitution pattern
  (Iteration-20 S4) is already in the generator — it carries over unchanged;
  keep `change` (never `show`).
* **R4 dims 2–5 legacy**: if the generator only emits n ≥ 6, either generalize
  (preferred — `charpoly_dimN` is dim-generic) or descope to 6–10 and record
  the reason.
