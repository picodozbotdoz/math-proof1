# blueprint/ — Task AA home (blueprint & exploration only)

Instructions for agents: `BLUEPRINT_INSTRUCTION.md` (Lean as a scratchpad —
elaboration checks, no project builds; Python-first; batched fixes).

Task AA loop: find a modular-forms open problem aligned with / building on
this repo's formalizations, produce **blueprints + exploration** (not the
implementation), commit at milestones, repeat.

## Cycle 1 (2026-10-29) — Maeda generic engine (Iteration 19) + the Sₙ bridge

Pick-up point: `research/iteration18-improvements.md` P1-4 ("decide
Iteration 19's mathematical route before building tooling") and
`research/maeda-scaling-study.md` §4 step 3.

| artifact | what it is |
|---|---|
| `exploration/maeda_dim6_10_probe.py` + `exploration/data/maeda_dim6_10.json` | exact T₂ charpolys for all 30 dim-6–10 weights, Rabin certificate primes, kernel-cost model, Frobenius cycle-type census + disc non-residues (regressions against the proved k=24/48 charpolys) |
| `exploration/FINDINGS-maeda-dim6-10.md` | headline findings, incl. the **new-Mathlib-tools table** (certified `eval_det` determinant tactic, `eval_charpoly`, interpolation lemma, `monicity!`/`compute_degree!`, the monic mod-ℓ irreducibility lift — all at the pin, all validated) |
| `lean/CharpolyInterpSketch.lean` (+ `gen_sketch_charpoly.py`) | elaborated pilot: generic `charpoly_of_eval_eq` + full k=72 charpoly via 7 certified Bareiss determinants + interpolation (~5 s local) |
| `lean/RabinCertSketch.lean` | elaborated reflected mod-ℓ polynomial engine (structural + fuel), toy and real k=72 Rabin condition kernel-decided, `[propext]` only |
| `iteration19-maeda-generic/BLUEPRINT.md` | **the Iteration 19 plan**: modules, the Rabin-theorem proof plan, `charpoly_dimN` design, generator, budget, risks |
| `dedekind-frobenius/BLUEPRINT.md` | trajectory 2: Dedekind–Frobenius cycle types + Jordan — the Mathlib gap blocking Gal = Sₙ beyond dim 5, staged delivery plan, census data already in hand |

Outcome: Iteration 19 is de-risked and much cheaper than the scaling study
assumed (its "main new engineering" is now a Mathlib tactic call); the one
new math lemma (Rabin's test, the needed direction) has a written proof plan
and validated reflection layer.

## Next-cycle candidates (pick up in order of impact)

1. **Implement Iteration 19** from its blueprint (that is main-loop work —
   `MathProof/` edits — not Task AA; a Task AA cycle can instead pre-build
   its generator self-check per improvements P1-1).
2. **Dedekind–Frobenius stage 1+2** (`dedekind-frobenius/BLUEPRINT.md` §4.1–4.2):
   the group-theory criterion + Frobenius hypothesis interface as Lean
   sketches here; disc non-residue certificates in HornerCert shape.
3. **The Maeda-statement upgrade** (`Tₙ ∈ ℚ[T₂]`; iteration19 blueprint §7):
   Hecke commutativity + field-module counting — blueprint-able in one cycle.
4. **Lehmer axis** (`maeda-scaling-study.md` §4 step 5): the 131072 packed
   attempt (slot width 96 / sparse η-packing / ≥192 GiB Modal) or a coverage
   quantification of the current verified set below 2³².
