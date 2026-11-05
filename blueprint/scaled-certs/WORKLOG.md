# WORKLOG — scaled-certs (iteration 25)

## 2026-11-05 — start
- Worker started on branch impl/iteration25/scaled-certs @ 0644b00.
- Next: G1 audit (read AGENTS.md recipe, HeckeLatticeIndex.hcard_of_check,
  generators, mrun.sh).

## 2026-11-05 — G1 (desk audit, no Modal run)
- Cells: `ext a b; fin_cases a <;> fin_cases b <;> decide +kernel` on
  `(∑ j ∈ Finset.range n, w j • M2 ^ j) a b = (s • M) a b` — all three
  causes present: `Finset` sum (Multiset quotient), `!![…]` literals of
  M2/M (Quot.sound via Matrix.of / vecCons), and in the big files the
  chunked literals `c * 10 ^ 74|80|e` (Monoid.npow).
- Decision: new light Mathlib-only module `MathProof/ModularForms/ScaledCert.lean`
  (`ScaledCert.powL`, `cellL`, `scaledCheck`, bridge `scaled_of_check`
  with pow-free value bridges `hw : ∀ j : Fin d, w j = wv j`, `hs : s = sv`).
  Matrix tables `t2tab`/`t3tab` (+ `ht2tab`/`ht3tab`, `fin_cases <;> rfl`)
  emitted once per weight in the HeckeRational files and REUSED by the
  HeckeIndex files (which import them).  Pow-free `certv`/`Dv`/`wpv`/`Ikv`
  only where the landed literal contains `^`.  Not importing
  HeckeLatticeIndex (it imports HeckeIndex/HeckeFieldRat — would weigh on
  HeckeRationalSmallWeights); the nopow renderer is reused from
  gen_hecke_index.py (imported by gen_hecke_rat.py).

## 2026-11-05 — G2 green
- `MathProof/ModularForms/ScaledCert.lean` (Mathlib-only imports) green on
  Modal: 40 s wall / 3.61 GiB peak tree (99 s round trip).  Registered in
  `MathProof.lean` + `defaultTargets` (after HeckeRational).
- Generic names: `ScaledCert.powL`, `cellL`, `scaledCheck`, `powL_getD`,
  `cellL_eq`, `scaled_of_check`.

## 2026-11-05 — G3 start
- gen_hecke_rat.py regenerated (tables t2tab/t3tab + hscaled + scaled_of_check;
  certv/Dv pow-free only where `^` appears).  Running Modal --file
  HeckeRationalSmallWeights (expected ~2-5 min).

## 2026-11-05 — G3/G4 run
- HeckeRationalSmallWeights green: 77 s / 7.08 GiB tree (5.83 GiB module).
- gen_hecke_index.py: `scaled` now via `hscaled` + `ScaledCert.scaled_of_check`,
  reusing `HeckeRatWeightK.t2tab/t3tab/ht2tab/ht3tab`; `wpv`/`Ikv` pow-free
  where needed.  All 4 files regenerated; --check byte-identical.
- Starting Modal `--target MathProof.AxCheckDecide` (full light root + both
  audit passes); expected 30-60 min wall (downstream of the HeckeRational
  files rebuilds: HeckeIndex*, HeckeIndexCard*, HeckeField*, HeckeCyclic*,
  HeckeRingGens*).
