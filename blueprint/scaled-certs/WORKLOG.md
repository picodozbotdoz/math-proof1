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
