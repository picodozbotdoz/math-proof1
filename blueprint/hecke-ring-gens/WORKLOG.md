# Worklog — impl/iteration24/hecke-ring-gens
Append dated entries as you go (stage gates passed/failed, Modal runs with
build time + peak RSS, decisions, deviations from the blueprint).  This file
is the inter-session resume point: make it possible to continue cold.
## Entries

### 2026-11-04 session 1 — START (hecke-ring-gens, gates G1–G4)
Read: AGENTS.md, CODING_STANDARDS.md, RESEARCH-WORKFLOW §4d/§5/§6,
BLUEPRINT hecke-ring-gens, FINDINGS F1–F7, index-card BLUEPRINT §0(i) (b1
contract). Inbox polled at session start: no STEER-hecke-ring-gens-* /
STEER-all-* present (only done/, README.md).
Plan (blueprint gates):
- G1 audit: re-derive M5/M7 coordinate matrices for 36 dims-5–10 weights
  (g1_audit pattern, sanity anchors per F4/F7); independently re-derive
  greedy table; MEASURE certificate routes (a) unimodular monomial n-subsets
  at the 22 {3,5}-weights with a CORRECT rank-tracking search (orchestrator's
  throwaway is not evidence), (b) HNF basis literals with |det| = idx3 / = 1.
  Commit measurement data + decision.
- G2 generic HeckeRingGens.lean: 𝕋 = Subring.closure {T₂,T₃,T₅,T₇} (try
  adjoin first; noncomm End risk noted) for n ≤ 10, zero per-weight
  certificates, instantiated at all 54 weights.
- G3 decision gate at w60: chosen route green (idx3 + 𝕋 = ℤ[T₂,T₃,T₅]);
  descope ladder per blueprint §4 G3.
- G4 full generated files + registration + audits.
Verification: mrun.sh seeded runner only (tools/modal_run.sh broken from
worktree). (ii) needs b1's HeckeLatticeIndex — check trunk progress at every
checkpoint; until b1 lands, develop against index-card BLUEPRINT §0(i)
  contract with a LOCAL STUB (never commit the stub).

### 2026-11-04 session 1 — G1 progress + before-run entry
G1 audit script written: research/iteration24/hecke-ring-gens/g1_ring_gens.py
(own echelon/transform/search implementations on top of g1_audit prodForm
arithmetic; self-tests included). Two bugs found+fixed during dev:
- Lean M2/M3 literals are RAW-basis coordinate matrices (g1_audit C2) — my
  first A1 compared Miller-basis ones.
- my incremental Euclid in add_row_inc had a broken swap; the w60 "no
  unimodular subset" it reported was an artifact (exactly the class of bug
  the briefing warned about — throwaway searches are not evidence either
  way). After the fix: **route (a) EXISTS at w60/w64**: subset {T₁, T₂, T₂²,
  T₃, T₅} (labels (0,(0,0)),(1,(0,0)),(2,(0,0)),(0,(1,0)),(0,(0,1))) has
  |det| = 1 — TINY certificate (5 monomial rows + det ±1), no representation
  coefficients needed. Route (b) at w60 viable too but strictly costlier:
  B235 1d entries / U235 18d; B23 2d / U23 42d (idx3 = 10 at w60).
Timing: w64 single-weight audit = 14 s. NEXT RUN (>10 min expected): the
full 36-weight audit with C1 subset search at all 22 {3,5}-weights, budget
4M/1M/300K nodes by dim. Expected wall: 15–40 min (36 weights × ~15–60 s
plus searches). Target: g1_data.json full table + stdout report. After:
commit G1.

### 2026-11-05 session 2 — START (fresh respawn after operator wrap-up)
Resume point: salvage cbfc588. Inbox polled: no STEER-hecke-ring-gens-* /
STEER-all-* (only done/, README.md). Plan: verify G1 log/data → close G1;
G2 generic module; G3 gate; G4 generated per-weight refinements.

### 2026-11-05 session 2 — G1 CLOSED + G2 design
G1 verified: g1_table2.log ends "{3,5}-weights: 22 (expect 22) / failures: 0 /
G1 AUDIT OK"; g1_data.json (36 weights) is byte-identical to the salvage
commit (git status clean) — G1 closed, no rerun.
KEY OBSERVATION (changes G3/G4 shape, cheaper than blueprint §0(ii)):
ℤ[T₂,T₃,T₅] = span_ℤ{T_m : m {2,3,5}-smooth}, so
* dims ≤ 6: 𝕋 = ℤ[T₂,T₃,T₅] is CERTIFICATE-FREE (T₁..T₆ all smooth) — 12 of
  the 22 {3,5}-weights (dims 5–6) need no data at all;
  likewise 𝕋 = ℤ[T₂,T₃] for n ≤ 4 and 𝕋 = ℤ[T₂] for n ≤ 2;
* dims 7–9 (10 weights 88,92,94,98,100,104,106,110,116,122): only T₇ needs a
  certificate: T₇ = ∑ cₜ T_{Mₜ}, Mₜ smooth ≤ 3n; probe (scratch t7probe.py):
  gcd of the T₇-Miller-coordinate over smooth m ∈ (n, 3n] is 1 at all 10 —
  certificate = Bezout + the q-lemma rows a₇(fᵢ) = ∑ cₜ a_{Mₜ}(fᵢ) (landed
  MaedaT3 q-lemmas, m ≤ 3n), no relIndex, no index-card dependency.
G2 module rewritten (generic `gensOf k ps`, smooth-closure lemma, transport,
corollaries 2357/n≤10, 235/n≤6, 23/n≤4, 2/n≤2, 235_of_t7, row certificate
`heckeTM_mem_closure_of_rows`). WIP bugs fixed (dvd.trans order, rw [hc],
smul_zero, op_eq hZsum). NEXT: Modal --file HeckeRingGens (expect 3–10 min).
G2a GREEN: HeckeRingGens.lean Modal --file 65 s wall / 4.76 GiB module peak
(5.99 GiB tree), 0 errors / 0 warnings; tauceti audit clean (0 sopt/eval/nat/
sorry). Registered: defaultTargets + MathProof.lean; ci_targets --report OK
(77 default, push tier 55 incl. HeckeRingGens). NEXT: generator
tools/gen_hecke_ring_gens.py → HeckeRingGens{Small,}Weights instances (54)
+ T₇ row certificates at the 10 dims-7–9 {3,5}-weights.
