# Worklog — impl/iteration24/index-cyclic
Append dated entries as you go (stage gates passed/failed, Modal runs with
build time + peak RSS, decisions, deviations from the blueprint).  This file
is the inter-session resume point: make it possible to continue cold.
## Entries

**2026-11-04 12:31 UTC — session 1 start (worker index-cyclic, branch impl/iteration24/index-cyclic, base f7628f6).**
Read: AGENTS.md, CODING_STANDARDS, RESEARCH-WORKFLOW §4d/§5/§6/§9, my BLUEPRINT,
FINDINGS F1/F5/F7. Inbox polled: empty (no STEER-index-cyclic-*/STEER-all-*).
Trunk check: dev/iteration24-hecke-index @ 9357338 = base + wave-spawn commit →
b1 (index-card) NOT landed yet → G1 + the non-importing parts of G2 proceed
against the b1 API contract (blueprint/index-card/BLUEPRINT.md §0(i)) with a
LOCAL STUB of MathProof/ModularForms/HeckeLatticeIndex.lean (never committed).
Plan:
- G1: audit landed D / D_dvd_Ik forms for the 12 dims-3–4 weights (reuse
  research/iteration23/hecke-index/g1_audit.py parsers), verify D > 0 and
  Dred = D, pin Mathlib names for card-dvd route. Commit audit.
- G2: HeckeCyclic.lean generic (quotient_span_of_le_four, order bridge,
  card_dvd_of_generator, D_eq_Ik, iff). Green on Modal (mrun.sh).
- G3: generated HeckeCyclicWeights.lean (18 weights dims 2–4) + registration
  + audits (root 0/0, AxCheckDecide, tauceti).
  Verification venue: /home/doz/tmp/math-proof1-temp/agent-work/index-cyclic/runs/mrun.sh.

**2026-11-04 12:55 UTC — G1 CLOSED (green, committed).**
`research/iteration24/index-cyclic/g1_audit_cyclic.py` (+ G1-AUDIT.md):
parsed the LANDED Ik/Dn/bez/bezc (HeckeIndexSmallWeights) and cert/scaled_id-D
(HeckeRationalSmallWeights) for all 18 dims-2-4 weights, cross-checked with
iteration-23 index_data.json. 0 failures:
- D > 0, Ik > 0 everywhere; Dn == scaled_id D (the two landed D forms agree);
- landed witnesses ALREADY Bézout-reduced: bez identity + gcd(N,D)=1 + D==Dred;
- D ∣ Ik (arithmetically, mirrors landed theorem);
- TARGET numerics: D == Ik at all 12 dims-3-4 (72 … 7905182810112, all > 1),
  D == Ik == 1 at all 6 dim-2; det_A sign = − at w36/42/46/48/50/54/56 (for b1).
Mathlib-at-pin pins for F5 recorded in G1-AUDIT.md (relIndex/index defs,
card_eq_card_quotient_mul_card, quotientKerEquivOfSurjective, ZMod.lift +
intCast_surjective + card, index_eq_one/subgroupOf_eq_top, toAddSubgroup
bridges). Design note: order-MINIMALITY is off the critical path for D=Ik
(card_dvd gives Ik.natAbs ∣ D; landed D_dvd_Ik gives D ∣ Ik; positivity
closes) — stays inside the pre-authorized descope ladder.
Next: G2 HeckeCyclic.lean WITHOUT any b1 import (own `t2Span` in the exact
contract form `span ℤ (range fun j : Fin n => T₂^j)`; at b1-adoption either
rfl-identical or a one-line span bridge — deviation recorded at next entry).
No stub needed for G2; G3 waits for b1's per-weight card facts.
