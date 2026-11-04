# G1 audit — index-cyclic (worker b2, iteration 24)

Run 2026-11-04, `python3 -I g1_audit_cyclic.py` (reuses
`research/iteration23/hecke-index/g1_audit.py` parsers: `int_expr_eval`,
`parse_cert_N`, `parse_scaled_id_D`), against the LANDED literals of
`MathProof/ModularForms/HeckeIndexSmallWeights.lean` (Ik, Dn, bez/bezc,
det_A sign) and `HeckeRationalSmallWeights.lean` (cert = N_j, scaled_id D),
cross-checked with `research/iteration23/hecke-index/index_data.json`
(Ik, Dred, dim).  18 weights (dims 2–4), **0 failures**.

## Results

* **D > 0, Ik > 0** at all 18 weights (so the G2 packaging can use
  `Nat`-side divisibility directly; no sign issues with `D`).
* **The two landed D forms agree**: `HeckeIndexWeightKK.Dn` ==
  the `D` of `HeckeRatWeightKK.scaled_id` at every dims-3–4 weight
  (the dims-3–4 `D_dvd_Ik` consumers and my order bridge read the same
  integer).  At the six dim-2 weights `D = 1` (`D_dvd_Ik = one_dvd`).
* **The landed witnesses are already Bézout-reduced (Dred = D)**: the
  landed `bez`/`bezc` satisfy `∑ bez_j·cert_j + bezc·D = 1` (checked in
  Python; in Lean this is the kernel-decided `hbezL`), and independently
  `gcd(cert_0..cert_{n-1}, D) = 1`; `D == Dred` from `index_data.json`.
  No re-reduction is needed anywhere — blueprint G1 requirement met.
* **D ∣ Ik** arithmetically at all 18 (mirrors the landed `D_dvd_Ik`).
* **TARGET numerically confirmed**: `D = Ik` at all twelve dims-3–4
  weights (72, 168, 576, 408, 336, 96, 7115931648, 59746885632,
  105556082688, 170609983488, 1331874496512, 7905182810112) and
  `D = Ik = 1` at all six dim-2 weights (24, 28, 30, 32, 34, 38).
  All dims-3–4 Ik > 1, so via the iff those weights will also give
  `𝕋 ≠ ℤ[T₂]`.
* **Sign conventions** (for b1's det bridge; my statements are
  sign-free): `det_A : A.det = ±Ik` with sign − at w36, 42, 46, 48, 50,
  54, 56 and + at the other eleven.  `Ik` itself is positive everywhere.

## Mathlib-at-pin API for the F5 card-divisibility route (all read)

* `AddSubgroup.relIndex H K := (H.subgroupOf K).index`,
  `index N = Nat.card (G ⧸ N)` — `Mathlib/GroupTheory/Index.lean:55–62`.
* `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (s) :
  Nat.card α = Nat.card (α ⧸ s) * Nat.card s`
  (to_additive of `Subgroup.card_eq_card_quotient_mul_card_subgroup`,
  `Mathlib/GroupTheory/Coset/Card.lean:52`) — Lagrange shape, no
  finiteness hypothesis.
* `QuotientGroup.quotientKerEquivOfSurjective (hφ : Surjective φ) :
  G ⧸ ker φ ≃* H` — `Mathlib/GroupTheory/QuotientGroup/Basic.lean:159`
  (additive twin available).
* `ZMod.lift (n : ℕ) : { f : ℤ →+ A // f n = 0 } ≃ (ZMod n →+ A)`
  for `[AddGroup A]` — `Mathlib/Data/ZMod/Basic.lean` (§lift); the
  universal property turning `D • [T₃] = 0` into `ZMod D →+ G`.
* `ZMod.intCast_surjective : Surjective ((↑) : ℤ → ZMod n)` —
  `Mathlib/Data/ZMod/Basic.lean:229` (surjectivity of the lift).
* `ZMod.fintype [NeZero n]`, `ZMod.card : Fintype.card (ZMod n) = n`
  (`Mathlib/Data/ZMod/Defs.lean:155,163`) + `Nat.card_eq_fintype_card`.
* `AddSubgroup.index_eq_one : N.index = 1 ↔ N = ⊤`,
  `relIndex_eq_one : H.relIndex K = 1 ↔ K ≤ H` (`GroupTheory/Index.lean`),
  `Subgroup.subgroupOf_eq_top : H.subgroupOf K = ⊤ ↔ K ≤ H`
  (`Mathlib/Algebra/Group/Subgroup/Map.lean:366`) — the iff's core.
* `Submodule.toAddSubgroup_le : p.toAddSubgroup ≤ p'.toAddSubgroup ↔
  p ≤ p'` (`Mathlib/Algebra/Module/Submodule/Basic.lean:130`),
  `Submodule.toAddSubgroup_injective` (`.../Defs.lean:334`) — the
  submodule ↔ AddSubgroup bridge for the iff statement.

## G2 design consequence (recorded)

`D = I_k` needs only `D • [T₃] = 0` + cyclicity (⟹ `Ik.natAbs ∣ D` via
the ZMod.lift route) + the landed `D ∣ Ik` + positivity — the
order-MINIMALITY (Bézout) is not on the critical path for `D_eq_Ik`
(it is proved anyway as the standalone `order_minimal` lemma, mirroring
`den_dvd_index`'s cross-multiplication).  This stays inside the
blueprint's descope ladder: minimality is available but not load-bearing.
