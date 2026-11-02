# Probe 2 FINDINGS — the Hecke index I_k and its Cramer certificates

Probe: `probe_index.py` (this directory; pure Python, ~2 min, exact).  Anchors:
the Lean-anchored `g1_data.json` M2/M3/D/N literals (themselves pinned to the
kernel-verified dim-file literals in the hecke-rational G1 audit), the Miller
normalization, kernel-verified τ (via the shared basis builder).  ALL CHECKS
PASSED (2026-11-02).

## 1. What was checked (and passed), all 54 weights

* **F1** Miller normalization `a_i(f_j) = δ_ij`; raw prodForm basis is
  q^{j+1}-leading unit-triangular; the raw↔Miller transition `Tmat` is integer
  upper-unitriangular, `|det| = 1`.
* **F2 (convention pin — G1-critical)**: the committed `g1_data` M2/M3 are the
  **coordinate matrices in the fb (raw prodForm) basis** — columns are the
  fb-coordinates of `T₂(fb j)`, built by the unit-diagonal lower-triangular
  solve (the Lean `coordsAux`/`coordN` back-substitution).  My re-derivation
  matches 54/54.  Conjugation bridge `Tmatᵀ·M2m = M2r·Tmatᵀ` holds.
* **F3** `|det C| = |det A| = I_k` where `A = (a_{2^i}(f_j))` (Miller) and
  `C = (a₁(T₂^i f_j))` (row-0s of Miller `M₂^i`) — probe-1 check E now at all
  54 weights.  (Concrete check of the bridge: at k=36, C-row2 − A-row2 =
  `2^{k-1}`·row0, the T₂² = T₄ + 2^{k-1}T₁ relation.)
* **F4 — the b2 certificate**: `Σ_i w'_i · M2r^i = I_k · M3r` **entrywise in
  RAW coordinates** (the landed-literal side — no basis bridge needed in the
  certificate: operator identities are basis-independent), where
  `w' = |det C|·w`, `w·C = v`, `v = (a₃(f_j))`.  54/54 exact.
* **F5** the committed reduced denominator `D` divides `I_k` and
  `w' = (I_k/D)·N` against the committed witness (N, D) — D ∣ I_k re-derived
  by two independent routes (index_check.py's det A; this probe's det C +
  adjugate).
* **F6 (candidate REFUTED)**: `a_i(T_m f_j) = a_j(T_m f_i)` does NOT hold in
  Miller coordinates (k=24, m=2: 20468736 ≠ 1).  Petersson self-adjointness
  does not descend to coordinate symmetry in a non-orthonormal basis.
  Recorded so the b2 worker does not chase it; independence of `T₁..Tₙ` uses
  only the dual-basis identity `φ_i(T_j) = a_j(f_i) = δ_ij` (φ_i(T) :=
  `a₁(T f_i)`), which is one line from b1's a₁-formula.
* **F7 sizing** (max digits, per dim): A-entries / I_k / w′-entries / M2r^i:
  dim 6: 62/71/91/98 · dim 8: 115/206/233/166 · dim 10: **180/462/494/248**.
  The w′ certificates (≤ 494 digits) exceed HeckeRational's 381-digit flat
  ceiling but fit the landed Horner base-10^74 chunking scheme verbatim.

## 2. Design consequences for b2 (`hecke-index`)

1. **Certificates ride the HeckeRational pattern verbatim**: per weight, emit
   `A` (Miller), the det lemma `A.det = I_k` (Mathlib `eval_det`/Bareiss —
   the `CharpolyEngine` route at 10×10 with 180-digit entries is measured
   territory), `w'` literals (Horner-chunked), and the entrywise
   `decide +kernel` identity `Σ_i w'_i • M2r^i = I_k • M3r` on the LANDED
   M2/M3 literals — no fb↔Miller bridge inside the certificate.
2. **D ∣ I_k**: generic reducedness lemma — if `aeval T₂ Q = T` with Q ∈ ℚ[X]
   of reduced denominator D and `D' • Q ∈ ℤ[X]` with `aeval T₂ (D'•Q) = D'•T`,
   then D ∣ D' — needs uniqueness of representing polys of degree < n
   (minpoly = charpoly, landed per weight as `maeda`).  Then the committed
   (N, D) + the new (w', I_k) certificate give D ∣ I_k per weight.
3. **Index statement shape** (staged): the mathematical core is
   (i) duality `T_m = Σ_j a_m(f_j)T_j` (b1+b2 generic), (ii) independence of
   `T₁..Tₙ` (dual basis, one line), (iii) `I_k = |det A| ≠ 0` ⟺
   `𝕋 ⊗ ℚ = ℚ[T₂]`, (iv) the certificates.  The lattice packaging
   (`[𝕋 : ℤ[T₂]] = I_k` as `Nat.card (𝕋 ⧸ ℤ[T₂])`) additionally needs a
   "card of quotient = |det|" bridge (~100–150 lines; Mathlib has
   `Submodule.card_eq_card_quotient_mul_card` + `AddSubgroup.index` but no
   det-bridge) — its own gate with a det-only descope.

## 3. Two-column reuse map (b2)

**Mathlib-at-pin**: `Matrix.adjugate`/`adjugateMul` (Cramer), `Matrix.det`
+ `Mathlib.Tactic.NormDet` (`eval_det`, certified Bareiss — in-project via
`CharpolyEngine`), `Submodule.span`, `Submodule.card_eq_card_quotient_mul_card`,
`AddSubgroup.index`, `Module.End` algebra; no lattice-index-by-det lemma
(checked) — build if the card packaging is kept.

**TauCeti** (study-only): `heckeTCuspAlgebra_finite` (𝕋 finite over ℤ, no
basis/index), `LinearMap.finite_adjoin_of_injective_pairing` (the abstract
duality shape).  No index/denominator formula there — b2's statement is new
formalization (Mathlib and TauCeti both lack it).

**Own library**: `HeckeRational.exists_aeval_rat_dimN` + `aeval_pow_rep`
(operator-power ↔ matrix-power), the per-weight M/Mᵗ/Xtab/Atab literals +
`coordN`/`coordsAux` (fb-coordinate machinery), `gen_hecke_rat.py` (chunked
literal emission + `--check` discipline + G1-style Lean-literal parsing),
`CharpolyEngine`, `MaedaCertC.seqPLc` (coefficient lists without Finset —
the a_m(f_j) data source for the duality), index_check.py (I_k ground truth).
