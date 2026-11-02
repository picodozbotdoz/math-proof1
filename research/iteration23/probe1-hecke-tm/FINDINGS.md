# Probe 1 FINDINGS — the composite Hecke operators T_m (hecke-tm)

Probe: `probe_tm.py` (this directory; pure Python, ~2 min, exact integers).
Anchors: kernel-verified τ values (`Basic.lean` tau_one..tau_twenty_one), the
landed prime coefficient formula shape (`heckeTP_qExpansion_coeff`), the
Miller-basis normalization (`a_i(f_j) = δ_ij`, i, j ≤ n — same builder as
`index_check.py`).  ALL CHECKS PASSED (2026-11-02).

## 1. What was checked (and passed)

* **A — prime specialization**: the general-m action
  `(T_m f)_n = Σ_{d | gcd(m,n)} d^{k-1} f_{mn/d²}` reproduces the landed
  `(T_p f)_n = f_{pn} + p^{k-1} [p|n] f_{n/p}` verbatim for p ∈ {2,3,5,7}.
* **B — T-calculus multiplicativity** `T_m ∘ T_n = Σ_{d | gcd(m,n)} d^{k-1}
  T_{mn/d²}`: 25 (m,n) pairs incl. composite-composite ((4,6), (6,9), (8,12),
  (12,18), (16,18), (10,15), …) on every Miller basis element + Δ at
  k ∈ {24,36,48}, 12 coefficients each (each coefficient is a full integer
  identity; trust-region discipline documented in the script).
* **C — Δ eigenform anchor**: `T_m Δ = τ(m)·Δ` for ALL m ≤ 21, τ(m) from the
  kernel-verified table (+ Mordell for composites).  Note: this anchor CAUGHT
  a wrong hand-typed τ table (τ(18) = 2727432, not 27674880 — the typed list
  was shifted from index 18 on).  Anchors work.
* **D — duality matrix identity** (the b2 core): with
  `M(m) := (a_i(T_m f_j))_{i,j ≤ n}`, `M(1) = I` and
  `M(m) = Σ_j a_m(f_j) · M(j)` for m = 1..40 at k ∈ {24,36,48,64}
  (dims 2..5).  This is the coefficient-level identity behind
  "T₁…Tₙ is a ℤ-basis of 𝕋 and T_m = Σ_j a_m(f_j)T_j".
* **E — unitriangular bridge**: `T₂^i` (composition power) is an INTEGER
  UNITRIANGULAR combination of the honest `T_{2^j}`, j ≤ i, verified at dims
  2..10 (k = 24,36,48,64,120) by exact rational solve (leading coeff 1,
  denominators 1).  So {T₂^i} and {T_{2^i}} span the same ℤ-lattice:
  `det A = det C` up to sign, A := (a_{2^i}(f_j)), C := (row-0s of M₂^i).

## 2. The definition route for T_m (design conclusion)

Two routes for honest composite T_m:

1. **Coset-sum route** (TauCeti's, `TauCeti/NumberTheory/ModularForms/LevelOne/
   Hecke.lean` at origin/main — study only): `T_n = Σ_{A ∈ reps n} f ∣[k] A`
   over upper-triangular reps of `SL₂(ℤ)\ℳ_n`; invariance by the
   right-multiplication permutation argument (`repsRightMul_injective` +
   coset absorption by left-invariance).  ~150 lines riding their
   `FixedDetMatrices.reps` infrastructure, which Mathlib-at-pin does NOT
   have (Mathlib's only "Hecke" hits are the abstract `NumberTheory/
   HeckeRing/Defs.lean` and irrelevant category-theory names — checked).
2. **Recursive route (RECOMMENDED — no new analysis)**: keep the LANDED prime
   `T_p` (`HeckeLevelOne.heckeTP`) and define on `CuspForm 𝒮ℒ k`:
   `T_1 = id`, `T_{p^{r+1}} = T_p ∘ T_{p^r} − p^{k-1} T_{p^{r-1}}`,
   `T_m = ∏_{p^e ∥ m} T_{p^e}` (order-free: prime commutativity landed in
   `heckeTPₗ_commute`).  Every operator so defined is a ℤ-combination of
   compositions of landed operators — linear, cusp-preserving, commuting by
   construction.  Then PROVE the general coefficient formula
   `heckeTM_qExpansion_coeff` by induction (the induction step is exactly
   probe check B), and everything downstream uses only that formula +
   `qExpansion_coeff_ext` (landed).  The classical coset operator satisfies
   the same coefficient formula (TauCeti's
   `qExpansion_coeff_heckeTCuspLevelOne`), hence coincides with ours on cusp
   forms — a remark, not a formal need.
   Cost estimate: the technical heart is the divisor-lattice reindexing in
   `T_p ∘ T_n` (one unrolling + p ∣ n case split, the `HeckeCommute`
   pattern with `Nat.divisors` Finset bookkeeping); est. 300–500 lines
   light module, no cosets, no S-invariance, no new Mathlib needs.

## 3. Feeds

* b1 (`hecke-tm`): the recursive definition + `heckeTM_qExpansion_coeff` +
  `heckeTM_mul` (full multiplicativity) + `a₁(T_m f) = a_m(f)` + the
  `T₂ ∘ T_m` two-term recurrence — the complete algebraic Hecke calculus.
* b2 (`hecke-index`): D is the duality mechanism (to be proven from
  `heckeTM_qExpansion_coeff` + `heckeTM_mul` by coefficient comparison on
  the Miller basis); E is the `det A = det C` lattice bridge.
* Probe incident for the record: dims must be read from `g1_data.json`
  (k=50 is dim 3, k=62 dim 4; dim-5 weights are {60,64,66,68,70,74}) —
  the `basis()` builder only supports prodForm shapes with b ≤ 2, fine for
  all 54 weights (it is the same builder `index_check.py` used).

## 4. Two-column reuse map (b1)

**Mathlib-at-pin**: `Finset.Nat.divisors`/`Nat.divisors`, dvd-lattice
lemmas, `Finset.sum_subset`, `Nat.Prime.dvd_mul` — for the reindexing; no
Hecke-operator content (checked: no modular-form Hecke ops in Mathlib at
the pin; `NumberTheory/HeckeRing/Defs.lean` is the abstract Γ₀-oriented
Hecke ring, not usable here).

**TauCeti** (study-only): `heckeTCuspLevelOne` (definition shape),
`qExpansion_coeff_heckeTCuspLevelOne` (the general-n coefficient formula —
CONFIRMS our recursive T_m coincides with the classical operator on cusp
forms), `qExpansion_coeff_one_heckeTCuspLevelOne` (a₁(T_n f) = a_n(f) — the
duality ingredient).  Nothing to port (their `FixedDetMatrices` dep is
absent from Mathlib; the recursive route avoids the whole surface).
