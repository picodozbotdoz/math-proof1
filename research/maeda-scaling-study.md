# Maeda beyond dimension 4 — a scaling study (pre-iteration feasibility probe)

**Question.** Iterations 14–16 verify Maeda's conjecture for every level-one
weight with `dim S_k ≤ 4` (`k = 24 … 62`, `k ∉ {26, 60}`).  What would it take
to push the formalized coverage to `dim S_k = 5` (weights `60, 64, 66, 68, 70,
74`) and onward to `dim S_k = 25` (all 63 even weights `60 ≤ k ≤ 314`)?

**Method.** `research/maeda-scaling-probe.py` (this directory) recomputes, in
exact integer arithmetic, exactly what the Lean machinery computes: the
triangular basis `Δ^i E₄^a E₆^b`, the matrix of `T₂` read off the first
q-coefficients (the `charpoly_dim2/3/4` algorithm), the characteristic
polynomial (Bareiss determinants + interpolation), and irreducibility
certificates.  It reproduces the *proved* charpolys at `k = 24` and `k = 48`
byte-for-byte, so its output is a faithful predictor of the Lean side.  As
always in this repo the numbers are only certificates; Lean re-checks
everything.

---

## 1. The data

### dim S_k = 5 (weights 60–74): everything is small

| k  | charpoly of `T₂` (leading terms; coefficients ≤ 54 digits) | irr. cert ℓ | disc non-res. mod | 3-cycle prime |
|----|---------------------------------------------|------------|-------------------|---------------|
| 60 | `X⁵ + 449691864X⁴ − 2209450184054433792X³ − 736010060393513697870348288X² + ⋯` | 83 | 37 | 67 |
| 64 | `X⁵ − 507315096X⁴ − 26316207229657439232X³ + ⋯` | 73 | 29 | 59 |
| 66 | `X⁵ + 3959709648X⁴ − 142850166119005483008X³ + ⋯` | 79 | 29 | 53 |
| 68 | `X⁵ − 5554901256X⁴ − 528742419683384143872X³ + ⋯` | 97 | 23 | 53 |
| 70 | `X⁵ + 18005734368X⁴ − 1942747456996431618048X³ + ⋯` | 79 | 41 | 73 |
| 74 | `X⁵ + 92089333488X⁴ − 19817164982845968703488X³ + ⋯` | 79 | 41 | 37 |

The full coefficients are printed by the probe (rerun
`python3 research/maeda-scaling-probe.py`, ≈ 10 s); the exact values for the
Lean file come from the generator, not from this table.

*Irreducibility certificate*: a reducible monic quintic has a factor of degree
≤ 2, so "no root mod ℓ + no monic quadratic factor mod ℓ" suffices — the
**exact same `decide +kernel` ℓ²-scan shape as the committed quartic
certificate** (`irreducible_quartic_of_mod`): a quadratic `X² + uX + v` forces
the cubic cofactor's `r, s, t`, leaving two equations to scan over.  All six
weights have such ℓ ≤ 97.

### Scaling law (probe, `k = 12·dim`)

| dim | k | T₂ matrix entries | charpoly coeffs | Python time | Rabin cert ℓ |
|-----|-----|-------------------|-----------------|-------------|--------------|
| 6 | 72 | ≤ 32 digits | ≤ 64 digits | 0.01 s | 107 |
| 8 | 96 | ≤ 43 digits | ≤ 115 digits | 0.02 s | 149 |
| 10 | 120 | ≤ 55 digits | ≤ 179 digits | 0.03 s | 293 |
| 12 | 144 | ≤ 67 digits | ≤ 258 digits | 0.05 s | 163 |
| 16 | 192 | ≤ 91 digits | ≤ 459 digits | 0.11 s | 227 |
| 20 | 240 | ≤ 116 digits | ≤ 719 digits | 0.28 s | 313 |
| 25 | 300–314 | ≤ 151 digits | ≤ 1176 digits | 0.95 s | 383–643 |

Digit counts grow ≈ quadratically in dim (they track `2^{k/2}` — coefficient
sizes are governed by the Hecke eigenvalue scale `2^{(k−1)/2}`, not by anything
kernel-hostile).  At dim 25 everything is still ordinary GMP-sized: 1176-digit
charpoly coefficients, 151-digit matrix entries.

**Maeda holds numerically in the whole range probed**: every charpoly above is
Rabin-irreducible mod (at least) two primes.  This is consistent with the
literature (Ghitza–McAndrew verified to weight ≈ 14000, i.e. dim ≈ 1160).

---

## 2. What each layer needs

### (a) Coefficient engine — works as-is, one knob to turn

`seqPL` lists of length `2d+1` cover dim 5 (11) through the existing `N = 12`
generator; `dim ≤ 10` (length ≤ 21) is covered by the existing verified
`tauTable` (τ through 21).  **Dim ≥ 11 needs τ(22 … 2d)** appended to
`tauTable` (individually kernel-decided values from the `Basic.lean` engine —
cheap: the whole 256-coefficient nonvanishing decide costs ~2 CPU-minutes).
Dim 25 needs τ through 50.

### (b) charpoly extraction — the main new engineering

`charpoly_dim2/3/4` + `charpoly_fin_*` are per-dimension by hand; a Laplace
formula does not scale past 4.  Generic route (recommended):

* a `Fin n`-structural `charpoly_dimN` (triangular q-coefficient
  back-substitution — same proof shape, inductive), and
* a **reflected Bareiss determinant** over `ℤ` plus interpolation:
  `Matrix.charpoly M = P` for monic `P` of degree `n` once
  `P(t) = det(tI − M)` at `n+1` integer points (each a kernel-decided Bareiss
  det).  Mathlib supplies `RingHom.map_det` (eval commutes with det) and
  `Polynomial.eq_of_natDegree_lt_card_of_eval_eq'`.

Cost at dim 25: 26 Bareiss dets of 25×25 integer matrices (≈ 15K exact
mult/div on ≤ 3000-digit integers each) — seconds of kernel time.

### (c) Irreducibility certificates — quintic scan now, Rabin from dim 6

* **dim 5**: no-root + no-quadratic ℓ²-scan (§1) — a small variant of
  `irreducible_quartic`.  Data: ℓ = 73–97.
* **dim ≥ 6**: "no factor of degree ≤ n/2" is no longer a bounded scan.
  Use **Rabin's test** mod ℓ: `f̄ ∣ X^(ℓⁿ) − X` and
  `gcd(f̄, X^(ℓ^(n/q)) − X) = 1` for primes `q ∣ n`.  This needs a reflected
  `ZMod ℓ`-polynomial square-and-multiply (`X^(ℓⁱ) mod f̄`) — the same
  list-reflection pattern as `seqPL`.  Kernel cost at dim 25 (ℓ ≈ 500):
  ~135 squarings of degree-24 polynomials ≈ 170K `ZMod ℓ` multiplications —
  seconds to minutes.
  Data: certificate primes ℓ ≤ 643 for all six dim-25 weights.

### (d) Galois group `S₅` — possible with current tools, via a sextic resolvent

The quartic module's architecture (explicit resolvent with `ring`-checked
identities + Vieta + discriminant) extends once more:

* `Gal ↪ S₅` (faithful action on the 5 roots — `galActionHom_injective`).
* `5 ∣ |Gal|` (irreducible ⇒ transitive) and **`6 ∣ |Gal|`** from an
  **irreducible sextic resolvent**: for the six pentagon structures
  `P` on `{0,…,4}` (the six 5-cycles up to powers; their stabilizer in `S₅` is
  `F₂₀`), `θ_P = Σ_{edges of P} x_i x_j` has six conjugates; the stabilizer
  argument gives `[ℚ(θ_P) : ℚ] = |Gal|/20`, so irreducibility of the sextic
  forces `6 ∣ |Gal|`.  Identifying the sextic's coefficients is classical
  (they are symmetric functions of the roots ⇒ polynomials in `a,b,c,d,e`);
  the degree-bound argument is the same "θ is a root of the resolvent"
  `ring`-identity + Vieta pattern as `MaedaGalois4`, roughly 2× its size.
* So `30 ∣ |Gal|`, `|Gal| ∣ 120` ⟹ `|Gal| ∈ {30, 60, 120}`; exclude 30 (no
  index-4 subgroup of `S₅`: coset-action core argument via
  `alternatingGroup.isSimpleGroup` — **in Mathlib**) and 60 (index 2 ⟹ `A₅`
  ⟹ square discriminant, excluded by the non-residue data of §1 — the
  `eq_alternatingGroup_of_index_eq_two` + δ-machinery already in
  `MaedaGalois/MaedaGalois4`).
* ⟹ `Gal = S₅`.

Design step before committing: write the explicit sextic resolvent into the
probe and confirm it is irreducible for the six weights (the (1,1,3)
factorization primes in §1 independently predict `3 ∣ |Gal|` via Frobenius,
as a cross-check).

### (e) Galois `S_n` for `n ≥ 6` — the genuine mathematical gap

The ad hoc resolvent game stops at 5.  The right generic tool is
**Dedekind/Frobenius**: "f̄ squarefree mod ℓ with a factor of degree e ⟹ Gal
contains an e-cycle", plus **Jordan's theorem** (transitive + p-cycle,
`p ≤ n−3` ⟹ contains `A_n`) to conclude `S_n` from an odd cycle + a
`(n−1)`-cycle or p-cycle.  Neither is in Mathlib (checked: `Polynomial.Gal`
has `restrict`, `galActionHom`, `card_of_separable`, but no reduction-mod-ℓ
Frobenius bridge; no Jordan).  The numerical certificates already exist —
every probed weight has (1,1,n−2)-type primes (a transposition) and p-cycle
primes — but formalizing the bridge is an algebraic-number-theory-sized
project (decomposition groups / Hensel lifting).  Recommend: state Galois
instances only up to dim 5 for now; treat Dedekind–Jordan as a separate
long-term workstream (valuable Mathlib contribution).

---

## 3. Cost extrapolation (Lean side)

Measured anchors: `MaedaSmallWeights` (11 weights, dims 2–3) 167 s on Modal;
`MaedaDim4Weights` (6 weights) 145 s; `MaedaGalois4` 261 s — all light, zero
warnings, ~50–60 KB generated files.

* **dim 5 instance file** (6 weights): same lemma count as dim 4 with slightly
  bigger integers, plus a `charpoly_dim5`; expect ≈ 150–300 s Modal, file
  ≈ 60 KB.  `S₅` module comparable to `MaedaGalois4` (≤ ~300 s).
* **dims 6–10** (weights 72–122, 28 weights): generic charpoly + Rabin
  modules land first; per-weight cost grows slowly (entries ≤ 55 digits).
  Batchable per dim or per few weights; hours of Modal time in total, all
  light modules.
* **dim 25** (6 weights, weights 300–314): 1250 q-coefficient literals
  (≤ 151 digits) + 625 matrix entries + 26 coefficients of ≤ 1176 digits per
  weight — generated file ≈ 2–3 MB for all six; kernel work dominated by the
  Bareiss/Rabin decides, estimated minutes per weight on Modal (fits the 4 h
  timeout with room; the estimates above want a one-weight Modal pilot before
  scheduling the full batch).

No new heavy-module infrastructure is needed anywhere on this axis —
everything stays "light" (sub-minute-to-minutes decides), unlike the Lehmer
packed route.

---

## 4. Recommended sequence

1. **Iteration 17 — Maeda dim 5, irreducibility** (weights 60, 64, 66, 68,
   70, 74): `charpoly_dim5` + `irreducible_quintic` (ℓ²-scan) + generated
   `MaedaDim5Weights.lean`.  Small, certain, and completes
   `dim ≤ 5 ⟺ all k ≤ 74 except 72`.
2. **Iteration 18 — Galois `S₅`** via the sextic resolvent (probe the
   resolvent first, §2d).
3. **Iteration 19 — generic engine**: `Fin n` `charpoly_dimN` + reflected
   Bareiss/interpolation + Rabin certificate; regenerate dims 2–5 through it
   (regression: byte-identical charpolys) and add dims 6–10.
4. **Ratchet**: dims 11–25 in batches (τ-table extension at dim 11; slot the
   63-weight run as several generated files).  End state: **Maeda
   irreducibility for every level-one weight `k ≤ 314` (`dim S_k ≤ 25`)**.
5. Optional alongside: the cheap general lemma "`charpoly(T₂)` irreducible ⟹
   `T_n` is a polynomial in `T₂` for every n" (Hecke algebra = `ℚ[T₂]`),
   upgrading the statements from "T₂-irreducibility" to the usual statement of
   Maeda's conjecture; and on the Lehmer axis, a 131072 packed attempt (slot
   width 96 + sparse η-packing + a ≥ 192 GiB Modal container) if a bigger
   headline bound is wanted — the scaling study's route, low mathematical
   risk, modest payoff (dense bound doubles; initial segment 70481 → ~131.5k).

## 5. Artifacts

* `research/maeda-scaling-probe.py` — the probe (exact integer arithmetic;
  regressions against the proved k = 24 / k = 48 charpolys; Rabin
  certificates; discriminant residues; factorization-type census for the
  future Dedekind route).  Running it reproduces every number in §1.
