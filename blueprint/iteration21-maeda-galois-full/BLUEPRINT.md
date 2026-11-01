# Blueprint — Maeda in FULL for dims 6–10: Galois group Sₙ from Frobenius certificates

**Status: blueprint.  Nothing in `MathProof/` is touched until stage gates pass.**
Base: branch `dev/iteration20-maeda-dim6-10` after Iteration 20 S6 (Maeda
irreducibility verified for all 54 level-one weights with `2 ≤ dim S_k ≤ 10`).

## 0. Objective

For each of the 30 weights `72 ≤ k ≤ 134` with `6 ≤ dim S_k ≤ 10`:

```
theorem maeda_galois_full_kKK :
    Function.Bijective (Polynomial.Gal.galActionHom (P_k.map (Int.castRingHom ℚ)) ℂ)
```

i.e. the Galois group of the characteristic polynomial of `T₂` on `S_k` acts
on the roots as the FULL symmetric group `S_{dim}` — completing "Maeda's
conjecture in full" for `2 ≤ dim ≤ 10` (dims 2–5 already have it:
`MaedaGalois{,4,5}.lean`).

## 1. Reuse map (why this blueprint is cheap NOW)

| existing asset | where | role here |
|---|---|---|
| `charpoly_T2` + `maeda : Irreducible …` | `MaedaDim{6..10}Weights.lean` (each weight namespace, e.g. `MaedaWeight84.maeda`) | irreducibility input to transitivity and to the cycle-type argument |
| `P` (literal ℤ[X] charpoly) + `fr` (mod-ℓ coefficient list) + `hmap` | same files | the polynomial whose Galois group we study; `fr` already reduces it mod the certificate prime |
| `RabinCert.zpgcd/zpxw` reflected arithmetic | `RabinCert.lean` | squarefreeness / gcd certificates mod ℓ for the Frobenius factorizations |
| `MaedaGalois.eq_top_of_sup_alternating_of_odd`, `eq_top_of_transitive_of_jordan_of_odd`, `FrobHasCycleType` | `MaedaPermCriterion.lean` (stage 1–2, proved) | the group-theoretic finish and the Dedekind hypothesis interface |
| `JordanFor n` hypothesis interface + the S₃≀S₂ caveat note | `MaedaPermCriterion.lean` | stage-4 corrected Jordan (p > n/2) discharges it |
| census Frobenius primes per weight: `disc_nonres`, `transposition`, `jordan_p_cycle`, `n_minus_1_cycle` | `research/iteration20/data/maeda_dim6_10.json` field `frobenius` | the certificate primes are ALREADY computed (e.g. k=72: 11/23/23/73; k=120: 29/23/23/127) — but their SEMANTICS must be re-validated against actual factorizations before use (see §5 risk R1) |
| `HornerCert` axiom-free residue certificates | `HornerCert.lean` | propext-clean non-square / no-root statements mod ℓ |
| `eval_det` (Mathlib NormDet) | Mathlib | resultant/discriminant determinants mod ℓ |

## 2. Module layout (all light, none an ancestor of `MaedaGalois5Defs`)

| module | content |
|---|---|
| `MathProof/ModularForms/FrobeniusCycleType.lean` (new, ~250 lines) | **the new math** (§3): Dedekind's theorem in the form we need + `frob_cycleType_of_factorization` |
| `MathProof/ModularForms/JordanPrimitive.lean` (new, ~150 lines) | corrected Jordan: transitive + p-cycle with `n/2 < p ≤ n − 3` ⟹ `Aₙ ≤ G` (primitive via the p-cycle; then `Mathlib.GroupTheory.GroupAction.Jordan`), discharging `JordanFor` for our n |
| `MathProof/ModularForms/MaedaGaloisFullDefs.lean` + generated `MaedaGaloisDim{6..10}Weights.lean` | per-weight factorization + non-square certificates and the assembly (generator: extend `tools/gen_maedan.py` or a sibling `tools/gen_galoisfull.py`) |

Register light modules per AGENTS.md (`MathProof.lean`, `defaultTargets`, CI).

## 3. The new mathematical lemma: Dedekind → cycle type, over ℚ

```
theorem frob_cycleType_of_factorization {f : ℤ[X]} (hf : f.Monic)
    {n : ℕ} (hdeg : f.natDegree = n) (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    {ℓ : ℕ} [Fact ℓ.Prime]
    (hsq : Squarefree (f.map (Int.castRingHom (ZMod ℓ))))     -- cert: zpgcd with derivative = 1
    (hfact : (f.map (Int.castRingHom (ZMod ℓ))).factors.degrees = ds)  -- reflected certificate
    : FrobHasCycleType (f.map (Int.castRingHom ℚ)) ds
```

Mathematical route (degree-level, all standard):
Frobenius `x ↦ x^ℓ` on the roots of `f̄` in `F̄_ℓ` has cycles exactly the
irreducible factors (orbits of the Frobenius on the roots); the Galois group
of `f` over ℚ injects into `S_n` (irreducible ⟹ transitive) and CONTAINS an
element with the same cycle type (Dedekind: lift the Frobenius conjugacy
class via a prime of the splitting field over ℓ; unramified by squarefreeness
of the discriminant mod ℓ).  In Lean the practical shape is:

* `Polynomial.Gal.galActionHom` + `Polynomial.Gal.cycleType_conj` (or the
  project's `MaedaPermCriterion` reuse) to speak of cycle types;
* Mathlib's `Polynomial.Gal` + `Ideal`/`integral closure` content for the
  Dedekind step — grep `.lake/packages/mathlib` FIRST
  (`FieldTheory/Galois.lean`, `RingTheory/Polynomial.lean`,
  `FieldTheory/Finite/GaloisField.lean`,
  `Mathlib/GroupTheory/GroupAction/Jordan.lean` already has the swap +
  3-cycle Jordan cases).  If the full Dedekind theorem is missing, the
  fallback is the weaker-but-sufficient per-ℓ statement proven through
  `AdjoinRoot`/`SplittingField` reduction to `ZMod ℓ` factor degrees via
  `Polynomial.Gal.ofEquiv`-style transport — validated as a Lean sketch
  BEFORE committing to 30 weights (stage gate G2).

## 4. Assembly per weight (mostly certificates)

1. **Transitivity**: `Polynomial.Gal.galAction_isPretransitive` (Mathlib,
   irreducible f) + transport `Fin n` ↔ `rootSet` (pattern already used in
   `MaedaGalois{,4,5}`; `MaedaPermCriterion` docstring names it).
2. **Odd element**: `disc f ≢ □ (mod ℓ_{disc_nonres})`.  disc = `res(f, f′)`
   computed by `eval_det` on the Sylvester matrix mod ℓ (entries ≤ ℓ; n = 10
   Sylvester is 19×19 — cheap), then a `HornerCert`-style no-square
   certificate.  disc ≠ 0 by squarefreeness; non-square at one prime ⟹
   non-square in ℚ ⟹ `Gal ↄ A_n` (sign homomorphism argument; dims 3–5 files
   have the 2-dim shadow of this — generalize the `Equiv.Perm.sign` surjection
   argument).
3. **p-cycle element**: factor `f̄ mod ℓ_{jordan}` into degrees via reflected
   division/GCD (`RabinCert.zpgcd` machinery, fuelled); squarefreeness from
   `gcd(f̄, f̄′) = 1`; apply §3.  Check the census p against `n/2 < p ≤ n − 3`
   (k=120, n=10 lists `jordan_p_cycle: 23` — p=23 > n is impossible as a
   cycle; the field must encode the PRIME ℓ at which some p-cycle appears:
   recompute the actual degree partitions before trusting it).
   Where the corrected Jordan bound fails, the census `n_minus_1_cycle`
   route applies: an (n−1)-cycle + transposition + transitivity ⟹ Sₙ
   (elementary conjugation argument — include as a lemma in
   `JordanPrimitive.lean` if the p > n/2 case doesn't cover all weights).
4. **Finish**: `eq_top_of_transitive_of_jordan_of_odd` with `JordanFor`
   discharged by `JordanPrimitive`, transported from `Equiv.Perm (Fin n)` to
   `Bijective (galActionHom …)` exactly as in dims 3–5.

## 5. Risks and fallbacks

* **R1 census semantics**: `frobenius` fields were computed by the Iteration
  20 probe but never cross-checked against real factorizations.  Stage G1 =
  a Python script recomputing degree partitions of each charpoly mod each
  census ℓ (with squarefreeness), asserting the needed cycle types exist;
  regenerate the data if wrong.  Never trust, always re-derive.
* **R2 Dedekind in Mathlib**: if missing, the blueprint needs a real proof
  (integral closure of ℤ in the splitting field, reduction mod ℓ).  Budget
  2–3 rounds; if it exceeds that, DESCOPE to dims where `n_minus_1_cycle` +
  transposition suffice with a weaker Frobenius lemma (still S_n, possibly
  via Mathlib's existing `Polynomial.Gal` resolvent-free routes) and report.
* **R3 kernel cost**: factorization certificates mod ℓ are Euclidean-algorithm
  transcripts (like `zpgcd`, ~10³ ops) — far cheaper than the Rabin decides
  already shipped.  Not a risk; do NOT raise any option.
* **R4 heavy chain**: `FrobeniusCycleType`/`JordanPrimitive` must import
  Mathlib + `MaedaPermCriterion` only — NEVER become ancestors of
  `MaedaGalois5Defs` (check with `lake env lean` import graph before commit).

## 6. Stage gates

* G0: local Lean sketch of §3 on a cubic (weight 36 charpoly, where S₃ is
  known) — the Frobenius lemma compiles before any scale-up.
* G1: Python re-derivation of all factorization/non-square data (R1) — data
  file + asserts, byte-identical regeneration rule like `gen_maedan.py`.
* G2: one weight end-to-end (k=72, dim 6): `maeda_galois_full_72` green on
  Modal (`tools/modal_run.sh --file …`, linters on, zero warnings).
* G3: generator emits all 30; Modal per file; `AxCheckDecide` propext-clean;
  `tauceti_audit.sh` clean.
* G4: registration (root/lakefile/CI), research-log entry, README/docs
  ("Maeda in full, weights 24–134").

Work log: append to `research/research-log.md`; keep the generator the single
source (byte-identical `--check`); every Modal run via `tools/modal_run.sh`
(never two heavy stages concurrently).
