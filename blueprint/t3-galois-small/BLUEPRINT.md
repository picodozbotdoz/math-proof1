# BLUEPRINT 3 — T3GaloisSmall: `Gal = Sₙ` for the T₃ charpolys, the 24 small weights

Iteration 22, orchestrator's-choice slot (§4b: maximal reuse of just-landed
machinery — the T1 certificates pipeline — at minimal CI cost; completes
"Maeda in full for T₃" over ALL 54 weights).  Authored 2026-11-02 from
`research/iteration22/probe3-t3-small-galois/FINDINGS.md` — read it first
(verified export lists, per-n routes, the complete cert-scan table, cost
model).  This blueprint DEPENDS on the T1 baseline (generator `--prime 3`
mode), which is already on the trunk.

## 0. Objective / non-objectives

**Objective.**
`Function.Bijective (Gal.galActionHom (P.map (Int.castRingHom ℚ)) ℂ)` for the
T₃ charpoly `P` of every weight `k ≤ 74` with `2 ≤ dim S_k ≤ 5` (24 weights:
dims 2/3/4/5 × 6 each).  Routes (FINDINGS §2): dims 3–5 (18 weights) via the
UNCHANGED `MaedaGaloisFull.bijective_of_frobenius` (nm1 + transp certs); dim 2
(6 weights) via a NEW ~20-line `bijective_of_quadratic` (irreducible over ℚ ⇒
transitive Gal on 2 roots ⇒ galActionHom bijective; no Mathlib lemma exists —
checked at the pin).

**Non-objectives.**  T₂ dim-2 Galois statements (collateral for another
iteration); dims ≥ 11; Mathlib bump; touching the heavy `MaedaGalois5` chain
or any pre-existing module except appending the root import;
`MaedaT3SmallWeights` registration changes; umbrella weight-indexed theorem.

## 1. Reuse map (two columns)

**Mathlib-at-pin**: `Polynomial.Gal.galAction_isPretransitive`,
`card_rootSet_eq_natDegree`, separability — all already exercised by
`MaedaGaloisFull.bijective_of_frobenius`; for n = 2 the same ingredients with
`S₂`'s structure (FINDINGS §2 lists the exact lemmas verified at the pin).

**TauCeti**: rich GaloisGroups theory but no Hecke-charpoly content, no
quadratic-bijectivity lemma (FINDINGS §5) — nothing to port.

**Own library (the point of this blueprint)**:
`MaedaGaloisFull.{bijective_of_frobenius, cycleType_of_cert,
irreducible_of_rabin_bezout}` unchanged; `galoisfull_certs.py`/`gen_galoisfull.py`
(the `--prime 3` modes from T1; byte-identity discipline); `MaedaT3SmallWeights`
exports (`P`, `P_monic`, `P_natDegree`, `maeda` per weight — FINDINGS §1 lists
all 24 namespace lines); cert data from the probe's anchored scan
(`/home/doz/tmp/math-proof1-temp/probe3/scan_small.json` — re-derive at S2,
never trust; all certs at ℓ ≤ 89).

## 2. Module layout

* NEW light `MathProof/ModularForms/MaedaGaloisQuad.lean` (~40 lines with
  header): `bijective_of_quadratic {q : ℤ[X]}` (monic, natDegree = 2,
  `Irreducible (ratOf q)` ⇒ `Bijective (Gal.galActionHom (ratOf q) ℂ)`).
  Full trio registration (it is tiny).
* `tools/galoisfull_certs.py --small` (+ `--prime 3 --small` interplay per
  FINDINGS §4): scans the 24 small weights from `maeda_t3_small.json`,
  RE-ANCHORS each charpoly to the kernel-verified `P` literal of
  `MaedaT3SmallWeights.lean` (same parser as `g1_anchor.py`), emits
  `research/iteration22/data/t3_galoisfull_small_certs.json` (dims 3–5 pairs;
  dim 2: an ℓ with irreducible quadratic reduction — FINDINGS §3 has them ≤ 41).
* `tools/gen_galoisfull.py --prime 3 --small` → generated
  `MathProof/ModularForms/MaedaT3GaloisSmallWeights.lean` (~2.4–2.8 k lines,
  root-ONLY registration — it imports the deliberately non-CI
  `MaedaT3SmallWeights`; the lakefile note documents this policy) +
  `MaedaT3GaloisSmallAxCheck.lean` (opt-in).

## 3. Verification plan

Per gate: Modal `--file` green (0/0); generator `--check` byte-identity for
EVERY untouched mode (prime-2, prime-3 dims, T₂ axcheck) before/after each
generator edit; `tauceti_audit.sh` on both new light modules; combined
`AxCheckDecide` after root registration (expect +≈90 certs, 0 > propext);
opt-in AxCheck shows the 24 theorems on exactly `propext, Classical.choice,
Quot.sound`.  Expect ≤ ~5.5 GiB peaks (no 16 GiB investigation owed).

## 4. Stage gates (one green-commit session each)

* **Q1 infra**: `MaedaGaloisQuad.lean` green + audit + trio registration.
* **S2 certs**: `--small` scan emits the 24-pair JSON, anchored, reproducing
  the probe's table (deterministic given scan order; any deviation = STOP and
  investigate — evidence hierarchy).
* **S3 generate + build**: generated file green on Modal; root-only
  registration; AxCheckDecide green.
* **S4 bookkeeping**: README (extend the T₃ Galois twin paragraph to all 54
  weights), docs card sentence, AGENTS.md layout entry with measured costs,
  research-log entry.

## 5. Risks / fallbacks (from FINDINGS §6, binding)

* D1: `bijective_of_quadratic` stalls ⇒ ship dims 3–5 (18 weights), n = 2
  later (one-flag retreat in the generator).
* D2: n = 3 `{3−1}` vs `{2}` defeq wrinkle ⇒ the `bijective_of_frobenius3`
  wrapper (one cert used twice; ℓ = 29…47 singles suffice per the scan).
* D3: single 24-weight file elaborates slowly (not expected) ⇒ per-dim split
  (generator scaffolding already supports `--only`/`--weight`).
* R3: cert-ℓ colliding with the irreducibility file's Rabin ℓ — independent
  blocks, no interference (checked in the probe).

## 6. Provenance (cold-executable)

This file; `research/iteration22/probe3-t3-small-galois/FINDINGS.md`;
`MathProof/ModularForms/MaedaGaloisFull.lean`;
`research/iteration22-t3-galois/WORKLOG.md` (the T1 discipline being reused —
read its G2 generator-gate entry);
`tools/gen_galoisfull.py` + `tools/galoisfull_certs.py` (`--prime 3` modes);
one landed generated file (`MaedaT3GaloisDim6Weights.lean`) as the output
template; `external-doc/CODING_STANDARDS.md`; AGENTS.md.  Base commit in
WAVE-TRACKING.md.

## Lessons learnt

The T1 record applies verbatim (byte-identity gates, anchored scans,
Bézout-not-zpgcd, chunk exponents ≤ 256, commit green, WORKLOG, inbox).
One new one from the probe: **`decide +kernel` per declaration ~200 s budget**
— the small dims are far below it; nothing to watch here beyond the norm.
