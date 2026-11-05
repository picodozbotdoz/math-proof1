# Iteration 25 review — the nested-certificate retrofit

Trunk `dev/iteration25-nested-certs` (from the iteration-24 trunk 825e5a6).
Operator decision 2026-11-05 ("Retrofit them", answering
iteration24-review §7.1): make every nested `decide` certificate in the
light library `propext`-only.  One wave, three workers, one chain rebuild.

## 1. What was delivered

| blueprint | branch tip | result |
|---|---|---|
| maeda-small | 9077b9d | `MaedaSmallWeights`: 120 per-cell `seqP` decides → 28 `seqPLc` list decides (one per basis form, `MaedaCertC` route, as dims 4–5 already did); nested 120 → 0 |
| scaled-certs | bbc682b | new `ScaledCert` (Mathlib-only: `powL`, `cellL`, `scaledCheck`, bridge `scaled_of_check`); `HeckeIndex{Small,}Weights.scaled` + `HeckeRational{Small,}Weights.scaled_id`: one Bool `decide +kernel` per weight over pow-free integer tables; nested 4608 → 0 |
| zmod-casts | cbabdb0 | new `IntCastCert.intCast_eq_of_emod` (decide the residue over ℤ, cast by lemma); `hmap` in the 11 Maeda dims-6–10 / T₃ files via `gen_maedan.py` (all modes); `LehmerSieve691` private certificates over bounded `Nat` / structural `geom211`; nested 568 → 0 |

Every exported statement is unchanged (checked against the base per file:
statement text identical; only proofs and new helper declarations).

Heavy re-verification: the `MaedaGalois5` chain + `MaedaGalois5AxCheck`
rebuilt in one container after the `MaedaSmallWeights` change — green,
1580 s, peak 34.75 GiB (IdE6 33.46, the budgeted chain cost), 30 `#print
axioms` all on ≤ the standard three, no `sorryAx`.

## 2. What worked / what was forced

* The iteration-24 recipe generalised to all four shapes (tables bridged by
  `rfl`, one `List` Bool decide, one generic bridge) with no statement
  changes and *cheaper* builds (`HeckeRationalWeights` 8.4 → 7.99 GiB).
* A single-container chain rebuild (target = `MaedaGalois5AxCheck`) beat
  `stage_chain.sh` here: the three workers' runs keep replacing the one
  rolling cache tarball, so staged resumption would have been unreliable.
* Two more parallel-rebuild memory alerts (22.2 / 25.6 GiB tree, ≤ 8 GiB per
  module) — closed as inherent.  Found: `lean_check.py` reads
  `LEAN_CHECK_MEMORY_MIB` in-container as the default 8192, so a *failing*
  heavy run is misreported as an OOM (`memory-alerts.md`).
* A worker died at the session limit mid-sequence; its background build
  script kept running and finished, and the branch was closed by the
  orchestrator from the run logs (WORKLOG + commits were sufficient).

## 3. Metrics

| item | value |
|---|---|
| nested certificates beyond `propext` | 5296 → **0** (combined trunk: nested 2412 audited / 0; top-level 1560 / 0) |
| combined light root | 8531 jobs green, 0 err / 0 warn, 324 s; tree peak 95.7 GiB = 19 parallel `lean` processes, max module 8.03 GiB (alert CLOSED) |
| new light modules | 2 (`ScaledCert`, `IntCastCert`) |
| generators changed | `gen_maeda.py` (regeneration byte-identical), `gen_hecke_index.py`, `gen_hecke_rat.py`, `gen_maedan.py` (all modes) — `--check` byte-identical, as are the untouched `gen_hecke_cyclic/ring_gens/field` |
| heavy re-verification | `MaedaGalois5` chain + AxCheck 1580 s / 34.75 GiB green; `LehmerGrand`/`LehmerPrimeGrand` skipped by operator decision (§4.1) |

## 4. Gaps left open

1. `LehmerGrand` / `LehmerPrimeGrand` (import `LehmerSieve691`) were **not
   rebuilt — operator decision 2026-11-05 ("skip … and record why")**.
   Why: (a) their heavy parents `LehmerPacked` (≈ 63 GiB) and `LehmerPow32`
   (≈ 144 GiB, ≈ 35 min) are not in the rolling build cache (checked: the
   cache tarball holds only `LehmerMod.olean` among the heavy Lehmer
   modules), so a re-check would rebuild both; (b) the `LehmerSieve691`
   change is proof-only: two `private` certificates re-proved over bounded
   `Nat` plus new private helpers, every public statement byte-identical,
   so the two importers — which see only statements — cannot elaborate
   differently.  Their last green builds stand; rebuild
   them the next time `LehmerPacked` is rebuilt for another reason.
2. Heavy modules' own in-file certificates are audited by their own
   `#print axioms` lines, not by the nested pass.
3. The `lean_check.py` in-container memory default (§2).

## 5. Recommendations

1. Make both `AxCheckDecide` passes part of every close-out (now in
   AGENTS.md) and fail CI-side review on any nested violation.
2. Fix the `lean_check.py` memory default (pass the request into the
   container explicitly).
3. Cap lake's parallelism in `lean_check.py` for cold full-root runs
   (19 concurrent processes observed; Modal memory is soft).
4. Return to the research frontier: iteration24-review §7.3 (ℤ[T₂,T₃]
   structure-constant probe).
