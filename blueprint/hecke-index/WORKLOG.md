# Worklog — impl/iteration23/hecke-index

Base: de3e387 (trunk `dev/iteration23-hecke-ring`, blueprints commit).
Blueprint: `blueprint/hecke-index/BLUEPRINT.md` — a STARTING POINT, not a
contract: G1-audit it, deviate per the §4d deviation protocol when facts
disagree (evidence here; corrections to the trunk).

Append dated entries as you go (gates passed/failed, mrun.sh Modal runs with
time + peak RSS, decisions, deviations).  This file is the inter-session
resume point: make it possible to continue cold.

## Entries

### 2026-11-02 — G1 data audit CLOSED (Miller strategy (a) chosen)

* **Probe re-run**: `research/iteration23/probe2-hecke-index/probe_index.py`
  regenerates cleanly at the pin (3 m 12 s, all F1–F7 pass, 54/54).
* **G1 audit script**: `research/iteration23/hecke-index/g1_audit.py` (new,
  self-contained like iteration-22's `g1_audit.py`); writes
  `research/iteration23/hecke-index/index_data.json`.  3 m 12 s, 0 failures.
  Checks C1–C6 at all 54 weights, re-pinned DIRECTLY to Lean literals (no
  g1_data.json intermediary):
  - C1 fb re-pin: Lean `Atab` + `q{i}_{m}` lemmas == raw prodForm rows
    (q-lemma coverage to 3n) — fb IS the raw basis, 54/54.
  - C2 Lean `M` literals == re-derived fb-coordinate matrices of T₂/T₃:
    dims 6–10 from `MaedaDim{d}`/`MaedaT3Dim{d}Weights`; dims 2–5: M3 from
    `MaedaT3SmallWeights`, M2 from `HeckeRationalSmallWeights` (landed
    literal, kernel-pinned by its entryT2 lemmas).  54/54.
  - C3 Miller: normalization, `Tmat` integer upper-unitriangular, |det| = 1,
    conjugation bridge `Tmatᵀ·M2m = M2r·Tmatᵀ`.  54/54.
  - C4 `|det A| = |det C| = I_k ≠ 0`; C5 Cramer certificate
    `∑ w'_i·M2Lean^i = I_k·M3Lean` entrywise ON THE LEAN-PARSED literals;
    C6 committed (N, D) parsed from the landed `cert`/`scaled_id` literals
    (new plain/flat/Horner integer-expression parser): D ∣ I_k and
    `w' = (I_k/D)·N`.  54/54.
* **Sizing** (matches probe F7; worst dim 10): A ≤ 180d, I_k ≤ 462d,
  w' ≤ 494d, M2^i ≤ 248d → Horner base-10^74 chunks as planned.
* **Data findings**:
  1. The landed HeckeRational `D` is ALREADY reduced at all 54 weights
     (`norm_certificate` divides out the gcd) — `Dred == D` everywhere;
     reuse it as "the" D, no re-reduction layer needed.
  2. `Ik/D == 1` exactly at dims 2–4 (44 weights... precisely: every weight
     with n ≤ 4), proper divisor from dim 5 — the article's prediction,
     re-confirmed on Lean-pinned data.
  3. Bézout witnesses for `gcd(D, N) = 1` (needed by `den_dvd_index`):
     naive sequential extgcd reaches 2677d at dim 10; a tree-ordered
     combination (N's first, then D once) should stay ≈ 400d — emission
     strategy to be measured at G4; descope provision: per-weight `D ∣ I_k`
     only for dims 2–5 (witness ≤ 89d) if the dim-10 witness fights.
* **Miller-strategy DECISION (a)** (blueprint recommendation, confirmed by
  C3/C5): build the Miller basis in Lean as the unit-triangular reduction of
  `fb` — well-founded recursion `miller f A n j = f j − ∑_{s} A j (n−1−s) •
  miller (n−1−s)` (analytic module, no kernel decides on it, so WF is
  acceptable; CODING_STANDARDS' structural rule targets decided content);
  the per-weight certificates stay in fb coordinates (basis-independent
  operator identities — C5 verifies them on the landed fb literals), so no
  fb↔Miller bridge is needed inside any certificate.
* Commit: `research/iteration23/hecke-index/{g1_audit.py,index_data.json}`.
