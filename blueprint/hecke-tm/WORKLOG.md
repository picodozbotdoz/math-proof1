# Worklog — impl/iteration23/hecke-tm

Base: de3e387 (trunk `dev/iteration23-hecke-ring`, blueprints commit).
Blueprint: `blueprint/hecke-tm/BLUEPRINT.md` — a STARTING POINT, not a
contract: G1-audit it, deviate per the §4d deviation protocol when facts
disagree (evidence here; corrections to the trunk).

Append dated entries as you go (gates passed/failed, mrun.sh Modal runs with
time + peak RSS, decisions, deviations).  This file is the inter-session
resume point: make it possible to continue cold.

## Entries

### 2026-11-03 (respawn of worker hecke-tm, ~00:30) — inherited-state compile

**Context.** Predecessor's session died silently 2026-11-02 ~21:07, no
completion notification, NO WORKLOG entries (protocol miss — this file was
empty).  Recovering per RESEARCH-WORKFLOW §4d.

**Inherited state (verified on disk / in run logs before this entry):**
- Branch `impl/iteration23/hecke-tm` at seed commit 4154d33 (WORKLOG +
  mrun.sh only); predecessor never committed anything.
- Untracked WIP: `MathProof/ModularForms/HeckeTM.lean` (26.8 KB, mtime
  21:05) + `MathProof/ModularForms/HeckeTMScratch.lean` (1.3 KB, mtime
  20:10, tactic-name probe file, header says "delete before commit").
- Predecessor's Modal runs (all `--file MathProof/ModularForms/HeckeTM.lean`
  or the scratch file), logs in
  `/home/doz/tmp/math-proof1-temp/agent-work/hecke-tm/runs/`:
  1. 20:32 `run-...-193211` — ? (not re-read in detail)
  2. 20:34 `run-...-203425` — HeckeTMScratch failed (unknown `𝒮ℒ`,
     `Nat.Prime.dvd_pow_iff` absent at pin).
  3. 20:37 `run-...-203716` — HeckeTM failed: ~20 errors clustered in the
     divisor-reindexing lemmas (`sum_mul_p`/`sum_p_mul`: mem_divisors
     tuple-shape mismatches, `rcases` on `p ∣ d → False`), plus cascade.
  4. 21:05 `run-...-210523` (LAST, build FAILED 28 s): same cluster
     persisted (lines 121–202: invalid ⟨⟩ against `m = 0 → False`, type
     mismatches, indentation error at 195 `unexpected token '·'`),
     `(deterministic) timeout at whnf` 200000 heartbeats at line 310,
     `omega` failure in the `decreasing_by` of `heckeTM` (line 333) which
     made the equation compiler insert `sorryAx` (cascading
     "declaration uses sorry" on every downstream lemma), and further
     rewrites failing in the coefficient-formula section (426+).
- Blueprint G1 (probe re-run + lemma-shape pinning) was never evidenced.

**Salvage verdict (from reading the WIP + logs, pre-recompile):** SALVAGE.
The WIP follows the blueprint's architecture exactly (recursive route at
`m.minFac`; pure-arithmetic `tsumF` transform; strong induction on `m` with
`tsumF_prime_step` as the check-B reindexing; prime/prime-power
specializations; `heckeTM_one`).  All observed failures are local
tactic-level issues (tuple shapes, one indentation, lemma-name drift, a
missing `maxHeartbeats`-safe split at the `heckeTM_coeff_tsumF`
`simp only [hmid, if_true, ...]` line, and the `decreasing_by` omega), not
structural divergence.  Recompiling as-is next to get the precise
error list at the current file state, then fixing in place.
- Scratch file: judged WORTHLESS (name-probe round 2; one finding —
  `Nat.Prime.dvd_pow_iff` does not exist at the pin — already absorbed by
  not using it; minFac-of-prime lemma duplicated in the WIP).  Delete after
  first green run (kept until then as name reference).
- Inbox polled 00:30: EMPTY (no STEER-hecke-tm-* / STEER-all-*).

**G1 — audit + pinning (2026-11-03, ~00:40–01:00): PASS.**
- **Probe re-run**: `python3 -I research/iteration23/probe1-hecke-tm/probe_tm.py`
  from the MAIN tree (read-only) — ALL CHECKS PASSED (A prime specialization,
  B multiplicativity grid, C Δ/τ anchor, D duality matrix identity, E
  unitriangularity).  ~3 min wall.
- **Landed lemma shapes pinned (read from the files, not the blueprint):**
  - `HeckeLevelOne.heckeTP_qExpansion_coeff (hp : p.Prime) {k : ℤ} (f) (m) :
    (qExpansion 1 (heckeTP hp f)).coeff m = (qExpansion 1 f).coeff (p * m) +
    (p : ℂ) ^ (k - 1) * (if p ∣ m then (qExpansion 1 f).coeff (m / p) else 0)`.
  - `HeckeLevelOne.heckeTPₗ (k : ℤ) {p} (hp : p.Prime) :
    CuspForm 𝒮ℒ k →ₗ[ℂ] CuspForm 𝒮ℒ k` (toFun := heckeTP hp).
  - `MaedaLevelOne.qL k : CuspForm 𝒮ℒ k →+ PowerSeries ℂ`;
    `qL_apply : qL k f = qExpansion 1 f := rfl`;
    `qe_smul : qExpansion 1 ⇑(c • f) = c • qExpansion 1 f`.
  - `HeckeCommute.qExpansion_coeff_ext {f g} (h : ∀ m, (qExpansion 1 f).coeff m
    = (qExpansion 1 g).coeff m) : f = g` — the operator-equality workhorse.
  - `HeckeCommute.heckeTP_commute (hp) (hq) {k} (f) :
    heckeTP hp (heckeTP hq f) = heckeTP hq (heckeTP hp f)`;
    `heckeTPₗ_commute (hp) (hq) (k) : Commute (heckeTPₗ k hp) (heckeTPₗ k hq)`
    (k explicit here).
- **WIP salvage (run 2 = as-is baseline, run 3 = after fix pass 1):**
  - Run 2 (00:27, `run-20261103-002657`, 65 s / 4.81 GiB peak): 34 errors —
    reproduced the predecessor's 21:05 failure exactly (disk file = last
    compiled version, verified via the mrun mirror git).
  - Root causes diagnosed and fixed in one pass: rintro/anonymous-constructor
    patterns must mirror the ∧-tree nesting EXACTLY (no rcases flattening);
    `Nat.dvd_of_dvd_mul_left/right` do not exist standalone — use
    `Nat.Coprime.dvd_of_dvd_mul_left/right (H : Coprime k m) (H2 : k ∣ m * n)`
    (core Nat/Coprime.lean:38/42) or the iff forms `Nat.Coprime.dvd_mul_left`;
    `dvd_mul_of_dvd_right/left` are ROOT-namespace (no `Nat.` prefix);
    `Nat.eq_zero_of_mul_eq_zero` does NOT exist at the pin — use core
    `Nat.mul_eq_zero : n * m = 0 ↔ n = 0 ∨ m = 0`; `if_pos/if_neg` deprecated
    → `ite_eq_left (hc : c)` / `ite_eq_right (hnc : ¬c)` (core Init/Core.lean);
    `if_true/if_false` → `ite_true/ite_false`; `LinearMap.smul_zero` does not
    exist — plain `smul_zero`; `Nat.minFac_prime (by omega)` fails on the
    metavariable n — always pass `show … ≠ 1 by omega` or a concrete Prime
    proof; rw through `minFac_eq` breaks on the dependent Prime-proof
    implicit of `heckeTPₗ` — use `simp only` (per Lean's own hint);
    `Nat.mul_div_cancel_left (m) (H : 0 < n) : n * m / n = m` needs the
    divisor as the FIRST factor (use mul_comm first otherwise);
    `Finset.filter_eq_empty_iff : s.filter p = ∅ ↔ ∀ ⦃x⦄, x ∈ s → ¬ p x`
    (strict implicit; lambda binds the ¬-argument as a third binder).
  - Run 3 (00:52, `run-20261103-005207`): 19 errors — all local (pattern
    nesting 2×, one wrong lemma name, eq_empty binder shape, second
    `Finset.sum_empty` over-rewrite, rfl-after-closed-rw, heckeTM_prime
    motive).  `tsumF_prime_step` machinery (hfree/hs1/hs2) now elaborates.
  - Run 4 (01:0x, in flight) after fix pass 2.
- Scratch file verdict unchanged: delete after first green run.


