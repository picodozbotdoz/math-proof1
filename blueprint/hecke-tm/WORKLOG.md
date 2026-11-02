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



### 2026-11-03 (respawn session, ~01:00–02:30) — G2+G3 GREEN, full multiplicativity landed

**Salvage completed → full blueprint content.**  Runs 5–12 (all
`./mrun.sh --file MathProof/ModularForms/HeckeTM.lean`, peak ≤ 6.1 GiB,
17–140 s wall each):

- Run 5: GREEN after fix pass 2 (0 err), 2 warnings (unused section variable
  `[Module ℂ M]` in `sum_mul_p`/`sum_p_mul` — the gotcha that a red build
  under-reports style warnings is confirmed: these only surfaced on green).
- Run 6: the `omit [Module ℂ M] in` placed AFTER the doc comment → parse
  error; Run 7: omit BEFORE the doc comment → **GREEN 0 err / 0 warn**;
  commit 573bcfb; HeckeTMScratch.lean deleted (worthless, absorbed).
- Runs 8–12: the G2/G3 section (prime-step identity, commutation,
  multiplicativity, T₂-recurrence) — fix iterations down from 19 errors:
  - rintro/⟨⟩ patterns mirror the ∧-tree nesting exactly (no rcases
    flattening of extra components; term-mode ⟨⟩ DOES flatten).
  - `if_pos/if_neg/if_true/if_false` all deprecated at the pin →
    `ite_eq_left (hc : c)` / `ite_eq_right (hnc : ¬c)` / `ite_true` /
    `ite_false` (core Init/Core.lean:1172/1181).
  - `LinearMap.mul_apply` does not exist → `Module.End.mul_apply`.
  - `PowerSeries.coeff_add` does not exist → private `ps_coeff_add (by simp)`;
    `PowerSeries.coeff_smul (n φ a)` exists.
  - `show` is linter-rejected even for defeq goal-restatements → `change`
    everywhere (per CODING_STANDARDS/AGENTS.md).
  - `Finset.sum_eq_zero` cannot be `refine`d against a REVERSED goal
    (`0 = ∑ …`) — the unifier leaves the AddCommMonoid-TC stuck on a
    metavariable; use `(Finset.sum_eq_zero …).symm`.
  - `rw [tsumF]` (bare-constant equation unfolding) got the AddCommMonoid-TC
    stuck on the generalized implicit M in one goal → replace with explicit
    `change`-statements of the unfolded sum.
  - `heckeTP hp 0 = 0` needed `qExpansion 1 0 = 0` via `← qL_apply` +
    `map_zero` (no ready-made lemma).
  - `Nat.cast_ofNat` normalizes `((p : ℕ) : ℂ)`-vs-numeral mismatches in the
    T₂ corollaries.
- Run 12 (final): **0 err / 0 warn**; commit 6edcb02.

**Landed exports (all in `namespace HeckeTM`, light module, no decides):**
- `heckeTM` (recursive route at `m.minFac`), `heckeTM_zero/id/add_two/ge_two/
  ge_two'/apply_ge_two`;
- `heckeTM_coeff_tsumF`, `heckeTM_qExpansion_coeff` (the general-m formula),
  `heckeTM_one` (duality ingredient `a₁(T_m f) = a_m f`);
- `heckeTM_prime`, `heckeTM_qExpansion_coeff_prime`, `heckeTM_prime_pow_succ`;
- `heckeTM_mul_prime_form` / `heckeTM_mul_prime` (the prime-step operator
  identity `T_p ∘ T_m = T_{pm} + p^(k-1) • [p ∣ m] T_{m/p}`),
  `heckeTM_mul_prime_apply` (prime-prime swap);
- `heckeTM_commute_apply` / `heckeTM_comp_commute` / `heckeTM_commute`;
- **`heckeTM_mul_tsumF` / `heckeTM_mul`** — the FULL all-pairs
  multiplicativity `T_m ∘ T_n = ∑_{d ∣ gcd m n} d^(k-1) • T_{m n / d²}` (no
  descope needed: the strong induction on `n` closes through the abstract
  `tsumF_prime_step` applied at the operator module — no new Finset
  reindexing was required);
- `heckeTM_two_mul_even_form` / `heckeTM_two_mul_even` (the T₂ recurrence for
  even m — the b2 staircase input).

**Deviation notes (§4d):** (1) the blueprint's suggested separate `heckeTPow`
family was subsumed by `heckeTM` + `heckeTM_prime_pow_succ` (the general-m
definition covers prime powers; b2 consumes `T_{2^i}` through `heckeTM` +
the recurrence).  (2) The Module.End-form is DEFEQ to the ℂ-linear-map form
(`Module.End ℂ V = V →ₗ[ℂ] V`), so no separate `heckeTME` definition is
needed — the `Commute`-form `heckeTM_commute` is exported for the
Hecke-algebra upgrade's hypothesis shape.

**G4 in progress:** trio registration done (MathProof.lean import after
HeckeGeneratedByT2Weights; lakefile defaultTargets; CI list — same
position).  tauceti_audit.sh clean (0/0/0/0/0, 797 lines).  AxCheckDecide
run in flight (builds the registered light root + audits decide-certificates).
Inbox polled at G2/G3 close: EMPTY.

### 2026-11-03 (~01:50) — G4 COMPLETE: registration verified, audits clean

- **AxCheckDecide on Modal** (`--file MathProof/AxCheckDecide.lean`, 65 s /
  6.75 GiB): the registered light root `MathProof` built (8483 jobs — the
  new HeckeTM import verified as part of the root) and the audit reports
  **1312 decide certificates audited, 0 depend on more than propext**.
- **tauceti_audit.sh**: clean (0 set_option / 0 eval / 0 native_decide /
  0 sorry / 0 bad-imports; 797 lines).
- **Trio registration**: MathProof.lean (import after
  HeckeGeneratedByT2Weights), lakefile.toml defaultTargets, CI list — same
  relative position in all three.
- Inbox polled at G4 close: EMPTY (no STEER-hecke-tm-* / STEER-all-*).
- Commit: G4 registration + this WORKLOG.

**Research-log draft (for the orchestrator's trunk merge):**
Iteration 23 / b1 hecke-tm: the level-one Hecke operators `T_m` for ALL
`m ≥ 1` on `CuspForm 𝒮ℒ k`, defined by the recursive route (`T₁ = id`;
`T_m = T_p ∘ T_{m/p} − p^(k-1) • [p ∣ m] T_{m/p²}` at the least prime
factor), with the complete algebraic calculus: the general coefficient
formula `(T_m f)_n = ∑_{d ∣ gcd m n} d^(k-1) f_{mn/d²}`, the duality
ingredient `a₁(T_m f) = a_m f`, the prime-step identity, commutation with
every `T_p` (pointwise, ∘ₗ, and `Commute` forms), the FULL multiplicativity
`T_m ∘ T_n = ∑_{d ∣ gcd m n} d^(k-1) • T_{mn/d²}` (the induction closes
through the abstract coefficient-level prime-step lemma `tsumF_prime_step`
lifted to the operator module — no additional Finset reindexing needed), the
prime/prime-power specializations reducing to the landed
`heckeTP_qExpansion_coeff`, and the `T₂` two-term recurrence for even `m`.
Light module (797 lines, Mathlib-level imports, no kernel decides, no
`set_option`); registered in the root/defaultTargets/CI; AxCheckDecide-clean.
Downstream: b2 hecke-index (duality + I_k) and b3 hecke-field (dim-2
integrality) consume `heckeTM`, `heckeTM_qExpansion_coeff`, `heckeTM_one`,
`heckeTM_mul`, `heckeTM_two_mul_even(_form)`, `heckeTM_commute`.

**State at session end:** branch tip = G4 commit; gates G1–G4 all PASS;
blueprint objective COMPLETE (no descopes); Modal runs this session: 13
(12 × HeckeTM/AxCheckDecide + 0 wasted); no pushes; ready for the wave merge.
