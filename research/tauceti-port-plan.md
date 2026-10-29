# TauCeti port plan — living checklist

Goal: upstream the *light, general* parts of math-proof1 into
[TauCeti](https://github.com/TauCetiProject/TauCeti) (Lean `v4.36.0-rc1`, Mathlib `master`),
one topic per PR, no stacking. Everything else stays here.

## 0. How to resume (read this first after any crash / restart)

This file is the single source of truth.  State lives in three places, all committed:

1. The **checkboxes below** (`[ ]` todo, `[~]` in progress, `[x]` done, `[-]` dropped/stays-local).
2. The **Progress journal** at the bottom — append one line per finished action (date, item, commit/PR).
3. **Git**: one branch per item, `tauceti/<item-id>` (forked from TauCeti `main`, in a clone at
   `~/zcode-workdir/tauceti`, *not* in this repo).  A half-done item = existing branch with commits.

Resume protocol:
```bash
git -C <this repo> log --oneline -5 -- research/tauceti-port-plan.md   # last recorded state
grep -n '^\- \[~\]' research/tauceti-port-plan.md                      # what was in flight
git -C ~/zcode-workdir/tauceti branch --list 'tauceti/*'               # unfinished branches
tools/tauceti_audit.sh                                                 # static compliance table
```
Rules for resilience:
- Mark `[~]` and commit this file **before** starting an item; mark `[x]` + journal line **after** it lands.
- Commit the plan after every state change (`git commit -m "tauceti plan: <id> <state>"`).
- Each item is idempotent: re-running its steps on an existing branch must be safe; never force-push, never
  `git stash` (use WIP commits).
- Builds go through `tools/modal_run.sh` only (see AGENTS.md); log long runs to `$TMPDIR/mathproof-runs/`.
  A killed build is simply re-run (the lake cache makes it resumable).
- Never open PRs/issues in TauCetiRoadmap from an agent — that is human-only (§Phase 1).
- Stop and ask the human at every box marked **HUMAN**.

## 1. Compliance gate (applies to every item)

Per TauCeti `AGENTS.md`.  An item is "ready" only if all hold:
- [ ] no `set_option` (found here: 69× `maxHeartbeats`, 12× `maxRecDepth`, `exponentiation.threshold`, a `longLine`)
- [ ] no `#eval`, `native_decide`, `sorry`, `unsafe`/`meta`; no `import Lean.*`/`Lake`/`Std` direct imports
- [ ] axioms ⊆ {propext, Classical.choice, Quot.sound} (`#print axioms`, run on Modal)
- [ ] Mathlib linters clean (full set, changed modules); builds on current Mathlib `master` + TauCeti toolchain
- [ ] namespace/names follow Mathlib (`Ramanujan.*` → Mathlib-style; declarations de-duplicated against Mathlib)
- [ ] no aliases/shims; one topic; PR body has `Roadmap: <Area>` or `Roadmap: none`
- [ ] `tauceti-review` local run: no `block`, no unresolved `changes requested`

`tools/tauceti_audit.sh` reports the mechanical subset (set_option / #eval / native_decide / sorry / bad imports).

## 2. Phases

### Phase 1 — Go / no-go (no code)
- [x] P1.1 Read TauCeti README "Coordinating work: intentions and claims" + TauCetiReview rubrics; note deltas here
- [ ] P1.2 **HUMAN** Zulip "Getting started: roadmaps": ask whether level-one modular forms / Hecke / Δ-bridge belongs and under which roadmap
- [ ] P1.3 **HUMAN** Roadmap hook: existing item, or human-authored roadmap PR in TauCetiRoadmap (milestones: Hecke `T_p`, Mordell, eigenforms, Δ bridge)
- [ ] P1.4 **HUMAN** `[Intention]` issue in leanprover-community/project-intentions (90-day expiry; renew before lapse)
- [x] P1.5 Clone TauCeti to `~/zcode-workdir/tauceti`; install `tauceti-review` (TauCetiWorker via `uv`); confirm toolchain = ours
- [x] P1.6 Mathlib overlap survey: for each candidate (below) diff against Mathlib `master` `NumberTheory/ModularForms` (Δ, Eisenstein, Hecke, q-expansion); record "already upstream / partial / new" in the table
- **Decision gate:** if P1.2/P1.3 are negative → only `Roadmap: none` improvements are possible; stop Phases 3+ and mark everything `[-]`.

### Phase 2 — Local pre-port hygiene (in *this* repo, benefits both)
- [ ] P2.1 Run `tools/tauceti_audit.sh`, paste table into §4 (baseline)
- [ ] P2.2 For each Tier A/B file: remove removable `set_option` (default heartbeats must suffice; split lemmas, replace `decide +kernel` where needed)
- [ ] P2.3 Re-audit axioms on Modal (`tools/modal_run.sh --target MathProof.AxCheck`, `MathProof.AxCheckDecide`)
- [ ] P2.4 Beware: edits to import ancestors of `MaedaGalois5Defs` trigger the ≈33 min heavy-chain rebuild (AGENTS.md); batch them, or do port work in TauCeti only and keep this repo frozen

### Phase 3 — Triage and port, smallest first

Tiers: **A** light, general, likely accepted · **B** light but instance-heavy/specialised, port only if A lands and a roadmap item wants it · **C** heavy/certificate modules — need `maxHeartbeats`/GiB of RAM, **cannot** go in (stay local) · **D** infra/audit, stays local.
Order inside a tier: fewest lines / fewest dependencies first; a PR may only start once its prerequisites are merged to TauCeti `main`.
Status key: `[ ]` todo · `[~]` in progress · `[x]` merged · `[-]` stays local / dropped.  Each row: id · module · lines · blockers (from audit) · PR.

#### Tier A — port candidates (one PR each unless noted)
| st | id | module | lines | blockers / notes | PR |
|----|----|--------|-------|------------------|----|
| [ ] | A1 | `ModularForms/HornerCert` | 76 | 2 set_option; ℕ/ℤ Horner residue certificates — maybe too niche; check usefulness first | |
| [~] | A2 | `Tau/Basic` (algebraic τ, list arithmetic) | 460 | Mathlib/TauCeti have Δ and `qExpansion Δ`, but **no integer-valued τ / no product-expansion coefficients** → still new | | |
| [~] | A3 | `Tau/Bridge` (qExpansion Δ = τ) | 516 | 2 set_option; Mathlib has only `discriminant_qExpansion_coeff_one`; coefficient-level bridge is new. Check vs `LevelOne/DiscriminantEigenform` | |
| [~] | A4 | `ModularForms/Weight12` (691•E₁₂ identity, Sturm) | 231 | 1 set_option; Bernoulli evaluations. NOT in TauCeti/Mathlib (no 691, no E₁₂ identity); TauCeti has `Sturm bound` + `LevelOne/GradedRing` (Δ=(E₄³−E₆²)/1728) to reuse | |
| [~] | A5 | `ModularForms/Congruence691` | 299 | 1 set_option; needs A4 | |
| [-] | A6 | `ModularForms/HeckeLevelOne` (T_p from scratch) | 938 | **REDUNDANT**: TauCeti already has Hecke operators at all levels (`ModularForms/HeckeSlash/*`, `Eigenform`, `Newforms/*`). Only salvage = a level-one cross-check, not a PR | |
| [-] | A7 | `Tau/Mordell` (multiplicativity, prime-power recursion) | 239 | **REDUNDANT**: `LevelOne/DiscriminantEigenform.lean` already has coprime multiplicativity of Δ coeffs + prime-power recurrence + `T₂Δ` | |
| [-] | A8 | `ModularForms/EigenLevelOne` (weight-generic rank-one eigenforms) | 270 | **REDUNDANT** with `Eigenform`/`Newforms/Coefficient` (generic-level); drop unless it has a unique statement | |
| [ ] | A9 | `Tau/LehmerPrimeReduction` (τp≠0 ⇒ τ(p^a)≠0; reduction to primes) | 223 | re-base on `discriminantEigenform` in TauCeti (A7 dropped) | |
| [ ] | A10 | `Tau/LehmerUnbounded` | 79 | re-base on `discriminantEigenform`; needs A9 | |
| [ ] | A11 | `Tau/LehmerSieve691` (mod-691 sieve) | 205 | 4 set_option; needs A5 | |
| [ ] | A12 | `ModularForms/BernoulliHigh` (B₁₃…B₂₆) | 624 | check vs Mathlib Bernoulli evaluations; decide-on-WF warning in AGENTS.md | |
| [ ] | A13 | `Tau/CongruenceSmall` (mod 2, 3 gaps) | 214 | needs A2/A3 | |

#### Tier B — conditional (only if a roadmap item asks)
| st | id | module | lines | blockers / notes | PR |
|----|----|--------|-------|------------------|----|
| [ ] | B1 | `Tau/Lehmer` (τ≠0 for n≤128) | 88 | 2 set_option; tiny, nice Lehmer anchor | |
| [ ] | B2 | `ModularForms/LehmerWeight16` | 271 | congruence mod B_k numerator; needs A8 | |
| [ ] | B3 | `ModularForms/LehmerWeight18` | 283 | | |
| [ ] | B4 | `ModularForms/LehmerWeight20` | 301 | | |
| [ ] | B5 | `ModularForms/LehmerWeight22` | 321 | | |
| [ ] | B6 | `ModularForms/LehmerWeight26` | 350 | | |
| [ ] | B7 | `ModularForms/MaedaLevelOne` | 338 | `decide +kernel` for `seqP`; heartbeat-sensitive | |
| [ ] | B8 | `ModularForms/MaedaWeight24` | 298 | | |
| [ ] | B9 | `ModularForms/MaedaCertC` | 91 | | |
| [ ] | B10 | `ModularForms/MaedaSmallWeights` (generated) | 1316 | 131 set_option; regenerate with `tools/gen_maeda.py` minus options | |
| [ ] | B11 | `ModularForms/MaedaGalois` (S₃) | 308 | 6 set_option | |
| [ ] | B12 | `ModularForms/MaedaDim4` + `MaedaDim4Weights` + `MaedaGalois4` | 304+1878+677 | 36+12 set_option | |
| [ ] | B13 | `ModularForms/MaedaDim5` + `MaedaDim5Weights` | 431+2620 | 42 set_option | |
| [ ] | B14 | `ModularForms/Poly5` | 237 | 2 set_option; only useful with S₅ chain (Tier C) → likely `[-]` | |

#### Tier C — stay local (cannot meet no-`set_option` / resource rules)
Record the reason; revisit only if a cheaper certificate is found.
- [-] C1 `Tau/LehmerMod` (512, 5 set_option, `native_decide` grep hit — verify it is only a comment)
- [-] C2 `Tau/LehmerPacked` (65536; ≈63 GiB; 11 set_option)
- [-] C3 `Tau/PowChain`, `LehmerPow32`, `LehmerPrimePower`, `LehmerGrand`, `LehmerPrimeGrand` (143 GiB class)
- [-] C4 `MaedaGalois5Defs` · `MaedaGalois5IdBase` · `MaedaGalois5IdE4` · `MaedaGalois5IdE5` · `MaedaGalois5IdE6` · `MaedaGalois5Identities` · `MaedaGalois5` · `MaedaGalois5Weights` · `MaedaGalois5AxCheck` (≈33 min chain, ≤35 GiB, ≈58 k lines)
Open question for later: can any C item be rephrased so default heartbeats suffice (e.g. smaller bound, sharper certificate)? Track under P2.2.

#### Tier D — infra, stays local
- [-] `AxCheck`, `AxCheckDecide`, `MaedaGalois5AxCheck`, `Bench/`, `tools/`, `docs/`, `research/`, Modal scripts

### Phase 4 — Per-item procedure (copy for each row; do not skip steps)
1. Mark row `[~]`, commit plan.
2. In the TauCeti clone: `git fetch && git checkout -b tauceti/<id> origin/main`.
3. Copy module → `TauCeti/<Area>/<Name>.lean`; rename namespace/decls to Mathlib style; add to `TauCeti.lean`.
4. Delete `set_option`/`#eval`; fix to default heartbeats; replace anything Mathlib already has.
5. `lake build` module on Modal-equivalent or locally; run linters; `#print axioms` for every headline theorem.
6. `tauceti-review` locally; fix findings; commit.
7. Open PR: one topic, body ends with `Roadmap: <Area>` line; no stacking — wait for merge before the next dependent row.
8. After merge: mark `[x]`, put PR link in the table + journal; in math-proof1 note the new home in `README.md` / `research/research-log.md`.

### Phase 5 — Wrap-up
- [ ] P5.1 Reconcile this table: every module in `MathProof/` appears in exactly one row (run the coverage check below)
- [ ] P5.2 Update `README.md`, `docs/index.html`, `research/research-log.md` with upstream locations
- [ ] P5.3 Renew/close the project-intentions issue (`done`)

## 3. Phase 1 findings (2026-10-29)

Clones: TauCeti `~/zcode-workdir/tauceti` (`821b7239`, toolchain `v4.36.0-rc1`), roadmap `~/zcode-workdir/tauceti-roadmap`.
Local Mathlib `~/zcode-workdir/encore-mathlib/repo/mathlib4` (`312e0b7a8e`, toolchain **rc2**, files use the `module`/`public import` system → expect port edits).
- **Roadmap exists**: `TauCetiRoadmap/ModularForms` ("Hecke theory, newforms, and L-functions"; suggested home `TauCeti/NumberTheory/ModularForms/`). So modular forms IS in scope — the gate question is only *which pieces are still new*. Its README lists the Δ level-one example (τ(2)=−24, Prop 5.8.5) but explicitly does not claim Lehmer nonvanishing; Lehmer/Maeda/691 are not roadmap targets.
- **Already in TauCeti** (46 files under ModularForms + `HeckeRing`): Hecke operators at general level (`HeckeSlash/*`), `Eigenform`, `Newforms/*`, `SturmBound`, `LevelOne/DiscriminantEigenform` (Δ eigenform, coprime multiplicativity `discriminant_qExpansion_coeff_mul`, prime-power recurrence, `T₂Δ`), `LevelOne/GradedRing`, `LevelOne/QExpansion` (private `bernoulli_four/six`). ⇒ **HeckeLevelOne, Mordell, EigenLevelOne are redundant (A6–A8 dropped).**
- **Already in Mathlib** (local `master`): Δ (`Discriminant.lean`, `discriminant_eq_q_prod`, `discriminant_qExpansion_coeff_one`), level-one dimension formula + `S_12` rank 1, E_k q-expansions, Ramanujan derivative formulas, `HeckeRing/Defs`. **Not** in Mathlib: Hecke operators on forms, integer τ, 691, Bernoulli B₁₂.. evaluations, Sturm for forms.
- **Still genuinely new** (candidates): integer-valued `τ` + Δ q-product coefficient bridge (A2/A3), E₁₂ identity & `τ ≡ σ₁₁ [691]` (A4/A5), Lehmer prime-reduction, mod-691 sieve (A9–A11), `BernoulliHigh` (A12), `LehmerWeight*`, Maeda (Tier B).
- **Mathlib-version risk**: Mathlib is already on `rc2` + `module` files; TauCeti lags (`rc1`) but tracks master. Port against TauCeti's pinned Mathlib, not this repo's.
- **Coordination**: TauCeti README: register intentions via `leanprover-community/project-intentions`; workers read that board. Details in `TauCetiRoadmap` README "Coordinating work: intentions and claims" (read it in P1.7). Reviewing: `uvx --from git+https://github.com/TauCetiProject/TauCetiReview tauceti-review <PR>` (needs own Claude/Codex/Kiro login; `--conf ./tauceti.toml`). Rubrics in TauCetiReview `rubrics/`.
- `tauceti-review` NOT installed (runs remote code; run via `uvx` only when a PR exists).
- PRs: `Roadmap: ModularForms` line, no PRs/issues in the roadmap repo from agents.

New Phase 1 items:
- [x] P1.7 Read `tauceti-roadmap/README.md#coordinating-work-intentions-and-claims`, `tauceti/COORDINATION.md` §1–5, `TauCetiReview/rubrics/README.md`; record rules here
- [ ] P1.8 Ask on Zulip (HUMAN, P1.2) with the narrowed pitch: "integer τ + Δ coefficient bridge, 691 congruence, Lehmer reductions on top of existing `discriminantEigenform`" — and whether Lehmer/Maeda results fit the ModularForms roadmap or need a new roadmap (P1.3)

### Blockers needing the human (autonomous run stops here, 2026-10-30)
Full analysis, tables and wave plan: [`tauceti-port-report.md`](tauceti-port-report.md).
- [ ] H1 Review the report; confirm dropping A6–A8 (HeckeLevelOne/Mordell/EigenLevelOne) from the upstream plan
- [x] H2 Approve `lake exe cache get` (~7 GB) in `~/zcode-workdir/tauceti` — needed to compile any port (Modal cannot target TauCeti; new plumbing is forbidden)
- [ ] H3 Phase 1 HUMAN steps (P1.2–P1.4): Zulip, roadmap hook, `[Intention]` + `claim` (scope rubric can block Lehmer/Maeda/691 without a roadmap hook)
- Phase 3 Wave 1 (τ + Δ coefficient bridge, A2/A3) is next once H2 is granted; do NOT start Waves 4+ before H3.

## 4. Coverage check (run before ticking P5.1; also after any new module is added)
```bash
cd <repo>; for f in $(find MathProof -name '*.lean' | sed 's|MathProof/||;s|\.lean$||;s|.*/||' | sort); do
  grep -q "$f" research/tauceti-port-plan.md || echo "MISSING from plan: $f"; done
```
(`Maeda*Weights`, `PowChain`, `LehmerPrimePower`, `LehmerGrand`, `LehmerPrimeGrand`, `AxCheck*`, `MaedaGalois5*` are listed in grouped rows.)

## 5. Baseline audit (P2.1) — snapshot 2026-10-29
Files with mechanical blockers (`tools/tauceti_audit.sh`): Congruence691 (1), Weight12 (1), Bridge (2), Lehmer (2),
LehmerSieve691 (4), HornerCert (2), Poly5 (2), MaedaGalois (6), MaedaGalois4 (12), MaedaDim4Weights (36),
MaedaDim5Weights (42), MaedaSmallWeights (131), LehmerMod (5), LehmerPacked (11), LehmerPow32 (3), and the whole
MaedaGalois5 chain.  Clean today (0 set_option): Tau/Basic, HeckeLevelOne, Mordell, EigenLevelOne,
LehmerPrimeReduction, LehmerUnbounded, CongruenceSmall, BernoulliHigh, LehmerWeight16–26 — start there.
29 files use the `Ramanujan` namespace.  Numbers are `set_option` counts; `#eval`, `sorry`, bad imports: none found.

## 6. Progress journal (append-only)
- 2026-10-29 plan created; audit script `tools/tauceti_audit.sh` added. No item started.
- 2026-10-29 Phase 1: P1.1/P1.5/P1.6 done (see §3). Dropped A6–A8 as redundant with TauCeti. Next: P1.7, then HUMAN P1.2–P1.4.
- 2026-10-30 P1.7 done; wrote `research/tauceti-port-report.md` (have / covered upstream / not covered / PR waves / risks). Stopped before downloads and outward actions; awaiting H1–H3.
- 2026-10-30 H2 granted. Cache fetched (7.3 GB). A2+A3 merged into ONE module `LevelOne/DiscriminantTau.lean`, built clean (linters, no set_option, axioms std) on local branch `tauceti/wave1-tau-bridge` (unpushed). PR draft: `research/tauceti-wave1-pr-draft.md`. Awaiting H3 before any submission.
- 2026-10-30 Wave 2 (A4): `LevelOne/Weight12Identity.lean` on local branch `tauceti/wave2-e12-identity` (based on `main`, independent of Wave 1 — no stacking). Builds clean; `bernoulli 12` by `decide +kernel`, no set_option; axioms std. Unpushed. Next: A5 (needs Wave 1 + 2 merged for a non-stacked PR; local draft allowed).
- 2026-10-30 Wave 3 (A5): `LevelOne/CongruenceMod691.lean` on local branch `tauceti/wave3-tau-congruence-691` (= wave1 + wave2 merged + 1 commit). Builds clean, axioms std (see draft). Also added public `E₁₂_qExpansion_rel` to the Wave 2 file. Real PR order: W1 and W2 independently, then W3 after both merge. Unpushed.
