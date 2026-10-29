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
- [ ] P1.1 Read TauCeti README "Coordinating work: intentions and claims" + TauCetiReview rubrics; note deltas here
- [ ] P1.2 **HUMAN** Zulip "Getting started: roadmaps": ask whether level-one modular forms / Hecke / Δ-bridge belongs and under which roadmap
- [ ] P1.3 **HUMAN** Roadmap hook: existing item, or human-authored roadmap PR in TauCetiRoadmap (milestones: Hecke `T_p`, Mordell, eigenforms, Δ bridge)
- [ ] P1.4 **HUMAN** `[Intention]` issue in leanprover-community/project-intentions (90-day expiry; renew before lapse)
- [ ] P1.5 Clone TauCeti to `~/zcode-workdir/tauceti`; install `tauceti-review` (TauCetiWorker via `uv`); confirm toolchain = ours
- [ ] P1.6 Mathlib overlap survey: for each candidate (below) diff against Mathlib `master` `NumberTheory/ModularForms` (Δ, Eisenstein, Hecke, q-expansion); record "already upstream / partial / new" in the table
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
| [ ] | A2 | `Tau/Basic` (algebraic τ, list arithmetic) | 460 | check vs Mathlib `ModularForm.Delta`/`ArithmeticFunction`; may be dropped if Mathlib has τ | |
| [ ] | A3 | `Tau/Bridge` (qExpansion Δ = τ) | 516 | 2 set_option; needs A2 or Mathlib τ | |
| [ ] | A4 | `ModularForms/Weight12` (691•E₁₂ identity, Sturm) | 231 | 1 set_option; Bernoulli evaluations | |
| [ ] | A5 | `ModularForms/Congruence691` | 299 | 1 set_option; needs A4 | |
| [ ] | A6 | `ModularForms/HeckeLevelOne` (T_p from scratch) | 938 | split into ≥2 PRs (definition+invariance / q-coefficient formula); check Mathlib Hecke overlap | |
| [ ] | A7 | `Tau/Mordell` (multiplicativity, prime-power recursion) | 239 | needs A6, A3 | |
| [ ] | A8 | `ModularForms/EigenLevelOne` (weight-generic rank-one eigenforms) | 270 | needs A6/A7 | |
| [ ] | A9 | `Tau/LehmerPrimeReduction` (τp≠0 ⇒ τ(p^a)≠0; reduction to primes) | 223 | needs A7 | |
| [ ] | A10 | `Tau/LehmerUnbounded` | 79 | needs A7/A9 | |
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
