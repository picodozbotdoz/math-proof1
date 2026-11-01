# Worklog — impl/iteration22/t3-galois-small

Append dated entries as you go (stage gates passed/failed, Modal runs with
build time + peak RSS, decisions, deviations from the blueprint).  This file
is the inter-session resume point: make it possible to continue cold.

Blueprint: blueprint/t3-galois-small/BLUEPRINT.md (in this worktree) — a STARTING
POINT, not a contract: run its G1 audit, then deviate per the deviation
protocol (RESEARCH-WORKFLOW §4d) whenever facts disagree, with evidence here.
Base commit: 569bcf0 (trunk dev/iteration22-maeda-lehmer).

## Entries

### 2026-11-02 — session start; inbox empty; Q1 PASSED: MaedaGaloisQuad green + trio

* State: worktree clean at `dcfe981` (base `569bcf0`), no prior entries —
  task started from scratch.  Blueprint + probe FINDINGS read; T1 WORKLOG
  (G2 byte-identity discipline, G3 Modal loop) read as precedent.
  Inbox poll (session start): empty.
* Baseline byte-identity gate BEFORE any generator edit:
  `gen_galoisfull.py --check` and `--prime 3 --check` — all ten dim files +
  both axchecks byte-identical. ✓
* **Q1**: `MathProof/ModularForms/MaedaGaloisQuad.lean` (67 lines, Mathlib-only
  imports): `bijective_of_quadratic` per FINDINGS §2.2 sketch — two roots
  (`card_rootSet_eq_natDegree`), pretransitivity (`galAction_isPretransitive`
  transported to the range), `2 ≤ card range` (surjective orbit map),
  `card range ≤ card Perm = 2! = 2`, `range = ⊤` (`Subgroup.eq_top_of_card_eq`),
  same finish as `MaedaGaloisFull.bijective_of_frobenius`.
  * Modal iteration 1: `SubmonoidClass.subtype_injective` needs its explicit
    subobject (`(SubmonoidClass.subtype_injective _)`); iteration 2: the lemma
    takes `H` explicitly, `refine … ?_` bound `?_` to `H` — switched to `apply`.
  * Modal green: **34 s wall / 3.84 GiB module peak RSS, 0 err / 0 warn**.
  * `tauceti_audit.sh`: 0 set_option / 0 eval / 0 native / 0 sorry / 0 bad-imports.
  * Trio registration: `MathProof.lean` root import, `lakefile.toml`
    defaultTargets, CI workflow list (all next to `MaedaGaloisFull`).
    Combined root build + AxCheckDecide deferred to S3 (one root build covers
    both registrations, T1 G4 precedent).
* Deviations: none (blueprint shape followed; D2 wrapper not needed yet —
  the n=3 defeq question only arises at S3).

### 2026-11-02 — S2 PASSED: --small scan, 24/24 anchored, reproduces probe table

* `tools/galoisfull_certs.py --small` (new `small_main`, prime-2/3 paths
  textually untouched except a pure refactor of `lean_t3_charpolys` into
  `_parse_charpoly_file`): census `maeda_t3_small.json`, anchors = kernel-
  verified `P` literals of `MaedaT3SmallWeights.lean` (24/24 exact), nm1 +
  transp scans `[max(2n, n+3), 4000)` with the transp scan skipping the nm1 ℓ
  (the probe's distinct-prime discipline for n = 3), every hit re-multiplied
  and squarefree-checked.
* Output `research/iteration22/data/t3_galoisfull_small_certs.json` (24
  records): dims 3–5 in the T1 shape (`nm1`/`transp`), dim 2 carries a
  `quad` provenance entry (irreducible-quadratic reduction ℓ; consumed by
  nothing on the Lean side).  **Every ℓ and gbar degree reproduces FINDINGS §3
  exactly** (nm1 23–89, transp 23–83, quad 23–41; no `same_ell` fallback fired).
* Name note: FINDINGS §4 suggested `t3_galois_small_certs.json`; the emitted
  name is `t3_galoisfull_small_certs.json` (mission/blueprint wording,
  consistent with the T1 `t3_galoisfull_certs.json`).
* Byte-identity gate after the edit: `gen_galoisfull.py --check` and
  `--prime 3 --check` — PASS (all ten files + both axchecks).

### 2026-11-02 — S3 PASSED: generated file green, root-only registration, audits

* `tools/gen_galoisfull.py --prime 3 --small`: `--small` mode (implies
  prime 3; prime-2 / prime-3-dim paths untouched), dim-2 branch in
  `emit_weight` (no cP/g1/g2 blocks — the theorem is
  `MaedaGaloisQuad.bijective_of_quadratic P_monic P_natDegree maeda`),
  `header_small` + `emit_axcheck_small`.  Emitted
  `MaedaT3GaloisSmallWeights.lean` (2 230 lines, 24 weights) +
  `MaedaT3GaloisSmallAxCheck.lean` (32 lines); `--small --check`
  byte-identical; prime-2 and prime-3 `--check` byte-identical before AND
  after every generator edit.
* **The n=3 `{3−1}`/`{2}` defeq holds** — no D2 wrapper needed: the uniform
  two-block emission with the two distinct scan primes elaborates as-is.
* Modal builds (all 0 err / 0 warn):
  * `MaedaT3GaloisSmallWeights`: **module 34 s, wall 72 s, peak tree
    6.62 GiB, module peak 5.38 GiB** (parent MaedaT3SmallWeights served from
    the shared build cache).
  * `MaedaT3GaloisSmallAxCheck`: all 24 theorems + the three infra lemmas +
    `MaedaGaloisQuad.bijective_of_quadratic` on exactly `propext,
    Classical.choice, Quot.sound`; 83 s / 4.76 GiB.  (One iteration: the
    audit docstring exceeded the 100-char line limit — reflowed in the
    generator, regenerated, rebuilt.)
  * Combined root + `MathProof.AxCheckDecide` (root-only registration in
    `MathProof.lean`; NOT defaultTargets/CI — the file imports the non-CI
    `MaedaT3SmallWeights`, policy note extended in `lakefile.toml`):
    **1 310 decide certificates audited, 0 depend on more than propext**
    (+108 over T1's 1 202; root 5.35 GiB, AxCheckDecide 5.47 GiB, wall 84 s).
* `tauceti_audit.sh` clean on all three new files (0/0/0/0/0).

### 2026-11-02 — S4 PASSED: bookkeeping; TASK CLOSED

* README: the "T₃ Galois twin" paragraph now states all 54 weights (both
  generated files, the two routes, ℓ ranges, the dim-2 lemma) — "(T₃ Galois
  dims 2–5 remain open)" removed.
* `docs/index.html` card: "across the dim-6…10 weights" → "at every one of
  the 54 weights … the six dim-2 weights need no certificate — an
  irreducible quadratic already has Gal = S₂".
* AGENTS.md layout: `MaedaGaloisQuad` + `MaedaT3GaloisSmallWeights` entries
  with the measured Modal costs and the root-only rationale, right after
  the T₃ dim entry.
* research-log: "Iteration 22, t3-galois-small" entry (result, two routes,
  pipeline, registration policy, measurements, audits).
  WAVE-TRACKING status row → COMPLETE.
* Inbox polled at every gate (start, Q1, S2, S3, S4): empty throughout —
  no steering files to process.
* Deviations from the blueprint: **none**.  D1/D2/D3 fallbacks all unused
  (the quad lemma elaborated after two one-line Modal iterations; the n=3
  defeq holds; the single 24-weight file builds in 34 s).  Descope-free.
* Task state: COMPLETE on `impl/iteration22/t3-galois-small`
  (base `569bcf0`, commits through the S4 commit); merge is the
  operator's.

