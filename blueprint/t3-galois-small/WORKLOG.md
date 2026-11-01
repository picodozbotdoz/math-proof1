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

