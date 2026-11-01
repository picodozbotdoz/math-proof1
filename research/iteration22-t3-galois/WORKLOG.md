# Worklog — dev/iteration22-t3-galois (T1: Gal = Sₙ for the T₃ charpolys, dims 6–10)

Append dated entries as you go (stage gates passed/failed, Modal runs with
build time + peak RSS, decisions, deviations).  This file is the
inter-session resume point: make it possible to continue cold.

Task source: T2 submission 2026-11-02, Task A; task definition =
`external-doc/ENTRY-PROMPTS.md` §2 (filled T1 example).

## Entries

### 2026-11-02 — session start: state determination, branch created

* No branch `dev/iteration22-t3-galois`, no `MaedaT3Galois*` modules, log lists
  the T₃ Galois half as open (iteration21-review §9.3) → task never commenced;
  executing it from scratch per the T1 definition.
* Branch `dev/iteration22-t3-galois` created from trunk `fbc5f9b`
  (= master = dev/zai tip; clean tree).
* Plan (mirrors the T₂ galois-full route, ENTRY-PROMPTS §2):
  - G1 audit: extract kernel-verified T₃ charpolys `P` from the committed
    `MaedaT3Dim{6..10}Weights.lean` (ground truth), cross-check the
    iteration-20 census `maeda_t3_dim6_10.json` against them.
  - G2: extend `tools/galoisfull_certs.py` + `tools/gen_galoisfull.py` with
    `--prime 3` (T₂ modes byte-identical via `--check` before/after).
  - G3: generate `MaedaT3GaloisDim{6..10}Weights.lean`, verify each on Modal
    (0 err / 0 warn), commit per green file.
  - G4: audits (combined AxCheckDecide, tauceti_audit.sh) + registration
    (measure CI add; > ~10 min ⇒ root-only + flag to operator).
  - G5: bookkeeping (README, docs page, AGENTS.md layout, research-log).
* Inbox poll (§9 checkpoint, session start): empty (README + empty done/) —
  no steering files.
