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

### 2026-11-02 — G1 PASSED: charpoly anchors 30/30

`g1_anchor.py` (this dir): parsed the chunked `P` literals of the committed
`MaedaT3Dim{6..10}Weights.lean` (leading-zero chunk numerals forced a
structural parser — Python `eval` rejects them), compared per weight against
(1) the iteration-20 census `charpoly` and (2) an independent Newton-identity
charpoly of the census `matrix`.  30/30 exact; census == kernel-verified
Lean literals.  Commit `0d131ed`.

### 2026-11-02 — G2 PASSED: --prime 3 in both generators, T₂ byte-identical

* `galoisfull_certs.py --prime 3`: census without Frobenius hints (`.get`),
  output `research/iteration22-t3-galois/data/t3_galoisfull_certs.json`;
  re-asserts census charpoly == Lean `P` literal per weight at run time.
  Scan found all 30 cert pairs; 4 weights hit the random transposition scan:
  k=112 ℓ=8 664 941, k=122 ℓ=4 953 917, k=130 ℓ=1 897 823, k=134
  ℓ=7 694 233 (Bézout witnesses mandatory at this scale — zpgcd overflows).
* `gen_galoisfull.py --prime 3`: emits `MaedaT3GaloisDim{6..10}Weights.lean`
  (+ `MaedaT3GaloisFullAxCheck.lean`), reopens `MaedaT3Weight{k}`.  T₂
  `--check` byte-identical before AND after the edits; T₃ `--check`
  byte-identical.  Line-length lint clean on all six files.
* Commit `e41319f`.

### 2026-11-02 — G3 PASSED: all five modules green on Modal (0 err / 0 warn)

| module | build | module peak RSS |
|---|---|---|
| MaedaT3GaloisDim6Weights | 25 s | 5.24 GiB |
| MaedaT3GaloisDim7Weights | 38 s | 5.38 GiB |
| MaedaT3GaloisDim8Weights | 37 s | 5.59 GiB |
| MaedaT3GaloisDim9Weights | 58 s | 5.87 GiB (k=112, ℓ≈8.7M) |
| MaedaT3GaloisDim10Weights | 83 s | 6.22 GiB (k=134, ℓ≈7.7M) |

All ≪ 16 GiB alert line; no memory investigation owed.  Commits `e41319f`
(files) — build results recorded here.

### 2026-11-02 — G4 PASSED: registration + all audits green

* `MaedaT3GaloisFullAxCheck` on Modal: all 30 theorems on exactly
  `propext, Classical.choice, Quot.sound`.
* Registration: full trio (root `MathProof.lean`, `defaultTargets`, CI list)
  — Modal total 241 s ≈ T₂ galois set; CI add ≈ 4–8 min < the ~10 min
  root-only threshold in the task constraints, so full registration (same
  treatment as the T₂ twins).  Commit `7a7135e`.
* Combined root build green (30 s / 6.64 GiB); combined `AxCheckDecide`:
  **1 202 certificates, 0 > propext** (+180 from T₃-Galois);
  `tauceti_audit.sh` clean ×5.

### 2026-11-02 — G5 PASSED: bookkeeping; T1 TASK CLOSED

README (T₃ Galois twin paragraph), docs card sentence, AGENTS.md layout with
measured costs, research-log entry "Iteration 22, T1".  Commits `27a6885` +
this entry.  Inbox polled at every gate: empty throughout.  Deviations from
the plan: none (the ENTRY-PROMPTS §2 task definition was accurate — the
first time a blueprint-shaped document needed no correction; the re-derivation
discipline still paid for itself as the anchor net that makes the certificates
trustworthy).  Task state: COMPLETE on `dev/iteration22-t3-galois`
(base `fbc5f9b`, head `27a6885`+); master merge is the operator's.
