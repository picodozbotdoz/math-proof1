# Worklog — impl/iteration22/lehmer-coverage

Append dated entries as you go (stage gates passed/failed, Modal runs with
build time + peak RSS, decisions, deviations from the blueprint).  This file
is the inter-session resume point: make it possible to continue cold.

Blueprint: blueprint/lehmer-coverage/BLUEPRINT.md (in this worktree) — a STARTING
POINT, not a contract: run its G1 audit, then deviate per the deviation
protocol (RESEARCH-WORKFLOW §4d) whenever facts disagree, with evidence here.
Base commit: 569bcf0 (trunk dev/iteration22-maeda-lehmer).

## Entries

### 2026-11-01 (session 1) — G1 study port + regeneration: GREEN

- Inbox poll at session start: only README.md present, no STEER-lehmer-coverage-*
  or STEER-all-* files. Nothing to disposition.
- Copied probe artifacts from /home/doz/tmp/math-proof1-temp/probe2/ into
  `research/iteration22/lehmer-coverage/` (script, npy, probe run log).
- Rewrote the script repo-relative (outputs land next to it), folded in as
  committed tests: the 70481 anchor assertion, the slice start-index guard
  (the probe's own bug class), the deterministic 12-base Miller-Rabin audit
  (all 98 < 2^20 + 3000 random + last), plus per-bound counts table and the
  G2 candidate census. Added bad_primes_2p32.txt.gz (decimal list).
- Regeneration (`python3 bad_prime_sieve.py all`, log = run_full.log) MATCHES
  every mission anchor: U(2^26)=40,226; U(2^32)=3,894,333 → covered
  4,291,072,962/4,294,967,295 = 99.909328%; bad primes (65536,2^32]=294,618;
  first bad prime 70481 (= Lean gap bound, asserted); npy array-identical to
  the probe's.
- DEVIATION (data corrections, evidence in run_full.log + STUDY.md §3):
  1. FINDINGS §2.2 census cell "2^30: 116,788 bad primes" is WRONG — exact
     78,715 (li(2^30)/690 ≈ 78,843 backs it; all U(B) cells match, data
     files unaffected). Blueprint CORRECTIONS note added.
  2. Blueprint/mission "284 candidates at 2^18" → actually 285 (k=94..378).
     17 primes / U=23 unchanged. Blueprint CORRECTIONS note added.
- G3 memo written alongside (DECISION-131072.md): descope by default,
  ~110–125 GiB ≈ 1.8× the 64 GiB stop-rule; surfaced to operator in the
  session summary + final report.
- Commit: G1 green commit (study dir complete).
