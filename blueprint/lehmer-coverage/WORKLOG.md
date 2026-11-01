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

### 2026-11-01 (session 1) — G2 anchor module: GREEN (bed7285); G3 memo: CLOSED

- Inbox poll before the Modal runs: no STEER files.
- DESIGN DEVIATION (forced by fact, evidence: Mathlib
  Data/Nat/Prime/Defs.lean — "This definition is by well-founded recursion,
  so `rfl` or `decide` cannot be used"): the blueprint's filter decide
  `(List.range n).filter (fun k => (691*k+690).Prime) = [...]` is NOT
  kernel-decidable — `Nat.Prime`'s decidability instance routes through
  `minFac`/`minFacAux`, which is well-founded recursion.  Replacement (same
  job, kernel-cheap): a structural trial-division certificate
  `noFactorFrom n d k : Bool` (own def, `HornerCert` tradition) with a
  one-time correctness lemma `prime_of_noFactorFrom` (via
  `Nat.minFac_sq_le_self`) and `noFactorFrom_of_prime` for the bridge.  The
  decided statements stay plain arithmetic (Bool/Nat), per the mission.
- Fast iteration trick used: `lake env lean <module>` from the MAIN repo
  (read-only; its .lake has warm oleans incl. LehmerSieve691) — full
  elaboration in seconds; the authoritative check stayed on Modal.
- Module MathProof/Tau/LehmerCoverageCount.lean (2^18 + 2^20 tiers):
  * `badPrimes2p18_filter` — decide +kernel: 285 candidates (k=94..378),
    divisors 2..512, → the 17 bad primes. `badPrimes2p18_spec` (each member:
    prime, >65536, <2^18, ≡690) + `bad_prime_lt_2p18_mem` (completeness) +
    Nodup (via filter/map).
  * `uncoveredSet B L` (Finset: n ∈ [1,B) divisible by some p ∈ L),
    `card_uncoveredSet` (structural no-overlap count identity:
    card = Σ⌊(B−1)/p⌋; disjointness from p·q ≥ 65537² > 2³² via
    `Nat.Prime.dvd_mul_of_dvd_ne`), `uncovered_2p18` (= 23, final sum by
    decide +kernel), `covered_count_2p18` (= 262120).
  * 2^20 twin: `badPrimes2p20` (98 literals), `badPrimes2p20_filter` (1423
    candidates, divisors 2..1024), spec/bridge/nodup, `uncovered_2p20` = 227,
    `covered_count_2p20` = 1048348.
  * COST GATE PASSED (measured): local `lake env lean` whole file ≈ 23 s;
    Modal `--file`: Built in 32 s, peak RSS 5.76 GiB (well under the ~120 s
    kernel gate and the 16 GiB alert threshold). 2^20 tier INCLUDED.
- tauceti_audit.sh: 0 set_option / 0 #eval / 0 native / 0 sorry / 0 bad-imports.
- Registration (trio, gate passed): lakefile.toml defaultTargets,
  MathProof.lean root import, CI workflow build-args — all after
  LehmerPrimeReduction.
- AxCheckDecide on Modal: "1204 decide certificates audited, 0 depend on
  more than propext" (+4 new certs from this module, all axiom-clean).
- G3 CLOSED (memo committed with G1 as DECISION-131072.md): monolithic 131072
  decide projects ~110–125 GiB ≈ 1.8× the 64 GiB steering stop-rule ⇒ default
  DESCOPE, reopen only on explicit steering + Bench-staged digit-list-split
  prototype (< 64 GiB/decl measured first). Surfaced to operator in the final
  session summary (this wave's report), per the stop-rule protocol.

### 2026-11-01 (session 1) — G4 bookkeeping: GREEN (final commit)

- research-log.md: appended "Iteration 22, T2 — LehmerCoverage" entry
  (headline numbers, module, audits, measurements, corrections, descope).
- README.md: new "Exact verified coverage" bullet (99.9093 % headline,
  4 291 072 962 / 4 294 967 295, kernel anchors) + module-list line for
  LehmerCoverageCount.
- docs/index.html: checked — no coverage/2^32 mentions ⇒ no change (G4
  conditional not triggered).
- AGENTS.md Layout: LehmerCoverageCount entry added (incl. the
  "Nat.Prime is not kernel-decidable" gotcha for future modules).
- Inbox polls throughout the session: no STEER-lehmer-coverage-* or
  STEER-all-* files ever appeared; nothing to disposition.
- All four gates G1–G4 closed; lineage not drained (session ~3 h, well under
  cap). Final state: 3 green commits on impl/iteration22/lehmer-coverage
  (G1 study 1ea9ae6, G2 module bed7285, G4 bookkeeping). Never pushed.
