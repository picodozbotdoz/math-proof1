# zmod-casts WORKLOG (iteration 25)

## 2026-11-05 start
- Worker started on impl/iteration25/zmod-casts @ 0644b00. Reading blueprint + NOTES.
- Wrote MathProof/ModularForms/IntCastCert.lean (intCast_eq_of_emod, intCast_eq_of_emod_of_eq), registered (lakefile + root).
- LehmerSieve691: bad_residues / two_pow_sigma_nonzero rewritten (Nat.decidableBallLT + Nat.pow, structural geom211). Uncommitted.
- Probe MathProof/Probe/ZModCastsProbe.lean (temporary, delete before commit). Running G2 probe on Modal (~5-10 min expected).
- G2 probe green (53 s / 6.03 GiB): nested 4 audited / 0 violations (sieve 2 + probes). Generator refactored (hmap_rw_items helper, IntCastCert import), all 11 files regenerated, --check byte-identical. Probing direct decide on chunked `^` literal.
- Probe: chunked `^` literal decided directly is propext-only -> single lemma IntCastCert.intCast_eq_of_emod (variant removed). Note: probe audits must cover map₂ (current module) — #audit_local.
- G3 run: probe importing MaedaT3SmallWeights + MaedaDim6Weights (expected 15-25 min).
- G3 GREEN (157 s wall, tree peak 15.17 GiB): MaedaT3SmallWeights 6.77 GiB, MaedaDim6Weights 6.39 GiB, LehmerSieve691 4.79 GiB; probe env nested 341 audited / 0 violations, top-level 182 / 0. No warnings. Committing.
- Next: Dim7..10 and T3Dim6..10, one Modal run each (probe importing the single file + nested audit), sequential background script runs/seq.sh. Expected total ~1.5-2 h (dim10 ~20 min each).
- Started runs/seq.sh (log: runs/seq.log, per-file runs/g4-<Module>.out) at $(date): Dim7 Dim8 Dim9 Dim10 T3Dim6..T3Dim10. Expected ~2 h total. Probe file is untracked scratch.
- 11:22:33 seq: T3Dim6 green (160 s, 6.56 GiB, nested 0), Dim7 green (215 s, 7.04 GiB, nested 0). Continuing.
- 11:41:53 seq: T3Dim7 green (233 s, 7.25 GiB), Dim8 green (367 s, 8.08 GiB), T3Dim8 green (343 s, 8.11 GiB), all nested 0. Next Dim9, T3Dim9 (~8 min each), Dim10, T3Dim10 (~20 min each).
- 12:02:48 seq: Dim9 green (574 s, 9.33 GiB), T3Dim9 green (557 s, 9.53 GiB), nested 0. Dim10 started (~20 min), then T3Dim10 (~20 min).
- 12:36:17 seq: Dim10 green (992 s, 11.18 GiB), T3Dim10 green (881 s, 11.13 GiB), nested 0 — G4 per-file runs ALL GREEN (11 Maeda files + LehmerSieve691, every probe nested 0).
- 2026-11-05 (orchestrator close-out): worker terminated by the session limit after starting seq.sh; the script finished on its own; WORKLOG closed and branch merged by the orchestrator from the run logs (runs/seq.log, runs/g4-*.out).  Scratch probe MathProof/Probe/ not committed (untracked scratch).  Full light root + both AxCheckDecide passes run on the integrated trunk.
