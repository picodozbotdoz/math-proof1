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
