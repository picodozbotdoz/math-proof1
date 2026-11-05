# BLUEPRINT i25-2 — zmod-casts: propext-only `hmap` and LehmerSieve691

Objective: (a) every nested certificate of `MaedaWeightK.hmap` /
`MaedaT3WeightK.hmap` in `MaedaDim{6..10}Weights`,
`MaedaT3Dim{6..10}Weights`, `MaedaT3SmallWeights` (564) depends on
`propext` only; (b) the private `bad_residues` and `two_pow_sigma_nonzero`
in `MathProof/Tau/LehmerSieve691.lean` likewise (4).  All exported
statements unchanged.

Design (a): the cells are `show ((n : ℤ) : ZMod ℓ) = (r : ZMod ℓ) from by
decide +kernel`.  Replace by a generic lemma in a NEW light module (not
`HornerCert` — avoid touching heavy-chain ancestors), e.g.
`intCast_eq_of_emod : n % ℓ = r % ℓ → ((n : ℤ) : ZMod ℓ) = (r : ZMod ℓ)`
(`ZMod.intCast_eq_intCast_iff'` / `Int.emod_emod_of_dvd` route), with the
hypothesis decided over ℤ (`Int.decEq`, pow-free literals).  Generator:
`tools/gen_maedan.py` (all modes: T₂, `--prime 3`, `--prime 3 --small`;
`--check` byte-identical).  The dims-6–10 files are the expensive
full-only family (dim 10 ≈ 20 min each): build them one at a time, WORKLOG
heartbeat before each.
Design (b): hand-written file — restate the two private lemmas over
`List.range` / structural recursion with a bridge to the `Finset` forms used
downstream in the file; keep every public statement unchanged.  Do NOT
build heavy importers (`LehmerGrand`, `LehmerPrimeGrand`) — the
orchestrator re-verifies them at integration.

Gates: G1 audit (`#axiom_path` on one `hmap` cell and on `bad_residues`);
G2 generic lemma module + LehmerSieve691 green, nested 0 there; G3
`MaedaT3SmallWeights` + one dims-6 file green, nested 0; G4 all 11 files
green + full light root + both AxCheckDecide passes (0 nested in these
modules) + tauceti + ci_targets.
