# Iteration 25 — INIT notes (2026-11-05)

Operator decision (chat, 2026-11-05, answering iteration24-review §7.1):
**"Retrofit them"** — make the 5296 pre-24 nested `decide` certificates
`propext`-only.  The chain rebuild the retrofit implies (`MaedaSmallWeights`
is an import ancestor of the heavy `MaedaGalois5` chain, ≈ 33 min / 35 GiB)
was named in the question and is taken as approved.

Trunk `dev/iteration25-nested-certs` from `dev/iteration24-hecke-index`
825e5a6 (iteration 24 not yet merged to master — the trunk carries it).
Recon: pin unchanged since 2026-11-04 (stay at `v4.36.0-rc1`); no boundary
bump.

Baseline (iteration-24 combined audit, `research/iteration24/nested-decide-audit.txt`):

| family | modules | lemma | count | cause |
|---|---|---|---|---|
| scaled | HeckeIndex{Small,}Weights | `scaled` | 2304 | `Finset` sum of `Matrix` powers, cell decides |
| scaled | HeckeRational{Small,}Weights | `scaled_id` | 2304 | same |
| zmod | MaedaDim{6..10}Weights, MaedaT3Dim{6..10}Weights, MaedaT3SmallWeights | `hmap` | 564 | `((n:ℤ) : ZMod ℓ) = r` decided in `ZMod` |
| seqP | MaedaSmallWeights | `q*_*` | 120 | `seqP … = v` decided (Finset / ArithmeticFunction) |
| sieve | Tau/LehmerSieve691 | private `bad_residues`, `two_pow_sigma_nonzero` | 4 | `Finset.range` quantifier / sum |

Heavy downstream re-verification (orchestrator, serialized, at
integration): `tools/stage_chain.sh` (MaedaGalois5 chain) +
`MaedaGalois5AxCheck`; `LehmerGrand`, `LehmerPrimeGrand` (import
`LehmerSieve691`).  Exported theorem statements must not change, so no
downstream light file needs edits.
