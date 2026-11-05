# WORKLOG — maeda-small (iteration 25)

## 2026-11-05 start
- Base 0644b00, branch impl/iteration25/maeda-small. Read BLUEPRINT; next: G1 audit (gen_maeda.py, MaedaCertC import order).
- G1: no cycle (MaedaCertC -> MaedaDim4 -> MaedaLevelOne; none import MaedaSmallWeights). Route = dim-4 pattern for all dims:
  per form `L{j}c : seqPLc … (2d+1) = [...]` decide + `L{j}` via `seqPLc_eq`, q cells via `seqP_getD` (proofs only; statements
  unchanged). gen_maeda.py patched (NL = 2d+1 everywhere, header imports MaedaCertC); dim4/dim5 regeneration byte-identical.
  MaedaSmallWeights regenerated (uncommitted). Next: Modal --file run.
- G2a: Modal --file MaedaSmallWeights green, 0 warnings (module 25 s; run 109 s wall; peak tree 6.15 GiB). Committed. Next: AxCheckDecide nested audit.
