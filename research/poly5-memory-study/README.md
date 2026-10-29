# Why the `MaedaGalois5` identity chain needs 137–202 GiB, and how to avoid it

Memory-alert investigation (AGENTS.md "Memory alerts"; backlog entry in
`research/memory-alerts.md`), 2026-10-29.  All runs on Modal (xyz account)
with `LEAN_CHECK_PROFILE` (per-declaration RSS attribution, `Elab.async=false`).

## 1. Where the memory goes

Per-declaration profile of `MaedaGalois5IdBase` (peak 24.5 GiB):

| declaration | RSS growth | time |
|---|---|---|
| `e3dec` (kernel `decide`) | **+18.5 GiB** | 225 s |
| `e2dec` | +1.9 GiB | 19 s |
| every `*_eval`, `theta_eK`, literal `def` | +0.0 GiB | ≤ 3 s |

`MaedaGalois5Identities`: `ddec` +14.6 GiB of a 19.5 GiB peak.  The kernel
certificates are the whole cost; elaboration (`simp`/`ring` in the bridge
lemmas) is negligible — the hypothesis in the improvements doc (P1-3) was
wrong.

## 2. A linear model

`workmodel.py` simulates `Poly5.pMul`/`pAdd` exactly (`pMul (t :: ts) q =
pAdd (pScale t q) (pMul ts q)`, so a product costs ≈ |p| · |result| list
operations) and counts the list operations each certificate makes the kernel
perform.  Against the measured memory:

| identity | work (M list ops) | measured | GiB / M ops |
|---|---|---|---|
| e2 | 0.09 | +1.9 GiB | 21 |
| e3 | 0.71 | +18.5 GiB | 26 |
| δ² (`ddec`) | 0.56 | +14.6 GiB | 26 |
| e4 | 7.40 | 202 GiB (module peak) | 27 |
| e5 | 5.04 | 137 GiB | 27 |
| e6 | 5.36 | 172 GiB | 32 |

**Kernel memory ≈ 27 GiB per million list operations inside one
declaration** (the kernel keeps every intermediate term of a `decide` in its
caches until the declaration is done), and time ≈ 300 s per M ops.  This
also explains the "E4 > E6" puzzle: E4's left side is C(6,4) = 15 separate
products of four Θ's (7.16 M ops), E6's is a single product (3.37 M).

## 3. Levers (modelled, then measured)

| lever | e4 | e5 | e6 |
|---|---|---|---|
| today (brute force e_k, one `decide`) | 7.40 M | 5.04 M | 5.36 M |
| balanced-tree `pMul` only | 3.45 M | 3.25 M | 3.99 M |
| **LHS by the recurrence** `E_k += Θ_j · E_{k−1}` (∏(1 + Θ_j T)) — LHS only | **0.44 M** (was 7.16) | 0.93 M (was 4.29) | 1.43 M (was 3.37) |
| RHS (Horner over `va … ve`), unchanged | 0.24 M | 0.76 M | 1.99 M |

The recurrence computes e_k(Θ₀ … Θ₅) with ≤ 6·k multiplications by a
25-term Θ_j instead of C(6,k) products of k Θ's.  Second lever: check LHS
and RHS in **separate declarations against one shared literal** (the
generator emits the canonical result, in 64-term chunks joined by `++`), so
the kernel caches reset in between and the peak is the larger side, not the
sum.

## 4. Measured prototypes (`proto_dp.py`)

| module | today | prototype (recurrence + split) |
|---|---|---|
| E4 | 202 GiB, 2343 s | **19.0 GiB, 221 s** (LHS +12.9 GiB / 129 s, RHS +6.7 GiB / 60 s) |
| E6 | 172 GiB, 2207 s | **63.2 GiB, 1414 s** (LHS +28.7 GiB / 379 s, RHS → 63 GiB / 942 s) |

E4 matches the model (≈ 18 GiB predicted).  In E6 the RHS Horner chain
(1.99 M ops ≈ 56 GiB) is now the bottleneck; splitting it once more at a
literal checkpoint should bring E6 to ≈ 35 GiB (estimate), E5 ≈ 31 GiB
(estimate).  A fully stepwise variant (`proto_stepwise.py`, one declaration
per operation) on e3 gave 10.2 GiB vs 24.5 GiB but doubled the time
(literal elaboration) — the coarse split above is the better trade-off.

## 5. Recommendation

1. `tools/gen_poly5.py`: emit the LHS by the recurrence; emit the canonical
   result as a chunked literal and certify `LHS = Lit`, `RHS = Lit` (and split
   the e5/e6 RHS at one checkpoint) as separate declarations.  The soundness
   bridge is unchanged: `PEval_pAdd`/`PEval_pMul` turn the recurrence into a
   polynomial in the six atoms Θ_j, and a `ring` of degree ≤ 6 (≤ 20
   monomials) matches it to the symmetric sum.  Expected: every chain module
   < 64 GiB, chain wall ≈ 40 min instead of ≈ 2 h (estimates from §3–4).
2. Further constant-factor lever (not prototyped): pack a `Mon` into one `ℕ`
   (Kronecker exponents) so monomial product/compare are single GMP ops; the
   ≈ 27 KiB-per-op cost is mostly instance unfolding on nested `Prod`s.  Needs
   a carry-free degree-bound argument in the soundness proof.
3. Apply the cost model before writing any new kernel certificate (dim ≥ 6):
   predicted GiB ≈ 27 × (M list ops in one declaration).

Rolling it out regenerates the heavy chain (`IdBase … Identities`), so it is
best batched with the other pending chain-rebuild items (improvements P1-2 /
P2-1, the 19 ancestor certificates).

## 6. Rollout (2026-10-29)

Implemented in `tools/gen_poly5.py` (recurrence nodes and Horner checkpoints
as literals, each with its own `decide`; budget 0.5 M modelled operations) and
rebuilt with `tools/stage_chain.sh`:

| module | before | after |
|---|---|---|
| `IdBase` | 24.5 GiB, 209 s | 8.1 GiB, 93 s |
| `IdE4` | 202 GiB, 2343 s | 13.5 GiB, 207 s |
| `IdE5` | 137 GiB, 1498 s | 22.0 GiB, 434 s |
| `IdE6` | 172 GiB, 2207 s | 34.7 GiB, 977 s |
| `Identities` | 23 GiB, 170 s | 17.6 GiB, 273 s |

## Files

`workmodel.py` (cost model; set `TREE=1` for the tree-`pMul` variant),
`dpmodel.py` (recurrence cost), `proto_dp.py K OUT.lean` (recurrence + split
prototype), `proto_stepwise.py` (fully stepwise prototype).  They read the
generated `MaedaGalois5Id*.lean` files; run from the repository root (paths
inside point at `/tmp` scratch copies).
