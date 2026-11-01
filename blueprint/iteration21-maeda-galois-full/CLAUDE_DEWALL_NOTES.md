I'll start with the state of that worktree and any record of where the stage stalled.

The real path is `/home/doz/claude-workdir/...` (hyphen, not underscore), and it's registered as a worktree of this repo.

The last committed step is M2, and an uncommitted M3 sits in the tree past where the worklog ends. I'm checking whether M3 compiles, which tooling the predecessor used, and whether any session recorded what blocked it.

Next I'll get access to that worktree and check the predecessor's run logs and session transcripts, to see whether the uncommitted M3 ever compiled.

No Modal run has built `FrobeniusCycleType` since Oct 31, so this file is still unverified there. I'm compiling the uncommitted M3 now for a real status and searching for the "wave tracker" commit that may describe the block.

That's the actual stall: lines 1–641, through M2, are fine, but the uncommitted M3 block has about 20 errors, and it was never built. Here is the full error text, plus the wave tracker.

The block is clearer now and smaller than the worklog implied: M3 was never compiled against this pin, so several errors are simple fixes, and the remaining plan can drop the resultant transport. I'm checking the APIs this depends on before committing to that simpler design.

All the needed APIs are confirmed, so the orbit analysis will be short. The session's main directory has moved to this worktree, and I'll read the Galois action definitions and the weight files' statements of P, maeda and the Rabin certificate before writing.

The design holds, so I'm rewriting the block as a whole: trimming M3 to what the proof needs, adding a generic orbit lemma over any field, and building the Dedekind theorem on it. I'm checking the last definitions before writing it out.

Only six real errors on the first pass, down from about 20, and the orbit lemma is nearly done. Details:

`ZMod.algebra` exists but isn't imported, the same failure as `QuotientRing`. Adding the import and rebuilding.

Only one error is left, a redundant trailing `rfl`, so the Dedekind core already type-checks. I'm dropping `hne` and the `rfl`, then checking the weight-file pattern for the G2 assembly.

The blocker is resolved: the uncommitted M3 draft had about 20 compile errors, so I rewrote it with a simpler proof, and the Dedekind theorem now type-checks apart from one stray `rfl` I removed, with nothing committed yet. Next I'm writing the generic `Sₙ` assembly and per-weight generator to run weight 72 end to end for gate G2.

The Dedekind theorem and the generic Sₙ assembly both build cleanly on Modal, with no warnings. I'm now building maeda_galois_full at weight 72, the G2 gate, which pulls in the dim-6 module.

G2 passed. Next I'll audit the axioms in `maeda_galois_full` and confirm its build log, then generate all 30 weights and fix the last `JordanPrimitive` warning.

The logs confirm the module compiled. Before the full run I'll fix the over-long generated lines and the JordanPrimitive warning, and add a kernel-checked axiom audit; then all five dimensions run in the background, one at a time.

All 30 weights are building in the background. Meanwhile I'm checking the two overlong lines flagged in dimension 10; the other hits come from Unicode lines that `awk` miscounted, and the linter already passed them.

Two lines in `g2_fact` are too long, so I'll wrap them in the generator. That only touches `MaedaGaloisDim10Weights.lean`, which the current run hasn't reached yet, so it won't affect that run.

Correction: that generator change touched all five files, not just dim 10, so the dim-6 module now running was built from slightly older text. The change is whitespace only, and the final axiom-audit step imports all five dimension modules, so it rebuilds any stale module from the final bytes.

I'll report back when the background run finishes. Nothing is committed yet.

Dims 6–9 passed with no errors or warnings, so 24 of the 30 weights are done. Dim 10 hit a kernel `deep recursion` on two lemmas. Here's what they are.

The root cause is an engine recursion limit, not a bad certificate, so the fix is to supply an explicit Bézout witness from Python and have the kernel check it without inverses. I'll add that as `irreducible_of_rabin_bezout` for all weights, update the stale docstring, and replace the `ring` call that only worked through its fallback.

The rebuild of all five dimensions plus the axiom audit is running in the background with the Bézout certificates. I'll report the result when it finishes.

Every module builds cleanly, and all 30 `maeda_galois_full` theorems rest only on the standard axioms with no `sorryAx`, with memory well under the alert. Next I'll register the light modules, run `AxCheckDecide` across the light library, and update the worklog and docs.

The galois-full stage is unstuck and now finished: all 30 weights from 72 to 134 prove that the Galois group of the `T₂` characteristic polynomial is the full `Sₙ`. With the existing dimensions 2–5 results, every level-one weight with `2 ≤ dim S_k ≤ 10` now has both irreducibility and full Galois group for `T₂`.

Nothing is committed or pushed, so all of this is sitting in the working tree of `impl/iteration21/maeda-galois-full`, and GitHub CI hasn't run on it. Your path had a typo: the worktree is at `/home/doz/claude-workdir/worktree/mp1/maeda-galois-full`, with a hyphen.

## Why it was stuck
- **Never compiled:** the uncommitted M3 block (the maximal ideal over `ℓ`) had never been built. It had about 20 errors, some just missing imports showing up as "Unknown constant".
- **Oversized plan:** the worklog still expected 300–400 lines of transport work plus about 10 Modal cycles. Most of that wasn't needed:
  - The reduced roots are distinct simply because the reduction is separable, so no resultant transport.
  - Indexing roots directly by `rootSet ℂ` removes the conjugation packaging.
  - One orbit lemma covers both the `{n−1}` and `{2}` certificates.

## What's new
- **`FrobeniusCycleType.lean`:** Dedekind's theorem in cycle-type form, `frob_cycleType_of_factorization`.
- **`MaedaGaloisFull.lean`:** the generic `Sₙ` assembly and the reflected certificates.
- **`tools/gen_galoisfull.py`:** generates `MaedaGaloisDim{6..10}Weights.lean`, which contain `MaedaWeightK.maeda_galois_full`. It also generates an opt-in audit, `MaedaGaloisFullAxCheck.lean`.
- **Registration and docs:** the light modules are in the lakefile, root import and CI list. I also updated `README.md`, `docs/index.html`, `AGENTS.md`, the research log and the worklog.

## Verification (all on Modal)
| Check | Result |
|---|---|
| Five dimension files | 0 errors, 0 warnings; 65–79 s each, peak ≤ 7.42 GiB on a warm cache, so no memory alert |
| Axioms, all 30 theorems + 3 generic ones | only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| `AxCheckDecide`, whole light library | 589 `decide` certificates, 0 depend on more than `propext` |
| `tauceti_audit.sh`, new or changed modules | no `set_option`, `#eval`, `native_decide` or `sorry` |
| `gen_galoisfull.py --check` | byte-identical |

## Worth knowing
- **Kernel recursion limit:** `RabinCert.zpgcd` overflows the kernel stack around `ℓ ≈ 5·10⁶`, which broke weights 130 and 134. All weights now use Bézout witnesses instead (`irreducible_of_rabin_bezout`), and the limit is recorded in `AGENTS.md`.
- **Blueprint deviations:** it's the `(n−1)`-cycle plus transposition route, with no discriminant step, and the module layout differs slightly. Both are recorded in the worklog.
- **Dead code:** `exists_frobenius_perm` and `resultant_ne_zero_of_linear_mul_irreducible` are now unused. I left them in `FrobeniusCycleType.lean` and noted that in its header, since they're proved work and removing them is your call.
- **Stale tracker:** `research/iteration21/WAVE-TRACKING.md` on `dev/iteration20-maeda-dim6-10` still lists this branch as RUNNING, and the wave-level merge plan hasn't started. I didn't change that branch.
