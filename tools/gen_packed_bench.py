#!/usr/bin/env python3
"""Generate `Bench/Packed/BBenchPacked.lean`: the packed-bignum kernel benchmark
for the Lehmer scaling study.

Computes, fully independently of the Lean side:

  * `eta[d]`  — coefficients of `∏_{m≥1} (1 − x^m)` mod P, truncated at degree
    `< d` (dense, ascending).  Over ℤ these coefficients are in {−1, 0, 1}
    (Euler's pentagonal number theorem), so int64 never overflows during the
    product accumulation.
  * `tau[d]` — residues of the Ramanujan τ function mod P, as coefficients of
    `eta^24` truncated at degree `< d`, computed by numpy convolution with
    15-bit operand splitting (every intermediate is an exact integer < 2^45
    inside float64, reassembled in int64 where sums stay < 2^62).

and cross-checks `tau[0..20]` against the 21 kernel-verified values of τ from
`MathProof/Tau/Basic.lean` before emitting anything.

The generated Lean file asserts `allNonzero (pow24Packed eta_S) = true` by
`decide +kernel` — so even if this script were wrong, a wrong certificate makes
the Lean check FAIL loudly; it cannot produce a false benchmark pass.
"""

import numpy as np

P = 999_999_937
KNOWN_TAU = [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920,
             534612, -370944, -577738, 401856, 1217160, 987136, -6905934,
             2727432, 10661420, -7109760, -4219488]  # τ(1)..τ(21), from Basic.lean


def eta_residues(d: int) -> np.ndarray:
    """Coefficients of ∏_{m≥1}(1 − x^m) mod P, degrees < d, ascending."""
    c = np.zeros(d, dtype=np.int64)
    c[0] = 1
    for m in range(1, d):
        c[m:] -= c[: d - m]  # multiply by (1 − x^m), truncate
    return np.where(c < 0, c % P, c)  # entries in [0, P)


def polymul_mod(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    """Truncated-at-min-len convolution of residue arrays, mod P, exact."""
    k = 1 << 15
    ah, al = a >> 15, a & (k - 1)
    bh, bl = b >> 15, b & (k - 1)

    def conv(x, y):
        # products of 15-bit limbs, <= min(len) < 2^15 terms: sums < 2^45,
        # exactly representable in float64 (exact integers up to 2^53)
        return np.convolve(x.astype(np.float64), y.astype(np.float64)).astype(np.int64)

    full = ((conv(ah, bh) % P) * ((k * k) % P)
            + ((conv(ah, bl) + conv(al, bh)) % P) * k
            + conv(al, bl) % P)  # each term < 2^60, sum < 2^62: int64-safe
    return full[: min(len(a), len(b))] % P


def tau_residues(d: int) -> np.ndarray:
    eta = eta_residues(d).astype(np.int64)
    # eta^24 by binary powering (24 = 16 + 8)
    s2 = polymul_mod(eta, eta)
    s4 = polymul_mod(s2, s2)
    s8 = polymul_mod(s4, s4)
    s16 = polymul_mod(s8, s8)
    return polymul_mod(s16, s8)


def main() -> None:
    import pathlib
    dmax = 65536
    sizes = [1024, 4096, 16384]
    bal_sizes = [16384, dmax]

    tau = tau_residues(dmax)
    ok = all(tau[i] % P == KNOWN_TAU[i] % P for i in range(len(KNOWN_TAU)))
    assert ok, "τ residues disagree with the kernel-verified values of Basic.lean"
    nz = int(np.count_nonzero(tau[:dmax]))
    print(f"τ residues mod P for n ≤ {dmax}: {nz}/{dmax} nonzero; first 21 match Basic.lean ✓")

    # slot-safety bound: raw convolution digit = Σ a_i b_j ≤ min(len)·(P−1)^2 < 2^74 < 2^80
    bound = dmax * (P - 1) ** 2
    assert bound < 1 << 80, f"slot width 80 insufficient: bound=2^{bound.bit_length()}"
    print(f"raw digit bound 2^{bound.bit_length()} < 2^80 (slot width) ✓")

    blocks = []
    for s in sizes:
        eta = eta_residues(s)
        rows = []
        for i in range(0, s, 10):
            rows.append("    " + " ".join(f"{v}," for v in eta[i:i + 10]))
        blocks.append(
            f"/-- Coefficients of `∏ (1 - X ^ m)` mod `P` in degrees `< {s}` (dense, ascending;\n"
            f"pentagonal: ±1 at generalized pentagonal indices, 0 elsewhere).  Data for the\n"
            f"benchmark only — in the sound version this list is built structurally and\n"
            f"certified by Mathlib's pentagonal number theorem. -/\n"
            f"private def eta_{s} : List ℕ := [\n" + "\n".join(rows) + "]\n"
        )

    out = pathlib.Path(__file__).resolve().parents[1] / "Bench/Packed/BBenchPacked.lean"

    # ── balanced variant ────────────────────────────────────────────────────
    # The v1 run measured Θ(d²)-bit retention: the *linear* packAsc/digitsModP
    # recursions keep every intermediate bignum alive in the kernel evaluator's
    # below-spine (≈ 40·d² bits ≈ 20 GB at d = 16384; measured peak 41 GiB for
    # 1024+4096+16384).  The balanced variant splits the list / digit range in
    # half (fuel-structural recursion, depth log₂ d), so retention drops to
    # O(d · log d · 80) bits (~30 MB at 16384) and the design extends to 65536.
    bal_blocks = []
    for s in bal_sizes:
        eta = eta_residues(s)
        rows = []
        for i in range(0, s, 10):
            rows.append("    " + " ".join(f"{v}," for v in eta[i:i + 10]))
        bal_blocks.append(
            f"/-- Coefficients of `∏ (1 - X ^ m)` mod `P`, degrees `< {s}` (see `BBenchPacked.lean`). -/\n"
            f"private def eta_{s} : List ℕ := [\n" + "\n".join(rows) + "]\n\n"
            f"theorem packed_bal_nonvanishing_{s} :\n"
            f"    allNonzero (pow24PackedBal eta_{s}) = true := by\n"
            f"  decide +kernel\n"
        )
    bal_header = """import Mathlib.Tactic

/-!
# Bench: balanced packed-bignum kernel arithmetic  (scaling-study artifact)

Variant of `BBenchPacked.lean` with balanced-tree packing/unpacking.  The linear
recursions of v1 retain every intermediate bignum in the kernel evaluator's
below-spine (Θ(d²) bits; measured peak 41.26 GiB for 1024+4096+16384 together).
Here the list (resp. digit range) is split at its midpoint — fuel-structural,
depth `log₂ d` — so all retained intermediates sum to `O(d · log d)` bits and
the same kernel-only design extends to `d = 65536`.

Also lifts the kernel's deterministic timeout (`deterministicTimeout`), which
is what kills multi-minute `decide +kernel`s at the default setting.
-/

namespace BenchPackedBal

local notation "P" => 999999937

private def twoW : ℕ := 1 <<< 80

/-- Linear pack for short lists (depth ≤ 64: negligible retention). -/
private def packAsc : List ℕ → ℕ
  | [] => 0
  | c :: cs => c + twoW * packAsc cs

private def takeF : ℕ → List ℕ → List ℕ
  | _, [] => []
  | 0, _ => []
  | k + 1, c :: cs => c :: takeF k cs

private def dropF : ℕ → List ℕ → List ℕ
  | 0, l => l
  | _, [] => []
  | k + 1, _ :: cs => dropF k cs

/-- Balanced pack: split at the midpoint, pack halves, combine with one
shift-multiply-add.  `F` is fuel (one per level); 64 levels covers lists of
`2 ^ 64` entries. -/
private def packBal : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | F + 1, l =>
      let n := l.length
      if n ≤ 64 then
        packAsc l
      else
        let h := n / 2
        packBal F (takeF h l) + (1 <<< (80 * h)) * packBal F (dropF h l)

/-- Linear digit extraction for short ranges. -/
private def digitsLin : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, N => (N % twoW % P) :: digitsLin k (N / twoW)

/-- Balanced digit extraction: split the digit range at its midpoint with one
mask + division. -/
private def digitsBal : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | F + 1, k, N =>
      if k ≤ 64 then
        digitsLin k N
      else
        let h := k / 2
        let B := 1 <<< (80 * h)
        digitsBal F h (N % B) ++ digitsBal F (k - h) (N / B)

/-- Truncated mod-`P` product of two ascending lists via one bignum product,
with balanced pack/unpack. -/
private def packedMul (a b : List ℕ) : List ℕ :=
  digitsBal 64 a.length (packBal 64 a * packBal 64 b)

private def pow24PackedBal (l : List ℕ) : List ℕ :=
  let s2 := packedMul l l
  let s4 := packedMul s2 s2
  let s8 := packedMul s4 s4
  let s16 := packedMul s8 s8
  packedMul s16 s8

private def allNonzero : List ℕ → Bool
  | [] => true
  | c :: cs => (c % P != 0) && allNonzero cs

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000 -- lift the kernel's deterministic time cap

"""
    out2 = pathlib.Path(__file__).resolve().parents[1] / "Bench/Packed/BBenchPackedBal.lean"
    bal_body = "\n".join(bal_blocks)
    out2.write_text(bal_header + bal_body + "\nend BenchPackedBal\n")
    print(f"wrote {out2} ({len((bal_header + bal_body).__str__()) // 1024} KB)")
    header = """import Mathlib.Tactic

/-!
# Bench: packed-bignum kernel arithmetic for `Δ` mod `P`  (scaling-study artifact)

Self-contained benchmark for the Lehmer scaling study (`research/lehmer-mod-scaling-study.md`).
Computes the coefficients of `(∏_{m} (1 - X ^ m)) ^ 24` mod `P = 999999937` by
packing each coefficient list into a single bignum in base `2 ^ 80` and letting
the kernel's GMP-backed `Nat.mul` do the dense convolution at C speed:

* one truncated product = 1 bignum multiplication + O(d) digit extractions,
  instead of Θ(d ^ 2) kernel reduction steps over linked lists;
* all data flow is through strict `Nat` binary operations, so the lazy kernel
  evaluator never retains a Θ(d ^ 2) list DAG (the 71 GB failure mode of the
  list-based `LehmerMod` computation at 1024).

This file is a *benchmark*, not a soundness artifact: the entry lists are data
generated by `tools/gen_packed_bench.py`; a wrong list makes the `decide`s fail
rather than pass.  Soundness transport (packing lemmas + pentagonal theorem) is
the follow-up iteration described in the study.
-/

namespace BenchPacked

local notation "P" => 999999937

/-- Slot base: `2 ^ 80`.  Raw convolution digits are at most `d · (P-1) ^ 2 < 2 ^ 74`
for `d ≤ 2 ^ 14`, so digits never bleed into each other. -/
private def twoW : ℕ := 1 <<< 80

/-- Ascending coefficient list (entries `< P`) packed into one bignum, base `twoW`. -/
private def packAsc : List ℕ → ℕ
  | [] => 0
  | c :: cs => c + twoW * packAsc cs

/-- First `k` base-`twoW` digits of a bignum, each reduced mod `P` (ascending). -/
private def digitsModP : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, N => (N % twoW % P) :: digitsModP k (N / twoW)

/-- Truncated mod-`P` product of two ascending lists via a single bignum product. -/
private def packedMul (a b : List ℕ) : List ℕ :=
  digitsModP a.length (packAsc a * packAsc b)

/-- 24th power by binary powering (`24 = 16 + 8`): 5 packed products. -/
private def pow24Packed (l : List ℕ) : List ℕ :=
  let s2 := packedMul l l
  let s4 := packedMul s2 s2
  let s8 := packedMul s4 s4
  let s16 := packedMul s8 s8
  packedMul s16 s8

private def allNonzero : List ℕ → Bool
  | [] => true
  | c :: cs => (c % P != 0) && allNonzero cs

set_option maxRecDepth 1000000 -- kernel evaluation depth for the checks below
set_option maxHeartbeats 8000000 -- kernel deterministic-time cap (default 200000)

"""
    body = ""
    for s, blk in zip(sizes, blocks):
        body += blk + f"""
theorem packed_nonvanishing_{s} :
    allNonzero (pow24Packed eta_{s}) = true := by
  decide +kernel

"""
    out.write_text(header + body + "end BenchPacked\n")
    print(f"wrote {out} ({(header + body).__len__() // 1024} KB)")


if __name__ == "__main__":
    main()
