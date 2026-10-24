# LehmerPacked.lean — iteration 6 working notes (in progress)

Goal: `tau_ne_zero_of_le_16384` (then 65536 with 64 GiB, user-authorized).
File: `MathProof/Tau/LehmerPacked.lean`. Status: computational skeleton DONE and
Modal-verified (both smoke checks pass: 16 pentagonal residues correct,
end-to-end packed compute at 512 true, 4 s). Proofs: in progress, some `sorry`.

## Design (validated)

- `etaList d = (List.range d).map pentRes`; `pentRes i` decides pentagonality by
  `24i+1 = (6k∓1)²` using `isqrtNew` (own fuel-structural Newton; core `Nat.sqrt`
  is well-founded = kernel-irreducible, must NOT appear in executable defs).
  Start guess/fuel 2048 valid for i ≤ 174762 (covers 65536).
- Packing: `packAsc`/`packBal` (fuel-structural; base case `| 0, l => packAsc l`
  makes `packBal F l = packAsc l` unconditional), `digitsLin`/`digitsBal`
  (base `| 0, k, N => digitsLin k N`), `packedMul`, `pow24Packed` (5 muls), `allNonzero`.
- Slot bound: conv digit < d·(P−1)² < 2^76 < 2^80 for d ≤ 65536. twoW = 1 <<< 80.

## Proof plan / lemma stack (order)

Part 1 isqrt (WRITTEN, iterating):
- `two_mul_le g s : g*(2*s) ≤ s*s + g*g` (parabola; via rcases + ring identities as omega atoms)
- `isqrt_step_ge`, `isqrtNew_spec` (invariant: sqrt n ≤ g; stop ⟺ q ≥ g ⟺ g² ≤ n),
  `isqrtNew_eq_sqrt` (N ≤ 2048²)

Part 2 pentRes (WRITTEN partially, sorries at pentRes_of_pent cases / zero_of_not / eq):
- `pent_ofNat jj : pentagonal (jj:ℤ) = jj*(3*jj-1)/2`, `pent_negNat` (via pentagonal_def/neg
  + Int.toNat_of_nonneg + Nat.cast_div)
- `sq24_a/b`, `sqrt24_a/b` (quadratic identities; `linear_combination 12 * half_exact …`;
  NOTE: linear_combination is a TACTIC — needs `by`)
- `jj_le/jj_le'` (jj < 342 when pent ≤ 174762; via Nat.mul_le_mul monotonicity + omega atoms)
- `pentRes_of_pent k : pentRes (pentagonal k) = if 2 ∣ k then 1 else P-1`
  (match k: 0 / (jj+1 : ℕ) / Int.negSucc jj; rewrite isqrt via sqrt24; branches fire with
  (6jj)%6=0 by Nat.mod_eq_zero_of_dvd ⟨jj, by ring⟩, (6jj)/6 = jj by Nat.mul_div_cancel_left)
- `pentRes_zero_of_not` (s²=24i+1 ∧ s%6∈{1,5} ⟹ construct k; `Nat.mul_mod s s 6` + interval
  reasoning via omega; 24i = (6jj∓1)²−1 = 12·jj(3jj∓1) via `ring`, then 2i = … by omega)
- `pentRes_eq i (hi : i ≤ 174762) : ((pentRes i : ℕ) : ZMod P) = (pentagonalSeries ℤ).coeff i`
  (by_cases ∃ k; `Int.negOnePow_even/odd` + `even_iff_two_dvd`; Int.natCast_dvd_natCast is
  norm_cast for 2 ∣ (jj:ℤ) ↔ 2 ∣ jj)

Part 3 packing (IN PROGRESS in /tmp/parts/parts.lean):
- `digitsLin_length`, `digitsLin_getD` (∧ via Nat.div_div_eq_div_mul), `digitsLin_app`
  (h+m split), `digitsBal_eq` (unconditional, by div_add_mod: k/2 + (k−k/2) = k)
- `packAsc_take_drop (i ≤ length) : packAsc l = packAsc (takeF i l) + twoW^i * packAsc (dropF i l)`
- `packAsc_lt : (∀ e, l.getD e 0 < twoW) → packAsc l < twoW ^ l.length`
- `getD_dropF`, `digit_extract : (packAsc l / twoW^i) % twoW = l.getD i 0` for i < length
  (uses Nat.add_mul_mod_self_left : (a + b*n) % b = a % b)
- convL (pscale0/padd0/convL, proof-only): `packAsc_pscale0`, `packAsc_padd0`,
  `packAsc_convL : packAsc (convL a b) = packAsc a * packAsc b`,
  `getD_padd0`, `getD_pscale0`, `convL_getD : (convL a b).getD i 0 =
  ∑ j ∈ range (i+1), a.getD j 0 * b.getD (i-j) 0` (Finset.sum_range_succ' split)
- `packBal_eq : packBal F l = packAsc l` (via packAsc_take_drop)
- `convSum_lt (k < a.length ≤ 65536, entries < P) : ∑ < twoW` (Finset.sum_le_sum + sum_const
  + card_range; 65536·999999936² < 2^80 by norm_num/decide)
- `packedMul_getD (i < a.length): ((packedMul a b).getD i 0 : ZMod P) = ((L2PMod a)*(L2PMod b)).coeff i`
  (digitsBal_eq + digit_extract on convL + Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
  to match Polynomial.coeff_mul)
- `L2PMod_packedMul` + pow24 chain mirroring LehmerMod's L2PMod_pmulM/pow24M/coeff_pow_congr'

Part 4 bridge (NOT WRITTEN):
- `coeff_one_sub_mul (f : ℤ⟦X⟧) (i < m+1) : coeff i (f * (1 - X^(m+1))) = coeff i f`
  (PowerSeries.coeff_mul + mirror Basic.lean coeff_mul_one_sub_pow24's sum_eq_single)
- `etaPoly_coeff_pent (i < N) : (etaPoly N).coeff i = (pentagonalSeries ℤ).coeff i`:
  (↑(etaPoly N)) = ∏ range N via Polynomial.coeToPowerSeries.ringHom + map_prod +
  PowerSeries.coeff_coe; extract from `coeff_prod_one_sub_X_pow_eventually_eq (R := ℤ) i`
  via `Filter.eventually_atTop` (atTop on Finset ℕ = ⊇-order: s ≥ t ↔ t ⊆ s); take
  M := max (t.sup id + 1) (i+1), t ⊆ range M via Finset.le_sup; stability for arbitrary N.

Part 5 assembly (NOT WRITTEN): L2PMod/cast_modP/coeff_L2PMod/etaPolyMod/coeff_pow_congr'
copies from LehmerMod (private there); `deltaCoeffsPacked_eq (d ≤ 65536) (i < d)`;
allNonzero lemma; `set_option maxHeartbeats 8000000 in` (SCOPED, linter bans file-wide)
before each decide; theorems at 16384 (+65536, needs lean_check memory → 65536 MiB).

## Confirmed API names

Nat.sqrt: `Nat.sqrt_le` (s*s ≤ n), `Nat.lt_succ_sqrt`, `Nat.le_sqrt` (iff m*m ≤ n),
`Nat.sqrt_le_sqrt`, `Nat.sqrt_eq : sqrt (n*n) = n`, `Nat.sqrt_eq'`, `Nat.sqrt_pos`.
Core Nat: `Nat.mul_mod a b n`, `Nat.le_div_iff_mul_le (k0) : x ≤ y/k ↔ x*k ≤ y`,
`Nat.mul_sub`, `Nat.div_div_eq_div_mul`, `Nat.mul_div_cancel_left`, `Nat.mod_eq_zero_of_dvd`,
`Nat.add_mul_mod_self_left`, `Nat.div_add_mod`, `Nat.mul_le_mul`, `Nat.lt_or_ge`,
`Nat.dvd_iff_mod_eq_zero`, `Nat.cast_div`.
Int/parity: `Int.natCast_dvd_natCast` (norm_cast), `Int.negOnePow_even/odd`,
`even_iff_two_dvd`, `Int.mul_nonneg`.
Pentagonal: `pentagonal_def`, `pentagonal_neg`, `pentagonal_injective`,
`coeff_pentagonalSeries_pentagonal` (@[simp], ℤˣ-valued), `coeff_pentagonalSeries_eq_zero`,
`coeff_prod_one_sub_X_pow_eventually_eq` (Finset-atTop, topology-free).
PowerSeries: `PowerSeries.coeff_coe : coeff n (φ : R⟦X⟧) = φ.coeff n`,
`Polynomial.coeToPowerSeries.ringHom` (+`ringHom_apply`), `PowerSeries.coeff_mul`,
`coeff_X_pow`.
Finset: `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk : ∑ ij ∈ antidiagonal n, f ij =
∑ k ∈ range n.succ, f (k, n-k)`, `Finset.sum_range_succ'`, `Finset.le_sup`, `Finset.sum_le_sum`.
Filter: `Filter.eventually_atTop : (∀ᶠ x in atTop, p x) ↔ ∃ b, ∀ x ≥ b, p x`.

## Gotchas learned (update 2)

- **omega does NOT abstract nonlinear-sum atoms** like `(g+t)*(g+t)` or `g*(2*s)`:
  hypotheses containing them are DROPPED. For parabola/AM-GM facts use
  `nlinarith [sq_nonneg x]`, or route through ℤ (`positivity` + `ring` identity +
  `exact_mod_cast`). Better: state intermediate facts as ADDITIVE ring identities
  (`have key : A + B = C + D := by ring`) and finish with omega ONLY when all atoms
  are simple variables or plain `a * b` products (those it does abstract).
- `omega` drops `n / g` (variable divisor) hypotheses: convert first via
  `Nat.le_div_iff_mul_le`/`Nat.mul_div_le` into variable-free-divisor facts.
- Prefer `obtain ⟨t, rfl⟩ : ∃ t, s = g + t := ⟨s - g, by omega⟩` over `set`+`rw`
  (set-variables interact badly with rw of the defining equation).
- pent_ofNat shape that works: hcast : ((jj:ℤ)*(3*(jj:ℤ)−1)) = ((jj*(3*jj−1):ℕ):ℤ)
  (push_cast; ring), then Int.toNat_of_nonneg (rw hnn TWICE — toNat and the value),
  then Nat.cast_div, then push_cast; ring.

## Remaining errors at last compile (17, file as of this session)

- two_mul_le (140/144): replace final omega with `nlinarith [sq_nonneg t]` /
  ℤ-mediated AM-GM (see gotcha above).
- isqrt_step_ge (167–179): restructure parabola via AM-GM `(g+u)² ≥ 4gu` (ℤ route);
  `Nat.le_div_iff_mul_le` for all div steps; no omega over `n / g`.
- isqrtNew_spec (195): `(by omega)` on `g*2 ≤ g + n/g` shape — use explicit
  le_div/mp chain.
- pentRes_of_pent / pentRes_zero_of_not / pentRes_eq: still `sorry` (proofs sketched
  in plan above; sub-free sq24_a'/b' + sqrt24_a/b now DONE and compile).
- digitsLin_getD (301/303): `ih (N / twoW) h1` argument mismatch — check generated
  ih shape (induction over k generalizing N — ih takes N implicitly?).
- digitsLin_app (309+): `intro h; induction h` WITHOUT `generalizing` (m, N are
  ∀-bound in the statement); case bodies per the corrected induction (see above).
- packedMul_getD + `private def L2PMod` placeholder: replace with real def + proofs.

## Gotchas learned

- `set_option maxHeartbeats` must be per-declaration (`... in example`), file-wide banned.
- Doc comments can't attach after `set_option ... in` — use `--` comments there.
- `linear_combination` is tactic-only.
- nlinarith on ℕ with `-` is fragile: restate with `ring`-provable identities as omega atoms.
- omega abstracts nonlinear products as atoms — provide ring identities as `have` then omega.
- Local `lake env lean FILE` works (~3.5 min, I/O-bound import; batch-verify whole file);
  Modal for kernel decides. Modal check cmd:
  `/home/doz/dozenv/bin/modal run lean_check.py --file MathProof/Tau/LehmerPacked.lean --target MathProof.Tau.LehmerPacked`
- The 65536 decide needs lean_check.py `memory=32768` → `65536` (user-authorized).
