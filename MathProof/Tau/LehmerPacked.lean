import MathProof.Tau.Basic
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries

/-!
# Lehmer's conjecture via packed-bignum kernel arithmetic

Iteration 6.  Raises the kernel-verified nonvanishing bound for the Ramanujan
τ function by computing the coefficients of `Δ = q ∏ (1 - q ^ m) ^ 24` mod
`P = 999999937` with **packed-bignum arithmetic**: each coefficient list is
packed into a single `Nat` in base `2 ^ 80`, so every dense polynomial
multiplication is one GMP-backed `Nat.mul` plus O(d) digit extractions —
O(d) kernel big-operations instead of Θ(d ^ 2) list-cell reduction steps
(see `research/lehmer-mod-scaling-study.md`).

* Entry list: `Ramanujan.etaList d` — the coefficients of `∏ (1 - X ^ m)` mod
  `P` (Euler's pentagonal number theorem: ±1 at generalized pentagonal
  indices, 0 elsewhere), computed per index by an integer square root test
  `24 i + 1 = (6 k ± 1) ^ 2` with a structurally-recursive Newton iterator
  (the core `Nat.sqrt` is well-founded and *not* kernel-reducible).
* Entry soundness: `Ramanujan.pentRes_eq` — each entry is the reduction mod
  `P` of the corresponding coefficient of Mathlib's `pentagonalSeries ℤ`.
* Packing soundness: `Ramanujan.deltaPacked_eq` — for `i < d ≤ 2 ^ 16`, the
  packed 24th power's entries are the coefficients of `(etaPoly d) ^ 24`
  reduced mod `P`, by (a) packing lemmas (digits of a product are its
  convolutions, given the slot bound `d · (P - 1) ^ 2 < 2 ^ 80`), and
  (b) Mathlib's pentagonal number theorem
  (`PowerSeries.coeff_pentagonalSeries_pentagonal`).
* `Ramanujan.tau_ne_zero_of_le_16384` and `Ramanujan.tau_ne_zero_of_le_65536`:
  `τ n ≠ 0` for all `1 ≤ n ≤ 65536`, verified by `decide +kernel` inside
  Lean's kernel alone (no `native_decide`, no external CAS).  The 16384
  decide needs ~18 GiB and the 65536 one ~60 GiB of kernel heap, so this
  module is built on Modal, never in CI.
-/

namespace Ramanujan

local notation "P" => 999999937

local instance : NeZero 999999937 := ⟨by norm_num⟩

open Polynomial

/-! ### Packed-bignum arithmetic (kernel-friendly) -/

/-- Slot base `2 ^ 80`.  Raw convolution digits are `< d · (P - 1) ^ 2 < 2 ^ 76`
for `d ≤ 2 ^ 16`, so digits never bleed into each other. -/
private def twoW : ℕ := 1 <<< 80

private def takeF : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | _, [] => []
  | k + 1, c :: cs => c :: takeF k cs

private def dropF : ℕ → List ℕ → List ℕ
  | 0, l => l
  | _, [] => []
  | k + 1, _ :: cs => dropF k cs

/-- Ascending coefficient list packed into one bignum, base `twoW`. -/
private def packAsc : List ℕ → ℕ
  | [] => 0
  | c :: cs => c + twoW * packAsc cs

/-- Balanced pack: split at the midpoint (fuel-structural, depth `log₂`).
`F` is fuel; `2 ^ F` bounds the list length. -/
private def packBal : ℕ → List ℕ → ℕ
  | 0, l => packAsc l
  | F + 1, l =>
      let n := l.length
      if n ≤ 64 then
        packAsc l
      else
        let h := n / 2
        packBal F (takeF h l) + (1 <<< (80 * h)) * packBal F (dropF h l)

/-- First `k` base-`twoW` digits of `N`, reduced mod `P` (ascending). -/
private def digitsLin : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, N => (N % twoW % P) :: digitsLin k (N / twoW)

/-- Balanced digit extraction (fuel-structural). -/
private def digitsBal : ℕ → ℕ → ℕ → List ℕ
  | 0, k, N => digitsLin k N
  | F + 1, k, N =>
      if k ≤ 64 then
        digitsLin k N
      else
        let h := k / 2
        let B := 1 <<< (80 * h)
        digitsBal F h (N % B) ++ digitsBal F (k - h) (N / B)

/-- Truncated mod-`P` product of two ascending lists via one bignum product. -/
private def packedMul (a b : List ℕ) : List ℕ :=
  digitsBal 64 a.length (packBal 64 a * packBal 64 b)

/-- 24th power by binary powering (`24 = 16 + 8`): five packed products. -/
private def pow24Packed (l : List ℕ) : List ℕ :=
  let s2 := packedMul l l
  let s4 := packedMul s2 s2
  let s8 := packedMul s4 s4
  let s16 := packedMul s8 s8
  packedMul s16 s8

private def allNonzero : List ℕ → Bool
  | [] => true
  | c :: cs => (c % P != 0) && allNonzero cs

/-! ### The pentagonal entry list -/

/-- Newton iteration for the integer square root (structural on fuel; unlike
the well-founded core `Nat.sqrt`, the kernel can reduce it).  Invariant: with
`0 < g`, `Nat.sqrt n ≤ g`, and `g ≤ f`, the result is `Nat.sqrt n`. -/
private def isqrtNew : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | f + 1, n, g =>
      let next := (g + n / g) / 2
      if next < g then isqrtNew f n next else g

/-- `2 ^ 11`; `isqrtNew 2048 N 2048` is valid for all `N ≤ 2048 ^ 2`, i.e.
all `d ≤ 174762` in `pentRes`. -/
private def sqrtGuess : ℕ := 2048

/-- Residue mod `P` of the `i`-th coefficient of `∏ (1 - X ^ m)` (Euler):
`(PowerSeries.pentagonalSeries ℤ).coeff i ∈ {0, 1, -1}`, decided by the square test
`24 i + 1 = (6 k ± 1) ^ 2`. -/
private def pentRes (i : ℕ) : ℕ :=
  let N := 24 * i + 1
  let s := isqrtNew sqrtGuess N sqrtGuess
  if s * s == N then
    if (s + 1) % 6 == 0 then
      if (s + 1) / 6 % 2 == 0 then 1 else P - 1
    else if s < 1 then 0
    else if (s - 1) % 6 == 0 then
      if (s - 1) / 6 % 2 == 0 then 1 else P - 1
      else 0
  else 0

/-- The coefficients of `∏_{m ≥ 1} (1 - X ^ m)` mod `P`, degrees `< d`. -/
def etaList (d : ℕ) : List ℕ := (List.range d).map pentRes

/-! ### The Newton iterator computes `Nat.sqrt` -/

private theorem twoW_pos : 0 < twoW := by norm_num [twoW]

private theorem twoW_pow (h : ℕ) : twoW ^ h = 1 <<< (80 * h) := by
  simp [twoW, Nat.one_shiftLeft, pow_mul]

private theorem twoW_pow_mono : ∀ (a b : ℕ), a ≤ b → twoW ^ a ≤ twoW ^ b := by
  intro a b h
  induction b with
  | zero =>
      have : a = 0 := by omega
      subst this
      exact le_refl _
  | succ b ih =>
      by_cases h' : a ≤ b
      · exact le_trans (ih h')
          (le_trans (Nat.le_mul_of_pos_right _ twoW_pos) (pow_succ twoW b).symm.le)
      · have : a = b + 1 := by omega
        subst this
        exact le_refl _

private theorem even_prod_a2 (jj : ℕ) : (jj + 1) * (3 * jj + 2) % 2 = 0 := by
  rcases Nat.even_or_odd jj with h | h
  · obtain ⟨m, rfl⟩ := h
    have hE : (m + m + 1) * (3 * (m + m) + 2) = 2 * ((m + m + 1) * (3 * m + 1)) := by ring
    rw [hE, Nat.mul_mod_right]
  · obtain ⟨m, rfl⟩ := h
    have hE : (2 * m + 1 + 1) * (3 * (2 * m + 1) + 2)
        = 2 * ((m + 1) * (3 * (2 * m + 1) + 2)) := by ring
    rw [hE, Nat.mul_mod_right]

private theorem even_prod_b2 (jj : ℕ) : (jj + 1) * (3 * jj + 4) % 2 = 0 := by
  rcases Nat.even_or_odd jj with h | h
  · obtain ⟨m, rfl⟩ := h
    have hE : (m + m + 1) * (3 * (m + m) + 4) = 2 * ((m + m + 1) * (3 * m + 2)) := by ring
    rw [hE, Nat.mul_mod_right]
  · obtain ⟨m, rfl⟩ := h
    have hE : (2 * m + 1 + 1) * (3 * (2 * m + 1) + 4)
        = 2 * ((m + 1) * (3 * (2 * m + 1) + 4)) := by ring
    rw [hE, Nat.mul_mod_right]

private theorem half_exact (n : ℕ) (h : n % 2 = 0) : 2 * (n / 2) = n := by omega

private theorem two_mul_le (g s : ℕ) : g * (2 * s) ≤ s * s + g * g := by
  rcases Nat.lt_or_ge g s with hlt | hge
  · obtain ⟨t, rfl⟩ : ∃ t, s = g + t := ⟨s - g, by omega⟩
    have h1 : (g + t) * (g + t) = g * g + 2 * (g * t) + t * t := by ring
    have h2 : g * (2 * (g + t)) = 2 * (g * g) + 2 * (g * t) := by ring
    omega
  · obtain ⟨u, rfl⟩ : ∃ u, g = s + u := ⟨g - s, by omega⟩
    have h1 : (s + u) * (s + u) = s * s + 2 * (s * u) + u * u := by ring
    have h2 : (s + u) * (2 * s) = 2 * (s * s) + 2 * (s * u) := by ring
    omega

/-- Newton's step never drops below `Nat.sqrt n` while `g ≤ 2 * Nat.sqrt n`. -/
private theorem isqrt_step_ge (n g : ℕ) (hpos : 0 < g) (_hg : Nat.sqrt n ≤ g)
    (hle : g ≤ 2 * Nat.sqrt n) : Nat.sqrt n ≤ (g + n / g) / 2 := by
  obtain ⟨u, hu⟩ : ∃ u, g + u = 2 * Nat.sqrt n := ⟨2 * Nat.sqrt n - g, by omega⟩
  -- parabola `g * u ≤ s ^ 2` via `2 g s ≤ s ^ 2 + g ^ 2` with `2 s = g + u`
  have hpara : g * (2 * Nat.sqrt n) ≤ Nat.sqrt n * Nat.sqrt n + g * g :=
    two_mul_le g _
  have hid : g * (2 * Nat.sqrt n) = g * g + g * u := by rw [← hu]; ring
  rw [hid] at hpara
  have hgu : g * u ≤ Nat.sqrt n * Nat.sqrt n := by omega
  have hgu2 : u * g ≤ n := by
    rw [Nat.mul_comm]
    exact Nat.le_trans hgu (Nat.sqrt_le n)
  have hudiv : u ≤ n / g := (Nat.le_div_iff_mul_le hpos).mpr hgu2
  have hfin : Nat.sqrt n * 2 ≤ g + n / g :=
    calc Nat.sqrt n * 2 = g + u := by omega
      _ ≤ g + n / g := Nat.add_le_add_left hudiv g
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr hfin

private theorem isqrtNew_spec : ∀ (f n g : ℕ), 0 < n → Nat.sqrt n ≤ g → g ≤ f →
    isqrtNew f n g = Nat.sqrt n := by
  intro f
  induction f with
  | zero =>
      intro n g hn hg hf
      have h1 : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
      show g = Nat.sqrt n
      omega
  | succ f ih =>
      intro n g hn hg hf
      have hspos : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
      have hpos : 0 < g := Nat.lt_of_lt_of_le hspos hg
      by_cases hstep : (g + n / g) / 2 < g
      · simp only [isqrtNew, if_pos hstep]
        have hge : Nat.sqrt n ≤ (g + n / g) / 2 := by
          rcases Nat.lt_or_ge g (2 * Nat.sqrt n) with hlt | hge
          · exact isqrt_step_ge n g hpos hg (le_of_lt hlt)
          · have h1 : Nat.sqrt n ≤ g / 2 :=
              (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
            exact le_trans h1 (Nat.div_le_div_right (Nat.le_add_right g (n / g)))
        exact ih n ((g + n / g) / 2) hn hge (by omega)
      · have h2 : g ≤ (g + n / g) / 2 := le_of_not_gt hstep
        have h3 : g * 2 ≤ g + n / g := (Nat.le_div_iff_mul_le (by norm_num)).mp h2
        have h4 : g ≤ n / g := by omega
        have hgg : g * g ≤ n := (Nat.le_div_iff_mul_le hpos).mp h4
        simp only [isqrtNew, if_neg hstep]
        exact le_antisymm (Nat.le_sqrt.mpr hgg) hg

private theorem isqrtNew_eq_sqrt {N : ℕ} (hN : 0 < N) (hN' : N ≤ sqrtGuess * sqrtGuess) :
    isqrtNew sqrtGuess N sqrtGuess = Nat.sqrt N := by
  have hle : Nat.sqrt N ≤ sqrtGuess := by
    have h := Nat.sqrt_le_sqrt hN'
    rwa [Nat.sqrt_eq sqrtGuess] at h
  exact isqrtNew_spec sqrtGuess N sqrtGuess hN hle (le_refl _)

private theorem sqrt_bound_174762 {i : ℕ} (hi : i ≤ 174762) :
    24 * i + 1 ≤ sqrtGuess * sqrtGuess := by
  have hsq : sqrtGuess * sqrtGuess = 4194304 := by norm_num [sqrtGuess]
  omega

/-! ### The pentagonal entries -/

private theorem pent_ofNat (jj : ℕ) :
    pentagonal (((jj + 1 : ℕ) : ℤ)) = (jj + 1) * (3 * jj + 2) / 2 := by
  have hT := two_mul_natCast_pentagonal (((jj + 1 : ℕ) : ℤ))
  have hE : ((jj + 1 : ℕ) : ℤ) * (3 * ((jj + 1 : ℕ) : ℤ) - 1)
      = (((jj + 1) * (3 * jj + 2) : ℕ) : ℤ) := by push_cast; ring
  rw [hE] at hT
  have hP2Y : (jj + 1) * (3 * jj + 2) = 2 * pentagonal (((jj + 1 : ℕ) : ℤ)) := by
    apply Nat.cast_injective (R := ℤ)
    omega
  rw [hP2Y, Nat.mul_div_cancel_left _ (by norm_num)]

private theorem pent_negSucc (jj : ℕ) :
    pentagonal (Int.negSucc jj) = (jj + 1) * (3 * jj + 4) / 2 := by
  rw [show Int.negSucc jj = -(((jj + 1 : ℕ) : ℤ)) from by omega]
  have hT := two_mul_natCast_pentagonal_neg (((jj + 1 : ℕ) : ℤ))
  have hE : ((jj + 1 : ℕ) : ℤ) * (3 * ((jj + 1 : ℕ) : ℤ) + 1)
      = (((jj + 1) * (3 * jj + 4) : ℕ) : ℤ) := by push_cast; ring
  rw [hE] at hT
  have hP2Y : (jj + 1) * (3 * jj + 4) = 2 * pentagonal (-(((jj + 1 : ℕ) : ℤ))) := by
    apply Nat.cast_injective (R := ℤ)
    omega
  rw [hP2Y, Nat.mul_div_cancel_left _ (by norm_num)]

/-- Quadratic identities, stated sub-free by splitting `k = k' + 1`. -/
private theorem sq24_a' (k' : ℕ) :
    24 * ((k' + 1) * (3 * k' + 2) / 2) + 1 = (6 * k' + 5) * (6 * k' + 5) := by
  have hE : 2 * ((k' + 1) * (3 * k' + 2) / 2) = (k' + 1) * (3 * k' + 2) :=
    half_exact _ (even_prod_a2 k')
  linear_combination 12 * hE

private theorem sq24_b' (k' : ℕ) :
    24 * ((k' + 1) * (3 * k' + 4) / 2) + 1 = (6 * k' + 7) * (6 * k' + 7) := by
  have hE : 2 * ((k' + 1) * (3 * k' + 4) / 2) = (k' + 1) * (3 * k' + 4) :=
    half_exact _ (even_prod_b2 k')
  linear_combination 12 * hE

private theorem sqrt24_a' (k' : ℕ) :
    Nat.sqrt (24 * ((k' + 1) * (3 * k' + 2) / 2) + 1) = 6 * k' + 5 := by
  rw [sq24_a', Nat.sqrt_eq]

private theorem sqrt24_b' (k' : ℕ) :
    Nat.sqrt (24 * ((k' + 1) * (3 * k' + 4) / 2) + 1) = 6 * k' + 7 := by
  rw [sq24_b', Nat.sqrt_eq]

/-- One-step unfolding of `pentRes` into an explicit decision tree on
`Nat.sqrt (24 * i + 1)`; valid whenever the Newton iterator computes the
root (`24 * i + 1 ≤ 2048 ^ 2`, i.e. `i ≤ 174762`). -/
private theorem pentRes_unfold (i : ℕ) (hi : i ≤ 174762) : pentRes i =
    (if Nat.sqrt (24 * i + 1) * Nat.sqrt (24 * i + 1) = 24 * i + 1 then
      (if (Nat.sqrt (24 * i + 1) + 1) % 6 = 0 then
        (if (Nat.sqrt (24 * i + 1) + 1) / 6 % 2 = 0 then 1 else P - 1)
      else if Nat.sqrt (24 * i + 1) < 1 then 0
      else if (Nat.sqrt (24 * i + 1) - 1) % 6 = 0 then
        (if (Nat.sqrt (24 * i + 1) - 1) / 6 % 2 = 0 then 1 else P - 1)
      else 0)
    else 0) := by
  have hpos : 0 < 24 * i + 1 := by omega
  simp only [pentRes, isqrtNew_eq_sqrt hpos (sqrt_bound_174762 hi), beq_iff_eq]

/-- Every `pentRes` value is a legitimate residue: `0`, `1`, or `P - 1`. -/
private theorem pentRes_lt (i : ℕ) : pentRes i < P := by
  simp only [pentRes]
  split_ifs <;> omega

private theorem div24_cancel {i v : ℕ} (h : 24 * i + 1 = 24 * v + 1) : i = v := by omega

private theorem pentRes_of_pent (k : ℤ) (hbd : pentagonal k ≤ 174762) :
    pentRes (pentagonal k) = if 2 ∣ k then 1 else P - 1 := by
  match k with
  | (0 : ℕ) =>
      rw [if_pos (by norm_num : (2:ℤ) ∣ ((0:ℕ):ℤ)),
        show pentagonal ((0 : ℕ) : ℤ) = 0 from by rw [pentagonal_def]; norm_num]
      decide
  | (jj + 1 : ℕ) =>
      have hi174 : (jj + 1) * (3 * jj + 2) / 2 ≤ 174762 := by
        rw [← pent_ofNat jj]; exact hbd
      rw [pent_ofNat jj, pentRes_unfold _ hi174]
      have hs := sqrt24_a' jj
      have hsq := sq24_a' jj
      rw [hs, if_pos hsq.symm]
      have h6a : 6 * jj + 5 + 1 = 6 * (jj + 1) := by omega
      rw [h6a, Nat.mul_mod_right, if_pos (rfl : (0:ℕ) = 0),
        Nat.mul_div_cancel_left _ (by norm_num)]
      by_cases hpar : (jj + 1) % 2 = 0
      · have hdvd : (2:ℤ) ∣ (((jj + 1 : ℕ) : ℤ)) := by
          obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hpar
          exact ⟨(m : ℤ), by omega⟩
        rw [hpar, if_pos (rfl : (0:ℕ) = 0), if_pos hdvd]
      · have h1m : (jj + 1) % 2 = 1 := by omega
        have hne : (2:ℤ) ∣ (((jj + 1 : ℕ) : ℤ)) → False := by
          intro hcon
          obtain ⟨t, ht⟩ := hcon
          omega
        rw [h1m, if_neg (by norm_num : (1:ℕ) ≠ 0), if_neg hne]
  | Int.negSucc jj =>
      have hi174 : (jj + 1) * (3 * jj + 4) / 2 ≤ 174762 := by
        rw [← pent_negSucc jj]; exact hbd
      rw [pent_negSucc jj, pentRes_unfold _ hi174]
      have hs := sqrt24_b' jj
      have hsq := sq24_b' jj
      rw [hs, if_pos hsq.symm]
      have h6a : (6 * jj + 7 + 1) % 6 = 2 := by omega
      rw [h6a, if_neg (by norm_num : (2:ℕ) ≠ 0),
        if_neg (by omega : ¬ 6 * jj + 7 < 1)]
      have h6b : 6 * jj + 7 - 1 = 6 * (jj + 1) := by omega
      rw [h6b, Nat.mul_mod_right, if_pos (rfl : (0:ℕ) = 0),
        Nat.mul_div_cancel_left _ (by norm_num)]
      by_cases hpar : (jj + 1) % 2 = 0
      · have hdvd : (2:ℤ) ∣ (Int.negSucc jj) := by
          obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hpar
          refine ⟨(-(m : ℤ)), ?_⟩
          omega
        rw [hpar, if_pos (rfl : (0:ℕ) = 0), if_pos hdvd]
      · have hne : (2:ℤ) ∣ (Int.negSucc jj) → False := by
          intro hcon
          obtain ⟨t, ht⟩ := hcon
          have h2 : (jj + 1) % 2 = 1 := by omega
          omega
        have h1m : (jj + 1) % 2 = 1 := by omega
        rw [h1m, if_neg (by norm_num : (1:ℕ) ≠ 0), if_neg hne]

private theorem pentRes_zero_of_not (i : ℕ) (hi : i ≤ 174762)
    (h : ∀ k : ℤ, pentagonal k ≠ i) : pentRes i = 0 := by
  rw [pentRes_unfold i hi]
  by_cases hs : Nat.sqrt (24 * i + 1) * Nat.sqrt (24 * i + 1) = 24 * i + 1
  · rw [if_pos hs]
    by_cases h6a : (Nat.sqrt (24 * i + 1) + 1) % 6 = 0
    · exfalso
      have h6d : Nat.sqrt (24 * i + 1) + 1 = 6 * ((Nat.sqrt (24 * i + 1) + 1) / 6) := by
        have hd := Nat.div_add_mod (Nat.sqrt (24 * i + 1) + 1) 6
        omega
      obtain ⟨m, hm⟩ : ∃ m, Nat.sqrt (24 * i + 1) = 6 * m + 5 :=
        ⟨((Nat.sqrt (24 * i + 1) + 1) / 6) - 1, by omega⟩
      have hiv : i = (m + 1) * (3 * m + 2) / 2 := by
        have hsq := sq24_a' m
        rw [hm] at hs
        exact div24_cancel (hs.symm.trans hsq.symm)
      exact h (((m + 1 : ℕ) : ℤ)) (by rw [pent_ofNat m, hiv])
    · rw [if_neg h6a]
      by_cases h1 : Nat.sqrt (24 * i + 1) < 1
      · rw [if_pos h1]
      · rw [if_neg h1]
        by_cases h6b : (Nat.sqrt (24 * i + 1) - 1) % 6 = 0
        · exfalso
          have h6d : Nat.sqrt (24 * i + 1) - 1 = 6 * ((Nat.sqrt (24 * i + 1) - 1) / 6) := by
            have hd := Nat.div_add_mod (Nat.sqrt (24 * i + 1) - 1) 6
            omega
          by_cases hq : (Nat.sqrt (24 * i + 1) - 1) / 6 = 0
          · have hs1 : Nat.sqrt (24 * i + 1) = 1 := by omega
            rw [hs1] at hs
            have hi0 : i = 0 := by omega
            have hp0 : pentagonal ((0 : ℕ) : ℤ) = 0 := by
              rw [pentagonal_def]; norm_num
            exact h ((0 : ℕ) : ℤ) (by rw [hp0, hi0])
          · obtain ⟨m, hm⟩ : ∃ m, Nat.sqrt (24 * i + 1) = 6 * m + 7 :=
              ⟨((Nat.sqrt (24 * i + 1) - 1) / 6) - 1, by omega⟩
            have hiv : i = (m + 1) * (3 * m + 4) / 2 := by
              have hsq := sq24_b' m
              rw [hm] at hs
              exact div24_cancel (hs.symm.trans hsq.symm)
            exact h (Int.negSucc m) (by rw [pent_negSucc m, hiv])
        · rw [if_neg h6b]
  · rw [if_neg hs]

/-- The pentagonal entry at `i` is the reduction of the true coefficient of
Mathlib's `pentagonalSeries ℤ` (Euler's pentagonal number theorem). -/
private theorem pentRes_eq (i : ℕ) (hi : i ≤ 174762) :
    ((pentRes i : ℕ) : ZMod P) = (((PowerSeries.pentagonalSeries ℤ).coeff i : ℤ) : ZMod P) := by
  by_cases hex : ∃ k : ℤ, pentagonal k = i
  · obtain ⟨k, hk⟩ := hex
    have hbd : pentagonal k ≤ 174762 := by rw [hk]; exact hi
    have h := pentRes_of_pent k hbd
    rw [← hk, h, PowerSeries.coeff_pentagonalSeries_pentagonal]
    by_cases hk2 : (2:ℤ) ∣ k
    · rw [if_pos hk2, Int.negOnePow_even k ((even_iff_two_dvd).mpr hk2)]
      push_cast
      norm_num
    · rw [if_neg hk2, Int.negOnePow_odd k ⟨k / 2, by omega⟩]
      have hPm1 : ((P - 1 : ℕ) : ZMod P) = -1 := by
        have h1 : ((P - 1 : ℕ) : ZMod P) + 1 = 0 := by
          have h4 : (P - 1 : ℕ) + 1 = P := by omega
          calc ((P - 1 : ℕ) : ZMod P) + 1 = (((P - 1 : ℕ) + 1 : ℕ) : ZMod P) := by
                push_cast; norm_num
            _ = ((P : ℕ) : ZMod P) := by rw [h4]
            _ = 0 := ZMod.natCast_self P
        linear_combination h1
      rw [hPm1]
      push_cast
      norm_num
  · rw [pentRes_zero_of_not i hi (fun k hk => hex ⟨k, hk⟩),
      PowerSeries.coeff_pentagonalSeries_eq_zero (R := ℤ) (by simpa [Set.mem_range] using hex)]
    simp

/-! ### Soundness of the packing -/

private theorem getD_eq_zero_of_length_leNat : ∀ (l : List ℕ) (i : ℕ),
    l.length ≤ i → l.getD i 0 = 0 := by
  intro l
  induction l with
  | nil => intro i _; rfl
  | cons a as ih =>
      intro i h
      match i with
      | 0 => simp at h
      | i + 1 =>
          simp only [List.getD_cons_succ]
          exact ih i (by simp at h; omega)

private theorem getD_eq_getElem' : ∀ (l : List ℕ) (i : ℕ) (h : i < l.length),
    l.getD i 0 = l[i] := by
  intro l
  induction l with
  | nil => intro i h; simp at h
  | cons a as ih =>
      intro i h
      match i with
      | 0 => rfl
      | i + 1 => exact ih i (by simp at h; omega)

private theorem etaList_length (d : ℕ) : (etaList d).length = d := by
  rw [etaList, List.length_map, List.length_range]

private theorem etaList_getD (d i : ℕ) (hi : i < d) : (etaList d).getD i 0 = pentRes i := by
  have hlen : i < ((List.range d).map pentRes).length := by
    rw [List.length_map, List.length_range]; exact hi
  have h1 : (etaList d).getD i 0 = ((List.range d).map pentRes).getD i 0 := rfl
  rw [h1, getD_eq_getElem' _ i hlen]
  simp only [List.getElem_map (f := pentRes) (h := hlen),
    List.getElem_range (h := by rw [List.length_range]; exact hi)]

private theorem digitsLin_length (k N : ℕ) : (digitsLin k N).length = k := by
  induction k generalizing N with
  | zero => rfl
  | succ k ih => simp [digitsLin, ih]

private theorem digitsLin_getD : ∀ (k i N : ℕ), i < k →
    (digitsLin k N).getD i 0 = (N / twoW ^ i) % twoW % P := by
  intro k
  induction k with
  | zero => intro i N h; omega
  | succ k ih =>
      intro i N hi
      match i with
      | 0 => simp [digitsLin, pow_zero, Nat.div_one]
      | i + 1 =>
          have h1 : i < k := by omega
          have e : (N / twoW) / twoW ^ i = N / twoW ^ (i + 1) := by
            rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
          simp only [digitsLin, List.getD_cons_succ, ih i (N / twoW) h1, e]

private theorem digitsLin_app : ∀ (h m N : ℕ),
    digitsLin (h + m) N = digitsLin h N ++ digitsLin m (N / twoW ^ h) := by
  intro h
  induction h with
  | zero => intro m N; simp [digitsLin, pow_zero, Nat.div_one]
  | succ h ih =>
      intro m N
      have e1 : h + 1 + m = (h + m) + 1 := by omega
      have e3 : (N / twoW) / twoW ^ h = N / twoW ^ (h + 1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm (twoW ^ h) twoW]
      have ihm := ih m (N / twoW)
      rw [e3] at ihm
      show digitsLin (h + 1 + m) N = digitsLin (h + 1) N ++ digitsLin m (N / twoW ^ (h + 1))
      rw [e1, digitsLin, digitsLin, ihm, List.cons_append]

/-- `(a % (b * c)) / b = (a / b) % c`: splitting a mixed-radix remainder. -/
private theorem mod_mul_div (a b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    a % (b * c) / b = (a / b) % c := by
  obtain ⟨q, r, hqr, hr⟩ : ∃ q r, a = b * q + r ∧ r < b :=
    ⟨a / b, a % b, by rw [Nat.div_add_mod], Nat.mod_lt a hb⟩
  obtain ⟨s, t, hq, ht⟩ : ∃ s t, q = c * s + t ∧ t < c :=
    ⟨q / c, q % c, by rw [Nat.div_add_mod], Nat.mod_lt q hc⟩
  have hbt : b * t + r < b * c := by
    have h1 : b * t ≤ b * (c - 1) := Nat.mul_le_mul_left b (by omega)
    have h2 : b * (c - 1) + b = b * c := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hc)]
    omega
  have hsplit1 : a = b * c * s + (b * t + r) := by rw [hqr, hq]; ring
  have hsplit2 : a = b * (c * s) + (b * t + r) := by rw [hqr, hq]; ring
  have hmod : a % (b * c) = b * t + r := by
    rw [hsplit1, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbt]
  have hdiv : a / b = c * s + t := by
    rw [hsplit2, Nat.add_comm, Nat.add_mul_div_left _ _ hb, Nat.add_comm (b * t) r,
      Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hr, zero_add]
    omega
  rw [hmod, Nat.add_comm (b * t) r, Nat.add_mul_div_left _ _ hb,
    Nat.div_eq_of_lt hr, zero_add, hdiv, Nat.add_comm (c * s) t,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

private theorem digitsLin_split : ∀ (h m N : ℕ),
    digitsLin (h + m) N = digitsLin h (N % twoW ^ h) ++ digitsLin m (N / twoW ^ h) := by
  intro h
  induction h with
  | zero => intro m N; simp [digitsLin, pow_zero, Nat.div_one]
  | succ h ih =>
      intro m N
      have hpow : twoW ^ (h + 1) = twoW ^ h * twoW := pow_succ twoW h
      have hhead : N % (twoW ^ (h + 1)) % twoW = N % twoW := by
        rw [hpow, Nat.mul_comm (twoW ^ h) twoW,
          Nat.mod_mod_of_dvd N (dvd_mul_right twoW (twoW ^ h))]
      have htdiv : N % twoW ^ (h + 1) / twoW = (N / twoW) % twoW ^ h := by
        rw [hpow, Nat.mul_comm (twoW ^ h) twoW,
          mod_mul_div N twoW (twoW ^ h) twoW_pos (Nat.pow_pos twoW_pos)]
      have htdiv2 : N / twoW ^ (h + 1) = (N / twoW) / twoW ^ h := by
        rw [hpow, Nat.mul_comm (twoW ^ h) twoW, ← Nat.div_div_eq_div_mul]
      show digitsLin (h + 1 + m) N
        = digitsLin (h + 1) (N % twoW ^ (h + 1)) ++ digitsLin m (N / twoW ^ (h + 1))
      rw [show h + 1 + m = (h + m) + 1 from by omega, digitsLin, digitsLin,
        List.cons_append, hhead, htdiv, htdiv2]
      rw [ih m (N / twoW)]

private theorem digitsBal_eq (F k N : ℕ) : digitsBal F k N = digitsLin k N := by
  induction F generalizing k N with
  | zero => rfl
  | succ F ih =>
      by_cases hk : k ≤ 64
      · simp [digitsBal, hk]
      · have h1 : k / 2 + (k - k / 2) = k := by omega
        simp only [digitsBal, if_neg hk]
        rw [ih, ih, ← twoW_pow, ← digitsLin_split (k / 2) (k - k / 2) N, h1]

private theorem digitsBal_length : ∀ (F k N : ℕ), (digitsBal F k N).length = k := by
  intro F
  induction F with
  | zero => intro k N; exact digitsLin_length k N
  | succ F ih =>
      intro k N
      by_cases hk : k ≤ 64
      · simp [digitsBal, hk, digitsLin_length]
      · have h1 : k / 2 + (k - k / 2) = k := by omega
        simp only [digitsBal, if_neg hk, List.length_append, ih, h1]

private theorem digitsBal_getD_lt (F k N e : ℕ) : (digitsBal F k N).getD e 0 < P := by
  by_cases h : e < k
  · rw [digitsBal_eq, digitsLin_getD k e N h]
    exact Nat.mod_lt _ (by norm_num)
  · rw [getD_eq_zero_of_length_leNat _ e (by rw [digitsBal_length]; omega)]
    norm_num

/-! #### Proof-only convolution machinery -/

/-- Pointwise sum (same shape as `paddM` of `LehmerMod`; proof-only). -/
private def padd0 : List ℕ → List ℕ → List ℕ
  | [], l => l
  | l, [] => l
  | a :: as, b :: bs => (a + b) :: padd0 as bs

private def pscale0 (x : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: as => (x * a) :: pscale0 x as

private def pshift0 (l : List ℕ) : List ℕ := 0 :: l

/-- Cauchy convolution of coefficient lists (proof-only). -/
private def convL : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, b :: bs => padd0 (pscale0 a (b :: bs)) (pshift0 (convL as (b :: bs)))

private theorem getD_nilNat (i : ℕ) : ([] : List ℕ).getD i 0 = 0 := rfl

private theorem getD_padd0 : ∀ (a b : List ℕ) (i : ℕ),
    (padd0 a b).getD i 0 = a.getD i 0 + b.getD i 0 := by
  intro a
  induction a with
  | nil =>
      intro b i
      cases b with
      | nil => rfl
      | cons y bs =>
          match i with
          | 0 => simp [padd0]
          | i + 1 =>
              simp only [padd0, List.getD_cons_succ, getD_nilNat, zero_add]
  | cons x as ih =>
      intro b i
      cases b with
      | nil =>
          match i with
          | 0 => simp [padd0]
          | i + 1 => simp only [padd0, List.getD_cons_succ, getD_nilNat, add_zero]
      | cons y bs =>
          match i with
          | 0 => simp [padd0]
          | i + 1 => simp only [padd0, List.getD_cons_succ, ih bs i]

private theorem getD_pscale0 (x : ℕ) : ∀ (l : List ℕ) (i : ℕ),
    (pscale0 x l).getD i 0 = x * l.getD i 0 := by
  intro l
  induction l with
  | nil => intro i; simp [pscale0]
  | cons a as ih =>
      intro i
      match i with
      | 0 => simp [pscale0]
      | i + 1 => simp only [pscale0, List.getD_cons_succ, ih i]

private theorem getD_pshift0 (l : List ℕ) (i : ℕ) :
    (pshift0 l).getD i 0 = if i = 0 then 0 else l.getD (i - 1) 0 := by
  cases i <;> simp [pshift0]

private theorem convL_getD : ∀ (a b : List ℕ) (i : ℕ),
    (convL a b).getD i 0 = ∑ j ∈ Finset.range (i + 1), a.getD j 0 * b.getD (i - j) 0 := by
  intro a
  induction a with
  | nil =>
      intro b i
      have h0 : (convL [] b).getD i 0 = 0 := by cases b <;> rfl
      rw [h0]
      refine Eq.symm (Finset.sum_eq_zero fun j _ => ?_)
      rw [getD_nilNat, zero_mul]
  | cons x as ih =>
      intro b i
      cases b with
      | nil =>
          have h0 : (convL (x :: as) []).getD i 0 = 0 := rfl
          rw [h0]
          refine Eq.symm (Finset.sum_eq_zero fun j _ => ?_)
          rw [getD_nilNat, mul_zero]
      | cons y bs =>
          have hc : convL (x :: as) (y :: bs)
              = padd0 (pscale0 x (y :: bs)) (pshift0 (convL as (y :: bs))) := rfl
          have hstep : ∀ (n : ℕ), (convL (x :: as) (y :: bs)).getD n 0
              = x * (y :: bs).getD n 0
                + (if n = 0 then 0 else (convL as (y :: bs)).getD (n - 1) 0) := by
            intro n
            rw [hc, getD_padd0, getD_pscale0, getD_pshift0]
          match i with
          | 0 =>
              rw [hstep 0, if_pos rfl, add_zero, Finset.sum_range_succ]
              simp
          | i + 1 =>
              have hsum : ∑ j ∈ Finset.range (i + 1 + 1),
                  (x :: as).getD j 0 * (y :: bs).getD (i + 1 - j) 0
                  = (x :: as).getD 0 0 * (y :: bs).getD (i + 1) 0
                    + ∑ j ∈ Finset.range (i + 1),
                        (x :: as).getD (j + 1) 0 * (y :: bs).getD (i + 1 - (j + 1)) 0 := by
                rw [Finset.sum_range_succ']
                simp only [List.getD_cons_succ, Nat.succ_sub_succ, List.getD_cons_zero,
                  Nat.sub_zero]
                omega
              rw [hstep (i + 1), if_neg (by omega), Nat.add_sub_cancel, ih (y :: bs) i, hsum]
              simp only [List.getD_cons_succ, Nat.succ_sub_succ, List.getD_cons_zero]

/-! #### Packing lemmas -/

private theorem packAsc_take_drop : ∀ (i : ℕ) (l : List ℕ), i ≤ l.length →
    packAsc l = packAsc (takeF i l) + twoW ^ i * packAsc (dropF i l) := by
  intro i
  induction i with
  | zero => intro l _; simp [takeF, dropF, pow_zero, packAsc]
  | succ i ih =>
      intro l h
      cases l with
      | nil =>
          have hz : packAsc ([] : List ℕ) = 0 := rfl
          rw [show takeF (i + 1) [] = [] from rfl, show dropF (i + 1) [] = [] from rfl, hz,
            mul_zero, add_zero]
      | cons c cs =>
          have h1 : i ≤ cs.length := by simp at h; omega
          have hrec := ih cs h1
          simp only [takeF, dropF, packAsc, pow_succ]
          rw [hrec]
          ring

private theorem packAsc_lt : ∀ (l : List ℕ), (∀ e, l.getD e 0 < twoW) →
    packAsc l < twoW ^ l.length := by
  intro l
  induction l with
  | nil => intro _; simp [packAsc]
  | cons c cs ih =>
      intro hl
      have hc : c < twoW := by simpa using hl 0
      have hcs : ∀ e, cs.getD e 0 < twoW := fun e => by simpa using hl (e + 1)
      have hrec := ih hcs
      have key : twoW * packAsc cs + twoW ≤ twoW ^ List.length cs * twoW := by
        have h1 : packAsc cs + 1 ≤ twoW ^ List.length cs := by omega
        have h2 : twoW * (packAsc cs + 1) ≤ twoW * (twoW ^ List.length cs) :=
          Nat.mul_le_mul_left twoW h1
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm twoW (twoW ^ List.length cs)] at h2
        exact h2
      show c + twoW * packAsc cs < twoW ^ (List.length (c :: cs))
      rw [List.length_cons, pow_succ twoW]
      omega

private theorem takeF_length : ∀ (i : ℕ) (l : List ℕ), (takeF i l).length = min i l.length := by
  intro i
  induction i with
  | zero => intro l; simp [takeF]
  | succ i ih =>
      intro l
      cases l with
      | nil => simp [takeF]
      | cons c cs =>
          simp only [takeF, List.length_cons, ih cs]
          omega

private theorem getD_takeF : ∀ (i : ℕ) (l : List ℕ) (e : ℕ),
    (takeF i l).getD e 0 = if e < i then l.getD e 0 else 0 := by
  intro i
  induction i with
  | zero => intro l e; simp [takeF]
  | succ i ih =>
      intro l e
      cases l with
      | nil => simp [takeF]
      | cons c cs =>
          match e with
          | 0 => simp [takeF]
          | e + 1 => simp only [takeF, List.getD_cons_succ, ih cs e, Nat.succ_lt_succ_iff]

private theorem dropF_cons : ∀ (l : List ℕ) (i : ℕ), i < l.length →
    dropF i l = l.getD i 0 :: dropF (i + 1) l := by
  intro l
  induction l with
  | nil => intro i h; simp at h
  | cons c cs ih =>
      intro i h
      match i with
      | 0 => simp [dropF]
      | i + 1 =>
          simp only [dropF, List.getD_cons_succ]
          exact ih i (by simp at h; omega)

/-- Digit extraction from a packed bignum: slot `i` of `packAsc l` (all
entries `< twoW`) is exactly `l`'s `i`-th entry. -/
private theorem digit_extract (l : List ℕ) (hl : ∀ e, l.getD e 0 < twoW) (i : ℕ) :
    (packAsc l / twoW ^ i) % twoW = l.getD i 0 := by
  by_cases hi : i < l.length
  · have hlen : (takeF i l).length = i := by rw [takeF_length]; omega
    have htake : ∀ e, (takeF i l).getD e 0 < twoW := by
      intro e
      rw [getD_takeF]
      split_ifs
      · exact hl e
      · exact twoW_pos
    have hlt : packAsc (takeF i l) < twoW ^ i := by
      have hp := packAsc_lt (takeF i l) htake
      rw [hlen] at hp
      exact hp
    have hdrop : packAsc l / twoW ^ i = packAsc (dropF i l) := by
      have hsplit := packAsc_take_drop i l (by omega)
      rw [hsplit, Nat.add_mul_div_left _ _ (Nat.pow_pos twoW_pos), Nat.div_eq_of_lt hlt,
        Nat.zero_add]
    rw [hdrop, dropF_cons l i hi, packAsc, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hl i)]
  · have hile : l.length ≤ i := by omega
    have h1 : packAsc l < twoW ^ l.length := packAsc_lt l hl
    have h2 : twoW ^ l.length ≤ twoW ^ i := twoW_pow_mono _ _ hile
    have h3 : packAsc l / twoW ^ i = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h1 h2)
    rw [h3, Nat.zero_mod, getD_eq_zero_of_length_leNat l i hile]

private theorem packAsc_padd0 : ∀ (a b : List ℕ),
    packAsc (padd0 a b) = packAsc a + packAsc b := by
  intro a
  induction a with
  | nil => intro b; simp [padd0, packAsc]
  | cons x as ih =>
      intro b
      cases b with
      | nil => simp [padd0, packAsc]
      | cons y bs => simp only [padd0, packAsc, ih]; ring

private theorem packAsc_pscale0 (x : ℕ) : ∀ (l : List ℕ),
    packAsc (pscale0 x l) = x * packAsc l := by
  intro l
  induction l with
  | nil => simp [pscale0, packAsc]
  | cons a as ih => simp only [pscale0, packAsc, ih]; ring

private theorem packAsc_pshift0 (l : List ℕ) : packAsc (pshift0 l) = twoW * packAsc l := by
  simp [pshift0, packAsc]

private theorem packAsc_convL : ∀ (a b : List ℕ),
    packAsc (convL a b) = packAsc a * packAsc b := by
  intro a
  induction a with
  | nil =>
      intro b
      cases b with
      | nil => rfl
      | cons y bs =>
          show (0 : ℕ) = 0 * packAsc (y :: bs)
          rw [Nat.zero_mul]
  | cons x as ih =>
      intro b
      cases b with
      | nil => rfl
      | cons y bs =>
          have hc : convL (x :: as) (y :: bs)
              = padd0 (pscale0 x (y :: bs)) (pshift0 (convL as (y :: bs))) := rfl
          rw [hc, packAsc_padd0, packAsc_pscale0, packAsc_pshift0, ih]
          show x * packAsc (y :: bs) + twoW * (packAsc as * packAsc (y :: bs))
            = (x + twoW * packAsc as) * packAsc (y :: bs)
          ring

private theorem packBal_eq : ∀ (F : ℕ) (l : List ℕ), packBal F l = packAsc l := by
  intro F
  induction F with
  | zero => intro l; rfl
  | succ F ih =>
      intro l
      by_cases h : l.length ≤ 64
      · simp [packBal, h]
      · simp only [packBal, if_neg h]
        rw [ih, ih, ← twoW_pow, ← packAsc_take_drop (l.length / 2) l (by omega)]

/-! #### The slot bound and the product soundness -/

/-- Every convolution slot of lists with entries `< P` and `a.length ≤ 2 ^ 16`
is `< 2 ^ 80`: `2 ^ 16 · P ^ 2 < 2 ^ 80`. -/
private theorem convSum_lt {a b : List ℕ} (hlen : a.length ≤ 65536)
    (ha : ∀ e, a.getD e 0 < P) (hb : ∀ e, b.getD e 0 < P) (e : ℕ) :
    ∑ j ∈ Finset.range (e + 1), a.getD j 0 * b.getD (e - j) 0 < twoW := by
  have hsub : Finset.range (min (e + 1) a.length) ⊆ Finset.range (e + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hzero : ∀ j ∈ Finset.range (e + 1), j ∉ Finset.range (min (e + 1) a.length) →
      a.getD j 0 * b.getD (e - j) 0 = 0 := by
    intro j hjmem hj
    have hjl : a.length ≤ j := by
      simp only [Finset.mem_range] at hjmem hj
      omega
    rw [getD_eq_zero_of_length_leNat a j hjl]
    ring
  have hsplit : ∑ j ∈ Finset.range (e + 1), a.getD j 0 * b.getD (e - j) 0
      = ∑ j ∈ Finset.range (min (e + 1) a.length), a.getD j 0 * b.getD (e - j) 0 :=
    (Finset.sum_subset hsub hzero).symm
  rw [hsplit]
  have hbound : ∀ j ∈ Finset.range (min (e + 1) a.length),
      a.getD j 0 * b.getD (e - j) 0 ≤ P * P := fun j _ =>
    Nat.mul_le_mul (Nat.le_of_lt (ha j)) (Nat.le_of_lt (hb _))
  have hsumle := calc
    ∑ j ∈ Finset.range (min (e + 1) a.length), a.getD j 0 * b.getD (e - j) 0
        ≤ ∑ j ∈ Finset.range (min (e + 1) a.length), P * P :=
      Finset.sum_le_sum hbound
    _ = (min (e + 1) a.length) * (P * P) := by
      rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
  have hfinal : (min (e + 1) a.length) * (P * P) ≤ 65536 * (999999937 * 999999937) :=
    Nat.mul_le_mul (Nat.le_trans (Nat.min_le_right _ _) hlen) (le_refl _)
  have hlt : 65536 * (999999937 * 999999937) < twoW := by decide
  omega

/-- Interpret a mod-`P` coefficient list as a polynomial over `ZMod P`. -/
private noncomputable def L2PMod : List ℕ → (ZMod P)[X]
  | [] => 0
  | a :: as => Polynomial.C ((a : ℕ) : ZMod P) + Polynomial.X * L2PMod as

private theorem cast_modP (n : ℕ) : ((n % P : ℕ) : ZMod P) = (n : ZMod P) :=
  (ZMod.natCast_eq_natCast_iff (n % P) n P).mpr (Nat.mod_modEq n P)

private theorem coeff_L2PMod (l : List ℕ) (i : ℕ) :
    (L2PMod l).coeff i = ((l.getD i 0 : ℕ) : ZMod P) := by
  induction l generalizing i with
  | nil => simp [L2PMod]
  | cons a as ih =>
      match i with
      | 0 => simp [L2PMod]
      | i + 1 =>
          change (Polynomial.C (((a : ℕ) : ZMod P)) + Polynomial.X * L2PMod as).coeff (i + 1)
            = ((a :: as).getD (i + 1) 0 : ZMod P)
          rw [Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C, ih]
          simp

private theorem coeff_mul_range {R : Type*} [CommRing R] (p q : R[X]) (i : ℕ) :
    (p * q).coeff i = ∑ j ∈ Finset.range (i + 1), p.coeff j * q.coeff (i - j) := by
  rw [Polynomial.coeff_mul,
    ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun x => p.coeff x.1 * q.coeff x.2) i]

/-- **Soundness of one packed product**: for `i < a.length` (with
`a.length ≤ 2 ^ 16` and all entries `< P`), slot `i` of the packed product is
the `i`-th coefficient of the polynomial product. -/
private theorem packedMul_getD (a b : List ℕ) (hlen : a.length ≤ 65536)
    (ha : ∀ e, a.getD e 0 < P) (hb : ∀ e, b.getD e 0 < P) (i : ℕ) (hi : i < a.length) :
    ((packedMul a b).getD i 0 : ZMod P) = ((L2PMod a) * (L2PMod b)).coeff i := by
  have hconvlt : ∀ e, (convL a b).getD e 0 < twoW := by
    intro e
    rw [convL_getD]
    exact convSum_lt hlen ha hb e
  have hstep1 : (packedMul a b).getD i 0
      = ((packAsc a * packAsc b) / twoW ^ i) % twoW % P := by
    rw [packedMul, digitsBal_eq, packBal_eq, packBal_eq]
    exact digitsLin_getD a.length i _ hi
  rw [hstep1, ← packAsc_convL a b, digit_extract (convL a b) hconvlt i, cast_modP,
    convL_getD a b i, Nat.cast_sum, coeff_mul_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.cast_mul, ← coeff_L2PMod a j, ← coeff_L2PMod b (i - j)]

private theorem packedMul_length (a b : List ℕ) : (packedMul a b).length = a.length := by
  rw [packedMul]
  exact digitsBal_length 64 _ _

private theorem packedMul_coeff (a b : List ℕ) (hlenA : a.length ≤ 65536)
    (ha : ∀ e, a.getD e 0 < P) (hb : ∀ e, b.getD e 0 < P) (i : ℕ) (hi : i < a.length) :
    (L2PMod (packedMul a b)).coeff i = (L2PMod a * L2PMod b).coeff i := by
  rw [coeff_L2PMod]
  exact packedMul_getD a b hlenA ha hb i hi

/-! #### The 24th power chain -/

private theorem coeff_mul_congr' {R : Type*} [CommRing R] {p q r s : R[X]} {i : ℕ}
    (h1 : ∀ j ≤ i, p.coeff j = q.coeff j) (h2 : ∀ j ≤ i, r.coeff j = s.coeff j) :
    (p * r).coeff i = (q * s).coeff i := by
  simp only [Polynomial.coeff_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hmem : x.1 + x.2 = i := Finset.mem_antidiagonal.mp hx
  rw [h1 x.1 (by omega), h2 x.2 (by omega)]

private theorem coeff_pow_congr' {R : Type*} [CommRing R] {p q : R[X]}
    (h : ∀ j ≤ i, p.coeff j = q.coeff j) (k : ℕ) :
    ∀ j ≤ i, (p ^ k).coeff j = (q ^ k).coeff j := by
  induction k with
  | zero => intro j _; simp
  | succ k ih =>
      intro j hj
      rw [pow_succ, pow_succ]
      exact coeff_mul_congr' (fun n hn ↦ ih n (le_trans hn hj))
        fun n hn ↦ h n (le_trans hn hj)

private theorem pow24Packed_spelled (l : List ℕ) :
    pow24Packed l = packedMul (packedMul (packedMul (packedMul
        (packedMul l l) (packedMul l l))
        (packedMul (packedMul l l) (packedMul l l)))
      (packedMul (packedMul (packedMul l l) (packedMul l l))
        (packedMul (packedMul l l) (packedMul l l))))
      (packedMul (packedMul (packedMul l l) (packedMul l l))
        (packedMul (packedMul l l) (packedMul l l))) := rfl

private theorem L2PMod_pow24Packed (l : List ℕ) (hlen : l.length ≤ 65536)
    (hl : ∀ e, l.getD e 0 < P) (i : ℕ) (hi : i < l.length) :
    (L2PMod (pow24Packed l)).coeff i = ((L2PMod l) ^ 24).coeff i := by
  rw [pow24Packed_spelled]
  have hstep : ∀ (j : ℕ) (x y : List ℕ) (kx ky : ℕ), j ≤ i → x.length = l.length →
      y.length = l.length → (∀ e, x.getD e 0 < P) → (∀ e, y.getD e 0 < P) →
      (∀ n ≤ i, (L2PMod x).coeff n = ((L2PMod l) ^ kx).coeff n) →
      (∀ n ≤ i, (L2PMod y).coeff n = ((L2PMod l) ^ ky).coeff n) →
      (L2PMod (packedMul x y)).coeff j
        = (((L2PMod l) ^ kx) * ((L2PMod l) ^ ky)).coeff j := by
    intro j x y kx ky hj hxlen hylen hxP hyP hx hy
    rw [packedMul_coeff x y (by rw [hxlen]; exact hlen) hxP hyP j (by rw [hxlen]; omega)]
    exact coeff_mul_congr' (fun n hn => hx n (le_trans hn hj))
      (fun n hn => hy n (le_trans hn hj))
  have hlpm : ∀ x y : List ℕ, (packedMul x y).length = x.length := fun x y =>
    packedMul_length x y
  have hent : ∀ x : List ℕ, (∀ e, x.getD e 0 < P) →
      ∀ e, (packedMul x x).getD e 0 < P := fun x _ e => digitsBal_getD_lt 64 _ _ e
  -- the five stages, bottom-up
  have e2 : ∀ j ≤ i, (L2PMod (packedMul l l)).coeff j = ((L2PMod l) ^ 2).coeff j := by
    intro j hj
    have h1 : ∀ n ≤ i, (L2PMod l).coeff n = ((L2PMod l) ^ (1 : ℕ)).coeff n :=
      fun n _ => by rw [pow_one]
    have hp2 : ((L2PMod l) ^ (1 : ℕ)) * ((L2PMod l) ^ (1 : ℕ)) = ((L2PMod l) ^ 2) := by
      rw [pow_one, pow_two]
    rw [hstep j l l 1 1 hj rfl rfl hl hl h1 h1, hp2]
  have h2len : (packedMul l l).length = l.length := hlpm l l
  have h2ent : ∀ e, (packedMul l l).getD e 0 < P := hent l hl
  have hp4 : ((L2PMod l) ^ 2) * ((L2PMod l) ^ 2) = ((L2PMod l) ^ 4) := by ring
  have e4 : ∀ j ≤ i, (L2PMod (packedMul (packedMul l l) (packedMul l l))).coeff j
      = ((L2PMod l) ^ 4).coeff j := by
    intro j hj
    rw [hstep j (packedMul l l) (packedMul l l) 2 2 hj h2len h2len h2ent h2ent e2 e2, hp4]
  have h4len : (packedMul (packedMul l l) (packedMul l l)).length = l.length := by
    rw [hlpm]; exact h2len
  have h4ent : ∀ e, (packedMul (packedMul l l) (packedMul l l)).getD e 0 < P :=
    hent _ h2ent
  have hp8 : ((L2PMod l) ^ 4) * ((L2PMod l) ^ 4) = ((L2PMod l) ^ 8) := by ring
  have e8 : ∀ j ≤ i, (L2PMod (packedMul (packedMul (packedMul l l) (packedMul l l))
      (packedMul (packedMul l l) (packedMul l l)))).coeff j
      = ((L2PMod l) ^ 8).coeff j := by
    intro j hj
    rw [hstep j (packedMul (packedMul l l) (packedMul l l))
        (packedMul (packedMul l l) (packedMul l l)) 4 4 hj h4len h4len h4ent h4ent e4 e4,
      hp8]
  set h8term : List ℕ := packedMul (packedMul (packedMul l l) (packedMul l l))
      (packedMul (packedMul l l) (packedMul l l)) with h8eq
  have h8len : h8term.length = l.length := by rw [h8eq, hlpm]; exact h4len
  have h8ent : ∀ e, h8term.getD e 0 < P := by
    intro e
    rw [h8eq]
    exact hent _ h4ent e
  have hp16 : ((L2PMod l) ^ 8) * ((L2PMod l) ^ 8) = ((L2PMod l) ^ 16) := by ring
  have e16 : ∀ j ≤ i, (L2PMod (packedMul h8term h8term)).coeff j
      = ((L2PMod l) ^ 16).coeff j := by
    intro j hj
    rw [hstep j h8term h8term 8 8 hj h8len h8len h8ent h8ent e8 e8, hp16]
  have h16len : (packedMul h8term h8term).length = l.length := by
    rw [hlpm]; exact h8len
  have h16ent : ∀ e, (packedMul h8term h8term).getD e 0 < P := hent _ h8ent
  have hp24 : ((L2PMod l) ^ 16) * ((L2PMod l) ^ 8) = ((L2PMod l) ^ 24) := by ring
  rw [hstep i (packedMul h8term h8term) h8term 16 8 (le_refl i) h16len h8len h16ent h8ent
    e16 e8, hp24]

private theorem pow24Packed_length (l : List ℕ) : (pow24Packed l).length = l.length := by
  rw [pow24Packed_spelled]
  simp only [packedMul_length]

/-! ### Bridge: `etaPoly` against the pentagonal series -/

/-- Multiplying by `1 - X ^ m` does not change coefficients below `m`. -/
private theorem coeff_mul_one_sub (p : ℤ[X]) (m i : ℕ) (hi : i < m) :
    (p * (1 - X ^ m : ℤ[X])).coeff i = p.coeff i := by
  have key : ∀ b ∈ Finset.antidiagonal i, b ≠ (i, 0) →
      p.coeff b.1 * (1 - X ^ m : ℤ[X]).coeff b.2 = 0 := by
    intro b hb hne
    have hmem : b.1 + b.2 = i := Finset.mem_antidiagonal.mp hb
    have hb2 : b.2 ≠ 0 := by
      intro h0
      apply hne
      rw [Prod.ext_iff]
      omega
    have hc : (1 - X ^ m : ℤ[X]).coeff b.2 = 0 := by
      have hcp := coeff_one_sub_X_pow m 1 b.2 (by omega)
      rw [pow_one] at hcp
      rw [hcp, if_neg hb2]
    rw [hc, mul_zero]
  rw [Polynomial.coeff_mul,
    Finset.sum_eq_single (i, 0) key (by simp [Finset.mem_antidiagonal])]
  show p.coeff i * (1 - X ^ m : ℤ[X]).coeff 0 = p.coeff i
  have hcp := coeff_one_sub_X_pow m 1 0 (by omega)
  rw [pow_one, if_pos rfl] at hcp
  rw [hcp, mul_one]

/-- The coefficients of `etaPoly` below the truncation point are stable. -/
private theorem etaPoly_coeff_stable (i N M : ℕ) (hi : i < N) (hNM : N ≤ M) :
    (etaPoly N).coeff i = (etaPoly M).coeff i := by
  induction M with
  | zero => omega
  | succ M ih =>
      by_cases h : N ≤ M
      · rw [etaPoly_succ, coeff_mul_one_sub _ (M + 1) i (by omega)]
        exact ih h
      · have hN : N = M + 1 := by omega
        rw [hN]

private theorem coe_prod_etaPoly (M : ℕ) : ((etaPoly M : ℤ[X]) : PowerSeries ℤ)
    = ∏ n ∈ Finset.range M, ((1 - X ^ (n + 1) : ℤ[X]) : PowerSeries ℤ) := by
  induction M with
  | zero => simp [etaPoly]
  | succ M ih =>
      rw [etaPoly_succ, Polynomial.coe_mul, ih, Finset.prod_range_succ]

/-- **The truncated Euler product has the pentagonal coefficients** (Euler's
pentagonal number theorem, low-degree instance): for `i < N`, the `i`-th
coefficient of `etaPoly N` is the `i`-th coefficient of `pentagonalSeries ℤ`. -/
private theorem etaPoly_coeff_pent (N i : ℕ) (hi : i < N) :
    (etaPoly N).coeff i = ((PowerSeries.pentagonalSeries ℤ).coeff i : ℤ) := by
  obtain ⟨t, ht⟩ := Filter.eventually_atTop.mp
    (PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq (R := ℤ) i)
  have hsub : t ≤ Finset.range (max (max N (i + 1)) (t.sup id + 1)) := by
    intro x hx
    have hle : x ≤ t.sup id := Finset.le_sup (f := id) hx
    simp only [Finset.mem_range]
    omega
  have h1 := ht (Finset.range (max (max N (i + 1)) (t.sup id + 1))) hsub
  have hM : N ≤ max (max N (i + 1)) (t.sup id + 1) :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  calc (etaPoly N).coeff i
      = (etaPoly (max (max N (i + 1)) (t.sup id + 1))).coeff i :=
        etaPoly_coeff_stable i N _ hi hM
    _ = (((etaPoly (max (max N (i + 1)) (t.sup id + 1)) : ℤ[X]) : PowerSeries ℤ)).coeff i :=
        (Polynomial.coeff_coe _ i).symm
    _ = (∏ n ∈ Finset.range (max (max N (i + 1)) (t.sup id + 1)),
          ((1 - X ^ (n + 1) : ℤ[X]) : PowerSeries ℤ)).coeff i := by rw [coe_prod_etaPoly]
    _ = (∏ n ∈ Finset.range (max (max N (i + 1)) (t.sup id + 1)),
          (1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ)).coeff i := by
        have hf : ∀ n ∈ Finset.range (max (max N (i + 1)) (t.sup id + 1)),
            ((1 - X ^ (n + 1) : ℤ[X]) : PowerSeries ℤ)
              = (1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ) := fun n _ => by simp
        rw [Finset.prod_congr rfl hf]
    _ = ((PowerSeries.pentagonalSeries ℤ).coeff i : ℤ) := h1

/-! ### The packed computation is sound -/

/-- The truncated Euler product over `ZMod P`. -/
private noncomputable def etaPolyMod (N : ℕ) : (ZMod P)[X] :=
  Polynomial.map (Int.castRingHom (ZMod P)) (etaPoly N)

/-- **Soundness of the packed pipeline**: for `i < d ≤ 2 ^ 16`, the `i`-th
entry of `pow24Packed (etaList d)` is the `i`-th coefficient of
`(etaPoly d) ^ 24`, reduced mod `P`. -/
theorem deltaPacked_eq (d i : ℕ) (hd : d ≤ 65536) (hi : i < d) :
    (((pow24Packed (etaList d)).getD i 0 : ℕ) : ZMod P)
      = (((etaPoly d ^ 24).coeff i : ℤ) : ZMod P) := by
  have hent : ∀ e, (etaList d).getD e 0 < P := by
    intro e
    by_cases he : e < d
    · rw [etaList_getD d e he]; exact pentRes_lt e
    · rw [getD_eq_zero_of_length_leNat _ e (by rw [etaList_length]; omega)]
      norm_num
  have h1 : (((pow24Packed (etaList d)).getD i 0 : ℕ) : ZMod P)
      = (L2PMod (pow24Packed (etaList d))).coeff i := (coeff_L2PMod _ i).symm
  have h2 : (L2PMod (pow24Packed (etaList d))).coeff i
      = ((L2PMod (etaList d)) ^ 24).coeff i :=
    L2PMod_pow24Packed (etaList d) (by rw [etaList_length]; exact hd) hent i
      (by rw [etaList_length]; exact hi)
  have hagree : ∀ j ≤ i, (L2PMod (etaList d)).coeff j = (etaPolyMod d).coeff j := by
    intro j hj
    rw [coeff_L2PMod, etaList_getD d j (by omega), pentRes_eq j (by omega), etaPolyMod,
      Polynomial.coeff_map, ← etaPoly_coeff_pent d j (by omega)]
    rfl
  rw [h1, h2, coeff_pow_congr' hagree 24 i (le_refl i), etaPolyMod, ← Polynomial.map_pow,
    Polynomial.coeff_map]
  rfl

/-- If the mod-`P` residue of the `i`-th packed coefficient is nonzero, then
`tauOf i ≠ 0` — a nonzero residue mod the prime `P` certifies the integer
coefficient is nonzero. -/
theorem tauOf_ne_zero_of_packed {d i : ℕ} (hd : d ≤ 65536) (hi : i < d)
    (hmod : (pow24Packed (etaList d)).getD i 0 % P ≠ 0) : tauOf i ≠ 0 := by
  intro hzero
  have hz : ((deltaCoeffs d).getD i 0 : ℤ) = 0 := by
    rw [← tauOf_eq_getD d i hi]
    exact hzero
  have hcoef : (((etaPoly d ^ 24).coeff i : ℤ) : ZMod P) = 0 := by
    have h3 : ((etaPoly d ^ 24).coeff i : ℤ) = ((deltaCoeffs d).getD i 0) :=
      (deltaCoeffs_getD d i hi).symm
    rw [h3, hz]
    push_cast
    ring
  have hcast : (((pow24Packed (etaList d)).getD i 0 : ℕ) : ZMod P) = 0 := by
    rw [deltaPacked_eq d i hd hi, hcoef]
  have hmod0 : (pow24Packed (etaList d)).getD i 0 ≡ 0 [MOD P] := by
    have h5 : (((pow24Packed (etaList d)).getD i 0 : ℕ) : ZMod P) = ((0 : ℕ) : ZMod P) := by
      rw [hcast, Nat.cast_zero]
    rw [ZMod.natCast_eq_natCast_iff] at h5
    exact h5
  have hv : (pow24Packed (etaList d)).getD i 0 % P = 0 := by
    simpa [Nat.ModEq] using hmod0
  exact absurd hv hmod

/-! ### The packed residue list as a public accessor -/

/-- The packed τ-residue list: `tauResList d` has length `d`; for `d ≤ 65536`
its `i`-th entry is an integer whose residue mod `P = 999999937` is
`τ (i + 1)` (see `tauResList_eq_tauZMod`).  Computed by the packed-bignum
pipeline: `etaList d` (pentagonal entries) raised to the 24th power. -/
def tauResList (d : ℕ) : List ℕ := pow24Packed (etaList d)

theorem tauResList_length (d : ℕ) : (tauResList d).length = d := by
  rw [tauResList, pow24Packed_length, etaList_length]

/-- **Residue bridge**: for `i < d ≤ 65536`, the `i`-th packed entry, cast
into `ZMod P`, is the residue of `τ (i + 1)` — the seed datum for the
prime-power recursion chains (`MathProof/Tau/PowChain.lean`). -/
theorem tauResList_eq_tauZMod (d i : ℕ) (hd : d ≤ 65536) (hi : i < d) :
    (((tauResList d).getD i 0 : ℕ) : ZMod P) = ((tau (i + 1) : ℤ) : ZMod P) := by
  rw [tauResList, deltaPacked_eq d i hd hi, tau_eq i, tauOf,
    coeff_pow_congr' (fun j hj => etaPoly_coeff_stable j (i + 1) d (by omega) (by omega)) 24 i
      (le_refl i)]

/-! ### The kernel-verified nonvanishing checks -/

private theorem allNonzero_iff {l : List ℕ} :
    allNonzero l = true ↔ ∀ i < l.length, l.getD i 0 % P ≠ 0 := by
  induction l with
  | nil => simp [allNonzero]
  | cons c cs ih =>
      simp only [allNonzero, List.length_cons, Bool.and_eq_true]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        match i with
        | 0 => simpa using h1
        | i + 1 => exact ih.mp h2 i (by simp at hi; omega)
      · intro h
        exact ⟨by simpa using h 0 (by simp), ih.mpr fun i hi => h (i + 1) (by simp; omega)⟩

-- η = 1 − X − X² + X⁵ + X⁷ − X¹² − X¹⁵ + …: the first 16 pentagonal residues.
set_option maxHeartbeats 8000000 in
example :
    (etaList 16).take 16 =
      [1, P - 1, P - 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, P - 1, 0, 0, P - 1] := by
  decide

-- End-to-end computational check at 512: τ residues mod P are nonzero.
set_option maxHeartbeats 8000000 in
theorem packed_nonvanishing_512 : allNonzero (pow24Packed (etaList 512)) = true := by
  decide +kernel

-- The 16384 decide needs ~16 GiB of kernel heap: build this module on the
-- Modal builder, not in CI (see AGENTS.md and research/lehmer-mod-scaling-study.md).
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000 in
theorem packed_nonvanishing_16384 : allNonzero (pow24Packed (etaList 16384)) = true := by
  decide +kernel

/-- **Lehmer's conjecture holds up to 16384**: `τ n ≠ 0` for all `1 ≤ n ≤ 16384`,
verified entirely inside Lean's kernel by the packed-bignum pipeline
(`tauOf_ne_zero_of_packed` + `packed_nonvanishing_16384`). -/
theorem tau_ne_zero_of_le_16384 {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 16384) : tau n ≠ 0 := by
  have hlen : (pow24Packed (etaList 16384)).length = 16384 := by
    rw [pow24Packed_length, etaList_length]
  have h := allNonzero_iff.mp packed_nonvanishing_16384 (n - 1) (by rw [hlen]; omega)
  change tauOf (n - 1) ≠ 0
  exact tauOf_ne_zero_of_packed (by norm_num) (by omega) h

/-- `τ p ≠ 0` for every prime `p ≤ 16384`. -/
theorem tau_prime_ne_zero_of_le_16384 {p : ℕ} (hp : p.Prime) (hle : p ≤ 16384) :
    tau p ≠ 0 :=
  tau_ne_zero_of_le_16384 (Nat.Prime.pos hp) hle

-- The 65536 decide needs ~60 GiB of kernel heap: build on the Modal builder
-- only, never in CI (see research/lehmer-mod-scaling-study.md and
-- Bench/Packed/BBenchPackedBal.lean).
set_option maxHeartbeats 8000000 in
theorem packed_nonvanishing_65536 : allNonzero (pow24Packed (etaList 65536)) = true := by
  decide +kernel

/-- **Lehmer's conjecture holds up to 65536**: `τ n ≠ 0` for all `1 ≤ n ≤ 65536`,
verified entirely inside Lean's kernel by the packed-bignum pipeline. -/
theorem tau_ne_zero_of_le_65536 {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 65536) : tau n ≠ 0 := by
  have hlen : (pow24Packed (etaList 65536)).length = 65536 := by
    rw [pow24Packed_length, etaList_length]
  have h := allNonzero_iff.mp packed_nonvanishing_65536 (n - 1) (by rw [hlen]; omega)
  change tauOf (n - 1) ≠ 0
  exact tauOf_ne_zero_of_packed (le_refl _) (by omega) h

/-- `τ p ≠ 0` for every prime `p ≤ 65536`. -/
theorem tau_prime_ne_zero_of_le_65536 {p : ℕ} (hp : p.Prime) (hle : p ≤ 65536) :
    tau p ≠ 0 :=
  tau_ne_zero_of_le_65536 (Nat.Prime.pos hp) hle

end Ramanujan
