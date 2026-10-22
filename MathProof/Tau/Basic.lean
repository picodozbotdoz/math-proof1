import Mathlib.Tactic

/-!
# The Ramanujan tau function

We define the **Ramanujan tau function** `τ : ℕ → ℤ`, the coefficient of `q ^ n`
in the q-expansion of the modular discriminant
`Δ = q ∏_{m ≥ 1} (1 - q ^ m) ^ 24`.

The definition is purely algebraic: `Ramanujan.tauOf i` is the coefficient of
`X ^ i` in `(∏_{m ≤ i+1} (1 - X ^ m)) ^ 24 ∈ ℤ[X]`, and `Ramanujan.tau n = tauOf (n-1)`.
A truncation-stability lemma (`Ramanujan.etaPow24_stable`) shows that using more
factors of the infinite product does not change low coefficients, so `τ` is
independent of the truncation point.

To support *verified computation* we represent truncated coefficient lists as
`List ℤ` with hand-rolled arithmetic (`pmul`, `psub`, `shiftBy`, ...) designed to
be kernel-friendly, and prove `Ramanujan.deltaCoeffs_getD`: the list
`deltaCoeffs d` consists of the coefficients of `∏_{m≥1} (1 - X ^ m) ^ 24` in
degrees `< d`.  Together with `Ramanujan.tauOf_eq_getD` this makes `τ` efficiently
evaluable inside Lean's kernel (`decide`), without trusting an external computer
algebra system.

## Main definitions

* `Ramanujan.tau` : the Ramanujan tau function `τ n`, for `n ≥ 1`.

## Main statements

* `Ramanujan.tauOf_eq_getD` : `τ` agrees with the verified list computation.
* `Ramanujan.tau_one` … `Ramanujan.tau_twelve` : the initial values
  `τ 1 = 1, τ 2 = -24, τ 3 = 252, …` of OEIS A000594, proved by `decide`.

## Tags

modular forms, Ramanujan tau function, discriminant, eta function
-/

open Polynomial

namespace Ramanujan

/-! ### Truncated coefficient-list arithmetic -/

/-- Elementwise sum of coefficient lists, padding the shorter with zeros. -/
def padd : List ℤ → List ℤ → List ℤ
  | [], l => l
  | l, [] => l
  | a :: as, b :: bs => (a + b) :: padd as bs

/-- Scalar multiple of a coefficient list. -/
def pscale (x : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: as => (x * a) :: pscale x as

/-- Multiplication by `X` on coefficient lists. -/
def pshift (l : List ℤ) : List ℤ := 0 :: l

/-- Product (Cauchy convolution) of coefficient lists. -/
def pmul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, b => padd (pscale a b) (pshift (pmul as b))

/-- Negation of a coefficient list (structural, so the kernel can reduce it). -/
def pneg : List ℤ → List ℤ
  | [] => []
  | b :: bs => (-b) :: pneg bs

/-- Entrywise difference of coefficient lists, padding the shorter with zeros. -/
def psub : List ℤ → List ℤ → List ℤ
  | [], l => pneg l
  | a :: as, [] => a :: psub as []
  | a :: as, b :: bs => (a - b) :: psub as bs

/-- Multiplication by `X ^ m` on coefficient lists. -/
def shiftBy : ℕ → List ℤ → List ℤ
  | 0, l => l
  | m + 1, l => 0 :: shiftBy m l

/-- Interpret a coefficient list `l` as the polynomial `∑ lᵢ Xⁱ`.
(Noncomputable: only used in proofs.) -/
noncomputable def L2P : List ℤ → ℤ[X]
  | [] => 0
  | a :: as => C a + X * L2P as

/-! ### Soundness of the list arithmetic -/

theorem getD_eq_zero_of_length_le : ∀ (l : List ℤ) (i : ℕ), l.length ≤ i → l.getD i 0 = 0 := by
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

theorem L2P_padd : ∀ a b : List ℤ, L2P (padd a b) = L2P a + L2P b := by
  intro a
  induction a with
  | nil => intro b; simp [padd, L2P]
  | cons a as ih =>
      intro b
      cases b with
      | nil => simp [padd, L2P]
      | cons b bs => simp [padd, L2P, ih]; ring

theorem L2P_pscale (x : ℤ) : ∀ l : List ℤ, L2P (pscale x l) = C x * L2P l := by
  intro l
  induction l with
  | nil => simp [pscale, L2P]
  | cons a as ih => simp [pscale, L2P, ih]; ring

theorem L2P_pshift (l : List ℤ) : L2P (pshift l) = X * L2P l := by
  simp [pshift, L2P]

theorem L2P_pmul : ∀ a b : List ℤ, L2P (pmul a b) = L2P a * L2P b := by
  intro a
  induction a with
  | nil => intro b; simp [pmul, L2P]
  | cons a as ih =>
      intro b
      simp only [pmul, L2P_padd, L2P_pscale, L2P_pshift, ih, L2P]
      ring

theorem coeff_L2P (l : List ℤ) (i : ℕ) : (L2P l).coeff i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [L2P]
  | cons a as ih =>
      match i with
      | 0 => simp [L2P]
      | i + 1 =>
          change (C a + X * L2P as).coeff (i + 1) = (a :: as).getD (i + 1) 0
          rw [Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C, ih]
          simp

theorem getD_pneg : ∀ (b : List ℤ) (i : ℕ), (pneg b).getD i 0 = -(b.getD i 0) := by
  intro b
  induction b with
  | nil => intro i; simp [pneg]
  | cons b bs ih =>
      intro i
      match i with
      | 0 => simp [pneg]
      | i + 1 => simp only [pneg, List.getD_cons_succ, ih i]

theorem getD_psub : ∀ (a b : List ℤ) (i : ℕ),
    (psub a b).getD i 0 = a.getD i 0 - b.getD i 0 := by
  intro a
  induction a with
  | nil => intro b i; simpa [psub] using getD_pneg b i
  | cons a as ih =>
      intro b i
      cases b with
      | nil =>
          match i with
          | 0 => simp [psub]
          | i + 1 =>
              simp only [psub, List.getD_cons_succ]
              rw [ih [] i]; simp
      | cons b bs =>
          match i with
          | 0 => simp [psub]
          | i + 1 => simp only [psub, List.getD_cons_succ, ih bs i]

theorem getD_shiftBy (m : ℕ) : ∀ (l : List ℤ) (i : ℕ),
    (shiftBy m l).getD i 0 = if i < m then 0 else l.getD (i - m) 0 := by
  induction m with
  | zero => intro l i; simp [shiftBy]
  | succ m ih =>
      intro l i
      match i with
      | 0 => simp [shiftBy]
      | i + 1 =>
          simp only [shiftBy, List.getD_cons_succ, ih l i]
          rw [show i + 1 - (m + 1) = i - m from by omega]
          split_ifs <;> omega

theorem getD_take : ∀ (d : ℕ) (l : List ℤ) (i : ℕ),
    (List.take d l).getD i 0 = if i < d then l.getD i 0 else 0 := by
  intro d
  induction d with
  | zero => intro l i; simp
  | succ d ih =>
      intro l i
      cases l with
      | nil => simp
      | cons a as =>
          match i with
          | 0 => simp
          | i + 1 =>
              simp only [List.take_succ_cons, List.getD_cons_succ, ih as i]
              split_ifs <;> omega

/-! ### The Euler product as a polynomial -/

/-- The finite Euler product `∏_{m=1}^{N} (1 - X ^ m)` as a polynomial in `ℤ[X]`. -/
noncomputable def etaPoly (N : ℕ) : ℤ[X] := ∏ m ∈ Finset.range N, (1 - X ^ (m + 1))

theorem etaPoly_succ (N : ℕ) : etaPoly (N + 1) = etaPoly N * (1 - X ^ (N + 1)) := by
  simp only [etaPoly, Finset.prod_range_succ]

/-- The truncated product `∏_{m=1}^{N} (1 - X ^ m)`, as a coefficient list of
length at most `d`.  Each step multiplies by `(1 - X ^ (N+1))` and truncates. -/
def Pbuild (d : ℕ) : ℕ → List ℤ
  | 0 => List.take d [1]
  | N + 1 => List.take d (psub (Pbuild d N) (shiftBy (N + 1) (Pbuild d N)))

theorem Pbuild_getD (d : ℕ) : ∀ (N i : ℕ), i < d →
    (Pbuild d N).getD i 0 = (etaPoly N).coeff i := by
  intro N
  induction N with
  | zero =>
      intro i hi
      match i, hi with
      | 0, _ =>
          rcases d with _ | d
          · omega
          · simp [Pbuild, etaPoly, List.take_succ_cons]
      | (i + 1), hi =>
          rcases d with _ | d
          · omega
          · have h0 : (List.take (d + 1) [1] : List ℤ).getD (i + 1) 0 = 0 := by
              rw [List.take_succ_cons]; simp
            rw [show Pbuild (d + 1) 0 = List.take (d + 1) [1] from rfl, h0]
            simp [etaPoly, Polynomial.coeff_one]
  | succ N ih =>
      intro i hi
      have hsplit : (Pbuild d (N + 1)).getD i 0
          = (Pbuild d N).getD i 0 - (shiftBy (N + 1) (Pbuild d N)).getD i 0 := by
        simp only [Pbuild, getD_take, hi, if_true, getD_psub]
      rw [hsplit, getD_shiftBy, ih i hi, etaPoly_succ, mul_sub, mul_one,
        Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow']
      by_cases h : N + 1 ≤ i
      · rw [if_neg (show ¬ i < N + 1 by omega), if_pos h,
        ih (i - (N + 1)) (by omega)]
      · rw [if_pos (show i < N + 1 by omega), if_neg h, sub_zero]

/-! ### Low coefficients of products -/

theorem coeff_mul_congr {p q r s : ℤ[X]} {i : ℕ}
    (h1 : ∀ j ≤ i, p.coeff j = q.coeff j) (h2 : ∀ j ≤ i, r.coeff j = s.coeff j) :
    (p * r).coeff i = (q * s).coeff i := by
  simp only [Polynomial.coeff_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hmem : x.1 + x.2 = i := Finset.mem_antidiagonal.mp hx
  rw [h1 x.1 (by omega), h2 x.2 (by omega)]

/-- If two polynomials agree in all coefficients up to degree `i`, then so do
their `k`-th powers. -/
theorem coeff_pow_congr {p q : ℤ[X]} (h : ∀ j ≤ i, p.coeff j = q.coeff j) (k : ℕ) :
    ∀ j ≤ i, (p ^ k).coeff j = (q ^ k).coeff j := by
  induction k with
  | zero => intro j _; simp
  | succ k ih =>
      intro j hj
      rw [pow_succ, pow_succ]
      exact coeff_mul_congr (fun n hn ↦ ih n (le_trans hn hj))
        fun n hn ↦ h n (le_trans hn hj)

/-- Coefficients of `(1 - X ^ m) ^ k` below `m`: just the constant term. -/
theorem coeff_one_sub_X_pow (m k i : ℕ) (hi : i < m) :
    (((1 - X ^ m : ℤ[X])) ^ k).coeff i = if i = 0 then 1 else 0 := by
  induction k with
  | zero => simp [Polynomial.coeff_one]
  | succ k ih =>
      have h0 : (((1 - X ^ m : ℤ[X])) ^ (k + 1)).coeff i
          = (((1 - X ^ m : ℤ[X])) ^ k).coeff i
            - (((1 - X ^ m : ℤ[X])) ^ k * X ^ m).coeff i := by
        rw [pow_succ, mul_sub, mul_one, Polynomial.coeff_sub]
      rw [h0, Polynomial.coeff_mul_X_pow', if_neg (show ¬ (m ≤ i) by omega),
        sub_zero, ih]

/-- Multiplying by `(1 - X ^ m) ^ 24` does not change coefficients below `m`. -/
theorem coeff_mul_one_sub_pow24 (p : ℤ[X]) (m i : ℕ) (hi : i < m) :
    (p * ((1 - X ^ m : ℤ[X])) ^ 24).coeff i = p.coeff i := by
  have key : ∀ b ∈ Finset.antidiagonal i, b ≠ (i, 0) →
      p.coeff b.1 * (((1 - X ^ m : ℤ[X])) ^ 24).coeff b.2 = 0 := by
    intro b hb hne
    have hmem : b.1 + b.2 = i := Finset.mem_antidiagonal.mp hb
    have hb2 : b.2 ≠ 0 := by
      intro h0
      apply hne
      rw [Prod.ext_iff]
      omega
    rw [coeff_one_sub_X_pow m 24 b.2 (by omega), if_neg hb2, mul_zero]
  rw [Polynomial.coeff_mul,
    Finset.sum_eq_single (i, 0) key (by simp [Finset.mem_antidiagonal]),
    coeff_one_sub_X_pow m 24 0 (by omega)]
  simp

/-- The coefficients of `(∏_{m=1}^{M} (1 - X ^ m)) ^ 24` below `M` are stable in `M`. -/
theorem etaPow24_stable (i M : ℕ) (h : i < M) :
    ((etaPoly M) ^ 24).coeff i = ((etaPoly (i + 1)) ^ 24).coeff i := by
  induction M with
  | zero => omega
  | succ M ih =>
      by_cases hM : i < M
      · rw [etaPoly_succ, mul_pow, coeff_mul_one_sub_pow24 _ (M + 1) i (by omega)]
        exact ih hM
      · have hiM : i = M := by omega
        subst hiM
        rfl

/-! ### The verified computation -/

/-- `l ^ 24` computed by five squarings (kernel-friendly). -/
def pow24 (l : List ℤ) : List ℤ :=
  let s2 := pmul l l
  let s4 := pmul s2 s2
  let s8 := pmul s4 s4
  let s16 := pmul s8 s8
  pmul s16 s8

theorem L2P_pow24 (l : List ℤ) : L2P (pow24 l) = (L2P l) ^ 24 := by
  have e2 : L2P (pmul l l) = (L2P l) ^ 2 := by rw [L2P_pmul, ← pow_two]
  have e4 : L2P (pmul (pmul l l) (pmul l l)) = (L2P l) ^ 4 := by
    rw [L2P_pmul, e2]; ring
  have e8 : L2P (pmul (pmul (pmul l l) (pmul l l)) (pmul (pmul l l) (pmul l l)))
      = (L2P l) ^ 8 := by
    rw [L2P_pmul, e4]; ring
  have e16 : L2P (pmul
      (pmul (pmul (pmul l l) (pmul l l)) (pmul (pmul l l) (pmul l l)))
      (pmul (pmul (pmul l l) (pmul l l)) (pmul (pmul l l) (pmul l l))))
      = (L2P l) ^ 16 := by
    rw [L2P_pmul, e8]; ring
  simp only [pow24]
  rw [L2P_pmul, e16, e8, ← pow_add]

/-- The coefficients of `∏_{m=1}^{d} (1 - X ^ m) ^ 24` in degrees `< d`,
as a computable list of integers. -/
def deltaCoeffs (d : ℕ) : List ℤ := List.take d (pow24 (Pbuild d d))

theorem deltaCoeffs_getD (d i : ℕ) (hi : i < d) :
    (deltaCoeffs d).getD i 0 = ((etaPoly d) ^ 24).coeff i := by
  rw [deltaCoeffs, getD_take]
  simp only [hi, ite_true, ← coeff_L2P, L2P_pow24]
  exact coeff_pow_congr
    (fun j hj ↦ (coeff_L2P (Pbuild d d) j).trans (Pbuild_getD d d j (by omega))) 24 i
    (le_refl i)

/-! ### The Ramanujan tau function -/

/-- The coefficient of `q ^ i` in `∏_{m ≥ 1} (1 - q ^ m) ^ 24`. -/
noncomputable def tauOf (i : ℕ) : ℤ := ((etaPoly (i + 1)) ^ 24).coeff i

/-- **The Ramanujan tau function**: `tau n` is the coefficient of `q ^ n` in the
q-expansion `Δ = q ∏_{m ≥ 1} (1 - q ^ m) ^ 24` of the modular discriminant, for
`n ≥ 1` (OEIS A000594). -/
noncomputable def tau (n : ℕ) : ℤ := tauOf (n - 1)

/-- Master computation lemma: `tauOf i` is read off the verified list
`deltaCoeffs d` whenever `i < d`. -/
theorem tauOf_eq_getD (d i : ℕ) (h : i < d) :
    tauOf i = (deltaCoeffs d).getD i 0 := by
  rw [tauOf, deltaCoeffs_getD d i h]
  exact (etaPow24_stable i d h).symm

theorem tau_eq (n : ℕ) : tau (n + 1) = tauOf n := rfl

/-! ### Initial values (OEIS A000594), verified by the kernel -/

theorem tau_one : tau 1 = 1 := by
  change tauOf 0 = 1
  rw [tauOf_eq_getD 1 0 (by omega)]; decide

theorem tau_two : tau 2 = -24 := by
  change tauOf 1 = -24
  rw [tauOf_eq_getD 2 1 (by omega)]; decide

theorem tau_three : tau 3 = 252 := by
  change tauOf 2 = 252
  rw [tauOf_eq_getD 3 2 (by omega)]; decide

theorem tau_four : tau 4 = -1472 := by
  change tauOf 3 = -1472
  rw [tauOf_eq_getD 4 3 (by omega)]; decide

theorem tau_five : tau 5 = 4830 := by
  change tauOf 4 = 4830
  rw [tauOf_eq_getD 5 4 (by omega)]; decide

theorem tau_six : tau 6 = -6048 := by
  change tauOf 5 = -6048
  rw [tauOf_eq_getD 6 5 (by omega)]; decide

theorem tau_seven : tau 7 = -16744 := by
  change tauOf 6 = -16744
  rw [tauOf_eq_getD 7 6 (by omega)]; decide

theorem tau_eight : tau 8 = 84480 := by
  change tauOf 7 = 84480
  rw [tauOf_eq_getD 8 7 (by omega)]; decide

theorem tau_nine : tau 9 = -113643 := by
  change tauOf 8 = -113643
  rw [tauOf_eq_getD 9 8 (by omega)]; decide

theorem tau_ten : tau 10 = -115920 := by
  change tauOf 9 = -115920
  rw [tauOf_eq_getD 10 9 (by omega)]; decide

theorem tau_eleven : tau 11 = 534612 := by
  change tauOf 10 = 534612
  rw [tauOf_eq_getD 11 10 (by omega)]; decide

theorem tau_twelve : tau 12 = -370944 := by
  change tauOf 11 = -370944
  rw [tauOf_eq_getD 12 11 (by omega)]; decide


theorem tau_thirteen : tau 13 = -577738 := by
  change tauOf 12 = -577738
  rw [tauOf_eq_getD 13 12 (by omega)]; decide

theorem tau_fourteen : tau 14 = 401856 := by
  change tauOf 13 = 401856
  rw [tauOf_eq_getD 14 13 (by omega)]; decide

theorem tau_fifteen : tau 15 = 1217160 := by
  change tauOf 14 = 1217160
  rw [tauOf_eq_getD 15 14 (by omega)]; decide

theorem tau_sixteen : tau 16 = 987136 := by
  change tauOf 15 = 987136
  rw [tauOf_eq_getD 16 15 (by omega)]; decide

theorem tau_seventeen : tau 17 = -6905934 := by
  change tauOf 16 = -6905934
  rw [tauOf_eq_getD 17 16 (by omega)]; decide

theorem tau_eighteen : tau 18 = 2727432 := by
  change tauOf 17 = 2727432
  rw [tauOf_eq_getD 18 17 (by omega)]; decide

theorem tau_nineteen : tau 19 = 10661420 := by
  change tauOf 18 = 10661420
  rw [tauOf_eq_getD 19 18 (by omega)]; decide

theorem tau_twenty : tau 20 = -7109760 := by
  change tauOf 19 = -7109760
  rw [tauOf_eq_getD 20 19 (by omega)]; decide

theorem tau_twenty_one : tau 21 = -4219488 := by
  change tauOf 20 = -4219488
  rw [tauOf_eq_getD 21 20 (by omega)]; decide

end Ramanujan
