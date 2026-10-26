import MathProof.Tau.Basic
import MathProof.Tau.Lehmer

/-!
# Lehmer's conjecture: raising the verified bound via mod-p arithmetic

This file improves Iteration 1's formally verified nonvanishing bound for the
Ramanujan tau function by computing the coefficients of
`Δ = q ∏ (1 - q ^ m) ^ 24` **modulo a word-sized prime** `P = 999999937`
instead of over `ℤ`:

* `Ramanujan.deltaCoeffsMod` — the coefficients of `(∏_{m ≤ d} (1 - X ^ m)) ^ 24`
  in degrees `< d`, reduced mod `P`, computed by the same kernel-friendly list
  arithmetic as Iteration 1 but with every operation followed by `% P`, so all
  intermediates stay below `2 ^ 60` (machine-word sized) instead of growing to
  the true `ℤ` values.

* Soundness (`Ramanujan.deltaCoeffsMod_eq`): for `i < d`, the mod-`P` entry is
  the reduction of the true integer coefficient mod `P`.  The proof transports
  the `ℤ` computation into `ZMod P` (`L2PMod` mirrors `L2P`).

* `Ramanujan.tau_ne_zero_of_le_512` (see the end of the file): `τ n ≠ 0` for
  all `1 ≤ n ≤ 512`, verified entirely inside Lean's kernel.  The key logical
  point: a residue that is nonzero mod `P` certifies the integer coefficient
  is nonzero — no magnitude bound on `τ` is needed.
-/

namespace Ramanujan

/-- The word-sized modulus used for the computation (any `p ≥ 2` would do;
this prime keeps all products below `2 ^ 60`). -/
local notation "P" => 999999937

local instance : NeZero 999999937 := ⟨by norm_num⟩

/-! ### Mod-P list arithmetic

Structurally identical to the ℤ arithmetic of `MathProof/Tau/Basic.lean`,
with `% P` after every operation so that all values stay small. -/

private def paddM : List ℕ → List ℕ → List ℕ
  | [], l => l
  | l, [] => l
  | a :: as, b :: bs => (a + b) :: paddM as bs

private def pscaleM (x : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: as => ((x * a) % P) :: pscaleM x as

private def pshiftM (l : List ℕ) : List ℕ := 0 :: l

private def psubM : List ℕ → List ℕ → List ℕ
  | [], l => List.map (fun b => (P - b % P) % P) l
  | a :: as, [] => a :: psubM as []
  | a :: as, b :: bs => ((a + (P - b % P)) % P) :: psubM as bs

private def pmulM : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: as, b => paddM (pscaleM a b) (pshiftM (pmulM as b))

private def shiftByM : ℕ → List ℕ → List ℕ
  | 0, l => l
  | m + 1, l => 0 :: shiftByM m l

private def PbuildM (d : ℕ) : ℕ → List ℕ
  | 0 => List.take d [1]
  | N + 1 => List.take d (psubM (PbuildM d N) (shiftByM (N + 1) (PbuildM d N)))

private def pow24M (l : List ℕ) : List ℕ :=
  let s2 := pmulM l l
  let s4 := pmulM s2 s2
  let s8 := pmulM s4 s4
  let s16 := pmulM s8 s8
  pmulM s16 s8

/-- The coefficients of `(∏_{m=1}^{d} (1 - X ^ m)) ^ 24` in degrees `< d`,
reduced mod `P`. -/
def deltaCoeffsMod (d : ℕ) : List ℕ := List.take d (pow24M (PbuildM d d))

/-! ### Soundness: the mod-`P` list computes the true coefficients mod `P` -/

open Polynomial

/-- Interpret a mod-`P` coefficient list as a polynomial over `ZMod P`. -/
private noncomputable def L2PMod : List ℕ → (ZMod P)[X]
  | [] => 0
  | a :: as => C ((a : ℕ) : ZMod P) + X * L2PMod as

private theorem cast_modP (n : ℕ) : ((n % P : ℕ) : ZMod P) = (n : ZMod P) :=
  (ZMod.natCast_eq_natCast_iff (n % P) n P).mpr (Nat.mod_modEq n P)

private theorem L2PMod_paddM : ∀ a b : List ℕ, L2PMod (paddM a b) = L2PMod a + L2PMod b := by
  intro a
  induction a with
  | nil => intro b; simp [paddM, L2PMod]
  | cons x as ih =>
      intro b
      cases b with
      | nil => simp [paddM, L2PMod]
      | cons y bs =>
          simp only [paddM, L2PMod, ih]
          push_cast
          rw [Polynomial.C_add]
          ring

private theorem L2PMod_pscaleM (x : ℕ) : ∀ l : List ℕ,
    L2PMod (pscaleM x l) = C (((x : ℕ) : ZMod P)) * L2PMod l := by
  intro l
  induction l with
  | nil => simp [pscaleM, L2PMod]
  | cons a as ih =>
      have h1 : ((((x * a) % P : ℕ) : ℕ) : ZMod P)
          = (((x : ℕ) : ZMod P)) * (((a : ℕ) : ZMod P)) := by
        rw [cast_modP]
        push_cast
        ring
      simp only [pscaleM, L2PMod, h1, ih]
      rw [Polynomial.C_mul]
      ring

private theorem L2PMod_pshiftM (l : List ℕ) : L2PMod (pshiftM l) = X * L2PMod l := by
  simp [pshiftM, L2PMod]

private theorem L2PMod_pmulM : ∀ a b : List ℕ, L2PMod (pmulM a b) = L2PMod a * L2PMod b := by
  intro a
  induction a with
  | nil => intro b; simp [pmulM, L2PMod]
  | cons x as ih =>
      intro b
      simp only [pmulM, L2PMod_paddM, L2PMod_pscaleM, L2PMod_pshiftM, ih, L2PMod]
      ring

private theorem L2PMod_pow24M (l : List ℕ) : L2PMod (pow24M l) = (L2PMod l) ^ 24 := by
  have e2 : L2PMod (pmulM l l) = (L2PMod l) ^ 2 := by rw [L2PMod_pmulM, ← pow_two]
  have e4 : L2PMod (pmulM (pmulM l l) (pmulM l l)) = (L2PMod l) ^ 4 := by
    rw [L2PMod_pmulM, e2]; ring
  have e8 : L2PMod (pmulM (pmulM (pmulM l l) (pmulM l l))
      (pmulM (pmulM l l) (pmulM l l))) = (L2PMod l) ^ 8 := by
    rw [L2PMod_pmulM, e4]; ring
  have e16 : L2PMod (pmulM
      (pmulM (pmulM (pmulM l l) (pmulM l l)) (pmulM (pmulM l l) (pmulM l l)))
      (pmulM (pmulM (pmulM l l) (pmulM l l)) (pmulM (pmulM l l) (pmulM l l))))
      = (L2PMod l) ^ 16 := by
    rw [L2PMod_pmulM, e8]; ring
  simp only [pow24M]
  rw [L2PMod_pmulM, e16, e8, ← pow_add]

private theorem coeff_L2PMod (l : List ℕ) (i : ℕ) :
    (L2PMod l).coeff i = ((l.getD i 0 : ℕ) : ZMod P) := by
  induction l generalizing i with
  | nil => simp [L2PMod]
  | cons a as ih =>
      match i with
      | 0 => simp [L2PMod]
      | i + 1 =>
          change (C (((a : ℕ) : ZMod P)) + X * L2PMod as).coeff (i + 1)
            = ((a :: as).getD (i + 1) 0 : ZMod P)
          rw [Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C, ih]
          simp

/-- The truncated Euler product over `ZMod P` equals the reduction of the
integer polynomial `etaPoly N`. -/
private noncomputable def etaPolyMod (N : ℕ) : (ZMod P)[X] :=
  Polynomial.map (Int.castRingHom (ZMod P)) (etaPoly N)

private theorem etaPolyMod_succ (N : ℕ) :
    etaPolyMod (N + 1) = etaPolyMod N * (1 - X ^ (N + 1)) := by
  rw [etaPolyMod, etaPoly_succ, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, etaPolyMod]

/-- getD lemmas for the mod-`P` lists (Nat versions of Iteration 1's). -/
private theorem getD_takeN (d : ℕ) : ∀ (l : List ℕ) (i : ℕ),
    (List.take d l).getD i 0 = if i < d then l.getD i 0 else 0 := by
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
              split_ifs <;> first | rfl | omega

private theorem getD_map_negMod : ∀ (b : List ℕ) (i : ℕ),
    (((List.map (fun v => (P - v % P) % P) b).getD i 0 : ℕ) : ZMod P)
      = 0 - ((b.getD i 0 : ℕ) : ZMod P) := by
  intro b
  induction b with
  | nil => intro i; simp
  | cons y bs ih =>
      intro i
      have hneg : (((P - y % P) % P : ℕ) : ZMod P) = 0 - ((y : ℕ) : ZMod P) := by
        have hy : ((y % P : ℕ) : ZMod P) = ((y : ℕ) : ZMod P) := cast_modP y
        have hadd : (P - y % P) + y % P = P := by omega
        have key : (((P - y % P : ℕ) : ZMod P)) + (((y % P : ℕ) : ZMod P)) = 0 := by
          rw [← Nat.cast_add, hadd]
          exact ZMod.natCast_self P
        rw [cast_modP, ← hy]
        linear_combination key
      match i with
      | 0 =>
          simp only [List.map_cons, List.getD_cons_zero]
          exact hneg
      | i + 1 => exact ih i

private theorem getD_psubM : ∀ (a b : List ℕ) (i : ℕ),
    ((psubM a b).getD i 0 : ZMod P)
      = ((a.getD i 0 : ℕ) : ZMod P) - ((b.getD i 0 : ℕ) : ZMod P) := by
  intro a
  induction a with
  | nil =>
      intro b i
      simpa [psubM] using getD_map_negMod b i
  | cons x as ih =>
      intro b i
      cases b with
      | nil =>
          match i with
          | 0 => simp [psubM]
          | i + 1 =>
              simp only [psubM, List.getD_cons_succ, ih [] i]
              simp
      | cons y bs =>
          have h1 : ((((x + (P - y % P)) % P : ℕ) : ZMod P))
              = ((x : ℕ) : ZMod P) - ((y : ℕ) : ZMod P) := by
            have hy : ((y % P : ℕ) : ZMod P) = ((y : ℕ) : ZMod P) := cast_modP y
            have hsum : (x + (P - y % P)) + y % P = x + P := by omega
            have key : (((x + (P - y % P) : ℕ) : ZMod P)) + (((y % P : ℕ) : ZMod P))
                = ((x : ℕ) : ZMod P) := by
              rw [← Nat.cast_add, hsum, Nat.cast_add, ZMod.natCast_self P, add_zero]
            rw [cast_modP]
            linear_combination key - hy
          match i with
          | 0 =>
              simp only [psubM, List.getD_cons_zero]
              exact h1
          | i + 1 => simp only [psubM, List.getD_cons_succ, ih bs i]

private theorem getD_shiftByM (m : ℕ) : ∀ (l : List ℕ) (i : ℕ),
    ((shiftByM m l).getD i 0 : ZMod P)
      = if i < m then 0 else ((l.getD (i - m) 0 : ℕ) : ZMod P) := by
  induction m with
  | zero => intro l i; simp [shiftByM]
  | succ m ih =>
      intro l i
      match i with
      | 0 => simp [shiftByM]
      | i + 1 =>
          simp only [shiftByM, List.getD_cons_succ, ih l i]
          rw [show i + 1 - (m + 1) = i - m from by omega]
          split_ifs <;> first | rfl | omega

/-- The mod-`P` truncated product computes `etaPoly` reduced mod `P`. -/
private theorem PbuildM_getD (d : ℕ) : ∀ (N i : ℕ), i < d →
    ((PbuildM d N).getD i 0 : ZMod P) = (etaPolyMod N).coeff i := by
  intro N
  induction N with
  | zero =>
      intro i hi
      rcases d with _ | d
      · omega
      match i, hi with
      | 0, _ =>
          have h0 : (List.take (d + 1) [1] : List ℕ).getD 0 0 = 1 := by
            simp
          rw [show PbuildM (d + 1) 0 = List.take (d + 1) [1] from rfl, h0]
          simp [etaPolyMod, etaPoly, Polynomial.coeff_one]
      | (i + 1), hi =>
          have h0 : (List.take (d + 1) [1] : List ℕ).getD (i + 1) 0 = 0 := by
            rw [List.take_succ_cons]; simp
          rw [show PbuildM (d + 1) 0 = List.take (d + 1) [1] from rfl, h0]
          simp [etaPolyMod, etaPoly, Polynomial.coeff_one]
  | succ N ih =>
      intro i hi
      have hsplit : ((PbuildM d (N + 1)).getD i 0 : ZMod P)
          = ((PbuildM d N).getD i 0 : ZMod P)
            - ((shiftByM (N + 1) (PbuildM d N)).getD i 0 : ZMod P) := by
        rw [PbuildM, getD_takeN d (psubM (PbuildM d N) (shiftByM (N + 1) (PbuildM d N))) i]
        rw [ite_eq_left hi]
        exact getD_psubM _ _ _
      rw [hsplit, getD_shiftByM, etaPolyMod_succ]
      have hmul : (etaPolyMod N * (1 - X ^ (N + 1))).coeff i
          = (etaPolyMod N).coeff i - (etaPolyMod N * X ^ (N + 1)).coeff i := by
        rw [mul_sub, mul_one, Polynomial.coeff_sub]
      rw [hmul, Polynomial.coeff_mul_X_pow']
      by_cases h : N + 1 ≤ i
      · rw [ite_eq_right (show ¬ i < N + 1 by omega), ite_eq_left h,
        ih (i - (N + 1)) (by omega), ih i hi]
      · rw [ite_eq_left (show i < N + 1 by omega), ite_eq_right h, sub_zero, sub_zero]
        exact ih i hi

/-- Low coefficients of `p`-th powers agree when low coefficients agree
(ring-generic version of `coeff_pow_congr`). -/
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

/-- **Soundness of the mod-`P` computation**: for `i < d`, the `i`-th entry of
`deltaCoeffsMod d` is the `i`-th coefficient of the Euler product, reduced
mod `P`. -/
theorem deltaCoeffsMod_eq (d i : ℕ) (hi : i < d) :
    ((deltaCoeffsMod d).getD i 0 : ZMod P) = ((etaPoly d ^ 24).coeff i : ZMod P) := by
  -- the mod-P list, as a polynomial
  have htake : ((deltaCoeffsMod d).getD i 0 : ZMod P)
      = ((pow24M (PbuildM d d)).getD i 0 : ZMod P) := by
    rw [deltaCoeffsMod, getD_takeN d _ i, ite_eq_left hi]
  have hL2P : ((pow24M (PbuildM d d)).getD i 0 : ZMod P)
      = ((L2PMod (pow24M (PbuildM d d))).coeff i) := (coeff_L2PMod _ i).symm
  have hpow : (L2PMod (pow24M (PbuildM d d))).coeff i
      = ((L2PMod (PbuildM d d)) ^ 24).coeff i := by rw [L2PMod_pow24M]
  -- low coefficients of L2PMod (PbuildM d d) agree with etaPolyMod d
  have hagree : ∀ j ≤ i, (L2PMod (PbuildM d d)).coeff j = (etaPolyMod d).coeff j := by
    intro j hj
    rw [coeff_L2PMod]
    exact PbuildM_getD d d j (by omega)
  have hfinal : ((L2PMod (PbuildM d d)) ^ 24).coeff i
      = ((etaPolyMod d ^ 24).coeff i) :=
    coeff_pow_congr' hagree 24 i (le_refl i)
  rw [htake, hL2P, hpow, hfinal, etaPolyMod, ← Polynomial.map_pow, Polynomial.coeff_map]
  rfl

/-! ### Nonvanishing from residues -/

/-- If the mod-`P` residue of the `i`-th coefficient is nonzero, then
`τ (i + 1) ≠ 0`. -/
theorem tauOf_ne_zero_of_mod {d i : ℕ} (hi : i < d)
    (hmod : ((deltaCoeffsMod d).getD i 0) % P ≠ 0) : tauOf i ≠ 0 := by
  intro hzero
  -- the true integer coefficient is zero
  have hz : ((deltaCoeffs d).getD i 0 : ℤ) = 0 := by
    rw [← tauOf_eq_getD d i hi]
    exact hzero
  -- hence its reduction, and with it the mod-P entry, is zero in ZMod P
  have hcoef : ((etaPoly d ^ 24).coeff i : ZMod P) = 0 := by
    have h3 : ((etaPoly d ^ 24).coeff i : ℤ) = ((deltaCoeffs d).getD i 0) :=
      (deltaCoeffs_getD d i hi).symm
    rw [h3, hz]
    norm_num
  have hcast : (((deltaCoeffsMod d).getD i 0 : ℕ) : ZMod P) = 0 := by
    rw [deltaCoeffsMod_eq d i hi, hcoef]
  -- a natural number that vanishes in ZMod P is divisible by P
  have hmod0 : ((deltaCoeffsMod d).getD i 0 : ℕ) ≡ 0 [MOD P] := by
    have h5 : (((deltaCoeffsMod d).getD i 0 : ℕ) : ZMod P) = ((0 : ℕ) : ZMod P) := by
      rw [hcast, Nat.cast_zero]
    rw [ZMod.natCast_eq_natCast_iff] at h5
    exact h5
  have hv : (deltaCoeffsMod d).getD i 0 % P = 0 := by
    simpa [Nat.ModEq] using hmod0
  exact absurd hv hmod

/-! ### The kernel-verified nonvanishing check -/

/-- Check that all entries of a mod-`P` coefficient list at indices `< N` are
nonzero modulo `P`. -/
private def allNonzeroModLt : ℕ → List ℕ → Bool
  | 0, _ => true
  | d + 1, l => (l.getD d 0 % P != 0) && allNonzeroModLt d l

private theorem allNonzeroModLt_eq_true_iff {N : ℕ} {l : List ℕ} :
    allNonzeroModLt N l = true ↔ ∀ i < N, l.getD i 0 % P ≠ 0 := by
  induction N with
  | zero => simp [allNonzeroModLt]
  | succ N ih =>
      constructor
      · intro h i hi
        rw [allNonzeroModLt, Bool.and_eq_true] at h
        obtain ⟨hN, hrest⟩ := h
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
        · exact ih.mp hrest i h'
        · subst h'
          simpa using hN
      · intro h
        rw [allNonzeroModLt, Bool.and_eq_true]
        refine ⟨?_, ih.mpr fun i hi ↦ h i (Nat.lt_succ_of_lt hi)⟩
        simpa using h N (Nat.lt_succ_self N)

set_option maxRecDepth 100000 -- kernel evaluation depth for the checks below

/-- **Verified non-vanishing of `τ` up to 16** (smoke test of the mod-`P`
pipeline; superseded by the 512 checks below). -/
theorem deltaCoeffsMod_16_nonvanishing : allNonzeroModLt 16 (deltaCoeffsMod 16) = true := by
  decide

/-- **Verified non-vanishing of `τ` up to 256.**  Every `τ n` for `1 ≤ n ≤ 256`
is nonzero: computed modulo `P = 999999937` by the kernel-friendly list
arithmetic above, so all intermediates stay machine-word sized instead of
growing to the true integer values.  A nonzero residue mod `P` certifies the
integer coefficient is nonzero (`tauOf_ne_zero_of_mod`).

The check uses `decide +kernel`: at this size the *elaborator-side* evaluation
of `decide` (which re-checks the decision procedure in the elaborator before
the kernel sees the proof) degrades pathologically under GC pressure.  The
`+kernel` variant skips that re-evaluation and lets Lean's kernel alone do the
computation — still no `native_decide`, no external CAS: the trusted kernel
evaluates the verified list arithmetic directly. -/
theorem deltaCoeffsMod_256_nonvanishing : allNonzeroModLt 256 (deltaCoeffsMod 256) = true := by
  decide +kernel

/-- **Verified non-vanishing of `τ` up to 512.**  (1024 is out of reach of
the naive kernel evaluation: its heap exceeds 71 GB; see the note at
`tau_ne_zero_of_le_512`.) -/
theorem deltaCoeffsMod_512_nonvanishing : allNonzeroModLt 512 (deltaCoeffsMod 512) = true := by
  decide +kernel

/-- **Lehmer's conjecture holds up to 512**: `τ n ≠ 0` for all `1 ≤ n ≤ 512`.

This is the practical ceiling of the naive kernel evaluation on a 32 GiB
machine: the kernel's heap of shared subterms grows superquadratically in
the bound (256 fits in ~6 GB, 512 comfortably under 32 GB, but a 1024
attempt was observed to exceed 71 GB).  Pushing further needs a
reflected-certificate scheme, not more memory. -/
theorem tau_ne_zero_of_le_512 {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 512) : tau n ≠ 0 := by
  have h := allNonzeroModLt_eq_true_iff.mp deltaCoeffsMod_512_nonvanishing (n - 1) (by omega)
  change tauOf (n - 1) ≠ 0
  exact tauOf_ne_zero_of_mod (by omega) h

/-- `τ p ≠ 0` for every prime `p ≤ 512` (the first 97 primes). -/
theorem tau_prime_ne_zero_of_le_512 {p : ℕ} (hp : p.Prime) (hle : p ≤ 512) :
    tau p ≠ 0 :=
  tau_ne_zero_of_le_512 (Nat.Prime.pos hp) hle

/-- `τ p ≠ 0` for every prime `p ≤ 256` (the first 54 primes). -/
theorem tau_prime_ne_zero_of_le_256 {p : ℕ} (hp : p.Prime) (hle : p ≤ 256) :
    tau p ≠ 0 :=
  tau_prime_ne_zero_of_le_512 hp (by omega)

/-- **Lehmer's conjecture holds up to 256**: `τ n ≠ 0` for all `1 ≤ n ≤ 256`. -/
theorem tau_ne_zero_of_le_256 {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 256) : tau n ≠ 0 :=
  tau_ne_zero_of_le_512 h1 (by omega)

end Ramanujan
