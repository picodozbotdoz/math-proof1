import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# The Hecke operator `T_p` on level-one modular forms

For a prime `p` and an integer weight `k` we define, for `f : ℍ → ℂ`,

    T_p f (z) = p⁻¹ • Σ_{j < p} f((z + j) / p) + p ^ (k - 1) • f (p • z),

the weight-`k` Hecke operator `T_p` for the full modular group, and prove:

* `heckeTPFun_slash_invariant`: `T_p f` is again slash-invariant of weight `k`
  under `SL(2, ℤ)` whenever `f` is (T- and S-invariance; S-invariance uses the
  explicit factorization `[j, -(jj'+1)/p]; [p, -j']` of the coset
  representatives, where `j j' ≡ -1 [MOD p]`);
* `heckeTP` acts on `ModularForm 𝒮ℒ k` and on `CuspForm 𝒮ℒ k`;
* `heckeTP_qExpansion_coeff`: `(T_p f)_m = f_{p m} + p ^ (k-1) • (if p ∣ m then f_{m/p} else 0)`.

This is the operator-level input to Mordell's theorem on the Ramanujan τ
function (`MathProof/Tau/Mordell.lean`): since `S₁₂(SL(2,ℤ))` is
one-dimensional, `T_p Δ = τ(p) • Δ`, and comparing coefficients gives
`τ(p n) = τ(p) τ(n)` for `p ∤ n` and the two-term recursion for `τ(p^r)`.
-/

open UpperHalfPlane ModularForm CuspForm Filter Function Periodic
open scoped MatrixGroups

namespace HeckeLevelOne

local notation "𝕢" => Periodic.qParam

/-! ### Padding `HasSum`s along the multiples of `p` -/

section Pad

variable {p : ℕ} {u : ℕ → ℂ} {L : ℂ}

private lemma mulLeft_injective (hp : 0 < p) : Function.Injective (fun m : ℕ => p * m) :=
  fun a b h => Nat.eq_of_mul_eq_mul_left hp h

/-- The family `u`, reindexed onto the multiples of `p` and extended by `0`. -/
lemma paddedEq (hp : 0 < p) :
    (fun n => if p ∣ n then u (n / p) else 0) = Function.extend (fun m => p * m) u 0 := by
  funext n
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have h1 : Function.extend (fun m => p * m) u 0 (p * m) = u m :=
      Function.Injective.extend_apply (f := fun m => p * m) (mulLeft_injective hp) u 0 m
    rw [h1, Nat.mul_div_cancel_left _ hp]
    simp [dvd_mul_right]
  · have h1 : Function.extend (fun m => p * m) u 0 n = 0 :=
      Function.extend_apply' (f := fun m => p * m) u 0 n
        (by rintro ⟨x, hx⟩; exact hpn ⟨x, hx.symm⟩)
    rw [h1]
    simp [hpn]

/-- If `u` has sum `L`, its extension by `0` off the multiples of `p` has sum `L`. -/
theorem hasSum_padMul (hp : 0 < p) (h : HasSum u L) :
    HasSum (fun n => if p ∣ n then u (n / p) else 0) L := by
  rw [paddedEq hp]
  exact hasSum_extend_zero (g := fun m => p * m) (mulLeft_injective hp) |>.mpr h

/-- Conversely, if the extension of `u` off the multiples of `p` has sum `L`, so does `u`. -/
theorem hasSum_unpadMul (hp : 0 < p) (h : HasSum (fun n => if p ∣ n then u (n / p) else 0) L) :
    HasSum u L := by
  rw [paddedEq hp] at h
  exact hasSum_extend_zero (g := fun m => p * m) (mulLeft_injective hp) |>.mp h

end Pad

/-! ### Points of ℍ and the operator `T_p` -/

section Points

variable {k : ℤ} {p : ℕ} {f : ℍ → ℂ}

lemma im_div_natCast (x : ℂ) (j : ℕ) {p : ℕ} (hp : 0 < p) :
    Complex.im ((x + (j : ℂ)) / (p : ℂ)) = x.im / p := by
  rw [Complex.div_natCast_im, Complex.add_im, Complex.natCast_im, add_zero]

/-- `(z + j) / p` as a point of the upper half-plane (`0 < p`). -/
noncomputable def shiftDivP {p : ℕ} (hp : 0 < p) (j : ℕ) (z : ℍ) : ℍ :=
  ⟨((z : ℂ) + j) / (p : ℂ), by
    rw [im_div_natCast (z : ℂ) j hp]
    exact div_pos z.im_pos (by exact_mod_cast hp)⟩

/-- `p • z` as a point of the upper half-plane (`0 < p`). -/
noncomputable def mulP {p : ℕ} (hp : 0 < p) (z : ℍ) : ℍ :=
  ⟨(p : ℂ) * z, by
    rw [← Complex.ofReal_natCast p, Complex.im_ofReal_mul]
    exact mul_pos (by exact_mod_cast hp) z.im_pos⟩

@[simp, norm_cast]
lemma coe_shiftDivP {p : ℕ} (hp : 0 < p) (j : ℕ) (z : ℍ) :
    ((shiftDivP hp j z : ℍ) : ℂ) = ((z : ℂ) + j) / (p : ℂ) := rfl

@[simp, norm_cast]
lemma coe_mulP {p : ℕ} (hp : 0 < p) (z : ℍ) : ((mulP hp z : ℍ) : ℂ) = (p : ℂ) * z := rfl

/-- The Hecke operator `T_p` on functions `ℍ → ℂ` (any `p ≥ 1`, any weight `k`). -/
noncomputable def heckeTPFun {p : ℕ} (hp : 0 < p) (k : ℤ) (f : ℍ → ℂ) : ℍ → ℂ := fun z =>
  (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (shiftDivP hp j z) + (p : ℂ) ^ (k - 1) * f (mulP hp z)

lemma heckeTPFun_apply {p : ℕ} (hp : 0 < p) (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    heckeTPFun hp k f z
      = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (shiftDivP hp j z)
        + (p : ℂ) ^ (k - 1) * f (mulP hp z) := rfl

lemma heckeTPFun_add {p : ℕ} (hp : 0 < p) (k : ℤ) (f g : ℍ → ℂ) :
    heckeTPFun hp k (f + g) = heckeTPFun hp k f + heckeTPFun hp k g := by
  funext z
  simp only [heckeTPFun_apply, Pi.add_apply, Finset.sum_add_distrib]
  ring

lemma heckeTPFun_smul {p : ℕ} (hp : 0 < p) (k : ℤ) (c : ℂ) (f : ℍ → ℂ) :
    heckeTPFun hp k (c • f) = c • heckeTPFun hp k f := by
  funext z
  have h1 : ((p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, (c * f (shiftDivP hp j z)))
      = (p : ℂ)⁻¹ * c * ∑ j ∈ Finset.range p, f (shiftDivP hp j z) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [heckeTPFun_apply, Pi.smul_apply, smul_eq_mul, h1]
  ring

end Points

/-! ### Weight-`k` invariance under `SL(2, ℤ)` -/

section Invariance

variable {k : ℤ} {p : ℕ} {f : ℍ → ℂ}

/-- Pointwise slash invariance of weight `k` under `SL(2, ℤ)`, in the form
`f (γ • z) = (γ 1 0 * z + γ 1 1) ^ k * f z`. -/
def IsSlashInvariantSL (k : ℤ) (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), ∀ z : ℍ, f (γ • z) = denom (γ : GL (Fin 2) ℝ) z ^ k * f z

lemma denomSL_apply (γ : SL(2, ℤ)) (z : ℍ) :
    denom (γ : GL (Fin 2) ℝ) z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := rfl

lemma coe_smul_SL_int (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) =
      (((γ 0 0 : ℤ) : ℂ) * z + (γ 0 1 : ℤ)) /
      (((γ 1 0 : ℤ) : ℂ) * z + (γ 1 1 : ℤ)) := by
  rw [coe_specialLinearGroup_apply]
  rfl

/-- Point formula for an `SL(2, ℤ)`-translate with entries supplied as opaque integers. -/
lemma coe_smul_SL_int' {γ : SL(2, ℤ)} {a b c d : ℤ} (w : ℍ)
    (h00 : (γ 0 0) = a) (h01 : (γ 0 1) = b) (h10 : (γ 1 0) = c) (h11 : (γ 1 1) = d) :
    ((γ • w : ℍ) : ℂ) =
      ((((a : ℤ) : ℂ)) * (w : ℂ) + ((b : ℤ) : ℂ)) /
      ((((c : ℤ) : ℂ)) * (w : ℂ) + ((d : ℤ) : ℂ)) := by
  rw [coe_smul_SL_int γ w, h00, h01, h10, h11]

lemma coe_ne_zero (z : ℍ) : (z : ℂ) ≠ 0 := by
  intro h
  apply z.im_pos.ne'
  have h2 : (z : ℂ).im = 0 := by rw [h, Complex.zero_im]
  simpa using h2

lemma coe_smul_T_zpow (n : ℤ) (w : ℍ) :
    ((ModularGroup.T ^ n • w : ℍ) : ℂ) = (w : ℂ) + n := by
  have h := congrArg UpperHalfPlane.coe (modular_T_zpow_smul w n)
  rw [coe_vadd, add_comm] at h
  exact h

lemma coe_smul_S (w : ℍ) : ((ModularGroup.S • w : ℍ) : ℂ) = -(w : ℂ)⁻¹ := by
  simpa using congrArg UpperHalfPlane.coe (modular_S_smul w)

lemma S_entries :
    ((ModularGroup.S : SL(2, ℤ)) 0 0 : ℤ) = 0 ∧ ((ModularGroup.S : SL(2, ℤ)) 0 1 : ℤ) = -1 ∧
    ((ModularGroup.S : SL(2, ℤ)) 1 0 : ℤ) = 1 ∧ ((ModularGroup.S : SL(2, ℤ)) 1 1 : ℤ) = 0 := by
  simp [ModularGroup.S]

/-- Translation invariance of a slash-invariant function. -/
lemma IsSlashInvariantSL.f_eq_of_coe_add_int (hf : IsSlashInvariantSL k f) (n : ℤ) (w w' : ℍ)
    (hcoe : (w' : ℂ) = (w : ℂ) + n) : f w' = f w := by
  have h1 : ((ModularGroup.T ^ n) • w : ℍ) = w' := by
    rw [UpperHalfPlane.ext_iff, coe_smul_T_zpow, hcoe]
  have hd : denom ((ModularGroup.T ^ n : SL(2, ℤ)) : GL (Fin 2) ℝ) w = 1 := by
    have e10 : ((ModularGroup.T ^ n : SL(2, ℤ)) 1 0 : ℤ) = 0 := by
      rw [show ((ModularGroup.T ^ n : SL(2, ℤ)) 1 0) =
        ((ModularGroup.T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 from rfl,
        ModularGroup.coe_T_zpow]
      rfl
    have e11 : ((ModularGroup.T ^ n : SL(2, ℤ)) 1 1 : ℤ) = 1 := by
      rw [show ((ModularGroup.T ^ n : SL(2, ℤ)) 1 1) =
        ((ModularGroup.T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 from rfl,
        ModularGroup.coe_T_zpow]
      rfl
    rw [denomSL_apply, e10, e11]
    simp
  have h2 := hf (ModularGroup.T ^ n) w
  rw [hd, one_zpow, one_mul] at h2
  rw [← h1, h2]

/-! ### T-invariance -/

lemma sum_shift_one {p : ℕ} (hp : 0 < p) (F : ℕ → ℂ) (hF : ∀ j, F (j + p) = F j) :
    ∑ j ∈ Finset.range p, F (j + 1) = ∑ j ∈ Finset.range p, F j := by
  have key : ∑ j ∈ Finset.Ico 1 (1 + p), F j = ∑ j ∈ Finset.range p, F (1 + j) := by
    have h := Finset.sum_Ico_eq_sum_range F 1 (1 + p)
    rw [show 1 + p - 1 = p from by omega] at h
    exact h
  have h1 : ∑ j ∈ Finset.range p, F (j + 1) = ∑ j ∈ Finset.Ico 1 (1 + p), F j := by
    rw [key]
    exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm j 1]
  have h2 : Finset.Ico 1 (1 + p) = insert p (Finset.Ico 1 p) := by
    rw [add_comm]
    exact Nat.Ico_succ_right_eq_insert_Ico (a := 1) (b := p) (by omega)
  have h3 : ∑ j ∈ Finset.Ico 1 p, F j = ∑ j ∈ Finset.range p, F j - F 0 := by
    have hmem : 0 ∈ Finset.Ico 0 p := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have hI : Finset.Ico (Nat.succ 0) p = Finset.erase (Finset.Ico 0 p) 0 :=
      Nat.Ico_succ_left_eq_erase_Ico
    rw [show (1 : ℕ) = Nat.succ 0 from rfl, hI, Finset.sum_erase_eq_sub hmem, ← Finset.range_eq_Ico]
  rw [h1, h2, Finset.sum_insert (by simp), h3]
  have h5 : F p = F 0 := by rw [← hF 0, Nat.zero_add]
  rw [h5]
  abel

theorem heckeTPFun_T (hp : 0 < p) (hf : IsSlashInvariantSL k f) (z : ℍ) :
    heckeTPFun hp k f (ModularGroup.T • z) = heckeTPFun hp k f z := by
  have hTz : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
    have h0 := coe_smul_T_zpow 1 z
    rwa [zpow_one, Int.cast_one] at h0
  have hsum : ∑ j ∈ Finset.range p, f (shiftDivP hp j (ModularGroup.T • z))
      = ∑ j ∈ Finset.range p, f (shiftDivP hp j z) := by
    have hshift : ∀ j ∈ Finset.range p, f (shiftDivP hp j (ModularGroup.T • z))
        = f (shiftDivP hp (j + 1) z) := by
      intro j _
      have hpt : (shiftDivP hp j (ModularGroup.T • z) : ℍ) = shiftDivP hp (j + 1) z := by
        rw [UpperHalfPlane.ext_iff, coe_shiftDivP, coe_shiftDivP, hTz,
          div_eq_div_iff (by exact_mod_cast hp.ne' : ((p : ℂ)) ≠ 0)
            (by exact_mod_cast hp.ne' : ((p : ℂ)) ≠ 0)]
        push_cast
        ring
      rw [hpt]
    rw [Finset.sum_congr rfl (fun j hj => hshift j hj)]
    refine sum_shift_one hp (fun j => f (shiftDivP hp j z)) ?_
    intro j
    refine hf.f_eq_of_coe_add_int (n := 1) (w := shiftDivP hp j z)
      (w' := shiftDivP hp (j + p) z) ?_
    rw [coe_shiftDivP, coe_shiftDivP]
    have hjp : ((j + p : ℕ) : ℂ) = (j : ℂ) + (p : ℂ) := by
      push_cast
      ring
    rw [hjp, ← add_assoc, add_div, div_self (by exact_mod_cast hp.ne' : ((p : ℂ)) ≠ 0)]
    norm_num
  have hmul : f (mulP hp (ModularGroup.T • z)) = f (mulP hp z) := by
    refine hf.f_eq_of_coe_add_int (n := (p : ℤ)) (w := mulP hp z)
      (w' := mulP hp (ModularGroup.T • z)) ?_
    rw [coe_mulP, coe_mulP, hTz]
    push_cast
    ring
  rw [heckeTPFun_apply, heckeTPFun_apply, hsum, hmul]

/-! ### The involution `j ↦ -j⁻¹` of `[1, p-1]` and the coset factorization -/

section Sigma

variable {p j : ℕ}

/-- `-j⁻¹` in `ZMod p`, as a natural number. -/
def phiInv (p j : ℕ) : ℕ := (p - ((j : ZMod p)⁻¹.val)) % p

lemma phiInv_lt {p : ℕ} (hp : 0 < p) (j : ℕ) : phiInv p j < p := Nat.mod_lt _ hp

lemma phiInv_cast (hp : p.Prime) {j : ℕ} (hj : (j : ZMod p) ≠ 0) :
    ((phiInv p j : ℕ) : ZMod p) = -((j : ZMod p)⁻¹) := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hv : ((j : ZMod p)⁻¹.val) < p := ZMod.val_lt _
  have hv0 : ((j : ZMod p)⁻¹.val) ≠ 0 := by
    intro h0
    have huv : (((j : ZMod p)⁻¹ : ZMod p).val : ZMod p) = (j : ZMod p)⁻¹ := by
      simpa [ZMod.cast_id] using ZMod.natCast_val ((j : ZMod p)⁻¹)
    rw [h0] at huv
    have hzero : ((j : ZMod p)⁻¹) = 0 := by simpa using huv.symm
    exact hj (inv_eq_zero.mp hzero)
  have hmod : (p - ((j : ZMod p)⁻¹.val)) % p = p - ((j : ZMod p)⁻¹.val) :=
    Nat.mod_eq_of_lt (by omega)
  rw [phiInv, hmod]
  have hcast : ((p - ((j : ZMod p)⁻¹.val) : ℕ) : ZMod p)
      = ((p : ℕ) : ZMod p) - (((j : ZMod p)⁻¹.val : ℕ) : ZMod p) := by
    rw [Nat.cast_sub (le_of_lt hv)]
  rw [hcast, ZMod.natCast_self, zero_sub]
  congr 1
  simpa [ZMod.cast_id] using ZMod.natCast_val ((j : ZMod p)⁻¹)

lemma phiInv_cast_ne_zero (hp : p.Prime) {j : ℕ} (hj : (j : ZMod p) ≠ 0) :
    ((phiInv p j : ℕ) : ZMod p) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [phiInv_cast hp hj]
  exact neg_ne_zero.mpr (inv_ne_zero hj)

lemma phiInv_ne_zero (hp : p.Prime) {j : ℕ} (hj : (j : ZMod p) ≠ 0) :
    phiInv p j ≠ 0 := by
  intro h
  have hc := phiInv_cast_ne_zero hp hj
  rw [h, Nat.cast_zero] at hc
  exact hc rfl

lemma phiInv_dvd (hp : p.Prime) {j : ℕ} (hj : (j : ZMod p) ≠ 0) :
    p ∣ j * phiInv p j + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff (j * phiInv p j + 1) p]
  push_cast
  rw [phiInv_cast hp hj, mul_neg,
    show ((j : ZMod p) * ((j : ZMod p))⁻¹) = 1 from mul_inv_cancel₀ hj]
  simp

lemma phiInv_involution (hp : p.Prime) {j : ℕ} (hj : (j : ZMod p) ≠ 0) (hjlt : j < p) :
    phiInv p (phiInv p j) = j := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 := phiInv_cast hp (phiInv_cast_ne_zero hp hj)
  rw [phiInv_cast hp hj, inv_neg, inv_inv, neg_neg] at h1
  have h2 := congrArg ZMod.val h1
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (phiInv_lt hp.pos _),
    Nat.mod_eq_of_lt hjlt] at h2
  exact h2

lemma phiInv_mem_Icc (hp : p.Prime) {j : ℕ} (hj : (j : ZMod p) ≠ 0) :
    phiInv p j ∈ Finset.Icc 1 (p - 1) := by
  have h1 := phiInv_ne_zero hp hj
  have h2 := phiInv_lt hp.pos j
  simp only [Finset.mem_Icc]
  omega

lemma eq_zero_of_zmod_cast {p j : ℕ} (hjlt : j < p) (hj : (j : ZMod p) = 0) : j = 0 := by
  have hd : p ∣ j := (ZMod.natCast_eq_zero_iff j p).mp hj
  exact Nat.eq_zero_of_dvd_of_lt hd hjlt

/-- The matrix `[[j, -(j·j'+1)/p], [p, -j']] ∈ SL(2, ℤ)` (determinant `1` when `p ∣ j·j'+1`). -/
def sigmaMatrix (p j j' : ℕ) (hdiv : p ∣ j * j' + 1) : SL(2, ℤ) :=
  ⟨!![(j : ℤ), -(((j * j' + 1) / p : ℕ) : ℤ); (p : ℤ), -(j' : ℤ)], by
    have h1 : (((j * j' + 1) / p : ℕ) : ℤ) * (p : ℤ) = (j : ℤ) * (j' : ℤ) + 1 := by
      have h := Nat.mul_div_cancel' hdiv
      rw [mul_comm] at h
      exact_mod_cast h
    rw [Matrix.det_fin_two]
    show ((j : ℤ) * (-(j' : ℤ)) - (-(((j * j' + 1) / p : ℕ) : ℤ)) * (p : ℤ)) = 1
    linarith [h1]⟩

end Sigma

/-! ### S-invariance -/

theorem heckeTPFun_S (hp : p.Prime) (hf : IsSlashInvariantSL k f) (z : ℍ) :
    heckeTPFun hp.pos k f (ModularGroup.S • z) = (z : ℂ) ^ k * heckeTPFun hp.pos k f z := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hz : (z : ℂ) ≠ 0 := coe_ne_zero z
  have h1p : 1 < p := hp.one_lt
  -- split off the j = 0 term
  have hsplit : ∀ g : ℍ → ℂ, ∑ j ∈ Finset.range p, g (shiftDivP hp.pos j (ModularGroup.S • z))
      = g (shiftDivP hp.pos 0 (ModularGroup.S • z))
        + ∑ j ∈ Finset.Icc 1 (p - 1), g (shiftDivP hp.pos j (ModularGroup.S • z)) := by
    intro g
    rw [show Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) from
      (Finset.ext fun j => by
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega),
      Finset.sum_insert (by simp [Finset.mem_Icc])]
  -- the j = 0 term is governed by the S-invariance of f at the point `p • z`
  have hS0 : f (shiftDivP hp.pos 0 (ModularGroup.S • z))
      = (p : ℂ) ^ k * (z : ℂ) ^ k * f (mulP hp.pos z) := by
    have hpt : (shiftDivP hp.pos 0 (ModularGroup.S • z) : ℍ)
        = ModularGroup.S • (mulP hp.pos z) := by
      rw [UpperHalfPlane.ext_iff, coe_shiftDivP, coe_smul_S, coe_smul_S, coe_mulP]
      push_cast
      rw [add_zero, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hpt, hf ModularGroup.S (mulP hp.pos z)]
    obtain ⟨-, -, e10, e11⟩ := S_entries
    have hdS : denom ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) (mulP hp.pos z)
        = (p : ℂ) * z := by
      rw [denomSL_apply, e10, e11, coe_mulP]
      simp
    rw [hdS, mul_zpow]
  -- the j ≥ 1 terms are governed by the matrices σ_j
  have hSj : ∀ j ∈ Finset.Icc 1 (p - 1), f (shiftDivP hp.pos j (ModularGroup.S • z))
      = (z : ℂ) ^ k * f (shiftDivP hp.pos (phiInv p j) z) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hjlt : j < p := by omega
    have hjz : (j : ZMod p) ≠ 0 := by
      intro hd
      have h0 := eq_zero_of_zmod_cast hjlt hd
      omega
    have hdiv := phiInv_dvd hp hjz
    have hc2 : (((j * phiInv p j + 1) / p : ℕ) : ℂ)
        = ((j : ℂ) * (phiInv p j : ℂ) + 1) / (p : ℂ) := by
      rw [eq_comm, div_eq_iff hp0,
        mul_comm (((j * phiInv p j + 1) / p : ℕ) : ℂ) ((p : ℂ))]
      exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
    have hpt : (shiftDivP hp.pos j (ModularGroup.S • z) : ℍ)
        = (sigmaMatrix p j (phiInv p j) hdiv) • (shiftDivP hp.pos (phiInv p j) z) := by
      rw [UpperHalfPlane.ext_iff, coe_shiftDivP, coe_smul_S,
        coe_smul_SL_int' (a := (j : ℤ)) (b := -(((j * phiInv p j + 1) / p : ℕ) : ℤ))
          (c := (p : ℤ)) (d := -((phiInv p j : ℕ) : ℤ))
          (shiftDivP hp.pos (phiInv p j) z) rfl rfl rfl rfl,
        coe_shiftDivP, Int.cast_neg, Int.cast_neg,
        Int.cast_natCast, Int.cast_natCast, Int.cast_natCast, Int.cast_natCast, hc2]
      have hw : (p : ℂ) * (((z : ℂ) + (phiInv p j : ℂ)) / (p : ℂ))
          = (z : ℂ) + (phiInv p j : ℂ) := by
        rw [mul_comm, div_mul_cancel₀ _ hp0]
      have hD : ((p : ℂ) * (((z : ℂ) + (phiInv p j : ℂ)) / (p : ℂ))
          + -((phiInv p j : ℂ))) ≠ 0 := by
        rw [hw, add_neg_cancel_right]
        exact hz
      have hc' : (p : ℂ) * (((j : ℂ) * (phiInv p j : ℂ) + 1) / (p : ℂ))
          = (j : ℂ) * (phiInv p j : ℂ) + 1 := by
        rw [mul_comm, div_mul_cancel₀ _ hp0]
      have hzz1 : (z : ℂ)⁻¹ * (z : ℂ) = 1 := inv_mul_cancel₀ hz
      rw [div_eq_div_iff hp0 hD]
      linear_combination hc' - (z : ℂ)⁻¹ * hw - hzz1
    rw [hpt, hf (sigmaMatrix p j (phiInv p j) hdiv) (shiftDivP hp.pos (phiInv p j) z)]
    have hdσ : denom ((sigmaMatrix p j (phiInv p j) hdiv : SL(2, ℤ)) : GL (Fin 2) ℝ)
        (shiftDivP hp.pos (phiInv p j) z) = (z : ℂ) := by
      rw [denomSL_apply,
        show ((sigmaMatrix p j (phiInv p j) hdiv : SL(2, ℤ)) 1 0) = (p : ℤ) from rfl,
        show ((sigmaMatrix p j (phiInv p j) hdiv : SL(2, ℤ)) 1 1) = -((phiInv p j : ℤ)) from rfl,
        coe_shiftDivP]
      push_cast
      rw [mul_div_cancel₀ _ hp0]
      ring
    rw [hdσ]
  -- the second term is governed by the S-invariance of f at the point `z / p`
  have hS1 : (p : ℂ) ^ (k - 1) * f (mulP hp.pos (ModularGroup.S • z))
      = (z : ℂ) ^ k * (p : ℂ)⁻¹ * f (shiftDivP hp.pos 0 z) := by
    have hpt : (mulP hp.pos (ModularGroup.S • z) : ℍ)
        = ModularGroup.S • (shiftDivP hp.pos 0 z) := by
      rw [UpperHalfPlane.ext_iff, coe_mulP, coe_smul_S, coe_smul_S, coe_shiftDivP]
      push_cast
      rw [add_zero, div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    rw [hpt, hf ModularGroup.S (shiftDivP hp.pos 0 z)]
    obtain ⟨-, -, e10, e11⟩ := S_entries
    have hdS : denom ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) (shiftDivP hp.pos 0 z)
        = (z : ℂ) / p := by
      rw [denomSL_apply, e10, e11, coe_shiftDivP]
      push_cast
      simp
    have hzz : ((z : ℂ) / p) ^ k = (z : ℂ) ^ k * (p : ℂ) ^ (-k) := by
      rw [div_eq_mul_inv, mul_zpow, inv_zpow']
    have hfin : (p : ℂ) ^ (k - 1) * ((z : ℂ) ^ k * (p : ℂ) ^ (-k))
        = (z : ℂ) ^ k * (p : ℂ)⁻¹ := by
      rw [mul_comm ((z : ℂ) ^ k) ((p : ℂ) ^ (-k)), ← mul_assoc, ← zpow_add₀ hp0,
        show (k : ℤ) - 1 + -k = -1 from by ring, zpow_neg_one]
      ring
    rw [hdS, hzz, ← mul_assoc, hfin]
  -- the involution j ↦ φ j permutes [1, p-1]
  have hbij : ∑ j ∈ Finset.Icc 1 (p - 1), f (shiftDivP hp.pos (phiInv p j) z)
      = ∑ j ∈ Finset.Icc 1 (p - 1), f (shiftDivP hp.pos j z) := by
    refine Finset.sum_bij (fun j _ => phiInv p j) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      have hjlt : j < p := by omega
      refine phiInv_mem_Icc hp (fun hd => ?_)
      have h0 := eq_zero_of_zmod_cast hjlt hd
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_Icc] at ha hb
      have halt : a < p := by omega
      have hblt : b < p := by omega
      have haz : (a : ZMod p) ≠ 0 := by
        intro hd
        have h0 := eq_zero_of_zmod_cast halt hd
        omega
      have hbz : (b : ZMod p) ≠ 0 := by
        intro hd
        have h0 := eq_zero_of_zmod_cast hblt hd
        omega
      have h3 := congrArg (phiInv p) hab
      rwa [phiInv_involution hp haz halt, phiInv_involution hp hbz hblt] at h3
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      have hblt : b < p := by omega
      have hbz : (b : ZMod p) ≠ 0 := by
        intro hd
        have h0 := eq_zero_of_zmod_cast hblt hd
        omega
      exact ⟨phiInv p b, phiInv_mem_Icc hp hbz, phiInv_involution hp hbz hblt⟩
    · intro a ha
      rfl
  -- assemble
  rw [heckeTPFun_apply, heckeTPFun_apply, hsplit f, hS0, hS1]
  rw [Finset.sum_congr rfl (fun j hj => hSj j hj)]
  have hmulsum : ∑ j ∈ Finset.Icc 1 (p - 1), ((z : ℂ) ^ k * f (shiftDivP hp.pos (phiInv p j) z))
      = (z : ℂ) ^ k * ∑ j ∈ Finset.Icc 1 (p - 1), f (shiftDivP hp.pos (phiInv p j) z) := by
    rw [Finset.mul_sum]
  rw [hmulsum, hbij]
  have hsplit' : ∑ j ∈ Finset.range p, f (shiftDivP hp.pos j z)
      = f (shiftDivP hp.pos 0 z) + ∑ j ∈ Finset.Icc 1 (p - 1), f (shiftDivP hp.pos j z) := by
    rw [show Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) from
      (Finset.ext fun j => by
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega),
      Finset.sum_insert (by simp [Finset.mem_Icc])]
  rw [hsplit']
  have hpow : (p : ℂ)⁻¹ * (p : ℂ) ^ k = (p : ℂ) ^ (k - 1) := by
    rw [← zpow_neg_one, ← zpow_add₀ hp0]
    congr 1
    ring
  linear_combination ((z : ℂ) ^ k * f (mulP hp.pos z)) * hpow

/-! ### Slash invariance of `T_p f` -/

theorem heckeTPFun_slash_invariant (hp : p.Prime) (hf : IsSlashInvariantSL k f) :
    ∀ γ : SL(2, ℤ), heckeTPFun hp.pos k f ∣[k] γ = heckeTPFun hp.pos k f := by
  refine SlashInvariantForm.slash_action_generators_SL2Z ?_ ?_
  · funext z
    rw [ModularForm.SL_slash_apply, heckeTPFun_S hp hf z]
    have hz : (z : ℂ) ≠ 0 := coe_ne_zero z
    obtain ⟨-, -, e10, e11⟩ := S_entries
    have hd : denom ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) z = (z : ℂ) := by
      rw [denomSL_apply, e10, e11]
      simp
    rw [hd, mul_assoc, mul_comm (heckeTPFun hp.pos k f z) ((z : ℂ) ^ (-k)), ← mul_assoc,
      ← zpow_add₀ hz, add_neg_cancel, zpow_zero, one_mul]
  · funext z
    rw [ModularForm.SL_slash_apply, heckeTPFun_T hp.pos hf z]
    have e10 : ((ModularGroup.T : SL(2, ℤ)) 1 0 : ℤ) = 0 := rfl
    have e11 : ((ModularGroup.T : SL(2, ℤ)) 1 1 : ℤ) = 1 := rfl
    have hd : denom ((ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) z = 1 := by
      rw [denomSL_apply, e10, e11]
      simp
    rw [hd, one_zpow, mul_one]

end Invariance

end HeckeLevelOne
