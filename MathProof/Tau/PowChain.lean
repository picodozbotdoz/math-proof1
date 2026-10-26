import MathProof.Tau.Mordell

/-!
# Prime-power chains for Lehmer nonvanishing (light machinery)

Mordell's prime-power recursion (Iteration 7) expresses every `τ (p ^ a)`
along a two-term linear recurrence: with `c₀ = τ (p⁰) = 1`, `c₁ = τ p` and

    c_{r+2} = τ(p) · c_{r+1} − p ^ 11 · c_r        (`tau_prime_pow_succ`),

the chain values are `c_a = τ (p ^ a)`, computable in `ZMod P` (`P = 999999937`)
with O(1) state.  So once the seeds `τ p mod P` are known (Iteration 6's packed
residue list), a *linear* walk of ~32 steps per prime verifies `τ (p ^ a) ≠ 0`
for `p ^ a ≤ 2 ^ 32` — prime-power indices 65 536 times past the dense
kernel-verified bound, at a kernel cost proportional to one small `ZMod`
operation per value instead of a dense 65 536-coefficient convolution.

This module is the light (CI-checkable) half:

* `ppowAt c1 p11 a` — the chain value `c_a` (structural recursion);
* `ppowAt_eq_tau` — soundness: for `p` prime, the chain seeded at
  `c1 = τ p`, `p11 = p ^ 11` (in `ZMod P`) satisfies
  `ppowAt = residue of τ (p ^ a)` for every `a`;
* `ppowAux` — the linear kernel-time runner checking all chain values
  nonzero, and `ppowOK_iff` its correctness;
* `chainsOK` / `seedChainOK` — the bulk check over a seed list, and
  `tau_prime_pow_ne_zero_of_chains` the resulting parametric nonvanishing
  theorem (seeds supplied abstractly as hypotheses).

The heavy instantiation — seeds from `LehmerPacked.tauResList 65536` and the
kernel decide over all 65 535 chains — is `MathProof/Tau/LehmerPow32.lean`.
-/

open Ramanujan

namespace Ramanujan

local notation "P" => 999999937

local instance : NeZero 999999937 := ⟨by norm_num⟩

/-! ### The chain -/

/-- The prime-power chain value: `ppowAt c1 p11 a = c_a` where `c₀ = 1`,
`c₁ = c1`, `c_{a+2} = c1 * c_{a+1} - p11 * c_a`.  For `c1 = τ p` and
`p11 = p ^ 11` (prime `p`), `c_a = τ (p ^ a)` in `ZMod P`
(`ppowAt_eq_tau`). -/
def ppowAt (c1 p11 : ZMod P) : ℕ → ZMod P
  | 0 => 1
  | 1 => c1
  | a + 2 => c1 * ppowAt c1 p11 (a + 1) - p11 * ppowAt c1 p11 a

/-- One step of the linear runner: state `(x0, x1) = (c_r, c_{r+1})`;
`ppowAux c1 p11 A x0 x1` checks `c_{r+1}, …, c_{r+A}` all nonzero. -/
def ppowAux (c1 p11 : ZMod P) : ℕ → ZMod P → ZMod P → Bool
  | 0, _, _ => true
  | A + 1, x0, x1 => (x1 != 0) && ppowAux c1 p11 A x1 (c1 * x1 - p11 * x0)

/-- **Chain soundness**: for `p` prime, the chain seeded at `τ p` with
coefficient `p ^ 11` computes the residues of the prime-power τ-values:
`ppowAt (τ p) (p ^ 11) a = τ (p ^ a)` in `ZMod P`, for every `a`. -/
theorem ppowAt_eq_tau {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ppowAt ((tau p : ℤ) : ZMod P) ((p ^ 11 : ℕ) : ZMod P) a
      = ((tau (p ^ a) : ℤ) : ZMod P) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    match a with
    | 0 => simp [ppowAt, tau_one]
    | 1 => simp [ppowAt]
    | a + 2 =>
      simp only [ppowAt]
      rw [ih (a + 1) (by omega), ih a (by omega), tau_prime_pow_succ hp a]
      push_cast
      ring

/-! ### The linear runner is correct -/

private theorem ppowAux_iff (c1 p11 : ZMod P) :
    ∀ (A r : ℕ) (x0 x1 : ZMod P),
      x0 = ppowAt c1 p11 r → x1 = ppowAt c1 p11 (r + 1) →
      (ppowAux c1 p11 A x0 x1 = true ↔ ∀ k, 1 ≤ k → k ≤ A → ppowAt c1 p11 (r + k) ≠ 0) := by
  intro A
  induction A with
  | zero =>
      intro r x0 x1 _ _
      constructor
      · intro _ k hk1 hk2; omega
      · intro _; rfl
  | succ A ih =>
      intro r x0 x1 hx0 hx1
      have hnext : c1 * x1 - p11 * x0 = ppowAt c1 p11 (r + 1 + 1) := by
        have h3 : ppowAt c1 p11 (r + 1 + 1)
            = c1 * ppowAt c1 p11 (r + 1) - p11 * ppowAt c1 p11 r := by simp [ppowAt]
        rw [h3, ← hx0, ← hx1]
      simp only [ppowAux, Bool.and_eq_true, bne_iff_ne,
        ih (r + 1) x1 (c1 * x1 - p11 * x0) hx1 hnext]
      constructor
      · rintro ⟨h1, h2⟩ k hk1 hk2
        rcases k with _ | k
        · omega
        rcases k with _ | k
        · rw [← hx1]
          exact h1
        · have hk : k + 1 ≤ A := by omega
          have hval := h2 (k + 1) (by omega) hk
          rwa [show r + (k + 2) = r + 1 + (k + 1) from by omega]
      · intro h
        refine ⟨?_, ?_⟩
        · have h1 := h 1 (by omega) (by omega)
          rwa [← hx1] at h1
        · intro k hk1 hk2
          have h2 := h (k + 1) (by omega) (by omega)
          rwa [show r + 1 + k = r + (k + 1) from by omega]

/-- Correctness of the runner at the base state `(c₀, c₁) = (1, c1)`:
`ppowAux c1 p11 A 1 c1 = true` iff no chain value `c_a`, `1 ≤ a ≤ A`,
vanishes. -/
theorem ppowOK_iff (c1 p11 : ZMod P) (A : ℕ) :
    ppowAux c1 p11 A 1 c1 = true ↔ ∀ a, 1 ≤ a → a ≤ A → ppowAt c1 p11 a ≠ 0 := by
  have h := ppowAux_iff c1 p11 A 0 1 c1 (by simp [ppowAt]) (by simp [ppowAt])
  simpa using h

/-! ### The bulk check over a seed list -/

/-- Chain check for the seed `r` (residue of `τ m`) at index `m`: 32 steps,
i.e. all chain values `c_a`, `1 ≤ a ≤ 32`, are checked nonzero. -/
def seedChainOK (m r : ℕ) : Bool :=
  ppowAux ((r % P : ℕ) : ZMod P) (((m ^ 11 % P) : ℕ) : ZMod P) 32 1 ((r % P : ℕ) : ZMod P)

/-- Walk a seed list `r₀, r₁, …` (seeds of indices `m, m + 1, …`) checking
every chain. -/
def chainsOK : ℕ → List ℕ → Bool
  | _, [] => true
  | m, r :: l => seedChainOK m r && chainsOK (m + 1) l

theorem chainsOK_iff (m : ℕ) (l : List ℕ) :
    chainsOK m l = true ↔ ∀ i, i < l.length → seedChainOK (m + i) (l.getD i 0) = true := by
  induction l generalizing m with
  | nil => simp [chainsOK]
  | cons r l ih =>
      simp only [chainsOK, Bool.and_eq_true]
      constructor
      · intro h i hi
        rcases i with _ | i
        · exact h.1
        · have hi' : i < l.length := by
            simp only [List.length_cons] at hi; omega
          have hval := (ih (m + 1)).mp h.2 i hi'
          rwa [show m + (i + 1) = m + 1 + i from by omega]
      · intro h
        refine ⟨h 0 (by simp), ?_⟩
        refine (ih (m + 1)).mpr fun i hi => ?_
        have hval := h (i + 1) (by simp only [List.length_cons]; omega)
        rwa [show m + (i + 1) = m + 1 + i from by omega, List.getD_cons_succ] at hval

/-- The seed-to-chain bridge in `ZMod P`: a residue `r` with `r ≡ τ m` maps
to the chain parameters of `ppowAt_eq_tau`. -/
private lemma cast_modP (n : ℕ) : ((n % P : ℕ) : ZMod P) = (n : ZMod P) :=
  (ZMod.natCast_eq_natCast_iff (n % P) n P).mpr (Nat.mod_modEq n P)

/-- **Prime-power nonvanishing from the chain check (parametric)**: if a seed
list `hl` of length 65535 has entry `i` congruent to `τ (i + 2)` mod `P`
(seeds for the indices `2, …, 65536`) and all its chains check nonzero
(`chainsOK 2 hl = true`), then `τ (p ^ a) ≠ 0` for every prime `2 ≤ p ≤ 65536`
and `1 ≤ a ≤ 32` — every prime power `p ^ a ≤ 2 ^ 32` with `p ≤ 65536`. -/
theorem tau_prime_pow_ne_zero_of_chains {hl : List ℕ}
    (hlen : hl.length = 65535)
    (hseed : ∀ i, i < 65535 → ((hl.getD i 0 % P : ℕ) : ZMod P) = ((tau (i + 2) : ℤ) : ZMod P))
    (hchains : chainsOK 2 hl = true) {p a : ℕ} (hp : p.Prime)
    (hp2 : 2 ≤ p) (hle : p ≤ 65536) (ha1 : 1 ≤ a) (ha32 : a ≤ 32) :
    tau (p ^ a) ≠ 0 := by
  have hidx : p - 2 < 65535 := by omega
  have hseed' : seedChainOK (2 + (p - 2)) (hl.getD (p - 2) 0) = true :=
    (chainsOK_iff 2 hl).mp hchains (p - 2) (by rw [hlen]; omega)
  rw [show 2 + (p - 2) = p from by omega] at hseed'
  simp only [seedChainOK] at hseed'
  rw [hseed (p - 2) hidx, show p - 2 + 2 = p from by omega, cast_modP (p ^ 11),
    ppowOK_iff (((tau p : ℤ) : ZMod P)) (((p ^ 11 : ℕ) : ZMod P)) 32] at hseed'
  have hz : ppowAt (((tau p : ℤ) : ZMod P)) (((p ^ 11 : ℕ) : ZMod P)) a ≠ 0 :=
    hseed' a ha1 ha32
  intro h0
  rw [ppowAt_eq_tau hp a, h0] at hz
  simp at hz

end Ramanujan
