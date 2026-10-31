import MathProof.ModularForms.FrobeniusCycleType
import MathProof.ModularForms.JordanPrimitive
import MathProof.ModularForms.RabinCert

/-!
# Maeda in full: `Gal = Sₙ` from two Frobenius certificates

The weight-independent assembly of Iteration 21.  A monic `q : ℤ[X]` of degree
`n ≥ 3`, irreducible over `ℚ`, has full Galois group as soon as its reductions
modulo two primes factor as

* `(X - r) * gb`, `gb` irreducible of degree `n - 1` (a Frobenius of cycle type
  `{n - 1}`), and
* `∏ᵢ (X - rᵢ) * hb`, the `rᵢ` distinct, `hb` irreducible of degree `2` (a
  Frobenius transposition).

`bijective_of_frobenius` is the group-theoretic finish; `cycleType_of_cert` turns
a reflected factorization (`RabinCert` lists, `decide +kernel`) into the
`FrobHasCycleType` hypothesis it consumes.

Everything here is light; nothing is an ancestor of the heavy
`MaedaGalois5Defs` chain.
-/

open Polynomial FrobeniusCert RabinCert

namespace MaedaGaloisFull

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-- **The finish.**  Transitivity (irreducibility), a Frobenius of cycle type
`{n - 1}` and a Frobenius transposition make the Galois action on the complex
roots the full symmetric group. -/
theorem bijective_of_frobenius {q : ℤ[X]} (hq : q.Monic) {n : ℕ} (hn : q.natDegree = n)
    (h3 : 3 ≤ n) (hirr : Irreducible (ratOf q))
    (hcyc : MaedaGalois.FrobHasCycleType (ratOf q) {n - 1})
    (hswap : MaedaGalois.FrobHasCycleType (ratOf q) {2}) :
    Function.Bijective (Gal.galActionHom (ratOf q) ℂ) := by
  classical
  have hcard : Fintype.card ((ratOf q).rootSet ℂ) = n := by
    rw [card_rootSet_eq_natDegree hirr.separable (IsAlgClosed.splits _),
      hq.natDegree_map, hn]
  obtain ⟨c, hc⟩ := hcyc
  obtain ⟨s, hs⟩ := hswap
  have htrans : MulAction.IsPretransitive (Gal.galActionHom (ratOf q) ℂ).range
      ((ratOf q).rootSet ℂ) := by
    have := Gal.galAction_isPretransitive (ratOf q) ℂ hirr
    refine ⟨fun a b => ?_⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ratOf q).Gal a b
    exact ⟨⟨_, g, rfl⟩, hg⟩
  have htop := MaedaGalois.eq_top_of_isPretransitive_of_cycleType_of_isSwap_mem
    (Gal.galActionHom (ratOf q) ℂ).range hcard h3 htrans ⟨c, rfl⟩ hc ⟨s, rfl⟩
    (Equiv.Perm.isSwap_iff_cycleType.mpr hs)
  exact ⟨Gal.galActionHom_injective _ _, MonoidHom.range_eq_top.mp htop⟩

/-! ### Reflected factorization certificates -/

/-- The integer polynomial of a little-endian coefficient list. -/
noncomputable def fromList : List ℤ → ℤ[X]
  | [] => 0
  | a :: t => C a + X * fromList t

theorem map_fromList (l : ℕ) : ∀ c : List ℤ,
    (fromList c).map (Int.castRingHom (ZMod l)) = toPoly l c
  | [] => by simp [fromList, toPoly_nil]
  | a :: t => by simp [fromList, toPoly_cons, map_fromList l t]

/-- The product of the linear factors `X - r` with `g`, as a coefficient list. -/
def mulLin (l : ℕ) (rs g : List ℤ) : List ℤ :=
  rs.foldr (fun r acc => zpmul l [-r, 1] acc) g

theorem toPoly_mulLin (l : ℕ) (g : List ℤ) : ∀ rs : List ℤ,
    toPoly l (mulLin l rs g) = (rs.map fun r : ℤ => X - C (r : ZMod l)).prod * toPoly l g
  | [] => by simp [mulLin]
  | r :: rs => by
    have ih := toPoly_mulLin l g rs
    have hlin : toPoly l [-r, 1] = X - C (r : ZMod l) := by
      simp [toPoly_cons, toPoly_nil, sub_eq_add_neg, add_comm]
    change toPoly l (zpmul l [-r, 1] (mulLin l rs g)) = _
    rw [toPoly_zpmul, ih, hlin, List.map_cons, List.prod_cons, mul_assoc]

/-- A reflected Bézout identity `u * f + v * (X ^ e - X mod f) = 1` proves the second
Rabin condition without any division mod `l`.  This matters for large `l`:
`RabinCert.zpgcd` inverts through a Fermat power structural in `l`, which overflows
the kernel stack at `l ≈ 5·10⁶`. -/
theorem isCoprime_of_bezout {l : ℕ} {f u v : List ℤ} {F e : ℕ} (hbits : e < 2 ^ F)
    (hb : znorm l (zadd l (zpmul l u f) (zpmul l v (zpxwsubX l f F e))) = [1]) :
    IsCoprime (toPoly l f) (X ^ e - X : (ZMod l)[X]) := by
  obtain ⟨q, hq⟩ := toPoly_zpxwsubX (l := l) (f := f) hbits
  have h1 := congrArg (toPoly l) hb
  rw [toPoly_znorm, toPoly_zadd, toPoly_zpmul, toPoly_zpmul, toPoly_one] at h1
  refine ⟨toPoly l u - toPoly l v * q, toPoly l v, ?_⟩
  linear_combination h1 + toPoly l v * hq

/-- The reflected Rabin test with Bézout witnesses in place of `zpgcd`. -/
theorem irreducible_of_rabin_bezout {l : ℕ} [Fact l.Prime] {f : List ℤ} {n F : ℕ}
    (hmon : (toPoly l f).Monic) (hnd : (toPoly l f).natDegree = n) (hn1 : 0 < n)
    (hF : l ^ n < 2 ^ F) (h1 : zpxw l f (bitsOf F (l ^ n)) [1] = [0, 1])
    (h2 : ∀ q : ℕ, q.Prime → q ∣ n → ∃ u v : List ℤ,
      znorm l (zadd l (zpmul l u f) (zpmul l v (zpxwsubX l f F (l ^ (n / q))))) = [1]) :
    Irreducible (toPoly l f) := by
  refine irreducible_of_rabin hmon hnd hn1 (dvd_of_zpxw hF h1) fun q hqp hqn => ?_
  obtain ⟨u, v, hb⟩ := h2 q hqp hqn
  have hle : l ^ (n / q) ≤ l ^ n :=
    Nat.pow_le_pow_right (Fact.out : l.Prime).pos (Nat.div_le_self n q)
  exact isCoprime_of_bezout (hle.trans_lt hF) hb

/-- **The certificate.**  If the coefficient list `c` of `P` reduces mod `l` to the
product of `X - r` (`r ∈ rs`, distinct mod `l`) with a monic irreducible `gb` of
degree `d ≥ 2`, then the Galois group of `P` contains an element of cycle type
`{d}`. -/
theorem cycleType_of_cert {P : ℤ[X]} {c : List ℤ} (hP : P = fromList c) (hm : P.Monic)
    (hsep : (ratOf P).Separable) {l : ℕ} [Fact l.Prime] {rs g : List ℤ}
    (hfact : znorm l c = znorm l (mulLin l rs g))
    (hdist : rs.Pairwise fun a b => a % (l : ℤ) ≠ b % (l : ℤ))
    (hgm : (toPoly l g).Monic) (hirr : Irreducible (toPoly l g)) {d : ℕ}
    (hd : (toPoly l g).natDegree = d) (h2 : 2 ≤ d) :
    MaedaGalois.FrobHasCycleType (ratOf P) {d} := by
  classical
  have hnd : (rs.map fun r : ℤ => (r : ZMod l)).Nodup :=
    List.pairwise_map.mpr (hdist.imp fun h heq => h ((ZMod.intCast_eq_intCast_iff _ _ _).mp heq))
  have hfac : P.map (Int.castRingHom (ZMod l))
      = (∏ r ∈ (rs.map fun r : ℤ => (r : ZMod l)).toFinset, (X - C r)) * toPoly l g := by
    rw [List.prod_toFinset _ hnd, List.map_map, hP, map_fromList, ← toPoly_znorm l c, hfact,
      toPoly_znorm, toPoly_mulLin]
    rfl
  subst hd
  exact frob_cycleType_of_factorization hm hsep _ hgm hirr h2 hfac

end MaedaGaloisFull
