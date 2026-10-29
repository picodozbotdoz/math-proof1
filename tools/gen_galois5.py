#!/usr/bin/env python3
"""Generate MathProof/ModularForms/MaedaGalois5Weights.lean: the six S5 Galois
instances for the dim-5 weights (60, 64, 66, 68, 70, 74), from the certificate
data in research/s5_certs.json (research/s5-certificates.py).

Everything numeric is re-checked by Lean (decide +kernel): the integers here
are only certificates.  The discriminant `Dval` and the resolvent `R` are
DEFINED as `disc5`/`resolvent5` applied to the integer coefficients, so the
transport lemmas (`disc5_map`, `resolvent5_map`) close definitionally and no
big-integer kernel evaluation is ever needed.
"""
import json

certs = json.load(open("research/s5_certs.json"))
WEIGHTS = [60, 64, 66, 68, 70, 74]

def fmt_int(z):
    return str(z) if z >= 0 else f"({z})"

def qargs(a, b, c, d, e, wrap_indent="      "):
    """the five coefficient literals as ℚ casts, line-wrapped"""
    zs = [fmt_int(a), fmt_int(b), fmt_int(c), fmt_int(d), fmt_int(e)]
    parts = [f"({z} : ℚ)" for z in zs]
    out, line = [], ""
    for i, p in enumerate(parts):
        piece = p if i == 0 else f" {p}"
        if line and len(line) + len(piece) > 92:
            out.append(line)
            line = piece
        else:
            line = (line + piece) if line else piece
    out.append(line)
    return ("\n" + wrap_indent).join(out)

sections = []
for k in WEIGHTS:
    v = certs[str(k)]
    a, b, c, d, e = v["a"], v["b"], v["c"], v["d"], v["e"]
    q, l = v["disc_q"], v["R_l"]
    Rc = [int(z) for z in v["R"]]  # [c5, c4, c3, c2, c1, c0]
    # sanity: the certificate really has no root mod l
    L = int(l)
    assert all((y**6 + sum(cc * y**(5 - i) for i, cc in enumerate(Rc))) % L for y in range(L)), k
    def rpoly():
        terms = ["X ^ 6"] + [f"C ({fmt_int(cc)}) * X ^ {5 - i}" for i, cc in enumerate(Rc)]
        return "\n    + ".join(terms)
    def rmod():
        terms = ["y ^ 6"] + [f"(({fmt_int(cc)} : ℤ) : ZMod {l}) * y ^ {5 - i}"
                             for i, cc in enumerate(Rc)]
        return "\n    + ".join(terms)
    ints = ", ".join(fmt_int(z) for z in (a, b, c, d, e))
    # wrap the disc5/resolvent5 application lines
    zs = [fmt_int(z) for z in (a, b, c, d, e)]
    def app_lines(name):
        out, line = [], ""
        for i, z in enumerate(zs):
            piece = z if i == 0 else f" {z}"
            if line and len(line) + len(piece) > 90:
                out.append(line)
                line = piece
            else:
                line = (line + piece) if line else piece
        out.append(line)
        return ("\n    ").join(out)
    sec = f"""/-! ### Weight {k} -/

namespace Weight{k}

/-- The discriminant of the weight-{k} quintic (its characteristic polynomial
is `MaedaWeight{k}.P`, proved irreducible in `MaedaDim5Weights.lean`). -/
def Dval : ℤ :=
  disc5 {app_lines("")}

/-- The discriminant is not a square mod {q}. -/
lemma nonsquare : ∀ x : ZMod {q}, ((Dval : ℤ) : ZMod {q}) ≠ x * x := by
  decide +kernel

/-- The `F₂₀` resolvent of the weight-{k} quintic, with its integer coefficients
written out (`hRint` re-derives them from `resolvent5`). -/
noncomputable def R : ℤ[X] :=
  {rpoly()}

lemma hRint : (resolvent5 {app_lines("")} : ℤ[X]) = R := by
  unfold resolvent5 R
  norm_num

lemma R_monic : R.Monic := by
  unfold R
  monicity!

/-- `R` reduced mod {l}, as a computable function (`Polynomial` is not). -/
def Rmod (y : ZMod {l}) : ZMod {l} :=
  {rmod()}

/-- The resolvent has no root mod {l}. -/
lemma noRootR : ∀ y : ZMod {l}, Rmod y ≠ 0 := by
  decide +kernel

lemma R_eval_cast (n : ℤ) : (((R : ℤ[X]).eval n : ℤ) : ZMod {l}) = Rmod (n : ZMod {l}) := by
  simp [R, Rmod]

lemma hP : MaedaWeight{k}.P.map (Int.castRingHom ℚ)
    = X ^ 5 + C ({fmt_int(a)} : ℚ) * X ^ 4 + C ({fmt_int(b)} : ℚ) * X ^ 3
      + C ({fmt_int(c)} : ℚ) * X ^ 2 + C ({fmt_int(d)} : ℚ) * X
      + C ({fmt_int(e)} : ℚ) := by
  simp [MaedaWeight{k}.P, map_ofNat]

lemma hR : resolvent5 {qargs(a, b, c, d, e)}
    = (R : ℤ[X]).map (Int.castRingHom ℚ) := by
  rw [← hRint]
  exact resolvent5_map (Int.castRingHom ℚ) _ _ _ _ _

/-- **Maeda's conjecture in weight {k}, in full**: the Galois group of the
characteristic polynomial of `T₂` on `S_{k}` acts on its five roots as `S₅`. -/
theorem maeda_galois{k} :
    Function.Bijective
      (Gal.galActionHom (MaedaWeight{k}.P.map (Int.castRingHom ℚ)) ℂ) := by
  have hirr := MaedaWeight{k}.maeda
  rw [hP] at hirr ⊢
  refine galActionHom_bijective_of_quintic hirr ?_ ?_
  · -- the discriminant is not a square
    intro hs
    have hD : disc5 {qargs(a, b, c, d, e, "        ")}
        = ((Dval : ℤ) : ℚ) :=
      disc5_map (Int.castRingHom ℚ) _ _ _ _ _
    rw [hD, Rat.isSquare_intCast_iff] at hs
    obtain ⟨n, hn⟩ := hs
    have h := congrArg (fun z : ℤ => (z : ZMod {q})) hn
    push_cast at h
    exact nonsquare n h
  · -- no rational root: the integral root theorem reduces to `noRootR`
    rintro r hr
    have hr' : aeval r (R : ℤ[X]) = 0 := by
      rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, ← hR]
      exact hr
    -- evaluation over `ℚ` is the cast of the integer evaluation
    have hE : ∀ m : ℤ, aeval (m : ℚ) (R : ℤ[X]) = (((R : ℤ[X]).eval m : ℤ) : ℚ) := by
      intro m
      induction R using Polynomial.induction_on' with
      | add p q ihp ihq => simp [ihp, ihq]
      | monomial b c => simp
    obtain ⟨n, hn, -⟩ := exists_integer_of_is_root_of_monic (p := (R : ℤ[X])) R_monic hr'
    have h3 : ((R : ℤ[X]).eval n : ℤ) = 0 := by
      rw [hn, algebraMap_int_eq, eq_intCast, hE n] at hr'
      exact_mod_cast hr'
    refine noRootR (n : ZMod {l}) ?_
    rw [← R_eval_cast, h3, Int.cast_zero]

end Weight{k}
"""
    sections.append(sec)

header = """import MathProof.ModularForms.MaedaGalois5
import MathProof.ModularForms.MaedaDim5Weights

/-!
# Maeda's conjecture in full for dimension 5: Galois group `S₅`

For the six level-one weights with `dim S_k = 5` (`k = 60, 64, 66, 68, 70, 74`),
`MathProof/ModularForms/MaedaDim5Weights.lean` proves the characteristic
polynomial `P` of `T₂` irreducible.  Here we prove its Galois group is all of
`S₅`, via `galActionHom_bijective_of_quintic`: for each weight the discriminant
`disc5` of `P` is a non-square (non-residue mod a small prime) and the `F₂₀`
resolvent `resolvent5` has no root mod a small prime, hence no rational root
(integral root theorem).  The integers in this file are only certificates —
Lean re-checks everything: `Dval` and `R` are *defined* as `disc5`/`resolvent5`
applied to the coefficients, so the transport lemmas close definitionally.
-/

open Polynomial

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

-- generated certificates: the integer literals cannot be line-broken
set_option linter.style.longLine false

namespace MaedaGalois

"""

# Heavy module (imports the Poly5 identity chain): audit axioms in-file.
footer = "\nend MaedaGalois\n\n" + "".join(
    f"#print axioms MaedaGalois.Weight{k}.maeda_galois{k}\n" for k in WEIGHTS)

out = header + "\n".join(sections) + footer
with open("MathProof/ModularForms/MaedaGalois5Weights.lean", "w") as f:
    f.write(out)
print("wrote MathProof/ModularForms/MaedaGalois5Weights.lean:", len(out), "chars")
