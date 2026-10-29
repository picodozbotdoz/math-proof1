#!/usr/bin/env python3
"""Generate the Maeda instance files for the level-one weights with dim <= 4.

Usage (dim S_k in {2, 3}; the committed file covers 28-50):
  python3 tools/gen_maeda.py 28 30 32 34 38 36 40 42 44 46 50 > MathProof/ModularForms/MaedaSmallWeights.lean
Usage (dim S_k = 4; the committed file covers 48-62):
  python3 tools/gen_maeda.py 48 52 54 56 58 62 > MathProof/ModularForms/MaedaDim4Weights.lean
Usage (dim S_k = 5; the committed file covers 60-74):
  python3 tools/gen_maeda.py 60 64 66 68 70 74 > MathProof/ModularForms/MaedaDim5Weights.lean

Computes, for each level-one weight k, the triangular basis
Delta^i E4^a E6^b, its q-coefficients, the matrix and charpoly of T_2 and a prime
ell with no root mod ell (dim 4: additionally no quadratic factor), then emits the
Lean instances (everything is re-checked by Lean: these numbers are only
certificates)."""
import argparse
from fractions import Fraction as F
from itertools import product
N=12
def sigma(k,n): return sum(d**k for d in range(1,n+1) if n%d==0)
def mul(a,b): return [sum(a[i]*b[n-i] for i in range(n+1)) for n in range(N)]
def pw(a,e):
    r=[1]+[0]*(N-1)
    for _ in range(e): r=mul(r,a)
    return r
E4=[1]+[240*sigma(3,n) for n in range(1,N)]
E6=[1]+[-504*sigma(5,n) for n in range(1,N)]
tau=[0,1,-24,252,-1472,4830,-6048,-16744,84480,-113643,-115920,534612]

# The table above must agree with the kernel-proven `tauTable` in
# MathProof/ModularForms/MaedaLevelOne.lean (itself proven equal to
# `Ramanujan.tau_one … tau_twenty_one`); fail loudly on drift.
def _check_tau_table():
    import re
    from pathlib import Path
    src = (Path(__file__).resolve().parent.parent
           / "MathProof/ModularForms/MaedaLevelOne.lean")
    m = re.search(r"tauTable\s*:\s*List\s*ℤ\s*:=\s*\[([^\]]+)\]", src.read_text())
    if m is None:
        raise SystemExit("tauTable not found in MathProof/ModularForms/MaedaLevelOne.lean")
    lean = [int(x) for x in m.group(1).replace("\n", " ").split(",")]
    if tau != lean[:len(tau)]:
        raise SystemExit(f"tau table drift vs MaedaLevelOne.lean: {tau} != {lean[:len(tau)]}")

_check_tau_table()

def G(w):  # E4^a E6^b weight w, minimal b
    for b in (0,1):
        if (w-6*b)>=0 and (w-6*b)%4==0: return ((w-6*b)//4,b)
def dim(k):
    m=k-12
    return m//12 if m%12==2 else m//12+1
def det(M):
    n=len(M)
    if n==1: return M[0][0]
    return sum((-1)**j*M[0][j]*det([r[:j]+r[j+1:] for r in M[1:]]) for j in range(n))
def charpoly(M):
    # coefficients via Faddeev–LeVerrier
    n=len(M)
    I=[[F(int(i==j)) for j in range(n)] for i in range(n)]
    Mk=[[F(0)]*n for _ in range(n)]; c=[F(1)]
    A=[[F(x) for x in r] for r in M]
    for k in range(1,n+1):
        Mk=[[sum(A[i][l]*Mk[l][j] for l in range(n)) + (c[-1] if i==j else 0) for j in range(n)] for i in range(n)]
        AM=[[sum(A[i][l]*Mk[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        c.append(-sum(AM[i][i] for i in range(n))/k)
    assert all(x.denominator == 1 for x in c), "non-integral charpoly coefficients"
    return [int(x) for x in c]  # X^n + c1 X^{n-1} + ...
def isp(n):
    return n>1 and all(n%i for i in range(2,int(n**.5)+1))

def compute(k):
    d=dim(k)
    basis=[]
    for i in range(1,d+1):
        a,b=G(k-12*i)
        f=mul(pw(tau,i),mul(pw(E4,a),pw(E6,b)))
        basis.append(((i,a,b),f))
    fs=[f for _,f in basis]
    def coords(x):
        c=[]
        for m in range(1,d+1):
            c.append(x[m]-sum(c[i]*fs[i][m] for i in range(len(c))))
        return c
    def T2(f): return [f[2*m]+(2**(k-1)*f[m//2] if m%2==0 else 0) if 2*m<N else None for m in range(N//2)]
    M=[coords(T2(f)) for f in fs]
    Mat=[[M[j][i] for j in range(d)] for i in range(d)]
    cp=charpoly(Mat)
    ell=[l for l in range(3,200) if isp(l) and all(sum(c*pow(x,d-i,l) for i,c in enumerate(cp))%l for x in range(l))]
    return d,basis,fs,Mat,cp,ell
def polyterm(cp):
    s = polyterm1(cp)
    if len(s) <= 96: return s
    parts = s.split(" + ")
    half = (len(parts) + 1) // 2
    a, b = " + ".join(parts[:half]), " + ".join(parts[half:])
    if len(b) <= 90:  # halving keeps both lines <= ~96 (dims 2-4)
        return a + "\n    + " + b
    # dim >= 5: coefficients up to ~54 digits force one term per line
    return "\n    + ".join(parts)
def polyterm1(cp):
    d=len(cp)-1
    parts=[f"X ^ {d}"]
    for i,c in enumerate(cp[1:],1):
        e=d-i
        mon = "" if e==0 else (" * X" if e==1 else f" * X ^ {e}")
        parts.append(f"C ({c}){mon}")
    return " + ".join(parts)
def rawpoly(cp):
    d=len(cp)-1
    parts=[f"x ^ {d}"]
    for i,c in enumerate(cp[1:],1):
        e=d-i
        mon = "" if e==0 else (" * x" if e==1 else f" * x ^ {e}")
        parts.append(f"({c}){mon}")
    return " + ".join(parts)
def section(k):
    d,basis,fs,Mat,cp,ell=compute(k)
    K=k
    out=[f"/-! ### Weight {k} (dim {d}) -/\n", f"namespace MaedaWeight{k}\n"]
    idx=sorted(set(list(range(1,d+1))+[2*m for m in range(1,d+1)]))
    for j,((i,a,b),f) in enumerate(basis,1):
        out.append(f"/-- `Δ^{i} E₄^{a} E₆^{b}`. -/\nnoncomputable def f{j} : CuspForm 𝒮ℒ (({k} : ℕ) : ℤ) :=\n  prodForm _ {i-1} {a} {b} (by norm_num)\n")
        out.append(f"lemma c{j} (n : ℕ) : (qExpansion 1 f{j}).coeff n = seqP {i-1} {a} {b} n :=\n  prodForm_coeff _ _ _ _ _ n\n")
        if d in (4, 5):
            # the kernel certificate is about the axiom-free `seqPLc`
            # (MaedaCertC); `seqPLc_eq` transfers it to `seqPL`
            NL = 9 if d == 4 else 11
            vs=[str(f[n]) for n in range(NL)]
            vals=",\n     ".join(", ".join(vs[r:r+4]) for r in range(0,NL,4))
            out.append(f"lemma L{j}c : seqPLc {i-1} {a} {b} {NL} =\n    [{vals}] := by\n  decide +kernel\n")
            out.append(f"lemma L{j} : seqPL {i-1} {a} {b} {NL} =\n    [{vals}] := by\n"
                       f"  rw [← seqPLc_eq (by norm_num)]\n  exact L{j}c\n")
        for n in idx:
            if d == 4:
                out.append(f"lemma q{j}_{n} : (qExpansion 1 f{j}).coeff {n} = ({f[n]} : ℂ) := by\n  rw [c{j}, seqP_getD (N := 9) (by norm_num), L{j}]\n  norm_num [List.getD_cons_succ, List.getD_cons_zero]\n")
            elif d == 5:
                out.append(f"lemma q{j}_{n} : (qExpansion 1 f{j}).coeff {n} = ({f[n]} : ℂ) := by\n  rw [c{j}, seqP_getD (N := 11) (by norm_num), L{j}]\n  norm_num [List.getD_cons_succ, List.getD_cons_zero]\n")
            else:
                out.append(f"lemma q{j}_{n} : (qExpansion 1 f{j}).coeff {n} = ({f[n]} : ℂ) := by\n  rw [c{j}, show seqP {i-1} {a} {b} {n} = {f[n]} by decide +kernel]; norm_num\n")
    m=k-12
    out.append(f"""lemma finrank_eq : Module.finrank ℂ (CuspForm 𝒮ℒ (({k} : ℕ) : ℤ)) = {d} := by
  apply Module.finrank_eq_of_rank_eq
  rw [CuspForm.discriminantEquiv.rank_eq]
  have h := ModularForm.dimension_level_one {m} (by decide)
  norm_num [Nat.ModEq] at h
  exact_mod_cast h
""")
    out.append(f"/-- `T₂` on `S_{k}`. -/\nnoncomputable def T2 := heckeTPₗ (({k} : ℕ) : ℤ) Nat.prime_two\n")
    tl=[]
    for j in range(1,d+1):
        f=fs[j-1]
        for mm in range(1,d+1):
            v=f[2*mm]+(2**(k-1)*f[mm//2] if mm%2==0 else 0)
            ls=f"q{j}_{2*mm}"+(f", q{j}_{mm//2}" if mm%2==0 else "")
            out.append(f"lemma t{j}_{mm} : (qExpansion 1 (T2 f{j})).coeff {mm} = ({v} : ℂ) := by\n  rw [T2, heckeT2_coeff (by norm_num)]; norm_num [{ls}]\n")
            tl.append(f"t{j}_{mm}")
    ql=[f"q{j}_{n}" for j in range(1,d+1) for n in range(1,d+1)]
    fargs=" ".join(f"f{j}" for j in range(1,d+1))
    out.append(f"/-- The integer characteristic polynomial of `T₂` on `S_{k}`. -/\nnoncomputable def P : ℤ[X] :=\n  {polyterm(cp)}\n")
    if d==4:
        return section4(k,d,basis,fs,cp,out,ql,tl,fargs)
    if d==5:
        return section5(k,d,basis,fs,cp,out,ql,tl,fargs)
    thm="charpoly_dim2" if d==2 else "charpoly_dim3"
    fin = "Matrix.charpoly_fin_two" if d==2 else "charpoly_fin_three"
    extra = "Matrix.trace_fin_two, Matrix.det_fin_two" if d==2 else "Matrix.det_fin_three"
    out.append(f"""/-- **The characteristic polynomial of `T₂` on `S_{k}`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [{thm} finrank_eq {fargs} {' '.join(ql)} T2
    {' '.join(tl)}, {fin}]
  simp [P, {extra}, map_ofNat]
  ring
""")
    l=ell[0]
    out.append(f"""lemma noRoot_raw : ∀ x : ZMod {l},
    {rawpoly(cp)} ≠ 0 := by
  decide

/-- **Maeda's conjecture in weight {k}**: the characteristic polynomial of `T₂`
on `S_{k}(SL(2, ℤ))` is irreducible over `ℚ` (no root mod {l}). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime {l}) := ⟨by norm_num⟩
  refine irreducible_of_noRoot (by unfold P; monicity!) ?_ {l} fun x hx => noRoot_raw x ?_
  · rw [show P.natDegree = {d} by unfold P; compute_degree!]; decide
  · simpa [P] using hx

end MaedaWeight{k}
""")
    return "\n".join(out)

def irr_mod4(cp,l):
    a,b,c,d=[x%l for x in cp[1:]]
    if any((x**4+a*x**3+b*x**2+c*x+d)%l==0 for x in range(l)): return False
    for u in range(l):
        for v in range(l):
            s_=(a-u)%l; t=(b-v-u*s_)%l
            if (u*t+v*s_-c)%l==0 and (v*t-d)%l==0: return False
    return True

def irr_mod5(cp,l):
    """No root and no monic quadratic x cubic factorization mod l (Lean-style
    certificate, matching `irreducible_quintic`'s `hquad`)."""
    a1,a2,a3,a4,a5=[x%l for x in cp[1:]]
    if any((x**5+a1*x**4+a2*x**3+a3*x**2+a4*x+a5)%l==0 for x in range(l)): return False
    for u in range(l):
        for v in range(l):
            s=(a2-v-u*(a1-u))%l; t=(a3-v*(a1-u)-u*s)%l
            if (u*t+v*s-a4)%l==0 and (v*t-a5)%l==0: return False
    return True

def zcert(name, l, vars_, zmod_stmt, int_conds, rdefs):
    """An axiom-free certificate `{name}_cert` over bounded ℕ with ℤ
    arithmetic (`decide +kernel`) and the `ZMod {l}` statement `{name}`
    derived from it (HornerCert: cast each variable, push_cast,
    linear_combination).  `int_conds` are ℤ expressions E with the meaning
    "E % l = 0"; one condition gives `E % l ≠ 0`, two give `¬ (… ∧ …)`."""
    binders = " → ".join(f"∀ {v} : ℕ, {v} < {l}" for v in vars_)
    if len(int_conds) == 1:
        body = f"({int_conds[0]}) % {l} ≠ 0"
    else:
        body = "¬ (" + "\n      ∧ ".join(f"({e}) % {l} = 0" for e in int_conds) + ")"
    def wrap(text, indent="      ", width=98):
        out = []
        for raw in text.split("\n"):
            lead = raw[:len(raw) - len(raw.lstrip())]
            line = lead
            for w in raw.split():
                if line.strip() and len(line) + 1 + len(w) > width:
                    out.append(line)
                    line = indent + w
                else:
                    line = f"{line} {w}" if line.strip() else line + w
            out.append(line)
        return "\n".join(out)
    cert = wrap(f"""lemma {name}_cert : {binders} →
    {body} := by""") + "\n  decide +kernel\n"
    ys = ["y", "z"]
    lines = [f"lemma {name} : {zmod_stmt} := by"]
    hs = [f"h{i + 1}" for i in range(len(int_conds))]
    if len(int_conds) == 1:
        lines.append(f"  intro {' '.join(vars_)} h1")
    else:
        lines.append(f"  rintro {' '.join(vars_)} ⟨{', '.join(hs)}⟩")
    for v, y in zip(vars_, ys):
        lines.append(f"  obtain ⟨{y}, h{y}, rfl⟩ := HornerCert.exists_natCast_eq {v}")
    # the hypotheses' left/right sides, to unfold only the `r`s each mentions
    # (an unused simp argument is a lint warning)
    import re as _re
    sides = zmod_stmt.split("∧") if len(hs) > 1 else [zmod_stmt]
    for h, side in zip(hs, sides):
        used = [r for r in rdefs if _re.search(rf"\b{r}\b", side)]
        if used:
            lines.append(f"  simp only [{', '.join(used)}] at {h}")
        lines.append(f"  push_cast at {h}")
    args = " ".join(f"{y} h{y}" for y in ys[:len(vars_)])
    if len(int_conds) == 1:
        lines.append(f"  refine {name}_cert {args} (HornerCert.emod_eq_zero_of_cast ?_)")
        lines.append("  push_cast")
        lines.append("  linear_combination h1")
    else:
        holes = ", ".join("HornerCert.emod_eq_zero_of_cast ?_" for _ in hs)
        lines.append(f"  refine {name}_cert {args}\n    ⟨{holes}⟩")
        for h in hs:
            lines.append(f"  · push_cast")
            lines.append(f"    linear_combination {h}")
    return cert + "\n" + "\n".join(lines) + "\n"

def section4(k,d,basis,fs,cp,out,ql,tl,fargs):
    l=[l for l in range(3,400) if isp(l) and irr_mod4(cp,l)][0]
    c1,c2,c3,c4=cp[1:]
    cst=lambda c: f"(({c} : ℤ) : ZMod {l})"
    a,b,c,dd="r3","r2","r1","r0"
    out.append(f"""/-- **The characteristic polynomial of `T₂` on `S_{k}`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim4 finrank_eq {fargs}
    {' '.join(ql[:8])}
    {' '.join(ql[8:])} T2
    {' '.join(tl[:8])}
    {' '.join(tl[8:])}, charpoly_fin_four]
  simp [P, map_ofNat]
  ring

/-- The coefficients of `P` modulo {l}. -/
def r3 : ZMod {l} := {cst(c1)}
/-- See `r3`. -/
def r2 : ZMod {l} := {cst(c2)}
/-- See `r3`. -/
def r1 : ZMod {l} := {cst(c3)}
/-- See `r3`. -/
def r0 : ZMod {l} := {cst(c4)}

{zcert("noRoot", l, ["x"],
        f"∀ x : ZMod {l}, x ^ 4 + {a} * x ^ 3 + {b} * x ^ 2 + {c} * x + {dd} ≠ 0",
        [f"X ^ 4 + ({c1}) * X ^ 3 + ({c2}) * X ^ 2 + ({c3}) * X + ({c4})".replace("X", "(x : ℤ)")],
        ["r3", "r2", "r1", "r0"])}
{zcert("noQuad", l, ["u", "v"],
        f"∀ u v : ZMod {l},\n    ¬ (u * ({b} - v - u * ({a} - u)) + v * ({a} - u) = {c}\n      ∧ v * ({b} - v - u * ({a} - u)) = {dd})",
        [e.replace("U", "(u : ℤ)").replace("V", "(v : ℤ)") for e in (
            f"U * (({c2}) - V - U * (({c1}) - U)) + V * (({c1}) - U) - ({c3})",
            f"V * (({c2}) - V - U * (({c1}) - U)) - ({c4})")],
        ["r3", "r2", "r1", "r0"])}
/-- **Maeda's conjecture in weight {k}** (irreducibility): the characteristic
polynomial of `T₂` on `S_{k}(SL(2, ℤ))` is irreducible over `ℚ` (irreducible mod {l}). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime {l}) := ⟨by norm_num⟩
  exact irreducible_quartic_of_mod (by unfold P; monicity!) {l} r3 r2 r1 r0
    (by simp [P, r3, r2, r1, r0, map_ofNat])
    noRoot noQuad

end MaedaWeight{k}
""")
    return "\n".join(out)

def section5(k,d,basis,fs,cp,out,ql,tl,fargs):
    l=[l for l in range(3,600) if isp(l) and irr_mod5(cp,l)][0]
    c1,c2,c3,c4,c5=cp[1:]
    cst=lambda c: f"(({c} : ℤ) : ZMod {l})"
    out.append(f"""/-- **The characteristic polynomial of `T₂` on `S_{k}`.** -/
theorem charpoly_T2 : T2.charpoly = P.map (Int.castRingHom ℂ) := by
  rw [charpoly_dim5 finrank_eq {fargs}
    {' '.join(ql[:13])}
    {' '.join(ql[13:])} T2
    {' '.join(tl[:13])}
    {' '.join(tl[13:])}, charpoly_fin_five]
  simp [P, map_ofNat]
  ring

/-- The coefficients of `P` modulo {l}. -/
def r4 : ZMod {l} := {cst(c1)}
/-- See `r4`. -/
def r3 : ZMod {l} := {cst(c2)}
/-- See `r4`. -/
def r2 : ZMod {l} := {cst(c3)}
/-- See `r4`. -/
def r1 : ZMod {l} := {cst(c4)}
/-- See `r4`. -/
def r0 : ZMod {l} := {cst(c5)}

{zcert("noRoot", l, ["x"],
        f"∀ x : ZMod {l},\n    x ^ 5 + r4 * x ^ 4 + r3 * x ^ 3 + r2 * x ^ 2 + r1 * x + r0 ≠ 0",
        [f"X ^ 5 + ({c1}) * X ^ 4 + ({c2}) * X ^ 3 + ({c3}) * X ^ 2\n      + ({c4}) * X + ({c5})".replace("X", "(x : ℤ)")],
        ["r4", "r3", "r2", "r1", "r0"])}
{zcert("noQuad", l, ["u", "v"],
        f"∀ u v : ZMod {l},\n    ¬ (u * (r2 - v * (r4 - u) - u * (r3 - v - u * (r4 - u)))\n        + v * (r3 - v - u * (r4 - u)) = r1\n      ∧ v * (r2 - v * (r4 - u) - u * (r3 - v - u * (r4 - u))) = r0)",
        [e.replace("U", "(u : ℤ)").replace("V", "(v : ℤ)") for e in (
            f"U * (({c3}) - V * (({c1}) - U) - U * (({c2}) - V - U * (({c1}) - U)))\n        + V * (({c2}) - V - U * (({c1}) - U)) - ({c4})",
            f"V * (({c3}) - V * (({c1}) - U) - U * (({c2}) - V - U * (({c1}) - U))) - ({c5})")],
        ["r4", "r3", "r2", "r1", "r0"])}
/-- **Maeda's conjecture in weight {k}** (irreducibility): the characteristic
polynomial of `T₂` on `S_{k}(SL(2, ℤ))` is irreducible over `ℚ` (irreducible mod {l}). -/
theorem maeda : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have : Fact (Nat.Prime {l}) := ⟨by norm_num⟩
  exact irreducible_quintic_of_mod (by unfold P; monicity!) {l} r4 r3 r2 r1 r0
    (by simp [P, r4, r3, r2, r1, r0, map_ofNat])
    noRoot noQuad

end MaedaWeight{k}
""")
    return "\n".join(out)

_parser = argparse.ArgumentParser(
    description="Generate Maeda instances for the given level-one weights "
                "(dim S_k in {2, 3, 4}); see the module docstring for usage.")
_parser.add_argument("weights", metavar="K", type=int, nargs="+",
                     help="even level-one weights with dim S_k in {2, 3, 4}")
ks = _parser.parse_args().weights
hdr='''import MathProof.ModularForms.MaedaLevelOne

/-!
# Maeda's conjecture for the level-one weights with `dim S_k ∈ {2, 3}`

Instances of `MathProof/ModularForms/MaedaLevelOne.lean`, generated from the
numerical data (`tools/gen_maeda.py`): for each weight the triangular basis
`Δ^i E₄^a E₆^b`, its first q-coefficients (kernel-computed), the matrix of `T₂`
(from `charpoly_dim2` / `charpoly_dim3`), the characteristic polynomial and its
irreducibility over `ℚ` (no root modulo a small prime).
-/

open UpperHalfPlane ModularForm CuspForm Polynomial MaedaLevelOne
open scoped MatrixGroups

'''
if any(compute(k)[0] == 5 for k in ks):
    hdr = hdr.replace("import MathProof.ModularForms.MaedaLevelOne", "import MathProof.ModularForms.MaedaDim5\nimport MathProof.ModularForms.MaedaCertC")
    hdr = hdr.replace("with `dim S_k ∈ {2, 3}`", "with `dim S_k = 5`")
    hdr = hdr.replace("(from `charpoly_dim2` / `charpoly_dim3`), the characteristic polynomial and its\nirreducibility over `ℚ` (no root modulo a small prime).",
                      "(from `charpoly_dim5`), the characteristic polynomial and its irreducibility\nover `ℚ` (irreducible modulo a small prime: no root and no quadratic factor).")
elif any(compute(k)[0] == 4 for k in ks):
    hdr = hdr.replace("import MathProof.ModularForms.MaedaLevelOne", "import MathProof.ModularForms.MaedaCertC")
    hdr = hdr.replace("with `dim S_k ∈ {2, 3}`", "with `dim S_k = 4`")
    hdr = hdr.replace("(from `charpoly_dim2` / `charpoly_dim3`), the characteristic polynomial and its\nirreducibility over `ℚ` (no root modulo a small prime).",
                      "(from `charpoly_dim4`), the characteristic polynomial and its irreducibility\nover `ℚ` (irreducible modulo a small prime: no root and no quadratic factor).")
print(hdr+"\n".join(section(k) for k in ks))
