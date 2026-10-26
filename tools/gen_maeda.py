#!/usr/bin/env python3
"""Generate MathProof/ModularForms/MaedaSmallWeights.lean (Maeda instances).

Usage: python3 tools/gen_maeda.py 28 30 32 34 38 36 40 42 44 46 50 > MathProof/ModularForms/MaedaSmallWeights.lean
Computes, for each level-one weight k with dim S_k in {2,3}, the triangular basis
Delta^i E4^a E6^b, its q-coefficients, the matrix and charpoly of T_2 and a prime
ell with no root mod ell, then emits the Lean instances (everything is re-checked
by Lean: these numbers are only certificates)."""
import sys
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
    n=len(M); import copy
    I=[[F(int(i==j)) for j in range(n)] for i in range(n)]
    Mk=[[F(0)]*n for _ in range(n)]; c=[F(1)]
    A=[[F(x) for x in r] for r in M]
    for k in range(1,n+1):
        Mk=[[sum(A[i][l]*Mk[l][j] for l in range(n)) + (c[-1] if i==j else 0) for j in range(n)] for i in range(n)]
        AM=[[sum(A[i][l]*Mk[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        c.append(-sum(AM[i][i] for i in range(n))/k)
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
        for n in idx:
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
ks=[int(a) for a in sys.argv[1:]]
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
print(hdr+"\n".join(section(k) for k in ks))
