#!/usr/bin/env python3
"""Generate the kernel-verified F20-resolvent / discriminant identity section
for MaedaGalois5.lean, replacing the infeasible monolithic `ring` proofs.

Method (the LehmerPacked methodology applied to multivariate identities):
  * Python expands both sides of each identity into canonical sparse form and
    cross-checks equality (parser validated against the Lean definitions).
  * The emitted Lean section rebuilds both sides as Poly5 chains over small
    literals; `decide +kernel` certifies each list equality, and PEval
    homomorphism lemmas transport it to every commutative ring.
  * The composed (coefficient) side uses a multivariate Horner scheme over
    va..ve — ~100x cheaper in kernel reductions than term-by-term expansion.

Run with no arguments: verifies identities, then (re)writes the module chain
MaedaGalois5IdBase -> IdE4 -> IdE5 -> IdE6 -> MaedaGalois5Identities.
"""
import itertools, re, sys

SRC = 'MathProof/ModularForms/MaedaGalois5Defs.lean'

# ------------- poly dict arithmetic -------------
def padd(p, q):
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, 0) + c
        if r[m] == 0: del r[m]
    return r

def pmul(p, q):
    r = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = (m1[0]+m2[0], m1[1]+m2[1], m1[2]+m2[2], m1[3]+m2[3], m1[4]+m2[4])
            r[m] = r.get(m, 0) + c1*c2
    return {m: c for m, c in r.items() if c != 0}

def pscale(p, k):
    return {m: c*k for m, c in p.items()} if k else {}

XS = [{tuple(1 if i == t else 0 for t in range(5)): 1} for i in range(5)]
ONE = {(0,0,0,0,0): 1}

# ------------- data -------------
cyc  = [[4,0,1,2,3],[4,0,3,1,2],[4,2,0,1,3],[4,2,3,0,1],[4,3,0,2,1],[4,3,1,0,2]]
pent = [[3,4,0,1,2],[2,4,1,0,3],[3,0,4,2,1],[1,3,0,4,2],[1,2,4,0,3],[2,0,3,4,1]]

def theta_poly(tab):
    r = {}
    for v in range(5):
        m = [0]*5; m[v] += 1; m[tab[v]] += 1
        r[tuple(m)] = r.get(tuple(m), 0) + 1
    return r

THETAS = [pmul(theta_poly(cyc[j]), theta_poly(pent[j])) for j in range(6)]

VA = pscale(padd(padd(padd(padd(XS[0], XS[1]), XS[2]), XS[3]), XS[4]), -1)
VB = {}
for i in range(5):
    for j in range(i+1,5):
        VB = padd(VB, pmul(XS[i], XS[j]))
VC = {}
for i,j,k in itertools.combinations(range(5),3):
    VC = padd(VC, pmul(pmul(XS[i], XS[j]), XS[k]))
VC = pscale(VC, -1)
VD = {}
for comb in itertools.combinations(range(5),4):
    t = dict(ONE)
    for i in comb: t = pmul(t, XS[i])
    VD = padd(VD, t)
VE = pscale(pmul(pmul(pmul(XS[0], XS[1]), XS[2]), pmul(XS[3], XS[4])), -1)
SYMS = {'a': VA, 'b': VB, 'c': VC, 'd': VD, 'e': VE}
FNS = {'a': 'va', 'b': 'vb', 'c': 'vc', 'd': 'vd', 'e': 've'}
LITS = {'a': 'LS1', 'b': 'LS2', 'c': 'LS3', 'd': 'LS4', 'e': 'LS5'}

src = open(SRC).read()

def grab_def(name):
    i = src.index(f'def {name} ')
    j = src.index(':=', i)
    k = min(x for x in [src.find('\n\n', j), src.find('/-!', j)] if x > 0)
    return src[j+2:k]

def parse_signed_chunks(text):
    terms = re.split(r'(?<=[\d\w\)])\s*([+-])\s*', text.strip())
    chunks = []; sign = 1; buf = terms[0]
    for kk in range(1, len(terms), 2):
        chunks.append((sign, buf)); sign = 1 if terms[kk] == '+' else -1; buf = terms[kk+1]
    chunks.append((sign, buf))
    return [(s, c.strip()) for s, c in chunks if c.strip()]

def term_to_pow(chunk):
    coeff = 1; pw = {'a':0,'b':0,'c':0,'d':0,'e':0}
    for f in chunk.split('*'):
        f = f.strip()
        if re.fullmatch(r'-?\d+', f):
            coeff = int(f)
        else:
            m = re.fullmatch(r'(\w)\s*\^\s*(\d+)', f)
            if m: pw[m.group(1)] += int(m.group(2))
            else:
                assert f in pw, f
                pw[f] += 1
    return coeff, pw

def chunks_poly(chunks):
    r = {}
    for s, c in chunks:
        coeff, pw = term_to_pow(c)
        t = pscale(ONE, s*coeff)
        for v, n in pw.items():
            for _ in range(n):
                t = pmul(t, SYMS[v])
        r = padd(r, t)
    return r

RES_TERMS = {}
for m in re.finditer(r'C \(\s*(.*?)\)\s*\*\s*X \^ (\d+)', src[src.index('def resolvent5'):], flags=re.S):
    RES_TERMS.setdefault(int(m.group(2)), parse_signed_chunks(m.group(1)))
DISC_CHUNKS = parse_signed_chunks(grab_def('disc5'))

def eK(k):
    r = {}
    for comb in itertools.combinations(range(6), k):
        t = dict(ONE)
        for j in comb: t = pmul(t, THETAS[j])
        r = padd(r, t)
    return r

VAND = dict(ONE)
for i in range(5):
    for j in range(i+1,5):
        VAND = pmul(VAND, padd(XS[i], pscale(XS[j], -1)))
DELTA2 = pmul(VAND, VAND)

ok = True
for k in range(1,7):
    good = eK(k) == pscale(chunks_poly(RES_TERMS[6-k]), (-1)**k)
    ok &= good
    print(f"e_{k}: {'OK' if good else 'MISMATCH'} ({len(eK(k))} monomials)")
good = DELTA2 == chunks_poly(DISC_CHUNKS)
ok &= good
print("delta2:", "OK" if good else "MISMATCH", f"({len(DELTA2)} monomials)")
if not ok:
    sys.exit("IDENTITY CHECK FAILED — aborting")

# ------------- emitters -------------
def mono_lit(m):
    return f"({m[0]}, ({m[1]}, ({m[2]}, ({m[3]}, {m[4]}))))"

def poly_lit(p, name):
    items = sorted(p.items())
    rows = []
    cur = ''
    for m, c in items:
        piece = f"({mono_lit(m)}, {c}), "
        if cur and len(cur) + len(piece) > 94:
            rows.append(cur.rstrip()); cur = piece
        else:
            cur += piece
    rows.append(cur.rstrip().rstrip(','))
    return f"def {name} : Poly5 :=\n  [" + "\n  ".join(rows) + "]"

def balanced_mul(names, polys):
    """Balanced product text.  Each `pMul` gets its SMALLER operand on the
    left: the kernel's native stack depth when forcing `pMul p q` grows with
    `len p` (measured: left factors of 2445 terms hit "deep recursion", 218
    pass)."""
    level = list(zip(names, polys))
    while len(level) > 1:
        nxt = []
        for i in range(0, len(level)-1, 2):
            (n1, p1), (n2, p2) = level[i], level[i+1]
            if len(p2) < len(p1):
                (n1, p1), (n2, p2) = (n2, p2), (n1, p1)
            nxt.append((f"(pMul {n1} {n2})", pmul(p1, p2)))
        if len(level) % 2:
            nxt.append(level[-1])
        level = nxt
    return level[0][0] if level else '[]'

def wrap(text, ind='    ', w=92):
    toks = re.split(r'(?<= )', text)
    out, line = [], ''
    for tk in toks:
        if line and len(line) + len(tk) > w:
            out.append(line.rstrip()); line = tk
        else:
            line += tk
    out.append(line.rstrip())
    return ('\n' + ind).join(out)

VF = ['x 0','x 1','x 2','x 3','x 4']

def sum_expr2(p):
    terms = []
    for m, c in sorted(p.items()):
        assert c == 1 and sum(m) == 2
        factors = [VF[i] for i in range(5) for _ in range(m[i])]
        terms.append(' * '.join(factors))
    return ' + '.join(terms)

def flat_expr(chunks):
    """flat K-expression text of a block with a..e -> va x .. ve x"""
    parts = []
    for s, c in chunks:
        coeff, pw = term_to_pow(c)
        v = s * coeff
        pieces = []
        if v != 1 or not any(pw.values()):
            pieces.append(str(v))
        for var in 'abcde':
            n = pw[var]
            if n == 1: pieces.append(f'{FNS[var]} x')
            elif n > 1: pieces.append(f'({FNS[var]} x) ^ {n}')
        parts.append(' * '.join(pieces))
    out = ''
    for i, ptxt in enumerate(parts):
        neg = ptxt.startswith('-')
        if neg: ptxt = ptxt[1:]
        if i == 0:
            out = ('-' + ptxt) if neg else ptxt
        else:
            out += (' - ' + ptxt) if neg else (' + ' + ptxt)
    return out if out else '0'

P = []
P.append(f"""/-! ### Kernel-verified identities (`Poly5`)

The coefficient identities of the `F₂₀` resolvent and the quintic discriminant
identity are far beyond the `ring` tactic (measured: >80 GiB elaborator
memory on the degree-24 sextic coefficients).  Both sides are instead rebuilt
as canonical `Poly5` chains over small literals, certified equal by
`decide +kernel` (the `LehmerPacked` methodology), and transported to every
commutative ring by the `PEval` homomorphism lemmas.  The composed side is a
multivariate Horner scheme over `va, vb, vc, vd, ve`.  Generated by
`tools/gen_poly5.py` — regenerate, don't hand-edit. -/""")

# --- literals + bridges
for j in range(6):
    for tab, nm in [(cyc[j], f'Cyc{j}'), (pent[j], f'Pent{j}')]:
        P.append(poly_lit(theta_poly(tab), f'L{nm}'))
for var in 'abcde':
    P.append(poly_lit(SYMS[var], LITS[var]))

for j in range(6):
    for tab, nm in [(cyc[j], f'Cyc{j}'), (pent[j], f'Pent{j}')]:
        P.append(f"""lemma L{nm}_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval L{nm} x = {wrap(sum_expr2(theta_poly(tab)))} := by
  simp [PEval, mEval, L{nm}]
  ring""")
for var in 'abcde':
    P.append(f"""lemma {LITS[var]}_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval {LITS[var]} x = {FNS[var]} x := by
  simp [PEval, mEval, {LITS[var]}, {FNS[var]}]
  try ring""")

# --- theta products
for j in range(6):
    P.append(f"def Theta{j} : Poly5 := pMul LCyc{j} LPent{j}")
for j in range(6):
    P.append(f"""lemma Theta{j}_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval Theta{j} x
      = theta x ![{','.join(map(str, cyc[j]))}] * theta x ![{','.join(map(str, pent[j]))}] := by
  rw [show PEval Theta{j} x = PEval LCyc{j} x * PEval LPent{j} x from PEval_pMul _ _ x,
    LCyc{j}_eval, LPent{j}_eval]
  simp [theta, Fin.sum_univ_succ, add_assoc]
  ring""")

# ------------- Horner emitter -------------
def horner(var_idx, terms, tag):
    """terms: list of (coeff:int, pw:dict-with-vars-≥var_idx).  Returns
    (lean_expr_of_chain, K-eval-text, emitted_lines)."""
    E = []
    def rec(vi, tms, tg):
        # strip zero terms
        tms = [(c, pw) for c, pw in tms if c != 0]
        if not tms:
            return '[]', '0', E
        if vi == 5:
            assert all(not any(pw.values()) for _, pw in tms)
            c = sum(cc for cc, _ in tms)
            nm = f'{tg}C'
            E.append(f"def {nm} : Poly5 := [(Mon.one, {c})]")
            E.append(f"""lemma {nm}_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval {nm} x = ({c} : K) := by
  simp [PEval, mEval, {nm}, Mon.one]""")
            return nm, f'({c} : K)', E
        var = 'abcde'[vi]
        by_deg = {}
        for c, pw in tms:
            d = pw[var]
            rest = {k2: v2 for k2, v2 in pw.items() if k2 != var}
            by_deg.setdefault(d, []).append((c, rest))
        maxd = max(by_deg)
        children = {}
        for d in sorted(by_deg):
            nm, txt, _ = rec(vi+1, by_deg[d], f'{tg}H{d}')
            children[d] = (nm, txt)
        cur_nm, cur_txt = children[maxd]
        for d in range(maxd-1, -1, -1):
            if d in children:
                cnm, ctxt = children[d]
                nm = f'{tg}N{d}'
                E.append(f"def {nm} : Poly5 := pAdd {cnm} (pMul {LITS[var]} {cur_nm})")
                E.append(f"""lemma {nm}_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval {nm} x = ({ctxt}) + ({FNS[var]} x) * ({cur_txt}) := by
  rw [show PEval {nm} x = PEval {cnm} x + PEval {LITS[var]} x * PEval {cur_nm} x from by
      simp only [{nm}, PEval_pAdd, PEval_pMul],
    {cnm}_eval, {LITS[var]}_eval, {cur_nm}_eval]""")
                cur_nm, cur_txt = nm, f'({ctxt}) + ({FNS[var]} x) * ({cur_txt})'
            else:
                nm = f'{tg}N{d}'
                E.append(f"def {nm} : Poly5 := pMul {LITS[var]} {cur_nm}")
                E.append(f"""lemma {nm}_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval {nm} x = ({FNS[var]} x) * ({cur_txt}) := by
  rw [show PEval {nm} x = PEval {LITS[var]} x * PEval {cur_nm} x from by
      simp only [{nm}, PEval_pMul],
    {LITS[var]}_eval, {cur_nm}_eval]""")
                cur_nm, cur_txt = nm, f'({FNS[var]} x) * ({cur_txt})'
        return cur_nm, cur_txt, E
    return rec(var_idx, terms, tag)

def chunks_to_terms(chunks):
    tms = []
    for s, c in chunks:
        coeff, pw = term_to_pow(c)
        tms.append((s*coeff, pw))
    return tms

# ------------- e_k sections -------------
HB = {1: 8000000, 2: 32000000, 3: 64000000, 4: 128000000, 5: 256000000, 6: 512000000}
THETA_TEXT = {j: f'(theta x ![{",".join(map(str, cyc[j]))}]) * (theta x ![{",".join(map(str, pent[j]))}])' for j in range(6)}

for k in range(1, 7):
    if k >= 4:
        P.append(f'@@CUT:E{k}@@')
    K = f'e{k}'
    combs = list(itertools.combinations(range(6), k))
    for idx, comb in enumerate(combs):
        P.append(f"def {K}T{idx} : Poly5 := {balanced_mul([f'Theta{j}' for j in comb], [THETAS[j] for j in comb])}")
    if len(combs) == 1:
        P.append(f"def {K}LHS : Poly5 := {K}T0")
        lhs_defs = [f'{K}LHS', f'{K}T0']
    else:
        P.append(f"def {K}A1 : Poly5 := pAdd {K}T0 {K}T1")
        for idx in range(2, len(combs)):
            P.append(f"def {K}A{idx} : Poly5 := pAdd {K}A{idx-1} {K}T{idx}")
        P.append(f"def {K}LHS : Poly5 := {K}A{len(combs)-1}")
        lhs_defs = [f'{K}LHS'] + [f'{K}A{i}' for i in range(len(combs)-1, 0, -1)] \
            + [f'{K}T{i}' for i in range(len(combs)-1, -1, -1)]
    sgn = (-1) ** k
    horner_nm, horner_txt, _ = horner(0, [(sgn * c, pw) for c, pw in chunks_to_terms(RES_TERMS[6-k])], f'{K}R')
    P.extend(_)
    P.append(f"def {K}RHS : Poly5 := {horner_nm}")
    P.append(f"""set_option maxHeartbeats {HB[k]} in
/-- Kernel certificate: the two canonical chains for the `X^{6-k}`-coefficient
of the `F₂₀` resolvent (as polynomials in `x 0, …, x 4`) agree. -/
theorem {K}dec : {K}LHS = {K}RHS := eq_of_pBeq (by decide +kernel)""")
    lhs_sum = ' + '.join(' * '.join(THETA_TEXT[j] for j in comb) for comb in combs)
    P.append(f"""set_option maxHeartbeats {HB[k]} in
lemma {K}lhs_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval {K}LHS x = {wrap(lhs_sum)} := by
  simp only [{', '.join(lhs_defs + [f'Theta{j}_eval' for j in range(6)])},
    PEval_pAdd, PEval_pMul]""" + ("\n  ring" if k > 1 else ""))
    sign = '-' if k % 2 == 1 else ''
    P.append(f"""lemma {K}rhs_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval {K}RHS x = {horner_txt} := {K}Rroot_eval x""")
    # the flat 140-term e₆ statement exceeds the default elaboration depth
    rec = "set_option maxRecDepth 100000 in\n" if k == 6 else ""
    P.append(f"""{rec}set_option maxHeartbeats {HB[k]} in
theorem theta_e{k} {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    {wrap(lhs_sum)} = {sign}({wrap(flat_expr(RES_TERMS[6-k]))}) := by
  calc {wrap(lhs_sum)} = PEval {K}LHS x := ({K}lhs_eval x).symm
    _ = PEval {K}RHS x := by rw [{K}dec]
    _ = {horner_txt} := {K}rhs_eval x
    _ = {sign}({wrap(flat_expr(RES_TERMS[6-k]))}) := by ring""")

# fix: the Horner root eval lemma name — horner returns (nm, txt, E) where the
# root's eval lemma is named {nm}_eval except for '[]'; patch {K}rhs_eval.
# (Handled below by rewriting the placeholder references.)

# ------------- delta2 -------------
P.append('@@CUT:Disc@@')
difs = [(i, j) for i in range(5) for j in range(i+1,5)]
for i, j in difs:
    P.append(poly_lit({tuple(1 if t == i else 0 for t in range(5)): 1,
                       tuple(1 if t == j else 0 for t in range(5)): -1}, f'D{i}{j}'))
D_POLYS = [{tuple(1 if t == i else 0 for t in range(5)): 1,
            tuple(1 if t == j else 0 for t in range(5)): -1} for i, j in difs]
P.append(f"def DLHS2 : Poly5 := {balanced_mul([f'D{i}{j}' for i, j in difs], D_POLYS)}")
horner_nm, horner_txt, _ = horner(0, chunks_to_terms(DISC_CHUNKS), 'dR')
P.extend(_)
P.append(f"def dRHS : Poly5 := {horner_nm}")
P.append(f"""set_option maxHeartbeats 128000000 in
/-- Kernel certificate: the two canonical chains for the quintic
discriminant agree. -/
theorem ddec : pMul DLHS2 DLHS2 = dRHS := eq_of_pBeq (by decide +kernel)""")
for i, j in difs:
    P.append(f"""lemma D{i}{j}_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval D{i}{j} x = x {i} - x {j} := by
  simp [PEval, mEval, D{i}{j}]
  ring""")
vand_txt = ' * '.join(f'(x {i} - x {j})' for i, j in difs)
P.append(f"""lemma dlhs_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval DLHS2 x = {vand_txt} := by
  simp only [DLHS2, {', '.join(f'D{i}{j}_eval' for i, j in difs)}, PEval_pMul]
  ring""")
P.append(f"""lemma drhs_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval dRHS x = {horner_txt} := dRroot_eval x""")
P.append(f"""set_option maxHeartbeats 32000000 in
theorem delta2_identity {{K : Type*}} [Field K] (x : Fin 5 → K) :
    ({vand_txt}) ^ 2 = disc5 (va x) (vb x) (vc x) (vd x) (ve x) := by
  have h1 : ({vand_txt}) ^ 2 = PEval DLHS2 x * PEval DLHS2 x := by
    rw [dlhs_eval x]
    ring
  rw [h1, ← PEval_pMul]
  calc PEval (pMul DLHS2 DLHS2) x = PEval dRHS x := by rw [ddec]
    _ = {horner_txt} := drhs_eval x
    _ = disc5 (va x) (vb x) (vc x) (vd x) (ve x) := by
        simp only [disc5]
        ring""")

section = '\n\n'.join(P)

# fix rhs_eval root references
root_names = {}
for k in range(1, 7):
    nm, _, _ = horner(0, chunks_to_terms(RES_TERMS[6-k]), f'e{k}R')
    root_names[f'e{k}'] = nm
dnm, _, _ = horner(0, chunks_to_terms(DISC_CHUNKS), 'dR')
root_names['d'] = dnm
section = section.replace(':= e{k}Rroot_eval x', '')  # no-op safeguard
for k in range(1, 7):
    section = section.replace(f':= e{k}Rroot_eval x', f':= {root_names[f"e{k}"]}_eval x')
section = section.replace(':= dRroot_eval x', f':= {root_names["d"]}_eval x')

# ------------- write the module chain -------------
# One module per heavy identity, each importing the previous one: lake builds
# them strictly in sequence (one elaborator process at a time, memory freed
# at every module boundary), and with lean_check.py's build cache a failure
# late in the chain never costs the modules before it.
CHAIN = [
    ('MaedaGalois5IdBase', 'MaedaGalois5Defs', 'literals, `θ` products, coefficients `e₁ … e₃`'),
    ('MaedaGalois5IdE4', 'MaedaGalois5IdBase', 'coefficient `e₄`'),
    ('MaedaGalois5IdE5', 'MaedaGalois5IdE4', 'coefficient `e₅`'),
    ('MaedaGalois5IdE6', 'MaedaGalois5IdE5', 'coefficient `e₆`'),
    ('MaedaGalois5Identities', 'MaedaGalois5IdE6', 'the discriminant identity `delta2_identity`'),
]
bodies = re.split(r'@@CUT:\w+@@', section)
assert len(bodies) == len(CHAIN), len(bodies)
for (mod, prev, what), body in zip(CHAIN, bodies):
    imports = f'import MathProof.ModularForms.{prev}\n'
    if mod == 'MaedaGalois5IdBase':
        imports += 'import MathProof.ModularForms.Poly5\n'
    text = f"""{imports}
/-!
# Kernel-verified `F₂₀`-resolvent identities (dim-5 Maeda): {what}

Generated by `tools/gen_poly5.py` — regenerate, don't hand-edit.  Part of the
chain `MaedaGalois5IdBase → IdE4 → IdE5 → IdE6 → MaedaGalois5Identities`
(heavy: build on Modal).
-/

open Polynomial

namespace MaedaGalois

section Resolvent

open Poly5

{body.strip()}

end Resolvent

end MaedaGalois
"""
    path = f'MathProof/ModularForms/{mod}.lean'
    open(path, 'w').write(text)
    print(f"{path}: {len(text)} chars")
