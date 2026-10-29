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
  * Memory (research/poly5-memory-study): the kernel keeps every intermediate
    term of a `decide` until the declaration ends, ~27 GiB per million list
    operations.  So (1) e_k(Θ) is computed by the recurrence
    E_{j,k} = E_{j-1,k} + Θ_j · E_{j-1,k-1} (not C(6,k) products), (2) every
    recurrence node is a literal certified by its own one-step `decide`, and
    (3) the Horner side is checkpointed into literals whenever the modelled
    work since the last checkpoint exceeds BUDGET.  Each declaration then
    stays far below the 64 GiB memory-alert threshold.

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

CHUNK = 64
BUDGET = 500_000          # modelled kernel list operations per declaration
def mono_term(m, c):
    return f"({mono_lit(m)}, {c})"

def chunked_lit(name, p):
    """`def name` as a balanced `++` tree of 64-term literal chunks (a single
    huge list literal is slow to elaborate)."""
    items = [mono_term(m, c) for m, c in sorted(p.items())]
    if not items:
        return [f"def {name} : Poly5 := []"]
    out, names = [], []
    for i in range(0, len(items), CHUNK):
        cn = f"{name}_c{i // CHUNK}"; names.append(cn)
        ch = items[i:i + CHUNK]
        rows = [", ".join(ch[r:r + 2]) for r in range(0, len(ch), 2)]
        out.append(f"def {cn} : Poly5 :=\n  [" + ",\n   ".join(rows) + "]")
    def tree(ns):
        if len(ns) == 1: return ns[0]
        h = len(ns) // 2
        return f"({tree(ns[:h])} ++ {tree(ns[h:])})"
    if len(names) == 1:
        out.append(f"def {name} : Poly5 := {names[0]}")
    else:
        out.append(f"def {name} : Poly5 :=\n  " + wrap(tree(names), '  ', 96))
    return out

def hb_for(work):
    """Kernel heartbeat budget for a `decide` of the modelled work."""
    return max(8_000_000, 60 * work)

def mul_work(a, b):
    """Modelled list operations of `pMul a b` (`a` supplies the scaled copies,
    merged one at a time into the growing result)."""
    acc = {}; w = 0
    for m, c in reversed(sorted(a.items())):
        sc = {tuple(x + y for x, y in zip(m, m2)): c * c2 for m2, c2 in b.items()}
        w += len(b) + len(sc) + len(acc)
        acc = padd(sc, acc)
    return w

def decide_thm(name, lhs, rhs, work, doc=None):
    d = f"/-- {doc} -/\n" if doc else ""
    return (f"set_option maxHeartbeats {hb_for(work)} in\n"
            f"-- kernel `decide` of ≈ {max(1, work // 1000)}k modelled list operations\n"
            f"{d}theorem {name} : {lhs} = {rhs} := eq_of_pBeq (by decide +kernel)")

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
    # `simp` alone closes the negated ones (`va`, `vc`, `ve`)
    tail = "" if var in "ace" else "\n  ring"
    P.append(f"""lemma {LITS[var]}_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval {LITS[var]} x = {FNS[var]} x := by
  simp [PEval, mEval, {LITS[var]}, {FNS[var]}]{tail}""")
P.append("""/-- The constant polynomial `1` (base of the e_k recurrence). -/
def EOne : Poly5 := [(Mon.one, 1)]""")
P.append("""lemma EOne_eval {K : Type*} [CommRing K] (x : Fin 5 → K) : PEval EOne x = 1 := by
  simp [PEval, mEval, EOne, Mon.one]""")

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
    (root_name, K-eval-text, emitted_lines, root_poly, root_work).  A node
    whose modelled work since the last checkpoint exceeds BUDGET becomes a
    literal certified by its own `decide` (`{name}_ck`), so no single
    declaration evaluates the whole chain."""
    E = []
    def node(nm, expr, poly, work, eval_stmt, eval_rw):
        """emit node `nm := expr`, checkpointed if `work` is over BUDGET;
        returns (name, effective work for the parent)"""
        if work > BUDGET:
            E.append(f"def {nm}c : Poly5 := {expr}")
            E.extend(chunked_lit(nm, poly))
            E.append(decide_thm(f"{nm}_ck", f"{nm}c", nm, work + len(poly)))
            E.append(f"""lemma {nm}_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    {eval_stmt} := by
  rw [← {nm}_ck, {eval_rw.replace('@@', nm + 'c')}""")
            return len(poly)
        E.append(f"def {nm} : Poly5 := {expr}")
        E.append(f"""lemma {nm}_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    {eval_stmt} := by
  rw [{eval_rw.replace('@@', nm)}""")
        return work
    def rec(vi, tms, tg):
        tms = [(c, pw) for c, pw in tms if c != 0]
        if not tms:
            return '[]', '0', {}, 0
        if vi == 5:
            assert all(not any(pw.values()) for _, pw in tms)
            c = sum(cc for cc, _ in tms)
            nm = f'{tg}C'
            E.append(f"def {nm} : Poly5 := [(Mon.one, {c})]")
            E.append(f"""lemma {nm}_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval {nm} x = ({c} : K) := by
  simp [PEval, mEval, {nm}, Mon.one]""")
            return nm, f'({c} : K)', ({(0,0,0,0,0): c} if c else {}), 1
        var = 'abcde'[vi]
        by_deg = {}
        for c, pw in tms:
            d = pw[var]
            rest = {k2: v2 for k2, v2 in pw.items() if k2 != var}
            by_deg.setdefault(d, []).append((c, rest))
        maxd = max(by_deg)
        children = {}
        for d in sorted(by_deg):
            children[d] = rec(vi+1, by_deg[d], f'{tg}H{d}')
        cur_nm, cur_txt, cur_p, cur_w = children[maxd]
        LSP = SYMS[var]
        for d in range(maxd-1, -1, -1):
            nm = f'{tg}N{d}'
            prod = pmul(LSP, cur_p)
            w = cur_w + mul_work(LSP, cur_p)
            if d in children:
                cnm, ctxt, cp, cw = children[d]
                poly = padd(cp, prod)
                w += cw + len(cp) + len(prod)
                txt = f'({ctxt}) + ({FNS[var]} x) * ({cur_txt})'
                eff = node(nm, f"pAdd {cnm} (pMul {LITS[var]} {cur_nm})", poly, w,
                    f"PEval {nm} x = {txt}",
                    f"""show PEval @@ x = PEval {cnm} x + PEval {LITS[var]} x * PEval {cur_nm} x from by
      simp only [@@, PEval_pAdd, PEval_pMul],
    {cnm}_eval, {LITS[var]}_eval, {cur_nm}_eval]""")
            else:
                poly = prod
                txt = f'({FNS[var]} x) * ({cur_txt})'
                eff = node(nm, f"pMul {LITS[var]} {cur_nm}", poly, w,
                    f"PEval {nm} x = {txt}",
                    f"""show PEval @@ x = PEval {LITS[var]} x * PEval {cur_nm} x from by
      simp only [@@, PEval_pMul],
    {LITS[var]}_eval, {cur_nm}_eval]""")
            cur_nm, cur_txt, cur_p, cur_w = nm, txt, poly, eff
        return cur_nm, cur_txt, cur_p, cur_w
    nm, txt, poly, w = rec(var_idx, terms, tag)
    return nm, txt, E, poly, w

def chunks_to_terms(chunks):
    tms = []
    for s, c in chunks:
        coeff, pw = term_to_pow(c)
        tms.append((s*coeff, pw))
    return tms

# ------------- e_k sections -------------
HB = {1: 8000000, 2: 32000000, 3: 64000000, 4: 128000000, 5: 256000000, 6: 512000000}
THETA_TEXT = {j: f'(theta x ![{",".join(map(str, cyc[j]))}]) * (theta x ![{",".join(map(str, pent[j]))}])' for j in range(6)}

# e_k(Θ_0 … Θ_5) by the recurrence E[j][k] = E[j-1][k] + Θ_j · E[j-1][k-1]
# (E[·][0] = 1, E[j][k] = 0 for k > j + 1).  Column k is emitted with e_k, so
# each module only adds one column on top of the literals of the previous.
EV = {}
def E_nm(j, k):
    return "EOne" if k == 0 else f"E{j}_{k}"
def E_val(j, k):
    return ONE if k == 0 else EV[(j, k)]

for k in range(1, 7):
    if k >= 4:
        P.append(f'@@CUT:E{k}@@')
    K = f'e{k}'
    combs = list(itertools.combinations(range(6), k))
    for j in range(k - 1, 6):
        below = (j - 1, k - 1) if j >= 1 else (0, 0)
        bnm = E_nm(*below) if k > 1 else "EOne"
        bval = E_val(*below) if k > 1 else ONE
        prod = pmul(THETAS[j], bval)
        work = mul_work(THETAS[j], bval) + len(bval) + 40   # + Θ_j = LCyc · LPent
        if j == k - 1:
            expr = f"pMul Theta{j} {bnm}"
            val = prod
            evtxt = f"{THETA_TEXT[j]} * PEval {bnm} x"
        else:
            prev = EV[(j - 1, k)]
            expr = f"pAdd E{j-1}_{k} (pMul Theta{j} {bnm})"
            val = padd(prev, prod)
            work += len(prev) + len(prev) + len(prod)
            evtxt = f"PEval E{j-1}_{k} x + {THETA_TEXT[j]} * PEval {bnm} x"
        EV[(j, k)] = val
        nm = f"E{j}_{k}"
        P.append(f"def {nm}c : Poly5 := {expr}")
        P.extend(chunked_lit(nm, val))
        P.append(decide_thm(f"{nm}_ck", f"{nm}c", nm, work + len(val)))
        P.append(f"""lemma {nm}_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval {nm} x = {evtxt} := by
  rw [← {nm}_ck]
  simp only [{nm}c, {'PEval_pAdd, ' if j > k - 1 else ''}PEval_pMul, Theta{j}_eval]""")
    assert EV[(5, k)] == eK(k)
    P.append(f"def {K}LHS : Poly5 := E5_{k}")
    sgn = (-1) ** k
    horner_nm, horner_txt, lines, rpoly, rwork = horner(
        0, [(sgn * c, pw) for c, pw in chunks_to_terms(RES_TERMS[6-k])], f'{K}R')
    assert rpoly == EV[(5, k)]
    P.extend(lines)
    P.append(f"def {K}RHS : Poly5 := {horner_nm}")
    P.append(decide_thm(f"{K}rhs_dec", f"{K}RHS", f"E5_{k}", rwork + len(rpoly)))
    P.append(f"""/-- Kernel certificate: the two canonical chains for the `X^{6-k}`-coefficient
of the `F₂₀` resolvent (as polynomials in `x 0, …, x 4`) agree.  Both are
literals certified step by step: `E5_{k}` (the e_{k} recurrence, `E·_·_ck`) and
the Horner chain (`{K}rhs_dec`). -/
theorem {K}dec : {K}LHS = {K}RHS := {K}rhs_dec.symm""")
    # eval lemmas reachable from E5_k
    reach, stack = [], [(5, k)]
    while stack:
        n = stack.pop()
        if n in reach or n[1] == 0: continue
        reach.append(n)
        if n[0] > n[1] - 1: stack.append((n[0] - 1, n[1]))
        if n[0] >= 1: stack.append((n[0] - 1, n[1] - 1))
    uses_one = any(nn[1] == 1 for nn in reach)
    lhs_sum = ' + '.join(' * '.join(THETA_TEXT[j] for j in comb) for comb in combs)
    simps = [f"{K}LHS"] + [f"E{a}_{b}_eval" for a, b in sorted(reach, reverse=True)] \
        + (["EOne_eval"] if uses_one else [])
    P.append(f"""set_option maxHeartbeats {HB[k]} in
-- `ring` over the 12 `theta` atoms (degree {2*k}) after unfolding the recurrence
lemma {K}lhs_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval {K}LHS x = {lhs_sum} := by
  simp only [{', '.join(simps)}]
  ring""")
    sign = '-' if k % 2 == 1 else ''
    P.append(f"""lemma {K}rhs_eval {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    PEval {K}RHS x = {horner_txt} := {horner_nm}_eval x""")
    # the flat 140-term e₆ statement exceeds the default elaboration depth
    rec = "set_option maxRecDepth 100000 in\n" if k == 6 else ""
    P.append(f"""{rec}set_option maxHeartbeats {HB[k]} in
-- `ring` matches the Horner form with the flat coefficient of `resolvent5`
theorem theta_e{k} {{K : Type*}} [CommRing K] (x : Fin 5 → K) :
    {lhs_sum} = {sign}({flat_expr(RES_TERMS[6-k])}) := by
  calc {lhs_sum} = PEval {K}LHS x := ({K}lhs_eval x).symm
    _ = PEval {K}RHS x := by rw [{K}dec]
    _ = {horner_txt} := {K}rhs_eval x
    _ = {sign}({flat_expr(RES_TERMS[6-k])}) := by ring""")

# ------------- delta2 -------------
P.append('@@CUT:Disc@@')
difs = [(i, j) for i in range(5) for j in range(i+1,5)]
for i, j in difs:
    P.append(poly_lit({tuple(1 if t == i else 0 for t in range(5)): 1,
                       tuple(1 if t == j else 0 for t in range(5)): -1}, f'D{i}{j}'))
D_POLYS = [{tuple(1 if t == i else 0 for t in range(5)): 1,
            tuple(1 if t == j else 0 for t in range(5)): -1} for i, j in difs]
P.append(f"def DLHS2 : Poly5 := {balanced_mul([f'D{i}{j}' for i, j in difs], D_POLYS)}")
horner_nm, horner_txt, lines, dpoly, dwork = horner(0, chunks_to_terms(DISC_CHUNKS), 'dR')
assert dpoly == DELTA2
P.extend(lines)
P.append(f"def dRHS : Poly5 := {horner_nm}")
P.extend(chunked_lit("DLit", DELTA2))
vw = sum(len(p) for p in D_POLYS) * 64          # the 10 small factors: negligible
P.append(decide_thm("dlhs_dec", "pMul DLHS2 DLHS2", "DLit", vw + mul_work(VAND, VAND) + len(DELTA2)))
P.append(decide_thm("drhs_dec", "dRHS", "DLit", dwork + len(DELTA2)))
P.append("""/-- Kernel certificate: the two canonical chains for the quintic
discriminant agree (each side against the literal `DLit`). -/
theorem ddec : pMul DLHS2 DLHS2 = dRHS := dlhs_dec.trans drhs_dec.symm""")
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
    PEval dRHS x = {horner_txt} := {horner_nm}_eval x""")
P.append(f"""set_option maxHeartbeats 32000000 in
-- `ring` matches the Vandermonde square and the Horner form with `disc5`
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

def wrap_long(text, width=100):
    """Wrap code lines over `width` at spaces (continuation indented 4 more);
    comment lines are left alone (the emitter keeps them short)."""
    out = []
    for line in text.split('\n'):
        if len(line) <= width or line.lstrip().startswith('--'):
            out.append(line); continue
        ind = line[:len(line) - len(line.lstrip())]
        cont = ind + '    '
        cur = ''
        for w in line.lstrip().split(' '):
            if cur and len(cur) + 1 + len(w) > width:
                out.append(cur); cur = cont + w
            else:
                cur = (cur + ' ' + w) if cur else ind + w
        out.append(cur)
    return '\n'.join(out)

section = wrap_long(section)

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
# Kernel-verified `F₂₀`-resolvent identities (dim-5 Maeda)

Contents: {what}.

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
