#!/usr/bin/env python3
"""Prototype: re-certify one Poly5 identity (`<K>LHS = <K>RHS` from a
MaedaGalois5Id* module) STEPWISE — every pMul/pAdd node becomes its own
`decide +kernel` over literal inputs, so the kernel's per-declaration caches
are dropped between steps.  Usage:
  proto_stepwise.py SRC.lean K OUT.lean MODULE_NAME
"""
import re, sys

src, K, out_path, modname = sys.argv[1:5]
text = open(src).read()

# --- parse `def NAME : Poly5 :=` bodies -------------------------------------
defs = {}
for m in re.finditer(r'^def (\w+) : Poly5 :=(.*?)(?=^\S)', text, re.S | re.M):
    defs[m.group(1)] = " ".join(m.group(2).split())

def tok(s):
    return re.findall(r'\(|\)|\[|\]|,|-?\d+|[A-Za-z_][\w.]*', s)

def parse_lit(s):
    # [((a, (b, (c, (d, e)))), c), ...]  ;  Mon.one allowed
    s = s.replace("Mon.one", "(0, (0, (0, (0, 0))))")
    nums = [int(x) for x in re.findall(r'-?\d+', s)]
    assert len(nums) % 6 == 0, s[:80]
    p = {}
    for i in range(0, len(nums), 6):
        m = tuple(nums[i:i + 5]); c = nums[i + 5]
        p[m] = p.get(m, 0) + c
    return {m: c for m, c in p.items() if c}

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
            m = tuple(a + b for a, b in zip(m1, m2))
            r[m] = r.get(m, 0) + c1 * c2
            if r[m] == 0: del r[m]
    return r

# expression AST: name | ('pMul'|'pAdd', a, b) | ('lit', poly)
def parse_expr(s):
    s = s.strip()
    if s.startswith('['):
        return ('lit', parse_lit(s))
    t = tok(s)
    pos = 0
    def atom():
        nonlocal pos
        if t[pos] == '(':
            pos += 1; e = app(); assert t[pos] == ')'; pos += 1; return e
        nm = t[pos]; pos += 1; return nm
    def app():
        nonlocal pos
        if t[pos] in ('pMul', 'pAdd'):
            op = t[pos]; pos += 1
            a = atom(); b = atom(); return (op, a, b)
        return atom()
    return app()

ast = {n: parse_expr(b) for n, b in defs.items()}
val = {}
def ev(e):
    if isinstance(e, str):
        if e not in val: val[e] = ev(ast[e])
        return val[e]
    if e[0] == 'lit': return e[1]
    a, b = ev(e[1]), ev(e[2])
    return pmul(a, b) if e[0] == 'pMul' else padd(a, b)

# --- flatten the chain under LHS/RHS into single-op steps ------------------
steps = []          # (stepname, op, argname, argname, poly)
lits = {}           # name -> poly (leaves and step results)
done = {}
def flat(e, hint):
    if isinstance(e, str):
        if e in done: return done[e]
        r = flat(ast[e], e); done[e] = r; return r
    if e[0] == 'lit':
        nm = f"L_{hint}"; lits[nm] = e[1]; return nm
    a = flat(e[1], hint + "a"); b = flat(e[2], hint + "b")
    nm = f"S_{hint}"
    p = pmul(lits[a], lits[b]) if e[0] == 'pMul' else padd(lits[a], lits[b])
    lits[nm] = p
    steps.append((nm, e[0], a, b))
    return nm

lhs = flat(f"{K}LHS", f"{K}LHS"); rhs = flat(f"{K}RHS", f"{K}RHS")
assert lits[lhs] == lits[rhs], "identity mismatch"

def mono(m):
    return f"(({m[0]}, ({m[1]}, ({m[2]}, ({m[3]}, {m[4]})))), {m[5]})"

CH = 64
def emit_lit(nm, p):
    items = [mono(m + (c,)) for m, c in sorted(p.items())]
    if not items:
        return [f"def {nm} : Poly5 := []"]
    chunks = [items[i:i + CH] for i in range(0, len(items), CH)]
    out = []
    names = []
    for i, ch in enumerate(chunks):
        cn = f"{nm}_c{i}"; names.append(cn)
        rows = []
        for j in range(0, len(ch), 3):
            rows.append(", ".join(ch[j:j + 3]))
        out.append(f"def {cn} : Poly5 :=\n  [" + ",\n   ".join(rows) + "]")
    # balanced append tree
    def tree(ns):
        if len(ns) == 1: return ns[0]
        h = len(ns) // 2
        return f"({tree(ns[:h])} ++ {tree(ns[h:])})"
    out.append(f"def {nm} : Poly5 := {tree(names)}")
    return out

L = [f"import MathProof.ModularForms.MaedaGalois5Defs", "import MathProof.ModularForms.Poly5", "",
     "/-! Prototype: stepwise kernel certificates (memory experiment). -/", "",
     "set_option linter.style.longLine false", "set_option maxRecDepth 100000", "",
     "namespace StepProto", "open Poly5", ""]
leafs = [n for n in lits if n.startswith("L_")]
for n in leafs:
    L += emit_lit(n, lits[n]); L.append("")
for nm, op, a, b in steps:
    L += emit_lit(nm, lits[nm])
    sz = max(len(lits[a]), len(lits[b]), len(lits[nm]))
    hb = max(200000, 400 * sz * min(len(lits[a]), len(lits[b])) + 200000)
    L.append(f"set_option maxHeartbeats {hb} in")
    L.append(f"theorem {nm}_ok : {op} {a} {b} = {nm} := eq_of_pBeq (by decide +kernel)")
    L.append("")
L.append(f"theorem final_ok : {lhs} = {rhs} := eq_of_pBeq (by decide +kernel)")
L += ["", "end StepProto", ""]
open(out_path, "w").write("\n".join(L))
big = max(steps, key=lambda s: len(lits[s[0]]))
print(f"{len(steps)} steps, {len(leafs)} leaves; largest step {big[0]}: "
      f"{len(lits[big[2]])} x {len(lits[big[3]])} -> {len(lits[big[0]])} terms; "
      f"final {len(lits[lhs])} terms")
