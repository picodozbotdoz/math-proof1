#!/usr/bin/env python3
"""Prototype for the memory study: certify e_K(Θ) for the F20 resolvent
with (1) the elementary-symmetric recurrence E_k += Θ_j · E_{k-1} instead of
C(6,K) brute-force products, and (2) the two sides checked in SEPARATE
declarations against one shared literal (kernel caches reset in between).
Usage: proto_dp.py K OUT.lean   (reads the Poly5 chains from the Id modules)"""
import sys
K, out = int(sys.argv[1]), sys.argv[2]
base = "MathProof/ModularForms/"
mod = {4: "MaedaGalois5IdE4", 5: "MaedaGalois5IdE5", 6: "MaedaGalois5IdE6"}.get(K, "MaedaGalois5IdBase")
src = open(sys.argv[0].replace("proto_dp.py", "proto_stepwise.py")).read().split("# --- flatten the chain")[0]
g = {"__name__": "x"}
text = open(base + "MaedaGalois5IdBase.lean").read() + open(base + mod + ".lean").read()
open("/tmp/poly5_cat.lean", "w").write(text)
exec(src.replace("src, K, out_path, modname = sys.argv[1:5]",
                 "src = '/tmp/poly5_cat.lean'"), g)
ev, padd, pmul = g["ev"], g["padd"], g["pmul"]
TH = [ev(f"Theta{j}") for j in range(6)]
ONE = {(0, 0, 0, 0, 0): 1}

L = [f"import {('MathProof.ModularForms.' + mod)}", "",
     "/-! Prototype (memory study): e_K(Θ) by the symmetric-function recurrence,",
     "LHS and RHS checked against one literal in separate declarations. -/", "",
     "set_option linter.style.longLine false", "", "namespace DPProto", "open Poly5 MaedaGalois", ""]
E = {}
def nm(j, k): return f"E{j}_{k}"
for j in range(6):
    for k in range(0, min(K, j + 1) + 1):
        if k == 0:
            E[(j, 0)] = ONE
            if j == 0: L.append("def E0_0 : Poly5 := [(Mon.one, 1)]")
            continue
        prev = E.get((j - 1, k), {}) if j > 0 else {}
        below = E[(j - 1, k - 1)] if j > 0 else ONE
        E[(j, k)] = padd(prev, pmul(TH[j], below))
        below_nm = nm(j - 1, k - 1) if (j > 0 and k > 1) else "E0_0"
        term = f"pMul Theta{j} {below_nm}"
        if j > 0 and (j - 1, k) in E and E[(j - 1, k)]:
            L.append(f"def {nm(j, k)} : Poly5 := pAdd {nm(j - 1, k)} ({term})")
        else:
            L.append(f"def {nm(j, k)} : Poly5 := {term}")
lit = E[(5, K)]

def mono(m, c):
    return f"(({m[0]}, ({m[1]}, ({m[2]}, ({m[3]}, {m[4]})))), {c})"
items = [mono(m, c) for m, c in sorted(lit.items())]
CH = 64
names = []
for i in range(0, len(items), CH):
    cn = f"Lit_c{i // CH}"; names.append(cn)
    ch = items[i:i + CH]
    rows = [", ".join(ch[r:r + 3]) for r in range(0, len(ch), 3)]
    L.append(""); L.append(f"def {cn} : Poly5 :=\n  [" + ",\n   ".join(rows) + "]")
def tree(ns):
    if len(ns) == 1: return ns[0]
    h = len(ns) // 2
    return f"({tree(ns[:h])} ++ {tree(ns[h:])})"
L += ["", f"def Lit : Poly5 := {tree(names)}", "",
      "set_option maxHeartbeats 0 in",
      f"theorem lhs_ok : E5_{K} = Lit := eq_of_pBeq (by decide +kernel)", "",
      "set_option maxHeartbeats 0 in",
      f"theorem rhs_ok : e{K}RHS = Lit := eq_of_pBeq (by decide +kernel)", "",
      "end DPProto", ""]
open(out, "w").write("\n".join(L))
print(f"e{K}: {len(lit)} terms, {sum(1 for l in L if l.startswith('def E'))} recurrence defs, {len(names)} literal chunks")
