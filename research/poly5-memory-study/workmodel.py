import re, sys, importlib.util
spec = importlib.util.spec_from_file_location("pw", sys.argv[1]); 
# reuse parser pieces from proto_stepwise without running its main
src = open(sys.argv[1]).read().split("# --- flatten the chain")[0]
ns = {"__name__": "x"}
def run(path, roots):
    g = dict(ns); g["sys"] = type("S", (), {"argv": ["", path, "x", "/dev/null", "x"]})
    exec(src.replace("src, K, out_path, modname = sys.argv[1:5]", f"src = {path!r}"), g)
    ast, ev, padd, pmul = g["ast"], g["ev"], g["padd"], g["pmul"]
    ast["DLHS2sq"] = ("pMul", "DLHS2", "DLHS2")
    memo = {}
    def cost(e):
        # returns (poly, work) with work = kernel list-cell operations
        key = e if isinstance(e, str) else None
        if key and key in memo: return memo[key]
        if isinstance(e, str): r = cost(ast[e]); memo[key] = (r[0], 0 if key in seen else r[1]); seen.add(key); return r
        if e[0] == 'lit': return (e[1], len(e[1]))
        (a, wa), (b, wb) = cost(e[1]), cost(e[2])
        if e[0] == 'pAdd':
            return (padd(a, b), wa + wb + len(a) + len(b))
        if TREE:
            # pMulT: scaled copies summed pairwise in a balanced tree; the
            # smaller operand supplies the copies
            x, y = (a, b) if len(a) <= len(b) else (b, a)
            lvl = []; w = 0
            for m, c in sorted(x.items()):
                lvl.append({tuple(p + q for p, q in zip(m, m2)): c * c2 for m2, c2 in y.items()})
                w += len(y)
            while len(lvl) > 1:
                nxt = []
                for i in range(0, len(lvl) - 1, 2):
                    w += len(lvl[i]) + len(lvl[i + 1]); nxt.append(padd(lvl[i], lvl[i + 1]))
                if len(lvl) % 2: nxt.append(lvl[-1])
                lvl = nxt
            return (lvl[0] if lvl else {}, wa + wb + w)
        # pMul a b = pAdd (pScale t b) (pMul ts b), processed from the end
        items = sorted(a.items()); acc = {}; w = 0
        for m, c in reversed(items):
            sc = {tuple(x + y for x, y in zip(m, m2)): c * c2 for m2, c2 in b.items()}
            w += len(b) + len(sc) + len(acc)
            acc = padd(sc, acc)
        return (acc, wa + wb + w)
    tot = 0
    for r in roots:
        seen.clear(); p, w = cost(r); tot += w
    return tot
seen = set()
import os
TREE = os.environ.get('TREE') == '1'
for path, k in [("MathProof/ModularForms/MaedaGalois5IdBase.lean", "e2"), ("MathProof/ModularForms/MaedaGalois5IdBase.lean", "e3"),
                ("/tmp/cat_d.lean", "d"),
                ("/tmp/cat_e4.lean", "e4"), ("/tmp/cat_e5.lean", "e5"),
                ("/tmp/cat_e6.lean", "e6")]:
    roots = ["DLHS2", "dRHS"] if k == "d" else [f"{k}LHS", f"{k}RHS"]
    if k == "d":
        print(k, "work(M)", round(run(path, ["DLHS2sq", "dRHS"]) / 1e6, 2))
    else:
        print(k, "work(M)", round(run(path, roots) / 1e6, 2), " LHS", round(run(path, [roots[0]]) / 1e6, 2), " RHS", round(run(path, [roots[1]]) / 1e6, 2))
