import sys
src = open(sys.argv[1]).read().split("# --- flatten the chain")[0]
g = {"__name__": "x"}
exec(src.replace("src, K, out_path, modname = sys.argv[1:5]", "src = 'MathProof/ModularForms/MaedaGalois5IdBase.lean'"), g)
ev, padd = g["ev"], g["padd"]
TH = [ev(f"Theta{j}") for j in range(6)]
print("Theta sizes", [len(t) for t in TH])
def mul_cost(a, b, tree):
    x, y = (a, b) if len(a) <= len(b) else (b, a)
    if tree:
        lvl = [{tuple(p+q for p,q in zip(m,m2)): c*c2 for m2,c2 in y.items()} for m,c in sorted(x.items())]
        w = len(x)*len(y)
        while len(lvl) > 1:
            nxt=[]
            for i in range(0,len(lvl)-1,2):
                w += len(lvl[i])+len(lvl[i+1]); nxt.append(padd(lvl[i],lvl[i+1]))
            if len(lvl)%2: nxt.append(lvl[-1])
            lvl=nxt
        return lvl[0], w
    acc={}; w=0
    for m,c in reversed(sorted(x.items())):
        sc={tuple(p+q for p,q in zip(m,m2)): c*c2 for m2,c2 in y.items()}
        w += len(y)+len(sc)+len(acc); acc=padd(sc,acc)
    return acc, w
for tree in (False, True):
    # E[k] after processing Θ_0..Θ_j ; cost to reach E_K needs only k <= K
    for K in (4,5,6):
        E = [{(0,0,0,0,0):1}] + [{} for _ in range(6)]
        w = 0
        for j in range(6):
            for k in range(min(K, j+1), 0, -1):
                if not E[k-1]: continue
                prod, wm = mul_cost(TH[j], E[k-1], tree)
                w += wm + len(E[k]) + len(prod)
                E[k] = padd(E[k], prod)
        print(f"tree={tree} e{K}: DP work {w/1e6:.2f} M, |e{K}| = {len(E[K])}")
