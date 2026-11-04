#!/usr/bin/env python3 -I
"""G1 data audit for BLUEPRINT index-card (iteration 24, b1).

Re-derives, per weight, the C-matrix design of the blueprint from prodForm
arithmetic and pins it against the LANDED Lean literals (parsed from the
generated weight files — never from index_data.json):

  D1  fb/Atab re-pin (imported iteration-23 machinery): the Lean Atab/M2
      literals equal the re-derived prodForm tables.
  D2  mu (millerCoeff): the fb-coefficients of the Miller basis recomputed
      (a) probe-style from the raw prodForm rows and (b) Lean-def-style from
      the LANDED Atab literal only — the two agree; (b) is what the Lean
      `millerTopC` recursion will kernel-reduce to.
  D3  duality: row0 of (M2m^i) — the COMPOSITION-POWER coordinates
      a_1(T2^i g_j) — equals (Q A) row i (the q-transform of the LANDED A,
      whose rows are the SINGLE-operator coordinates a_{2^i}(g_j)); the
      iter-23 audit only checked |det A| = |det C|.
  D4  p/q transforms (T_{2^i} = sum_s p_{i,s} T2^s, T2^i = sum_s q_{i,s}
      T_{2^s}, the two-term heckeTM_two_mul_even recurrence): inverse pair,
      det Q = 1, |det (Q A)| = Ik.
  D5  THE STAR CERTIFICATE (the identity the per-weight Lean file will
      decide): for all i, j < n,
        A[i][j] = sum_s p[i][s] * sum_c mu[j][c] * (M2lean^s)[0][c]
      with p from k, mu from LANDED Atab (D2b), M2lean the LANDED literal.
  D6  inventory: landed Ik/det_A sign/minpoly_nd presence per weight; the
      minpoly-degree route for the six dim-2 weights (no minpoly_nd landed);
      the c-lemma inventory for hfi.

Output: research/iteration24/index-card/g1_data.json + stdout report.
Exit 1 on any failure.
"""

import json
import re
import sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "research" / "iteration23" / "hecke-index"))
import g1_audit as G  # noqa: E402  (iteration-23 machinery, imported not copied)

MF = ROOT / "MathProof" / "ModularForms"
HI_SMALL = MF / "HeckeIndexSmallWeights.lean"
HI_BIG = MF / "HeckeIndexWeights.lean"
HF = MF / "HeckeFieldWeights.lean"
OUT = Path(__file__).resolve().parent / "g1_data.json"


# --- Lean literal parsing (HeckeIndexWeight namespaces) ---------------------

def parse_index_files():
    """{weight: section} from the two landed HeckeIndex files."""
    out = {}
    for f in [HI_SMALL, HI_BIG]:
        text = f.read_text()
        parts = re.split(r"^namespace (HeckeIndexWeight\d+)$", text, flags=re.M)
        for i in range(1, len(parts), 2):
            out[int(parts[i][len("HeckeIndexWeight"):])] = parts[i + 1]
    assert len(out) == 54, len(out)
    return out


def parse_Ik(section):
    m = re.search(r"def Ik : ℤ :=\n(.*?)\n\n", section, flags=re.S)
    assert m, "no Ik"
    return G.int_expr_eval(re.sub(r"\s+", " ", m.group(1)))


def parse_A_matrix(section):
    m = re.search(r"def A : Matrix \(Fin (\d+)\) \(Fin (\d+)\) ℤ :=\s*!!\[",
                  section)
    assert m, "no A literal"
    n = int(m.group(1))
    start, depth, i = m.end(), 1, m.end()
    while depth:
        c = section[i]
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
        i += 1
    body = section[start:i - 1]
    # chunked entries may span lines and contain parens; split top-level rows
    rows, depth, cur = [], 0, ""
    for ch in body:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == ";" and depth == 0:
            rows.append(cur)
            cur = ""
        else:
            cur += ch
    rows.append(cur)
    assert len(rows) == n, (len(rows), n)
    mat = []
    for r in rows:
        toks, depth, cur = [], 0, ""
        for ch in r:
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
            if ch == "," and depth == 0:
                toks.append(cur)
                cur = ""
            else:
                cur += ch
        toks.append(cur)
        mat.append([G.int_expr_eval(re.sub(r"\s+", " ", t)) for t in toks])
    assert all(len(r) == n for r in mat)
    return mat


def parse_det_A_sign(section):
    m = re.search(r"theorem det_A : A\.det = (-?)Ik", section)
    assert m, "no det_A"
    return -1 if m.group(1) == "-" else 1


def has_minpoly_nd(section):
    return "theorem minpoly_nd" in section


def parse_hmin_inventory():
    """hmin name per weight in HeckeFieldWeights (reference only)."""
    text = HF.read_text()
    parts = re.split(r"^namespace (HeckeFieldWeight\d+)$", text, flags=re.M)
    return {int(parts[i][len("HeckeFieldWeight"):]): parts[i + 1]
            for i in range(1, len(parts), 2)}


# --- the Lean-shaped recursions (mirror the planned Lean defs) --------------

def miller_top_c(atab_z, n):
    """millerTopC atabZ n r — coefficient rows of g_{n-1-t} over fb, EXACTLY
    the planned Lean accumulator (prepend, positions t < r).  Row t of
    accumulator r holds the fb-coefficients of g_{t + (n - r)}."""
    acc = []
    for r in range(n):
        j = n - 1 - r
        # head row: e_j - sum_{t < r} atab(j, t + (n-r)) * acc[t]
        head = [0] * n
        head[j] = 1
        for t in range(r):
            a = atab_z(j, t + (n - r))
            if a:
                rowt = acc[t]
                for c in range(n):
                    if rowt[c]:
                        head[c] -= a * rowt[c]
        acc.insert(0, head)
    # acc is now [row for position 0 .. r = n-1]; row at position t = g_{t}
    return acc  # mu[j][c] = acc[j][c]


def ptrans(c, i_max):
    """p_{i,s}: T_{2^i} = sum_s p_{i,s} T2^s (rows over s, s <= i)."""
    rows = [[1]]
    if i_max >= 1:
        rows.append([0, 1])
    for i in range(i_max - 1):
        prev2, prev1 = rows[i], rows[i + 1]
        new = [0] * (i + 3)
        for s in range(i + 2):
            if prev1[s]:
                new[s + 1] += prev1[s]
            if s >= 1 and prev2[s - 1]:
                new[s - 1] += prev2[s - 1] * (-c)
        rows.append(new)
    return rows


def qtrans(c, i_max):
    """q_{i,s}: T2^i = sum_s q_{i,s} T_{2^s} (s <= i)."""
    rows = [[1]]
    for i in range(i_max):
        prev = rows[i]
        new = [0] * (i + 2)
        for s in range(i + 1):
            if prev[s]:
                new[s + 1] += prev[s]
                if s >= 1:
                    new[s - 1] += prev[s] * c
        rows.append(new)
    return rows


# ---------------------------------------------------------------------------


def main():
    idx = parse_index_files()
    hfinv = parse_hmin_inventory()

    # the iteration-23 parsers for the T3/M2 sources
    t3, small = {}, set()
    for f in [G.T3_SMALL] + list(G.T3_DIM.values()):
        for ns, sec in G.namespaces(f).items():
            t3[G.weight_of(ns)] = (ns, sec)
            if f is G.T3_SMALL:
                small.add(G.weight_of(ns))
    t2dim = {}
    for d, f in G.T2_DIM.items():
        for ns, sec in G.namespaces(f).items():
            t2dim[G.weight_of(ns)] = (ns, sec)
    hr = {}
    for f in [G.HR_BIG, G.HR_SMALL]:
        for ns, sec in G.namespaces(f).items():
            hr[G.hr_weight_of(ns)] = sec

    weights = sorted(t3)
    assert len(weights) == 54
    fail = []
    report = []
    data = {}

    def check(cond, msg):
        if not cond:
            fail.append(msg)
        return cond

    for k in weights:
        ns3, sec3 = t3[k]
        n = len(G.parse_M(sec3))
        atab = G.parse_Atab(sec3)                      # Lean Atab literal
        M2lean = (G.parse_M2(hr[k]) if k in small
                  else G.parse_M(t2dim[k][1]))         # LANDED M2 literal
        secI = idx[k]
        Ik = parse_Ik(secI)
        A_lean = parse_A_matrix(secI)
        dsign = parse_det_A_sign(secI)
        mpnd = has_minpoly_nd(secI)

        # D1: landed tables == re-derived (imported checks)
        rrows = G.basis_raw(k, n)
        mrows = G.basis_miller(k, n)
        M2r = G.op_matrix(k, 2, rrows)
        M2m = G.op_matrix(k, 2, mrows)
        check(M2r == M2lean, f"w{k}: D1 M2 literal != re-derived")
        ok_at = all(atab.get((i, j), 0) == (rrows[i][j + 1] if i < j else 0)
                    for i in range(n) for j in range(n))
        check(ok_at, f"w{k}: D1 Atab literal != raw prodForm rows")

        # D2: mu two ways
        atab_z = lambda i, j: atab.get((i, j), 0)
        mu = miller_top_c(atab_z, n)                   # Lean-def style
        Tmat = [[0] * n for _ in range(n)]             # probe style (rrows)
        for i in range(n):
            for j in range(i, n):
                v = int(i == j)
                for t in range(i, j):
                    v -= Tmat[i][t] * rrows[t][j + 1]
                Tmat[i][j] = v
        check(mu == Tmat, f"w{k}: D2 millerCoeff(Atab) != probe Tmat(rrows)")
        # mu really is the fb-expansion of the Miller basis
        check(all(sum(mu[j][c] * rrows[c][m] for c in range(n)) == mrows[j][m]
                  for j in range(n) for m in range(1, 4 * n)),
              f"w{k}: D2 mu . rrows != miller rows")

        # D3: duality, two flavors — the landed A holds the T_{2^i} (single
        # operator) coordinates a_{2^i}(g_j); row0 of the Miller M2-POWERS
        # holds the T2^i (composition power) coordinates.  They differ by
        # the q-transform (D4), so D3 checks row0(M2m^i) == Q . A row i.
        Pows = [G.matpow(M2m, i) for i in range(n)]
        PowsL = [G.matpow(M2lean, i) for i in range(n)]

        # D4: p/q transforms
        c = 2 ** (k - 1)
        P = ptrans(c, n - 1)
        Q = qtrans(c, n - 1)
        # inverse pair: sum_s q[i][s] p[s][t] = delta_{it}   (s <= min(i, ...))
        ok_inv = True
        for i in range(n):
            for t in range(n):
                acc = 0
                for s in range(n):
                    qi = Q[i][s] if s < len(Q[i]) else 0
                    pt = P[s][t] if t < len(P[s]) else 0
                    acc += qi * pt
                if acc != int(i == t):
                    ok_inv = False
        check(ok_inv, f"w{k}: D4 p/q not inverse")
        dQ = G.det([[(Q[i][s] if s < len(Q[i]) else 0) for s in range(n)]
                    for i in range(n)])
        check(dQ == 1, f"w{k}: D4 det Q = {dQ} != 1")
        QA = [[sum((Q[i][s] if s < len(Q[i]) else 0) * A_lean[s][j]
                   for s in range(n)) for j in range(n)] for i in range(n)]
        check(abs(G.det(QA)) == Ik, f"w{k}: D4 |det(QA)| != Ik")

        check(all(Pows[i][0][j] == QA[i][j]
                  for i in range(n) for j in range(n)),
              f"w{k}: D3 row0(M2m^i) != (Q A) row i")

        # D5: THE STAR CERTIFICATE on LANDED literals
        ok_star = True
        for i in range(n):
            for j in range(n):
                acc = 0
                for s in range(n):
                    ps = P[i][s] if s < len(P[i]) else 0
                    if ps:
                        acc += ps * sum(mu[j][c] * PowsL[s][0][c]
                                        for c in range(n))
                if acc != A_lean[i][j]:
                    ok_star = False
        check(ok_star, f"w{k}: D5 star certificate failed")

        # D6: inventory
        hmin_ref = "theorem hmin" in hfinv[k]
        check(hmin_ref, f"w{k}: D6 no HeckeFieldWeight{k}.hmin reference")
        ccount = len(re.findall(r"^lemma c(\d+) ", sec3, flags=re.M))
        check(ccount == n, f"w{k}: D6 c-lemma count {ccount} != {n}")
        if n >= 6:
            check(mpnd, f"w{k}: D6 expected minpoly_nd landed")
        else:
            check(mpnd == (n > 2), f"w{k}: D6 minpoly_nd presence unexpected")

        detA = G.det(A_lean)
        check(detA == dsign * Ik, f"w{k}: det_A sign/literal mismatch")

        mu_dg = max((len(str(abs(v))) for row in mu for v in row), default=0)
        star_terms = n * n * n
        data[k] = {
            "dim": n, "Ik": Ik, "detA_sign": dsign, "minpoly_nd": mpnd,
            "mu_maxdigits": mu_dg,
            "Pmax": max(abs(v) for row in P for v in row),
            "Qmax": max(abs(v) for row in Q for v in row),
        }
        report.append(f"w{k:3d} dim {n:2d}: Ik {len(str(Ik)):3d}d sign {dsign:+d} "
                      f"mpnd={int(mpnd)} mu<={mu_dg}d "
                      f"Pmax={len(str(abs(data[k]['Pmax'])))}d c-count={ccount}")

    OUT.write_text(json.dumps(data, indent=1))
    print("\n".join(report))
    print(f"\n{len(weights)} weights, failures: {len(fail)}")
    for f_ in fail[:30]:
        print("  " + f_)
    if fail:
        sys.exit(1)
    print("ALL CHECKS PASSED; data written to", OUT)


if __name__ == "__main__":
    main()
