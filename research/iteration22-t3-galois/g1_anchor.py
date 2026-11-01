#!/usr/bin/env python3
"""Iteration-22 T3-Galois G1 audit: anchor the T3 charpoly data.

Ground truth = the `P` literals of the committed, Modal-verified
`MathProof/ModularForms/MaedaT3Dim{6..10}Weights.lean` (each file proves
`charpoly_T3 : T3.charpoly = P.map (Int.castRingHom ℂ)` kernel-side).
This script parses every `P` (chunked coefficient literals included),
evaluates it to a big-endian integer list, and cross-checks:

  1. Lean P  ==  census charpoly  (research/iteration20/data/maeda_t3_dim6_10.json)
  2. census `matrix` charpoly (numpy-free integer Leverrier/Bareiss via
     sympy-free own code: charpoly by fraction-free Faddeev–LeVerrier over ℚ)
     == census charpoly  (internal-consistency of the census JSON)
  3. monic, degree = dim, 30 weights total, dims 6..10 x 6 weights.

Exit code 0 = all anchors hold; prints a compact table.
"""

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
MF = ROOT / "MathProof/ModularForms"
CENSUS = ROOT / "research/iteration20/data/maeda_t3_dim6_10.json"

# term: [+-]? C ( <digits/ws/*+^ parens> ) * (X : ℤ[X]) ^ <exp>   or trailing C(...)
TERM = re.compile(
    r"([+-])?\s*C\s*\(\s*([^()+]+(?:\([^()]*\))?[^()]*)\)\s*(?:\*\s*\(X : ℤ\[X\]\)\s*\^\s*(\d+))?",
    re.M,
)
NUMOK = re.compile(r"^[\d\s+*^]+$")


def eval_coeff(txt: str) -> int:
    """Evaluate `num * 10 ^ e + num (+ …)` — chunk literals may zero-pad, so
    never `eval`: Python rejects leading zeros in decimal literals."""
    txt = " ".join(txt.split())  # collapse chunked multi-line literals
    assert NUMOK.match(txt), f"unexpected coefficient text: {txt!r}"
    total = 0
    for part in txt.split("+"):
        part = part.strip()
        if "*" in part:
            num, exp = part.split("*")
            assert exp.strip().startswith("10 ^"), part
            total += int(num) * 10 ** int(exp.strip()[4:])
        else:
            total += int(part)
    return total


def parse_P(text: str, k: int) -> list[int]:
    """Extract the `P` def of namespace MaedaT3Weight{k} as big-endian ints."""
    # isolate the namespace block
    m = re.search(rf"namespace MaedaT3Weight{k}\b(.*?)\nend MaedaT3Weight{k}\b", text, re.S)
    assert m, f"namespace MaedaT3Weight{k} not found"
    block = m.group(1)
    d = re.search(r"noncomputable def P : ℤ\[X\] :=(.*?)\n\ntheorem P_natDegree", block, re.S)
    assert d, f"P not found in MaedaT3Weight{k}"
    body = d.group(1)
    n = None
    coeffs: dict[int, int] = {}
    for sign, ctext, exp in TERM.findall(body):
        val = eval_coeff(ctext)
        if sign == "-":
            val = -val
        e = int(exp) if exp else 0
        assert e not in coeffs, f"duplicate exponent {e} in weight {k}"
        coeffs[e] = val
        n = max(n or 0, e)
    assert coeffs.get(n) == 1, f"weight {k}: not monic in the literal ({coeffs.get(n)})"
    return [coeffs.get(i, 0) for i in range(n, -1, -1)]  # big-endian


def charpoly_fl2(mat: list[list[int]]) -> list[int]:
    """Exact charpoly of an integer matrix by the Faddeev–LeVerrier recurrence
    M_1 = A, M_k = A·M_{k-1} − (tr(A·M_{k-1})/ (k−1))·I …  Instead of the
    textbook one-off (error-prone), use the plain division-free version over
    ℚ: p(x) = det(xI − A) via interpolation-free Hessenberg …  Simplest exact
    and verified route:  expansion by the Berlekamp-style identity is
    overkill; use  det(xI − A) = Σ_{k} (−1)^k tr(∧^k A) x^{n−k}  computed by
    the Newton identities from the power sums s_m = tr(A^m)."""
    n = len(mat)

    def mul(A, B):
        return [[sum(A[i][t] * B[t][j] for t in range(n)) for j in range(n)] for i in range(n)]

    from fractions import Fraction as Fr
    # power sums s_m = tr(A^m), m = 1..n
    P = [[Fr(x) for x in row] for row in mat]
    s = []
    for _ in range(n):
        s.append(sum(P[i][i] for i in range(n)))
        P = mul(P, [[Fr(x) for x in row] for row in mat])
    # Newton: e_0 = 1; k e_k = Σ_{i=1..k} (−1)^{i−1} e_{k−i} s_i
    e = [Fr(1)]
    for k in range(1, n + 1):
        acc = Fr(0)
        for i in range(1, k + 1):
            acc += (Fr(-1) ** (i - 1)) * e[k - i] * s[i - 1]
        e.append(acc / k)
    # det(xI − A) = Σ_k (−1)^k e_k x^{n−k}
    out = [int((Fr(-1) ** k) * e[k]) for k in range(n + 1)]
    assert out[0] == 1
    return out


def main() -> int:
    census = {w["k"]: w for w in json.loads(CENSUS.read_text())}
    lean: dict[int, list[int]] = {}
    for d in range(6, 11):
        text = (MF / f"MaedaT3Dim{d}Weights.lean").read_text()
        ks = sorted(int(m) for m in re.findall(r"namespace MaedaT3Weight(\d+)\b", text))
        for k in ks:
            lean[k] = parse_P(text, k)
    assert len(lean) == 30, len(lean)
    bad = 0
    for k in sorted(lean):
        cp = lean[k]
        n = len(cp) - 1
        c = census[k]
        ok_census = cp == c["charpoly"]
        ok_matrix = charpoly_fl2(c["matrix"]) == c["charpoly"]
        ok_meta = c["dim"] == n and c["charpoly"][0] == 1
        status = "OK" if (ok_census and ok_matrix and ok_meta) else "MISMATCH"
        if status != "OK":
            bad += 1
        print(f"k={k:3d} dim={n} census={'=' if ok_census else 'X'} "
              f"matrix→cp={'=' if ok_matrix else 'X'} {status}")
    print(f"\n{len(lean)} weights, {bad} mismatches")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
