#!/usr/bin/env python3 -I
"""G1 audit for blueprint index-cyclic (iteration 24, worker index-cyclic).

Parses the LANDED per-weight literals for the 18 dims-2-4 weights and checks,
independently (pure integer arithmetic, no trust in the Lean proofs being
re-run — they are kernel-verified already; this audit pins the DATA the
blueprint's G2/G3 wiring will consume):

  * `HeckeIndexWeightKK.Ik`   (from HeckeIndexSmallWeights.lean) == index_data.json Ik;
  * `HeckeIndexWeightKK.Dn`   (dims 3-4) == the `D` of HeckeRatWeightKK.scaled_id
    (HeckeRationalSmallWeights.lean) — the two landed D forms agree;
  * D > 0, Ik > 0;
  * the landed Bézout witnesses `bez`/`bezc` satisfy sum bez_j * cert_j + bezc * D = 1
    (so the witness (cert, D) is reduced: Dred = D);
  * arithmetically gcd(cert_0..cert_{n-1}, D) = 1 and D == index_data.json Dred;
  * D | Ik arithmetically (mirrors the landed D_dvd_Ik);
  * THE THEOREM TARGET (numerically): D == Ik at all twelve dims-3-4 weights,
    D == 1 (= Ik) at all six dim-2 weights;
  * the D • T3 identity certificate exists per weight (scaled_id over cert).

Run: python3 -I g1_audit_cyclic.py   (exit 0 = all checks green).
"""
import json
import math
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
G1 = HERE.parent.parent / "iteration23" / "hecke-index"
sys.path.insert(0, str(G1))

from g1_audit import int_expr_eval, parse_cert_N, parse_scaled_id_D  # noqa: E402

WT = HERE.parent.parent.parent
HSW = WT / "MathProof" / "ModularForms" / "HeckeIndexSmallWeights.lean"
HRW = WT / "MathProof" / "ModularForms" / "HeckeRationalSmallWeights.lean"
DATA = G1 / "index_data.json"

DIMS24 = [24, 28, 30, 32, 34, 38]                     # dim 2
DIMS34 = [36, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 62]  # dims 3-4 (12)


def sections(path, prefix):
    """Split a generated file into `namespace <prefix>KK … end` blocks."""
    text = path.read_text()
    out = {}
    for m in re.finditer(r"namespace (" + prefix + r"(\d+))\b(.*?)\nend " + prefix, text, flags=re.S):
        out[int(m.group(2))] = m.group(3)
    return out


def parse_def_int(section, name):
    """The body of `def <name> : ℤ := <int-expr>` (possibly multiline)."""
    m = re.search(r"def " + name + r" : ℤ :=\n?\s*(.*?)(?=\n\n|\n/--|\ntheorem|\ndef)", section, flags=re.S)
    assert m, f"no def {name}"
    return int_expr_eval(re.sub(r"\s+", " ", m.group(1)).strip())


def parse_def_int_or_none(section, name):
    if f"def {name} : ℤ" not in section:
        return None
    return parse_def_int(section, name)


def parse_natfun_or_none(section, name):
    """The `def <name> : ℕ → ℤ` arms (bez etc.), or None when absent (dim-2
    weights carry no Bézout block: `D_dvd_Ik` is `one_dvd` there)."""
    block = re.search(r"def " + name + r" : ℕ → ℤ\n(.*?)\n  \| _ =>", section, flags=re.S)
    if not block:
        return None
    out = {}
    for line in block.group(1).splitlines():
        m = re.match(r"  \| (\d+) =>\s*(.*)", line)
        if m:
            out[int(m.group(1))] = int_expr_eval(m.group(2).strip())
    return out


def parse_det_A_sign(section):
    """`theorem det_A : A.det = ?Ik` — record the sign convention."""
    m = re.search(r"theorem det_A : A\.det = (-?)Ik", section)
    assert m, "no det_A"
    return -1 if m.group(1) == "-" else 1


def main():
    idx = sections(HSW, "HeckeIndexWeight")
    rat = sections(HRW, "HeckeRatWeight")
    data = json.loads(DATA.read_text())
    weights = DIMS24 + DIMS34
    assert set(idx) >= set(weights), "HeckeIndexSmallWeights missing weights"
    assert set(rat) >= set(weights), "HeckeRationalSmallWeights missing weights"

    failures = 0
    rows = []
    for k in weights:
        dim = data[str(k)]["dim"]
        expect_dim = 2 if k in DIMS24 else None
        if expect_dim is None:
            expect_dim = data[str(k)]["dim"]
        assert data[str(k)]["dim"] == (2 if k in DIMS24 else (3 if k in [36, 40, 42, 44, 46, 50] else 4)), k

        ik_lean = parse_def_int(idx[k], "Ik")
        ik_json = data[str(k)]["Ik"]
        dn_lean = parse_def_int_or_none(idx[k], "Dn")
        cert = parse_cert_N(rat[k])
        d_scaled = parse_scaled_id_D(rat[k])
        bez = parse_natfun_or_none(idx[k], "bez")
        bezc = parse_def_int_or_none(idx[k], "bezc")
        det_sign = parse_det_A_sign(idx[k])

        n = data[str(k)]["dim"]
        certs = [cert.get(j, 0) for j in range(n)]
        d = dn_lean if dn_lean is not None else d_scaled

        checks = {
            "Ik_lean==Ik_json": ik_lean == ik_json,
            "Ik>0": ik_lean > 0,
            "D>0": d > 0,
            "Dn==scaled_id_D": dn_lean is None or dn_lean == d_scaled,
            "bez_identity": bez is None or (
                sum(bez.get(j, 0) * certs[j] for j in range(n)) + bezc * d == 1
            ),
            "gcd(N,D)=1 (Dred=D)": math.gcd(d, math.gcd(*[abs(c) for c in certs])) == 1,
            "D==Dred_json": d == data[str(k)]["Dred"],
            "D|Ik": d != 0 and ik_lean % d == 0,
            "TARGET D==Ik": d == ik_lean,
        }
        rows.append((k, dim, ik_lean, d, d_scaled, det_sign, checks))
        for name, ok in checks.items():
            if not ok:
                failures += 1
                print(f"FAIL w{k}: {name}")

    hdr = f"{'w':>4} {'dim':>3} {'Ik':>12} {'D':>10} {'D(scaled)':>10} {'sgn':>3}  checks"
    print(hdr)
    print("-" * len(hdr))
    for k, dim, ik, d, ds, sgn, checks in rows:
        flag = "ok" if all(checks.values()) else "XX"
        print(f"{k:>4} {dim:>3} {ik:>12} {d:>10} {ds:>10} {sgn:>+3}  {flag}")
    # The six dim-2 weights: Ik.natAbs = 1 (the iff's left side there)
    dim2 = [r for r in rows if r[1] == 2]
    assert len(dim2) == 6 and all(r[2] == 1 for r in dim2), "dim-2 Ik != 1"
    # The twelve dims-3-4 weights: D = Ik != 1 (so 𝕋 ≠ ℤ[T₂] there via the iff)
    dim34 = [r for r in rows if r[1] in (3, 4)]
    assert len(dim34) == 12 and all(r[2] == r[3] and r[2] != 1 for r in dim34)
    print(f"\n{len(rows)} weights: dim-2 Ik=1 x{len(dim2)}, dims-3-4 D=Ik>1 x{len(dim34)}; "
          f"failures={failures}")
    if failures:
        sys.exit(1)
    print("G1 AUDIT GREEN")


if __name__ == "__main__":
    main()
