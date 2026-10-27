#!/usr/bin/env python3
"""Certificate data for the six dim-5 S5 instances (research only).

For each weight k in {60,64,66,68,70,74} with charpoly
  P_k = X^5 + a X^4 + b X^3 + c X^2 + d X + e  (proved in MaedaDim5Weights):
  * disc_k = disc5(a,b,c,d,e) exactly (integer);
  * a small prime q with disc_k a non-residue mod q (certifies non-square);
  * R_k(Y) = resolvent5(a..e; Y), the F20 sextic (integer coefficients);
  * a small prime l with R_k having no root mod l (certifies no rational root).
Everything re-verified against the symmetric-function data in
/tmp/maeda5/s5_resolvent.json (itself exact-verified at random points).
"""
import json

data = json.load(open("/tmp/maeda5/s5_resolvent.json"))

def items(key):
    return {m: c for m, c in data[key].items()}

DISC_E = items("disc")
EJ = {j: data["ej_theta"][str(j)] for j in range(1, 7)}

def ev(sol, es):
    import math
    return sum(c * math.prod(e ** a for e, a in zip(es, [int(x) for x in m]))
               for m, c in sol.items())

def isp(n):
    return n > 1 and all(n % i for i in range(2, int(n ** .5) + 1))

# the six charpolys from tools/gen_maeda.py (proved in MaedaDim5Weights.lean)
CPS = {
    60: [449691864, -2209450184054433792, -736010060393513697870348288,
         810634763334812972416233648439689216,
         263222216157060824115203098902237248565018624],
    64: [-507315096, -26316207229657439232, 7816999697067374824780726272,
         93356730870958242939964792647614201856,
         59899702063757157544982491709928053576589901824],
    66: [3959709648, -142850166119005483008, -339986038308627409973683421184,
         4888759358323485530147825225712235708416,
         6737365607750178848535412403321340119893376237568],
    68: [-5554901256, -528742419683384143872, 1360506199877236618906967212032,
         50978026392314038029857853615859298205696,
         -224135116306806567372209572838489759238644853374976],
    70: [18005734368, -1942747456996431618048, -14539211744046993293953166475264,
         613518461067953168654246762332094963122176,
         4169744246282611427836654706819235757668276180615168],
    74: [92089333488, -19817164982845968703488, -1377989142595747748686715833810944,
         11802708847432637761332792635527627366465536,
         113628227457643966226006850359168010340399423074336768],
}

out = {}
for k, (a, b, c, d, e) in CPS.items():
    es = [-a, b, -c, d, -e]  # e1..e5 of the roots
    disc = ev(DISC_E, es)
    assert disc != 0
    # non-residue prime for disc
    q = None
    for qq in range(3, 400):
        if isp(qq) and disc % qq != 0 and pow(disc % qq, (qq - 1) // 2, qq) == qq - 1:
            q = qq
            break
    # resolvent coefficients: Y^6 - E1 Y^5 + E2 Y^4 - E3 Y^3 + E4 Y^2 - E5 Y + E6
    R = []
    for j in range(1, 7):
        R.append(((-1) ** j) * ev(EJ[j], es))
    # no-root prime for R
    l = None
    for ll in range(3, 400):
        if not isp(ll):
            continue
        # leading coeff 1; evaluate R (descending, degree 6) at all points mod ll
        if all((x ** 6 + sum(co * x ** (5 - i) for i, co in enumerate(R))) % ll
               for x in range(ll)):
            l = ll
            break
    out[k] = {"a": a, "b": b, "c": c, "d": d, "e": e,
              "disc": str(disc), "disc_q": q, "R": R, "R_l": l}
    print(f"k={k}: disc non-residue mod {q};  R no-root mod {l};  "
          f"R coeffs (digits): {[len(str(abs(x))) for x in R]}")

json.dump(out, open("/tmp/maeda5/s5_certs.json", "w"), indent=1)
print("saved /tmp/maeda5/s5_certs.json")

# cross-check: disc equals the Sylvester discriminant of the quintic (independent)
def sylv_disc(cp, p):
    """Sylvester-determinant discriminant of a monic quintic mod p."""
    n = 5
    f = [x % p for x in cp]
    fp = [((5 - i) * f[i]) % p for i in range(5)]
    m = 2 * n - 1
    Syl = [[0] * m for _ in range(m)]
    for r in range(n - 1):
        for i, cf in enumerate(f):
            Syl[r][r + i] = cf
    for r in range(n):
        for i, cf in enumerate(fp):
            Syl[n - 1 + r][r + i] = cf
    det, sgn = 1, 1
    for col in range(m):
        piv = next((r for r in range(col, m) if Syl[r][col]), None)
        if piv is None:
            return 0
        if piv != col:
            Syl[col], Syl[piv] = Syl[piv], Syl[col]
            sgn = -sgn
        inv = pow(Syl[col][col], p - 2, p)
        for r in range(col + 1, m):
            if Syl[r][col]:
                fac = Syl[r][col] * inv % p
                for cc in range(col, m):
                    Syl[r][cc] = (Syl[r][cc] - fac * Syl[col][cc]) % p
        det = det * Syl[col][col] % p
    return sgn * det % p

for k, v in out.items():
    cp = [1] + CPS[k]
    for p in (11, 13, 17, 19, 23):
        if v["disc"] and int(v["disc"]) % p != 0:
            assert sylv_disc(cp, p) == int(v["disc"]) % p, (k, p)
    print(f"k={k}: disc == Sylvester discriminant mod small primes ✓")
