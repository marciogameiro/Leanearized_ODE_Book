"""Computer-assisted proofs of Chapters 14 and 15 (Chebyshev series).

Run:  python3 examples.py
Prints the bounds Y0, Z0, Z1, Z2 (rigorous decimal upper bounds, rounded up to three
significant digits), radii r0 < r1 such that p(r0) < 0 and p(r1) < 0 for the radii
polynomial built from these PRINTED values (checked in exact rational arithmetic),
rigorous enclosures of solution values, and plot data used in the chapters.

It also writes, for each example, a certificate (see certificate.py) with the DATA of the
proof only: the problem data, the truncation data N and nu, the approximate solution abar
(Newton's floats rounded to 17 significant digits), the approximate inverse A^{(N)} (rounded
to 17 significant digits, full double precision), the radii r0, r1 and the claimed enclosures. Every number is a
JSON number denoting exactly the decimal written (beta = 8/3 is stored as the string "8/3").
The data are rounded BEFORE the bounds are computed, so the bounds printed here are exactly
those of the stored data; the bounds are not stored, every checker recomputes them:

    certificates/ch14_scalar.json, certificates/ch14_lorenz.json,
    certificates/ch15_chafee_infante.json
"""
import math
import os
from fractions import Fraction as Fr

import certificate

from chebyshev_rp import (ChebProblem, newton, approximate_inverse, bounds, radii_poly,
                          neg_interval, peval, round_up, up, enclosure, cheb_eval, cheb_interp)


CERT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "certificates")


def report(name, prob, abar, N, nu, printed, radii):
    """Print the bounds and radii for the data abar (exact decimals) and the rounded
    approximate inverse A; return the data of the proof (for the certificate).

    printed = (Y0, Z0, Z1, [Z2 coefficients]) and radii = (r0, r1) are the values printed in
    the book; it is checked that the bounds rounded up to three digits are these values and,
    exactly, that the radii polynomial built from them is negative at r0 and r1."""
    A = approximate_inverse(prob, abar, N)
    Y0, Z0, Z1, Z2, Z2_exact = bounds(prob, abar, A, N, nu)
    # the printed (rounded up) bounds; the radii polynomial is built from these
    Y0p, Z0p, Z1p = (round_up(x)[0] for x in (Y0, Z0, Z1))
    Z2p = [round_up(c)[0] for c in Z2]
    p = radii_poly(Y0p, Z0p, Z1p, Z2p)
    assert (up(Y0), up(Z0), up(Z1), [up(c) for c in Z2]) == printed, "printed bounds changed"
    r0, r1 = (Fr(r) for r in radii)
    assert peval(p, r0) < 0 and peval(p, r1) < 0          # exact check with printed values
    best0, best1 = neg_interval(p)                         # for information only
    print(f"== {name}: N = {N}, nu = {nu}, L = {prob.L}")
    print(f"   Y0 <= {up(Y0)}, Z0 <= {up(Z0)}, Z1 <= {up(Z1)}, "
          f"Z2(r) <= {' + '.join(f'{up(c)} r^{d}' for d, c in enumerate(Z2))}"
          f"  ({'equals max_j Z2_j' if Z2_exact else 'upper bound for max_j Z2_j'})")
    print(f"   with these printed values: p(r0) < 0 for r0 = {up(r0)} ({r0}), "
          f"p(r1) < 0 for r1 = {up(r1)} ({r1})  [best 3-digit radii: {up(best0)}, {up(best1)}]")
    return {"r0": r0, "r1": r1, "A": A}


def write_certificate(filename, example, prob, abar, N, nu, proof, **extra):
    """Write the certificate of one example (data only; every number an exact decimal)."""
    cert = {
        "example": example,
        "theorem": "thm:cheb_IVP_bounds (IVP) / thm:cheb_BVP_bounds (BVP)",
        "problem": "u' = L f(u) on [-1, 1], q - B_minus u(-1) - B_plus u(1) = 0; "
                   "u_j = (a_j)_0 + 2 sum_{k>=1} (a_j)_k T_k",
        "f": [[{"exponent": list(e), "coefficient": Fr(c)} for e, c in fj.items()] for fj in prob.f],
        "L": Fr(prob.L), "B_minus": prob.Bm, "B_plus": prob.Bp, "q": prob.q,
        "N": N, "nu": Fr(nu),
        "weights": "X: w_0 = 1, w_k = 2 nu^k; Y: v_0 = 1, v_k = nu^k / k; max over components",
        "unknown_ordering": "index (j, k) -> j (N + 1) + k, j = 0..n-1, k = 0..N",
        "abar": abar,
        "A": proof["A"],
        "radii_polynomial": "p(r) = Z2(r) r^2 - (1 - Z0 - Z1) r + Y0 with the bounds of the theorem, "
                            "computed by the checker from the data abar and A; p(r0) < 0 and p(r1) < 0",
        "r0": proof["r0"], "r1": proof["r1"],
    }
    cert.update(extra)
    os.makedirs(CERT_DIR, exist_ok=True)
    certificate.write(os.path.join(CERT_DIR, filename), cert)


def decimal_seqs(abar):
    """Newton's float approximation abar rounded to exact decimals (17 significant digits):
    these decimals are the data of the proof."""
    return [certificate.decimal_seq(seq, certificate.ABAR_DIGITS) for seq in abar]


def samples(abar, ts):
    return [[cheb_eval(a, t) for a in abar] for t in ts]


def scalar_ivp():
    """u' = L (u^2 - u), u(-1) = 1/2, L = 1 (time interval [0, 2])."""
    f = [{(2,): 1, (1,): -1}]
    N, nu = 20, Fr(11, 10)
    prob = ChebProblem(f, 1, [[1]], [[0]], [Fr(1, 2)])
    abar = decimal_seqs(newton(prob, [[0.5] + [0.0] * N], N))
    proof = report("scalar IVP", prob, abar, N, nu, ("9.79e-17", "8.60e-16", "2.14e-1", ["6.40e0"]),
                   ("1.25e-16", "0.122"))
    write_certificate("ch14_scalar.json", "Chapter 14, Example ex:cheb_scalar_IVP", prob, abar, N, nu, proof,
                      ode="x' = x (x - 1), x(0) = 1/2, tau in [0, 2]; x(tau) = u(tau - 1)")
    print(f"   abar_0..3 = {[f'{float(x):.6f}' for x in abar[0][:4]]}")
    # floating point sanity check only (not part of the proof)
    exact = lambda t: 1 / (1 + math.exp(t + 1))
    abar_f = [float(x) for x in abar[0]]
    err = max(abs(cheb_eval(abar_f, t) - exact(t)) for t in [k / 100 - 1 for k in range(201)])
    print(f"   (float sanity check: max |ubar - 1/(1+e^(t+1))| on a grid = {err:.1e})")


def lorenz_ivp():
    """Lorenz, sigma = 10, rho = 28, beta = 8/3, x0 = (-8, 8, 27), L = 1/8."""
    b = Fr(8, 3)
    f = [{(0, 1, 0): 10, (1, 0, 0): -10},
         {(1, 0, 0): 28, (1, 0, 1): -1, (0, 1, 0): -1},
         {(1, 1, 0): 1, (0, 0, 1): -b}]
    I3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    O3 = [[0] * 3 for _ in range(3)]
    x0 = [Fr(-8), Fr(8), Fr(27)]
    N, nu, L = 30, Fr(3, 2), Fr(1, 8)
    abar = [[float(x)] + [0.0] * N for x in x0]
    for k in range(1, 9):                       # continuation in L for the initial guess
        abar = newton(ChebProblem(f, L * k / 8, I3, O3, x0), abar, N)
    prob = ChebProblem(f, L, I3, O3, x0)
    abar = decimal_seqs(abar)
    proof = report("Lorenz IVP", prob, abar, N, nu, ("8.79e-12", "6.80e-15", "1.94e-1", ["2.33e0"]),
                   ("1.10e-11", "0.345"))
    r0 = proof["r0"]
    # x(1/4) = u(1): exact value of ubar(1), then |x_j(1/4) - ubar_j(1)| <= r0
    centers = [enclosure(cheb_eval(a, Fr(1)), r0) for a in abar]
    write_certificate("ch14_lorenz.json", "Chapter 14, Example ex:cheb_Lorenz_IVP", prob, abar, N, nu, proof,
                      ode="Lorenz, sigma = 10, rho = 28, beta = 8/3, x(0) = (-8, 8, 27), tau in [0, 1/4]; "
                          "x(tau) = u(8 tau - 1)",
                      enclosure_x_at_quarter={"centers": [Fr(c) for c in centers],
                                              "radius": Fr(1, 10 ** 10)})
    print(f"   x(1/4) in ({', '.join(centers)}) + [-1e-10, 1e-10]^3")
    print(f"   |abar_N| = {[f'{float(abs(a[N])):.1e}' for a in abar]}")
    abar_f = [[float(x) for x in a] for a in abar]
    print("   plot data (tau = (t+1)/8, x, y, z):")
    for t in [k / 20 - 1 for k in range(41)]:
        v = [cheb_eval(a, t) for a in abar_f]
        print(f"   ({(t + 1) / 8:.5f},{v[0]:.4f}) ({(t + 1) / 8:.5f},{v[1]:.4f}) ({(t + 1) / 8:.5f},{v[2]:.4f})")


def chafee_infante_bvp():
    """u'' + lam u (1 - u^2) = 0, u(-1) = u(1) = 0, lam = 4, as u1' = u2, u2' = -lam u1 + lam u1^3."""
    lam = Fr(4)
    f = [{(0, 1): 1}, {(1, 0): -lam, (3, 0): lam}]
    Bm, Bp, q = [[1, 0], [0, 0]], [[0, 0], [1, 0]], [0, 0]
    N, nu = 40, Fr(6, 5)
    prob = ChebProblem(f, 1, Bm, Bp, q)
    g1 = cheb_interp(lambda t: 0.8 * math.cos(math.pi * t / 2), N)
    g2 = cheb_interp(lambda t: -0.4 * math.pi * math.sin(math.pi * t / 2), N)
    abar = decimal_seqs(newton(prob, [g1, g2], N))
    proof = report("Chafee-Infante BVP", prob, abar, N, nu,
                   ("5.39e-16", "1.58e-15", "2.17e-1", ["7.23e1", "8.19e1"]), ("7.00e-16", "0.0107"))
    r0 = proof["r0"]
    # u(0) = u_1(0) and u'(-1) = u_2(-1), each within r0 of the exact values of ubar
    a1, a2 = abar
    u0, du = enclosure(cheb_eval(a1, Fr(0)), r0), enclosure(cheb_eval(a2, Fr(-1)), r0)
    print(f"   u(0) in {u0} + [-1e-10, 1e-10], u'(-1) in {du} + [-1e-10, 1e-10]")
    write_certificate("ch15_chafee_infante.json", "Chapter 15, Example ex:cheb_BVP_Chafee_Infante",
                      prob, abar, N, nu, proof,
                      ode="u'' + lam u (1 - u^2) = 0, u(-1) = u(1) = 0, lam = 4; u_1 = u, u_2 = u'",
                      parameters={"lambda": lam},
                      enclosures={"u(0)": {"center": Fr(u0), "radius": Fr(1, 10 ** 10)},
                                  "u'(-1)": {"center": Fr(du), "radius": Fr(1, 10 ** 10)}})
    print(f"   abar_1 even coefficients 0..6 = {[f'{float(abar[0][k]):.8f}' for k in range(0, 7, 2)]}")
    print("   plot data (x, u):")
    print("   " + " ".join(f"({t:.3f},{cheb_eval([float(x) for x in abar[0]], t):.4f})" for t in [k / 20 - 1 for k in range(41)]))


if __name__ == "__main__":
    scalar_ivp()
    lorenz_ivp()
    chafee_infante_bvp()
