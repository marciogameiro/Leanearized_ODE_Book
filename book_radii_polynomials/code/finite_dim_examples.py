"""Computer-assisted proofs of Chapter 2 (radii polynomials in finite dimensions).

Run:  python3 finite_dim_examples.py

Re-checks, in exact rational arithmetic, the two examples of Chapter 2 that use
Theorem th:radiiFiniteDim with the sup norm |x| = max_i |x_i| on R^n and the induced
operator norm |M| = max_i sum_j |M_ij| (row sums):

    Y0 >= |A f(xbar)|,   Z0 >= |I - A Df(xbar)|,   Z2 r >= |A [Df(c) - Df(xbar)]| for |c - xbar| <= r,
    p(r) = Z2 r^2 - (1 - Z0) r + Y0.

If p(a) < 0 and p(b) < 0 with 0 < a <= b, Lemma lem:existenceinterval gives a unique,
nondegenerate zero of f in the closed ball of radius b about xbar, and it lies in the open
ball of radius a.

* Example ex:2d_example: f(x) = (4 x1^2 + x2 - lam, x1 + x2^2 - 1), lam = 3, four
  approximate zeros xbar^(j) (the decimals printed in the chapter), A = Df(xbar)^{-1}
  computed exactly, so Z0 = 0.
* Example ex:equilibria_Lorenz: the equilibrium (sqrt 72, sqrt 72, 27) of the Lorenz
  system with sigma = 10, rho = 28, beta = 8/3, approximated by xbar = (8.4853, 8.4853, 27),
  with the 15-digit numerical inverse A printed in the chapter.

All input data are the decimal numbers printed in the chapter, read as exact rationals.
The bounds are computed twice: from the closed formulas derived in the examples, and from a
generic formula for quadratic f (see z2_quadratic); the two must agree. The script asserts
every numerical claim made in the text and writes the certificates

    certificates/ch2_parabolas.json, certificates/ch2_lorenz_equilibrium.json

with the data only (approximate zeros, approximate inverses, radii; numbers as exact decimals,
see certificate.py). The bounds are not stored: every checker recomputes them from the data.
"""
import os
from fractions import Fraction as Fr

import certificate

HERE = os.path.dirname(os.path.abspath(__file__))
CERT_DIR = os.path.join(HERE, "certificates")


# ----------------------------------------------------------------------------------------
# Exact linear algebra with the sup norm
# ----------------------------------------------------------------------------------------

def norm_inf(v):
    """|v|_inf = max_i |v_i|."""
    return max(abs(x) for x in v)


def opnorm_inf(M):
    """Induced operator norm of the sup norm: maximal absolute row sum."""
    return max(sum(abs(x) for x in row) for row in M)


def matvec(M, v):
    return [sum(m * x for m, x in zip(row, v)) for row in M]


def matmul(P, Q):
    return [[sum(P[i][k] * Q[k][j] for k in range(len(Q))) for j in range(len(Q[0]))]
            for i in range(len(P))]


def identity_minus(M):
    return [[(1 if i == j else 0) - M[i][j] for j in range(len(M))] for i in range(len(M))]


def z2_quadratic(A, H):
    """Z2 for a quadratic f, computed generically.

    For quadratic f, Df(c) - Df(xbar) = sum_k b_k H_k with b = c - xbar and H_k the
    (constant) matrix d/dx_k Df. Hence, if |b|_inf <= r,
        |(A [Df(c) - Df(xbar)])_ij| <= sum_k |(A H_k)_ij| r,
    and taking row sums gives Z2 = max_i sum_j sum_k |(A H_k)_ij|.
    """
    AH = [matmul(A, Hk) for Hk in H]
    return max(sum(abs(AHk[i][j]) for AHk in AH for j in range(len(A))) for i in range(len(A)))


def radii_poly(Y0, Z0, Z2):
    """p(r) = Z2 r^2 - (1 - Z0) r + Y0 (Z2 constant)."""
    return lambda r: Z2 * r * r - (1 - Z0) * r + Y0


def float_roots(Y0, Z0, Z2):
    """Approximate zeros of p (floats, for information only)."""
    a, b, c = float(Z2), -float(1 - Z0), float(Y0)
    qq = -0.5 * (b - (b * b - 4 * a * c) ** 0.5)       # numerically stable quadratic formula
    return c / qq, qq / a


def dec(s):
    """A printed decimal number, as an exact rational."""
    return Fr(s)


# ----------------------------------------------------------------------------------------
# Example ex:2d_example: intersection of two parabolas
# ----------------------------------------------------------------------------------------

def parabolas():
    lam = Fr(3)
    f = lambda x: [4 * x[0] ** 2 + x[1] - lam, x[0] + x[1] ** 2 - 1]
    Df = lambda x: [[8 * x[0], Fr(1)], [Fr(1), 2 * x[1]]]
    H = [[[Fr(8), Fr(0)], [Fr(0), Fr(0)]],          # d/dx1 Df
         [[Fr(0), Fr(0)], [Fr(0), Fr(2)]]]          # d/dx2 Df

    # Printed data: approximate zeros xbar^(j) and intervals I^(j) = [a_j, b_j]
    xbars = [("-0.6545436118927946", "1.286290640521338"),
             ("0.7986333753610425", "0.4487389270377125"),
             ("0.9086121587039679", "-0.3023042197787387"),
             ("-1.052701922172216", "-1.432725347780312")]
    intervals = [("3e-16", "0.640"), ("6e-16", "0.227"), ("1.7e-16", "0.239"), ("2.2e-16", "0.927")]
    residual_bound = dec("1.3e-15")

    print(f"== Example ex:2d_example (parabolas), lambda = {lam}, sup norm")
    sols = []
    for j, ((s1, s2), (sa, sb)) in enumerate(zip(xbars, intervals), start=1):
        x = [dec(s1), dec(s2)]
        a, b = dec(sa), dec(sb)
        fx = f(x)
        assert norm_inf(fx) <= residual_bound

        # A = Df(xbar)^{-1}, exactly (closed formula of the example)
        det = 16 * x[0] * x[1] - 1
        assert det != 0
        A = [[2 * x[1] / det, Fr(-1) / det], [Fr(-1) / det, 8 * x[0] / det]]

        # Y0 = |A f(xbar)|, Z0 = |I - A Df(xbar)| = 0
        Y0 = norm_inf(matvec(A, fx))
        Z0 = opnorm_inf(identity_minus(matmul(A, Df(x))))
        assert Z0 == 0

        # Z2 as derived in the example, and cross-check with the generic formula
        Z2 = max((16 * abs(x[1]) + 2) / abs(det), (8 + 16 * abs(x[0])) / abs(det))
        assert Z2 == z2_quadratic(A, H)

        p = radii_poly(Y0, Z0, Z2)
        assert p(a) < 0 and p(b) < 0                    # I^(j) is in the existence interval
        lo, hi = float_roots(Y0, Z0, Z2)
        print(f"   xbar^({j}): |f(xbar)| = {float(norm_inf(fx)):.2e}, Y0 = {float(Y0):.4e}, "
              f"Z0 = 0, Z2 = {float(Z2):.6f}")
        print(f"            p < 0 at both ends of I^({j}) = [{sa}, {sb}]  "
              f"(zeros of p approx {lo:.5e}, {hi:.7f})")
        sols.append({"xbar": x, "r0": a, "r1": b})

    certificate.write(os.path.join(CERT_DIR, "ch2_parabolas.json"), {
        "example": "Chapter 2, Example ex:2d_example (intersection of two parabolas)",
        "theorem": "th:radiiFiniteDim with Lemma lem:existenceinterval",
        "problem": "f(x) = (4 x1^2 + x2 - lambda, x1 + x2^2 - 1)",
        "parameters": {"lambda": lam},
        "norm": "sup norm on R^2, induced operator norm (maximal absolute row sum)",
        "A": "not stored: A = Df(xbar)^{-1}, computed exactly from xbar",
        "radii_polynomial": "p(r) = Z2 r^2 - (1 - Z0) r + Y0, r_* = infinity; p(r0) < 0 and p(r1) < 0",
        "solutions": sols,
    })


# ----------------------------------------------------------------------------------------
# Example ex:equilibria_Lorenz: an equilibrium of the Lorenz system
# ----------------------------------------------------------------------------------------

def lorenz_equilibrium():
    sigma, rho, beta = Fr(10), Fr(28), Fr(8, 3)
    f = lambda x: [sigma * (x[1] - x[0]), rho * x[0] - x[1] - x[0] * x[2], -beta * x[2] + x[0] * x[1]]
    Df = lambda x: [[-sigma, sigma, Fr(0)], [rho - x[2], Fr(-1), -x[0]], [x[1], x[0], -beta]]
    O = [Fr(0)] * 3
    H = [[O, [Fr(0), Fr(0), Fr(-1)], [Fr(0), Fr(1), Fr(0)]],     # d/dx1 Df
         [O, O, [Fr(1), Fr(0), Fr(0)]],                         # d/dx2 Df
         [O, [Fr(-1), Fr(0), Fr(0)], O]]                        # d/dx3 Df

    # Printed data
    x = [dec("8.4853"), dec("8.4853"), Fr(27)]
    A = [[dec("-0.051851843722001"), dec("-0.018518437220007"), dec("0.058925435753597")],
         [dec("0.048148156277999"), dec("-0.018518437220007"), dec("0.058925435753597")],
         [dec("-0.011785087150719"), dec("-0.117850871507195"), Fr(0)]]
    Y0p, Z0p, Z2p = dec("1.86258e-5"), dec("1.2e-14"), dec("0.23570174301439")
    r0, r1 = dec("1.8626e-5"), dec("4.2426")

    fx = f(x)
    Y0 = norm_inf(matvec(A, fx))
    Z0 = opnorm_inf(identity_minus(matmul(A, Df(x))))
    # Z2 as derived in the example, and cross-check with the generic formula
    rows = [2 * (abs(A[i][1]) + abs(A[i][2])) for i in range(3)]
    Z2 = max(rows)
    assert Z2 == z2_quadratic(A, H)
    assert Z2 == Z2p and rows.index(Z2) == 2                   # exact, attained at i = 3
    assert dec("1.86257409e-5") <= Y0 < dec("1.86257410e-5")   # "1.86257409... x 10^-5"
    assert dec("1.17335e-14") <= Z0 < dec("1.17336e-14")       # "1.17335... x 10^-14"
    assert Y0 <= Y0p and Z0 <= Z0p and Z2 <= Z2p               # printed values are upper bounds

    p = radii_poly(Y0p, Z0p, Z2p)                              # built from the PRINTED values
    assert p(r0) < 0 and p(r1) < 0
    lo, hi = float_roots(Y0p, Z0p, Z2p)
    print(f"== Example ex:equilibria_Lorenz, sigma = {sigma}, rho = {rho}, beta = {beta}, sup norm")
    print(f"   |A f(xbar)| = {float(Y0):.9e} <= Y0 = 1.86258e-5")
    print(f"   |I - A Df(xbar)| = {float(Z0):.6e} <= Z0 = 1.2e-14")
    print("   Z2 = max_i 2(|a_i2| + |a_i3|) = 0.23570174301439 (exact, attained at i = 3)")
    print(f"   with these printed values: p(r0) < 0 for r0 = 1.8626e-5, p(r1) < 0 for r1 = 4.2426"
          f"  (zeros of p approx {lo:.6e}, {hi:.6f})")

    certificate.write(os.path.join(CERT_DIR, "ch2_lorenz_equilibrium.json"), {
        "example": "Chapter 2, Example ex:equilibria_Lorenz (equilibrium of the Lorenz system)",
        "theorem": "th:radiiFiniteDim with Lemma lem:existenceinterval",
        "problem": "f(x) = (sigma (x2 - x1), rho x1 - x2 - x1 x3, -beta x3 + x1 x2)",
        "parameters": {"sigma": sigma, "rho": rho, "beta": beta},
        "norm": "sup norm on R^3, induced operator norm (maximal absolute row sum)",
        "radii_polynomial": "p(r) = Z2 r^2 - (1 - Z0) r + Y0, r_* = infinity; p(r0) < 0 and p(r1) < 0",
        "xbar": x, "A": A,
        "r0": r0, "r1": r1,
    })


if __name__ == "__main__":
    os.makedirs(CERT_DIR, exist_ok=True)
    parabolas()
    lorenz_equilibrium()
