"""Radii polynomial approach for IVPs via Taylor series (Chapter 8).

Run:  python3 taylor_ivp.py          (from the code folder)

The rescaled IVP is  x' = tau f(x),  x(0) = x0,  with f a polynomial vector field on R^n.
Unknowns are Taylor coefficients x_j(t) = sum_k a_{j,k} t^k and the zero finding problem is

    F_{j,0}(a) = a_{j,0} - x0_j,
    F_{j,k}(a) = k a_{j,k} - tau phi_j(a)_{k-1},   k >= 1,

where phi_j(a) is f_j with products replaced by the Cauchy product (a*b)_k = sum_i a_{k-i} b_i.
Spaces: X = (l^1_nu)^n with weights nu^k, Y = (l^1_omega)^n with omega_k = nu^{k+1}/(k+1),
both with the max norm over components.

This script proves two results of Chapter 8 by evaluating EXACTLY the bounds of
  * Theorem thm:NewtonFx(1-x) (scalar IVP x' = tau x(x-1), Section 8.1), and
  * Theorem thm:TaylorIVPsystem (systems, Section 8.2), applied to the Lorenz system
    (Section 8.3),
in exact rational arithmetic (fractions.Fraction).

Scalar example: x0 = 1/2, tau = 1, N = 27, nu = 1. The truncated problem is lower
triangular; its exact rational solution (given by a recursion) is rounded to 17 significant
decimal digits (certificate.ABAR_DIGITS), and this decimal sequence is abar. A^{(N)} is the
exact inverse of DF^{(N)}(abar) (a formula in abar, so it is not stored in the certificate);
hence Z0 = 0, and F^{(N)}(abar) is tiny but nonzero.

Lorenz example: sigma = 10, rho = 28, beta = 8/3, x0 = (-8, 8, 27), tau = 1/16, N = 40,
nu = 1. Again abar is the exact rational solution of the (lower triangular) truncated
problem rounded to 17 significant digits. The approximate inverse A^{(N)} is a floating
point inverse of DF^{(N)}(abar), rounded to certificate.A_DIGITS = 17 significant decimal
digits (full double precision); Z0 is then computed exactly. The theorems hold for ANY
abar and A^{(N)}, so these choices only affect the size of the bounds, not the validity of
the proofs.

The data are rounded BEFORE the bounds are computed, so the bounds below are exactly the
bounds of the stored data. The bounds are printed rounded UP, and the radii r0 < r1 are
chosen (and checked exactly) so that the radii polynomial built from the PRINTED values is
negative at both. Since p(r) is nondecreasing in Y0, Z0, Z1, Z2 for r > 0, this implies the
same for the exact bounds.

Certificates certificates/ch8_scalar.json and certificates/ch8_lorenz.json store the DATA
only (parameters, N, nu, abar, the numerical A^{(N)} for Lorenz, and the claimed radii and
enclosure), every number as an exact decimal (see certificate.py); the bounds Y0, Z0, Z1, Z2
are not stored, they are recomputed from the data by every checker.
"""
import math
import os
import time
from decimal import Decimal
from fractions import Fraction as Fr

import certificate
from chebyshev_rp import inverse, peval, round_up, up, enclosure, poly_diff

HERE = os.path.dirname(os.path.abspath(__file__))


# ----------------------------------------------------------------------------------------
# Taylor sequences (finite lists, index k >= 0)
# ----------------------------------------------------------------------------------------

def cauchy(a, b):
    """Cauchy product (a*b)_k = sum_{i=0}^k a_{k-i} b_i, full support (length len(a)+len(b)-1)."""
    out = [a[0] * 0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for l, y in enumerate(b):
                out[i + l] += x * y
    return out


def seq_add(a, b):
    n = max(len(a), len(b))
    z = (a + b)[0] * 0
    return [(a[k] if k < len(a) else z) + (b[k] if k < len(b) else z) for k in range(n)]


def poly_eval(poly, a, one):
    """phi(a): the polynomial {exponent tuple: coefficient} with the Cauchy product.
    a is a list of n component sequences; `one` is 1 in the number type used."""
    out = [one * 0]
    for expo, coef in poly.items():
        m = [one]                                    # e_0
        for i, e in enumerate(expo):
            for _ in range(e):
                m = cauchy(m, a[i])
        out = seq_add(out, [coef * x for x in m])
    return out


def norm_nu(a, nu):
    """||a||_{1,nu} = sum_k |a_k| nu^k."""
    return sum(abs(x) * nu ** k for k, x in enumerate(a))


def matrix_norm_nu(C, nu, rows, cols):
    """Weighted matrix norm (eq:weightedmatrixnorm) of the block C[rows][cols]:
    max over columns k' of nu^{-k'} sum_k |C_{k,k'}| nu^k (indices relative to the block)."""
    return max(sum(abs(C[r][c]) * nu ** k for k, r in enumerate(rows)) / nu ** kp
               for kp, c in enumerate(cols))


def taylor_eval(a, t):
    """Horner evaluation of sum_k a_k t^k (exact for Fractions)."""
    s = a[-1] * 0
    for x in reversed(a):
        s = s * t + x
    return s


def taylor_recursion(f, x0, tau, N, one):
    """The unique solution of the lower triangular problem F^{(N)}(a) = 0:
    a_{j,0} = x0_j,  a_{j,k} = tau phi_j(a)_{k-1} / k  (phi_j(a)_{k-1} uses a_{.,0..k-1})."""
    n = len(f)
    a = [[one * x0[j]] for j in range(n)]
    for k in range(1, N + 1):
        phi = [poly_eval(f[j], a, one) for j in range(n)]
        for j in range(n):
            a[j].append(tau * phi[j][k - 1] / k)
    return a


# ----------------------------------------------------------------------------------------
# The truncated problem: F^{(N)}, DF^{(N)} (index (j, k) -> j (N+1) + k)
# ----------------------------------------------------------------------------------------

def residual(f, x0, tau, a, N, one):
    """F^{(N)}(a) as a list of n sequences of length N+1, eq. (F(a)=0_1st_order_system_IVP)."""
    n = len(f)
    phi = [poly_eval(f[j], a, one) for j in range(n)]
    return [[a[j][0] - x0[j]] + [k * a[j][k] - tau * phi[j][k - 1] for k in range(1, N + 1)]
            for j in range(n)]


def derivative_seqs(f, a, one):
    """D_{j'} phi_j(a) for all j, j' (eq:Djphii), as sequences."""
    n = len(f)
    return [[poly_eval(poly_diff(f[j], jp), a, one) for jp in range(n)] for j in range(n)]


def jacobian(f, tau, a, N, one):
    """DF^{(N)}(a), from eq. (formulaforDF)."""
    n, D = len(f), N + 1
    Dphi = derivative_seqs(f, a, one)
    J = [[one * 0] * (n * D) for _ in range(n * D)]
    for j in range(n):
        J[j * D][j * D] = one                                   # k = 0: initial condition
        for k in range(1, D):
            J[j * D + k][j * D + k] = one * k                   # k = m >= 1
            for jp in range(n):
                s = Dphi[j][jp]
                for m in range(k):                              # m <= k-1
                    if k - 1 - m < len(s):
                        J[j * D + k][jp * D + m] = -tau * s[k - 1 - m]
    return J


def matmul(A, B):
    """Exact (or float) matrix product, skipping zero entries."""
    n, m = len(A), len(B[0])
    Bnz = [[(c, x) for c, x in enumerate(row) if x] for row in B]
    out = []
    for row in A:
        r = [row[0] * 0] * m
        for i, x in enumerate(row):
            if x:
                for c, y in Bnz[i]:
                    r[c] += x * y
        out.append(r)
    return out


def exact_lower_inverse(J):
    """Exact inverse of a lower triangular matrix with nonzero diagonal (forward substitution)."""
    n = len(J)
    inv = [[Fr(0)] * n for _ in range(n)]
    for c in range(n):
        inv[c][c] = 1 / J[c][c]
        for r in range(c + 1, n):
            s = sum(J[r][i] * inv[i][c] for i in range(c, r) if J[r][i])
            inv[r][c] = -s / J[r][r]
    return inv


# ----------------------------------------------------------------------------------------
# Theorem thm:NewtonFx(1-x): x' = tau x(x-1), x(0) = x0
# ----------------------------------------------------------------------------------------

def scalar_bounds(x0, tau, N, nu, abar, A):
    """Y0, Z0, Z1, Z2 of Theorem thm:NewtonFx(1-x), evaluated exactly.
    abar: list of N+1 rationals; A: (N+1)x(N+1) rational matrix A^{(N)}."""
    D = N + 1
    one = Fr(1)
    f = [{(2,): 1, (1,): -1}]                    # f(x) = x^2 - x; F_n = n a_n + tau (a - a*a)_{n-1}
    FN = residual(f, [x0], tau, [abar], N, one)[0]
    DFN = jacobian(f, tau, [abar], N, one)
    AF = [sum(A[i][l] * FN[l] for l in range(D)) for i in range(D)]
    aa = cauchy(abar, abar)
    tail = [(abar[n] if n <= N else 0) - aa[n] for n in range(2 * N + 1)]   # (abar - abar*abar)_n
    Y0 = (sum(abs(AF[n]) * nu ** n for n in range(D))
          + tau * nu * sum(abs(tail[n]) * nu ** n / (n + 1) for n in range(N, 2 * N + 1)))
    ADF = matmul(A, DFN)
    B = [[(1 if i == l else 0) - ADF[i][l] for l in range(D)] for i in range(D)]
    Z0 = matrix_norm_nu(B, nu, range(D), range(D))
    g = [(1 if n == 0 else 0) - 2 * abar[n] for n in range(D)]
    Z1 = tau * nu / (N + 1) * norm_nu(g, nu)
    normA = matrix_norm_nu(A, nu, range(D), range(D))
    Z2 = 2 * tau * nu * max(normA, Fr(1, N + 1))
    return Y0, Z0, Z1, Z2, normA


# ----------------------------------------------------------------------------------------
# Theorem thm:TaylorIVPsystem
# ----------------------------------------------------------------------------------------

def system_bounds(f, x0, tau, N, nu, abar, A, r_star):
    """Y0, Z0, Z1, Z2 of Theorem thm:TaylorIVPsystem, evaluated exactly.
    f: list of n polynomials {exponent tuple: coefficient}; abar: n exact sequences of
    length N+1; A: exact n(N+1) x n(N+1) matrix A^{(N)}; r_star > 0."""
    n, D = len(f), N + 1
    one = Fr(1)
    M = max(sum(e) for poly in f for e in poly)
    blk = lambda j: range(j * D, (j + 1) * D)
    # Y0 (eq:systemNewtonY0)
    FN = residual(f, x0, tau, abar, N, one)
    FNvec = [x for Fj in FN for x in Fj]
    AF = [sum(A[i][l] * FNvec[l] for l in range(n * D) if FNvec[l]) for i in range(n * D)]
    phi = [poly_eval(f[j], abar, one) for j in range(n)]
    Y0j = []
    for j in range(n):
        fin = sum(abs(AF[j * D + k]) * nu ** k for k in range(D))
        tl = tau * nu * sum(abs(phi[j][k]) * nu ** k / (k + 1)
                            for k in range(N, min(M * N, len(phi[j]) - 1) + 1))
        Y0j.append(fin + tl)
    Y0 = max(Y0j)
    # Z0 (eq:systemNewtonZ0): blocks of B = I - A^{(N)} DF^{(N)}(abar)
    DFN = jacobian(f, tau, abar, N, one)
    ADF = matmul(A, DFN)
    B = [[(1 if i == l else 0) - ADF[i][l] for l in range(n * D)] for i in range(n * D)]
    Z0 = max(sum(matrix_norm_nu(B, nu, blk(j), blk(jp)) for jp in range(n)) for j in range(n))
    # Z1 (eq:systemNewtonZ1)
    Dphi = derivative_seqs(f, abar, one)
    Z1 = tau * nu / (N + 1) * max(sum(norm_nu(Dphi[j][jp], nu) for jp in range(n))
                                  for j in range(n))
    # Z2 (eq:systemNewtonZ2), with K_{j,j'} from eq:defKjj and zeta_{j,m,j'}(r_star)
    K = [[max(matrix_norm_nu(A, nu, blk(j), blk(jp)), Fr(1 if j == jp else 0, N + 1))
          for jp in range(n)] for j in range(n)]
    abar_norm = [norm_nu(abar[l], nu) for l in range(n)]

    def zeta(j, m, jp):
        s = Fr(0)
        for alpha, c in f[j].items():
            if sum(alpha) < 2 or alpha[jp] < 1 or alpha[m] - (1 if jp == m else 0) < 1:
                continue
            term = abs(Fr(c)) * alpha[jp] * (alpha[m] - (1 if jp == m else 0))
            for l in range(n):
                term *= (abar_norm[l] + r_star) ** (alpha[l] - (l == jp) - (l == m))
            s += term
        return s

    Z2jj = [[sum(K[j][m] * sum(zeta(m, mp, jp) for mp in range(n)) for m in range(n))
             for jp in range(n)] for j in range(n)]
    Z2 = tau * nu * max(sum(Z2jj[j]) for j in range(n))
    return dict(Y0=Y0, Y0j=Y0j, Z0=Z0, Z1=Z1, Z2=Z2, K=K, FN=FN)


# ----------------------------------------------------------------------------------------
# Radii polynomial with constant Z2
# ----------------------------------------------------------------------------------------

def radii_poly(Y0, Z0, Z1, Z2):
    """p(r) = Z2 r^2 - (1 - Z0 - Z1) r + Y0 as a coefficient list."""
    return [Fr(Y0), -(1 - Fr(Z0) - Fr(Z1)), Fr(Z2)]


def short_decimal(x, digits, up_):
    """x rounded up (up_=True) or down to `digits` significant decimal digits, as a Fraction."""
    e = math.floor(math.log10(float(x))) - digits + 1
    s = Fr(10) ** e
    k = math.ceil(x / s) if up_ else math.floor(x / s)
    return k * s


def radii(p, digits=3):
    """Short decimals r0 < r1 with p(r0) < 0 and p(r1) < 0 (exactly verified), near the roots."""
    c, b, a = (float(x) for x in p)
    disc = math.sqrt(b * b - 4 * a * c)
    lo = 2 * c / (-b + disc)                    # smaller root, computed stably
    hi = (-b + disc) / (2 * a)
    r0 = short_decimal(lo * (1 + 1e-9), digits, True)
    r1 = short_decimal(hi * (1 - 1e-9), digits, False)
    assert peval(p, r0) < 0 and peval(p, r1) < 0 and r0 < r1
    return r0, r1


def sci(x, digits):
    """Decimal string of the short decimal x (digits significant digits)."""
    e = math.floor(math.log10(float(x)))
    m = x / Fr(10) ** e
    if m >= 10:
        m, e = m / 10, e + 1
    return f"{float(m):.{digits - 1}f}e{e}"


def latex_float(x):
    """The exact decimal x (at most 17 significant digits, as stored in the certificate),
    as LaTeX (m\\cdot 10^{e}), using scientific notation when the exponent is < -4 (as %g)."""
    x = Fr(x)
    s = "0"
    if x != 0:
        d = (Decimal(x.numerator) / Decimal(x.denominator)).normalize()
        s = f"{d:e}" if d.adjusted() < -4 else f"{d:f}"
        s = s.replace("e+0", "") if s.endswith("e+0") else s
    assert Fr(s) == x
    if "e" in s:
        m, e = s.split("e")
        s = f"{m}\\cdot 10^{{{int(e)}}}"
    return s


def print_data(seqs):
    """The coefficients as LaTeX blocks of lines '$k$: value' (the exact stored decimals)."""
    for j, a in enumerate(seqs):
        if len(seqs) > 1:
            print(f"\\medskip\\noindent\\textit{{Component $j={j + 1}$:}}\\par")
        print("{\\footnotesize\n\\begin{multicols}{3}\n\\noindent")
        print("\\\\\n".join(f"${k}$: ${latex_float(x)}$" for k, x in enumerate(a)))
        print("\\end{multicols}}\n")


def num_digits(x):
    return len(str(abs(x)))


# ----------------------------------------------------------------------------------------
# Example 1: x' = x(x-1), x0 = 1/2 (Section 8.1)
# ----------------------------------------------------------------------------------------

def scalar_proof(x0, tau=Fr(1), N=27, nu=Fr(1)):
    """abar (exact recursion rounded to 17 significant digits), A^{(N)} (exact inverse of
    DF^{(N)}(abar)) and the exact bounds of Theorem thm:NewtonFx(1-x) for x' = tau x(x-1),
    x(0) = x0."""
    f = [{(2,): 1, (1,): -1}]
    exact = taylor_recursion(f, [x0], tau, N, Fr(1))[0]
    abar = certificate.decimal_seq(exact, certificate.ABAR_DIGITS)   # the stored data
    A = exact_lower_inverse(jacobian(f, tau, [abar], N, Fr(1)))
    Y0, Z0, Z1, Z2, normA = scalar_bounds(x0, tau, N, nu, abar, A)
    assert Z0 == 0
    # float sanity check (not part of the proof): x(t) = 1/(1 + C e^{tau t}), C = (1-x0)/x0
    C = float((1 - x0) / x0)
    err = max(abs(float(taylor_eval(abar, Fr(k, 50))) - 1 / (1 + C * math.exp(float(tau) * k / 50)))
              for k in range(-50, 51))
    return dict(abar=abar, A=A, Y0=Y0, Z0=Z0, Z1=Z1, Z2=Z2, normA=normA, err=err)


def scalar_example():
    x0, tau, N, nu = Fr(1, 2), Fr(1), 27, Fr(1)
    t = time.time()
    s = scalar_proof(x0, tau, N, nu)
    abar, A, Y0, Z0, Z1, Z2 = (s[k] for k in ("abar", "A", "Y0", "Z0", "Z1", "Z2"))
    # the values printed in the chapter (rounded up) and r0 = 2.72e-15
    Y0p, Z1p, Z2p = Fr("2.6630e-15"), Fr("1.9511e-2"), Fr("2.5969")
    assert Y0 <= Y0p and Z1 <= Z1p and Z2 <= Z2p
    p = radii_poly(Y0p, 0, Z1p, Z2p)
    r0 = Fr("2.72e-15")
    _, r1 = radii(p)
    assert peval(p, r0) < 0 and peval(p, r1) < 0
    print("== Scalar IVP x' = tau x(x-1), x0 = 1/2, tau = 1, N = 27, nu = 1 "
          f"({time.time() - t:.1f}s)")
    print(f"   Y0 = {float(Y0):.6e} <= {sci(Y0p, 5)},  Z0 = 0,  Z1 = {float(Z1):.6e} <= "
          f"{sci(Z1p, 5)},  Z2 = {float(Z2):.6f} <= {sci(Z2p, 5)}")
    print(f"   ||A^(N)||_nu,N = {float(s['normA']):.6f}")
    print(f"   with the printed values: p(r0) < 0 for r0 = 2.72e-15, p(r1) < 0 for r1 = {sci(r1, 3)}")
    dA = max(x.denominator for row in A for x in row)
    nA = max(abs(x.numerator) for row in A for x in row)
    print(f"   A^(N) = DF^(N)(abar)^-1 exactly: largest denominator {num_digits(dA)} digits "
          f"(numerators up to {num_digits(nA)} digits)")
    print(f"   (float sanity check: max |xbar - 1/(1+e^t)| on a grid of [-1,1] = {s['err']:.1e})")
    print("   abar (17 significant digits, exactly as stored in the certificate):")
    print_data([abar])
    # The figure: the same proof for x0 = 1/4 and x0 = 3/4 (same tau, N, nu)
    curves = {}
    for y0 in (Fr(1, 4), Fr(1, 2), Fr(3, 4)):
        c = s if y0 == x0 else scalar_proof(y0, tau, N, nu)
        Yp, Z1q, Z2q = (round_up(c[k])[0] for k in ("Y0", "Z1", "Z2"))
        c0, c1 = radii(radii_poly(Yp, 0, Z1q, Z2q))
        if y0 != x0:   # the values printed in the chapter for x0 = 1/4 and 3/4
            assert (Yp, Z1q, Z2q, c0) == (Fr("9.31e-16"), Fr("3.54e-2"), Fr("3.40"),
                                          Fr("9.66e-16"))
        print(f"   figure curve x0 = {y0}: Y0 <= {up(c['Y0'])}, Z0 = 0, Z1 <= {up(c['Z1'])}, "
              f"Z2 <= {up(c['Z2'])}, r0 = {sci(c0, 3)}, r1 = {sci(c1, 3)}, "
              f"(float check {c['err']:.1e})")
        pts = " ".join(f"({k / 20:.2f},{float(taylor_eval(c['abar'], Fr(k, 20))):.4f})"
                       for k in range(-20, 21))
        print(f"   plot x0 = {y0}: {pts}")
        if y0 != x0:
            curves[str(y0)] = dict(x0=y0, abar=c["abar"], r0=c0, r1=c1)
    cert = dict(chapter=8, example="scalar IVP x' = tau x(x-1)",
                theorem="thm:NewtonFx(1-x)",
                parameters=dict(x0=x0, tau=tau), N=N, nu=nu,
                abar=abar, abar_note="exact rational solution of F^{(N)}(a) = 0, rounded to "
                "17 significant decimal digits",
                A_note="A^{(N)} = DF^{(N)}(abar)^{-1} exactly (lower triangular); not stored, "
                "recomputed from abar by the checker (so Z0 = 0)",
                r0=r0, r1=r1,
                figure_curves=curves,
                figure_curves_note="the same proof (same tau, N, nu, same choice of abar and "
                "A^{(N)}) for x0 = 1/4 and 3/4, plotted in fig:taylorEx1")
    certificate.write(os.path.join(HERE, "certificates", "ch8_scalar.json"), cert)


# ----------------------------------------------------------------------------------------
# Example 2: Lorenz system (Section 8.3)
# ----------------------------------------------------------------------------------------

LORENZ = dict(sigma=Fr(10), rho=Fr(28), beta=Fr(8, 3))


def lorenz_field(sigma, rho, beta):
    return [{(0, 1, 0): sigma, (1, 0, 0): -sigma},
            {(1, 0, 0): rho, (1, 0, 1): -1, (0, 1, 0): -1},
            {(1, 1, 0): 1, (0, 0, 1): -beta}]


def lorenz_example(tau=Fr(1, 16), N=40, nu=Fr(1), x0=(Fr(-8), Fr(8), Fr(27)), write=True, plot=True):
    """Since M = 2, the functions zeta_{j,m,j'} of the Z2 lemma are constants, so Z2 does not
    depend on r_*. We check this (by evaluating Z2 for two values of r_*) and then take
    r_* = r1, the largest radius we certify."""
    t = time.time()
    f = lorenz_field(**LORENZ)
    n, D = 3, N + 1
    exact = taylor_recursion(f, x0, tau, N, Fr(1))               # exact solution of F^{(N)} = 0
    abar = [certificate.decimal_seq(a, certificate.ABAR_DIGITS) for a in exact]   # stored data
    J = jacobian(f, tau, abar, N, Fr(1))
    Af = inverse([[float(x) for x in row] for row in J])          # float inverse
    A = certificate.decimal_matrix(Af, certificate.A_DIGITS)      # exact decimal A^{(N)}
    t1 = time.time()
    b = system_bounds(f, list(x0), tau, N, nu, abar, A, Fr(1))
    t2 = time.time()
    assert system_bounds(f, list(x0), tau, N, nu, abar, A, Fr(10 ** 6))["Z2"] == b["Z2"]
    Y0, Z0, Z1, Z2 = b["Y0"], b["Z0"], b["Z1"], b["Z2"]
    Y0p, Z0p, Z1p, Z2p = (round_up(x)[0] for x in (Y0, Z0, Z1, Z2))
    p = radii_poly(Y0p, Z0p, Z1p, Z2p)
    r0, r1 = radii(p)
    if write:          # the default example: the values printed in the chapter
        assert (Y0p, Z0p, Z1p, Z2p) == (Fr("3.62e-15"), Fr("2.16e-16"), Fr("6.05e-2"),
                                        Fr("0.384"))
        assert (r0, r1) == (Fr("3.86e-15"), Fr("2.44"))
    r_star = r1
    print(f"== Lorenz IVP, x0 = {tuple(str(x) for x in x0)}, tau = {tau}, N = {N}, nu = {nu}, "
          f"r_* = {r_star}  ({3 * D} unknowns; data {t1 - t:.1f}s, bounds {t2 - t1:.1f}s)")
    print(f"   Y0 <= {up(Y0)}, Z0 <= {up(Z0)}, Z1 <= {up(Z1)}, Z2 <= {up(Z2)}")
    print(f"   Y0^(j) = {[up(y) for y in b['Y0j']]}, K = {[[up(k) for k in row] for row in b['K']]}")
    print(f"   with these printed values: p(r0) < 0 for r0 = {sci(r0, 3)}, "
          f"p(r1) < 0 for r1 = {sci(r1, 3)}")
    # x(tau) = xtilde(1) (rescaled time t = 1 = nu), within r0 of xbar(1) evaluated exactly
    end = [taylor_eval(a, Fr(1)) for a in abar]
    centers = [enclosure(v, r0) for v in end]
    print(f"   x({tau}) in ({', '.join(centers)}) + [-1e-10, 1e-10]^3")
    print(f"   |abar_N| = {[f'{float(abs(a[N])):.1e}' for a in abar]}")
    print("   abar_j (17 significant digits, exactly as stored in the certificate):")
    print_data(abar)
    if plot:
        print("   plot data (real time s = tau t, x1, x2, x3):")
        ts = [Fr(k, 20) for k in range(-20, 21)]
        for i in range(3):
            pts = " ".join(f"({float(tau * s):.5f},{float(taylor_eval(abar[i], s)):.4f})" for s in ts)
            print(f"   x{i + 1}: {pts}")
    if write:
        cert = dict(chapter=8, example="Lorenz IVP (Taylor)", theorem="thm:TaylorIVPsystem",
                    parameters=dict(LORENZ, x0=list(x0), tau=tau), N=N, nu=nu, r_star=r_star,
                    abar=abar, abar_note="exact rational solution of F^{(N)}(a) = 0, rounded "
                    "to 17 significant decimal digits; component j is abar[j], coefficients "
                    "k = 0..N",
                    A=A, A_note="a float inverse of DF^{(N)}(abar), rounded to 17 significant "
                    "decimal digits (full double precision); index (j,k) -> j(N+1)+k",
                    r0=r0, r1=r1,
                    x_at_tau=dict(center=[Fr(c) for c in centers], radius=Fr(1, 10 ** 10)),
                    x_at_tau_note="x(tau) lies in center + [-radius, radius]^3 (an enclosure "
                    "of xbar(1) = (sum_k abar_{j,k})_j with error r0)")
        certificate.write(os.path.join(HERE, "certificates", "ch8_lorenz.json"), cert)
    return r0, r1


if __name__ == "__main__":
    scalar_example()
    lorenz_example()
