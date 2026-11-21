"""Computer-assisted proofs of Chapter 10 (periodic orbits, Fourier series).

Run:  python3 periodic_orbits.py [helmholtz] [hopf] [lorenz]      (from the code/ folder;
      without arguments all three examples are run)

Three examples are re-checked, each with the bound formulas stated in the chapter:

1. Section sec:PeriodicOrbitForcing, Theorem thm:helmholtzradii. The forced Helmholtz-Duffing
   equation u'' + c1 u' + c2 u - u^2 = c3 cos t, c1 = 1/10, c2 = 4, c3 = 1, with
   u(t) = sum_n a_n e^{int} and F_n(a) = lambda_n a_n - (a*a)_n - c3 b_n,
   lambda_n = -n^2 + i n c1 + c2. Truncation N = 10, weight nu = 5/4, r_* = infinity:
       Y0 = sum_{|n|<=N} |(A F^(N)(abar))_n| nu^|n| + sum_{N<|n|<=2N} |(abar*abar)_n| nu^|n| / |lambda_n|
       Z0 = ||I - A DF^(N)(abar)||_{1,nu,N}
       Z1 = 2 (||A Gamma||_{1,nu,N} + 1/|lambda_{N+1}|) ||abar||_{1,nu},  Gamma_nn = nu^(2|n|-2N-2)
       Z2 = 2 max(||A||_{1,nu,N}, 1/|lambda_{N+1}|)
   Certificate: certificates/ch10_helmholtz.json

2. Section sec:Hopf_bifurcation (Lorenz equations), Theorem th:radiiFiniteDim of Chapter 2 for
   the Hopf map F: R^11 -> R^11, X = (x, v1, v2, rho, omega), sigma = 10, beta = 8/3, with
   phase vectors xi_i = vbar_i and the sup norm (induced norm = maximal absolute row sum):
       Y0 = |A F(Xbar)|_inf,  Z0 = |I - A DF(Xbar)|_inf,
       Z2 = max_i sum_j sum_k |(A H_k)_ij|,  H_k = d/dX_k DF (constant: F is quadratic).
   Certificate: certificates/ch10_hopf.json

3. Section sec:ps_lorenz, Theorem thm:fourierPeriodicOrbits: the periodic orbit LR of the Lorenz
   system (sigma, rho, beta) = (10, 28, 8/3), with unknowns x = (tau0, a1, a2, a3),
   gamma(t) = sum_k a_k e^{ikt/tau0} (period 2 pi tau0), truncation N = 35, nu = 9/8,
   r_* = 10^-5, and the bounds Y0 (Lemma lem:systemFourierY0), Z0 (lem:systemFourierZ0),
   Z1 (lem:systemFourierZ1) and Z2 (lem:systemFourierZ2) exactly as stated there.
   Certificate: certificates/ch10_lorenz_LR.json

Floats are used only to compute the approximate solutions (Newton's method) and the approximate
inverses A^(N) (Gauss-Jordan elimination). These data are then rounded to decimals and the
decimals are taken as the exact data of the proof (abar to 17 significant digits, A^(N) to 17
significant digits, i.e. full double precision, see certificate.decimal), BEFORE any bound is
computed: every bound is
evaluated in exact rational arithmetic (fractions.Fraction, Python integers) from exactly the
data stored in the certificate. Complex numbers are Gaussian rationals x + iy with x, y in Q
(class GQ below). The only operation that leaves Q is the modulus |z| = sqrt(x^2 + y^2); every
modulus is replaced by a rational UPPER bound (abs_up: integer square root rounded up, absolute
error below 1/q where q is the denominator of x^2 + y^2), and by a rational LOWER bound (abs_low)
where it appears in a denominator (|lambda_n|). All bounds are monotone in these moduli, so the
rational numbers computed are rigorous upper bounds of the expressions in the theorems.

The certificates (certificates/ch10_*.json, see certificate.py) store DATA ONLY: parameters,
truncation data, abar, A^(N) and the claimed radii r0, r1, every number as an exact decimal
(non-terminating rationals such as beta = 8/3 as "p/q" strings). The bounds Y0, Z0, Z1, Z2 are
not stored; they are recomputed from the data by every checker (this script, the Lean library).

The bounds are printed rounded UP to three significant digits, and the radii r0 < r1 are chosen
so that the radii polynomial built from the PRINTED values is negative at r0 and at r1 (checked
exactly). Since p(r) is nondecreasing in Y0, Z0, Z1, Z2 for r > 0, the printed numbers alone
certify the proofs. The values printed in the book (bounds, radii, period enclosure) are pinned
by assertions (check_printed), so any change of the data that changes them is caught. The script
also prints the data abar (17 significant digits, exactly the
stored decimals) and the plot data used in the chapter.
"""
import cmath
import math
import os
import sys
import time
from fractions import Fraction as Fr

import certificate
from chebyshev_rp import solve, inverse, poly_diff, neg_interval, peval, round_up, up

CERT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "certificates")


# ----------------------------------------------------------------------------------------
# Gaussian rationals and rigorous moduli
# ----------------------------------------------------------------------------------------

class GQ:
    """Exact complex number re + i im with re, im in Q."""
    __slots__ = ("re", "im")

    def __init__(self, re=0, im=0):
        self.re = re if isinstance(re, Fr) else Fr(re)
        self.im = im if isinstance(im, Fr) else Fr(im)

    @staticmethod
    def of(z):
        if isinstance(z, GQ):
            return z
        if isinstance(z, complex):
            return GQ(Fr(z.real), Fr(z.imag))
        return GQ(Fr(z), Fr(0))

    def __add__(self, o):
        o = GQ.of(o)
        return GQ(self.re + o.re, self.im + o.im)

    __radd__ = __add__

    def __sub__(self, o):
        o = GQ.of(o)
        return GQ(self.re - o.re, self.im - o.im)

    def __rsub__(self, o):
        return GQ.of(o) - self

    def __neg__(self):
        return GQ(-self.re, -self.im)

    def __mul__(self, o):
        if isinstance(o, (int, Fr)):
            return GQ(self.re * o, self.im * o)
        o = GQ.of(o)
        return GQ(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    __rmul__ = __mul__

    def __bool__(self):
        return bool(self.re) or bool(self.im)

    def __eq__(self, o):
        o = GQ.of(o)
        return self.re == o.re and self.im == o.im

    def conj(self):
        return GQ(self.re, -self.im)

    def abs2(self):
        return self.re * self.re + self.im * self.im

    def __complex__(self):
        return complex(float(self.re), float(self.im))


def isqrt_up(m):
    """Smallest integer s with s^2 >= m (m a nonnegative integer)."""
    s = math.isqrt(m)
    return s if s * s == m else s + 1


def abs_up(z):
    """Rational upper bound of |z| (z a GQ, Fraction or int)."""
    if not isinstance(z, GQ):
        return abs(Fr(z))
    q2 = z.abs2()
    p, q = q2.numerator, q2.denominator
    return Fr(isqrt_up(p * q), q)                 # sqrt(p/q) = sqrt(p q) / q


def abs_low(z):
    """Rational lower bound of |z|."""
    if not isinstance(z, GQ):
        return abs(Fr(z))
    q2 = z.abs2()
    p, q = q2.numerator, q2.denominator
    return Fr(math.isqrt(p * q), q)


def decimal_gq(z, digits=certificate.ABAR_DIGITS):
    """Round a float complex number to a GQ whose real and imaginary parts are decimals
    with `digits` significant digits (exact rationals)."""
    return GQ(certificate.decimal(z.real, digits), certificate.decimal(z.imag, digits))


def gq_pair(z):
    """A GQ as the pair [re, im] of exact decimals (for the certificates)."""
    return [z.re, z.im]


# ----------------------------------------------------------------------------------------
# Exact matrix products with Python integers
# ----------------------------------------------------------------------------------------

def int_matrix(M):
    """A matrix of GQ as (R, I, d): integer matrices with M = (R + i I) / d."""
    d = 1
    for row in M:
        for z in row:
            d = math.lcm(d, z.re.denominator, z.im.denominator)
    R = [[z.re.numerator * (d // z.re.denominator) for z in row] for row in M]
    I = [[z.im.numerator * (d // z.im.denominator) for z in row] for row in M]
    return R, I, d


def identity_minus_product(A, J):
    """B = I - A J for square GQ matrices, computed exactly. Returns (BR, BI, d) with
    B = (BR + i BI) / d. The columns of J are processed sparsely."""
    n = len(A)
    AR, AI, dA = int_matrix(A)
    JR, JI, dJ = int_matrix(J)
    d = dA * dJ
    BR = [[0] * n for _ in range(n)]
    BI = [[0] * n for _ in range(n)]
    for c in range(n):
        nz = [(t, JR[t][c], JI[t][c]) for t in range(n) if JR[t][c] or JI[t][c]]
        for r in range(n):
            ar, ai = AR[r], AI[r]
            sr = sum(ar[t] * jr - ai[t] * ji for t, jr, ji in nz)
            si = sum(ar[t] * ji + ai[t] * jr for t, jr, ji in nz)
            BR[r][c] = (d if r == c else 0) - sr
            BI[r][c] = -si
    return BR, BI, d


def abs_up_int(R, I):
    """Integer upper bounds of the moduli |R + i I| (entrywise)."""
    return [[isqrt_up(x * x + y * y) for x, y in zip(rr, ii)] for rr, ii in zip(R, I)]


def weighted_colnorm(U, d, rows, cols, row_w, col_w):
    """max_{c in cols} (1/col_w[c]) sum_{r in rows} (U[r][c]/d) row_w[r], exactly.
    U: integer upper bounds of moduli; row_w, col_w: positive Fractions."""
    L = 1
    for r in rows:
        L = math.lcm(L, row_w[r].denominator)
    W = {r: row_w[r].numerator * (L // row_w[r].denominator) for r in rows}
    return max(Fr(sum(U[r][c] * W[r] for r in rows), d * L) / col_w[c] for c in cols)


# ----------------------------------------------------------------------------------------
# Two-sided sequences: lists s with s[k + K] = s_k for |k| <= K
# ----------------------------------------------------------------------------------------

def order(s):
    return (len(s) - 1) // 2


def conv(p, q, zero):
    """Full discrete convolution (p*q)_k = sum_j p_{k-j} q_j, |k| <= order(p) + order(q)."""
    P, Q = order(p), order(q)
    out = [zero] * (2 * (P + Q) + 1)
    for i, pv in enumerate(p):
        if not pv:
            continue
        for l, qv in enumerate(q):
            if qv:
                out[i + l] = out[i + l] + pv * qv
    return out


def pad(s, K, zero):
    k0 = order(s)
    return [zero] * (K - k0) + list(s) + [zero] * (K - k0)


def seq_add(p, q, zero):
    K = max(order(p), order(q))
    return [x + y for x, y in zip(pad(p, K, zero), pad(q, K, zero))]


def poly_eval(poly, a, one, zero, coef=lambda c: c):
    """phi(a) = sum_alpha c_alpha a^alpha (convolution powers, a^0 = e), full support."""
    out = [zero]
    for expo, c in poly.items():
        m = [one]                                           # the unit e
        for l, e in enumerate(expo):
            for _ in range(e):
                m = conv(m, a[l], zero)
        out = seq_add(out, [coef(c) * v for v in m], zero)
    return out


def seq_norm_up(s, nu):
    """Rational upper bound of ||s||_{1,nu} = sum |s_k| nu^|k|."""
    K = order(s)
    return sum((abs_up(v) * nu ** abs(i - K) for i, v in enumerate(s) if v), Fr(0))


def float_norm(s, nu):
    K = order(s)
    return sum(abs(v) * nu ** abs(i - K) for i, v in enumerate(s))


# ----------------------------------------------------------------------------------------
# Rounding, printing
# ----------------------------------------------------------------------------------------

def g17(x):
    return f"{x:.17g}"


def cstr(z):
    """A float complex number as 'a + b i' with 17 significant digits."""
    if z.imag == 0:
        return g17(z.real)
    sign = "-" if z.imag < 0 else "+"
    return f"{g17(z.real)} {sign} {g17(abs(z.imag))} i"


def printed_poly(Y0, Z0, Z1, Z2):
    """Round the bounds up to three digits and return them with the radii polynomial."""
    Y0p, Z0p, Z1p, Z2p = (round_up(x)[0] if x > 0 else Fr(0) for x in (Y0, Z0, Z1, Z2))
    p = [Y0p, -(1 - Z0p - Z1p), Z2p]
    return Y0p, Z0p, Z1p, Z2p, p


def check_printed(example, bounds, book_bounds, p, radii, book_radii):
    """Pin the numbers printed in Chapter 10 for one example.

    Mathematical intent: the book prints each bound rounded UP to three significant digits and
    states that the radii polynomial p built from these PRINTED bounds is negative at the printed
    radii. We assert (i) every exact bound rounded up equals the printed string, (ii) the radii
    computed (and stored in the certificate) equal the printed radii exactly, and (iii) p < 0 at
    the printed radii, evaluated exactly in rational arithmetic from the printed bounds."""
    for name, x in bounds.items():
        s = round_up(x)[1] if x > 0 else "0"
        assert Fr(s) == Fr(book_bounds[name]), \
            f"{example}: {name} rounded up is {s}, the book prints {book_bounds[name]}"
    for r, rb in zip(radii, book_radii):
        assert r == Fr(rb), f"{example}: radius {up(r)} differs from the printed radius {rb}"
        assert peval(p, Fr(rb)) < 0, f"{example}: p({rb}) >= 0 for the printed bounds"


def pi_bounds():
    """Rational bounds lo < pi < hi (pi = 3.14159265358979323846...)."""
    return Fr("3.14159265358979323"), Fr("3.14159265358979324")


# ========================================================================================
# Example 1: the forced Helmholtz-Duffing equation (Theorem thm:helmholtzradii)
# ========================================================================================

def helmholtz():
    c1, c2, c3 = Fr(1, 10), Fr(4), Fr(1)
    N, nu = 10, Fr(5, 4)
    D = 2 * N + 1
    assert (N + 1) ** 2 > c2
    lam = lambda n: GQ(c2 - n * n, n * c1)                   # lambda_n = -n^2 + i n c1 + c2
    b = lambda n: Fr(1, 2) if abs(n) == 1 else Fr(0)
    t_start = time.time()

    # ---- numerics: Newton for F^(N) in complex floats ---------------------------------
    lamf = [complex(lam(n)) for n in range(-N, N + 1)]

    def FN(a):
        aa = conv(a, a, 0j)[N:N + D]                          # truncated a*a, |n| <= N
        return [lamf[i] * a[i] - aa[i] - float(c3 * b(i - N)) for i in range(D)]

    def DFN(a):
        return [[(lamf[i] if i == j else 0) - (2 * a[i - j + N] if abs(i - j) <= N else 0)
                 for j in range(D)] for i in range(D)]

    a = [0j] * D
    a[N + 1] = 0.5 / lamf[N + 1]
    a[N - 1] = a[N + 1].conjugate()
    for _ in range(30):
        dx = solve(DFN(a), FN(a))
        a = [x - y for x, y in zip(a, dx)]
        a = [(a[i] + a[2 * N - i].conjugate()) / 2 for i in range(D)]   # abar_{-n} = abar_n^*
        if max(abs(x) for x in dx) < 1e-17:
            break
    a[N] = complex(a[N].real, 0.0)
    A_float = inverse(DFN(a))

    # ---- exact data: decimals, rounded BEFORE the bounds are computed ------------------
    abar = [decimal_gq(x) for x in a]
    A = [[decimal_gq(x, certificate.A_DIGITS) for x in row] for row in A_float]
    zero = GQ()
    w = [nu ** abs(n) for n in range(-N, N + 1)]                 # nu^|n|
    rows = range(D)

    # Y0
    aa_full = conv(abar, abar, zero)                              # |n| <= 2N
    F = [lam(n) * abar[n + N] - aa_full[n + 2 * N] - c3 * b(n) for n in range(-N, N + 1)]
    AF = [sum((A[i][j] * F[j] for j in range(D)), zero) for i in range(D)]
    Y0_fin = sum(abs_up(AF[i]) * w[i] for i in range(D))
    Y0_tail = sum(abs_up(aa_full[n + 2 * N]) * nu ** abs(n) / abs_low(lam(n))
                  for n in range(-2 * N, 2 * N + 1) if abs(n) > N)
    Y0 = Y0_fin + Y0_tail

    # Z0 = ||I - A DF^(N)(abar)||_{1,nu,N}
    J = [[(lam(i - N) if i == j else zero) - (2 * abar[i - j + N] if abs(i - j) <= N else zero)
          for j in range(D)] for i in range(D)]
    BR, BI, d = identity_minus_product(A, J)
    Z0 = weighted_colnorm(abs_up_int(BR, BI), d, rows, rows, w, w)

    # Z1 and Z2
    AR, AI, dA = int_matrix(A)
    UA = abs_up_int(AR, AI)
    normA = weighted_colnorm(UA, dA, rows, rows, w, w)
    Gamma = [nu ** (2 * abs(n) - 2 * (N + 1)) for n in range(-N, N + 1)]
    normAG = weighted_colnorm(UA, dA, rows, rows, w, [w[j] / Gamma[j] for j in rows])
    lamN1 = abs_low(lam(N + 1))
    norm_abar = seq_norm_up(abar, nu)
    Z1 = 2 * (normAG + 1 / lamN1) * norm_abar
    Z2 = 2 * max(normA, 1 / lamN1)

    Y0p, Z0p, Z1p, Z2p, p = printed_poly(Y0, Z0, Z1, Z2)
    r0, r1 = neg_interval(p)
    assert peval(p, r0) < 0 and peval(p, r1) < 0
    # the values printed in Chapter 10 (Section sec:PeriodicOrbitForcing)
    check_printed("Helmholtz-Duffing", {"Y0": Y0, "Z0": Z0, "Z1": Z1, "Z2": Z2},
                  {"Y0": "3.59e-9", "Z0": "3.93e-15", "Z1": "0.219", "Z2": "12.5"},
                  p, (r0, r1), ("4.60e-9", "6.24e-2"))
    assert Y0_fin < Fr(4, 10 ** 17)              # "the first sum is smaller than 4e-17"
    elapsed = time.time() - t_start

    print(f"== Helmholtz-Duffing (Theorem thm:helmholtzradii): c1 = {c1}, c2 = {c2}, c3 = {c3}, "
          f"N = {N}, nu = {nu}")
    print(f"   residual |F^(N)(abar)| = {max(abs(complex(x)) for x in F):.2e}")
    print(f"   Y0 <= {up(Y0)}  (finite part {float(Y0_fin):.3e}, tail {float(Y0_tail):.3e})")
    print(f"   Z0 <= {up(Z0)}, Z1 <= {up(Z1)}, Z2 <= {up(Z2)}")
    print(f"   ||A^(N)||_(1,nu,N) = {float(normA):.6f}, ||A^(N) Gamma|| = {float(normAG):.4e}, "
          f"1/|lambda_(N+1)| = {float(1 / lamN1):.6e}, ||abar||_(1,nu) = {float(norm_abar):.6f}")
    print(f"   printed values: p(r0) < 0 for r0 = {up(r0)}, p(r1) < 0 for r1 = {up(r1)}")
    print(f"   time {elapsed:.2f} s")
    print("   abar_n, n = 0..N (abar_{-n} = abar_n^*):")
    for n in range(N + 1):
        print(f"     {n}: {cstr(a[n + N])}")

    # plot data: u(t) and u'(t) on [0, 2 pi]
    def u(t, deriv=0):
        return sum(((1j * (n)) ** deriv) * a[n + N] * cmath.exp(1j * n * t)
                   for n in range(-N, N + 1)).real
    ts = [2 * math.pi * i / 64 for i in range(65)]
    print("   plot (t, u(t)):", " ".join(f"({t:.4f},{u(t):.5f})" for t in ts))
    print("   plot (u, u'):", " ".join(f"({u(t):.5f},{u(t, 1):.5f})" for t in ts))

    certificate.write(os.path.join(CERT_DIR, "ch10_helmholtz.json"), {
        "example": "Chapter 10, Section sec:PeriodicOrbitForcing (Helmholtz-Duffing equation)",
        "theorem": "thm:helmholtzradii",
        "problem": "u'' + c1 u' + c2 u - u^2 = c3 cos t, u(t) = sum_n a_n e^{int}, "
                   "F_n(a) = lambda_n a_n - (a*a)_n - c3 b_n, lambda_n = -n^2 + i n c1 + c2",
        "parameters": {"c1": c1, "c2": c2, "c3": c3},
        "N": N, "nu": nu, "r_star": "infinity",
        "complex_numbers": "pairs [re, im] of exact decimals",
        "moduli": "the checker bounds |z| by rational upper bounds (lower bounds for "
                  "|lambda_n| in denominators); Y0, Z0, Z1, Z2 of thm:helmholtzradii are "
                  "recomputed from the data, not stored",
        "abar_index": "n = -N..N",
        "abar": [gq_pair(z) for z in abar],
        "A_N": "numerical inverse of DF^(N)(abar), real and imaginary parts rounded to "
               "17 significant decimal digits (full double precision); rows/columns n = -N..N",
        "A_re": [[z.re for z in row] for row in A],
        "A_im": [[z.im for z in row] for row in A],
        "radii_polynomial": "p(r) = Z2 r^2 - (1 - Z0 - Z1) r + Y0 (bounds recomputed from "
                            "the data) is negative at r0 and r1",
        "r0": r0, "r1": r1,
    })
    return elapsed


# ========================================================================================
# Example 2: the Hopf point of the Lorenz equations (Theorem th:radiiFiniteDim, sup norm)
# ========================================================================================

def hopf():
    sigma, beta = Fr(10), Fr(8, 3)
    t_start = time.time()

    def make_F(xi1, xi2, num):
        """The Hopf map F(X), X = (x1,x2,x3, v1 (3), v2 (3), rho, omega)."""
        def F(X):
            x, v1, v2, rho, om = X[0:3], X[3:6], X[6:9], X[9], X[10]
            Jx = [[-sigma * num, sigma * num, 0 * num],
                  [rho - x[2], -1 * num, -x[0]],
                  [x[1], x[0], -beta * num]]
            f = [sigma * (x[1] - x[0]), rho * x[0] - x[1] - x[0] * x[2], -beta * x[2] + x[0] * x[1]]
            g1 = [sum(Jx[i][j] * v1[j] for j in range(3)) + om * v2[i] for i in range(3)]
            g2 = [sum(Jx[i][j] * v2[j] for j in range(3)) - om * v1[i] for i in range(3)]
            return f + g1 + g2 + [sum(v1[i] * xi1[i] for i in range(3)) - 1,
                                  sum(v2[i] * xi2[i] for i in range(3)) - 1]
        return F

    def jac(F, X, one):
        """DF(X): exact for quadratic F by the central difference (F(X+e)-F(X-e))/2."""
        n = len(X)
        cols = []
        for j in range(n):
            Xp = list(X); Xm = list(X)
            Xp[j] += one; Xm[j] -= one
            cols.append([(p - m) / 2 for p, m in zip(F(Xp), F(Xm))])
        return [[cols[j][i] for j in range(n)] for i in range(n)]

    # ---- Newton in floats, from the 16-digit values of the previous edition -------------
    X0 = [7.956019457871823, 7.956019457871823, 23.736842105263147, 0.556151966545753,
          0.696054940405531, 0.454095265384198, 0.145360836252368, -0.389909295949055,
          0.909307961153164, 24.736842105263147, -9.624530063715754]
    X = X0[:]
    for _ in range(4):        # the phase vectors xi_i = vbar_i are refreshed at each round
        Ff = make_F(X[3:6], X[6:9], 1.0)
        for _ in range(4):
            dx = solve(jac(Ff, X, 1.0), Ff(X))
            X = [x - y for x, y in zip(X, dx)]
    Xbar_f = X
    xi1f, xi2f = Xbar_f[3:6], Xbar_f[6:9]           # xi_i = vbar_i exactly
    Ff = make_F(xi1f, xi2f, 1.0)
    A_float = inverse(jac(Ff, Xbar_f, 1.0))

    # ---- exact data (decimals, rounded BEFORE the bounds are computed) and bounds -------
    Xbar = certificate.decimal_seq(Xbar_f)                 # 17 significant digits
    xi1, xi2 = Xbar[3:6], Xbar[6:9]                        # xi_i = vbar_i exactly
    F = make_F(xi1, xi2, Fr(1))
    A = certificate.decimal_matrix(A_float, certificate.A_DIGITS)
    n = 11
    FX = F(Xbar)
    AFX = [sum(A[i][j] * FX[j] for j in range(n)) for i in range(n)]
    Y0 = max(abs(v) for v in AFX)
    DFX = jac(F, Xbar, Fr(1))
    AD = [[sum(A[i][t] * DFX[t][j] for t in range(n)) for j in range(n)] for i in range(n)]
    Z0 = max(sum(abs((1 if i == j else 0) - AD[i][j]) for j in range(n)) for i in range(n))
    # H_k = d/dX_k DF (constant), (H_k)_{ij} = d^2 F_i / dX_j dX_k
    H = []
    for k in range(n):
        Xk = list(Xbar)
        Xk[k] += 1
        DFk = jac(F, Xk, Fr(1))
        H.append([[DFk[i][j] - DFX[i][j] for j in range(n)] for i in range(n)])
    AH = [[[sum(A[i][t] * H[k][t][j] for t in range(n)) for j in range(n)] for i in range(n)]
          for k in range(n)]
    Z2 = max(sum(abs(AH[k][i][j]) for k in range(n) for j in range(n)) for i in range(n))
    normA = max(sum(abs(v) for v in row) for row in A)

    Y0p, Z0p, _, Z2p, p = printed_poly(Y0, Z0, Fr(0), Z2)
    r0, r1 = neg_interval(p)
    assert peval(p, r0) < 0 and peval(p, r1) < 0
    # the values printed in Chapter 10 (Section sec:Hopf_bifurcation); r0 = 1.73e-14 is also
    # the printed bound on |rho~ - rhobar| and |omega~ - omegabar|
    check_printed("Hopf", {"Y0": Y0, "Z0": Z0, "Z2": Z2},
                  {"Y0": "1.72e-14", "Z0": "7.37e-14", "Z2": "334"},
                  p, (r0, r1), ("1.73e-14", "2.99e-3"))
    elapsed = time.time() - t_start
    rho_exact = Fr(470, 19)
    print(f"== Hopf point of Lorenz (Theorem th:radiiFiniteDim, sup norm), sigma = {sigma}, "
          f"beta = {beta}")
    print("   Xbar (= the phase vectors xi_1 = vbar_1, xi_2 = vbar_2 in components 4-6, 7-9):")
    for i, v in enumerate(Xbar_f):
        print(f"     {i + 1}: {g17(v)}")
    print(f"   |F(Xbar)|_inf = {float(max(abs(v) for v in FX)):.3e}, |A|_inf = {float(normA):.4f}")
    print(f"   Y0 <= {up(Y0)}, Z0 <= {up(Z0)}, Z2 <= {up(Z2)}")
    print(f"   printed values: p(r0) < 0 for r0 = {up(r0)}, p(r1) < 0 for r1 = {up(r1)}")
    print(f"   check: |rhobar - 470/19| = {float(abs(Xbar[9] - rho_exact)):.2e}, "
          f"omega^2 = beta (sigma + rho) at rho = 470/19: {math.sqrt(float(beta * (sigma + rho_exact))):.17g}")
    print(f"   time {elapsed:.2f} s")

    certificate.write(os.path.join(CERT_DIR, "ch10_hopf.json"), {
        "example": "Chapter 10, Section sec:Hopf_bifurcation, Hopf point of the Lorenz equations",
        "theorem": "th:radiiFiniteDim (Chapter 2) with Lemma lem:existenceinterval",
        "problem": "Hopf map F(X) = (f(x,rho), Df v1 + omega v2, Df v2 - omega v1, v1.xi1 - 1, "
                   "v2.xi2 - 1), X = (x, v1, v2, rho, omega) in R^11, f = Lorenz field",
        "parameters": {"sigma": sigma, "beta": beta},
        "norm": "sup norm on R^11, induced operator norm (maximal absolute row sum)",
        "Xbar": Xbar, "xi1": xi1, "xi2": xi2,
        "A": [[v for v in row] for row in A],
        "A_note": "numerical inverse of DF(Xbar), entries rounded to 17 significant decimal digits "
                  "(full double precision)",
        "Z2_formula": "max_i sum_j sum_k |(A H_k)_ij|, H_k = d/dX_k DF (constant)",
        "radii_polynomial": "p(r) = Z2 r^2 - (1 - Z0) r + Y0 (bounds recomputed from the data) "
                            "is negative at r0 and r1, r_* = infinity",
        "r0": r0, "r1": r1,
    })
    return elapsed


# ========================================================================================
# Example 3: the periodic orbit LR of the Lorenz system (Theorem thm:fourierPeriodicOrbits)
# ========================================================================================

class FourierProblem:
    """F(tau0, a) of Section sec:ps_general_polynomial_vec_field for a polynomial field f
    (list of dicts {exponent tuple: rational coefficient}), phase data xi, xihat, N0 = N."""

    def __init__(self, f, xi, xihat, N):
        self.f, self.n, self.N = f, len(f), N
        self.M = max(sum(e) for p in f for e in p)
        self.xi, self.xihat = xi, xihat
        self.df = [[poly_diff(f[j], jp) for jp in range(self.n)] for j in range(self.n)]
        self.size = 1 + self.n * (2 * N + 1)

    def idx(self, j, k):
        """Position of the unknown a_{j,k} (j = 1..n, |k| <= N); position 0 is tau0."""
        return 1 + (j - 1) * (2 * self.N + 1) + k + self.N

    def _num(self, exact):
        if exact:
            return GQ(1), GQ(), (lambda c: Fr(c))
        return 1 + 0j, 0j, (lambda c: float(c))

    def phi(self, a, exact):
        one, zero, coef = self._num(exact)
        return [pad(poly_eval(self.f[j], a, one, zero, coef), self.M * self.N, zero)
                for j in range(self.n)]

    def dphi(self, a, exact):
        """D_{j'} phi_j(a) for j, j' = 0..n-1 (sequences of order (M-1) N)."""
        one, zero, coef = self._num(exact)
        K = (self.M - 1) * self.N
        return [[pad(poly_eval(self.df[j][jp], a, one, zero, coef), K, zero)
                 for jp in range(self.n)] for j in range(self.n)]

    def FN(self, tau, a, exact):
        """F^(N)(tau, a): (F_0, F_{j,k} for j = 1..n, |k| <= N)."""
        N, MN = self.N, self.M * self.N
        ph = self.phi(a, exact)
        F0 = sum(self.xihat[j] * (sum(a[j], a[j][0] * 0) - self.xi[j]) for j in range(self.n))
        out = [F0]
        for j in range(self.n):
            for k in range(-N, N + 1):
                out.append(a[j][k + N] * (1j * k if not exact else GQ(0, k)) - tau * ph[j][k + MN])
        return out

    def DFN(self, tau, a, exact):
        N, n, MN = self.N, self.n, self.M * self.N
        one, zero, coef = self._num(exact)
        ph = self.phi(a, exact)
        dp = self.dphi(a, exact)
        K1 = (self.M - 1) * N
        S = self.size
        J = [[zero] * S for _ in range(S)]
        for jp in range(n):
            for m in range(-N, N + 1):
                J[0][self.idx(jp + 1, m)] = self.xihat[jp] * one
        for j in range(n):
            for k in range(-N, N + 1):
                r = self.idx(j + 1, k)
                J[r][0] = -ph[j][k + MN]
                J[r][r] = J[r][r] + (GQ(0, k) if exact else 1j * k)
                for jp in range(n):
                    s = dp[j][jp]
                    for m in range(-N, N + 1):
                        if abs(k - m) <= K1 and s[k - m + K1]:
                            c = self.idx(jp + 1, m)
                            J[r][c] = J[r][c] - tau * s[k - m + K1]
        return J


def rk4_orbit(f, x0, T, samples, sub):
    """Points of the RK4 solution of x' = f(x) at times m T / samples (floats)."""
    def step(x, h):
        k1 = f(x)
        k2 = f([x[i] + h / 2 * k1[i] for i in range(3)])
        k3 = f([x[i] + h / 2 * k2[i] for i in range(3)])
        k4 = f([x[i] + h * k3[i] for i in range(3)])
        return [x[i] + h / 6 * (k1[i] + 2 * k2[i] + 2 * k3[i] + k4[i]) for i in range(3)]
    h = T / (samples * sub)
    pts, x = [], list(x0)
    for _ in range(samples):
        pts.append(x)
        for _ in range(sub):
            x = step(x, h)
    return pts


def lorenz_lr(N=35, nu=Fr(9, 8), r_star=Fr(1, 10 ** 5)):
    sigma, rho, beta = Fr(10), Fr(28), Fr(8, 3)
    # f as polynomials {exponent: coefficient}
    f = [{(1, 0, 0): -sigma, (0, 1, 0): sigma},
         {(1, 0, 0): rho, (0, 1, 0): Fr(-1), (1, 0, 1): Fr(-1)},
         {(0, 0, 1): -beta, (1, 1, 0): Fr(1)}]
    ff = lambda x: [10.0 * (x[1] - x[0]), 28.0 * x[0] - x[1] - x[0] * x[2],
                    -8.0 / 3 * x[2] + x[0] * x[1]]
    t_start = time.time()
    D = 2 * N + 1
    # Phase condition: xi = a point of the orbit (12 decimals), xihat = f(xi) (exact)
    xi = [Fr("-13.763610682134"), Fr("-19.578751942452"), Fr(27)]
    xihat = [sum(c * xi[0] ** e[0] * xi[1] ** e[1] * xi[2] ** e[2] for e, c in fj.items()) for fj in f]
    prob_f = FourierProblem(f, [float(v) for v in xi], [float(v) for v in xihat], N)
    prob = FourierProblem(f, xi, xihat, N)

    # ---- initial guess: RK4 + discrete Fourier transform --------------------------------
    T0 = 1.5586522109964
    samples = 256
    pts = rk4_orbit(ff, [float(v) for v in xi], T0, samples, 40)
    a = [[sum(pts[m][j] * cmath.exp(-2j * math.pi * k * m / samples) for m in range(samples)) / samples
          for k in range(-N, N + 1)] for j in range(3)]
    tau = T0 / (2 * math.pi)

    def symmetrize(tau, a):
        """tau real, a_{j,-k} = a_{j,k}^*; the LR orbit is invariant under
        (x1,x2,x3) -> (-x1,-x2,x3) with a half period shift, so a_1, a_2 vanish at even k and
        a_3 at odd k: these coefficients are set to zero exactly."""
        out = []
        for j in range(3):
            s = [0j] * D
            for k in range(N + 1):
                v = (a[j][N + k] + a[j][N - k].conjugate()) / 2
                if (j < 2 and k % 2 == 0) or (j == 2 and k % 2 == 1):
                    v = 0j
                if k == 0:
                    v = complex(v.real, 0.0)
                s[N + k], s[N - k] = v, v.conjugate()
            out.append(s)
        return float(tau.real), out

    tau, a = symmetrize(tau, a)
    for it in range(8):
        Fv = prob_f.FN(tau, a, False)
        if max(abs(v) for v in Fv) < 1e-12 and it >= 3:
            break
        dx = solve(prob_f.DFN(tau, a, False), Fv)
        tau = tau - dx[0].real
        a = [[a[j][k] - dx[prob_f.idx(j + 1, k - N)] for k in range(D)] for j in range(3)]
        tau, a = symmetrize(tau, a)
    t_newton = time.time() - t_start
    A_float = inverse(prob_f.DFN(tau, a, False))
    t_inv = time.time() - t_start - t_newton

    # ---- exact data: decimals, rounded BEFORE the bounds are computed ----------------
    taub = certificate.decimal(tau)
    abar = [[decimal_gq(v) for v in s] for s in a]
    A = [[decimal_gq(v, certificate.A_DIGITS) for v in row] for row in A_float]
    S = prob.size
    n = 3
    zero = GQ()
    blocks = [[0]] + [list(range(prob.idx(j, -N), prob.idx(j, N) + 1)) for j in range(1, n + 1)]
    kof = lambda r: 0 if r == 0 else (r - 1) % D - N           # Fourier index of position r
    w = [nu ** abs(kof(r)) for r in range(S)]                    # weight nu^|k| (1 for tau0)
    w[0] = Fr(1)

    # Y0 (Lemma lem:systemFourierY0)
    FNv = prob.FN(taub, abar, True)
    AR, AI, dA = int_matrix(A)
    dF = 1
    for v in FNv:
        dF = math.lcm(dF, v.re.denominator, v.im.denominator)
    fr = [v.re.numerator * (dF // v.re.denominator) for v in FNv]
    fi = [v.im.numerator * (dF // v.im.denominator) for v in FNv]
    AFU = [isqrt_up(sum(AR[r][t] * fr[t] - AI[r][t] * fi[t] for t in range(S)) ** 2
                    + sum(AR[r][t] * fi[t] + AI[r][t] * fr[t] for t in range(S)) ** 2) for r in range(S)]
    dAF = dA * dF
    ph = prob.phi(abar, True)                                    # order M N = 2N
    MN = 2 * N
    Y0_parts = [Fr(AFU[0], dAF)]
    for j in range(1, n + 1):
        fin = sum(Fr(AFU[r], dAF) * w[r] for r in blocks[j])
        tail = sum(abs(taub) / abs(k) * abs_up(ph[j - 1][k + MN]) * nu ** abs(k)
                   for k in range(-MN, MN + 1) if abs(k) > N)
        Y0_parts.append(fin + tail)
    Y0 = max(Y0_parts)
    t_y0 = time.time()

    # Z0 (Lemma lem:systemFourierZ0)
    J = prob.DFN(taub, abar, True)
    BR, BI, dB = identity_minus_product(A, J)
    UB = abs_up_int(BR, BI)
    Z0_parts = [sum(weighted_colnorm(UB, dB, blocks[j], blocks[jp], w, w) for jp in range(n + 1))
                for j in range(n + 1)]
    Z0 = max(Z0_parts)
    t_z0 = time.time()

    # Z1 (Lemma lem:systemFourierZ1)
    UA = abs_up_int(AR, AI)
    Gam = [Fr(1)] + [nu ** (2 * abs(kof(r)) - 2 * (N + 1)) for r in range(1, S)]
    wG = [w[r] / Gam[r] for r in range(S)]
    kappa = [[weighted_colnorm(UA, dA, blocks[j], blocks[m], w, wG) for m in range(1, n + 1)]
             for j in range(n + 1)]                                # kappa[j][m-1]
    dp = prob.dphi(abar, True)
    dpn = [[seq_norm_up(dp[m][jp], nu) for jp in range(n)] for m in range(n)]   # ||D_{j'} phi_m||
    tail_phi = [sum(abs_up(ph[j][k + MN]) * nu ** abs(k) for k in range(-MN, MN + 1) if abs(k) > N)
                for j in range(n)]
    Z1_parts = []
    for j in range(n + 1):
        s = Fr(0)
        for jp in range(n + 1):
            if j == 0 and jp == 0:
                term = Fr(0)
            elif jp == 0:
                term = tail_phi[j - 1] / (N + 1)
            elif j == 0:
                term = abs(taub) * sum(kappa[0][m] * dpn[m][jp - 1] for m in range(n))
            else:
                term = (abs(taub) * sum(kappa[j][m] * dpn[m][jp - 1] for m in range(n))
                        + abs(taub) / (N + 1) * dpn[j - 1][jp - 1])
            s += term
        Z1_parts.append(s)
    Z1 = max(Z1_parts)

    # Z2 (Lemma lem:systemFourierZ2)
    K = [[weighted_colnorm(UA, dA, blocks[j], blocks[m], w, w) if j == 0 else
          max(weighted_colnorm(UA, dA, blocks[j], blocks[m], w, w), Fr(1, N + 1) if j == m else Fr(0))
          for m in range(1, n + 1)] for j in range(n + 1)]       # K[j][m'-1]
    abar_norm = [seq_norm_up(s, nu) for s in abar]
    R = [v + r_star for v in abar_norm]

    def eta(j, m):        # eq:fouriereta, j, m = 0..n-1
        return sum(abs(c) * e[m] * math.prod(R[l] ** (e[l] - (1 if l == m else 0)) for l in range(n))
                   for e, c in f[j].items() if sum(e) >= 1 and e[m] >= 1)

    def zeta(j, m, jp):   # eq:fourierzeta
        tot = Fr(0)
        for e, c in f[j].items():
            em = e[m] - (1 if jp == m else 0)
            if sum(e) >= 2 and e[jp] >= 1 and em >= 1:
                tot += abs(c) * e[jp] * em * math.prod(
                    R[l] ** (e[l] - (1 if l == jp else 0) - (1 if l == m else 0)) for l in range(n))
        return tot

    Z2_parts = []
    for j in range(n + 1):
        s = sum(K[j][mp] * sum(eta(mp, m) for m in range(n)) for mp in range(n))          # j' = 0
        for jp in range(n):
            s += sum(K[j][mp] * (eta(mp, jp) + (abs(taub) + r_star) * sum(zeta(mp, m, jp) for m in range(n)))
                     for mp in range(n))
        Z2_parts.append(s)
    Z2 = max(Z2_parts)
    t_end = time.time()

    Y0p, Z0p, Z1p, Z2p, p = printed_poly(Y0, Z0, Z1, Z2)
    r0, _ = neg_interval(p)
    r1 = r_star
    assert peval(p, r0) < 0 and peval(p, r1) < 0 and r0 <= r_star and r0 < taub
    # the values printed in Chapter 10 (Section sec:ps_lorenz)
    check_printed("Lorenz LR", {"Y0": Y0, "Z0": Z0, "Z1": Z1, "Z2": Z2},
                  {"Y0": "7.23e-7", "Z0": "1.08e-12", "Z1": "0.789", "Z2": "8.74e3"},
                  p, (r0, r1), ("4.14e-6", "1e-5"))
    elapsed = t_end - t_start

    print(f"== Lorenz periodic orbit LR (Theorem thm:fourierPeriodicOrbits): N = {N}, nu = {nu}, "
          f"r_* = {up(r_star)}, unknowns = {S}")
    print(f"   xi = {[str(v) for v in xi]}, xihat = f(xi) = {[str(v) for v in xihat]}")
    print(f"   residual |F^(N)(xbar)| = {max(abs(complex(v)) for v in FNv):.2e}")
    print(f"   Y0 parts {[f'{float(v):.3e}' for v in Y0_parts]}")
    print(f"   Z0 parts {[f'{float(v):.3e}' for v in Z0_parts]}")
    print(f"   Z1 parts {[f'{float(v):.4f}' for v in Z1_parts]}")
    print(f"   Z2 parts {[f'{float(v):.1f}' for v in Z2_parts]}")
    print(f"   Y0 <= {up(Y0)}, Z0 <= {up(Z0)}, Z1 <= {up(Z1)}, Z2 <= {up(Z2)}")
    print(f"   printed values: p(r0) < 0 for r0 = {up(r0)}, p(r_*) < 0 for r1 = r_* = {up(r1)}")
    lo, hi = pi_bounds()
    Tlo, Thi = 2 * lo * (taub - r0), 2 * hi * (taub + r0)
    print(f"   tau0 in [{float(taub - r0):.12f}, {float(taub + r0):.12f}], "
          f"period 2 pi tau0 in [{float(Tlo):.10f}, {float(Thi):.10f}] "
          f"(exact: [{Tlo.numerator * 10**10 // Tlo.denominator}e-10, "
          f"{-(-Thi.numerator * 10**10 // Thi.denominator)}e-10])")
    # printed enclosure of the period: 2 pi tau0~ in [1.5586261983, 1.5586782232]
    assert Fr("1.5586261983") <= Tlo and Thi <= Fr("1.5586782232")
    print(f"   timings: Newton {t_newton:.1f} s, inverse {t_inv:.1f} s, Y0 {t_y0 - t_start - t_newton - t_inv:.1f} s, "
          f"Z0 {t_z0 - t_y0:.1f} s, Z1+Z2 {t_end - t_z0:.1f} s, total {elapsed:.1f} s")
    print(f"   tau0bar = {g17(tau)}  (period {g17(2 * math.pi * tau)})")
    for j in range(3):
        print(f"   abar_{j + 1},k for k = 0..N (nonzero ones):")
        for k in range(N + 1):
            if a[j][k + N] != 0:
                print(f"     {k}: {cstr(a[j][k + N])}")

    # plot data: (x1, x3) and components over one period
    def gam(t):
        return [sum(a[j][k + N] * cmath.exp(1j * k * t) for k in range(-N, N + 1)).real for j in range(3)]
    ss = [2 * math.pi * i / 120 for i in range(121)]
    G = [gam(s) for s in ss]
    print("   plot (x1, x3):", " ".join(f"({g[0]:.3f},{g[2]:.3f})" for g in G))
    for j in range(3):
        print(f"   plot (t, x{j + 1}):", " ".join(f"({tau * s:.4f},{g[j]:.3f})" for s, g in zip(ss, G)))

    certificate.write(os.path.join(CERT_DIR, "ch10_lorenz_LR.json"), {
        "example": "Chapter 10, Section sec:ps_lorenz, periodic orbit LR of the Lorenz system",
        "theorem": "thm:fourierPeriodicOrbits (Lemmas lem:systemFourierY0, lem:systemFourierZ0, "
                   "lem:systemFourierZ1, lem:systemFourierZ2)",
        "problem": "F_0 = sum_j xihat_j (sum_{|k|<=N} a_{j,k} - xi_j), "
                   "(F_j)_k = i k a_{j,k} - tau0 (phi_j(a))_k, gamma(t) = sum_k a_k e^{ikt/tau0}",
        "f": [[{"exponent": list(e), "coefficient": c} for e, c in fj.items()] for fj in f],
        "parameters": {"sigma": sigma, "rho": rho, "beta": beta},
        "N": N, "nu": nu, "r_star": r_star, "N0": N,
        "xi": xi, "xihat": xihat,
        "norm": "X = C x (l^1_nu)^3 with the max norm over the components",
        "complex_numbers": "pairs [re, im] of exact decimals",
        "moduli": "the checker bounds |z| by rational upper bounds; Y0, Z0, Z1, Z2 of the "
                  "lemmas are recomputed from the data, not stored",
        "unknown_order": "tau0, then a_{1,k}, a_{2,k}, a_{3,k} for k = -N..N",
        "tau0bar": taub,
        "abar": [[gq_pair(z) for z in s] for s in abar],
        "A_N": "numerical inverse of DF^(N)(xbar), real and imaginary parts rounded to 17 "
               "significant decimal digits (full double precision); rows/columns in unknown_order",
        "A_re": [[z.re for z in row] for row in A],
        "A_im": [[z.im for z in row] for row in A],
        "radii_polynomial": "p(r) = Z2 r^2 - (1 - Z0 - Z1) r + Y0 (bounds recomputed from the "
                            "data, Z2 = Z2(r_*) valid for 0 < r <= r_*) is negative at r0 and r1",
        "r0": r0, "r1": r1,
    })
    return elapsed


if __name__ == "__main__":
    which = sys.argv[1:] or ["helmholtz", "hopf", "lorenz"]
    for name in which:
        {"helmholtz": helmholtz, "hopf": hopf, "lorenz": lorenz_lr}[name]()
