"""Radii polynomial approach for IVPs and BVPs via Chebyshev series.

Computer-assisted proofs for Chapters 14 and 15. The problem is

    u' = L f(u),  t in [-1, 1],   q - B_minus u(-1) - B_plus u(1) = 0,

with f a polynomial vector field on R^n. An IVP u(-1) = x0 is the case
B_minus = I, B_plus = 0, q = x0. All sequences are real.

Unknowns are Chebyshev coefficients u_j(t) = (a_j)_0 + 2 sum_{k>=1} (a_j)_k T_k(t).
The zero finding problem (rows k = 0, 1, 2, ... of each component j) is

    F_{j,0}(a) = q_j - sum_i (B_minus)_{ji} u_i(-1) - sum_i (B_plus)_{ji} u_i(1),
    F_{j,k}(a) = 2k (a_j)_k + L ((c_j)_{k+1} - (c_j)_{k-1}),   k >= 1,

where c_j = phi_j(a) is f_j with products replaced by the Chebyshev product.

Spaces (nu >= 1):
    X: weights w_0 = 1, w_k = 2 nu^k        (norm |a_0| + 2 sum |a_k| nu^k)
    Y: weights v_0 = 1, v_k = nu^k / k
Products of components carry the max norm.

Numerics (Newton, approximate inverse) use floats. The data are then rounded to exact
decimals (see certificate.py): the approximate solution abar to certificate.ABAR_DIGITS = 17
significant digits and the approximate inverse A^{(N)} to certificate.A_DIGITS = 17
significant digits (full double precision). These decimals are the data stored in the certificates, and every bound
Y0, Z0, Z1, Z2 is evaluated in exact rational arithmetic (fractions.Fraction) from exactly
these data, so the reported bounds are rigorous upper bounds for the stored data (the
bounds themselves are not stored; every checker recomputes them). The bounds are printed
rounded up to a few significant digits, and the radii r0, r1 are chosen (and checked
exactly) so that the radii polynomial built from the PRINTED values is negative there.
Since p(r) is nondecreasing in Y0, Z0, Z1 and in the coefficients of Z2 (for r > 0), this
implies the same for the unrounded bounds, so the printed numbers alone certify the proof.
"""
from fractions import Fraction
import itertools
import math

import certificate


# ----------------------------------------------------------------------------------------
# Chebyshev sequences (index k >= 0, symmetric extension a_{-k} = a_k)
# ----------------------------------------------------------------------------------------

def cheb_mult(a, b):
    """Chebyshev product (a*b)_k = sum_{k1 in Z} a_{|k1|} b_{|k-k1|}, full support."""
    na, nb = len(a) - 1, len(b) - 1
    K = na + nb
    zero = a[0] * 0
    out = [zero] * (K + 1)
    for k in range(K + 1):
        s = zero
        for k1 in range(-na, na + 1):
            k2 = abs(k - k1)
            if k2 <= nb:
                s += a[abs(k1)] * b[k2]
        out[k] = s
    return out


def cheb_add(a, b):
    n = max(len(a), len(b))
    z = (a + b)[0] * 0
    return [(a[k] if k < len(a) else z) + (b[k] if k < len(b) else z) for k in range(n)]


def cheb_scale(c, a):
    return [c * x for x in a]


def identity_seq(one):
    return [one]


def monomial(a, expo, one):
    """a^expo with the Chebyshev product (a is a list of component sequences)."""
    out = identity_seq(one)
    for i, e in enumerate(expo):
        for _ in range(e):
            out = cheb_mult(out, a[i])
    return out


def poly_eval(poly, a, one):
    """phi(a) for a polynomial given as {exponent tuple: coefficient}."""
    out = [one * 0]
    for expo, coef in poly.items():
        out = cheb_add(out, cheb_scale(coef, monomial(a, expo, one)))
    return out


def poly_diff(poly, i):
    """Partial derivative of a polynomial with respect to variable i."""
    out = {}
    for expo, coef in poly.items():
        if expo[i] > 0:
            e = list(expo)
            e[i] -= 1
            out[tuple(e)] = out.get(tuple(e), 0) + coef * expo[i]
    return out


def seq_norm(a, nu):
    """|a_0| + 2 sum_{k>=1} |a_k| nu^k."""
    return abs(a[0]) + 2 * sum(abs(a[k]) * nu ** k for k in range(1, len(a)))


# ----------------------------------------------------------------------------------------
# The zero finding problem
# ----------------------------------------------------------------------------------------

class ChebProblem:
    def __init__(self, f, L, Bm, Bp, q):
        self.f = f              # list of n polynomials
        self.n = len(f)
        self.L = L
        self.Bm, self.Bp, self.q = Bm, Bp, q
        self.M = max(sum(e) for p in f for e in p)   # degree
        self.df = [[poly_diff(f[j], i) for i in range(self.n)] for j in range(self.n)]

    # values u_i(-1), u_i(1)
    @staticmethod
    def endpoint(a, s):
        return a[0] + 2 * sum((s ** k) * a[k] for k in range(1, len(a)))

    def residual(self, a, kmax):
        """F_{j,k}(a) for k = 0..kmax (a has finite support)."""
        one = a[0][0] * 0 + 1
        c = [poly_eval(self.f[j], a, one) for j in range(self.n)]
        F = []
        for j in range(self.n):
            row0 = self.q[j]
            for i in range(self.n):
                row0 -= self.Bm[j][i] * self.endpoint(a[i], -1) + self.Bp[j][i] * self.endpoint(a[i], 1)
            Fj = [row0]
            cj = c[j]
            get = lambda k: cj[k] if k < len(cj) else 0 * one
            for k in range(1, kmax + 1):
                ak = a[j][k] if k < len(a[j]) else 0 * one
                Fj.append(2 * k * ak + self.L * (get(k + 1) - get(k - 1)))
            F.append(Fj)
        return F

    def derivative_seqs(self, a):
        """b^{ji} = D_i phi_j(a) as Chebyshev sequences."""
        one = a[0][0] * 0 + 1
        return [[poly_eval(self.df[j][i], a, one) for i in range(self.n)] for j in range(self.n)]

    def jacobian(self, a, N):
        """DF^{(N)}(a): square matrix of size n(N+1), index (j,k) -> j*(N+1)+k."""
        one = a[0][0] * 0 + 1
        zero = 0 * one
        b = self.derivative_seqs(a)
        D = N + 1
        J = [[zero] * (self.n * D) for _ in range(self.n * D)]
        for j in range(self.n):
            for i in range(self.n):
                for k in range(D):
                    e_minus = 1 if k == 0 else 2 * (-1) ** k
                    e_plus = 1 if k == 0 else 2
                    J[j * D][i * D + k] = -(self.Bm[j][i] * e_minus + self.Bp[j][i] * e_plus) * one
                bij = b[j][i]
                g = lambda l: bij[l] if l < len(bij) else zero
                for m in range(1, D):
                    for k in range(D):
                        # d/dh_k of (b*h)_l = b_l (k=0) or b_{|l-k|} + b_{l+k} (k>=1)
                        def dconv(l):
                            return g(l) if k == 0 else g(abs(l - k)) + g(l + k)
                        J[j * D + m][i * D + k] += self.L * (dconv(m + 1) - dconv(m - 1))
            for m in range(1, D):
                J[j * D + m][j * D + m] += 2 * m
        return J


# ----------------------------------------------------------------------------------------
# Float linear algebra
# ----------------------------------------------------------------------------------------

def solve(A, b):
    n = len(A)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(M[r][c]))
        M[c], M[p] = M[p], M[c]
        for r in range(c + 1, n):
            fct = M[r][c] / M[c][c]
            if fct:
                for k in range(c, n + 1):
                    M[r][k] -= fct * M[c][k]
    x = [0.0] * n
    for r in range(n - 1, -1, -1):
        x[r] = (M[r][n] - sum(M[r][k] * x[k] for k in range(r + 1, n))) / M[r][r]
    return x


def inverse(A):
    n = len(A)
    M = [row[:] + [1.0 if i == j else 0.0 for j in range(n)] for i, row in enumerate(A)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(M[r][c]))
        M[c], M[p] = M[p], M[c]
        piv = M[c][c]
        M[c] = [x / piv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c]:
                fct = M[r][c]
                M[r] = [x - fct * y for x, y in zip(M[r], M[c])]
    return [row[n:] for row in M]


def newton(prob, a0, N, tol=1e-15, maxit=50):
    """Newton for F^{(N)}; a0 is a list of n float sequences of length N+1."""
    a = [list(x) for x in a0]
    D = N + 1
    for _ in range(maxit):
        F = prob.residual(a, N)
        vec = [F[j][k] for j in range(prob.n) for k in range(D)]
        if max(abs(x) for x in vec) < tol:
            break
        J = prob.jacobian(a, N)
        dx = solve(J, vec)
        for j in range(prob.n):
            for k in range(D):
                a[j][k] -= dx[j * D + k]
    return a


# ----------------------------------------------------------------------------------------
# Rigorous bounds (exact rational arithmetic)
# ----------------------------------------------------------------------------------------

def approximate_inverse(prob, abar, N):
    """The approximate inverse A^{(N)} of DF^{(N)}(abar): the floating point inverse of the
    (float) Jacobian, rounded to certificate.A_DIGITS significant decimal digits. Any matrix
    is admissible in the radii polynomial theorem; the rounding only affects Z0 (and, very
    slightly, the other bounds), since the bounds are computed exactly from this A."""
    abar_float = [[float(x) for x in seq] for seq in abar]
    return certificate.decimal_matrix(inverse(prob.jacobian(abar_float, N)), certificate.A_DIGITS)


def bounds(prob, abar, A, N, nu):
    """Exact bounds for the data abar (exact rationals, the stored decimals) and A (the
    approximate inverse, exact rationals): return Y0, Z0, Z1 (Fractions), Z2 as a list of
    polynomial coefficients in r, and a flag telling whether Z2 equals max_j Z2_j."""
    n, D, L, M = prob.n, N + 1, Fraction(prob.L), prob.M
    nu = Fraction(nu)
    abar = [[Fraction(x) for x in seq] for seq in abar]
    A = [[Fraction(x) for x in row] for row in A]
    exact = ChebProblem(prob.f, L, prob.Bm, prob.Bp, prob.q)

    w = [Fraction(1)] + [2 * nu ** k for k in range(1, M * N + 5)]          # X weights
    v = [Fraction(1)] + [nu ** k / k for k in range(1, M * N + 5)]          # Y weights

    # --- Y0 -------------------------------------------------------------------------
    F = exact.residual(abar, M * N + 1)
    FN = [F[j][k] for j in range(n) for k in range(D)]
    AF = [sum(A[r][c] * FN[c] for c in range(n * D) if FN[c]) for r in range(n * D)]
    Y0 = max(
        sum(abs(AF[j * D + k]) * w[k] for k in range(D))
        + sum(abs(F[j][k]) * w[k] / (2 * k) for k in range(D, M * N + 2))
        for j in range(n))

    # --- Z0 -------------------------------------------------------------------------
    # E = I - A^{(N)} DF^{(N)}(xbar)
    J = exact.jacobian(abar, N)
    E = [[(1 if r == c else 0) - sum(A[r][t] * J[t][c] for t in range(n * D) if J[t][c] != 0)
          for c in range(n * D)] for r in range(n * D)]

    def block_colnorm(Mat, j, i, wrow, wcol, cols):
        return max(sum(abs(Mat[j * D + m][i * D + k]) * wrow[m] for m in range(D)) / wcol[k]
                   for k in cols)

    Z0 = max(sum(block_colnorm(E, j, i, w, w, range(D)) for i in range(n)) for j in range(n))

    # --- Z1 -------------------------------------------------------------------------
    b = exact.derivative_seqs(abar)
    Omega = [sum(seq_norm(b[j][i], nu) for i in range(n)) for j in range(n)]

    # Finite rows: C = pi_N DF(abar) restricted to the tail columns k > N (the matrix
    # \mathcal{C} of the text). For 1 <= m <= N the entries vanish when k > M N + 1, since
    # b^{ji} has support in [0, (M-1) N]. The row m = 0 depends on k only through (-1)^k.
    # Hence column k of A^{(N)} C equals column k + 2 for k >= M N + 2, and since w_k is
    # increasing, the supremum over all k > N is attained at some N < k <= KT = M N + 3.
    KT = M * N + 3
    Dk = KT + 1
    Jext = exact.jacobian(abar, KT)
    C = [[Jext[j * Dk + m][i * Dk + k] for i in range(n) for k in range(D, Dk)]
         for j in range(n) for m in range(D)]
    ncol = KT - N
    AC = [[sum(A[r][t] * C[t][c] for t in range(n * D) if C[t][c] != 0) for c in range(n * ncol)]
          for r in range(n * D)]
    Z1_fin = [sum(max(sum(abs(AC[j * D + m][i * ncol + kk]) * w[m] for m in range(D)) / w[N + 1 + kk]
                      for kk in range(ncol)) for i in range(n)) for j in range(n)]
    Z1 = max(Z1_fin[j] + L * (nu + 1 / nu) * Omega[j] / (2 * (N + 1)) for j in range(n))

    # --- Z2 -------------------------------------------------------------------------
    # ||A_{ji}||_{B(Y,X)}: finite columns, and the tail diagonal contributes 1 when i == j
    K = [[max(block_colnorm(A, j, i, w, v, range(D)), Fraction(1 if i == j else 0))
          for i in range(n)] for j in range(n)]
    norms = [seq_norm(s, nu) for s in abar]

    def theta_coeffs(i):
        """Coefficients (in r) of sum_{m,l} |d_l d_m f_i|(||abar|| + r)."""
        coeffs = {}
        for m_, l_ in itertools.product(range(n), repeat=2):
            p2 = poly_diff(poly_diff(prob.f[i], m_), l_)
            for expo, coef in p2.items():
                # prod_k (norm_k + r)^{e_k}, expanded in r
                poly_r = {0: Fraction(abs(Fraction(coef)))}
                for kk, e in enumerate(expo):
                    for _ in range(e):
                        new = {}
                        for d, cf in poly_r.items():
                            new[d] = new.get(d, 0) + cf * norms[kk]
                            new[d + 1] = new.get(d + 1, 0) + cf
                        poly_r = new
                for d, cf in poly_r.items():
                    coeffs[d] = coeffs.get(d, 0) + cf
        return coeffs

    theta = [theta_coeffs(i) for i in range(n)]
    deg = max([max(t) for t in theta if t] + [0])
    const = L * (nu + 1 / (2 * nu))
    # Theorem: Z2(r) = max_j Z2_j(r) with Z2_j(r) = const * sum_i K_ji Theta_i(r).
    Z2_rows = [[const * sum(K[j][i] * theta[i].get(d, 0) for i in range(n)) for d in range(deg + 1)]
               for j in range(n)]
    # We use the polynomial whose coefficients are the maxima over j. All coefficients are
    # nonnegative, so it is >= max_j Z2_j(r) for every r >= 0, i.e. it is a valid Z2 bound.
    # It equals max_j Z2_j(r) when a single row j dominates every coefficient (checked below
    # and reported as Z2_exact; this holds in all examples of the book).
    Z2 = [max(Z2_rows[j][d] for j in range(n)) for d in range(deg + 1)]
    Z2_exact = any(Z2_rows[j] == Z2 for j in range(n))
    return Y0, Z0, Z1, Z2, Z2_exact


def radii_poly(Y0, Z0, Z1, Z2):
    """p(r) = Z2(r) r^2 - (1 - Z0 - Z1) r + Y0 as a coefficient list."""
    p = [Fraction(0)] * (len(Z2) + 2)
    p[0] = Y0
    p[1] = -(1 - Z0 - Z1)
    for d, c in enumerate(Z2):
        p[d + 2] += c
    return p


def peval(p, r):
    return sum(c * r ** d for d, c in enumerate(p))


def neg_interval(p):
    """Rational r0 < r1 with p(r0) < 0 and p(r1) < 0 (exactly verified), or None."""
    pf = [float(c) for c in p]
    f = lambda r: sum(c * r ** d for d, c in enumerate(pf))
    grid = [10 ** (e / 20) for e in range(-400, 21)]
    neg = [r for r in grid if f(r) < 0]
    if not neg:
        return None

    def nice(x, up):
        e = math.floor(math.log10(x)) - 2
        s = 10 ** e
        k = math.ceil(x / s) if up else math.floor(x / s)
        return Fraction(k) * Fraction(10) ** e

    lo, hi = min(neg), max(neg)
    # refine the left root by bisection on floats
    a, b = lo / 10 ** (1 / 20), lo
    for _ in range(200):
        m = (a + b) / 2
        a, b = (a, m) if f(m) < 0 else (m, b)
    r0 = nice(b * (1 + 1e-6), True)
    a, b = hi, hi * 10 ** (1 / 20)
    for _ in range(200):
        m = (a + b) / 2
        a, b = (m, b) if f(m) < 0 else (a, m)
    r1 = nice(a * (1 - 1e-6), False)
    assert peval(p, r0) < 0 and peval(p, r1) < 0
    return r0, r1


def round_up(x, digits=3):
    """The nonnegative rational x rounded UP to `digits` significant decimal digits.
    Returns (value, string), where value is the exact Fraction denoted by the string."""
    x = Fraction(x)
    if x == 0:
        return Fraction(0), "0"
    e = math.floor(math.log10(float(x))) - digits + 1
    while Fraction(10) ** (e + digits - 1) > x:      # guard against float log10 rounding
        e -= 1
    while Fraction(10) ** (e + digits) <= x:
        e += 1
    k = math.ceil(x / Fraction(10) ** e)
    if k == 10 ** digits:                            # rounding up carried into a new digit
        k, e = 10 ** (digits - 1), e + 1
    val = Fraction(k) * Fraction(10) ** e
    digs = str(k)
    string = f"{digs[0]}.{digs[1:]}e{e + digits - 1}"
    assert val >= x and Fraction(string) == val
    return val, string


def up(x, digits=3):
    """Decimal string that is a guaranteed upper bound for the nonnegative rational x."""
    return round_up(x, digits)[1]


def enclosure(v, r, decimals=10):
    """Rigorous enclosure of a number known to lie within r of the rational v:
    returns the decimal string c with `decimals` digits nearest to v and checks
    (exactly) that |x - c| <= 10^-decimals for every x with |x - v| <= r."""
    s = Fraction(1, 10 ** decimals)
    c = Fraction(round(v / s)) * s
    assert abs(v - c) + r <= s
    sign = "-" if c < 0 else ""
    q, rem = divmod(abs(c.numerator) * 10 ** decimals // c.denominator, 10 ** decimals)
    return f"{sign}{q}.{rem:0{decimals}d}"


def cheb_eval(a, t):
    """Evaluate a_0 + 2 sum a_k T_k(t) using T_{k+1} = 2 t T_k - T_{k-1}. Exact if the
    a_k and t are Fractions, float otherwise."""
    T_prev, T_cur = t * 0 + 1, t          # T_0, T_1
    s = a[0]
    for k in range(1, len(a)):
        if k > 1:
            T_prev, T_cur = T_cur, 2 * t * T_cur - T_prev
        s += 2 * a[k] * T_cur
    return s


def cheb_interp(func, N):
    """Chebyshev coefficients (a_0 + 2 sum a_k T_k convention) interpolating func at
    the N+1 Chebyshev points; used only to build Newton initial guesses."""
    th = [math.pi * (j + 0.5) / (N + 1) for j in range(N + 1)]
    vals = [func(math.cos(t)) for t in th]
    return [sum(vals[j] * math.cos(k * th[j]) for j in range(N + 1)) / (N + 1) for k in range(N + 1)]
