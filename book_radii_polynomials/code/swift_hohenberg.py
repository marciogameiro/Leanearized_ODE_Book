"""Equilibria of the Swift-Hohenberg equation via Fourier series (Chapter 13).

Run:  python3 swift_hohenberg.py          (from the code/ folder)

The problem (Section "Equilibria of Swift-Hohenberg with Neumann boundary conditions"):

    0 = (lambda - 1) u - 2 u'' - u'''' - u^3,   u even and 2 pi / L periodic,

with u(y) = a_0 + 2 sum_{k>=1} a_k cos(k L y). The coefficients solve F(a) = 0, where

    F_k(a) = mu_k a_k - (a^3)_k,   mu_k = lambda - (1 - k^2 L^2)^2,   k >= 0,

and a^3 = a*a*a is the symmetric convolution of one-sided sequences
(a*b)_k = sum_{k1 in Z} a_{|k1|} b_{|k - k1|}  (the same product as in chebyshev_rp.cheb_mult).

What is proved. For lambda = 1 (m = 18) and lambda = 10 (m = 31), L = 13/20, and several
weights nu >= 1, the script evaluates EXACTLY the bounds of Theorem thm:SH_radii_polynomial:

    Y0     = sum_{k<m} |[A_m F^(m)(abar)]_k| nu^k + sum_{k=m}^{3m-3} |(abar^3)_k| nu^k / |mu_k|
    Z^(0)  = max_n nu^-n sum_l |(I_m - A_m DF^(m)(abar))_{l,n}| nu^l
    Z^(1)  = 3 sum_{k<m} (|A_m| (|abar|^2 * omega~)_F)_k nu^k + 48 ||abar||_nu^2 / |mu_m|
    Z^(2)  = 96 alpha_nu ||abar||_nu,   Z^(3) = 48 alpha_nu,
    alpha_nu = max(K, 1/|mu_m|),  K = max_n nu^-n sum_l |(A_m)_{l,n}| nu^l,

with omega~_j = nu^-j for m <= j <= 3m-3 and 0 otherwise, and the radii polynomial
p(r) = Z^(3) r^3 + Z^(2) r^2 + (Z^(0) + Z^(1) - 1) r + Y0. The hypothesis eq:SH_mu_hyp is
checked through Lemma lem:SH_mu_tail (m L >= 1 and (m^2 L^2 - 1)^2 > lambda).

Floats are used only for Newton's method and for the approximate inverse A_m; these data
are then rounded to exact decimals (abar to certificate.ABAR_DIGITS = 17 significant digits,
A_m to certificate.A_DIGITS = 17, full double precision) BEFORE any bound is computed,
and all the bounds are computed in exact rational arithmetic (fractions.Fraction) from
exactly these decimals. The
bounds are printed rounded UP to three significant digits, and r0 < r1 are chosen so that
the radii polynomial built from the PRINTED values is negative at r0 and at r1 (checked
exactly). Since p is nondecreasing in each bound for r > 0 (Remark rem:SH_upper_bounds),
the printed numbers alone certify the proofs.

Certificates: certificates/ch13_sh_lambda1.json and certificates/ch13_sh_lambda10.json.
They store DATA only (lambda, L, m, abar, A_m and, for every weight nu, the radii r0, r1),
every number as a JSON number denoting exactly the decimal written (see certificate.py;
e.g. L = 13/20 is stored as 0.65). The bounds are not stored: every checker recomputes them
from the stored data.
"""
from fractions import Fraction as Fr
import math
import os
import time

import certificate
from chebyshev_rp import cheb_mult, solve, inverse, neg_interval, peval, round_up, up, enclosure

L_WAVE = Fr(13, 20)          # L = 0.65

# The values printed in Table fig:data_proof_SH of the book (Chapter 13): for each nu the
# bounds Y0, Z^(0), Z^(1), Z^(2), Z^(3) rounded up to three significant digits and the radii
# r0, r1 (stored exactly in the certificates); then the sup error 2 r0(1) and the enclosure
# of u(0) printed in the text. run() asserts that the computation reproduces them.
BOOK = {
    1: dict(table={
        Fr(1): ("8.54e-17", "3.03e-15", "7.56e-4", "5.03e2", "5.12e2", "8.55e-17", "1.98e-3"),
        Fr(2): ("3.39e-14", "4.48e-15", "2.98e-3", "1.47e3", "6.87e2", "3.41e-14", "6.78e-4"),
        Fr(4): ("1.91e-8", "1.96e-14", "2.15e-2", "1.69e4", "2.93e3", "1.96e-8", "5.78e-5"),
        Fr(5): ("1.41e-6", "3.34e-14", "5.09e-2", "4.84e4", "5.47e3", "1.62e-6", "1.79e-5")},
        sup_error="1.71e-16", u0="0.9289703567"),
    10: dict(table={
        Fr(1): ("2.88e-16", "1.11e-12", "2.00e-3", "1.62e3", "3.50e2", "2.89e-16", "6.15e-4"),
        Fr(3, 2): ("2.12e-12", "2.50e-14", "5.71e-3", "3.62e3", "4.15e2", "2.14e-12", "2.74e-4"),
        Fr(2): ("1.79e-8", "2.85e-14", "1.93e-2", "1.62e4", "9.99e2", "1.83e-8", "6.05e-5"),
        Fr(75, 32): ("2.75e-6", "3.96e-14", "4.77e-2", "5.01e4", "1.97e3", "3.56e-6", "1.54e-5")},
        sup_error="5.78e-16", u0="3.1730186915"),
}


# ----------------------------------------------------------------------------------------
# The zero finding problem (generic in the number type: float or Fraction)
# ----------------------------------------------------------------------------------------

def mu(k, lam, L):
    """Eigenvalue mu_k = lambda - (1 - k^2 L^2)^2 of the linear part (eq:sh_eig)."""
    return lam - (1 - k * k * L * L) ** 2


def cube(a):
    """a^3 = a*a*a (symmetric convolution); full support 0..3(len(a)-1)."""
    return cheb_mult(cheb_mult(a, a), a)


def galerkin_F(a, lam, L):
    """F^(m)(a) = (mu_k a_k - (a^3)_k)_{k<m}, with a identified with (a, 0)."""
    c = cube(a)
    return [mu(k, lam, L) * a[k] - c[k] for k in range(len(a))]


def galerkin_DF(a, lam, L):
    """DF^(m)(a) (eq:SH_DFm): entries mu_l delta_{ln} - 3 w_l (n = 0) or
    mu_l delta_{ln} - 3 (w_{|l-n|} + w_{l+n}) (n >= 1), where w = a^2."""
    m = len(a)
    w = cheb_mult(a, a)                      # support 0..2m-2
    g = lambda i: w[i] if i < len(w) else 0 * a[0]
    J = [[(-3 * g(l) if n == 0 else -3 * (g(abs(l - n)) + g(l + n))) for n in range(m)]
         for l in range(m)]
    for l in range(m):
        J[l][l] += mu(l, lam, L)
    return J


def newton(a, lam, L, tol=1e-14, maxit=60):
    a = list(a)
    for _ in range(maxit):
        F = galerkin_F(a, lam, L)
        dx = solve(galerkin_DF(a, lam, L), F)
        a = [x - d for x, d in zip(a, dx)]
        if max(abs(d) for d in dx) < tol:
            break
    return a


def norm(a, nu):
    """||a||_nu = sum_{k>=0} |a_k| nu^k (one-sided)."""
    return sum(abs(x) * nu ** k for k, x in enumerate(a))


def u_eval(a, y):
    """u(y) = a_0 + 2 sum_{k>=1} a_k cos(k L y) (float)."""
    return float(a[0]) + 2 * sum(float(a[k]) * math.cos(k * float(L_WAVE) * y) for k in range(1, len(a)))


# ----------------------------------------------------------------------------------------
# The bounds of Theorem thm:SH_radii_polynomial (exact if all inputs are Fractions)
# ----------------------------------------------------------------------------------------

def hypothesis_mu(lam, L, m):
    """Lemma lem:SH_mu_tail: m L >= 1 and (m^2 L^2 - 1)^2 > lambda imply eq:SH_mu_hyp."""
    return m * L >= 1 and (m * m * L * L - 1) ** 2 > lam


def bounds(abar, A, lam, L, nu):
    """Y0, Z^(0), Z^(1), Z^(2), Z^(3), alpha_nu, K, ||abar||_nu."""
    m = len(abar)
    zero = 0 * abar[0]
    pw = [nu ** k for k in range(3 * m)]                         # nu^k, k <= 3m-1
    mus = [mu(k, lam, L) for k in range(3 * m)]
    absA = [[abs(x) for x in row] for row in A]

    def colnorm(M):
        """max_n nu^-n sum_l |M_{l,n}| nu^l  (eq:K_background with omega = omega' = nu^n)."""
        return max(sum(abs(M[l][n]) * pw[l] for l in range(m)) / pw[n] for n in range(m))

    # --- Y0 (eq:explicit_Y) ---------------------------------------------------------
    c3 = cube(abar)                                              # support 0..3m-3
    F = [mus[k] * abar[k] - c3[k] for k in range(m)]
    AF = [sum(A[l][n] * F[n] for n in range(m)) for l in range(m)]
    Y0 = sum(abs(AF[k]) * pw[k] for k in range(m)) \
        + sum(abs(c3[k]) * pw[k] / abs(mus[k]) for k in range(m, 3 * m - 2))

    # --- Z^(0) (eq:gamma_0) ---------------------------------------------------------
    J = galerkin_DF(abar, lam, L)
    E = [[(1 if l == n else 0) - sum(A[l][t] * J[t][n] for t in range(m)) for n in range(m)]
         for l in range(m)]
    Z0 = colnorm(E)

    # --- alpha_nu (eq:norm_of_A) ----------------------------------------------------
    K = colnorm(A)
    alpha = max(K, 1 / abs(mus[m]))

    # --- Z^(1) (eq:SHZ1) ------------------------------------------------------------
    abs_a = [abs(x) for x in abar]
    a2 = cheb_mult(abs_a, abs_a)                                 # |abar|^2, support 0..2m-2
    om = [zero] * m + [1 / pw[j] for j in range(m, 3 * m - 2)]   # omega~, support m..3m-3
    v = cheb_mult(a2, om)[:m]                                    # (|abar|^2 omega~)_F
    nrm = norm(abar, nu)
    Z1 = 3 * sum(sum(absA[k][n] * v[n] for n in range(m)) * pw[k] for k in range(m)) \
        + 48 * nrm ** 2 / abs(mus[m])

    # --- Z^(2), Z^(3) (eq:SHZ2, eq:SHZ3) ---------------------------------------------
    Z2 = 96 * alpha * nrm
    Z3 = 48 * alpha
    return dict(Y0=Y0, Z0=Z0, Z1=Z1, Z2=Z2, Z3=Z3, alpha=alpha, K=K, norm_abar=nrm)


def radii_poly(b):
    """p(r) = Z3 r^3 + Z2 r^2 + (Z0 + Z1 - 1) r + Y0 (eq:explicit_rad_poly), coefficients."""
    return [b["Y0"], b["Z0"] + b["Z1"] - 1, b["Z2"], b["Z3"]]


def float_success(abar, A, lam, nu):
    """Float evaluation: is p(r) < 0 for some r > 0? Used only to locate nu_max.
    p(r)/r is convex in r (Remark rem:SH_upper_bounds), hence unimodal in log r, and we
    minimize it by ternary search over log r."""
    b = bounds(abar, A, lam, float(L_WAVE), nu)
    p = radii_poly(b)
    q = lambda t: sum(c * math.exp(t) ** (d - 1) for d, c in enumerate(p))
    lo, hi = -80.0, 5.0
    for _ in range(200):
        t1, t2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        lo, hi = (lo, t2) if q(t1) < q(t2) else (t1, hi)
    return q(lo) < 0


# ----------------------------------------------------------------------------------------
# The examples
# ----------------------------------------------------------------------------------------

def run(lam, m, nus, cert_name):
    t_start = time.time()
    L = L_WAVE
    assert hypothesis_mu(lam, L, m)
    # Newton: start from the single-mode approximation u = 2 a_1 cos(L y), for which
    # mu_1 a_1 = (a^3)_1 = 3 a_1^3, i.e. a_1 = sqrt(mu_1 / 3); all other modes zero.
    mu1 = float(mu(1, lam, L))
    a0 = [0.0] * m
    a0[1] = math.sqrt(mu1 / 3)
    abar = newton(a0, float(lam), float(L))
    J = galerkin_DF(abar, float(lam), float(L))
    A_float = inverse(J)
    A = certificate.decimal_matrix(A_float, certificate.A_DIGITS)   # exact decimal inverse
    abar_q = certificate.decimal_seq(abar, certificate.ABAR_DIGITS)  # exact decimal data

    # nu_max: largest nu with I(nu) nonempty (float bisection; not part of any proof)
    lo, hi = 1.0, 16.0
    for _ in range(40):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if float_success(abar, A_float, float(lam), mid) else (lo, mid)
    nu_max = lo

    print(f"== lambda = {lam}, L = {L}, m = {m}: hypothesis (lem:SH_mu_tail) holds: "
          f"m L = {float(m * L)}, (m^2L^2-1)^2 = {float((m * m * L * L - 1) ** 2):.4g} > lambda")
    print(f"   abar_1, abar_3, abar_5 = {abar[1]:.10f}, {abar[3]:.10f}, {abar[5]:.10f}; "
          f"max |abar_even| = {max(abs(abar[k]) for k in range(0, m, 2))}")
    print("   abar (odd k; the even coefficients are exactly 0): "
          + ", ".join(f"{k}: {certificate.decimal_text(abar_q[k])}" for k in range(1, m, 2)))
    print(f"   |abar_{m - 1}| = {abs(abar[m - 1]):.3e}; float nu_max ~ {nu_max:.4f}")

    cert = dict(chapter=13, example=f"Swift-Hohenberg equilibrium, lambda = {lam}",
                theorem="thm:SH_radii_polynomial", lam=Fr(lam), L=L, m=m,
                hypothesis="lem:SH_mu_tail: m L >= 1 and (m^2 L^2 - 1)^2 > lambda (checked)",
                abar=abar_q, A_m=A, proofs=[])
    for nu in nus:
        t0 = time.time()
        b = bounds(abar_q, A, Fr(lam), L, nu)
        printed = {k: round_up(b[k]) for k in ("Y0", "Z0", "Z1", "Z2", "Z3")}
        pp = radii_poly({k: v[0] for k, v in printed.items()})
        r0, r1 = neg_interval(pp)
        assert peval(pp, r0) < 0 and peval(pp, r1) < 0            # exact, printed values
        strip = math.log(nu) / float(L)
        print(f"   nu = {nu}:  Y0 <= {printed['Y0'][1]}, Z0 <= {printed['Z0'][1]}, "
              f"Z1 <= {printed['Z1'][1]}, Z2 <= {printed['Z2'][1]}, Z3 <= {printed['Z3'][1]}"
              f"  (alpha <= {up(b['alpha'])}, ||abar|| <= {up(b['norm_abar'])})")
        print(f"            p < 0 at r0 = {up(r0)} and r1 = {up(r1)};  ln(nu)/L = {strip:.4f}"
              f"   [{time.time() - t0:.1f} s]")
        # the book's table: printed bounds (rounded up) and radii (exact) must agree
        book = BOOK[lam]["table"][nu]
        for key, val in zip(("Y0", "Z0", "Z1", "Z2", "Z3"), book[:5]):
            assert printed[key][0] == Fr(val), (lam, nu, key, printed[key][1], val)
        assert (r0, r1) == (Fr(book[5]), Fr(book[6])), (lam, nu, r0, r1, book[5:])
        cert["proofs"].append(dict(nu=nu, r0=r0, r1=r1))     # data only; bounds recomputed

    # sup_y |u(y) - ubar(y)| <= 2 ||a~ - abar||_1 <= 2 r0 (with r0 of nu = 1)
    r0_1 = cert["proofs"][0]["r0"]
    u0 = abar_q[0] + 2 * sum(abar_q[1:])
    u0_text = enclosure(u0, 2 * r0_1, 10)
    assert u0_text == BOOK[lam]["u0"] and up(2 * r0_1) == BOOK[lam]["sup_error"]
    print(f"   u(0) in {u0_text} +- 1e-10 (sup error <= 2 r0 = {up(2 * r0_1)})")
    ys = [k * 2 * math.pi / float(L) / 80 for k in range(81)]
    print("   plot: " + " ".join(f"({y:.4f},{u_eval(abar, y):.4f})" for y in ys))
    certificate.write(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                   "certificates", cert_name), cert)
    print(f"   certificate: certificates/{cert_name}   total time {time.time() - t_start:.1f} s")
    return cert


if __name__ == "__main__":
    run(1, 18, [Fr(1), Fr(2), Fr(4), Fr(5)], "ch13_sh_lambda1.json")
    run(10, 31, [Fr(1), Fr(3, 2), Fr(2), Fr(75, 32)], "ch13_sh_lambda10.json")
