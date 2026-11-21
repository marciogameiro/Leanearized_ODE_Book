"""Certificates for the computer-assisted proofs.

A certificate is a JSON file that records the DATA of one example: the problem parameters,
the truncation data, the approximate solution abar, the approximate inverse A^{(N)} (when it
is not given by a formula), and the radii r0 <= r1 that are claimed. The bounds Y0, Z0, Z1, Z2
are NOT stored: they are functions of the data and are recomputed by every checker (the
scripts in this directory, and the Lean library RadiiPolynomial, where they are evaluated
exactly by the kernel).

Number convention. Every number is a JSON number written as a decimal (for instance
8.4853 or -1.86258e-05), and it denotes EXACTLY the rational number written, not the
nearest binary double. To read a certificate exactly use `read` below (or, in any language,
parse the decimal text as an exact rational). A parameter that is not a terminating decimal
(such as beta = 8/3) is stored as a string "p/q".

The data are rounded to decimals before the bounds are computed, so the bounds are those of
the stored data. Both the approximate solution abar and the approximate inverse A keep 17
significant digits, enough to reproduce their double precision values (full precision).
Since the radii polynomial theorems hold for ANY abar and A, rounding affects only the size
of the bounds, not the validity of the proof.
"""
import json
from decimal import Decimal
from fractions import Fraction

A_DIGITS = 17          # significant digits kept for approximate inverses (full double precision)
ABAR_DIGITS = 17       # significant digits kept for approximate solutions


def decimal(x, digits=ABAR_DIGITS):
    """Round x (float or rational) to `digits` significant decimal digits, as an exact rational."""
    x = Fraction(x)
    if x == 0:
        return Fraction(0)
    return Fraction(f"{Decimal(x.numerator) / Decimal(x.denominator):.{digits - 1}e}")


def decimal_seq(xs, digits=ABAR_DIGITS):
    return [decimal(x, digits) for x in xs]


def decimal_matrix(rows, digits=A_DIGITS):
    return [decimal_seq(row, digits) for row in rows]


def decimal_text(x):
    """The exact decimal text of a rational with a terminating decimal expansion, else None."""
    x = Fraction(x)
    if x.denominator == 1:
        return str(x.numerator)
    d, k2, k5 = x.denominator, 0, 0
    while d % 2 == 0:
        d //= 2
        k2 += 1
    while d % 5 == 0:
        d //= 5
        k5 += 1
    if d != 1:
        return None
    short = repr(float(x))                    # Python's shortest form, if it is exact
    if Fraction(short) == x:
        return short
    k = max(k2, k5)
    return format(Decimal(x.numerator * 10 ** k // x.denominator).scaleb(-k).normalize(), "e")


class _Exact(float):
    """A float subclass carrying exact decimal text, so that json writes it verbatim."""

    def __new__(cls, text):
        obj = super().__new__(cls, float(Fraction(text)))
        obj.text = text
        return obj

    def __repr__(self):
        return self.text


def encode(obj):
    """Recursively turn rationals into exact JSON numbers (or "p/q" strings)."""
    if isinstance(obj, (Fraction, int)) and not isinstance(obj, bool):
        t = decimal_text(obj)
        if t is None:
            x = Fraction(obj)
            return f"{x.numerator}/{x.denominator}"
        return int(t) if Fraction(obj).denominator == 1 else _Exact(t)
    if isinstance(obj, float):
        raise TypeError("store rationals (e.g. via decimal()), not floats")
    if isinstance(obj, dict):
        return {k: encode(v) for k, v in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [encode(v) for v in obj]
    return obj


def _dumps(obj, indent=1, level=0):
    """JSON text; floats are written with their exact decimal text."""
    pad, pad1 = " " * (indent * level), " " * (indent * (level + 1))
    if isinstance(obj, dict):
        if not obj:
            return "{}"
        items = [f"{pad1}{json.dumps(k)}: {_dumps(v, indent, level + 1)}" for k, v in obj.items()]
        return "{\n" + ",\n".join(items) + "\n" + pad + "}"
    if isinstance(obj, list):
        if all(not isinstance(v, (dict, list)) for v in obj):
            return "[" + ", ".join(_dumps(v) for v in obj) + "]"
        return "[\n" + ",\n".join(pad1 + _dumps(v, indent, level + 1) for v in obj) + "\n" + pad + "]"
    if isinstance(obj, _Exact):
        return obj.text
    return json.dumps(obj)


def write(path, cert):
    with open(path, "w") as fh:
        fh.write(_dumps(encode(cert)) + "\n")


def read(path):
    """Read a certificate; every number becomes an exact Fraction ("p/q" strings stay strings)."""
    with open(path) as fh:
        return json.load(fh, parse_float=Fraction, parse_int=Fraction)


def read_rational(s):
    return Fraction(s)
