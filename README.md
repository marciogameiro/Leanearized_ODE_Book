# Leanearized_ODE_Book

The Lean 4 formalization of the computer-assisted proofs of the book *Ordinary Differential
Equations: A Constructive Approach*. The proofs are based on the radii polynomial approach; they
are checked in Lean with the library `RadiiPolynomial` (developed separately). The repository also
contains the Python programs and the certificates of the book's computer-assisted proofs.

## Contents

| Folder | Contents |
|---|---|
| `book_radii_polynomials/code/` | Python programs that carry out and check the computer-assisted proofs of the book, in exact rational arithmetic (standard library only) |
| `book_radii_polynomials/code/certificates/` | One JSON certificate per example |
| `lean/` | The Lean 4 proofs of the book's results and computer-assisted examples |

## The computer-assisted proofs

Run the programs from `book_radii_polynomials/code/` with Python 3:

| Chapter | Program | Certificates |
|---|---|---|
| 2. Existence of Zeros of Functions | `finite_dim_examples.py` | `ch2_parabolas.json`, `ch2_lorenz_equilibrium.json` |
| 8. Taylor Methods | `taylor_ivp.py` | `ch8_scalar.json`, `ch8_lorenz.json` |
| 10. Periodic Orbits | `periodic_orbits.py` | `ch10_helmholtz.json`, `ch10_hopf.json`, `ch10_lorenz_LR.json` |
| 13. Boundary Value Problems via Fourier Series | `swift_hohenberg.py` | `ch13_sh_lambda1.json`, `ch13_sh_lambda10.json` |
| 14. Initial Value Problems via Chebyshev Series; 15. Boundary Value Problems and Connecting Orbits | `examples.py` (with `chebyshev_rp.py`) | `ch14_scalar.json`, `ch14_lorenz.json`, `ch15_chafee_infante.json` |

For example:

```bash
cd book_radii_polynomials/code
python3 taylor_ivp.py
```

Each program prints the bounds `Y0`, `Z0`, `Z1`, `Z2` and the radii `r0`, `r1` stated in the
book, and checks in exact arithmetic that the radii polynomial is negative at `r0` and `r1`.

### Certificates

A certificate records only the *data* of a proof: the problem parameters, the truncation
data, the approximate solution, the approximate inverse (when it is not given by a formula)
and the radii. The bounds are not stored; every checker recomputes them from the data.

Every number in a certificate is a JSON decimal that denotes *exactly* the rational number
written (not the nearest binary double); a parameter that is not a terminating decimal, such
as `8/3`, is stored as the string `"8/3"`. `code/certificate.py` reads certificates exactly.

## The Lean formalization (`lean/`)

`lean/` is a Lean 4 project (`LeanearizedODEs`, Lean and Mathlib `v4.35.0`) that checks the
computer-assisted proofs of the book with the library `RadiiPolynomial`.

* `LeanearizedODEs/ChNN.lean`: one theorem per example of Chapter NN, with the problem written
  out and the conclusions of the book: existence and uniqueness of the zero, the solution of the
  differential equation, error bounds, and the numerical claims of the text.
* `LeanearizedODEs/Data/ChNN.lean`: the certificate data, generated from
  `book_radii_polynomials/code/certificates/` by `scripts/json_to_lean.py` (do not edit by hand).
* `BOOK_MAP.md`: every numbered result of the book (Chapters 2, 7, 8, 10, 13, 14, 15) with the Lean
  declarations proving it.
* `PLAN.md`: the plan and the decisions of the formalization.

`lean/lakefile.toml` requires the library as a git dependency
(`github.com/marciogameiro/RadiiPolynomial`, branch `master`); the commit used is pinned in
`lean/lake-manifest.json`. To build:

```bash
cd lean
lake exe cache get   # Mathlib build cache
lake build
```

To use a newer version of the library, run `lake update RadiiPolynomial` in `lean/`.

The large examples are checked by compiled code (`native_decide`); the Chapter 2 examples and the
Hopf point by the Lean kernel alone.

## License

Released under the MIT License; see [`LICENSE`](LICENSE).
