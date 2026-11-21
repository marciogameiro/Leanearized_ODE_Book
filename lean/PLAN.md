# RadiiPolynomial — Lean 4 formalization plan

Formalization in Lean 4 (Lean v4.35.0, Mathlib v4.35.0) of the radii polynomial theorems and the
computer-assisted examples of the book in `LeanearizedODEs/book_radii_polynomials/` (Chapters 2, 7, 8,
10, 13, 14, 15). `BOOK_MAP.md` maps every numbered result of the book to its Lean declaration(s).

## Status (2026-10-25)

The existence layers (an isolated zero of `F` near `ā`) and the interpretation layers (the zero is a
solution of the differential equation, with error bounds, uniqueness and the numerical claims of the
example texts) are complete for all chapters, and so is the general theory of Chapter 7 including
Young's inequality (Theorem 7.4.8: `Convolution.convLp`, `summable_fiber_Lp`, `norm_convLp_le`). No `sorry`; the axioms are `propext`, `Classical.choice`,
`Quot.sound` and, for the examples checked by compiled code, the `native_decide` axioms
(`<name>._native.native_decide.ax_…`). The book has been edited so that it states what Lean proves.

| Ch | Problem class (library, Problems/) | Examples (book project, LeanearizedODEs/ChNN) | Check |
|---|---|---|---|
| 2 | `FiniteDimZeros` (`QuadraticSystem`) | four parabola intersections, Lorenz equilibrium | kernel (`decide +kernel`) |
| 8 | `TaylorIVP` (+ Radii, Check) | scalar x' = x(x−1), x₀ ∈ {1/2, 1/4, 3/4}; Lorenz, τ = 1/16 | `native_decide` |
| 10 | `QuadraticFourier`, `FourierPeriodic` (+ Radii, Check, Solution) | Helmholtz–Duffing; Lorenz LR orbit; Hopf point (finite-dim.) | `native_decide`; Hopf: kernel |
| 13 | `CubicCosine` (+ Radii, Check, Solution) | Swift–Hohenberg, Table 13.1 (λ = 1, 10; four ν each) | `native_decide` |
| 14 | `ChebBVP.ivp` (Chebyshev, + Radii, Check, Solution) | scalar x' = x² − x; Lorenz on [0, 1/4] | `native_decide` |
| 15 | `ChebBVP` | Chafee–Infante BVP | `native_decide` |

What the example theorems state (no hypotheses; problem data written out, certificate data by name):
* existence of the zero within `r₀` of `ā`, unique within `r₁` (`HasIsolatedZero F ā r₀ r₁`);
* the solution: the ODE (or PDE equilibrium equation) written out, the error bound `< r₀` for all times,
  uniqueness — among all solutions on the interval for the IVPs (Ch 8, 14), at the level of coefficients
  for the BVP, the periodic orbits and the equilibria (Ch 10, 13, 15); reality, periodicity, minimal
  period (LR), symmetry, regularity as in the book;
* the numerical consequences printed in the example texts (point enclosures ±10⁻¹⁰, the LR period
  interval, nontriviality, the eigenvalues at the Hopf point, the coincidence of the Ch 13 zeros for
  different ν), by exact rational evaluation of the approximate solution and `abs_sub_le_of_approx`.

Build: `lake build` in `LeanearizedODEs/lean/` (fetches and builds the library as a git dependency); ≈ 5–7 min from scratch (LeanearizedODEs/Data/Ch10 ≈ 3 min, LeanearizedODEs/Ch10 ≈ 4–6 min with the
LR check); no warnings (all files are Lean modules since 2026-10-24).

## Remaining work

None. When the library repository is made public, change the dependency URL to HTTPS (see "Split").

## Deferred (possible later work)

* Uniqueness in function space for the BVP (Ch 15), periodic orbits (Ch 10) and equilibria (Ch 13):
  needs the converse correspondence (solution ⇒ coefficient sequence in ℓ¹_ν). Uniqueness of the zero of
  `F` within `r₁` is proved, and so is uniqueness among all solutions for the IVPs.
* A kernel-oriented checker (plain lists, integers, no recomputation) so that the large examples need
  only the kernel instead of `native_decide`.
* An interval backend (`Certificate/Interval`, e.g. LeanCert), only if transcendental enclosures are
  needed (π is handled by Mathlib's 20-digit bounds).

## Not formalized (by design)

* Classical results cited by the book: the Hopf bifurcation theorem (10.4.1), Definition 10.4.2 and
  Theorem 10.4.3 (its eigenvalue part is proved for the example, `Ch10.hopf_point_eigenvalues`).
* Results Mathlib provides: the book keeps the statement with "available in Mathlib" (14 entries
  "Mathlib (statement only)" in BOOK_MAP).
* Remarks 7.6.3 and 13.1.7 (the convexity remark), and the phrase "converges uniformly" in Lemmas
  14.2.2(ii) and 14.2.4 (the sup bound, continuity and the integral identity are proved).

## Decisions

| Topic | Decision |
|---|---|
| Library name | `RadiiPolynomial` |
| Comments | No references to the book in the library `RadiiPolynomial`; book references only in the book project (`LeanearizedODEs/ChNN.lean`, BOOK_MAP.md) (decided 2026-10-22). |
| Radii polynomial theorems | Only those the examples use: `radii_poly` (single radius) and `radii_poly_two_radii` (decided 2026-10-22). |
| Layers | Existence layer first, interpretation layer (zero of F ⇒ solution) afterwards, in `Problems/*Solution.lean` (both done). |
| Book and Lean | The book states what Lean proves: results proved in Lean are stated in the book, and claims of the book are either formalized or reworded (user rule, 2026-10-24). |
| Uniqueness | IVPs: uniqueness among all solutions on the interval (Grönwall); BVP, periodic orbits, equilibria: uniqueness of the zero within r₁ (user decision, 2026-10-24). |
| ℓ^p | Weighted ℓ^p_{ω,I} defined by transport from Mathlib's `lp` via a ↦ (ω_k a_k); norm/space/completeness by transport; ℓ¹ formula `‖a‖ = ∑' k, ω k * ‖a k‖`. |
| Book proofs | Do not formalize proofs that Mathlib provides (the book says "available in Mathlib"); proofs not used by the formalization were removed from the book (pruning pass approved 2026-10-22). |
| Arithmetic | Exact arithmetic (rationals). One checker per problem class with two trust modes: `decide +kernel` (trust: kernel only) for Ch 2 and the Hopf point; `native_decide` (also trusts the compiler and runtime) for all other examples, including the Chebyshev ones (the kernel check of the Ch 14 scalar example did not finish in 20 min; user decision 2026-10-23). |
| Certificates | JSON stores DATA ONLY (parameters, truncation, x̄/ā, A when numerical, radii r₀ r₁); every number is a JSON decimal denoting exactly the decimal written (non-decimal parameters as "p/q" strings); ā and A to 17 significant digits (full double precision). Bounds are NOT stored: Lean evaluates them exactly from the data (computable bound functions in Problems/, proved to be bounds) and checks only p(r₀) < 0, p(r₁) < 0 (decided 2026-10-22). |
| Example statements | No hypotheses; the problem (map, parameters, derivative) written out; certificate data (x̄, r₀, r₁) referenced by name from the generated `LeanearizedODEs/Data/ChNN.lean`; every piece of problem data (vector field, `L`, initial value, `B₋`, `B₊`, `q`, …) is a named definition with a docstring just above the theorem (2026-10-22/23). |
| Data encoding in Lean | Generated data files use one decimal literal per number (`List ℚ`, `Array`); elaboration costs ≈ 2.5 ms per literal (Data/Ch10, 3 MB, builds once in ≈ 3 min). Packing rows into natural-number literals remains an option if needed. Large intermediate results are computed once per check (tables `fast`, proved equal to `direct`). |
| Performance | In compiled/interpreted checks avoid `Finset` membership tests in hot loops (use `natAbs` comparisons): the LR check went from > 10 min to ≈ 3 min. |
| Lean modules | Every file is a module (2026-10-24): `module`, `public import …`, and `@[expose] public section` after the module docstring, so all declarations and definition bodies stay visible to importers (needed for `rfl`, `decide +kernel` and unfolding). An example file that uses `native_decide` also has `public meta import` of its checker module(s) and its data module, so that the code is available at compile time. Generated data files are written in this form by `scripts/json_to_lean.py`. |
| Layer check | `scripts/check_layers.py` in the library, run by the library's pre-commit hook (`scripts/hooks/pre-commit`, enabled by `git config core.hooksPath scripts/hooks`). |
| LeanCert | Not used (see "Deferred"). |
| External code | Do not use or consult the RadiiPolynomial repository of arXiv 2610.02335 (github.com/IlPreteRosso/RadiiPolynomial). |
| Lean/Mathlib | Lean v4.35.0, Mathlib v4.35.0. |

## Organization

Two Lean projects (split 2026-10-24):

```
ODE_Book_Formalization/
  RadiiPolynomial/             the library (own repository; see its README.md for the layers)
    RadiiPolynomial/
      WeightedLp/   WeightedLp (`WeightedLp 𝕜 ω p` via Mathlib lp), WeightedL1, Operators (column-norm bounds)
      Convolution/  Basic (Banach algebra ℓ¹_{ω,I}), Instances (ℕ, ℤ), Symmetric, Character, PowerSeries,
                    Taylor, Chebyshev, ChebyshevSeries, Cosine, Fourier, FourierSeries, Young
      Calculus/     Polynomial (derivatives, Lipschitz bounds), ODE (uniqueness via Grönwall)
      Abstract/     RadiiPoly (`radii_poly`, `radii_poly_two_radii`, `HasIsolatedZero`), Injectivity,
                    FiniteDim
      BlockTail/    FiniteTail (finite block + diagonal tail), ParamTail (extra scalar unknown)
      Certificate/  Exact, Polynomial, FinSeq, TaylorSeq, ChebyshevSeq, CosineSeq, Complex, FourierSeq
      Problems/     per problem class: operator, `*Radii`, `*Check`, `*Solution`
    scripts/check_layers.py    checks the allowed imports between layers
  LeanearizedODEs/             the book repository
    book_radii_polynomials/    the book (Chapter_N.tex/.pdf, figures/, code/, code/certificates/)
    lean/                      the book's proofs (Lean project `LeanearizedODEs`)
      LeanearizedODEs/ChNN.lean        one theorem per example of Chapter NN (namespace LeanearizedODEs.ChNN)
      LeanearizedODEs/Data/ChNN.lean   certificate data (generated)
      scripts/json_to_lean.py          code/certificates/*.json → LeanearizedODEs/Data/ChNN.lean
      BOOK_MAP.md, PLAN.md
```

Layer rule (library): the general part (WeightedLp, Convolution, Calculus) imports Mathlib only;
`python3 scripts/check_layers.py` checks all layers. Problems = reusable framework per problem class;
the book project contains only concrete instances (data + application). New ODEs in an existing class
need only a new example.

## Split: library + book (done 2026-10-24)

* The library `RadiiPolynomial` is its own Lean project and repository
  (github.com/marciogameiro/RadiiPolynomial, branch `master`; private for now).
* The book's proofs are the Lean project `lean/` in the book repository `LeanearizedODEs`, with
  `require RadiiPolynomial` as a git dependency (`git@github.com:marciogameiro/RadiiPolynomial.git`,
  `rev = "master"`; the commit is pinned in `lake-manifest.json`, Mathlib is inherited from the
  library) (2026-10-25). Before that, a path dependency on the sibling checkout with a shared
  `packagesDir`.
* A library change reaches the book project after it is pushed and `lake update RadiiPolynomial` is run
  in `lean/` (this also fetches the Mathlib cache).
* The SSH URL works only with access to the private repository; when the library is made public,
  change it to `https://github.com/marciogameiro/RadiiPolynomial` and run `lake update RadiiPolynomial`.
* Rules: the library never refers to the book; example-specific helpers stay in the book project;
  certificate conventions and generators live with the book (`lean/scripts/`).

## Backend-independent bounds (LeanCert-ready)

Problem theorems take bound hypotheses as REAL inequalities on finite-dimensional quantities
(e.g. `colNorm (1 - A * DF) ≤ (Z0 : ℝ)`), never a Boolean check. Certification backends produce those
inequalities: `Certificate/Exact` (ℚ + `decide`) now, `Certificate/Interval` (LeanCert, trust := kernel
by default) later. Computable code is kernel-friendly: structural recursion, integer arithmetic, no Float.

## History

1. Setup, BOOK_MAP (2026-10-22). 2. Abstract/ and the Chapter 2 examples (kernel decide). 3. Certificate
performance test: decimal literals ≈ 2.5 ms each; kernel ≈ 7 s at 31×31, > 6 min at 93×93 → kernel for
small, `native_decide` for large examples. 4. WeightedLp/, Convolution/, Calculus/ (2026-10-22).
5. Existence layers (2026-10-22 to 10-23), each as operator F → bound theorem → checker → examples:
Ch 14–15 (one Chebyshev BVP framework, IVP as a special case), Ch 8 (Taylor), Ch 13 (Swift–Hohenberg; the
cosine space has no ring structure, products via the Chebyshev algebra), Ch 10 (Hopf point; Helmholtz–Duffing
with exact complex arithmetic `QC`; Lorenz LR orbit, 214 × 214 complex A). All bounds reproduce the book's.
6. Interpretation layers (2026-10-24):
* I1, I1b Ch 8: power series solution, uniqueness via Grönwall (new book Lemma 8.1.2).
* I2 Ch 10: evaluation at characters, Fourier series and derivatives, reality via conjugation symmetry.
* I3 Ch 13: cosine series, Σ k⁴|a_k| < ∞ from the equation, C⁴ equilibria (Remark 13.1.8).
* I4 Ch 14–15: Chebyshev series via θ = arccos t and the Fourier series of the symmetric extension,
  endpoints by one-sided limits of the derivative, integration (Lemma 14.2.4), BVP (Lemma 15.1.1), IVP with
  uniqueness on [0, 2L] (Lemma 14.3.2; book updated).
* I5: the numerical claims of the example texts; Taylor solution continuous on the closed interval;
  Fourier coefficients (new book Lemma 10.5.3) and the minimal period of LR; coincidence of the Ch 13 zeros
  for different ν (inclusion ℓ¹_ν ⊂ ℓ¹_ν'); Hopf eigenvalues via the characteristic polynomial. Book
  reworded where the original argument was not the one formalized (Ch 8, 10, 13).
7. Split into library and book project, layer check with pre-commit hook, conversion of all files to
   Lean modules (2026-10-24). Library on GitHub, book project switched to a git dependency (2026-10-25).
8. Young's inequality (2026-10-24): Hölder on each fiber (Mathlib's `Real.inner_le_Lp_mul_Lq_tsum_of_nonneg`),
   injectivity of (i, j) ↦ j on a fiber (cancellative monoid), regrouping over I × I; no countability needed.

## decide vs native_decide (for reference)

- `decide`: the kernel evaluates the decision procedure by reduction; trusted base = kernel only; slow
  (natural-number arithmetic is GMP-accelerated, the rest is symbolic). `decide +kernel` skips the
  elaborator pre-check.
- `native_decide`: compiles and runs the procedure natively, accepted via the axiom `Lean.ofReduceBool`;
  also trusts compiler/runtime/implemented_by; much faster; visible in `#print axioms`.
- LeanCert exposes the same choice (`trust := native | kernel | auto`, default native).
