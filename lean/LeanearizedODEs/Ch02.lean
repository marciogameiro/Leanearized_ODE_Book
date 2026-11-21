module

public import RadiiPolynomial.Problems.FiniteDimZeros
public import LeanearizedODEs.Data.Ch02

/-!
# Examples of Chapter 2

Section 2.4 of the book: zeros of maps `f : ℝⁿ → ℝⁿ` via the finite-dimensional radii polynomial
theorem (Theorem 2.4.2, here `QuadraticSystem.radii_poly_two_radii_exact`), with the sup norm on
`ℝⁿ`. In both examples `f` is quadratic, so `Z₂` is a constant (`r_* = ∞`).

Conventions for the statements:
* the problem (the map `f`, its parameters and its derivative `Df`) is written out explicitly;
  `hasFDerivAt_fPar` and `hasFDerivAt_fLor` prove that `Df` is the derivative of `f`;
* the certificate data (`x̄`, `r₀`, `r₁`, and the approximate inverse `A` for the Lorenz system)
  are named constants from `Examples/Data/Ch02.lean`, generated from
  `code/certificates/ch2_*.json` by `scripts/json_to_lean.py`; the `_eq` lemmas restate the
  decimal values printed in the book as real numbers;
* the theorems have no hypotheses: the matrix `A` and the bounds `Y₀`, `Z₀`, `Z₂` enter only the
  proofs. The bounds are evaluated exactly from the data (`QuadraticSystem.Y0`, `Z0`, `Z2`) and
  the signs of the radii polynomial are checked by the kernel (`decide +kernel`).

* Example 2.4.4 (`ex:2d_example`): the four intersection points of the parabolas
  `4x₁² + x₂ = λ` and `x₁ + x₂² = 1`, `λ = 3` (`parabolas_zero_1`, …, `parabolas_zero_4`).
* Example 2.4.5 (`ex:equilibria_Lorenz`): the equilibrium of the Lorenz system for `σ = 10`,
  `ρ = 28`, `β = 8/3` (`lorenz_equilibrium`).

Each theorem states: there is a nondegenerate zero `x̃` with `‖x̃ - x̄‖ < r₀`, and it is the unique
zero in the closed ball of radius `r₁` about `x̄` (the endpoints of the interval `I` in the book).
-/

@[expose] public section

namespace LeanearizedODEs.Ch02

open RadiiPolynomial
open Metric Matrix QuadraticSystem Ch02Data

/-! ## Example 2.4.4: intersection of two parabolas -/

/-- The parameter `λ = 3`. -/
def lam : ℚ := 3

/-- `f(x) = (4x₁² + x₂ - λ, x₁ + x₂² - 1)` as a quadratic system with rational coefficients. -/
def parabolas : QuadraticSystem ℚ 2 where
  c := ![-lam, -1]
  L := !![0, 1; 1, 0]
  Q := ![![![4, 0], ![0, 0]], ![![0, 0], ![0, 1]]]

/-- The map `f(x) = (4x₁² + x₂ - λ, x₁ + x₂² - 1)` (indices start at `0` in Lean). -/
noncomputable def fPar (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![4 * x 0 ^ 2 + x 1 - lam, x 0 + x 1 ^ 2 - 1]

/-- Its derivative `Df(x) = [[8x₁, 1], [1, 2x₂]]`. -/
noncomputable def DfPar (x : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  matCLM !![8 * x 0, 1; 1, 2 * x 1]

theorem parabolas_eval : (parabolas.map (Rat.castHom ℝ)).eval = fPar := by
  funext x i
  fin_cases i <;> simp [eval, QuadraticSystem.map, parabolas, fPar, Fin.sum_univ_two] <;> ring

theorem parabolas_jac : (fun x => matCLM ((parabolas.map (Rat.castHom ℝ)).jac x)) = DfPar := by
  funext x
  simp only [DfPar]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jac, QuadraticSystem.map, parabolas, Fin.sum_univ_two] <;>
    norm_num

/-- `DfPar x` is the derivative of `fPar` at `x`. -/
theorem hasFDerivAt_fPar (x : Fin 2 → ℝ) : HasFDerivAt fPar (DfPar x) x := by
  have h := (parabolas.map (Rat.castHom ℝ)).hasFDerivAt x
  rwa [parabolas_eval, show matCLM ((parabolas.map (Rat.castHom ℝ)).jac x) = DfPar x from
    congrFun parabolas_jac x] at h

/-- The approximate inverse `A = Df(x̄)⁻¹ = (16x̄₁x̄₂ - 1)⁻¹ [[2x̄₂, -1], [-1, 8x̄₁]]`, computed
exactly from `x̄` (so `Z₀ = 0`). -/
def parabolasA (x : Fin 2 → ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  let d := 16 * x 0 * x 1 - 1
  !![2 * x 1 / d, -1 / d; -1 / d, 8 * x 0 / d]

/-- The finite-dimensional radii polynomial theorem for the parabolas with `A = Df(x̄)⁻¹`. -/
theorem parabolas_zero_of_rat (xbar : Fin 2 → ℚ) {r₀ r₁ : ℚ} (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ r₁)
    (hp₀ : radiiPoly (parabolas.Y0 (parabolasA xbar) xbar) (parabolas.Z0 (parabolasA xbar) xbar) 0
      (parabolas.Z2 (parabolasA xbar)) r₀ < 0)
    (hp₁ : radiiPoly (parabolas.Y0 (parabolasA xbar) xbar) (parabolas.Z0 (parabolasA xbar) xbar) 0
      (parabolas.Z2 (parabolasA xbar)) r₁ < 0) :
    ∃ x ∈ ball (castVec xbar) r₀, IsNondegenerateZero fPar DfPar x ∧
      ∀ y ∈ closedBall (castVec xbar) r₁, fPar y = 0 → y = x := by
  have h := radii_poly_two_radii_exact parabolas (parabolasA xbar) xbar hr₀ hr₀₁ hp₀ hp₁
  rwa [parabolas_eval, parabolas_jac] at h

/-- The zero near `x̄⁽1⁾`. -/
theorem parabolas_zero_1 :
    ∃ x ∈ ball (castVec parabolas_xbar_1) parabolas_r0_1, IsNondegenerateZero fPar DfPar x ∧
      ∀ y ∈ closedBall (castVec parabolas_xbar_1) parabolas_r1_1, fPar y = 0 → y = x :=
  parabolas_zero_of_rat parabolas_xbar_1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem parabolas_xbar_1_eq : castVec parabolas_xbar_1 = ![-0.6545436118927946, 1.286290640521338] := by
  funext i; fin_cases i <;> norm_num [parabolas_xbar_1]

theorem parabolas_r0_1_eq : (parabolas_r0_1 : ℝ) = 3e-16 := by norm_num [parabolas_r0_1]

theorem parabolas_r1_1_eq : (parabolas_r1_1 : ℝ) = 0.640 := by norm_num [parabolas_r1_1]

/-- The zero near `x̄⁽2⁾`. -/
theorem parabolas_zero_2 :
    ∃ x ∈ ball (castVec parabolas_xbar_2) parabolas_r0_2, IsNondegenerateZero fPar DfPar x ∧
      ∀ y ∈ closedBall (castVec parabolas_xbar_2) parabolas_r1_2, fPar y = 0 → y = x :=
  parabolas_zero_of_rat parabolas_xbar_2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem parabolas_xbar_2_eq : castVec parabolas_xbar_2 = ![0.7986333753610425, 0.4487389270377125] := by
  funext i; fin_cases i <;> norm_num [parabolas_xbar_2]

theorem parabolas_r0_2_eq : (parabolas_r0_2 : ℝ) = 6e-16 := by norm_num [parabolas_r0_2]

theorem parabolas_r1_2_eq : (parabolas_r1_2 : ℝ) = 0.227 := by norm_num [parabolas_r1_2]

/-- The zero near `x̄⁽3⁾`. -/
theorem parabolas_zero_3 :
    ∃ x ∈ ball (castVec parabolas_xbar_3) parabolas_r0_3, IsNondegenerateZero fPar DfPar x ∧
      ∀ y ∈ closedBall (castVec parabolas_xbar_3) parabolas_r1_3, fPar y = 0 → y = x :=
  parabolas_zero_of_rat parabolas_xbar_3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem parabolas_xbar_3_eq : castVec parabolas_xbar_3 = ![0.9086121587039679, -0.3023042197787387] := by
  funext i; fin_cases i <;> norm_num [parabolas_xbar_3]

theorem parabolas_r0_3_eq : (parabolas_r0_3 : ℝ) = 1.7e-16 := by norm_num [parabolas_r0_3]

theorem parabolas_r1_3_eq : (parabolas_r1_3 : ℝ) = 0.239 := by norm_num [parabolas_r1_3]

/-- The zero near `x̄⁽4⁾`. -/
theorem parabolas_zero_4 :
    ∃ x ∈ ball (castVec parabolas_xbar_4) parabolas_r0_4, IsNondegenerateZero fPar DfPar x ∧
      ∀ y ∈ closedBall (castVec parabolas_xbar_4) parabolas_r1_4, fPar y = 0 → y = x :=
  parabolas_zero_of_rat parabolas_xbar_4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem parabolas_xbar_4_eq : castVec parabolas_xbar_4 = ![-1.052701922172216, -1.432725347780312] := by
  funext i; fin_cases i <;> norm_num [parabolas_xbar_4]

theorem parabolas_r0_4_eq : (parabolas_r0_4 : ℝ) = 2.2e-16 := by norm_num [parabolas_r0_4]

theorem parabolas_r1_4_eq : (parabolas_r1_4 : ℝ) = 0.927 := by norm_num [parabolas_r1_4]

/-! ## Example 2.4.5: equilibrium of the Lorenz system -/

/-- The parameter `σ = 10`. -/
def σ : ℚ := 10

/-- The parameter `ρ = 28`. -/
def ρ : ℚ := 28

/-- The parameter `β = 8/3`. -/
def β : ℚ := 8 / 3

/-- The Lorenz vector field `f(x) = (σ(x₂ - x₁), ρx₁ - x₂ - x₁x₃, -βx₃ + x₁x₂)` as a quadratic
system with rational coefficients. -/
def lorenz : QuadraticSystem ℚ 3 where
  c := ![0, 0, 0]
  L := !![-σ, σ, 0; ρ, -1, 0; 0, 0, -β]
  Q := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]],
         ![![0, 0, -1], ![0, 0, 0], ![0, 0, 0]],
         ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]]]

/-- The Lorenz vector field (indices start at `0` in Lean). -/
noncomputable def fLor (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![σ * (x 1 - x 0), ρ * x 0 - x 1 - x 0 * x 2, -β * x 2 + x 0 * x 1]

/-- Its derivative `Df(x) = [[-σ, σ, 0], [ρ - x₃, -1, -x₁], [x₂, x₁, -β]]`. -/
noncomputable def DfLor (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  matCLM !![-σ, σ, 0; ρ - x 2, -1, -x 0; x 1, x 0, -β]

theorem lorenz_eval : (lorenz.map (Rat.castHom ℝ)).eval = fLor := by
  funext x i
  fin_cases i <;> simp [eval, QuadraticSystem.map, lorenz, fLor, Fin.sum_univ_three] <;> ring

theorem lorenz_jac : (fun x => matCLM ((lorenz.map (Rat.castHom ℝ)).jac x)) = DfLor := by
  funext x
  simp only [DfLor]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jac, QuadraticSystem.map, lorenz, Fin.sum_univ_three,
      ← sub_eq_add_neg]

/-- `DfLor x` is the derivative of `fLor` at `x`. -/
theorem hasFDerivAt_fLor (x : Fin 3 → ℝ) : HasFDerivAt fLor (DfLor x) x := by
  have h := (lorenz.map (Rat.castHom ℝ)).hasFDerivAt x
  rwa [lorenz_eval, show matCLM ((lorenz.map (Rat.castHom ℝ)).jac x) = DfLor x from
    congrFun lorenz_jac x] at h

/-- The equilibrium of the Lorenz system near `x̄`. (It is `(√72, √72, 27)`.) The bounds are
evaluated exactly; the book prints the upper bounds `Y₀ = 1.86258 × 10⁻⁵`, `Z₀ = 1.2 × 10⁻¹⁴`,
`Z₂ = 0.23570174301439`. -/
theorem lorenz_equilibrium :
    ∃ x ∈ ball (castVec lorenz_xbar) lorenz_r0, IsNondegenerateZero fLor DfLor x ∧
      ∀ y ∈ closedBall (castVec lorenz_xbar) lorenz_r1, fLor y = 0 → y = x := by
  have h := radii_poly_two_radii_exact lorenz lorenz_A lorenz_xbar (r₀ := lorenz_r0)
    (r₁ := lorenz_r1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  rwa [lorenz_eval, lorenz_jac] at h

theorem lorenz_xbar_eq : castVec lorenz_xbar = ![8.4853, 8.4853, 27] := by
  funext i; fin_cases i <;> norm_num [lorenz_xbar]

theorem lorenz_r0_eq : (lorenz_r0 : ℝ) = 1.8626e-5 := by norm_num [lorenz_r0]

theorem lorenz_r1_eq : (lorenz_r1 : ℝ) = 4.2426 := by norm_num [lorenz_r1]

end LeanearizedODEs.Ch02
