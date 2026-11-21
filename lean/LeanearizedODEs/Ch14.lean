module

public import RadiiPolynomial.Problems.ChebyshevIVP
public import RadiiPolynomial.Problems.ChebyshevCheck
public import RadiiPolynomial.Problems.ChebyshevSolution
public import LeanearizedODEs.Data.Ch14
public meta import RadiiPolynomial.Problems.ChebyshevCheck
public meta import LeanearizedODEs.Data.Ch14

/-!
# Examples of Chapter 14

Initial value problems `u' = L f(u)`, `u(-1) = x₀` on `[-1, 1]`, solved with Chebyshev series and
the radii polynomial theorem of Section 14.4 (`ChebBVP.radii_poly_two_radii`, via the checker
`ChebData.verify`), with the weight `ν` and the truncation `N` of the book.

Conventions: the problem data (vector field, `L`, initial condition) are named definitions written
out next to each theorem; the conclusion is `HasIsolatedZero F ā r₀ r₁`; the certificate data (`ā`,
`A^{(N)}`, `ν`, `N`, `r₀`, `r₁`) are named constants from `Examples/Data/Ch14.lean`, generated from
`code/certificates/ch14_*.json`. All bounds are computed from the data by `ChebData.check`, which is
evaluated by compiled code (`native_decide`).

* Example 14.5.1 (`ex:cheb_scalar_IVP`): `x' = x (x - 1)`, `x(0) = 1/2` on `τ ∈ [0, 2]`, i.e.
  `u' = u² - u`, `u(-1) = 1/2` (`L = 1`) (`scalar_ivp`).
* Example 14.5.2 (`ex:cheb_Lorenz_IVP`): the Lorenz system with `σ = 10`, `ρ = 28`, `β = 8/3`,
  `x(0) = (-8, 8, 27)` on `τ ∈ [0, 1/4]`, i.e. `u' = (1/8) f(u)`, `u(-1) = x(0)` (`lorenz_ivp`).

The solutions (Lemma 14.3.2, via `ChebBVP.exists_ivp_solution`): the zero gives a solution
`x(τ) = u(τ/L - 1)` of the IVP on `[0, 2L]` (one-sided derivatives at the endpoints) within `r₀` of
`ū(τ/L - 1)`, `ū = ā_0 + 2 ∑_k ā_k T_k` (`evalSeries`), and every solution on `[0, 2L]` coincides
with it (`scalar_solution`, `lorenz_solution`). The enclosure of `x(1/4)` evaluates `ū(1)` exactly
(`ChebSeq.evalT`, the recurrence for `T_k`) and adds `r₀`.
-/

@[expose] public section

namespace LeanearizedODEs.Ch14

open RadiiPolynomial
open MvPolynomial ChebSeq Ch14Data

/-! ## Example 14.5.1: a scalar IVP -/

/-- `f(x) = x² - x`. -/
def scalarF : PolyData 1 := [⟨1, ![2]⟩, ⟨-1, ![1]⟩]

/-- The certificate of Example 14.5.1. -/
def scalarData : ChebData 1 where
  f := ![scalarF]
  L := 1
  Bm := fun _ _ => 1
  Bp := fun _ _ => 0
  q := fun _ => 1 / 2
  N := scalar_N
  ν := scalar_nu
  M := 2
  abar := scalar_abar
  A := fun j m i l =>
    (scalar_A.getD (j.val * (scalar_N + 1) + m) #[]).getD (i.val * (scalar_N + 1) + l) 0
  r0 := scalar_r0
  r1 := scalar_r1

theorem scalar_check : scalarData.check := by native_decide

theorem one_le_scalar_nu : (1 : ℝ) ≤ (scalar_nu : ℝ) := by norm_num [scalar_nu]

/-- The field `x² - x`. -/
noncomputable def scalarField : Fin 1 → MvPolynomial (Fin 1) ℝ := ![X 0 ^ 2 - X 0]

/-- The time scale: `t = L (τ + 1)`, `τ ∈ [-1, 1]`, so the IVP is solved on `[0, 2]`. -/
noncomputable def scalarL : ℝ := 1

/-- The initial value `x(0) = 1/2`. -/
noncomputable def scalarInit : Fin 1 → ℝ := ![1 / 2]

/-- The problem of the certificate is `u' = L f(u)`, `u(-1) = x₀` with the data above. -/
theorem scalarData_toBVP :
    scalarData.toBVP = ChebBVP.ivp scalarField scalarL scalarInit := by
  simp only [ChebData.toBVP, ChebBVP.ivp, scalarData, scalarF, scalarL, scalarInit]
  congr 1
  · funext j
    fin_cases j
    simp [scalarField, PolyData.toMv, PolyData.termToMv_eq]
    ring
  · norm_num
  · funext j i; rw [Subsingleton.elim j i, Matrix.one_apply_eq]; norm_num
  · funext j i; simp
  · funext j; fin_cases j; norm_num

/-- Example 14.5.1: the Chebyshev IVP-operator of `x' = x² - x`, `x(0) = 1/2` on `[0, 2]` has a
zero within `r₀` of `ā` (in `X_ν`, `ν = 1.1`), unique within `r₁`. -/
theorem scalar_ivp :
    HasIsolatedZero
      ((ChebBVP.ivp scalarField scalarL scalarInit).F scalar_nu one_le_scalar_nu)
      (toXVec scalar_abar) scalar_r0 scalar_r1 := by
  rw [← scalarData_toBVP]
  exact scalarData.verify one_le_scalar_nu scalar_check

/-- Example 14.5.1: `x' = x² - x`, `x(0) = 1/2` has a solution on `[0, 2]` within `r₀` of
`ū(τ - 1)`, and every solution on `[0, 2]` coincides with it. -/
theorem scalar_solution :
    ∃ x : ℝ → ℝ, x 0 = 1 / 2 ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 2, HasDerivWithinAt x (x τ ^ 2 - x τ) (Set.Icc 0 2) τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 2, |x τ - evalSeries (scalar_abar 0) (τ - 1)| < scalar_r0) ∧
      ∀ y : ℝ → ℝ, y 0 = 1 / 2 →
        (∀ τ ∈ Set.Icc (0 : ℝ) 2, HasDerivWithinAt y (y τ ^ 2 - y τ) (Set.Icc 0 2) τ) →
        Set.EqOn y x (Set.Icc 0 2) := by
  have hL : (0 : ℝ) < scalarL := by norm_num [scalarL]
  have h2L : 2 * scalarL = 2 := by norm_num [scalarL]
  have hτL : ∀ τ : ℝ, τ / scalarL - 1 = τ - 1 := fun τ => by norm_num [scalarL]
  obtain ⟨a, -, -, x, hx0, -, hxd, hxe, hxu⟩ := ChebBVP.exists_ivp_solution hL scalar_ivp
  simp only [h2L, hτL, toXVec, chebSeries_toX] at hxd hxe hxu
  have hfield : ∀ z : Fin 1 → ℝ, MvPolynomial.eval z (scalarField 0) = z 0 ^ 2 - z 0 := by
    intro z; simp [scalarField]
  refine ⟨fun t => x t 0, by simp [hx0, scalarInit], fun τ hτ => ?_, fun τ hτ => hxe τ hτ 0,
    fun y hy0 hyd τ hτ => ?_⟩
  · have := (hasDerivWithinAt_pi.1 (hxd τ hτ)) 0
    rwa [hfield] at this
  · have hY := hxu (fun s _ => y s) (by funext i; rw [Subsingleton.elim i 0]; simpa [scalarInit] using hy0)
      (fun s hs => hasDerivWithinAt_pi.2 fun i => by
        rw [Subsingleton.elim i 0]
        simpa only [hfield] using hyd s hs) hτ
    exact congrFun hY 0

/-! ## Example 14.5.2: the Lorenz IVP -/

/-- The Lorenz vector field `(10 (y - x), 28 x - y - x z, x y - (8/3) z)`. -/
def lorenzF : Fin 3 → PolyData 3 :=
  ![[⟨10, ![0, 1, 0]⟩, ⟨-10, ![1, 0, 0]⟩],
    [⟨28, ![1, 0, 0]⟩, ⟨-1, ![0, 1, 0]⟩, ⟨-1, ![1, 0, 1]⟩],
    [⟨1, ![1, 1, 0]⟩, ⟨-8 / 3, ![0, 0, 1]⟩]]

/-- The certificate of Example 14.5.2. -/
def lorenzData : ChebData 3 where
  f := lorenzF
  L := 1 / 8
  Bm := fun j i => if j = i then 1 else 0
  Bp := fun _ _ => 0
  q := ![-8, 8, 27]
  N := lorenz_N
  ν := lorenz_nu
  M := 2
  abar := lorenz_abar
  A := fun j m i l =>
    (lorenz_A.getD (j.val * (lorenz_N + 1) + m) #[]).getD (i.val * (lorenz_N + 1) + l) 0
  r0 := lorenz_r0
  r1 := lorenz_r1

theorem lorenz_check : lorenzData.check := by native_decide

theorem one_le_lorenz_nu : (1 : ℝ) ≤ (lorenz_nu : ℝ) := by norm_num [lorenz_nu]

/-- The Lorenz field with `σ = 10`, `ρ = 28`, `β = 8/3`. -/
noncomputable def lorenzField : Fin 3 → MvPolynomial (Fin 3) ℝ :=
  ![10 * (X 1 - X 0), 28 * X 0 - X 1 - X 0 * X 2, X 0 * X 1 - C (8 / 3) * X 2]

/-- The time scale: `t = L (τ + 1)`, `τ ∈ [-1, 1]`, so the IVP is solved on `[0, 2L] = [0, 1/4]`. -/
noncomputable def lorenzL : ℝ := 1 / 8

/-- The initial value `x(0) = (-8, 8, 27)`. -/
noncomputable def lorenzInit : Fin 3 → ℝ := ![-8, 8, 27]

/-- The problem of the certificate is `u' = L f(u)`, `u(-1) = x₀` with the data above. -/
theorem lorenzData_toBVP :
    lorenzData.toBVP = ChebBVP.ivp lorenzField lorenzL lorenzInit := by
  simp only [ChebData.toBVP, ChebBVP.ivp, lorenzData, lorenzL, lorenzInit]
  congr 1
  · have h83 : (C (-8 / 3 : ℝ) : MvPolynomial (Fin 3) ℝ) = -C (8 / 3) := by
      rw [neg_div, map_neg]
    funext j
    fin_cases j <;> simp [lorenzF, lorenzField, PolyData.toMv, PolyData.termToMv_eq,
      Fin.prod_univ_three, map_neg, map_ofNat, h83] <;> ring
  · norm_num
  · funext j i; rw [Matrix.one_apply]; split_ifs <;> simp
  · funext j i; simp
  · funext j; fin_cases j <;> norm_num

/-- Example 14.5.2: the Chebyshev IVP-operator of the Lorenz system, `x(0) = (-8, 8, 27)` on
`[0, 1/4]`, has a zero within `r₀` of `ā` (in `X_ν³`, `ν = 3/2`), unique within `r₁`. -/
theorem lorenz_ivp :
    HasIsolatedZero
      ((ChebBVP.ivp lorenzField lorenzL lorenzInit).F lorenz_nu one_le_lorenz_nu)
      (toXVec lorenz_abar) lorenz_r0 lorenz_r1 := by
  rw [← lorenzData_toBVP]
  exact lorenzData.verify one_le_lorenz_nu lorenz_check

theorem lorenzField_eval (z : Fin 3 → ℝ) :
    (fun j => MvPolynomial.eval z (lorenzField j)) =
      ![10 * (z 1 - z 0), 28 * z 0 - z 1 - z 0 * z 2, z 0 * z 1 - 8 / 3 * z 2] := by
  funext j
  fin_cases j <;> simp [lorenzField]

/-- Example 14.5.2: the Lorenz IVP `x(0) = (-8, 8, 27)` has a solution on `[0, 1/4]` within `r₀` of
`ū(8τ - 1)`, with `x(1/4) ∈ (7.6272480715, 12.2520965592, 18.4544351142) + [-10⁻¹⁰, 10⁻¹⁰]³`, and every
solution on `[0, 1/4]` coincides with it. -/
theorem lorenz_solution :
    ∃ x : ℝ → Fin 3 → ℝ, x 0 = ![-8, 8, 27] ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) (1 / 4), HasDerivWithinAt x
        ![10 * (x τ 1 - x τ 0), 28 * x τ 0 - x τ 1 - x τ 0 * x τ 2,
          x τ 0 * x τ 1 - 8 / 3 * x τ 2] (Set.Icc 0 (1 / 4)) τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) (1 / 4), ∀ j,
        |x τ j - evalSeries (lorenz_abar j) (8 * τ - 1)| < lorenz_r0) ∧
      (∀ j, |x (1 / 4) j - ![7.6272480715, 12.2520965592, 18.4544351142] j| ≤ 1 / 10 ^ 10) ∧
      ∀ y : ℝ → Fin 3 → ℝ, y 0 = ![-8, 8, 27] →
        (∀ τ ∈ Set.Icc (0 : ℝ) (1 / 4), HasDerivWithinAt y
          ![10 * (y τ 1 - y τ 0), 28 * y τ 0 - y τ 1 - y τ 0 * y τ 2,
            y τ 0 * y τ 1 - 8 / 3 * y τ 2] (Set.Icc 0 (1 / 4)) τ) →
        Set.EqOn y x (Set.Icc 0 (1 / 4)) := by
  have hL : (0 : ℝ) < lorenzL := by norm_num [lorenzL]
  have h2L : 2 * lorenzL = 1 / 4 := by norm_num [lorenzL]
  have hτL : ∀ τ : ℝ, τ / lorenzL - 1 = 8 * τ - 1 := fun τ => by rw [lorenzL]; ring
  have hinit : lorenzInit = ![-8, 8, 27] := by funext j; fin_cases j <;> rfl
  obtain ⟨a, -, -, x, hx0, -, hxd, hxe, hxu⟩ := ChebBVP.exists_ivp_solution hL lorenz_ivp
  simp only [h2L, hτL, toXVec, chebSeries_toX, lorenzField_eval] at hxd hxe hxu
  have hval : ∀ j, |x (1 / 4) j - evalT 1 (lorenz_abar j)| < lorenz_r0 := fun j => by
    have h := hxe (1 / 4) ⟨by norm_num, le_rfl⟩ j
    rwa [show (8 * (1 / 4 : ℝ) - 1) = ((1 : ℚ) : ℝ) by norm_num, evalSeries_ratCast] at h
  refine ⟨x, hx0.trans hinit, hxd, hxe, fun j => ?_,
    fun y hy0 hyd => hxu y (hy0.trans hinit.symm) hyd⟩
  fin_cases j
  · have := abs_sub_le_of_approx (hval 0) (c := 7.6272480715) (δ := 1 / 10 ^ 10) (by native_decide)
    simpa using this
  · have := abs_sub_le_of_approx (hval 1) (c := 12.2520965592) (δ := 1 / 10 ^ 10) (by native_decide)
    simpa using this
  · have := abs_sub_le_of_approx (hval 2) (c := 18.4544351142) (δ := 1 / 10 ^ 10) (by native_decide)
    simpa using this

end LeanearizedODEs.Ch14
