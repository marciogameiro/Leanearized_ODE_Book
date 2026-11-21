module

public import RadiiPolynomial.Problems.TaylorCheck
public import LeanearizedODEs.Data.Ch08
public meta import RadiiPolynomial.Problems.TaylorCheck
public meta import LeanearizedODEs.Data.Ch08

/-!
# Examples of Chapter 8

Initial value problems `x' = τ f(x)`, `x(0) = x₀`, solved with Taylor series and the radii
polynomial theorem of Chapter 8 (`TaylorIVP.radii_poly_two_radii`, via the checker
`TaylorData.verify`), with the weight `ν` and the truncation `N` of the book. A solution of the
rescaled problem on `|s| < ν` gives the solution of `x' = f(x)` on `|t| < τ ν` (`t = τ s`).

Conventions: the problem data (vector field, `τ`, initial value) are named definitions written out
next to each theorem; the conclusion is `HasIsolatedZero F ā r₀ r₁`; the certificate data (`ā`,
`A^{(N)}`, `ν`, `N`, `r₀`, `r₁`) are named constants from `Examples/Data/Ch08.lean`, generated from
`code/certificates/ch8_*.json`. All bounds are computed from the data by `TaylorData.check`, which
is evaluated by compiled code (`native_decide`).

Solutions (Lemmas 8.1.1, 8.1.2 and 8.2.1, Theorems 8.1.5 and 8.2.9, via
`TaylorIVP.exists_unique_solution`): each zero gives a solution of the original IVP `x' = f(x)`,
`x(0) = x₀` on `|t| < τ ν`, within `r₀` of the computed Taylor polynomial `x̄(t) = ∑_k ā_k (t/τ)^k`
(`TaySeq.evalAt`) on `|t| ≤ τ ν`, and it is the only
solution of the IVP on `|t| < τ ν` (`scalar_solution_half`, `scalar_solution_quarter`,
`scalar_solution_threeQuarters`, `lorenz_solution`; the ODEs written out).

* Theorem 8.1.5 (`thm:NewtonFx(1-x)`), Section 8.1: `x' = x (x - 1)` with `τ = 1`, `N = 27`,
  `ν = 1` and `x(0) = 1/2` (`scalar_ivp_half`), `1/4` (`scalar_ivp_quarter`), `3/4`
  (`scalar_ivp_threeQuarters`). As in the book, `A^{(N)}` is the exact inverse of `DF^{(N)}(ā)`
  (`TaylorData.withExactInverse`), so `Z₀ = 0`.
* Section 8.3 (`sec:LorenzIVP`): the Lorenz system with `σ = 10`, `ρ = 28`, `β = 8/3`,
  `x(0) = (-8, 8, 27)`, `τ = 1/16`, `N = 40`, `ν = 1` (`lorenz_ivp`).
-/

@[expose] public section

namespace LeanearizedODEs.Ch08

open RadiiPolynomial
open MvPolynomial TaySeq Ch08Data

/-! ## Section 8.1: a scalar IVP -/

/-- `f(x) = x² - x`. -/
def scalarF : PolyData 1 := [⟨1, ![2]⟩, ⟨-1, ![1]⟩]

/-- The certificate of Section 8.1 for the initial value `x₀`, before `A^{(N)}` is computed. -/
def scalarBase (x₀ : ℚ) (abar : List ℚ) (r0 r1 : ℚ) : TaylorData 1 where
  f := ![scalarF]
  τ := 1
  x₀ := ![x₀]
  N := scalar_N
  ν := scalar_nu
  M := 2
  abar := ![abar]
  A := fun _ _ _ _ => 0
  r0 := r0
  r1 := r1

/-- The certificate of Section 8.1 for `x₀ = 1/2`, with `A^{(N)} = DF^{(N)}(ā)⁻¹`. -/
def scalarHalfData : TaylorData 1 :=
  (scalarBase (1 / 2) scalar_abar_half scalar_r0_half scalar_r1_half).withExactInverse

/-- The certificate of Section 8.1 for `x₀ = 1/4`, with `A^{(N)} = DF^{(N)}(ā)⁻¹`. -/
def scalarQuarterData : TaylorData 1 :=
  (scalarBase (1 / 4) scalar_abar_quarter scalar_r0_quarter scalar_r1_quarter).withExactInverse

/-- The certificate of Section 8.1 for `x₀ = 3/4`, with `A^{(N)} = DF^{(N)}(ā)⁻¹`. -/
def scalarThreeQuartersData : TaylorData 1 :=
  (scalarBase (3 / 4) scalar_abar_threeQuarters scalar_r0_threeQuarters
    scalar_r1_threeQuarters).withExactInverse

theorem scalar_half_check : scalarHalfData.check := by native_decide

theorem scalar_quarter_check : scalarQuarterData.check := by native_decide

theorem scalar_threeQuarters_check : scalarThreeQuartersData.check := by native_decide

theorem scalar_nu_pos : (0 : ℝ) < (scalar_nu : ℝ) := by norm_num [scalar_nu]

/-- The field `x(x - 1) = x² - x`. -/
noncomputable def scalarField : Fin 1 → MvPolynomial (Fin 1) ℝ := ![X 0 ^ 2 - X 0]

/-- The time scale `τ = 1`: the solution is obtained on `|t| < τ ν = 1`. -/
noncomputable def scalarTau : ℝ := 1

/-- The initial value `x(0) = 1/2`. -/
noncomputable def scalarInitHalf : Fin 1 → ℝ := ![1 / 2]

/-- The initial value `x(0) = 1/4`. -/
noncomputable def scalarInitQuarter : Fin 1 → ℝ := ![1 / 4]

/-- The initial value `x(0) = 3/4`. -/
noncomputable def scalarInitThreeQuarters : Fin 1 → ℝ := ![3 / 4]

/-- The problem of the certificate is `x' = τ f(x)`, `x(0) = x₀` with the data above. -/
theorem scalarBase_toIVP (x₀ : ℚ) (abar : List ℚ) (r0 r1 : ℚ) :
    (scalarBase x₀ abar r0 r1).toIVP = { f := scalarField, τ := scalarTau, x₀ := ![(x₀ : ℝ)] } := by
  simp only [TaylorData.toIVP, scalarBase, scalarTau]
  congr 1
  · funext j
    fin_cases j
    simp [scalarF, scalarField, PolyData.toMv, PolyData.termToMv_eq]
    ring
  · norm_num
  · funext j; fin_cases j; rfl

theorem scalarHalfData_toIVP :
    scalarHalfData.toIVP = { f := scalarField, τ := scalarTau, x₀ := scalarInitHalf } := by
  rw [scalarHalfData, TaylorData.toIVP_withExactInverse, scalarBase_toIVP, scalarInitHalf]
  norm_num

theorem scalarQuarterData_toIVP :
    scalarQuarterData.toIVP = { f := scalarField, τ := scalarTau, x₀ := scalarInitQuarter } := by
  rw [scalarQuarterData, TaylorData.toIVP_withExactInverse, scalarBase_toIVP, scalarInitQuarter]
  norm_num

theorem scalarThreeQuartersData_toIVP :
    scalarThreeQuartersData.toIVP =
      { f := scalarField, τ := scalarTau, x₀ := scalarInitThreeQuarters } := by
  rw [scalarThreeQuartersData, TaylorData.toIVP_withExactInverse, scalarBase_toIVP,
    scalarInitThreeQuarters]
  norm_num

/-- Theorem 8.1.5, `x(0) = 1/2`: the Taylor IVP-operator of `x' = x (x - 1)` has a zero within `r₀`
of `ā` (in `ℓ¹_ν`, `ν = 1`), unique within `r₁`. -/
theorem scalar_ivp_half :
    HasIsolatedZero
      (TaylorIVP.F { f := scalarField, τ := scalarTau, x₀ := scalarInitHalf } scalar_nu
        scalar_nu_pos)
      (toXVec ![scalar_abar_half]) scalar_r0_half scalar_r1_half := by
  rw [← scalarHalfData_toIVP]
  exact scalarHalfData.verify scalar_nu_pos scalar_half_check

/-- Theorem 8.1.5, `x(0) = 1/4`. -/
theorem scalar_ivp_quarter :
    HasIsolatedZero
      (TaylorIVP.F { f := scalarField, τ := scalarTau, x₀ := scalarInitQuarter } scalar_nu
        scalar_nu_pos)
      (toXVec ![scalar_abar_quarter]) scalar_r0_quarter scalar_r1_quarter := by
  rw [← scalarQuarterData_toIVP]
  exact scalarQuarterData.verify scalar_nu_pos scalar_quarter_check

/-- Theorem 8.1.5, `x(0) = 3/4`. -/
theorem scalar_ivp_threeQuarters :
    HasIsolatedZero
      (TaylorIVP.F { f := scalarField, τ := scalarTau, x₀ := scalarInitThreeQuarters } scalar_nu
        scalar_nu_pos)
      (toXVec ![scalar_abar_threeQuarters]) scalar_r0_threeQuarters scalar_r1_threeQuarters := by
  rw [← scalarThreeQuartersData_toIVP]
  exact scalarThreeQuartersData.verify scalar_nu_pos scalar_threeQuarters_check

/-! ### The solutions (Lemmas 8.1.1 and 8.1.2) -/

/-- A zero of the operator of Section 8.1 near `ā` gives a solution of `x' = x (x - 1)`,
`x(0) = x₀` on `|t| < 1`, continuous on `[-1, 1]`, within `r₀` of the Taylor polynomial
`x̄(t) = ∑_k ā_k t^k` for `|t| ≤ 1`, and it is the only solution of this IVP on `|t| < 1`. -/
theorem scalar_solution_of {x₀ : Fin 1 → ℝ} {abar : List ℚ} {r₀ r₁ : ℝ}
    (h : HasIsolatedZero (TaylorIVP.F { f := scalarField, τ := scalarTau, x₀ := x₀ } scalar_nu
      scalar_nu_pos) (toXVec ![abar]) r₀ r₁) :
    ∃ x : ℝ → ℝ, x 0 = x₀ 0 ∧ (∀ t, |t| < 1 → HasDerivAt x (x t * (x t - 1)) t) ∧
      (∀ t, |t| ≤ 1 → |x t - evalAt abar t| < r₀) ∧ ContinuousOn x (Set.Icc (-1) 1) ∧
      ∀ y : ℝ → ℝ, y 0 = x₀ 0 → (∀ t, |t| < 1 → HasDerivAt y (y t * (y t - 1)) t) →
        ∀ t, |t| < 1 → y t = x t := by
  have hτ : (0 : ℝ) < scalarTau := by norm_num [scalarTau]
  have hτν : scalarTau * (scalar_nu : ℝ) = 1 := by norm_num [scalarTau, scalar_nu]
  obtain ⟨x, hx0, hxd, hxe, hxc, hxu⟩ := TaylorIVP.exists_unique_solution h hτ
  simp only [hτν] at hxd hxe hxc hxu
  have hfield : ∀ z : Fin 1 → ℝ, MvPolynomial.eval z (scalarField 0) = z 0 * (z 0 - 1) := by
    intro z; simp [scalarField]; ring
  refine ⟨fun t => x t 0, by simp only [hx0], fun t ht => ?_, fun t ht => ?_,
    continuousOn_pi.1 hxc 0, fun y hy0 hyd t ht => ?_⟩
  · have := (hasDerivAt_pi.1 (hxd t ht)) 0
    rwa [hfield] at this
  · have := hxe t ht 0
    rwa [show t / scalarTau = t by norm_num [scalarTau], toXVec, Matrix.cons_val_zero,
      tsum_toX_mul_pow] at this
  · have hY := hxu (fun s _ => y s) (by funext i; rw [Subsingleton.elim i 0]; exact hy0)
      (fun s hs => hasDerivAt_pi.2 fun i => by
        rw [Subsingleton.elim i 0]
        simpa only [hfield] using hyd s hs) t ht
    exact congrFun hY 0

/-- Section 8.1, `x(0) = 1/2`: `x' = x (x - 1)`, `x(0) = 1/2` has a solution on `|t| < 1`, within
`r₀ = 2.72 · 10⁻¹⁵` of `x̄(t) = ∑_{k ≤ 27} ā_k t^k` on `|t| ≤ 1` (where it is continuous), and it is
the only solution of
this IVP on `|t| < 1`; explicitly, `x(t) = 1/(1 + e^t)` on `|t| < 1`. -/
theorem scalar_solution_half :
    ∃ x : ℝ → ℝ, x 0 = 1 / 2 ∧ (∀ t, |t| < 1 → HasDerivAt x (x t * (x t - 1)) t) ∧
      (∀ t, |t| ≤ 1 → |x t - evalAt scalar_abar_half t| < scalar_r0_half) ∧
      ContinuousOn x (Set.Icc (-1) 1) ∧
      (∀ y : ℝ → ℝ, y 0 = 1 / 2 → (∀ t, |t| < 1 → HasDerivAt y (y t * (y t - 1)) t) →
        ∀ t, |t| < 1 → y t = x t) ∧
      ∀ t, |t| < 1 → x t = 1 / (1 + Real.exp t) := by
  obtain ⟨x, h0, hd, he, hc, hu⟩ := scalar_solution_of scalar_ivp_half
  have h0' : x 0 = 1 / 2 := by simpa [scalarInitHalf] using h0
  have hu' : ∀ y : ℝ → ℝ, y 0 = 1 / 2 → (∀ t, |t| < 1 → HasDerivAt y (y t * (y t - 1)) t) →
      ∀ t, |t| < 1 → y t = x t := fun y hy0 => hu y (by simpa [scalarInitHalf] using hy0)
  refine ⟨x, h0', hd, he, hc, hu', fun t ht => (hu' (fun s => 1 / (1 + Real.exp s)) (by norm_num) (fun s _ => ?_) t ht).symm⟩
  have hpos : (1 + Real.exp s) ≠ 0 := (add_pos one_pos (Real.exp_pos s)).ne'
  have h := ((Real.hasDerivAt_exp s).const_add 1).inv hpos
  simp only [one_div]
  convert h using 1
  field_simp
  ring

/-- Section 8.1, `x(0) = 1/4`. -/
theorem scalar_solution_quarter :
    ∃ x : ℝ → ℝ, x 0 = 1 / 4 ∧ (∀ t, |t| < 1 → HasDerivAt x (x t * (x t - 1)) t) ∧
      (∀ t, |t| ≤ 1 → |x t - evalAt scalar_abar_quarter t| < scalar_r0_quarter) ∧
      ContinuousOn x (Set.Icc (-1) 1) ∧
      ∀ y : ℝ → ℝ, y 0 = 1 / 4 → (∀ t, |t| < 1 → HasDerivAt y (y t * (y t - 1)) t) →
        ∀ t, |t| < 1 → y t = x t := by
  simpa [scalarInitQuarter] using scalar_solution_of scalar_ivp_quarter

/-- Section 8.1, `x(0) = 3/4`. -/
theorem scalar_solution_threeQuarters :
    ∃ x : ℝ → ℝ, x 0 = 3 / 4 ∧ (∀ t, |t| < 1 → HasDerivAt x (x t * (x t - 1)) t) ∧
      (∀ t, |t| ≤ 1 → |x t - evalAt scalar_abar_threeQuarters t| < scalar_r0_threeQuarters) ∧
      ContinuousOn x (Set.Icc (-1) 1) ∧
      ∀ y : ℝ → ℝ, y 0 = 3 / 4 → (∀ t, |t| < 1 → HasDerivAt y (y t * (y t - 1)) t) →
        ∀ t, |t| < 1 → y t = x t := by
  simpa [scalarInitThreeQuarters] using scalar_solution_of scalar_ivp_threeQuarters

/-! ## Section 8.3: the Lorenz IVP -/

/-- The Lorenz vector field `(10 (y - x), 28 x - y - x z, x y - (8/3) z)`. -/
def lorenzF : Fin 3 → PolyData 3 :=
  ![[⟨10, ![0, 1, 0]⟩, ⟨-10, ![1, 0, 0]⟩],
    [⟨28, ![1, 0, 0]⟩, ⟨-1, ![0, 1, 0]⟩, ⟨-1, ![1, 0, 1]⟩],
    [⟨1, ![1, 1, 0]⟩, ⟨-8 / 3, ![0, 0, 1]⟩]]

/-- The certificate of Section 8.3. -/
def lorenzData : TaylorData 3 where
  f := lorenzF
  τ := 1 / 16
  x₀ := ![-8, 8, 27]
  N := lorenz_N
  ν := lorenz_nu
  M := 2
  abar := lorenz_abar
  A := fun j m i l =>
    (lorenz_A.getD (j.val * (lorenz_N + 1) + m) #[]).getD (i.val * (lorenz_N + 1) + l) 0
  r0 := lorenz_r0
  r1 := lorenz_r1

theorem lorenz_check : lorenzData.check := by native_decide

theorem lorenz_nu_pos : (0 : ℝ) < (lorenz_nu : ℝ) := by norm_num [lorenz_nu]

/-- The Lorenz field with `σ = 10`, `ρ = 28`, `β = 8/3`. -/
noncomputable def lorenzField : Fin 3 → MvPolynomial (Fin 3) ℝ :=
  ![10 * (X 1 - X 0), 28 * X 0 - X 1 - X 0 * X 2, X 0 * X 1 - C (8 / 3) * X 2]

/-- The time scale `τ = 1/16`: the solution is obtained on `|t| < τ ν = 1/16`. -/
noncomputable def lorenzTau : ℝ := 1 / 16

/-- The initial value `x(0) = (-8, 8, 27)`. -/
noncomputable def lorenzInit : Fin 3 → ℝ := ![-8, 8, 27]

/-- The problem of the certificate is `x' = τ f(x)`, `x(0) = x₀` with the data above. -/
theorem lorenzData_toIVP :
    lorenzData.toIVP = { f := lorenzField, τ := lorenzTau, x₀ := lorenzInit } := by
  simp only [TaylorData.toIVP, lorenzData, lorenzTau, lorenzInit]
  congr 1
  · have h83 : (C (-8 / 3 : ℝ) : MvPolynomial (Fin 3) ℝ) = -C (8 / 3) := by
      rw [neg_div, map_neg]
    funext j
    fin_cases j <;> simp [lorenzF, lorenzField, PolyData.toMv, PolyData.termToMv_eq,
      Fin.prod_univ_three, map_neg, map_ofNat, h83] <;> ring
  · norm_num
  · funext j; fin_cases j <;> norm_num

/-- Section 8.3: the Taylor IVP-operator of the Lorenz system, `x(0) = (-8, 8, 27)`, `τ = 1/16`,
has a zero within `r₀` of `ā` (in `(ℓ¹_ν)³`, `ν = 1`), unique within `r₁`. -/
theorem lorenz_ivp :
    HasIsolatedZero
      (TaylorIVP.F { f := lorenzField, τ := lorenzTau, x₀ := lorenzInit } lorenz_nu lorenz_nu_pos)
      (toXVec lorenz_abar) lorenz_r0 lorenz_r1 := by
  rw [← lorenzData_toIVP]
  exact lorenzData.verify lorenz_nu_pos lorenz_check

/-- The Lorenz field `(10 (y - x), 28 x - y - x z, x y - (8/3) z)`, written out. -/
theorem lorenzField_eval (z : Fin 3 → ℝ) :
    (fun j => MvPolynomial.eval z (lorenzField j)) =
      ![10 * (z 1 - z 0), 28 * z 0 - z 1 - z 0 * z 2, z 0 * z 1 - 8 / 3 * z 2] := by
  funext j
  fin_cases j <;> simp [lorenzField]

/-- Section 8.3 (Lemmas 8.1.2 and 8.2.1, Theorem 8.2.9): the Lorenz system
`x' = (10 (y - x), 28 x - y - x z, x y - (8/3) z)`, `x(0) = (-8, 8, 27)`, has a solution on
`|t| < 1/16`, within `r₀ = 3.86 · 10⁻¹⁵` (in each component) of
`x̄_j(t) = ∑_{k ≤ 40} ā_{j,k} (16 t)^k` on `|t| ≤ 1/16`, continuous on `[-1/16, 1/16]`, with
`x(1/16) ∈ (-0.9207563767, 6.6760434433, 21.1618426942) + [-10⁻¹⁰, 10⁻¹⁰]³` (from the exact value
`x̄(1/16) = ∑_k ā_{j,k}`), and it is the only solution of this IVP on `|t| < 1/16`. -/
theorem lorenz_solution :
    ∃ x : ℝ → Fin 3 → ℝ, x 0 = ![-8, 8, 27] ∧
      (∀ t, |t| < 1 / 16 → HasDerivAt x
        ![10 * (x t 1 - x t 0), 28 * x t 0 - x t 1 - x t 0 * x t 2,
          x t 0 * x t 1 - 8 / 3 * x t 2] t) ∧
      (∀ t, |t| ≤ 1 / 16 → ∀ j, |x t j - evalAt (lorenz_abar j) (16 * t)| < lorenz_r0) ∧
      ContinuousOn x (Set.Icc (-(1 / 16)) (1 / 16)) ∧
      (∀ j, |x (1 / 16) j - ![-0.9207563767, 6.6760434433, 21.1618426942] j| ≤ 1 / 10 ^ 10) ∧
      ∀ y : ℝ → Fin 3 → ℝ, y 0 = ![-8, 8, 27] →
        (∀ t, |t| < 1 / 16 → HasDerivAt y
          ![10 * (y t 1 - y t 0), 28 * y t 0 - y t 1 - y t 0 * y t 2,
            y t 0 * y t 1 - 8 / 3 * y t 2] t) →
        ∀ t, |t| < 1 / 16 → y t = x t := by
  have hτ : (0 : ℝ) < lorenzTau := by norm_num [lorenzTau]
  have hτν : lorenzTau * (lorenz_nu : ℝ) = 1 / 16 := by norm_num [lorenzTau, lorenz_nu]
  have hinit : lorenzInit = ![-8, 8, 27] := by funext j; fin_cases j <;> rfl
  obtain ⟨x, hx0, hxd, hxe, hxc, hxu⟩ := TaylorIVP.exists_unique_solution lorenz_ivp hτ
  simp only [hτν, lorenzField_eval] at hxd hxe hxc hxu
  have hxe' : ∀ t, |t| ≤ 1 / 16 → ∀ j, |x t j - evalAt (lorenz_abar j) (16 * t)| < lorenz_r0 :=
    fun t ht j => by
      have := hxe t ht j
      rwa [show t / lorenzTau = 16 * t by rw [lorenzTau]; ring, toXVec, tsum_toX_mul_pow] at this
  have hval : ∀ j, |x (1 / 16) j - evalQ 1 (lorenz_abar j)| < lorenz_r0 := fun j => by
    have h := hxe' (1 / 16) (by norm_num [abs_of_pos]) j
    rwa [show (16 * (1 / 16 : ℝ)) = ((1 : ℚ) : ℝ) by norm_num, evalAt_ratCast] at h
  refine ⟨x, by rw [hx0]; exact hinit, hxd, hxe', hxc, fun j => ?_, fun y hy0 hyd t ht =>
    hxu y (hy0.trans hinit.symm) hyd t ht⟩
  fin_cases j
  · have := abs_sub_le_of_approx (hval 0) (c := -0.9207563767) (δ := 1 / 10 ^ 10) (by native_decide)
    simpa using this
  · have := abs_sub_le_of_approx (hval 1) (c := 6.6760434433) (δ := 1 / 10 ^ 10) (by native_decide)
    simpa using this
  · have := abs_sub_le_of_approx (hval 2) (c := 21.1618426942) (δ := 1 / 10 ^ 10) (by native_decide)
    simpa using this

end LeanearizedODEs.Ch08
