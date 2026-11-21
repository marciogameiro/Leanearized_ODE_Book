module

public import RadiiPolynomial.Problems.ChebyshevCheck
public import RadiiPolynomial.Problems.ChebyshevSolution
public import LeanearizedODEs.Data.Ch15
public meta import RadiiPolynomial.Problems.ChebyshevCheck
public meta import LeanearizedODEs.Data.Ch15

/-!
# Examples of Chapter 15

* Example 15.1.3 (`ex:cheb_BVP_Chafee_Infante`): equilibria of the Chafee-Infante equation,
  `u'' + λ u (1 - u²) = 0`, `u(-1) = u(1) = 0`, `λ = 4`, as the first-order boundary value problem
  `u₁' = u₂`, `u₂' = λ u₁³ - λ u₁` (`L = 1`) with `B₋ = [[1, 0], [0, 0]]`, `B₊ = [[0, 0], [1, 0]]`,
  `q = 0` (`chafee_infante_bvp`). The zero gives a solution `u` of the BVP on `[-1, 1]` (Lemma 15.1.1,
  via `ChebBVP.exists_solution`) within `r₀` of `ū = ā_0 + 2 ∑_k ā_k T_k` (`evalSeries`), whose
  Chebyshev coefficients form the unique zero within `r₁`, with the enclosures of `u₁(0)` and `u₁'(-1)`
  obtained by evaluating `ū` exactly (`ChebSeq.evalT`) (`chafee_infante_solution`).

The problem data (vector field, `L`, `B₋`, `B₊`, `q`) are named definitions written out next to the
theorem; the conclusion is `HasIsolatedZero F ā r₀ r₁`; the certificate data (`ā`, `A^{(N)}`, `ν`,
`N`, `r₀`, `r₁`) are named constants from `Examples/Data/Ch15.lean`, generated from
`code/certificates/ch15_chafee_infante.json`. All bounds of Theorem 15.1.2 are computed from the
data by `ChebData.check`, evaluated by compiled code (`native_decide`).
-/

@[expose] public section

namespace LeanearizedODEs.Ch15

open RadiiPolynomial
open MvPolynomial ChebSeq Ch15Data

/-- The vector field `(u₂, 4 u₁³ - 4 u₁)` (`λ = 4`). -/
def chafeeF : Fin 2 → PolyData 2 :=
  ![[⟨1, ![0, 1]⟩], [⟨-4, ![1, 0]⟩, ⟨4, ![3, 0]⟩]]

/-- The certificate of Example 15.1.3. -/
def chafeeData : ChebData 2 where
  f := chafeeF
  L := 1
  Bm := ![![1, 0], ![0, 0]]
  Bp := ![![0, 0], ![1, 0]]
  q := ![0, 0]
  N := chafee_N
  ν := chafee_nu
  M := 3
  abar := chafee_abar
  A := fun j m i l =>
    (chafee_A.getD (j.val * (chafee_N + 1) + m) #[]).getD (i.val * (chafee_N + 1) + l) 0
  r0 := chafee_r0
  r1 := chafee_r1

theorem chafee_check : chafeeData.check := by native_decide

theorem one_le_chafee_nu : (1 : ℝ) ≤ (chafee_nu : ℝ) := by norm_num [chafee_nu]

/-- The field `(u₂, λ u₁³ - λ u₁)` with `λ = 4`. -/
noncomputable def chafeeField : Fin 2 → MvPolynomial (Fin 2) ℝ := ![X 1, 4 * X 0 ^ 3 - 4 * X 0]

/-- The time scale: the BVP is posed on `[-1, 1]`. -/
noncomputable def chafeeL : ℝ := 1

/-- The boundary conditions `B₋ u(-1) + B₊ u(1) = q`, i.e. `u₁(-1) = 0`, `u₁(1) = 0`: `B₋`. -/
noncomputable def chafeeBm : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- The boundary conditions: `B₊`. -/
noncomputable def chafeeBp : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- The boundary conditions: `q`. -/
noncomputable def chafeeQ : Fin 2 → ℝ := ![0, 0]

/-- The problem of the certificate is the BVP with the data above. -/
theorem chafeeData_toBVP :
    chafeeData.toBVP =
      { f := chafeeField, L := chafeeL, Bm := chafeeBm, Bp := chafeeBp, q := chafeeQ } := by
  simp only [ChebData.toBVP, chafeeData, chafeeL, chafeeBm, chafeeBp, chafeeQ]
  congr 1
  · funext j
    fin_cases j <;> simp [chafeeF, chafeeField, PolyData.toMv, PolyData.termToMv_eq,
      Fin.prod_univ_two, map_neg, map_ofNat]; ring
  · norm_num
  · funext j i; fin_cases j <;> fin_cases i <;> simp
  · funext j i; fin_cases j <;> fin_cases i <;> simp
  · funext j; fin_cases j <;> simp

/-- Example 15.1.3: the Chebyshev BVP-operator of the Chafee-Infante problem has a zero within `r₀`
of `ā` (in `X_ν²`, `ν = 1.2`), unique within `r₁`. -/
theorem chafee_infante_bvp :
    HasIsolatedZero
      (ChebBVP.F { f := chafeeField, L := chafeeL, Bm := chafeeBm, Bp := chafeeBp, q := chafeeQ }
        chafee_nu one_le_chafee_nu)
      (toXVec chafee_abar) chafee_r0 chafee_r1 := by
  rw [← chafeeData_toBVP]
  exact chafeeData.verify one_le_chafee_nu chafee_check

/-- Example 15.1.3: the Chafee-Infante BVP `u₁' = u₂`, `u₂' = 4 u₁³ - 4 u₁`, `u₁(-1) = u₁(1) = 0`
has a solution `u` on `[-1, 1]` (one-sided derivatives at the endpoints) within `r₀` of `ū`; its
Chebyshev coefficients form the unique zero of the BVP-operator within `r₁` of `ā`. Moreover
`u₁(0) ∈ 0.7059325447 + [-10⁻¹⁰, 10⁻¹⁰]` and `u₁'(-1) = u₂(-1) ∈ 1.2233871052 + [-10⁻¹⁰, 10⁻¹⁰]`, so
that `u` is not the trivial solution. -/
theorem chafee_infante_solution :
    ∃ a : Fin 2 → Chebyshev.X chafee_nu one_le_chafee_nu,
      ChebBVP.F { f := chafeeField, L := chafeeL, Bm := chafeeBm, Bp := chafeeBp, q := chafeeQ }
        chafee_nu one_le_chafee_nu a = 0 ∧
      (∀ b ∈ Metric.closedBall (toXVec chafee_abar) chafee_r1,
        ChebBVP.F { f := chafeeField, L := chafeeL, Bm := chafeeBm, Bp := chafeeBp, q := chafeeQ }
          chafee_nu one_le_chafee_nu b = 0 → b = a) ∧
      ∃ u : ℝ → Fin 2 → ℝ, (∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ j, u t j = Chebyshev.chebSeries (a j) t) ∧
        (∀ t ∈ Set.Icc (-1 : ℝ) 1,
          HasDerivWithinAt u ![u t 1, 4 * u t 0 ^ 3 - 4 * u t 0] (Set.Icc (-1) 1) t) ∧
        u (-1) 0 = 0 ∧ u 1 0 = 0 ∧
        (∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ j, |u t j - evalSeries (chafee_abar j) t| < chafee_r0) ∧
        |u 0 0 - 0.7059325447| ≤ 1 / 10 ^ 10 ∧ |u (-1) 1 - 1.2233871052| ≤ 1 / 10 ^ 10 ∧
        u 0 0 ≠ 0 := by
  obtain ⟨a, hFa, huniq, u, hu, hud, hbc, herr⟩ := ChebBVP.exists_solution _ chafee_infante_bvp
  have hfield : ∀ z : Fin 2 → ℝ, (fun j => chafeeL * MvPolynomial.eval z (chafeeField j)) =
      ![z 1, 4 * z 0 ^ 3 - 4 * z 0] := fun z => by
    funext j
    fin_cases j <;> simp [chafeeField, chafeeL]
  have h0 := congrFun hbc 0
  have h1 := congrFun hbc 1
  simp [chafeeBm, chafeeBp, chafeeQ, dotProduct, Fin.sum_univ_two] at h0 h1
  simp only [hfield] at hud
  simp only [toXVec, chebSeries_toX] at herr
  have e0 : |u 0 0 - evalT 0 (chafee_abar 0)| < chafee_r0 := by
    have h := herr ((0 : ℚ) : ℝ) (by norm_num) 0
    rwa [evalSeries_ratCast, Rat.cast_zero] at h
  have e1 : |u (-1) 1 - evalT (-1) (chafee_abar 1)| < chafee_r0 := by
    have h := herr ((-1 : ℚ) : ℝ) (by norm_num) 1
    rwa [evalSeries_ratCast, Rat.cast_neg, Rat.cast_one] at h
  have v0 : |u 0 0 - 0.7059325447| ≤ 1 / 10 ^ 10 := by
    have := abs_sub_le_of_approx e0 (c := 0.7059325447) (δ := 1 / 10 ^ 10) (by native_decide)
    simpa using this
  have v1 : |u (-1) 1 - 1.2233871052| ≤ 1 / 10 ^ 10 := by
    have := abs_sub_le_of_approx e1 (c := 1.2233871052) (δ := 1 / 10 ^ 10) (by native_decide)
    simpa using this
  refine ⟨a, hFa, huniq, u, hu, hud, h0, h1, herr, v0, v1, fun h => ?_⟩
  rw [h, zero_sub, abs_neg] at v0
  norm_num at v0

end LeanearizedODEs.Ch15
