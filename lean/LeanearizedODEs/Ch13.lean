module

public import RadiiPolynomial.Problems.CubicCosineCheck
public import RadiiPolynomial.Problems.CubicCosineSolution
public import LeanearizedODEs.Data.Ch13
public meta import RadiiPolynomial.Problems.CubicCosineCheck
public meta import LeanearizedODEs.Data.Ch13

/-!
# Examples of Chapter 13

Equilibria of the Swift–Hohenberg equation `u_t = (λ - 1) u - 2 u_yy - u_yyyy - u³` with even,
`2π/L`-periodic boundary conditions, `L = 13/20`, as zeros of `F(a)_k = μ_k a_k - (a³)_k` in
`ℓ¹_ν`, `μ_k = λ - (1 - k² L²)²` (Section 13.1), proved with Theorem 13.1.6
(`CubicCosine.radii_poly_two_radii`, via the checker `CubicCosineData.verify`).

Conventions: the problem data (`λ`, `L`, the eigenvalues `μ_k`) are named definitions written out
next to the theorems; the conclusion is `HasIsolatedZero F ā r₀ r₁`; the certificate data (`ā`,
`A_m`, `m`, `ν`, `r₀`, `r₁`) are named constants from `Examples/Data/Ch13.lean`, generated from
`code/certificates/ch13_sh_lambda*.json`. All bounds are computed from the data by
`CubicCosineData.check`, which is evaluated by compiled code (`native_decide`); the tail condition
`|μ_k| ≥ |μ_m|` (`k ≥ m`) is Lemma 13.1.3 (`sh_tail`).

Equilibria (Remark 13.1.8): each zero `ã` gives an even, `2π/L`-periodic `C⁴` equilibrium
`u(y) = ã_0 + 2 ∑_k ã_k cos(kLy)` of the equation (`SHEquilibrium`) with `|u(y) - ū(y)| < 2 r₀`
(`sh_lambda1_nu1_equilibrium`, …, via `CubicCosine.exists_equilibrium`).

Conclusions (Section 13.1.3): for each `λ` the zeros for the four weights have the same coefficients
(`CubicCosine.coeff_eq_of_isolatedZero`), and the equilibrium satisfies the sup bound and the
enclosure of `u(0)` (exact value of `ū(0)`, `shU0`), hence is nontrivial (`sh_lambda1_conclusions`,
`sh_lambda10_conclusions`).

The eight theorems are the eight rows of Table 13.1: `λ = 1`, `m = 18`, `ν ∈ {1, 2, 4, 5}`
(`sh_lambda1_nu1`, …) and `λ = 10`, `m = 31`, `ν ∈ {1, 3/2, 2, 75/32}` (`sh_lambda10_nu1`, …).
-/

@[expose] public section

namespace LeanearizedODEs.Ch13

open RadiiPolynomial
open CosSeq Ch13Data

/-! ## Lemma 13.1.3: the tail condition -/

/-- Lemma 13.1.3: if `m L ≥ 1` and `μ_m < 0`, where `μ_k = λ - (1 - k² L²)²`, then
`|μ_k| ≥ |μ_m|` for all `k ≥ m`. -/
theorem sh_tail (lam L : ℚ) {m k : ℕ} (hL : 0 ≤ L) (hmL : 1 ≤ m * L)
    (hμ : lam - (1 - (m : ℚ) ^ 2 * L ^ 2) ^ 2 < 0) (hk : m ≤ k) :
    |lam - (1 - (m : ℚ) ^ 2 * L ^ 2) ^ 2| ≤ |lam - (1 - (k : ℚ) ^ 2 * L ^ 2) ^ 2| := by
  have hmk : (m : ℚ) * L ≤ k * L := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hL
  have h1 : 0 ≤ (m : ℚ) ^ 2 * L ^ 2 - 1 := by nlinarith
  have h2 : (m : ℚ) ^ 2 * L ^ 2 - 1 ≤ (k : ℚ) ^ 2 * L ^ 2 - 1 := by nlinarith
  have hsq : (1 - (m : ℚ) ^ 2 * L ^ 2) ^ 2 ≤ (1 - (k : ℚ) ^ 2 * L ^ 2) ^ 2 := by nlinarith
  rw [abs_of_neg hμ, abs_of_neg (by linarith)]
  linarith

/-! ## The problem -/

/-- The fundamental wave number `L = 13/20`. -/
noncomputable def shL : ℝ := 13 / 20

/-- The parameter `λ = 1`. -/
noncomputable def shLambda1 : ℝ := 1

/-- The parameter `λ = 10`. -/
noncomputable def shLambda10 : ℝ := 10

/-- The eigenvalues `μ_k = λ - (1 - k² L²)²` of the linear part. -/
noncomputable def shMu (lam L : ℝ) (k : ℕ) : ℝ := lam - (1 - (k : ℝ) ^ 2 * L ^ 2) ^ 2

/-- The eigenvalues with rational `λ` and `L = 13/20`, for the checker. -/
def shMuQ (lam : ℚ) (k : ℕ) : ℚ := lam - (1 - (k : ℚ) ^ 2 * (13 / 20) ^ 2) ^ 2

/-! ## λ = 1 (`m = 18`) -/

/-- The certificate for `λ = 1` with weight `ν` and radii `r₀`, `r₁`. -/
def sh1Data (ν r0 r1 : ℚ) : CubicCosineData where
  μ := shMuQ 1
  m := sh1_m
  ν := ν
  abar := sh1_abar
  A k l := (sh1_A.getD k #[]).getD l 0
  r0 := r0
  r1 := r1

/-- The tail condition for `λ = 1` (Lemma 13.1.3). -/
theorem sh1_tail (ν r0 r1 : ℚ) (k : ℕ) (hk : (sh1Data ν r0 r1).m ≤ k) :
    |(sh1Data ν r0 r1).μ (sh1Data ν r0 r1).m| ≤ |(sh1Data ν r0 r1).μ k| :=
  sh_tail 1 (13 / 20) (by norm_num) (by norm_num [sh1Data, sh1_m])
    (by norm_num [sh1Data, sh1_m]) hk

/-- The problem of the certificate: eigenvalues `μ_k = λ - (1 - k² L²)²`, `λ = 1`, `L = 13/20`. -/
theorem sh1Data_toProblem (ν r0 r1 : ℚ) :
    (sh1Data ν r0 r1).toProblem = { μ := shMu shLambda1 shL } := by
  simp only [CubicCosineData.toProblem, sh1Data, shMuQ, shLambda1, shL]
  congr 1
  funext k
  rw [shMu]
  push_cast
  ring

theorem sh1_check_1 : (sh1Data sh1_nu_1 sh1_r0_1 sh1_r1_1).check := by native_decide

theorem one_le_sh1_nu_1 : (1 : ℝ) ≤ (sh1_nu_1 : ℝ) := by norm_num [sh1_nu_1]

/-- Table 13.1, `λ = 1`, `ν = 1`: `F` has a zero within `r₀` of `ā` in `ℓ¹_ν`, unique
within `r₁`. -/
theorem sh_lambda1_nu1 :
    HasIsolatedZero
      (CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_1 one_le_sh1_nu_1)
      (toX sh1_abar) sh1_r0_1 sh1_r1_1 := by
  rw [← sh1Data_toProblem sh1_nu_1 sh1_r0_1 sh1_r1_1]
  exact (sh1Data sh1_nu_1 sh1_r0_1 sh1_r1_1).verify one_le_sh1_nu_1
    (sh1_tail _ _ _) sh1_check_1

theorem sh1_check_2 : (sh1Data sh1_nu_2 sh1_r0_2 sh1_r1_2).check := by native_decide

theorem one_le_sh1_nu_2 : (1 : ℝ) ≤ (sh1_nu_2 : ℝ) := by norm_num [sh1_nu_2]

/-- Table 13.1, `λ = 1`, `ν = 2`: `F` has a zero within `r₀` of `ā` in `ℓ¹_ν`, unique
within `r₁`. -/
theorem sh_lambda1_nu2 :
    HasIsolatedZero
      (CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_2 one_le_sh1_nu_2)
      (toX sh1_abar) sh1_r0_2 sh1_r1_2 := by
  rw [← sh1Data_toProblem sh1_nu_2 sh1_r0_2 sh1_r1_2]
  exact (sh1Data sh1_nu_2 sh1_r0_2 sh1_r1_2).verify one_le_sh1_nu_2
    (sh1_tail _ _ _) sh1_check_2

theorem sh1_check_3 : (sh1Data sh1_nu_3 sh1_r0_3 sh1_r1_3).check := by native_decide

theorem one_le_sh1_nu_3 : (1 : ℝ) ≤ (sh1_nu_3 : ℝ) := by norm_num [sh1_nu_3]

/-- Table 13.1, `λ = 1`, `ν = 4`: `F` has a zero within `r₀` of `ā` in `ℓ¹_ν`, unique
within `r₁`. -/
theorem sh_lambda1_nu4 :
    HasIsolatedZero
      (CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_3 one_le_sh1_nu_3)
      (toX sh1_abar) sh1_r0_3 sh1_r1_3 := by
  rw [← sh1Data_toProblem sh1_nu_3 sh1_r0_3 sh1_r1_3]
  exact (sh1Data sh1_nu_3 sh1_r0_3 sh1_r1_3).verify one_le_sh1_nu_3
    (sh1_tail _ _ _) sh1_check_3

theorem sh1_check_4 : (sh1Data sh1_nu_4 sh1_r0_4 sh1_r1_4).check := by native_decide

theorem one_le_sh1_nu_4 : (1 : ℝ) ≤ (sh1_nu_4 : ℝ) := by norm_num [sh1_nu_4]

/-- Table 13.1, `λ = 1`, `ν = 5`: `F` has a zero within `r₀` of `ā` in `ℓ¹_ν`, unique
within `r₁`. -/
theorem sh_lambda1_nu5 :
    HasIsolatedZero
      (CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_4 one_le_sh1_nu_4)
      (toX sh1_abar) sh1_r0_4 sh1_r1_4 := by
  rw [← sh1Data_toProblem sh1_nu_4 sh1_r0_4 sh1_r1_4]
  exact (sh1Data sh1_nu_4 sh1_r0_4 sh1_r1_4).verify one_le_sh1_nu_4
    (sh1_tail _ _ _) sh1_check_4

/-! ## λ = 10 (`m = 31`) -/

/-- The certificate for `λ = 10` with weight `ν` and radii `r₀`, `r₁`. -/
def sh10Data (ν r0 r1 : ℚ) : CubicCosineData where
  μ := shMuQ 10
  m := sh10_m
  ν := ν
  abar := sh10_abar
  A k l := (sh10_A.getD k #[]).getD l 0
  r0 := r0
  r1 := r1

/-- The tail condition for `λ = 10` (Lemma 13.1.3). -/
theorem sh10_tail (ν r0 r1 : ℚ) (k : ℕ) (hk : (sh10Data ν r0 r1).m ≤ k) :
    |(sh10Data ν r0 r1).μ (sh10Data ν r0 r1).m| ≤ |(sh10Data ν r0 r1).μ k| :=
  sh_tail 10 (13 / 20) (by norm_num) (by norm_num [sh10Data, sh10_m])
    (by norm_num [sh10Data, sh10_m]) hk

/-- The problem of the certificate: eigenvalues `μ_k = λ - (1 - k² L²)²`, `λ = 10`, `L = 13/20`. -/
theorem sh10Data_toProblem (ν r0 r1 : ℚ) :
    (sh10Data ν r0 r1).toProblem = { μ := shMu shLambda10 shL } := by
  simp only [CubicCosineData.toProblem, sh10Data, shMuQ, shLambda10, shL]
  congr 1
  funext k
  rw [shMu]
  push_cast
  ring

theorem sh10_check_1 : (sh10Data sh10_nu_1 sh10_r0_1 sh10_r1_1).check := by native_decide

theorem one_le_sh10_nu_1 : (1 : ℝ) ≤ (sh10_nu_1 : ℝ) := by norm_num [sh10_nu_1]

/-- Table 13.1, `λ = 10`, `ν = 1`: `F` has a zero within `r₀` of `ā` in `ℓ¹_ν`, unique
within `r₁`. -/
theorem sh_lambda10_nu1 :
    HasIsolatedZero
      (CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_1 one_le_sh10_nu_1)
      (toX sh10_abar) sh10_r0_1 sh10_r1_1 := by
  rw [← sh10Data_toProblem sh10_nu_1 sh10_r0_1 sh10_r1_1]
  exact (sh10Data sh10_nu_1 sh10_r0_1 sh10_r1_1).verify one_le_sh10_nu_1
    (sh10_tail _ _ _) sh10_check_1

theorem sh10_check_2 : (sh10Data sh10_nu_2 sh10_r0_2 sh10_r1_2).check := by native_decide

theorem one_le_sh10_nu_2 : (1 : ℝ) ≤ (sh10_nu_2 : ℝ) := by norm_num [sh10_nu_2]

/-- Table 13.1, `λ = 10`, `ν = 3/2`: `F` has a zero within `r₀` of `ā` in `ℓ¹_ν`, unique
within `r₁`. -/
theorem sh_lambda10_nu3_2 :
    HasIsolatedZero
      (CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_2 one_le_sh10_nu_2)
      (toX sh10_abar) sh10_r0_2 sh10_r1_2 := by
  rw [← sh10Data_toProblem sh10_nu_2 sh10_r0_2 sh10_r1_2]
  exact (sh10Data sh10_nu_2 sh10_r0_2 sh10_r1_2).verify one_le_sh10_nu_2
    (sh10_tail _ _ _) sh10_check_2

theorem sh10_check_3 : (sh10Data sh10_nu_3 sh10_r0_3 sh10_r1_3).check := by native_decide

theorem one_le_sh10_nu_3 : (1 : ℝ) ≤ (sh10_nu_3 : ℝ) := by norm_num [sh10_nu_3]

/-- Table 13.1, `λ = 10`, `ν = 2`: `F` has a zero within `r₀` of `ā` in `ℓ¹_ν`, unique
within `r₁`. -/
theorem sh_lambda10_nu2 :
    HasIsolatedZero
      (CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_3 one_le_sh10_nu_3)
      (toX sh10_abar) sh10_r0_3 sh10_r1_3 := by
  rw [← sh10Data_toProblem sh10_nu_3 sh10_r0_3 sh10_r1_3]
  exact (sh10Data sh10_nu_3 sh10_r0_3 sh10_r1_3).verify one_le_sh10_nu_3
    (sh10_tail _ _ _) sh10_check_3

theorem sh10_check_4 : (sh10Data sh10_nu_4 sh10_r0_4 sh10_r1_4).check := by native_decide

theorem one_le_sh10_nu_4 : (1 : ℝ) ≤ (sh10_nu_4 : ℝ) := by norm_num [sh10_nu_4]

/-- Table 13.1, `λ = 10`, `ν = 75/32`: `F` has a zero within `r₀` of `ā` in `ℓ¹_ν`, unique
within `r₁`. -/
theorem sh_lambda10_nu75_32 :
    HasIsolatedZero
      (CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_4 one_le_sh10_nu_4)
      (toX sh10_abar) sh10_r0_4 sh10_r1_4 := by
  rw [← sh10Data_toProblem sh10_nu_4 sh10_r0_4 sh10_r1_4]
  exact (sh10Data sh10_nu_4 sh10_r0_4 sh10_r1_4).verify one_le_sh10_nu_4
    (sh10_tail _ _ _) sh10_check_4

/-! ## The equilibria (Remark 13.1.8) -/

/-- `u` is an equilibrium of `u_t = (λ - 1) u - 2 u_yy - u_yyyy - u³` with even, `2π/L`-periodic
boundary conditions: `u` is `C⁴` (with derivatives `u₁, …, u₄`), `(λ - 1) u - 2 u₂ - u₄ - u³ = 0`,
`u(-y) = u(y)` and `u(y + 2π/L) = u(y)`. -/
def SHEquilibrium (lam L : ℝ) (u : ℝ → ℝ) : Prop :=
  ∃ u₁ u₂ u₃ u₄ : ℝ → ℝ, ∀ y, HasDerivAt u (u₁ y) y ∧ HasDerivAt u₁ (u₂ y) y ∧
    HasDerivAt u₂ (u₃ y) y ∧ HasDerivAt u₃ (u₄ y) y ∧
    (lam - 1) * u y - 2 * u₂ y - u₄ y - u y ^ 3 = 0 ∧ u (-y) = u y ∧
    u (y + 2 * Real.pi / L) = u y

/-- An isolated zero of the Swift–Hohenberg operator near `ā` gives an equilibrium `u` (the cosine
series of the zero) within `2 r₀` of the cosine series `ū` of `ā`. -/
theorem sh_equilibrium_of {lam : ℝ} {ν : ℝ} {hν : 1 ≤ ν} {abar : List ℚ} {r₀ r₁ : ℝ}
    (h : HasIsolatedZero (CubicCosine.F { μ := shMu lam shL } ν hν) (toX abar) r₀ r₁) :
    ∃ a : Cosine.X ν hν, CubicCosine.F { μ := shMu lam shL } ν hν a = 0 ∧
      (∀ b ∈ Metric.closedBall (toX abar) r₁, CubicCosine.F { μ := shMu lam shL } ν hν b = 0 →
        b = a) ∧
      SHEquilibrium lam shL (CubicCosine.cosSeries shL a) ∧
      ∀ y, |CubicCosine.cosSeries shL a y - CubicCosine.cosSeries shL (toX abar : Cosine.X ν hν) y| < 2 * r₀ := by
  obtain ⟨a, hF, hu, u₁, u₂, u₃, u₄, h'⟩ :=
    CubicCosine.exists_equilibrium _ (by norm_num [shL] : (0 : ℝ) < shL) (fun k => rfl) h
  exact ⟨a, hF, hu, ⟨u₁, u₂, u₃, u₄, fun y => ⟨(h' y).1, (h' y).2.1, (h' y).2.2.1,
    (h' y).2.2.2.1, (h' y).2.2.2.2.1, (h' y).2.2.2.2.2.1, (h' y).2.2.2.2.2.2.1⟩⟩,
    fun y => (h' y).2.2.2.2.2.2.2⟩

/-- Table 13.1, `λ = 1`, `ν = 1`: the cosine series `u(y) = ã_0 + 2 ∑_k ã_k cos(kLy)` of
the zero `ã` is an equilibrium of the Swift–Hohenberg equation with `|u(y) - ū(y)| < 2 r₀` for all
`y`; `ã` is the unique zero of `F` within `r₁` of `ā`. -/
theorem sh_lambda1_nu1_equilibrium :
    ∃ a : Cosine.X sh1_nu_1 one_le_sh1_nu_1,
      CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_1 one_le_sh1_nu_1 a = 0 ∧
      (∀ b ∈ Metric.closedBall (toX sh1_abar) sh1_r1_1,
        CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_1 one_le_sh1_nu_1 b = 0 → b = a) ∧
      SHEquilibrium shLambda1 shL (CubicCosine.cosSeries shL a) ∧
      ∀ y, |CubicCosine.cosSeries shL a y - CubicCosine.cosSeries shL
        (toX sh1_abar : Cosine.X sh1_nu_1 one_le_sh1_nu_1) y| < 2 * sh1_r0_1 :=
  sh_equilibrium_of sh_lambda1_nu1

/-- Table 13.1, `λ = 1`, `ν = 2`: the cosine series `u(y) = ã_0 + 2 ∑_k ã_k cos(kLy)` of
the zero `ã` is an equilibrium of the Swift–Hohenberg equation with `|u(y) - ū(y)| < 2 r₀` for all
`y`; `ã` is the unique zero of `F` within `r₁` of `ā`. -/
theorem sh_lambda1_nu2_equilibrium :
    ∃ a : Cosine.X sh1_nu_2 one_le_sh1_nu_2,
      CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_2 one_le_sh1_nu_2 a = 0 ∧
      (∀ b ∈ Metric.closedBall (toX sh1_abar) sh1_r1_2,
        CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_2 one_le_sh1_nu_2 b = 0 → b = a) ∧
      SHEquilibrium shLambda1 shL (CubicCosine.cosSeries shL a) ∧
      ∀ y, |CubicCosine.cosSeries shL a y - CubicCosine.cosSeries shL
        (toX sh1_abar : Cosine.X sh1_nu_2 one_le_sh1_nu_2) y| < 2 * sh1_r0_2 :=
  sh_equilibrium_of sh_lambda1_nu2

/-- Table 13.1, `λ = 1`, `ν = 4`: the cosine series `u(y) = ã_0 + 2 ∑_k ã_k cos(kLy)` of
the zero `ã` is an equilibrium of the Swift–Hohenberg equation with `|u(y) - ū(y)| < 2 r₀` for all
`y`; `ã` is the unique zero of `F` within `r₁` of `ā`. -/
theorem sh_lambda1_nu4_equilibrium :
    ∃ a : Cosine.X sh1_nu_3 one_le_sh1_nu_3,
      CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_3 one_le_sh1_nu_3 a = 0 ∧
      (∀ b ∈ Metric.closedBall (toX sh1_abar) sh1_r1_3,
        CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_3 one_le_sh1_nu_3 b = 0 → b = a) ∧
      SHEquilibrium shLambda1 shL (CubicCosine.cosSeries shL a) ∧
      ∀ y, |CubicCosine.cosSeries shL a y - CubicCosine.cosSeries shL
        (toX sh1_abar : Cosine.X sh1_nu_3 one_le_sh1_nu_3) y| < 2 * sh1_r0_3 :=
  sh_equilibrium_of sh_lambda1_nu4

/-- Table 13.1, `λ = 1`, `ν = 5`: the cosine series `u(y) = ã_0 + 2 ∑_k ã_k cos(kLy)` of
the zero `ã` is an equilibrium of the Swift–Hohenberg equation with `|u(y) - ū(y)| < 2 r₀` for all
`y`; `ã` is the unique zero of `F` within `r₁` of `ā`. -/
theorem sh_lambda1_nu5_equilibrium :
    ∃ a : Cosine.X sh1_nu_4 one_le_sh1_nu_4,
      CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_4 one_le_sh1_nu_4 a = 0 ∧
      (∀ b ∈ Metric.closedBall (toX sh1_abar) sh1_r1_4,
        CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_4 one_le_sh1_nu_4 b = 0 → b = a) ∧
      SHEquilibrium shLambda1 shL (CubicCosine.cosSeries shL a) ∧
      ∀ y, |CubicCosine.cosSeries shL a y - CubicCosine.cosSeries shL
        (toX sh1_abar : Cosine.X sh1_nu_4 one_le_sh1_nu_4) y| < 2 * sh1_r0_4 :=
  sh_equilibrium_of sh_lambda1_nu5

/-- Table 13.1, `λ = 10`, `ν = 1`: the cosine series `u(y) = ã_0 + 2 ∑_k ã_k cos(kLy)` of
the zero `ã` is an equilibrium of the Swift–Hohenberg equation with `|u(y) - ū(y)| < 2 r₀` for all
`y`; `ã` is the unique zero of `F` within `r₁` of `ā`. -/
theorem sh_lambda10_nu1_equilibrium :
    ∃ a : Cosine.X sh10_nu_1 one_le_sh10_nu_1,
      CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_1 one_le_sh10_nu_1 a = 0 ∧
      (∀ b ∈ Metric.closedBall (toX sh10_abar) sh10_r1_1,
        CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_1 one_le_sh10_nu_1 b = 0 → b = a) ∧
      SHEquilibrium shLambda10 shL (CubicCosine.cosSeries shL a) ∧
      ∀ y, |CubicCosine.cosSeries shL a y - CubicCosine.cosSeries shL
        (toX sh10_abar : Cosine.X sh10_nu_1 one_le_sh10_nu_1) y| < 2 * sh10_r0_1 :=
  sh_equilibrium_of sh_lambda10_nu1

/-- Table 13.1, `λ = 10`, `ν = 3/2`: the cosine series `u(y) = ã_0 + 2 ∑_k ã_k cos(kLy)` of
the zero `ã` is an equilibrium of the Swift–Hohenberg equation with `|u(y) - ū(y)| < 2 r₀` for all
`y`; `ã` is the unique zero of `F` within `r₁` of `ā`. -/
theorem sh_lambda10_nu3_2_equilibrium :
    ∃ a : Cosine.X sh10_nu_2 one_le_sh10_nu_2,
      CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_2 one_le_sh10_nu_2 a = 0 ∧
      (∀ b ∈ Metric.closedBall (toX sh10_abar) sh10_r1_2,
        CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_2 one_le_sh10_nu_2 b = 0 → b = a) ∧
      SHEquilibrium shLambda10 shL (CubicCosine.cosSeries shL a) ∧
      ∀ y, |CubicCosine.cosSeries shL a y - CubicCosine.cosSeries shL
        (toX sh10_abar : Cosine.X sh10_nu_2 one_le_sh10_nu_2) y| < 2 * sh10_r0_2 :=
  sh_equilibrium_of sh_lambda10_nu3_2

/-- Table 13.1, `λ = 10`, `ν = 2`: the cosine series `u(y) = ã_0 + 2 ∑_k ã_k cos(kLy)` of
the zero `ã` is an equilibrium of the Swift–Hohenberg equation with `|u(y) - ū(y)| < 2 r₀` for all
`y`; `ã` is the unique zero of `F` within `r₁` of `ā`. -/
theorem sh_lambda10_nu2_equilibrium :
    ∃ a : Cosine.X sh10_nu_3 one_le_sh10_nu_3,
      CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_3 one_le_sh10_nu_3 a = 0 ∧
      (∀ b ∈ Metric.closedBall (toX sh10_abar) sh10_r1_3,
        CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_3 one_le_sh10_nu_3 b = 0 → b = a) ∧
      SHEquilibrium shLambda10 shL (CubicCosine.cosSeries shL a) ∧
      ∀ y, |CubicCosine.cosSeries shL a y - CubicCosine.cosSeries shL
        (toX sh10_abar : Cosine.X sh10_nu_3 one_le_sh10_nu_3) y| < 2 * sh10_r0_3 :=
  sh_equilibrium_of sh_lambda10_nu2

/-- Table 13.1, `λ = 10`, `ν = 75/32`: the cosine series `u(y) = ã_0 + 2 ∑_k ã_k cos(kLy)` of
the zero `ã` is an equilibrium of the Swift–Hohenberg equation with `|u(y) - ū(y)| < 2 r₀` for all
`y`; `ã` is the unique zero of `F` within `r₁` of `ā`. -/
theorem sh_lambda10_nu75_32_equilibrium :
    ∃ a : Cosine.X sh10_nu_4 one_le_sh10_nu_4,
      CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_4 one_le_sh10_nu_4 a = 0 ∧
      (∀ b ∈ Metric.closedBall (toX sh10_abar) sh10_r1_4,
        CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_4 one_le_sh10_nu_4 b = 0 → b = a) ∧
      SHEquilibrium shLambda10 shL (CubicCosine.cosSeries shL a) ∧
      ∀ y, |CubicCosine.cosSeries shL a y - CubicCosine.cosSeries shL
        (toX sh10_abar : Cosine.X sh10_nu_4 one_le_sh10_nu_4) y| < 2 * sh10_r0_4 :=
  sh_equilibrium_of sh_lambda10_nu75_32

/-! ## Conclusions of Section 13.1.3 -/

/-- `ū(0) = ā_0 + 2 ∑_{k ≥ 1} ā_k`, computed exactly. -/
def shU0 (a : List ℚ) : ℚ := FinSeq.get a 0 + 2 * ∑ k ∈ Finset.range a.length, FinSeq.get a (k + 1)

theorem cosSeries_toX_zero {ν : ℝ} {hν : 1 ≤ ν} (L : ℝ) (a : List ℚ) :
    CubicCosine.cosSeries L (toX a : Cosine.X ν hν) 0 = shU0 a := by
  simp only [CubicCosine.cosSeries, mul_zero, Real.cos_zero, mul_one, toX_apply]
  rw [tsum_eq_sum (s := Finset.range a.length) fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    simp [FinSeq.get_eq_zero a (show a.length ≤ k + 1 by omega)]]
  simp [shU0]

/-- Conclusions of Section 13.1.3, `λ = 1`: the zero `ã` obtained with `ν = 1` (Table 13.1) has the
same coefficients as the zeros obtained with `ν = 2, 4, 5` (since `r₀(ν) ≤ r₁(1)`); its cosine
series `u` is an equilibrium of the Swift–Hohenberg equation with `sup_y |u(y) - ū(y)| ≤ 1.71e-16`, and
`u(0) ∈ 0.9289703567 + [-10⁻¹⁰, 10⁻¹⁰]`, so that `u` is nontrivial. -/
theorem sh_lambda1_conclusions :
    ∃ a : Cosine.X sh1_nu_1 one_le_sh1_nu_1,
      CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_1 one_le_sh1_nu_1 a = 0 ∧
      (∀ b ∈ Metric.closedBall (toX sh1_abar) sh1_r1_1,
        CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_1 one_le_sh1_nu_1 b = 0 → b = a) ∧
      (∀ b ∈ Metric.closedBall (toX sh1_abar : Cosine.X sh1_nu_2 one_le_sh1_nu_2) sh1_r1_2,
        CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_2 one_le_sh1_nu_2 b = 0 → ∀ k, b k = a k) ∧
      (∀ b ∈ Metric.closedBall (toX sh1_abar : Cosine.X sh1_nu_3 one_le_sh1_nu_3) sh1_r1_3,
        CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_3 one_le_sh1_nu_3 b = 0 → ∀ k, b k = a k) ∧
      (∀ b ∈ Metric.closedBall (toX sh1_abar : Cosine.X sh1_nu_4 one_le_sh1_nu_4) sh1_r1_4,
        CubicCosine.F { μ := shMu shLambda1 shL } sh1_nu_4 one_le_sh1_nu_4 b = 0 → ∀ k, b k = a k) ∧
      SHEquilibrium shLambda1 shL (CubicCosine.cosSeries shL a) ∧
      (∀ y, |CubicCosine.cosSeries shL a y - CubicCosine.cosSeries shL
        (toX sh1_abar : Cosine.X sh1_nu_1 one_le_sh1_nu_1) y| ≤ 1.71e-16) ∧
      |CubicCosine.cosSeries shL a 0 - 0.9289703567| ≤ 1 / 10 ^ 10 ∧ CubicCosine.cosSeries shL a 0 ≠ 0 := by
  obtain ⟨a, hF, hu, hE, herr⟩ := sh_equilibrium_of sh_lambda1_nu1
  obtain ⟨a₀, ha₀, hF₀, -⟩ := sh_lambda1_nu1
  have hmem : a ∈ Metric.closedBall (toX sh1_abar : Cosine.X sh1_nu_1 one_le_sh1_nu_1) sh1_r1_1 := by
    have ha₀' : a₀ ∈ Metric.closedBall (toX sh1_abar : Cosine.X sh1_nu_1 one_le_sh1_nu_1)
        sh1_r1_1 := Metric.closedBall_subset_closedBall (by norm_num [sh1_r0_1, sh1_r1_1])
      (Metric.ball_subset_closedBall ha₀)
    rw [← hu a₀ ha₀' hF₀]
    exact ha₀'
  have h0 : |CubicCosine.cosSeries shL a 0 - shU0 sh1_abar| < ((2 * sh1_r0_1 : ℚ) : ℝ) := by
    have h := herr 0
    rw [cosSeries_toX_zero] at h
    push_cast
    exact h
  have hv : |CubicCosine.cosSeries shL a 0 - 0.9289703567| ≤ 1 / 10 ^ 10 := by
    have := abs_sub_le_of_approx h0 (c := 0.9289703567) (δ := 1 / 10 ^ 10) (by native_decide)
    simpa using this
  refine ⟨a, hF, hu,
    fun b hb hFb k => CubicCosine.coeff_eq_of_isolatedZero _ (ν := sh1_nu_2) (ν' := sh1_nu_1)
      (by norm_num [sh1_nu_1, sh1_nu_2])
      (fun k => by rw [toX_apply, toX_apply]) sh_lambda1_nu2 sh_lambda1_nu1 (by norm_num [sh1_r0_2, sh1_r1_1]) hb hFb hmem hF k,
    fun b hb hFb k => CubicCosine.coeff_eq_of_isolatedZero _ (ν := sh1_nu_3) (ν' := sh1_nu_1)
      (by norm_num [sh1_nu_1, sh1_nu_3])
      (fun k => by rw [toX_apply, toX_apply]) sh_lambda1_nu4 sh_lambda1_nu1 (by norm_num [sh1_r0_3, sh1_r1_1]) hb hFb hmem hF k,
    fun b hb hFb k => CubicCosine.coeff_eq_of_isolatedZero _ (ν := sh1_nu_4) (ν' := sh1_nu_1)
      (by norm_num [sh1_nu_1, sh1_nu_4])
      (fun k => by rw [toX_apply, toX_apply]) sh_lambda1_nu5 sh_lambda1_nu1 (by norm_num [sh1_r0_4, sh1_r1_1]) hb hFb hmem hF k,
    hE, fun y => (herr y).le.trans (by norm_num [sh1_r0_1]), hv, fun h => ?_⟩
  rw [h, zero_sub, abs_neg] at hv
  norm_num at hv

/-- Conclusions of Section 13.1.3, `λ = 10`: the zero `ã` obtained with `ν = 1` (Table 13.1) has the
same coefficients as the zeros obtained with `ν = 3/2, 2, 75/32` (since `r₀(ν) ≤ r₁(1)`); its cosine
series `u` is an equilibrium of the Swift–Hohenberg equation with `sup_y |u(y) - ū(y)| ≤ 5.78e-16`, and
`u(0) ∈ 3.1730186915 + [-10⁻¹⁰, 10⁻¹⁰]`, so that `u` is nontrivial. -/
theorem sh_lambda10_conclusions :
    ∃ a : Cosine.X sh10_nu_1 one_le_sh10_nu_1,
      CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_1 one_le_sh10_nu_1 a = 0 ∧
      (∀ b ∈ Metric.closedBall (toX sh10_abar) sh10_r1_1,
        CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_1 one_le_sh10_nu_1 b = 0 → b = a) ∧
      (∀ b ∈ Metric.closedBall (toX sh10_abar : Cosine.X sh10_nu_2 one_le_sh10_nu_2) sh10_r1_2,
        CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_2 one_le_sh10_nu_2 b = 0 → ∀ k, b k = a k) ∧
      (∀ b ∈ Metric.closedBall (toX sh10_abar : Cosine.X sh10_nu_3 one_le_sh10_nu_3) sh10_r1_3,
        CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_3 one_le_sh10_nu_3 b = 0 → ∀ k, b k = a k) ∧
      (∀ b ∈ Metric.closedBall (toX sh10_abar : Cosine.X sh10_nu_4 one_le_sh10_nu_4) sh10_r1_4,
        CubicCosine.F { μ := shMu shLambda10 shL } sh10_nu_4 one_le_sh10_nu_4 b = 0 → ∀ k, b k = a k) ∧
      SHEquilibrium shLambda10 shL (CubicCosine.cosSeries shL a) ∧
      (∀ y, |CubicCosine.cosSeries shL a y - CubicCosine.cosSeries shL
        (toX sh10_abar : Cosine.X sh10_nu_1 one_le_sh10_nu_1) y| ≤ 5.78e-16) ∧
      |CubicCosine.cosSeries shL a 0 - 3.1730186915| ≤ 1 / 10 ^ 10 ∧ CubicCosine.cosSeries shL a 0 ≠ 0 := by
  obtain ⟨a, hF, hu, hE, herr⟩ := sh_equilibrium_of sh_lambda10_nu1
  obtain ⟨a₀, ha₀, hF₀, -⟩ := sh_lambda10_nu1
  have hmem : a ∈ Metric.closedBall (toX sh10_abar : Cosine.X sh10_nu_1 one_le_sh10_nu_1) sh10_r1_1 := by
    have ha₀' : a₀ ∈ Metric.closedBall (toX sh10_abar : Cosine.X sh10_nu_1 one_le_sh10_nu_1)
        sh10_r1_1 := Metric.closedBall_subset_closedBall (by norm_num [sh10_r0_1, sh10_r1_1])
      (Metric.ball_subset_closedBall ha₀)
    rw [← hu a₀ ha₀' hF₀]
    exact ha₀'
  have h0 : |CubicCosine.cosSeries shL a 0 - shU0 sh10_abar| < ((2 * sh10_r0_1 : ℚ) : ℝ) := by
    have h := herr 0
    rw [cosSeries_toX_zero] at h
    push_cast
    exact h
  have hv : |CubicCosine.cosSeries shL a 0 - 3.1730186915| ≤ 1 / 10 ^ 10 := by
    have := abs_sub_le_of_approx h0 (c := 3.1730186915) (δ := 1 / 10 ^ 10) (by native_decide)
    simpa using this
  refine ⟨a, hF, hu,
    fun b hb hFb k => CubicCosine.coeff_eq_of_isolatedZero _ (ν := sh10_nu_2) (ν' := sh10_nu_1)
      (by norm_num [sh10_nu_1, sh10_nu_2])
      (fun k => by rw [toX_apply, toX_apply]) sh_lambda10_nu3_2 sh_lambda10_nu1 (by norm_num [sh10_r0_2, sh10_r1_1]) hb hFb hmem hF k,
    fun b hb hFb k => CubicCosine.coeff_eq_of_isolatedZero _ (ν := sh10_nu_3) (ν' := sh10_nu_1)
      (by norm_num [sh10_nu_1, sh10_nu_3])
      (fun k => by rw [toX_apply, toX_apply]) sh_lambda10_nu2 sh_lambda10_nu1 (by norm_num [sh10_r0_3, sh10_r1_1]) hb hFb hmem hF k,
    fun b hb hFb k => CubicCosine.coeff_eq_of_isolatedZero _ (ν := sh10_nu_4) (ν' := sh10_nu_1)
      (by norm_num [sh10_nu_1, sh10_nu_4])
      (fun k => by rw [toX_apply, toX_apply]) sh_lambda10_nu75_32 sh_lambda10_nu1 (by norm_num [sh10_r0_4, sh10_r1_1]) hb hFb hmem hF k,
    hE, fun y => (herr y).le.trans (by norm_num [sh10_r0_1]), hv, fun h => ?_⟩
  rw [h, zero_sub, abs_neg] at hv
  norm_num at hv

end LeanearizedODEs.Ch13
