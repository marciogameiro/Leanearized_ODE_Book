module

public import RadiiPolynomial.Problems.FiniteDimZeros
public import RadiiPolynomial.Problems.QuadraticFourierCheck
public import RadiiPolynomial.Problems.FourierPeriodicCheck
public import RadiiPolynomial.Problems.QuadraticFourierSolution
public import RadiiPolynomial.Problems.FourierPeriodicSolution
public import LeanearizedODEs.Data.Ch10
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Analysis.Complex.Polynomial.Basic
public meta import RadiiPolynomial.Problems.FiniteDimZeros
public meta import RadiiPolynomial.Problems.QuadraticFourierCheck
public meta import RadiiPolynomial.Problems.FourierPeriodicCheck
public meta import LeanearizedODEs.Data.Ch10

/-!
# Examples of Chapter 10

* Section 10.1: a `2π`-periodic solution of the Helmholtz–Duffing equation
  `u'' + c₁ u' + c₂ u - u² = c₃ cos t`, `c₁ = 1/10`, `c₂ = 4`, `c₃ = 1`, as a zero of
  `F_n(a) = λ_n a_n - (a * a)_n - c₃ b_n` in `ℓ¹_ν(ℤ)`, `λ_n = -n² + i c₁ n + c₂`, `ν = 5/4`, `N = 10`
  (`helmholtz_duffing`), via Theorem 10.1.5 (`QuadraticFourier.radii_poly_two_radii`, through the
  checker `QuadraticFourierData.verify`); the tail condition `|λ_n| ≥ |λ_{N+1}|` is Lemma 10.1.3(ii)
  (`helm_tail`). The problem data (`c₁`, `c₂`, `c₃`, `λ_n`, the forcing) are named definitions next
  to the theorem; the certificate data (`ā`, `A_N`, `N`, `ν`, `r₀`, `r₁`) come from
  `code/certificates/ch10_helmholtz.json`. All bounds are computed exactly from the data (moduli by
  rational upper and lower bounds) by `QuadraticFourierData.check`, evaluated by compiled code
  (`native_decide`).
  Solution (Lemma 10.1.1, Proposition 10.1.4, `helmholtz_solution`): a real `2π`-periodic `C²`
  solution `u` of the equation within `r₀` of `∑_{|n| ≤ 10} ā_n e^{int}`, whose Fourier coefficients
  form the unique zero of `F` within `r₁` (via `QuadraticFourier.exists_solution`).
* Section 10.3: the periodic orbit `LR` of the Lorenz system (`σ = 10`, `ρ = 28`, `β = 8/3`) as a
  zero of the periodic orbit map `F(τ₀, a)` of Section 10.2 in `ℂ × (ℓ¹_ν)³`, `N = 35`, `ν = 9/8`,
  with the phase condition at `ξ` and `ξ̂ = f(ξ)` (`lorenz_LR`), via Theorem 10.2.12
  (`FourierPeriodic.radii_poly_two_radii`, through the checker `FourierPeriodicData.verify`; the
  `214 × 214` complex matrix `A^{(N)}` and `ā` come from `code/certificates/ch10_lorenz_LR.json`;
  `native_decide`). Solution (Lemmas 10.2.2, 10.2.8–10.2.11, `lorenz_LR_solution`): a periodic
  solution `γ` of the Lorenz system with period `T`, `|T - 2π τ̄₀| < 2π r₀`, within `r₀` of
  `∑_{|k| ≤ 35} ā_k e^{2πikt/T}`, whose coefficients form the unique zero of `F` within `r₁` (via
  `FourierPeriodic.exists_solution`).
* Section 10.4.1: the Hopf bifurcation point of the Lorenz system with `σ = 10`, `β = 8/3`, as a
  nondegenerate zero of the Hopf map `F : ℝ¹¹ → ℝ¹¹`,
  `F(X) = (f(x, ρ), D_x f(x, ρ) v₁ + ω v₂, D_x f(x, ρ) v₂ - ω v₁, v₁ · ξ₁ - 1, v₂ · ξ₂ - 1)`,
  `X = (x, v₁, v₂, ρ, ω)`, `ξᵢ = v̄ᵢ` (`hopf_point`), via the finite-dimensional radii polynomial
  theorem (Theorem 2.4.2, `QuadraticSystem.radii_poly_two_radii_exact`) with the sup norm. `F` is
  quadratic, so `Z₂` is a constant. The eigenvalues of `D_x f(x̃, ρ̃)` are `±iω̃`, `ω̃ ≠ 0`, and
  `-41/3` (`hopf_point_eigenvalues`); that `(x̃, ρ̃)` is then a Hopf bifurcation point is the
  classical Hopf bifurcation theorem (Theorems 10.4.1, 10.4.3), cited, not formalized.

Conventions for the Hopf point: the problem (the Hopf map and its parameters) is written out
explicitly, and nondegeneracy refers to its derivative `fderiv ℝ hopfMap`; the certificate data
(`X̄`, `ξ₁`, `ξ₂`, `A`, `r₀`, `r₁`) are named constants from `Examples/Data/Ch10.lean`, generated
from `code/certificates/ch10_hopf.json`. The bounds are evaluated exactly from the data and the
signs of the radii polynomial are checked by the kernel (`decide +kernel`).

Indices start at `0`: `X = (X 0, X 1, X 2 | X 3, X 4, X 5 | X 6, X 7, X 8 | X 9 | X 10)` is
`(x | v₁ | v₂ | ρ | ω)`.
-/

@[expose] public section

namespace LeanearizedODEs.Ch10

open RadiiPolynomial
open QuadraticSystem Metric Ch10Data

/-! ## The parameters of the Lorenz system -/

/-- The parameter `σ = 10`. -/
noncomputable def σ : ℝ := 10

/-- The parameter `ρ = 28`. -/
noncomputable def ρ : ℝ := 28

/-- The parameter `β = 8/3`. -/
noncomputable def β : ℝ := 8 / 3

/-! ## Section 10.1: the Helmholtz–Duffing equation -/

/-- The eigenvalues `λ_n = -n² + i c₁ n + c₂` with rational `c₁`, `c₂`, for the checker. -/
def helmLamQ (c₁ c₂ : ℚ) (n : ℤ) : QC := (-(n : ℚ) ^ 2 + c₂, c₁ * n)

/-- Lemma 10.1.3(ii): if `(N + 1)² ≥ c₂`, then `|λ_n| ≥ |λ_{N+1}|` for all `|n| > N`
(stated for `|λ_n|² = (n² - c₂)² + c₁² n²`). -/
theorem helm_tail (c₁ c₂ : ℚ) {N : ℕ} (hN : c₂ ≤ ((N : ℚ) + 1) ^ 2) {n : ℤ}
    (hn : N < n.natAbs) :
    QC.normSq (helmLamQ c₁ c₂ (N + 1)) ≤ QC.normSq (helmLamQ c₁ c₂ n) := by
  have hx : ((N : ℚ) + 1) ^ 2 ≤ (n : ℚ) ^ 2 := by
    have h1 : ((N : ℚ) + 1) ≤ (n.natAbs : ℚ) := by exact_mod_cast hn
    have h2 : (n : ℚ) ^ 2 = (n.natAbs : ℚ) ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [h2]
    exact pow_le_pow_left₀ (by positivity) h1 2
  simp only [QC.normSq, helmLamQ]
  push_cast
  nlinarith [mul_self_nonneg c₁, sq_nonneg ((n : ℚ) ^ 2 - ((N : ℚ) + 1) ^ 2)]

/-- The parameter `c₁ = 1/10` (damping). -/
noncomputable def helmC1 : ℝ := 1 / 10

/-- The parameter `c₂ = 4`. -/
noncomputable def helmC2 : ℝ := 4

/-- The parameter `c₃ = 1` (amplitude of the forcing). -/
noncomputable def helmC3 : ℝ := 1

/-- The eigenvalues `λ_n = -n² + i c₁ n + c₂` of `u'' + c₁ u' + c₂ u` on `e^{int}`. -/
noncomputable def helmholtzLam (n : ℤ) : ℂ := -(n : ℂ) ^ 2 + Complex.I * helmC1 * n + helmC2

/-- The forcing `c₃ cos t = (c₃/2) e^{it} + (c₃/2) e^{-it}`. -/
noncomputable def helmholtzForcing : ℤ →₀ ℂ :=
  Finsupp.single (1 : ℤ) ((helmC3 / 2 : ℝ) : ℂ) + Finsupp.single (-1 : ℤ) ((helmC3 / 2 : ℝ) : ℂ)

/-- The certificate. -/
def helmData : QuadraticFourierData where
  lam := helmLamQ (1 / 10) 4
  g n := if n = 1 ∨ n = -1 then (1 / 2, 0) else 0
  N := helm_N
  ν := helm_nu
  abar := helm_abar
  A k l := (helm_A.getD (k + helm_N).toNat #[]).getD (l + helm_N).toNat 0
  r0 := helm_r0
  r1 := helm_r1

/-- The problem of the certificate: `λ_n = -n² + i c₁ n + c₂`, forcing `c₃ cos t`. -/
theorem helmData_toProblem :
    helmData.toProblem = { lam := helmholtzLam, g := helmholtzForcing } := by
  have hlam : helmData.toProblem.lam = helmholtzLam := by
    funext n
    rw [QuadraticFourierData.toProblem_lam]
    apply Complex.ext <;> simp [helmData, helmLamQ, helmholtzLam, helmC1, helmC2, sq]
  have hg : helmData.toProblem.g = helmholtzForcing := by
    ext n
    rw [QuadraticFourierData.toProblem_g, QuadraticFourierData.gN]
    simp only [helmData, helm_N, helmholtzForcing, helmC3, Finsupp.add_apply,
      Finsupp.single_apply]
    by_cases h1 : n = 1
    · subst h1; apply Complex.ext <;> norm_num
    · by_cases h2 : n = -1
      · subst h2; apply Complex.ext <;> norm_num
      · have h1' : (1 : ℤ) ≠ n := Ne.symm h1
        have h2' : (-1 : ℤ) ≠ n := Ne.symm h2
        simp [h1, h2, h1', h2']
  cases h : helmData.toProblem
  rw [h] at hlam hg
  simp only at hlam hg
  rw [hlam, hg]

theorem helm_check : helmData.check := by native_decide

theorem one_le_helm_nu : (1 : ℝ) ≤ (helm_nu : ℝ) := by norm_num [helm_nu]

/-- Theorem 10.1.5 with the data of Section 10.1 (`c₁ = 1/10`, `c₂ = 4`, `c₃ = 1`, `N = 10`,
`ν = 5/4`): `F(a) = Λ a - a * a - c₃ b` has a zero within `r₀` of `ā` in `ℓ¹_ν`, unique within
`r₁`. -/
theorem helmholtz_duffing :
    HasIsolatedZero
      (QuadraticFourier.F { lam := helmholtzLam, g := helmholtzForcing } helm_nu one_le_helm_nu)
      (FourierSeq.toX helm_N helm_abar) helm_r0 helm_r1 := by
  rw [← helmData_toProblem]
  exact helmData.verify one_le_helm_nu
    (fun n hn => helm_tail (1 / 10) 4 (by norm_num [helmData, helm_N]) hn) helm_check

/-! ### The solution (Lemma 10.1.1, Proposition 10.1.4) -/

theorem helm_symm : FourierSeq.IsSymm helm_N helm_abar := by native_decide

theorem one_lt_helm_nu : (1 : ℝ) < (helm_nu : ℝ) := by norm_num [helm_nu]

/-- The forcing series is `c₃ cos t`. -/
theorem re_forcing (t : ℝ) :
    (∑' n, helmholtzForcing n * Fourier.expI t n).re = helmC3 * Real.cos t := by
  rw [tsum_eq_sum (s := {1, -1}) fun n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [helmholtzForcing, Ne.symm hn.1, Ne.symm hn.2]]
  rw [Finset.sum_pair (by norm_num)]
  simp only [helmholtzForcing, Finsupp.add_apply, Finsupp.single_apply]
  norm_num [Fourier.expI]
  rw [show -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  ring

/-- Lemma 10.1.1, Proposition 10.1.4 and Theorem 10.1.5 with the data of Section 10.1: the
Helmholtz–Duffing equation `u'' + c₁ u' + c₂ u - u² = c₃ cos t` (`c₁ = 1/10`, `c₂ = 4`, `c₃ = 1`)
has a real `2π`-periodic `C²` solution `u` within `r₀ = 4.6 · 10⁻⁹` (for all `t`) of
`ū(t) = ∑_{|n| ≤ 10} ā_n e^{int}`; its Fourier coefficients form the unique zero of `F` within
`r₁ = 0.0624` of `ā` in `ℓ¹_ν`, `ν = 5/4`. -/
theorem helmholtz_solution :
    ∃ a : Fourier.X (helm_nu : ℝ) one_le_helm_nu,
      QuadraticFourier.F { lam := helmholtzLam, g := helmholtzForcing } helm_nu one_le_helm_nu a = 0 ∧
      (∀ b ∈ closedBall (FourierSeq.toX helm_N helm_abar) helm_r1,
        QuadraticFourier.F { lam := helmholtzLam, g := helmholtzForcing } helm_nu one_le_helm_nu b =
          0 → b = a) ∧
      ∃ u u' u'' : ℝ → ℝ, ∀ t, (u t : ℂ) = ∑' n, a n * Fourier.expI t n ∧
        HasDerivAt u (u' t) t ∧ HasDerivAt u' (u'' t) t ∧
        u'' t + helmC1 * u' t + helmC2 * u t - u t ^ 2 = helmC3 * Real.cos t ∧
        u (t + 2 * Real.pi) = u t ∧ ‖(u t : ℂ) - FourierSeq.evalAt helm_N helm_abar t‖ < helm_r0 := by
  have hg : ∀ n : ℤ, helmholtzForcing (-n) = star (helmholtzForcing n) := fun n => by
    by_cases h1 : n = 1
    · subst h1; simp [helmholtzForcing, helmC3]
    · by_cases h2 : n = -1
      · subst h2; simp [helmholtzForcing, helmC3]
      · have h1' : (1 : ℤ) ≠ -n := fun h => h2 (by omega)
        have h2' : (-1 : ℤ) ≠ -n := fun h => h1 (by omega)
        simp [helmholtzForcing, h1', h2', Ne.symm h1, Ne.symm h2]
  obtain ⟨a, hFa, huniq, u, u', u'', hu⟩ :=
    QuadraticFourier.exists_solution { lam := helmholtzLam, g := helmholtzForcing } one_lt_helm_nu
      (c₁ := helmC1) (c₂ := helmC2) (fun n => rfl) hg (FourierSeq.conjX_toX helm_symm)
      (by norm_num [helm_r0, helm_r1]) helmholtz_duffing
  refine ⟨a, hFa, huniq, u, u', u'', fun t => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hu t
  refine ⟨h1, h2, h3, ?_, h5, ?_⟩
  · rw [h4]; exact re_forcing t
  · rwa [FourierSeq.fourierEval_toX] at h6

/-! ## Section 10.3: the periodic orbit LR of the Lorenz system -/

open MvPolynomial in
/-- The Lorenz vector field `f(x) = (σ (x₂ - x₁), ρ x₁ - x₂ - x₁ x₃, x₁ x₂ - β x₃)`, with complex
coefficients (indices `0, 1, 2`). -/
noncomputable def lorenzPOField : Fin 3 → MvPolynomial (Fin 3) ℂ :=
  ![C (σ : ℂ) * (X 1 - X 0), C (ρ : ℂ) * X 0 - X 1 - X 0 * X 2, X 0 * X 1 - C (β : ℂ) * X 2]

/-- The anchor point `ξ` of the phase condition. -/
noncomputable def lrXi : Fin 3 → ℂ := fun j => (lr_xi j : ℂ)

/-- The normal vector `ξ̂ = f(ξ)` of the phase condition. -/
noncomputable def lrXihat : Fin 3 → ℂ := fun j => MvPolynomial.eval lrXi (lorenzPOField j)

/-- The periodic orbit problem: `x' = f(x)` with the phase condition
`∑_j ξ̂_j (∑_{|k| ≤ N} a_{j,k} - ξ_j) = 0`. -/
noncomputable def lorenzLR : FourierPeriodic 3 :=
  { f := lorenzPOField, ξ := lrXi, ξhat := lrXihat, N₀ := lr_N }

/-- The approximate solution `x̄ = (τ̄₀, ā)`. -/
noncomputable def lrXbar (hν : 1 ≤ (lr_nu : ℝ)) : FourierPeriodic.X 3 (lr_nu : ℝ) hν :=
  ((lr_tau : ℂ), fun j => FourierSeq.toX lr_N (lr_abar j))

/-- The Lorenz field with rational coefficients, for the checker. -/
def lorenzPolyData : Fin 3 → PolyData 3 :=
  ![[⟨-10, ![1, 0, 0]⟩, ⟨10, ![0, 1, 0]⟩],
    [⟨28, ![1, 0, 0]⟩, ⟨-1, ![0, 1, 0]⟩, ⟨-1, ![1, 0, 1]⟩],
    [⟨-8 / 3, ![0, 0, 1]⟩, ⟨1, ![1, 1, 0]⟩]]

/-- `ξ̂ = f(ξ)`, exactly. -/
def lrXihatQ : Fin 3 → ℚ :=
  ![10 * (lr_xi 1 - lr_xi 0), 28 * lr_xi 0 - lr_xi 1 - lr_xi 0 * lr_xi 2,
    lr_xi 0 * lr_xi 1 - 8 / 3 * lr_xi 2]

/-- The certificate. -/
def lrData : FourierPeriodicData 3 where
  f := lorenzPolyData
  ξ j := (lr_xi j, 0)
  ξhat j := (lrXihatQ j, 0)
  N := lr_N
  ν := lr_nu
  tau := (lr_tau, 0)
  abar := lr_abar
  A p q := (lr_A.getD p #[]).getD q 0
  r0 := lr_r0
  r1 := lr_r1

/-- The problem of the certificate is the Lorenz periodic orbit problem. -/
theorem lrData_toProblem : lrData.toProblem = lorenzLR := by
  have hf : (fun j => (lrData.f j).toMvC) = lorenzPOField := by
    funext j
    fin_cases j <;>
      simp [lrData, lorenzPolyData, lorenzPOField, PolyData.toMvC, PolyData.toMv,
        PolyData.termToMv_eq, Fin.prod_univ_succ, σ, ρ, β] <;>
      (try simp only [neg_div, map_neg]) <;> ring
  have hxi : (fun j => QC.toC (lrData.ξ j)) = lrXi := by
    funext j; exact QC.toC_ofRat _
  have hxihat : (fun j => QC.toC (lrData.ξhat j)) = lrXihat := by
    funext j
    refine (QC.toC_ofRat _).trans ?_
    fin_cases j <;> simp [lrXihatQ, lrXihat, lorenzPOField, lrXi, σ, ρ, β]
  simp only [FourierPeriodicData.toProblem, lorenzLR]
  rw [hf, hxi, hxihat]
  rfl

theorem one_le_lr_nu : (1 : ℝ) ≤ (lr_nu : ℝ) := by norm_num [lr_nu]

theorem lrData_xbar : lrData.xbar one_le_lr_nu = lrXbar one_le_lr_nu := by
  refine Prod.ext ?_ rfl
  exact QC.toC_ofRat _

theorem lr_check : lrData.check := by native_decide

/-- Theorem 10.2.12 with the data of Section 10.3 (`N = 35`, `ν = 9/8`): the periodic orbit problem
of the Lorenz system has a zero within `r₀` of `x̄ = (τ̄₀, ā)` in `ℂ × (ℓ¹_ν)³`, unique within
`r₁`. -/
theorem lorenz_LR :
    HasIsolatedZero (lorenzLR.F (lr_nu : ℝ) one_le_lr_nu) (lrXbar one_le_lr_nu) lr_r0 lr_r1 := by
  rw [← lrData_toProblem, ← lrData_xbar]
  exact lrData.verify one_le_lr_nu lr_check

/-! ### The periodic solution (Lemmas 10.2.2, 10.2.8–10.2.11) -/

theorem lr_symm : ∀ j : Fin 3, FourierSeq.IsSymm lr_N (lr_abar j) := by native_decide

theorem one_lt_lr_nu : (1 : ℝ) < (lr_nu : ℝ) := by norm_num [lr_nu]

theorem lorenzLR_isReal : lorenzLR.IsReal := by
  rw [← lrData_toProblem]
  refine ⟨fun j d => ?_, fun j => ?_, fun j => ?_⟩
  · simp only [FourierPeriodicData.toProblem, PolyData.toMvC, MvPolynomial.coeff_map,
      Complex.coe_algebraMap, Complex.star_def, Complex.conj_ofReal]
  · simp only [FourierPeriodicData.toProblem, lrData, QC.toC_ofRat, Complex.star_def,
      map_ratCast]
  · simp only [FourierPeriodicData.toProblem, lrData, QC.toC_ofRat, Complex.star_def,
      map_ratCast]

/-- The Lorenz field, with real arguments, written out. -/
theorem re_lorenzPOField (z : Fin 3 → ℝ) :
    (fun j => (MvPolynomial.eval (fun i => (z i : ℂ)) (lorenzPOField j)).re) =
      ![10 * (z 1 - z 0), 28 * z 0 - z 1 - z 0 * z 2, z 0 * z 1 - 8 / 3 * z 2] := by
  funext j
  fin_cases j <;> simp [lorenzPOField, σ, ρ, β]

/-- Lemma 10.2.2, Lemmas 10.2.8–10.2.11 and Theorem 10.2.12 with the data of Section 10.3: the
Lorenz system `x' = (10 (y - x), 28 x - y - x z, x y - (8/3) z)` has a periodic solution `γ` with
period `T`, `|T - 2π τ̄₀| < 2π r₀` (`τ̄₀ ≈ 0.24807`, `r₀ = 4.14 · 10⁻⁶`), within `r₀` (in each
component, for all `t`) of `∑_{|k| ≤ 35} ā_k e^{2πikt/T}`; in particular
`T ∈ [1.5586261983, 1.5586782232]` (with `3.14159265358979323846 < π < 3.14159265358979323847`), and `T`
is the smallest period of `γ` (no `T' ∈ (0, T)` is a period, since the first Fourier coefficient of `γ₁`
is nonzero: `|ã_{1,1} - ā_{1,1}| < r₀ < |ā_{1,1}|`). Its coefficients form the unique zero of the periodic orbit map within `r₁ = 10⁻⁵` of `x̄`. -/
theorem lorenz_LR_solution :
    ∃ x : FourierPeriodic.X 3 (lr_nu : ℝ) one_le_lr_nu,
      lorenzLR.F lr_nu one_le_lr_nu x = 0 ∧
      (∀ y ∈ closedBall (lrXbar one_le_lr_nu) lr_r1, lorenzLR.F lr_nu one_le_lr_nu y = 0 → y = x) ∧
      ∃ T : ℝ, 0 < T ∧ |T - 2 * Real.pi * lr_tau| < 2 * Real.pi * lr_r0 ∧
        1.5586261983 ≤ T ∧ T ≤ 1.5586782232 ∧
        ∃ γ : ℝ → Fin 3 → ℝ,
          (∀ t, HasDerivAt γ
            ![10 * (γ t 1 - γ t 0), 28 * γ t 0 - γ t 1 - γ t 0 * γ t 2,
              γ t 0 * γ t 1 - 8 / 3 * γ t 2] t) ∧
          (∀ t, γ (t + T) = γ t) ∧ (∀ T', 0 < T' → T' < T → ∃ t, γ (t + T') ≠ γ t) ∧
          ∀ t j, (γ t j : ℂ) = ∑' k, x.2 j k * Fourier.expI (2 * Real.pi * t / T) k ∧
            ‖(γ t j : ℂ) - FourierSeq.evalAt lr_N (lr_abar j) (2 * Real.pi * t / T)‖ < lr_r0 := by
  obtain ⟨x, hFx, huniq, T, hT0, hT, γ, hγd, hγp, hγe⟩ :=
    FourierPeriodic.exists_solution one_lt_lr_nu lorenzLR_isReal (xbar := lrXbar one_le_lr_nu)
      (τbar := lr_tau) (by simp [lrXbar]) (fun j => FourierSeq.conjX_toX (lr_symm j))
      (by norm_num [lr_r0, lr_r1]) (by norm_num [lr_r0, lr_tau]) lorenz_LR
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  obtain ⟨hT1, hT2⟩ := abs_lt.1 hT
  have hT1' : 1.5586261983 ≤ T := by norm_num [lr_tau, lr_r0] at hT1; linarith
  have hT2' : T ≤ 1.5586782232 := by norm_num [lr_tau, lr_r0] at hT2; linarith
  -- the first Fourier coefficient of `γ₁` is nonzero
  have hcoef : x.2 0 1 ≠ 0 := by
    obtain ⟨x₀, hx₀, hF₀, -⟩ := lorenz_LR
    have hxx : x₀ = x := huniq x₀ (Metric.closedBall_subset_closedBall
      (by norm_num [lr_r0, lr_r1]) (Metric.ball_subset_closedBall hx₀)) hF₀
    rw [← hxx]
    rw [Metric.mem_ball, dist_eq_norm] at hx₀
    have h1 : ‖(x₀ - lrXbar one_le_lr_nu).2 0 1‖ < lr_r0 := by
      have a1 := WeightedLp.norm_apply_le ((x₀ - lrXbar one_le_lr_nu).2 0) 1
      have a2 := norm_le_pi_norm (x₀ - lrXbar one_le_lr_nu).2 0
      have a3 := norm_snd_le (x₀ - lrXbar one_le_lr_nu)
      have hω : 1 ≤ Weights.geomInt (lr_nu : ℝ) one_le_lr_nu 1 := by
        rw [Weights.geomInt_apply]; norm_num [lr_nu]
      nlinarith [norm_nonneg ((x₀ - lrXbar one_le_lr_nu).2 0 1)]
    have h2 : (lr_r0 : ℝ) < ‖(lrXbar one_le_lr_nu).2 0 1‖ := by
      have hq : lr_r0 < |(FourierSeq.get lr_N (lr_abar 0) 1).1| := by native_decide
      have hq' : (lr_r0 : ℝ) < |((FourierSeq.get lr_N (lr_abar 0) 1).1 : ℝ)| := by exact_mod_cast hq
      refine hq'.trans_le ?_
      have := Complex.abs_re_le_norm ((lrXbar one_le_lr_nu).2 0 1)
      simpa [lrXbar] using this
    intro h0
    have e : (x₀ - lrXbar one_le_lr_nu).2 0 1 = x₀.2 0 1 - (lrXbar one_le_lr_nu).2 0 1 := by simp
    rw [e, h0, zero_sub, norm_neg] at h1
    linarith
  have hmin : ∀ T', 0 < T' → T' < T → ∃ t, γ (t + T') ≠ γ t := by
    intro T' h0 h1
    have hpi := Real.pi_pos
    obtain ⟨θ, hθ⟩ := Fourier.exists_ne_of_coeff_one_ne_zero hcoef (φ := 2 * Real.pi * T' / T)
      (div_pos (mul_pos (by positivity) h0) hT0) ((div_lt_iff₀ hT0).2 (by nlinarith))
    refine ⟨θ * T / (2 * Real.pi), fun h => hθ ?_⟩
    have hT' := hT0.ne'
    have e1 : 2 * Real.pi * (θ * T / (2 * Real.pi)) / T = θ := by field_simp
    have e2 : 2 * Real.pi * (θ * T / (2 * Real.pi) + T') / T = θ + 2 * Real.pi * T' / T := by
      field_simp
    have g1 := (hγe (θ * T / (2 * Real.pi) + T') 0).1
    have g2 := (hγe (θ * T / (2 * Real.pi)) 0).1
    rw [e2] at g1
    rw [e1] at g2
    rw [Fourier.fourierEval_apply, Fourier.fourierEval_apply, ← g1, ← g2, h]
  refine ⟨x, hFx, huniq, T, hT0, hT, hT1', hT2', γ, fun t => ?_, hγp, hmin, fun t j => ?_⟩
  · have := hγd t
    rwa [show lorenzLR.f = lorenzPOField from rfl, re_lorenzPOField] at this
  · obtain ⟨h1, h2⟩ := hγe t j
    refine ⟨h1, ?_⟩
    rwa [show (lrXbar one_le_lr_nu).2 j = FourierSeq.toX lr_N (lr_abar j) from rfl,
      FourierSeq.fourierEval_toX] at h2

/-! ## Section 10.4.1: the Hopf point of the Lorenz system -/

/-- The Hopf map of the Lorenz system, `X = (x, v₁, v₂, ρ, ω)`, with the phase vectors
`ξ₁ = hopf_xi1`, `ξ₂ = hopf_xi2`. -/
noncomputable def hopfMap (X : Fin 11 → ℝ) : Fin 11 → ℝ :=
  ![σ * (X 1 - X 0),
    X 9 * X 0 - X 1 - X 0 * X 2,
    X 0 * X 1 - β * X 2,
    -σ * X 3 + σ * X 4 + X 10 * X 6,
    (X 9 - X 2) * X 3 - X 4 - X 0 * X 5 + X 10 * X 7,
    X 1 * X 3 + X 0 * X 4 - β * X 5 + X 10 * X 8,
    -σ * X 6 + σ * X 7 - X 10 * X 3,
    (X 9 - X 2) * X 6 - X 7 - X 0 * X 8 - X 10 * X 4,
    X 1 * X 6 + X 0 * X 7 - β * X 8 - X 10 * X 5,
    hopf_xi1 0 * X 3 + hopf_xi1 1 * X 4 + hopf_xi1 2 * X 5 - 1,
    hopf_xi2 0 * X 6 + hopf_xi2 1 * X 7 + hopf_xi2 2 * X 8 - 1]

/-- The Hopf map as a quadratic system with rational coefficients:
`F(X)ᵢ = cᵢ + ∑ⱼ Lᵢⱼ Xⱼ + ∑ⱼ ∑ₖ Qᵢⱼₖ Xⱼ Xₖ`. -/
def hopf : QuadraticSystem ℚ 11 where
  c := ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1]
  L := !![-10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, -8 / 3, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, -10, 10, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, -8 / 3, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, -10, 10, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, -8 / 3, 0, 0;
      0, 0, 0, hopf_xi1 0, hopf_xi1 1, hopf_xi1 2, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, hopf_xi2 0, hopf_xi2 1, hopf_xi2 2, 0, 0]
  Q := ![!![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    !![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    !![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

theorem hopf_eval : (hopf.map (Rat.castHom ℝ)).eval = hopfMap := by
  funext X i
  fin_cases i <;>
    simp [eval, QuadraticSystem.map, hopf, hopfMap, σ, β, Fin.sum_univ_succ] <;> ring

/-- The derivative of the encoding is the derivative of the Hopf map. -/
theorem hopf_jac :
    (fun X => matCLM ((hopf.map (Rat.castHom ℝ)).jac X)) = fderiv ℝ hopfMap := by
  funext X
  rw [← hopf_eval]
  exact ((hopf.map (Rat.castHom ℝ)).hasFDerivAt X).fderiv.symm

/-- Section 10.4.1: the Hopf map of the Lorenz system has a nondegenerate zero within `r₀` of `X̄`
(sup norm), and it is the unique zero within `r₁`. The bounds are evaluated exactly; the book
prints the upper bounds `Y₀ = 1.72 × 10⁻¹⁴`, `Z₀ = 7.37 × 10⁻¹⁴`, `Z₂ = 334`. -/
theorem hopf_point :
    ∃ X ∈ ball (castVec hopf_Xbar) hopf_r0, IsNondegenerateZero hopfMap (fderiv ℝ hopfMap) X ∧
      ∀ Y ∈ closedBall (castVec hopf_Xbar) hopf_r1, hopfMap Y = 0 → Y = X := by
  have h := radii_poly_two_radii_exact hopf hopf_A hopf_Xbar (r₀ := hopf_r0) (r₁ := hopf_r1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rwa [hopf_eval, hopf_jac] at h

/-- If a complex `3 × 3` matrix has two distinct eigenvalues `μ ≠ μ'`, then the roots of its
characteristic polynomial, with multiplicity, are `μ`, `μ'` and `tr A - μ - μ'`. -/
theorem charpoly_roots_of_two_eigenvalues (A : Matrix (Fin 3) (Fin 3) ℂ) {μ μ' : ℂ}
    {v w : Fin 3 → ℂ} (hv : v ≠ 0) (hAv : A.mulVec v = μ • v) (hw : w ≠ 0)
    (hAw : A.mulVec w = μ' • w) (hne : μ ≠ μ') :
    A.charpoly.roots = {μ, μ', A.trace - μ - μ'} := by
  have hroot : ∀ {c : ℂ} {u : Fin 3 → ℂ}, u ≠ 0 → A.mulVec u = c • u → c ∈ A.charpoly.roots :=
    fun {c u} hu hAu => by
      rw [Polynomial.mem_roots A.charpoly_monic.ne_zero, Polynomial.IsRoot, Matrix.eval_charpoly,
        ← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨u, hu, ?_⟩
      rw [Matrix.sub_mulVec, hAu, Matrix.scalar_apply]
      ext i
      simp
  have hc : A.charpoly.roots.card = 3 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem (hroot hv hAv)
  have h2 : μ' ∈ s := by
    have := hroot hw hAw
    rw [hs, Multiset.mem_cons] at this
    exact this.resolve_left (Ne.symm hne)
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem h2
  have ht1 : t.card = 1 := by
    rw [hs, ht, Multiset.card_cons, Multiset.card_cons] at hc
    omega
  obtain ⟨c, rfl⟩ := Multiset.card_eq_one.1 ht1
  have htr := Matrix.trace_eq_sum_roots_charpoly A
  rw [hs, ht] at htr ⊢
  simp only [Multiset.sum_cons, Multiset.sum_singleton] at htr
  rw [show A.trace - μ - μ' = c by rw [htr]; ring]
  rfl

/-- The Jacobian `D_x f(x, ρ)` of the Lorenz field at `x = (X₀, X₁, X₂)`, `ρ = X₉`. -/
noncomputable def hopfJac (X : Fin 11 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-σ, σ, 0; X 9 - X 2, -1, -X 0; X 1, X 0, -β]

/-- Section 10.4.1, the eigenvalues: at the zero `X̃ = (x̃, ṽ₁, ṽ₂, ρ̃, ω̃)` of the Hopf map,
`|ρ̃ - ρ̄| < r₀`, `|ω̃ - ω̄| < r₀`, so `ω̃ ≠ 0`; rows 4–9 give `D_x f(x̃, ρ̃)(ṽ₁ ± i ṽ₂) = ±i ω̃ (ṽ₁ ± i ṽ₂)`,
`ṽ₁ ± i ṽ₂ ≠ 0` by the phase condition (the eigenvalue part of Theorem 10.4.3), and the trace
`-(σ + 1 + β) = -41/3` gives the third eigenvalue: the eigenvalues of `D_x f(x̃, ρ̃)`, with
multiplicity, are `iω̃`, `-iω̃` and `-41/3`. -/
theorem hopf_point_eigenvalues :
    ∃ X ∈ ball (castVec hopf_Xbar) hopf_r0, hopfMap X = 0 ∧
      |X 9 - hopf_Xbar 9| < hopf_r0 ∧ |X 10 - hopf_Xbar 10| < hopf_r0 ∧ X 10 ≠ 0 ∧
      ((hopfJac X).map (algebraMap ℝ ℂ)).charpoly.roots =
        {Complex.I * X 10, -(Complex.I * X 10), -41 / 3} := by
  obtain ⟨X, hX, hnd, -⟩ := hopf_point
  have h0 := hnd.1
  have hb : ∀ i, |X i - hopf_Xbar i| < hopf_r0 := fun i => by
    rw [mem_ball, dist_eq_norm] at hX
    have := (norm_le_pi_norm (X - castVec hopf_Xbar) i).trans_lt hX
    simpa [castVec, Real.norm_eq_abs] using this
  have hω : X 10 ≠ 0 := fun h => by
    have := hb 10
    rw [h] at this
    norm_num [hopf_Xbar, hopf_r0, abs_of_neg] at this
  have e : ∀ i, hopfMap X i = 0 := fun i => by rw [h0]; rfl
  have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7; have e8 := e 8
  have e9 := e 9
  simp [hopfMap] at e3 e4 e5 e6 e7 e8 e9
  set A := (hopfJac X).map (algebraMap ℝ ℂ)
  set v : Fin 3 → ℂ := ![X 3 + Complex.I * X 6, X 4 + Complex.I * X 7, X 5 + Complex.I * X 8]
  set w : Fin 3 → ℂ := ![X 3 - Complex.I * X 6, X 4 - Complex.I * X 7, X 5 - Complex.I * X 8]
  have hv : v ≠ 0 := fun h => by
    have h3 := congrArg (fun z => (z 0).re) h; have h4 := congrArg (fun z => (z 1).re) h
    have h5 := congrArg (fun z => (z 2).re) h
    simp [v] at h3 h4 h5
    rw [h3, h4, h5] at e9; norm_num at e9
  have hw : w ≠ 0 := fun h => by
    have h3 := congrArg (fun z => (z 0).re) h; have h4 := congrArg (fun z => (z 1).re) h
    have h5 := congrArg (fun z => (z 2).re) h
    simp [w] at h3 h4 h5
    rw [h3, h4, h5] at e9; norm_num at e9
  have hAv : A.mulVec v = (Complex.I * X 10) • v := by
    ext i
    fin_cases i <;> apply Complex.ext <;>
      simp [A, v, hopfJac, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> linarith
  have hAw : A.mulVec w = (-(Complex.I * X 10)) • w := by
    ext i
    fin_cases i <;> apply Complex.ext <;>
      simp [A, w, hopfJac, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> linarith
  have hne : Complex.I * X 10 ≠ -(Complex.I * X 10) := fun h => by
    have := congrArg Complex.im h
    simp at this
    exact hω (by linarith)
  have htr : A.trace = -41 / 3 := by
    simp [A, hopfJac, Matrix.trace_fin_three, σ, β]
    norm_num
  refine ⟨X, hX, h0, hb 9, hb 10, hω, ?_⟩
  rw [charpoly_roots_of_two_eigenvalues A hv hAv hw hAw hne, htr, sub_neg_eq_add,
    sub_add_cancel]

end LeanearizedODEs.Ch10
