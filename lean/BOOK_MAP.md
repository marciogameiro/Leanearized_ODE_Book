# BOOK_MAP: book results ↔ Lean declarations

Book: `LeanearizedODEs/book_radii_polynomials/Chapter_N.tex` (numbering as in the compiled chapters).

Layers: `existence` = formalized in the first phase; `interpretation` = zero of F ⇒ ODE
solution (`(later)`: not yet formalized); `Mathlib (statement only)` = taken from Mathlib, not reproved;
`example (certificate)` = proved from the data in `code/certificates/`; `definition` = becomes a
Lean definition.

Library names (`WeightedLp.…`, `ChebBVP.…`, …) are in namespace `RadiiPolynomial` (library
`RadiiPolynomial`); the example theorems `ChNN.…` are in namespace `LeanearizedODEs` (this project,
`LeanearizedODEs/ChNN.lean`). "proved" = declared and proved (no `sorry`);
"stated, proof pending" = the declaration exists
with a `sorry` proof; "defined" = the definition exists; "(tentative)" = planned name, not declared yet.
Trust: the Chapter 2 examples and the Hopf point (§10.4.1) are checked by the kernel only
(`decide +kernel`); the Chapter 8, 13 and 14-15 examples, the Helmholtz-Duffing example (§10.1) and
the periodic orbit LR (§10.3)
are checked by compiled code
(`native_decide`, which also trusts the Lean compiler).

## Chapter 2

| No. | Kind | Label | Lean | Layer |
|---|---|---|---|---|
| 2.1.1 | Definition | `defn:complete_metric_space` | — | definition |
| 2.1.2 | Definition | `defn:contraction` | — | definition |
| 2.1.3 | Theorem (Contraction Mapping Theorem) | `thm:contractionMapping` | — | Mathlib (statement only) |
| 2.2.1 | Definition | `def:operator_norm` | — | definition |
| 2.2.2 | Proposition | `prop:operatorBounds` | — | Mathlib (statement only) |
| 2.2.3 | Proposition | `prop:infinityMatrixNorm` | `norm_matCLM_le` — proved | Mathlib (statement only) |
| 2.2.4 | Corollary (The mean value inequality) | `cor:mean_value_inequality` | — | Mathlib (statement only) |
| 2.3.1 | Proposition | `prop:fixed_point` | `sub_apply_eq_self_iff` — proved | existence |
| 2.3.2 | Definition | `defn:nondegenerateZero` | `IsNondegenerateZero` — defined | definition |
| 2.4.1 | Lemma | `lem:finiteDimInvertible` | `isInvertible_of_norm_id_sub_comp_lt_one` — proved | existence |
| 2.4.2 | Theorem | `th:radiiFiniteDim` | `radii_poly_finiteDim` + `radii_poly_finiteDim_two_radii` — proved | existence |
| 2.4.3 | Definition | `defn:radiipolynomial` | `radiiPoly` — defined | definition |
| 2.4.4 | Example | `ex:2d_example` | `parabolas_zero_1` + `parabolas_zero_2` + `parabolas_zero_3` + `parabolas_zero_4` — proved | example (certificate) |
| 2.4.5 | Example | `ex:equilibria_Lorenz` | `lorenz_equilibrium` — proved | example (certificate) |

## Chapter 7

| No. | Kind | Label | Lean | Layer |
|---|---|---|---|---|
| 7.1.1 | Definition | (unlabeled) | — | definition |
| 7.1.2 | Proposition | `prop:productBanach` | — | Mathlib (statement only) |
| 7.1.3 | Definition | (unlabeled) | — | definition |
| 7.1.4 | Proposition | `prop:IminusMInjective` | `injective_of_norm_id_sub_lt_one` — proved | existence |
| 7.1.5 | Proposition | `prop:linearOpBound` | — | Mathlib (statement only) |
| 7.1.6 | Proposition | `prop:normSubmultiplicative` | — | Mathlib (statement only) |
| 7.2.1 | Definition | (unlabeled) | — | definition |
| 7.2.2 | Proposition | `prop:derivativeRules` | — | Mathlib (statement only) |
| 7.2.3 | Proposition | `prop:DG(x_0)=ADF(x_0)` | — | Mathlib (statement only) |
| 7.2.4 | Corollary | `cor:derivativeNewtonOperator` | — | existence |
| 7.2.5 | Theorem (Mean Value Inequality) | `thm:MeanValue` | — | Mathlib (statement only) |
| 7.3.1 | Lemma (Regrouping) | `lem:regrouping` | — | Mathlib (statement only) |
| 7.3.2 | Definition | `def:weighted_ellp` | `WeightedLp` — defined | definition |
| 7.3.3 | Lemma | `lem:weightedSumIsNorm` | `WeightedLp.toLpEquiv` — proved | existence |
| 7.3.4 | Theorem | `thm:sequenceBanachSpace` | `WeightedLp.instCompleteSpace` — proved | existence |
| 7.3.5 | Definition | `def:ellnuN` | `Weights.geom` — defined | definition |
| 7.3.6 | Definition | `def:ellnuZ` | `Weights.geomInt` — defined | definition |
| 7.3.7 | Lemma | `lem:dualityBound` | `WeightedL1.norm_tsum_mul_le` — proved | existence |
| 7.3.8 | Proposition | `prop:colNormBound` | `ColNormBound.toCLM` + `ColNormBound.norm_toCLM_le` — proved | existence |
| 7.4.1 | Definition | `defn:banachAlgebra` | — | definition |
| 7.4.2 | Definition | `defn:convolution` | `Convolution.conv` — defined | definition |
| 7.4.3 | Definition | `defn:submultiplicative` | `Weights.IsSubmultiplicative` — defined | definition |
| 7.4.4 | Theorem | `thm:convolutionBanachAlgebra` | `WeightedL1.instNormedCommRing` + `WeightedL1.instNormedAlgebra` — proved | existence |
| 7.4.5 | Corollary | `thm:l1BanachAlgebra` | `Weights.geom` + `Convolution.conv_nat` — proved | existence |
| 7.4.6 | Corollary | `thm:l2BanachAlgebra` | `Weights.geomInt` + `Convolution.conv_int` — proved | existence |
| 7.4.7 | Corollary | `cor:powerSeriesProduct` | `WeightedL1.powerSeriesEval_mul` + `WeightedL1.powerSeriesEval_prod_pow` — proved | existence |
| 7.4.8 | Theorem (Young's inequality) | `thm:young` | `Convolution.summable_fiber_Lp` + `Convolution.convLp` + `Convolution.norm_convLp_le` — proved | existence |
| 7.4.9 | Lemma (Product rule) | `lem:productRule` | — | Mathlib (statement only) |
| 7.4.10 | Theorem | `thm:banachAlgebras_differentiation` | — | Mathlib (statement only) |
| 7.5.1 | Proposition | `prop:productOperatorNorm` | `norm_blockCLM_le` — proved | existence |
| 7.5.2 | Theorem | `thm:polynomialDifferentiable` | `hasFDerivAt_aeval` + `hasFDerivAt_aeval_pi` — proved | existence |
| 7.6.1 | Theorem (Radii polynomial approach on Banach spaces) | `thm:radPolyBanach` | `radii_poly` — proved | existence |
| 7.6.2 | Corollary | `cor:radPolyTwoRadii` | `radii_poly_two_radii` — proved | existence |
| 7.6.3 | Remark | `rem:radPolyApplication` | — | remark |
| 7.6.4 | Proposition | `prop:AisInjective` | `injective_of_decomposition` — proved | existence |

## Chapter 8

| No. | Kind | Label | Lean | Layer |
|---|---|---|---|---|
| 8.1.1 | Lemma | `lem:solvesIVP` | `TaylorIVP.sol_zero` + `TaylorIVP.hasDerivAt_sol` + `TaylorIVP.continuousOn_sol` + `TaylorIVP.exists_solution` — proved | interpretation |
| 8.1.2 | Lemma | `lem:IVPunique` | `eqOn_Ioo_of_lipschitzOnWith_closedBall` + `lipschitzOnWith_aeval_pi` + `TaylorIVP.exists_unique_solution` — proved | interpretation |
| 8.1.3 | Proposition | `prop:rangeDerivative` | `Taylor.diffOp` + `Taylor.norm_diffOp_le` + `Taylor.norm_incl_le` — proved | existence |
| 8.1.4 | Proposition | `prop:scalarIVPoperators` | `TaylorIVP.opA` + `TaylorIVP.opD` — proved | existence |
| 8.1.5 | Theorem | `thm:NewtonFx(1-x)` | `TaylorIVP.radii_poly_two_radii` — proved | existence |
| 8.1.6 | Lemma | `lem:NewtonFx(1-x)Y0` | `TaylorIVP.norm_opA_F_le` — proved | existence |
| 8.1.7 | Lemma | `lem:NewtonFx(1-x)Z0` | `TaylorIVP.norm_id_sub_opA_opD_le` — proved | existence |
| 8.1.8 | Lemma | `lem:NewtonFx(1-x)Z1` | `TaylorIVP.norm_opA_DF_sub_opD_le` — proved | existence |
| 8.1.9 | Lemma | `lem:NewtonFx(1-x)Z2` | `TaylorIVP.norm_opA_DF_sub_DF_le` — proved | existence |
| 8.2.1 | Lemma | `lem:solvesIVPsystem` | `TaylorIVP.eval_sol` + `TaylorIVP.hasDerivAt_sol` + `TaylorIVP.continuousOn_sol` + `TaylorIVP.abs_sol_sub_le` + `TaylorIVP.exists_solution` + `TaylorIVP.exists_unique_solution` — proved | interpretation |
| 8.2.2 | Lemma | `lem:somenorms` | `Taylor.norm_shift_le` + `TaylorIVP.tailA_le` — proved | existence |
| 8.2.3 | Lemma | `lem:Aisinvertible` | `TaylorIVP.opA_injective` — proved | existence |
| 8.2.4 | Proposition | `prop:AF:X->X_ivp` | `TaylorIVP.hasFDerivAt_F` + `TaylorIVP.opA` + `TaylorIVP.opD` — proved | existence |
| 8.2.5 | Lemma | `eq:systemNewtonY0` | `TaylorIVP.norm_opA_F_le` — proved | existence |
| 8.2.6 | Lemma | `lem:ivptaylorZ0` | `TaylorIVP.norm_id_sub_opA_opD_le` — proved | existence |
| 8.2.7 | Lemma | `eq:systemNewtonZ1` | `TaylorIVP.norm_opA_DF_sub_opD_le` — proved | existence |
| 8.2.8 | Lemma | `eq:systemNewtonZ2` | `TaylorIVP.norm_opA_DF_sub_DF_le` — proved | existence |
| 8.2.9 | Theorem | `thm:TaylorIVPsystem` | `TaylorIVP.radii_poly_two_radii` — proved | existence |
| §8.1 | Example (x₀ = 1/2, 1/4, 3/4) | `sec:scalarIVP` | `Ch08.scalar_ivp_half` + `Ch08.scalar_ivp_quarter` + `Ch08.scalar_ivp_threeQuarters` + `Ch08.scalar_solution_half` + `Ch08.scalar_solution_quarter` + `Ch08.scalar_solution_threeQuarters` — proved | example (certificate) |
| §8.3 | Example (Lorenz) | `sec:LorenzIVP` | `Ch08.lorenz_ivp` + `Ch08.lorenz_solution` — proved | example (certificate) |

## Chapter 10

| No. | Kind | Label | Lean | Layer |
|---|---|---|---|---|
| 10.1.1 | Lemma | `lem:helmholtzformal` | `QuadraticFourier.solves_of_F_eq_zero` — proved | interpretation |
| 10.1.2 | Proposition | `prop:rangeDerivative_fourier` | `QuadraticFourier.diag` + `QuadraticFourier.incl` — proved | existence |
| 10.1.3 | Lemma | `lem:helmholtzSetup` | `QuadraticFourier.hasFDerivAt_F` + `QuadraticFourier.TailCond` + `Ch10.helm_tail` + `QuadraticFourier.opA` + `QuadraticFourier.opD` + `QuadraticFourier.opA_incl` + `QuadraticFourier.opA_injective` — proved | existence |
| 10.1.4 | Proposition | `prop:helmholtzreal` | `QuadraticFourier.conjX_eq_of_isolatedZero` + `Fourier.ofReal_re_fourierEval` — proved | interpretation |
| 10.1.5 | Theorem | `thm:helmholtzradii` | `QuadraticFourier.radii_poly_two_radii` + `QuadraticFourier.exists_solution` — proved | existence |
| 10.1.6 | Proposition | `prop:auxGamma` | `Fourier.sum_center_mul_le` — proved | existence |
| 10.1.7 | Lemma | `lem:helmholtzZ1` | `QuadraticFourier.norm_opA_DF_sub_opD_le` — proved | existence |
| 10.2.1 | Definition | `defn:periodicOrbit` | — | definition |
| 10.2.2 | Lemma | `lem:fourierformal` | `FourierPeriodic.hasDerivAt_orbit` + `FourierPeriodic.orbit_add_period` — proved | interpretation |
| 10.2.3 | Lemma | `lem:fourierSetup` | `FourierPeriodic.hasFDerivAt_F` + `FourierPeriodic.opA` + `FourierPeriodic.opD` + `FourierPeriodic.opA_injective` + `ParamTail.injective_op` — proved | existence |
| 10.2.4 | Lemma | `lem:systemFourierY0` | `FourierPeriodic.norm_opA_F_le` — proved | existence |
| 10.2.5 | Lemma | `lem:systemFourierZ0` | `FourierPeriodic.norm_id_sub_opA_opD_le` + `ParamTail.id_sub_op_comp_op` + `ParamTail.norm_op_le` — proved | existence |
| 10.2.6 | Lemma | `lem:systemFourierZ1` | `FourierPeriodic.norm_opA_DF_sub_opD_le` — proved | existence |
| 10.2.7 | Lemma | `lem:systemFourierZ2` | `FourierPeriodic.norm_opA_DF_sub_DF_le` — proved | existence |
| 10.2.8 | Lemma | `lem:convolutionconjugation` | `Fourier.conjX_mul` — proved | interpretation |
| 10.2.9 | Lemma | `eq:symmetryF` | `FourierPeriodic.F_conjXP_eq_zero` + `Fourier.conjX_aeval` — proved | interpretation |
| 10.2.10 | Lemma | `eq:symmetryB` | `FourierPeriodic.norm_conjXP` — proved | interpretation |
| 10.2.11 | Lemma | `lem:fourierSymmetricZero` | `FourierPeriodic.conjXP_eq_of_isolatedZero` — proved | interpretation |
| 10.2.12 | Theorem | `thm:fourierPeriodicOrbits` | `FourierPeriodic.radii_poly_two_radii` + `FourierPeriodic.exists_solution` — proved | existence |
| 10.4.1 | Theorem (Hopf Bifurcation Theorem) | `thm:hopf_bifurcation` | — | not formalized (classical, cited) |
| 10.4.2 | Definition | `def:hopf_bifurcation` | — | not formalized (classical, cited) |
| 10.4.3 | Theorem | `thm:nondegenerate_Hopf` | — | not formalized (classical, cited) |
| 10.5.1 | Lemma | `lem:fourierProduct` | `WeightedL1.charEval` + `WeightedL1.tsum_conv_mul_char` + `Fourier.fourierEval` — proved | interpretation |
| 10.5.2 | Lemma (Derivative of Fourier Series) | `lem:DerivativeFourier` | `Fourier.derivX` + `Fourier.hasDerivAt_fourierEval` — proved | interpretation |
| 10.5.3 | Lemma (Fourier coefficients) | `lem:fourierCoefficients` | `Fourier.integral_fourierEval_mul_expI` + `Fourier.eq_of_fourierEval_eq` + `Fourier.coeff_mul_expI_eq_of_periodic` + `Fourier.exists_ne_of_coeff_one_ne_zero` — proved | interpretation |
| §10.1 | Example (Helmholtz–Duffing, N = 10, ν = 5/4) | `sec:PeriodicOrbitForcing` | `Ch10.helmholtz_duffing` + `Ch10.helmholtz_solution` — proved | example (certificate) |
| §10.3 | Example (periodic orbit LR of Lorenz, N = 35, ν = 9/8) | `sec:ps_lorenz` | `Ch10.lorenz_LR` + `Ch10.lorenz_LR_solution` — proved | example (certificate) |
| §10.4.1 | Example (Hopf point of Lorenz) | `sec:Hopf_bifurcation` | `Ch10.hopf_point` + `Ch10.hopf_point_eigenvalues` — proved | example (certificate) |

## Chapter 13

| No. | Kind | Label | Lean | Layer |
|---|---|---|---|---|
| 13.1.1 | Lemma | `lem:SH_symmetric_convolution` | `Cosine.mul3` + `Cosine.norm_mul3_le` + `Cosine.cube_add` — proved | existence |
| 13.1.2 | Proposition | `prop:A_norm` | `FiniteTail.op1` + `FiniteTail.norm_op1_le` — proved | existence |
| 13.1.3 | Lemma | `lem:SH_mu_tail` | `Ch13.sh_tail` — proved | existence |
| 13.1.4 | Proposition | `prop:SH_setting` | `CubicCosine.hasFDerivAt_F` + `CubicCosine.opA` + `CubicCosine.opD` + `CubicCosine.opA_incl` — proved | existence |
| 13.1.5 | Lemma | `lem:SH_bounds` | `CubicCosine.norm_opA_F_le` + `CubicCosine.norm_id_sub_opA_opD_le` + `CubicCosine.norm_opA_DF_sub_opD_le` + `CubicCosine.norm_opA_DF_sub_DF_le` — proved | existence |
| 13.1.6 | Theorem (Radii polynomial for Swift-Hohenberg equilibria) | `thm:SH_radii_polynomial` | `CubicCosine.radii_poly_two_radii` — proved | existence |
| 13.1.7 | Remark | `rem:SH_upper_bounds` | — | remark |
| 13.1.8 | Remark | `rem:SH_equilibrium` | `CubicCosine.summable_pow_four` + `CubicCosine.equilibrium_of_F_eq_zero` + `CubicCosine.exists_equilibrium` — proved | interpretation |
| §13.1.3 | Example (Table 13.1, λ = 1) | `fig:data_proof_SH` | `Ch13.sh_lambda1_nu1` + `Ch13.sh_lambda1_nu2` + `Ch13.sh_lambda1_nu4` + `Ch13.sh_lambda1_nu5` + `Ch13.sh_lambda1_nu1_equilibrium` + `Ch13.sh_lambda1_nu2_equilibrium` + `Ch13.sh_lambda1_nu4_equilibrium` + `Ch13.sh_lambda1_nu5_equilibrium` + `Ch13.sh_lambda1_conclusions` — proved | example (certificate) |
| §13.1.3 | Example (Table 13.1, λ = 10) | `fig:data_proof_SH` | `Ch13.sh_lambda10_nu1` + `Ch13.sh_lambda10_nu3_2` + `Ch13.sh_lambda10_nu2` + `Ch13.sh_lambda10_nu75_32` + `Ch13.sh_lambda10_nu1_equilibrium` + `Ch13.sh_lambda10_nu3_2_equilibrium` + `Ch13.sh_lambda10_nu2_equilibrium` + `Ch13.sh_lambda10_nu75_32_equilibrium` + `Ch13.sh_lambda10_conclusions` — proved | example (certificate) |

## Chapter 14

| No. | Kind | Label | Lean | Layer |
|---|---|---|---|---|
| 14.1.1 | Definition | `def:cheb_poly` | — | definition |
| 14.1.2 | Proposition | `prop:chebyshev_are_fourier_in_disguise` | `Chebyshev.chebSeries_cos` — proved | interpretation |
| 14.2.1 | Definition | `def:cheb_product` | `Chebyshev.mul_apply` — defined | definition |
| 14.2.2 | Lemma | `lem:cheb_banach_algebra` | `Chebyshev.instNormedCommRing` + `Chebyshev.norm_symExt` + `Chebyshev.continuousOn_chebSeries` + `Chebyshev.abs_chebSeries_le_norm` + `Chebyshev.chebSeries_mul` — proved | existence |
| 14.2.3 | Corollary | `cor:cheb_phi` | `Chebyshev.chebSeries_aeval` + `norm_aeval_le` — proved | existence |
| 14.2.4 | Lemma | `lem:cheb_integration` | `Chebyshev.integral_chebSeries` + `Chebyshev.hasDerivWithinAt_chebSeries` — proved | interpretation |
| 14.3.1 | Lemma | `lem:IVP_operator_smooth` | `ChebBVP.hasFDerivAt_F` — proved | existence |
| 14.3.2 | Lemma | `lem:IVP_equivalence` | `ChebBVP.solves_of_F_eq_zero` + `ChebBVP.exists_ivp_solution` + `eqOn_Icc_of_lipschitzOnWith_closedBall` — proved | interpretation |
| 14.4.1 | Theorem | `thm:cheb_IVP_bounds` | `ChebBVP.radii_poly_two_radii` + `ChebBVP.ivp_F_apply_zero` — proved | existence |
| 14.5.1 | Example | `ex:cheb_scalar_IVP` | `Ch14.scalar_ivp` + `Ch14.scalar_solution` — proved | example (certificate) |
| 14.5.2 | Example | `ex:cheb_Lorenz_IVP` | `Ch14.lorenz_ivp` + `Ch14.lorenz_solution` — proved | example (certificate) |

## Chapter 15

| No. | Kind | Label | Lean | Layer |
|---|---|---|---|---|
| 15.1.1 | Lemma | `lem:BVP_equivalence` | `ChebBVP.solves_of_F_eq_zero` + `ChebBVP.exists_solution` — proved | interpretation |
| 15.1.2 | Theorem | `thm:cheb_BVP_bounds` | `ChebBVP.radii_poly_two_radii` — proved | existence |
| 15.1.3 | Example | `ex:cheb_BVP_Chafee_Infante` | `Ch15.chafee_infante_bvp` + `Ch15.chafee_infante_solution` — proved | example (certificate) |

## Chapter 19

| No. | Kind | Label | Lean | Layer |
|---|---|---|---|---|
| 19.1.1 | Definition | `defn:metric_space` | — | definition |
| 19.2.1 | Definition | `defn:vector_norm` | — | definition |
| 19.2.2 | Definition | `defn:banach_space` | — | definition |
| 19.2.3 | Definition | `defn:equivalent_norms` | — | definition |
| 19.2.4 | Proposition | `prop:normEquiv` | — | Mathlib (statement only) |
