# RadiiPolynomial Module Architecture

The repository follows the mathematical dependency chain

```text
Algebra + Analysis
        |
        v
Core radii-polynomial method + reusable operators
        |
        v
Application discretizations
        |
        v
Concrete examples and certificates
```

`Certification` and `Tactic` are adapter layers. They may consume the mathematical
layers, but the mathematical layers must not depend on them.

## Directories

| Directory | Mathematical role |
| --- | --- |
| `Algebra/Convolution` | Mathlib's discrete convolution (`Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution`: `mulFiber`, `convolution`, `ringConvolution` and their laws) re-exported through `Basic`; library-owned, in `RadiiPolynomial.DiscreteConvolution`: the fiber equivalences (`mulFiberEquiv`, `sigmaMulFiberEquiv`), the point mass `delta` (`delta_eq_single`), the two-atom rule `single_ringConvolution_single` (any monoid index, additive `ℤ` included), triple-fiber associativity (`ringConvolution_assoc` under explicit summability, via the `HasSum` transfers `hasSum_sigma_leftMulAssoc`/`hasSum_sigma_rightMulAssoc`), the operation equality `ringConvolution_eq_finiteMulConvolution` with the finite-fiber convolution on indices with `Finset.HasMulAntidiagonal` (an equality of operations on `M → R`, not of carriers), and their additive twins (`Basic`, `Ring`); the topology-free finite-fiber core `Finite` (`finiteMulConvolution` over any `Mul` index with `Finset.HasMulAntidiagonal`, `finiteAddConvolution` by `to_additive`; laws at their weakest hypotheses, including the general-coefficient atom laws `single_one_left_apply`/`single_one_right_apply` and the map law `map_finiteMulConvolution`), of which the module `CauchyProduct` (definition `cauchyProduct`) is the natural-index specialization (`cauchyProduct_eq_finiteAddConvolution`), with the coefficient view `toPowerSeries` into `PowerSeries R` and its bundled `S`-linear equivalence `toPowerSeriesLinearEquiv`, real-free (no `Mathlib.Basic.Real.Basic` in its closure); the adapter `CauchyProductReal` owns the one real-number specialization `cauchyProduct.ratCast` (the cast `ℚ → ℝ` through the Cauchy product, from `cauchyProduct.map_cauchyProduct`), imported by the hub and explicitly by its consumer `Algebra/Polynomial/MvPolynomial/WeightedL1`; the topology-free wrapper `FiniteFiber` (imports only `Finite` and Mathlib algebra): the `def` synonyms `FiniteFiberConvolution M R` / `FiniteFiberAddConvolution M R` of all functions `M → R` with pointwise additive/module data, the convolution `Mul`, the unit `single 1 1` (`single 0 1`), the semiring and ring branches from `NonUnitalNonAssocSemiring` to `CommRing` (finite fibers explicit on every branch, `DecidableEq M` on the unital ones) and `Algebra S`; computation face `coeff`, extensionality by all coefficients; no instance on raw `M → R`; the power-series connections `FiniteFiber/PowerSeries` (imports `FiniteFiber`, `CauchyProduct` and Mathlib's power series; no topology): the ring equivalences `FiniteFiberAddConvolution.toPowerSeriesRingEquiv : FiniteFiberAddConvolution ℕ R ≃+* PowerSeries R` (forward map = `cauchyProduct.toPowerSeries`, `[Semiring R]` only) and `FiniteFiberAddConvolution.toMvPowerSeriesRingEquiv : FiniteFiberAddConvolution (σ →₀ ℕ) R ≃+* MvPowerSeries σ R` (identity on coefficients, explicit `[DecidableEq σ]`, no finiteness of `σ`), with scalar compatibility for every `[Module S R]`; the topology-free connection `FiniteFiber/MonoidAlgebra` (imports `FiniteFiber`, `Mathlib.Algebra.MonoidAlgebra.Defs`, `Mathlib.Algebra.Ring.Subsemiring.Basic`): the injective ring homomorphism `ofMonoidAlgebra R M : MonoidAlgebra R M →+* FiniteFiberConvolution M R` (additive twin `ofAddMonoidAlgebra`), its range characterized as the finitely supported elements (`mem_rangeS_ofMonoidAlgebra`, one closure package: `RingHom.rangeS`), and the ring isomorphism `ofMonoidAlgebraEquivRangeS` onto that range with the noncomputable inverse `toMonoidAlgebra` (`Finsupp.ofSupportFinite`); not generally onto (onto on a finite index and with one-element coefficients; tests only); the bridge `cauchyProduct.eq_addRingConvolution` to Mathlib's additive-index ring convolution (`Ring`) |
| `Algebra/Polynomial` | Semantic `MvPolynomial` calculus and computable `CompPoly` syntax, with Taylor and finite Laurent/Chebyshev interpreters, and certificate constants read off the syntax (`CompPoly/Bounds`, `CompPoly/Chebyshev/Bounds`: `normBound`, `lipschitzBound`, `derivativeBound`) |
| `Algebra/Ring` | Mathlib-only ring identities for an idempotent head `P` and its complement `1 - P` (`HeadTailIdentities`: composition, defect and inverse-defect identities) |
| `Algebra/Rees/Laurent` | Laurent/\|k\|-filtered Rees family `U R ⊆ R[X][T;T⁻¹]` with its atoms, tail ideal and structure constants (`Family`); the Euler derivation and the finite-core diagonal/cutoff calculus with the tail-inverse criterion and the specialization ring hom `specU t : U R →+* R[T;T⁻¹]` (coefficientwise evaluation at `t`, carrying `deltaU`, `qDelta`, `PH` to `deltaL` and the multipliers `diagL`) (`Euler`; only its four operator-level identities `PH_comp_one_sub`, `one_sub_comp_PH`, `PH_qDelta_tail`, `PH_add_qDelta_tail` sit in the documented local-instance section `Selection`, every other statement uses the default instances); the carrier-free Γ exponent identities and the real inverse bound `gammaW_inv_le` (`Gamma`, `GammaCutoff`); Mathlib-only |
| `Analysis/Calculus` | One Mathlib-only bridge on coordinate projections, `fderiv_pi_apply` (`Pi`, `@[simp]`); differentiability of a projection is Mathlib's `@[fun_prop] differentiable_apply` |
| `Analysis/Norm` | Carrier-neutral finite-sum inequalities in `RadiiPolynomial.NormHelpers` (`FiniteSum`, Mathlib-only imports): real-valued (weighted triangle, uniform factor, index swap) and normed-ring (`norm_sum_mul_pi_le`: `‖∑ i, f i * h i‖ ≤ (∑ i, ‖f i‖) * ‖h‖` over any `NonUnitalSeminormedRing`), the single proof home of that bound, of which the two `MvPolyBridge` names are consumer-compatibility faces |
| `Analysis/SequenceSpace/WeightedL1` | Generic weighted `l1` sequence spaces whose one fiber datum is the chosen frame `FiberTrivialization 𝕜 M E` (`FiberTrivialization`, independent of `lpOneAlg`): linear equivalences `θ_m : 𝕜 ≃ₗ[𝕜] E m`, bundled as continuous linear equivalences `equivL`, with the derived atom `θ_m 1` and weight `‖θ_m 1‖`; there is no ring-data or scalar-compatibility class. The frame is part of the datum: scalar coordinates, scalar singles, the weight classes and the convolution product take it as an instance argument, equal weights do not determine the product (the `−1` frame keeps every weight and negates the product, `tests/FT/FrameReindexProbes`), and a second frame on the same family is selected explicitly (`letI`), never by inference. Two layers. `Carrier` (imports only `FiberTrivialization`, Mathlib's `lpSpace` and `TransferInstance`; no index operation, no convolution): the Beurling-weight classes `lpOneAlgWeightMul`/`lpOneAlgWeightSubMul` (and multiplicative twins) stated on `FiberTrivialization.weight`; the frame-free carrier `lpOneAlg M E` with its normed-group/complete/normed-space instances and norm faces; the frame-free fiber insertion `fiberSingle m (x : E m)`, bundled as the linear isometry `fiberSingleₗᵢ m : E m →ₗᵢ[𝕜] lpOneAlg M E`, with `norm_fiberSingle` and the expansions `hasSum_fiberSingle`, `hasSum_fiberSingle_mapCLM`; the θ-coordinates `toRealSeq f m = θ_m⁻¹ (f m)` (`toRealSeq_apply`, `equiv_toRealSeq`) bundled as the injective linear map `toRealSeqₗ : lpOneAlg M E →ₗ[𝕜] (M → 𝕜)`, the weighted norm `norm_eq_abs_toReal_mul_weight` and the bound `abs_toRealSeq_le` under `∀ m, 1 ≤ weight m`; the sign split of the norm over `ℤ` (`norm_eq_tsum_natCast_add_tsum_neg`, finite-support sums `norm_eq_bilatFinSum`, `norm_eq_natFinSum_of_finSupp`); scalar singles `single m x = fiberSingle m (θ_m x)` and the mode expansion, `evalCLM`, and the pointwise column-norm bounds `norm_le_of_cols`. `Algebra` (imports `Carrier` and `Algebra/Convolution/Ring`): the convolution ring transported through the frame (`mul_apply : (f * g) k = θ_k ((θ⁻¹f ⋆ θ⁻¹g)_k)`, `one_apply : 1 m = θ_m (δ_m)`), with the frame-indexed convolution classes `lpOneAlgConvCompat`/`lpOneMulAlgConvCompat` and their two summability routes from a submultiplicative weight, finite antidiagonals (`instConvCompatOfAntidiag`, priority 1100, no completeness) or a complete scalar field (`instConvCompatOfWeightMul`), neither needing weight ≥ 1; `Ring`/`NormedRing` from the index monoid, `DecidableEq` and convolution compatibility, `Algebra`/`NormedAlgebra` from the linearity of `θ⁻¹`, `CommRing`/`NormedCommRing` over a commutative index, and `NormOneClass` from the field `ω_0 = 1` of `lpOneAlgWeightMul` with no convolution witness. On top: the universal-property API (`liftCLM`, atom extensionality, `single_mul_single`, `singleCLM m = fiberSingleₗᵢ m ∘ equivL m`, one-sided multiplication `mulLeftCLM`/`mulRightCLM` with norm bounds) (`UniversalProperty`); the curried column principle and atom-supremum formulas for bilinear/trilinear maps, one frame per slot (`Multilinear`); the one-slot column principle `‖T‖ = ⨆ i, colRatio T i` (`Columns`, carrier-only); bounded scalar diagonals `diagCLM`, finite-head projections `headProj`/`tailProj` (both frame-free) and the exact head/tail aggregation of column ratios and operator norms (`Diagonal`, carrier-only: imports `Columns`, not `UniversalProperty`). `ScalarInstances` (imports `Scalar` and `Carrier`) registers the standard frame of `WeightedScalar` (`θ_m` the identity of `𝕜`, `fiberTrivialization_weight : weight m = w m`), the only `FiberTrivialization` instance of the library, and its weight classes. |
| `Analysis/SequenceSpace/CharacterTopology` | Carrier-independent topology of pointwise convergence on continuous characters (`Gelfand.pointwiseTopology`) and its continuity API: elimination `Gelfand.continuous_character_apply` and introduction `Gelfand.continuous_of_continuous_apply` (the universal property of the induced topology) |
| `Analysis/SequenceSpace/Geometric` | Taylor coefficient algebras, differentiation, evaluation, analytic extensionality, radius restriction, full-disc power series and complex synthesis (`Analytic`), and the character space as the closed disc (`Spectrum`, which installs the shared `Gelfand.pointwiseTopology` as a `local instance`); every module declares inside namespace `RadiiPolynomial` (the evaluation family of `Evaluation`/`EvaluationDerivative` is `RadiiPolynomial.l1Weighted.eval…`), and the geometric fibers `ScaledReal`, `geomFiber`, `OmegaScaledReal` are `WeightedScalar` abbreviations carrying its standard frame (`geomFiber_weight : FiberTrivialization.weight n = νⁿ`, `Aeval`) |
| `Analysis/SequenceSpace/Chebyshev` | Bilateral storage, the flip-fixed physical algebra, the finite Galerkin carrier `FνN` with its even padding `ιN` and projection `πN` (`Galerkin`), the unnormalized one-sided cosine interface `OneSided` (symmetric extension and restriction as continuous maps, the reflected product with its exact constants; a different normalization from the bordered carrier), evaluation, analytic extensionality, the Laurent character space as the closed annulus (`LaurentSpectrum`), and the physical spectrum: classification, Bernstein ellipse, series, topology, holomorphy on the open ellipse with endpoint analyticity (`Spectrum/*`); both character spaces install the shared `Gelfand.pointwiseTopology` as a `local instance`; `Scalar` also owns the bilateral geometric fiber `geomFiberZ 𝕜 ν` of the Fourier carrier, so `Fourier/Support` imports `Chebyshev/Scalar` (with `WeightedL1/UniversalProperty`) and not the Chebyshev algebra; module chain: `Scalar` (bilateral weight, `geomFiberZ` with its frame weight `geomFiberZ_weight : FiberTrivialization.weight k = ν^|k|`, atom norm `lpOneAlg.norm_single_geomFiberZ`, the real fiber-norm bridge `ScaledRealZ.norm_equiv_apply`) → `Algebra` (`l1Chebyshev`, coefficient faces incl. `summable_norm_natCast`, `norm_fiber_natCast`, `finSum_le_norm`, `ext_natCast_negSucc`) → `Symmetrize` (`IsSymmetric`, `symmetrize`, `symmetrize_CLM`, `natEmbed`; the import hub through which `UnitLift`, `Bordered` and `CompPoly/Chebyshev/Coefficients` reach symmetrization) → { `UnitLift` → `Evaluation` (`eval`, `evalAtCLM`); `UConversion` (T↔U on raw storage) → `Bordered` (`nonnegRestrict`, `borderedTU_equiv`, the fiber-norm bridge `BorderedScaledReal.norm_equiv_apply`) } → `SymmetricSubalgebra` (`symmetricRetract`, a continuous linear retraction, not an algebra hom; `nonnegRestrictCLM`; `physicalBorderedEquiv : symmetricSubalgebra ν ≃ₗᵢ[ℝ] l1Bordered ν`, linear and isometric, not multiplicative) → `Galerkin`, `OneSided`, `AnalyticExt`; there is no `Bordered → SymmetricSubalgebra` edge |
| `Analysis/SequenceSpace/Fourier` | Bilateral `ℤ`-window and band support on the geometric carrier `lpOneAlg ℤ (geomFiberZ 𝕜 ν)` (`winZ`, the far-antitone window maximum principle, the coefficient norm, `band_mul`, `band_pow`), and the exact finite-window operator norm of the tail-diagonal defect `M P L_b Q + R L_b` (`defect`, `opNorm_defect_eq_sup'`, explicit and joint head-block forms, `opNorm_joint_defect_eq_sup'`), attained as a weighted column ratio at an atom (`defect_attained`); the Γ leakage layer on the same carrier over real scalars `[NormedAlgebra ℝ 𝕜]` (`gammaDiag`, `gammaInvDiag`, the all-coefficient head/tail leakage estimates and the Γ majorant `norm_defect_le_gamma`, `Fourier/GammaLeakage`; its `norm_mulLeftCLM_le` is the carrier lemma `lpOneAlg.norm_mulLeftCLM_le`); no Fourier module declares into `Rees.Laurent` (`gammaW_inv_le` lives in `Rees/Laurent/Gamma`); imports Analysis and `Algebra/Rees/Laurent/Gamma` |
| `Analysis/SequenceSpace/CrossGeometry` | Bounded maps between coefficient geometries, their evaluation and differentiation naturality, and the character obstructions (`CharacterObstruction`: no real extension of the zero physical character, two complex extensions) |
| `Core` | Abstract Newton map and radii polynomial with local and finite-dimensional faces (`Theorem`), canonical bounds (`Bounds`), the degree-general `Z₂` engine (`AlgebraZ2`), and certificate transport (`Transport`); every declaration of the four modules lies in namespace `RadiiPolynomial` (the former root family of `Theorem` — `I_E`, `NewtonLikeMap`, `generalRadiiPolynomial`/`radiiPolynomial`/`simpleRadiiPolynomial`, `general_radii_polynomial_theorem`, … — moved there in the DEFER round, no aliases) |
| `Operators/Matrix` | Finite weighted matrices and their continuous-linear realizations, bundled as the algebra equivalence `FinWeightedMatrix.toWeightedCLMAlgEquiv` (units correspond: `isUnit_toWeightedCLM_iff`); matrices over a normed real algebra acting on `R^n` with the sup norm (`SupNorm`: `matCLM` and the row-sum operator-norm bound `opNorm_le_of_rowSum`) |
| `Operators/BlockDiagonal` | Finite-plus-tail operators, lifts, composition, and scalar specialization; `Basic` imports only `Geometric/Scalar`, `Norm/FiniteSum`, `Matrix/WeightedNorm` and Mathlib's `FDeriv.Add`/`FDeriv.Mul`, while `WeightedL1` imports `Core/Bounds` and `Geometric/Basic` |
| `Operators/HeadTail` | Bounded-operator transport of the head/tail ring identities (`HeadTail.composition_identity`, its `headProj` instance and the norm-one scalar face); imported only by higher consumers, never by `Algebra` or `Analysis` |
| `Certification` | RadiiPolynomial witness reductions, residual (Neumann) certificates for approximate inverses and finite Bézout identities with finite-support completeness, and adapters to external LeanCert; the LeanCert-free exact-rational finite-matrix layer `Rational/Matrix` (stored ℚ columns, the `I − A B` defect, weighted and block matrix norms in exact ℚ, `activeBlockNormQ`, `blockActionQ`, and the CLM-norm, entry and action bridges; imports only `Operators/BlockDiagonal/Scalar` and `Mathlib.Data.List.GetD`), imported by `Rational/Grid`, `LeanCertAdapter`, the facade and the family faces `IVP/Taylor`, `IVP/Chebyshev`, `PowerSeries/PolynomialZero`; `IVP/Chebyshev` imports `Applications/IVP/Chebyshev/Polynomial` (the narrow owner, not the facade); the family faces carry `StdChebIVPData.Z₁_le_semiMajor_of_Q`/`_of_checksK` and `IVP.StdIVPData.ivpCoeffs_abar_eq_zero_of_compPoly`/`_mem_of_compPoly`, and are not in the `Certification` facade |
| `Tactic` | Proof automation: `pderiv_simp` (`PDerivSimp`, Mathlib-only, with a `tests` section that runs the macro), `auto_poly_fderiv` (`AutoPolyFDeriv`: Mathlib `fderiv` sets, the projection bridge `fderiv_pi_apply`, projection differentiability through Mathlib's `differentiable_apply`, and the Pi-level bridge `l1Weighted.smul_proj_eq_leftMul_comp_proj` declared in `Geometric/Basic`), the term elaborator `compPolyOf%` (`MakeCompPoly`), and the certificate tactics `finmatrix_bound`/`finmatrix_dyadic` (`FinMatrixBound`, imports `LeanCertAdapter`; syntax kinds `RadiiPolynomial.Tactic.finMatrixBound`/`finMatrixDyadic`) |
| `Applications/IVP/VectorField.lean` | Geometry-free ODE right-hand side `IVP.vectorField` of a `CompPoly` system and its calculus: `C^ω` and differentiability (`contDiff_vectorField(_pi)`, `differentiable_vectorField(_pi)`), the syntactic Lipschitz faces (`vectorField_lipschitzOnWith`, `lipschitzOnWith_vectorField_closedBall`, `exists_lipschitz_vectorField_closedBall`); imports `CompPoly/{Core,Bounds,Derivative}` only (no ℓ¹ carrier); both discretizations state their function-space conclusions through it |
| `Applications/IVP/Taylor` | Taylor-coefficient IVP operator, Jacobian (with the syntactic `ivp_Dφ_norm_le_of_compPoly` socket), theorem, analytic bridge (`Analytic`: the ball-solution predicate `IVP.IsBallSolution` — initial value, trajectory in `closedBall 0 R` and the ODE on `(-ν, ν)`, with no analyticity hypothesis — met by the canonical solution `x_analytic` and unique on the interval), real analyticity of the canonical trajectory (`Analyticity`: `IVP.analyticOnNhd_x_analytic`), complex time (`ComplexTime`: complex trajectory and vector field), and the example-facing polynomial faces `StdIVPData.existsUnique_of_compPoly`, `Z₁_le_of_compPoly`, `Z₂_le_of_compPoly`, `analytic_existsUnique_of_compPoly_of_radii`, `StdIVPData.existsUnique_ivpCoeffs_of_compPoly`, `StdIVPData.analytic_existsUnique_of_compPoly` |
| `Applications/IVP/Chebyshev` | Chebyshev-coefficient IVP operator, block-diagonal realization, polynomial residual/Jacobian adapter (`ChebyshevIVP.banachField` and syntactic Z₁/Z₂ constants), return to the IVP, analyticity of the canonical realization across `[-1, 1]` for `ν > 1` (`Analyticity`), and the example-facing faces `StdChebIVPData.existsUnique_of_compPoly`, `StdChebIVPData.Z₂_le_of_compPoly_max`, `StdChebIVPData.defect_finBlockNorm_lt_one_of_radii`, and (`AnalyticPolynomial`) `solution_existsUnique_of_compPoly`, `solution_existsUnique_of_two_le_of_compPoly`, `analytic_solution_existsUnique_of_two_le_of_compPoly`; `chebyshevShiftDiv` is by definition the U-factorization `-(uIntegrate (chebyshevToU c))`, and the Z₁ chain rests on one core `chebyshev_Z₁_component_le_semiMajor` with the `ν/(N+1)` forms through `semiMajor_div_le_div` (`Operator`, no `CrossGeometry/Joukowski` edge); the XCheb defect lift is the XL1 lift transported along `OneSided.restr`/`natEmbed`, and `composedApproxCheb` abbreviates `BlockDiagLift.composedApproxCLM` (`BlockDiagonal`, imports `Chebyshev/OneSided`); `TCtail` is componentwise `lpOneAlg.tailProj (Icc 0 N) ∘ chebyshevShiftDiv_CLM` and `TCtailElem_norm_le_tail` lives with it (`Lambda`, imports `WeightedL1/Diagonal`); row 0 of `F` is endpoint evaluation (`chebyshevIvpCoeffs_zero_eq_eval`, `FAseq_zero_eq_eval`), and `IVP.chebyshevBoundary` is `l1Chebyshev.evalAtCLM (-1)` (`Boundary`) |
| `Applications/IVP/Boundary.lean` | Shared split-boundary and anchored-primitive mechanism for IVP realizations |
| `Applications/PowerSeries` | Polynomial zeros `P(x) - c = 0` on `ℓ¹_ν` for a univariate `CompPoly` of any degree: the approximate inverse and derivative and the `Z₁`, `Z₂` bounds (`PolynomialZero`); `Z₂` bounds for maps whose derivative is affine in `leftMul`, as corollaries of the degree-general engine (`AffineZ2`, a transition module) |
| `Applications/FiniteDimensional` | The row-sum face on `R^n` over a finite-dimensional normed real algebra `R` (`Face`: `enclosure_of_rowSum`), polynomial systems with rational certificate data (`Polynomial`: `StdFinDimData` and the decidable check `ChecksC`), the scalar instance `n = 1` (`Scalar`), and periodic points on a finite-dimensional real normed space (`Periodic`) |
| `Applications/Galerkin` | The polynomial Galerkin face (`Face`): a `CompPoly` system between a lift, a projection and continuous linear parts (`polyFace`), its derivative `DpolyFace` from the syntactic Jacobian, the centred bounds from `derivativeCentredBound`, and on the finite Galerkin carrier the `Z₂`-shaped bound `norm_fderiv_galerkinFace_sub_le`; the componentwise maps `Galerkin.I`/`Galerkin.Pi'` are `ContinuousLinearMap.piMap` of `ιN`/`πN` |
| `Applications/Fourier` | The general-symbol semilinear consumer on `lpOneAlg ℤ (geomFiberZ 𝕜 ν)` (`Semilinear`): for any symbol `lam` and any bounded tail diagonal `r`, the preconditioned map `precondMap` and its model derivative `modelDeriv` with `DG(ā) − B₀ = −defect` (`fderiv_sub_modelDeriv`), the raw identification under `r = 0` on the head and `r_k λ_k = 1` off it, the exact finite window `norm_fderiv_sub_modelDeriv_eq_sup'` with window `B + max (N + 1) K₀` and attainment, the degree window `(d − 1) N + max (N + 1) K₀`, and the Γ majorant `norm_fderiv_sub_modelDeriv_le_gamma` (a universal head bound, not the exact window norm); the first-order family `λ_k = i k` as its specialization (`SemilinearFirstOrder`: `ikSymbol`, the first-tail bound `1/(N + 1)`, the window `N + m + 1`); imports Analysis/SequenceSpace/Fourier/GammaLeakage, Operators/HeadTail and Algebra/Polynomial/MvPolynomial/Calculus |
| `Examples` | End-to-end mathematical applications and numerical certificates |

The external LeanCert library remains a Lake dependency. `Certification/LeanCertAdapter.lean`
contains only project-specific bridges into that dependency: the dyadic evaluators (`colNormSumDyadic`,
`checkMatrixNormDyadic`, `scalarBlockDiagActionEval`, `systemBlockDiagActionEval`, with their correctness lemmas) and
the LeanCert-free per-column decomposition `finWeightedMatrixNorm_le_via_cols` that serves `finmatrix_dyadic`.
The exact-ℚ layer lives in `Certification/Rational/Matrix.lean`; only the `Certification` facade, `LeanCertAdapter`,
`Tactic/FinMatrixBound` and the modules importing them load LeanCert.

## Import Rules

1. `Algebra` and `Analysis` do not import `Core`, `Operators`, `Certification`,
   `Applications`, or `Examples`.
2. `Core` may import `Algebra` and `Analysis`, but not application or certificate modules.
3. `Operators` may import `Core`, `Algebra`, and `Analysis`.
4. `Certification` may import reusable operators and the external LeanCert dependency.
   A specialized Certification adapter may import an application discretization to verify its concrete certificate data; Algebra, Analysis, Core, Operators and Applications do not import Certification or Tactic.
5. `Applications` may import all reusable mathematical layers, but never `Examples`.
6. `Examples` are terminal consumers; reusable library modules never import them.
   Example families do not import one another either: the single surviving
   cross-family `Examples -> Examples` edge is
   `Examples/Transport/TwinTransport.lean -> Examples/IVP/Chebyshev/Example1421/Certificate.lean`.
7. `Tactic` is tooling. Generic polynomial tactics must not depend on applications;
   certificate tactics may depend on `Certification`.

## Public Facades

Use the facade modules at application boundaries:

- `RadiiPolynomial.Algebra.Convolution`
- `RadiiPolynomial.Algebra.Polynomial`
- `RadiiPolynomial.Algebra.Rees.Laurent`
- `RadiiPolynomial.Analysis.SequenceSpace.WeightedL1`
- `RadiiPolynomial.Analysis.SequenceSpace.Geometric`
- `RadiiPolynomial.Analysis.SequenceSpace.Chebyshev`
- `RadiiPolynomial.Analysis.SequenceSpace.Fourier`
- `RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry`
- `RadiiPolynomial.Core`
- `RadiiPolynomial.Operators.Matrix`
- `RadiiPolynomial.Operators.BlockDiagonal`
- `RadiiPolynomial.Certification`
- `RadiiPolynomial.Applications.IVP.Taylor`
- `RadiiPolynomial.Applications.IVP.Chebyshev`
- `RadiiPolynomial.Applications.Fourier`

Internal library modules should still import the narrow module that owns a declaration.
Facades are for examples and downstream users, not a substitute for precise internal edges.

## Preserved Mathematical Boundaries

- `CompPoly` remains the computable certificate representation; `MvPolynomial` remains
  the semantic algebraic representation.
- `evalBanach` remains the canonical completed evaluation map.
- `CompPoly.Laurent` computes with explicit finite support bounds; its coefficients are
  independent of the chosen valid bounds. `CompPoly.Chebyshev` interprets stored inputs
  through symmetrization and symmetrizes derivative directions as well. Generic algebra-hom
  naturality belongs to `CompPoly.Core`; the derivative of `MvPolynomial.aeval` belongs to
  `MvPolynomial.Calculus`. The regularity of the real evaluation `x ↦ p.evalBanach x` on `ℝ^L`
  (`MvPolyBridge.contDiff_evalBanach`, `differentiable_evalBanach`) belongs to `CompPoly/Derivative`, beside the
  syntactic gradient and Jacobian; `CompPoly/WeightedL1` imports `CompPoly/Derivative` and keeps only ℓ¹-carrier semantics.
- `Applications/IVP/Chebyshev/Polynomial.lean` connects the polynomial interpreter to raw
  residuals, exact rational Jacobian columns, and the bounded preconditioned derivative.
  Finite Chebyshev output rows can depend on high input modes: a finite square Jacobian
  identity leaves tail couplings for the Z₁ bound.
- Power-series evaluation and termwise differentiation remain separate modules.
- Taylor and Chebyshev residual coefficients remain raw `Nat -> Real` values that are
  immediately consumed by the approximate inverse.
- `SystemBlockDiagData.composedApprox` is shared operator infrastructure. The Taylor
  compatibility alias `IVP.ivpComposedApprox` was retired on 2026-09-13; every call site
  names the `SystemBlockDiagData` declaration directly, and the Taylor-specific Jacobian
  identity is `IVP.composedApprox_eq_fderiv_fin`.
- Each production example preserves the progression
  `Numbers -> Algebra -> Certificate -> Analytic -> Analyticity` when all five layers
  apply; Example 14.2.1 has exactly these five and no `Lambda.lean`. The analytic
  strengthenings live in per-example modules with the same axiom sets as the example's
  main theorem: `Analyticity` for Examples 8.1, 8.3 and 14.2.1, and in addition
  `ComplexTime` for Example 8.3.
- The topology of pointwise convergence on continuous characters is defined once, without a
  carrier, as `Gelfand.pointwiseTopology` in
  `Analysis/SequenceSpace/CharacterTopology.lean`, together with its continuity introduction/elimination
  API (`Gelfand.continuous_of_continuous_apply`, `Gelfand.continuous_character_apply`). The three character-space modules
  (`TaylorSpectrum`, `LaurentSpectrum`, `PhysicalSpectrum`) specialize it in one line and
  each keeps its own `local instance`; no global `TopologicalSpace` instance is installed on
  any `→A[ℝ] ℂ` type.
- `Analysis/SequenceSpace/Chebyshev/Spectrum/*` sits ABOVE `CrossGeometry/Joukowski.lean`
  (it is the Joukowski-side theory of the physical carrier), so the Chebyshev facade
  transitively imports CrossGeometry and Geometric; `CrossGeometry` modules must not import
  `Chebyshev/Spectrum`. `Applications/IVP/Taylor/{Analytic,Analyticity,ComplexTime}.lean` are wired at
  the root next to one another (all three are endpoints imported separately from the Taylor
  facade). `Taylor/Analyticity.lean` owns the purely real `IVP.analyticOnNhd_x_analytic`, so
  an example needing only real analyticity does not import the complex-time layer;
  `ComplexTime.lean` imports `Analyticity.lean`.
- Certificate norm constants are read off the `CompPoly` syntax where the constant is
  exact (`normBound`/`lipschitzBound`/`derivativeBound`); an exact-arithmetic bound on the
  evaluated coefficient array stays the tool when cancellation matters (Example 8.1's Z₁).

## Example Groups

```text
Examples/
  FiniteDimensional/Example245
  PowerSeries/Example77
  IVP/Taylor/Example81
  IVP/Taylor/Example83
  IVP/Chebyshev/Example1421
  Polynomial/Chebyshev
  Galerkin/Fisher
  Galerkin/Diblock
```

Book example numbers remain in paths and namespaces, while the parent directories expose
the mathematical problem family and discretization.

`Examples/tests/<family>` holds regression witnesses outside the default build: no library module
imports them, and each is built by its module name. Families: `CH`, `FD`, `FZ`, `GC`, `K`, `PS`, `RS`, `CV`
(finite-fiber convolution: additive `ℕ`, `Multiplicative ℕ`, the noncommutative `Function.End (Fin 2)`,
`2×2` matrices over `ℕ`, and the `IsEmpty` rejection controls for additive `ℤ` and multiplicative `ℕ`),
`FT` (the fiber-trivialization probes `tests/FT/FiberTrivializationProbes.lean`; the frame re-index probes
`tests/FT/FrameReindexProbes.lean`: real and complex scalars, non-unit weights, the frame-free primitives, both
convolution summability routes, and two distinct frames on one family with the `−1`-frame theorem; the import-order
probes `tests/FT/ImportOrderA.lean`/`ImportOrderB.lean`), `TY` (the Taylor
all-generated face, `tests/TY/AllGenerated.lean`) and `TC` (tactic quotation tests,
`tests/TC/FinMatrixBound.lean`).
