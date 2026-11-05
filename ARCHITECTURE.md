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
| `Algebra/Convolution` | Mathlib's discrete-convolution primitives and laws through `Basic`; generic point masses, two-atom multiplication and associativity under explicit fiber/triple summability in `Ring`, including additive images with coefficient order preserved. The topology-free `Finite` core keeps finite-fiber convolution, its application formula and first-input scalar action. `CauchyProduct` keeps the natural-index operation, its finite-fiber equality, coefficient/range/support formulas, `toPowerSeries` coefficient view and generic `map_cauchyProduct`. Additional finite-fiber laws and power-series compatibility belong to staged recovery records; `toPowerSeriesLinearEquiv` is not a shipped service. |
| `Algebra/Polynomial` | Semantic `MvPolynomial` calculus and computable `CompPoly` syntax, with Taylor and finite Laurent/Chebyshev interpreters, and certificate constants read off the syntax (`CompPoly/Bounds`, `CompPoly/Chebyshev/Bounds`: `normBound`, `lipschitzBound`, `derivativeBound`) |
| `Analysis/Calculus` | Coordinate differentiation uses Mathlib's projection and continuous-linear-map calculus directly. The former library `Pi` bridge and polynomial-derivative automation are historical recovery material, not shipped modules. |
| `Analysis/Norm` | Carrier-neutral finite-sum inequalities in `RadiiPolynomial.NormHelpers` (`FiniteSum`, Mathlib-only imports): real-valued (weighted triangle, uniform factor, index swap) and normed-ring (`norm_sum_mul_pi_le`: `‖∑ i, f i * h i‖ ≤ (∑ i, ‖f i‖) * ‖h‖` over any `NonUnitalSeminormedRing`), the single proof home of that bound, invoked directly by polynomial, Galerkin and Taylor Jacobian consumers; and `Exponential` (Mathlib-only imports): the Banach-algebra exponential estimates `map_exp_of_continuous` and `norm_exp_sub_exp_le` (`NormedAlgebra ℝ` scalars, hence normed `ℂ`-algebras by Mathlib's `NormedAlgebra.complexToReal`; completeness; commutativity only for the mean-value bound; no unit-norm hypothesis) and the finite-Taylor contract `norm_taylorTerm_sub_le`, `norm_exp_sub_sum_le` (`RCLike` scalars, explicit) with the tail majorant `tsum_pow_div_factorial_tail_le`, consumed by `Examples/Fourier/Exponential` |
| `Analysis/SequenceSpace/WeightedL1` | The frame-free `lpOneAlg M E` carrier, chosen `FiberTrivialization 𝕜 M E`, fiber atoms, scalar coordinates and weighted norm identities form the base. A frame is explicit mathematical data: equal weights need not give equal convolution products. `Algebra` registers one additive-index operation family globally; `instMulMul`, `instMulOne`, `instMulRing`, `instMulNormedRing` remain named explicit data. Both convolution-compatibility families retain their own instances. Arbitrary multiplicative monoids use the `Additive M` index/fiber presentation. The tsum and finite-antidiagonal routes retain their distinct completeness hypotheses. Submultiplicativity, unit normalization and an explicit coefficient-extraction lower bound remain separate assumptions. `UniversalProperty` retains the bounded `liftCLM`/`liftAlgHom` contracts, atom computation and extensionality; `Diagonal` retains bounded diagonals and finite head/tail projections, including tail contractivity under `NormedField` without a frame or completeness assumption. Exact column/multilinear families belong to staged records, not shipped `Columns`/`Multilinear` modules. `Diagonal` also ships the head/tail faces reached by `Examples/Fourier/Exponential`: the atom faces `headProj_single`/`tailProj_single`, idempotence `isIdempotentElem_headProj`, the head expansion `headProj_eq_sum` and the instance `finiteDimensional_range_headProj`, the head norm identity `norm_headProj` and the tail bound of a diagonal `norm_tailProj_diagCLM_apply_le`; the remaining head/tail aggregation families (fiber-range characterizations, diagonal compositions, head–tail norm additivity, column ratios, joint operator norms) stay in the staged record `B5RecordL1HeadTail`. `Algebra` ships convolution against an atom `toRealSeq_mul_single` (additive index group). Coefficient conjugation `coeffConj : lpOneAlg M E ≃ₗᵢ⋆[𝕜] lpOneAlg M E` (`Carrier`; `RCLike` scalars, any index and frame) is a conjugate-linear isometric equivalence of the carrier; its ring part `coeffConjRingHom` (`Algebra`; `RCLike` scalars, any additive index monoid, any frame, `lpOneAlgConvCompat`) is the same function as a ring homomorphism. `UniversalProperty` ships the reflection `refl hw : lpOneAlg M E →A[𝕜] lpOneAlg M E` (additive commutative index group, complete fibers, symmetric weight `hw : ∀ m, ω_(−m) ≤ ω_m`, equivalently `ω_(−m) = ω_m`; the algebra lift of `m ↦ e_(−m)`) with `refl_single`, `norm_refl_le`, `refl_refl`, `toRealSeq_refl` and `coeffConj_refl`; no `Star` instance (the Banach-*-involution is `coeffConj ∘ refl`). |
| `Analysis/SequenceSpace/CharacterTopology` | The pointwise character-topology family is owned by the staged topology record; the former shipped owner module is removed. |
| `Analysis/SequenceSpace/Geometric` | Taylor coefficient algebras, retained differentiation/evaluation and full-disc complex power-series synthesis (`Analytic`) use the canonical additive-index weighted ℓ¹ structure on `ℕ`. The geometric fibers are `WeightedScalar` abbreviations with the standard frame. Analytic extensionality, radius-restriction and character-spectrum families are owned by staged recovery records; they are not shipped owners. |
| `Analysis/SequenceSpace/Chebyshev` | Bilateral storage with fiber `geomFiberZ` (`Scalar`: the frame weight `geomFiberZ_weight`, `ν^\|k\|`, and its symmetry `geomFiberZ_weight_neg`, `ν^\|−k\| = ν^\|k\|` for every positive `ν`, the hypothesis of `conjReflL` on `X₂ ℂ ν` and, through `.le`, of `lpOneAlg.refl` in the exponential example), the flip-fixed physical algebra, symmetrization and retained evaluation/U-conversion primitives, bordered storage and retraction, and the finite Galerkin carrier `FνN` with padding `ιN` and projection `πN`. The full one-sided cosine principle, physical/bordered isometric equivalence and Laurent/physical spectrum families have staged record ownership. Retained one-sided restriction/embedding primitives used by the IVP remain shipped; record ownership does not restore the full old interface. |
| `Analysis/SequenceSpace/CrossGeometry` | The Joukowski map `CrossGeometry.joukowski z = (z + z⁻¹) / 2` and the symmetric Laurent generator `joukowskiGen ν = (e₁ + e₋₁) / 2` in `l1Chebyshev ν`, symmetric by `joukowskiGen_isSymmetric` and, for `1 ≤ ν`, an element `joukowskiGenSymm ν` of the physical algebra (`Joukowski`; consumed by `Chebyshev/Spectrum`). The bounded maps between coefficient geometries (`joukowskiAeval`, `chebyshevToTaylorCLM`), their evaluation and character naturality and the derivative naturality square are staged in `B5RecordJoukowski` (`exterior/api_v2/probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/`), not shipped. |
| `Core` | Abstract Newton map and radii polynomial with local and finite-dimensional faces (`Theorem`), basis-independent quadratic calculus and radii faces (`Quadratic`, with a symmetrized preconditioned bilinear curvature socket), canonical bounds (`Bounds`), the degree-general `Z₂` engine (`AlgebraZ2`), and finite-dimensional pulled-back-norm and isometric zero transport (`Transport`); every declaration of these modules lies in namespace `RadiiPolynomial` (the former root family of `Theorem` — `I_E`, `NewtonLikeMap`, `generalRadiiPolynomial`/`radiiPolynomial`/`simpleRadiiPolynomial`, `general_radii_polynomial_theorem`, … — moved there in the DEFER round, no aliases) |
| `Operators/Matrix` | Finite weighted matrices and their continuous-linear realizations, bundled as the algebra equivalence `FinWeightedMatrix.toWeightedCLMAlgEquiv` (units correspond: `isUnit_toWeightedCLM_iff`); matrices over a normed real algebra acting on `R^n` with the sup norm (`SupNorm`: `matCLM` and the row-sum operator-norm bound `opNorm_le_of_rowSum`) |
| `Operators/BlockDiagonal` | Finite-plus-tail operators, lifts, composition, and scalar specialization; `ProdBlock` (Mathlib-only imports; in the facade) bounds an operator between binary products by its block row sums under the max norm (`opNorm_le_max_block`, `opNorm_le_max_of_rows`; `NontriviallyNormedField` is needed for the operator norm); `Basic` imports only `Geometric/Scalar`, `Norm/FiniteSum`, `Matrix/WeightedNorm` and Mathlib's `FDeriv.Add`/`FDeriv.Mul`, while `WeightedL1` imports `Core/Bounds` and `Geometric/Basic` |
| `Certification` | RadiiPolynomial witness reductions, adapters to external LeanCert, with the residual/Neumann and finite-support completeness families owned by staged recovery records; the LeanCert-free exact-rational finite-matrix layer `Rational/Matrix` (stored ℚ columns, the `I − A B` defect, weighted and block matrix norms in exact ℚ, `activeBlockNormQ`, the shared `blockActionQ` with its cast bridge `SystemBlockDiagData.action_eq_blockActionQ`, used by the Chebyshev `Y₀` soundness `ChebyshevIVP.StdChebIVPData.Y₀_le_of_Q` at tail multiplier `(2n)⁻¹` (the Taylor `Y₀` clause at `n⁻¹` is staged in `B5RecordTaylorY0P1`), and the CLM-norm and entry bridges; imports only `Operators/BlockDiagonal/Scalar` and `Mathlib.Data.List.GetD`), imported by `Rational/Grid`, `LeanCertAdapter`, the facade and the family faces `IVP/Taylor`, `IVP/Chebyshev`, `PowerSeries/PolynomialZero`; the rational-leaf adapter of the quadratic Fourier family `Fourier/Quadratic` (namespace `RadiiPolynomial.Certification.Fourier.Quadratic`; imports `Applications/Fourier/{Quadratic,IkData}`, `WeightedLp/Operators/FiniteBlock`, `RadiiPolynomialQ`; no `Examples`, no Duffing import): the computable ℚ×ℚ mirror and index lists, the leaf `QuadFourierLeafQ` (head `N`, band `B`, `nuQ`, symbol and forcing mirrors, data over `D`, constants, `t2Q`, `tailInvSqQ`, chunks), its two obligations `Checks` (ONE `decide +kernel`) and `ChunkChecks` (one `native_decide` per chunk at the consumer, so the per-chunk axiom names stay the consumer's), the bridges under `ν = nuQ`, `μ = toC ∘ muQ`, `coeff g = toC ∘ forcQ`, the certificate `QuadFourierLeafQ.cert : Cert (headF N) μ ν` and the soundness theorem `QuadFourierLeafQ.cert_spec` (`Y₀`, squared `Z₁` at every tail factor `x` with `(x²)⁻¹ ≤ tailInvSqQ`, squared `Z₂` at `T2 = t2Q`, `0 ≤ Z1c`, `0 ≤ Z2c`), consumed by both Duffing instances, whose carrier-free bridges the polynomial-weight Duffing example reuses; `IVP/Chebyshev` is the facade of the eight modules `IVP/Chebyshev/{QLayer, Common, Y0Z0, TC, Z1, Face, Kernel/QLayer, Kernel/Face}`, whose imports form the DAG `QLayer → Y0Z0 → {TC, Z1} → Face → Kernel/Face`, `Common → {TC, Z1} → Kernel/QLayer → Kernel/Face` (`TC` and `Z1` independent), with `QLayer` importing `Rational/Matrix` and `Applications/IVP/Chebyshev/Polynomial` (the narrow owner, not the facade), `Common` importing `Applications/IVP/Chebyshev/Polynomial`, `Y0Z0` importing `Rational/Grid` and `Face` importing `RadiiPolynomialQ`; the retained Taylor family face `IVP.StdIVPData.ivpCoeffs_abar_eq_zero_of_compPoly`; the specialized Chebyshev semi-major certificate family has staged record ownership |
| `Tactic` | No shipped module: `finmatrix_bound` (`FinMatrixBound`) is deleted (see the LeanCert paragraph below). Polynomial derivative macros and `compPolyOf%` reification are retired service interfaces with historical recovery material. Dyadic syntax, elaboration, evaluators and the dyadic self-test have staged ownership. |
| `Applications/IVP/VectorField.lean` | Geometry-free ODE right-hand side `IVP.vectorField` of a `CompPoly` system and the retained syntactic Lipschitz faces (`vectorField_lipschitzOnWith`, `lipschitzOnWith_vectorField_closedBall`, `exists_lipschitz_vectorField_closedBall`); imports `CompPoly/{Core,Bounds,Derivative}` only (no ℓ¹ carrier); both discretizations state their function-space conclusions through it |
| `Applications/IVP/Taylor` | Taylor-coefficient IVP operator, Jacobian (with the syntactic `ivp_Dφ_norm_le_of_compPoly` socket), theorem, analytic bridge (`Analytic`: the ball-solution predicate `IVP.IsBallSolution` — initial value, trajectory in `closedBall 0 R` and the ODE on `(-ν, ν)`, with no analyticity hypothesis — met by the canonical solution `x_analytic` and unique on the interval), real analyticity of the canonical trajectory (`Analyticity`: `IVP.analyticOnNhd_x_analytic`), complex time (`ComplexTime`: complex trajectory and vector field), and the example-facing polynomial faces `StdIVPData.existsUnique_of_compPoly`, `Z₁_le_of_compPoly`, `Z₂_le_of_compPoly`, `analytic_existsUnique_of_compPoly_of_radii`, `StdIVPData.existsUnique_ivpCoeffs_of_compPoly`, `StdIVPData.analytic_existsUnique_of_compPoly` |
| `Applications/IVP/Chebyshev` | Chebyshev-coefficient IVP operator, block-diagonal realization, polynomial residual/Jacobian adapter (`ChebyshevIVP.banachField` and syntactic Z₁/Z₂ constants), return to the IVP, analyticity of the canonical realization across `[-1, 1]` for `ν > 1` (`Analyticity`), and the example-facing faces `StdChebIVPData.existsUnique_of_compPoly`, `StdChebIVPData.Z₂_le_of_compPoly_max`, `StdChebIVPData.defect_finBlockNorm_lt_one_of_radii`, and (`AnalyticPolynomial`) the canonical-witness face `exists_canonical_solution_of_compPoly_of_evalBound` (a uniform evaluator bound `C` on `[-1, 1]` and `C · (‖ā‖ + r₀) ≤ R` give a coefficient witness `xTilde` whose `x_sol xTilde` is the unique solution on `[-1, 1]`) with its consumers `solution_existsUnique_of_compPoly` (`C = 2`), `solution_existsUnique_of_two_le_of_compPoly`, `analytic_solution_existsUnique_of_two_le_of_compPoly` (`C = 1` at `2 ≤ ν`); `chebyshevShiftDiv` is by definition the U-factorization `-(uIntegrate (chebyshevToU c))`, and the specialized shift-div and semi-major families are recovered in staged records; the XCheb defect lift is the XL1 lift transported along `OneSided.restr`/`natEmbed`, and `composedApproxCheb` abbreviates `BlockDiagLift.composedApproxCLM` (`BlockDiagonal`, imports `Chebyshev/OneSided`); `TCtail` is componentwise `lpOneAlg.tailProj (Icc 0 N) ∘ chebyshevShiftDiv_CLM` and `TCtailElem_norm_le_tail` lives with it (`Lambda`, imports `WeightedL1/Diagonal`); row 0 of `F` is endpoint evaluation (`chebyshevIvpCoeffs_zero_eq_eval`, `FAseq_zero_eq_eval`), the additional `IVP.chebyshevBoundary` and split-boundary family belong to staged IVP-boundary records |
| `Applications/IVP/Boundary.lean` | The split-boundary and anchored-primitive family has staged IVP-boundary record ownership; this former shipped module is removed. |
| `Applications/PowerSeries` | Polynomial zeros `P(x) - c = 0` on `ℓ¹_ν` for a univariate `CompPoly` of any degree: the approximate inverse and derivative and the `Z₁`, `Z₂` bounds (`PolynomialZero`); `Z₂` bounds for maps whose derivative is affine in `leftMul`, as a corollary of the degree-general engine (`AffineZ2`) |
| `Applications/FiniteDimensional` | The row-sum enclosure face on finite-dimensional normed real algebras, rational polynomial certificates (`StdFinDimData`, `ChecksC`) and scalar specialization remain shipped. The periodic-point family is owned by a staged record. |
| `Applications/Galerkin` | The polynomial Galerkin face (`Face`): a `CompPoly` system between a lift, a projection and continuous linear parts (`polyFace`), its derivative `DpolyFace` from the syntactic Jacobian, the centred bounds from `derivativeCentredBound`, with consumers using the generic bound `norm_DpolyFace_sub_le`; the componentwise maps `Galerkin.I`/`Galerkin.Pi'` are `ContinuousLinearMap.piMap` of `ιN`/`πN` |
| `Applications/Fourier` | The Fourier realization of bilateral coefficient families (`Realization`, namespace `RadiiPolynomial.Fourier`): `realization c t = ∑' n, cₙ e^{int}`, its complex-time form `complexRealization` and real part `realRealization`, `2π`-periodic for every `c`; the algebra lift `circleLift ν : ℓ¹_ν →A[ℂ] C(AddCircle (2π), ℂ)` (`ν ≥ 1`; `liftAlgHom` at Mathlib's `fourier`, with the global instance `fact_zero_lt_two_pi`), its sup-norm series `hasSum_circleLift` (uniform convergence), `circleLift_apply_coe` and multiplicativity `realization_mul` from `map_mul`; the decay chain `ℓ²_ν → ℓ^∞_ν → ℓ¹_{ν'}` (`Bilateral.incl`, then `toL1` for `0 < ν' < ν` with constant `(1 + q)/(1 − q)`, `q = ν'/ν`) and the moments `summable_moment_Y` of `Y ℂ ν` data at every weight `ρ < ν`; termwise differentiation in moment form `hasDerivAt_realization` (`∑ \|n\| ‖cₙ‖ < ∞`); holomorphy on the full strip `\|Im z\| < log ν` and real analyticity (`ν > 1`) for `Y ℂ ν` data; reality under conjugate symmetry; and the parameter-generic Duffing equation transfer `realization_duffing`/`realRealization_duffing` (termwise differentiation, linearity and `realization_mul`); the raw-coefficient product `realization_addRingConvolution` (with `summable_norm_addRingConvolution`; absolutely summable families, through `circleLift` at `ν = 1`), the linear second-order transfer with a potential `realRealization_linearSecondOrder` (`(c₀ + i c₁ n − c₂ n²) vₙ + κ (p ⋆ v)ₙ − λ vₙ = 0` ⇒ `c₂ V″ + c₁ V′ + c₀ V + κ P V = λ V`), the first Fourier-coefficient service `fourierCoeff_circleLift` (`fourierCoeff (circleLift ν a) = toRealSeq a`, through `ContinuousMap.toLp`, `fourierBasis` and Mathlib's `fourierCoeff_fourier`) with `circleLift_injective`, `eq_zero_of_realization_eq_zero` and `eq_zero_of_realRealization_eq_zero` (nonvanishing of realized end statements), and the ℓ²_w → ℓ¹ summability `summable_norm_coeff_of_summable_inv_sq` / `summable_norm_coeff_weightedScalar` with the ℤ series `summable_inv_one_add_abs_pow_sq` (generic in the index; placed here by the U-E placement order, a candidate for `WeightedLp/Carrier`), consumed by `Examples/Fourier/Duffing/Polynomial/Eigenpair/Analytic`; consumed by `Examples/Fourier/Duffing/Analytic` and `Examples/Fourier/Riccati/Analytic`; also the exponential realization `realization_exp` (`u_(e^a) = exp ∘ u_a`, through `circleLift` and `NormHelpers.map_exp_of_continuous`; no evenness hypothesis), the inclusion `lpOneAlg.toLinf : ℓ¹_ν →L Y 𝕜 ν` (`Compatibility/WeightedL1Iso`, the one home of the ℓ¹ → ℓ^∞ inclusion) and the parity `realization_neg_of_even`, consumed by `Examples/Fourier/Exponential/Analytic`. The quadratic Fourier family (`Quadratic`, namespace `RadiiPolynomial.Fourier.Quadratic`; imports `Bilateral/Quadratic`, `Operators/FiniteBlock`, `Operators/Reality`, `Core/Quadratic`, `Core/Transport`): on `X₂ ℂ ν` with an arbitrary symbol `μ : ℤ → ℂ`, a finite head `F`, a forcing `g` and an approximate head inverse `M`, the raw coefficient map `rawF μ g a n = μₙ aₙ − (a ⋆ a)ₙ − gₙ` and the raw preconditioner `rawA` (raw codomain `ℤ → ℂ`), the bounded preconditioned residual `G` (the canonical quadratic map, `G_eq`) with derivative `DG` (`DG_eq`), the coefficient identity `coeff_G`, the centre defect `DG_sub_B0` (`= −tailDefect`), the four bound faces (`Y₀` `norm_sq_G_abar`, `Z₀` `block_one_sub_B0`, `Z₁` `norm_DG_sub_B0_le`, `Z₂` `norm_quadComp_add_flip_le_of_bounds` with the `U_row` certificate `norm_comp_headReal_le_urow`; the norm bounds are upper enclosures; `norm_sq_G_abar` and `block_one_sub_B0` are exact identities), the radii-polynomial existence `existsUnique_G` and the transfer of zeros to a unique raw zero `existsUnique_rawF` (head injectivity of `M` from the finite-head solver service of `Operators/FiniteBlock`, not injectivity of `rawF`; the raw-zero equivalence of the solver identity `coeff_G`; `Core/Transport.existsUnique_zero_transport` at the identity isometry), the head certificate `Cert F μ ν` (candidate supported in `F`, head matrix with `P M = M`, the three head numbers `Z₀`, `H`, `U` with their operator bounds; forcing, tail and radius hypotheses stay with the consuming theorem), and the conjugate reflection `conjRefl` (any positive `ν`; the geometric specialization `conjReflL (geomFiberZ_weight_neg ν)` of `WeightedLp.conjReflL`, a `def`; an additive isometry `isometry_conjRefl` by `isometry_conjReflL`, not complex-linear) with the square identity `convCoeff_conjRefl`; the raw map is `R`-equivariant for a conjugate-symmetric symbol and forcing (`rawF_conjRefl`) and `Bilateral.refl`-equivariant for an even symbol and forcing (`rawF_refl`); the symmetry of a particular symbol and forcing is the consumer's hypothesis. The Helmholtz–Duffing family (`Duffing`, namespace `RadiiPolynomial.Fourier.Duffing`; imports `Quadratic`, `IkData`): the symbol `duffing c₁ c₂` and the forcing `forcing c₃` for all real parameters, the norm identity, tail witness, nonvanishing and summability on `headF N`, the tail-sum producer `tsum_sq_tailSymbol_duffing_le` under `−(N+1)(N+2) ≤ c₂ < (N+1)²` (its pointwise step `duffing_lower_linear` under `−(N+1)(N+2) ≤ c₂` alone, by the integer-tail factorization; sufficient, the aggregate domain is not characterized), `rawF_duffing`, the symmetries `duffing_conj`, `coeff_forcing_conj` (real parameters) and `duffing_neg` (`c₁ = 0`), `coeff_forcing_neg`, and the existence theorems `duffing_existsUnique`, `duffing_enclosure` (two radii), `duffing_existsUnique_real` on `Cert (headF N) (duffing c₁ c₂) ν` (reality through `isometry_conjRefl.mapsTo_closedBall` and `rawF_conjRefl`), and for the undamped even subfamily (`c₁ = 0`) `duffing_existsUnique_even` (conjugate symmetry and evenness of the zero from an even candidate: `isometry_refl`, `rawF_refl`, `duffing_neg`, `coeff_forcing_neg`; parametric in `c₂, c₃, N, ν`); a Duffing-specific family module in `Applications/` (Codex Q3; the precedent `realization_duffing`), read as the `(c₁, c₂, c₃)` family. The first-order symbol data (`IkData`, namespace `RadiiPolynomial.Fourier.IkData`; imports `Operators/TailDiagonal`): the fixed complex symbol `ik k = I k`, the head `headZ N`, and `∑' ‖tailSymbol (headZ N) ik k‖² = 2 psi1 N`; the symbol-free `Finset` head `headF N = Icc (−N) N` with `mem_headF`, its symmetry `neg_mem_headF` and the head bridge `tailSymbol_headF`. The Duffing family also carries the shifted-symbol tail data at a real eigenvalue `l` (`duffing_sub_ofReal`, `duffing_ne_ofReal`, `norm_tailSymbol_duffing_sub_le`, `bddAbove_tailSymbol_duffing_sub`, `inv_norm_duffing_succ_le` under `c₂ − l < (N+1)²`) and the cofinite growth `tendsto_norm_duffing` (every real `c₁, c₂`; through `abs_le_norm_duffing_add`). The bordered eigenpair face (`Eigenpair`, namespace `RadiiPolynomial.Fourier.Eigenpair`; imports `Core/Quadratic`, `WeightedLp/Pairing`, `Operators/RealityConvolution`, `Operators/BlockDiagonal/ProdBlock`): for `EigenData` (conjugate-symmetric symbol, symmetric finite head `S`, real potential `q`, bordered head inverse `(Mv, mv, ψ, c)`; data and the reality fields only, no `hψ`), the bordered map `eigenMap = quadMap cG LG BilG` on `XR × ℝ`, its zeros = the normalized eigenpairs under `borderInj` (`eigenMap_eq_zero_iff`, with tail nonresonance `hres` and the head support `hmvS` as theorem hypotheses), `borderInj` from a defect bound (`borderInj_of_norm_id_sub_lt_one`, `borderInj_of_eigenB0`), the existence/uniqueness theorem `existsUnique_eigenpair` and the four faces `norm_eigenMap_le` (`Y₀`), `norm_id_sub_eigenB0_le` (`Z₀`), `norm_eigenB0_sub_quadDeriv_le` (`Z₁`), `norm_quadComp_BilG_add_flip_le` (`Z₂`); generic in the index `M`, only the reality structure is Fourier's. Imports no `Examples`; `Quadratic`, `IkData` and `Duffing` are consumed by `Certification/Fourier/Quadratic`, `Examples/Fourier/Duffing` (both instances and the polynomial-weight example) and `Examples/Fourier/Riccati` (symmetry layer, no Duffing declaration) |
| `Examples` | End-to-end mathematical applications and numerical certificates |

The external LeanCert library remains a Lake dependency. `Certification/LeanCertAdapter.lean`
keeps weighted-term and system block-diagonal action evaluators with their correctness proofs.
The exact-ℚ bridges of `Certification/Rational/Matrix.lean` are soundness lemmas consumed directly by
the certification faces (`Certification/PowerSeries/PolynomialZero`). A certificate closes each bound
by ONE call: the family checker by `decide +kernel`, or a LeanCert tactic such as `finsum_bound`.
The tactic-wrapper-over-a-bridge pattern (`finmatrix_bound`) is retired as technical debt (user
2026-10-23). Dyadic checker support is recovered outside shipped imports.

## Import Rules

1. `Algebra` and `Analysis` do not import `Core`, `Operators`, `Certification`,
   `Applications`, or `Examples`.
2. `Core` may import `Algebra` and `Analysis`, but not application or certificate modules.
3. `Operators` may import `Core`, `Algebra`, and `Analysis`.
4. `Certification` may import reusable operators and the external LeanCert dependency.
   A specialized Certification adapter may import an application discretization to verify its concrete certificate data; Algebra, Analysis, Core, Operators and Applications do not import Certification or Tactic.
5. `Applications` may import all reusable mathematical layers, but never `Examples`.
6. `Examples` are terminal consumers; reusable library modules never import them.
   Example families do not import one another.
7. `Tactic` is tooling. Generic polynomial tactics must not depend on applications;
   certificate tactics may depend on `Certification`.

## Public Facades

Use the facade modules at application boundaries:

- `RadiiPolynomial.Algebra.Convolution`
- `RadiiPolynomial.Algebra.Polynomial`
- `RadiiPolynomial.Analysis.SequenceSpace.WeightedL1`
- `RadiiPolynomial.Analysis.SequenceSpace.WeightedLp`
- `RadiiPolynomial.Analysis.SequenceSpace.Geometric`
- `RadiiPolynomial.Analysis.SequenceSpace.Chebyshev`
- `RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry`
- `RadiiPolynomial.Core`
- `RadiiPolynomial.Operators.Matrix`
- `RadiiPolynomial.Operators.BlockDiagonal`
- `RadiiPolynomial.Certification`
- `RadiiPolynomial.Applications.IVP.Taylor`
- `RadiiPolynomial.Applications.IVP.Chebyshev`

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
  `MvPolynomial.Calculus`. The derivative of the real evaluation `x ↦ p.evalBanach x` on `ℝ^L`
  is exposed through `CompPoly.hasFDerivAt_evalBanach` in `CompPoly/Derivative`, beside the
  syntactic gradient and Jacobian; the former smoothness/differentiability convenience wrappers are retired; `CompPoly/WeightedL1` imports `CompPoly/Derivative` and keeps only ℓ¹-carrier semantics.
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
- Pointwise character topologies are recovery services: `B5RecordGelfandTopology` owns the
  common topology and continuity interfaces; `B5RecordTaylorSpectrum`, `B5RecordLaurentSpectrum`
  and `B5RecordPhysicalSpectrum` own the character-space specializations. The removed
  `Analysis/SequenceSpace/CharacterTopology.lean` is a historical owner, not a shipped module.
  Recovery modules use their own local topology instances; importing the shipped coefficient
  carriers does not install a global character-space topology.
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
probes `tests/FT/ImportOrderA.lean`/`ImportOrderB.lean`) and `WL` (weighted-ℓᵖ regression checks, including `LiftBoundChecks`). `TailKernelChecks` and the full `Example81L2/` caller chain
belong to the staged R30 finite-tail-kernel record. The finite-fiber convolution law probes
belong to `B5RecordFiniteFiberConvolution`. The former `Example81L1NewAPI` witness is retained in
the early-U37a recovery record after its production migration.


## API-v2 finite-p integration (2026-10-19)

This section describes the isolated API-v2 copy. `WeightedLp/Carrier` and `Module` provide framed scalar coordinates, atoms and completeness on Mathlib lp. `Operators/LiftBound` specifies bounded finite synthesis by its extension, atom computation, pointwise bound and uniqueness/converse laws. Construction uses a normed field and a complete target; operator-norm statements retain a nontrivially normed field. `Operators/Schur` supplies an independent sufficient producer, with the coefficient identity relating its operator to the canonical extension. Absolute row summability inferred from unconditional convergence remains a separate real/complex assertion.

`Compatibility/WeightedL1Iso` identifies the p=1 carrier; bounds for an already supplied operator require no scalar completeness. `Compatibility/FiniteBlockTransport` (imports `Compatibility/WeightedL1Iso` and `Operators/FiniteBlock`) transports the finite matrix `lpOneAlg.finMatrixCLM` with `toRealSeq_finMatrixCLM` to the library ℓ¹ carrier through `toLpₗᵢ` (no new carrier equivalence), consumed by `Examples/Fourier/Exponential`. `Compatibility/TaylorTailL1` owns the coefficient/operator bridge. The family numerical certificate and its shared per-pair assembly are in `Certification/IVP/Taylor`; analysis has no certification dependency. `WeightedScalar.instCompleteSpace` now transfers completeness through the existing scalar equivalence and works for complete trivially normed fields.

Production Example81 uses the kernel-column Z₁ clause on its unchanged ℓ¹ carrier, data,
norm, bounds and radius. The generated-only contract and its former `AllGenerated` test are
staged recoverable evidence outside shipped source. The production consumer trail
exposes LiftBound's finite-synthesis contract and the p=1 compatibility service through the
existing production imports; no direct root/facade lift import is needed. Production retains its
existing Y₀/native proof. The independent ℓ² witness and its ten-module caller/test chain
are owned by the staged R30 finite-tail-kernel record. That record has its own ball, map and
preconditioner and returns a solution on (-1,1); it is outside the shipped root. No global convolution algebra on the ℓ²
state is introduced.

## Isolated API-copy U10 retirement (2026-10-19)

The prior Fourier ℓ¹ semilinear/finite-window/Γ stack, its head-tail transport, and the Laurent Rees family are archived outside this Lake source tree. The 32 exact source modules, their build artifacts, and all 1783 elaborated declaration types and axiom sets are recoverable in `../probes/records/U10_retired_20261019/`. The five root imports and empty facade sources were removed. No essential classical example imports this cluster. Historical rename entries below or in `RENAMES.md` describe earlier generations, not current availability. Re-entry requires a concrete mathematical consumer and minimal assumptions; there are no compatibility aliases. ReferenceBook compatibility is deferred. The replacement ℓ² Fourier consumer is described below; its coefficient certificate does not reproduce the retired exact ℓ¹ norm results.

## Weighted ℓ² Fourier consumer in the isolated API copy

`Analysis/SequenceSpace/WeightedLp` exposes the bounded symbol action, the Schur
producer, the bilateral product and the finite-block/tail operator bounds. `Module.symbolAction₀`
is the operator-series action of ℓ¹ symbols with a positive weight v on ℓᵖ states whose weight
is v-moderate. If v is additionally submultiplicative, `symbolAction₀_eq` identifies the series
with the universal algebra lift `symbolAction`; its construction, generator computation,
multiplicativity, uniqueness and norm laws are the contract of the consumed series, not extra
consumer proof dependencies. No unit-weight normalization premise is imposed. Pointwise diagonals
and finite-block bounds for an existing operator do not require scalar completeness.

For `X = ℓ²_(ν^|n|)(ℤ;ℂ)` and `Y = ℓ∞_(ν^|n|)(ℤ;ℂ)`, `Bilateral.Product` supplies
`q : X × X → Y` at ν ≥ 1, and the reflection `Bilateral.refl : X₂ 𝕜 ν → X₂ 𝕜 ν`,
`(refl a)ₙ = a₋ₙ` (any `NormedField 𝕜`, any positive ν, no `Fact`; named by carrier, the ℓ²
sibling of `lpOneAlg.refl`), with `coeff_refl`, `isometry_refl` and
`convCoeff_refl : (refl x ⋆ refl y)ₙ = (x ⋆ y)₋ₙ`. `TailDiagonal` supplies the return map Y → X, the separate X → X
diagonal, and the single coefficient-disjoint square-norm identity. `Bilateral.Quadratic`
composes the product with a return map. `Fourier.ConvolutionAction` owns only the geometric moderation constant; `TailDefect` and `FiniteBlock` own the full shared-input defect and finite
matrix composition before entrywise modulus. The resulting operator-norm aggregation is an
upper bound, not an equality of independently optimized summands. The physical matrix map
`matrixOf T n k = coeff (T (single k 1)) n` belongs to `FiniteBlock`.
`FiniteBlock` also owns the finite-head solver service (§FiniteHead): the carrier-neutral head
injectivity `eq_zero_of_mem_of_norm_sub_comp_lt_one` (finite-dimensional `V`, `P|_V = id`,
`K(V) ⊆ V`, `‖P − M K‖ < 1` give `M` injective on `V`; no completeness, Neumann series or
`M(V) ⊆ V`), its head-range instance `eq_zero_of_headProj_eq_of_norm_lt_one` on any framed
carrier and `1 ≤ p ≤ ∞` (`P_F K P_F = K P_F`), and the raw-zero equivalence
`eq_zero_iff_of_coeff_eq_headSolve` of a finite-head / diagonal-tail coefficient solver
`coeff (G u) k = coeff (M (J (R u))) k + d k * R u k` (`P_F M P_F = M P_F`, head injectivity,
`d = 0` on `F`, `d ≠ 0` off `F`). The geometric family (`existsUnique_rawF`) and the polynomial
certificate (`existsUnique_raw`) consume both.

`Examples/Fourier/Duffing/{Numbers,Certificate}` is the first instance of the Helmholtz–Duffing
family `Applications/Fourier/Duffing` (`u'' + c₁ u' + c₂ u − u² = c₃ cos t`, book §10.1, at
`c = (1/10, 4, 1)`, `N = 10`, `ν = 6/5`): `Numbers` is the generated rational leaf of the adapter
`Certification/Fourier/Quadratic` (generator copy `exterior/tmp/lp_api_campaign_20261017/POST_MERGE/promotion_20261104/U-B/gen/d1/`;
17 per-chunk `native_decide` checks under their 29d0d62 names, the leaf obligations and the two
radii one `decide +kernel` each); `Certificate` supplies only the instance bridges, the
tail-factor, tail-sum and forcing discharges, the radii and the endpoints (the former
`Duffing/Algebra.lean` is gone: its family content is `Applications/Fourier/Duffing`, its
instance data `control_hN`, `sq_norm_duffing_control` are in `Certificate`).
The numerical candidate and four bounds give a radii-polynomial certificate, raw coefficient
zeros, a local uniqueness/enclosure statement and conjugate-reflection reality. The raw residual
is sequence-valued: the identity with the bounded map is coefficientwise through `rawA`, not
an unsupported assertion that the residual itself belongs to Y. The head certificate has no
phantom c₃ parameter; forcing and its residual bound retain c₃. The default Examples facade
imports this actual certificate. `Examples/Fourier/Duffing/Analytic` reads the shipped zero of
`duffing_l2_real` as a function through `Applications/Fourier/Realization`
(`duffing_analytic_solution`: a real-analytic `2π`-periodic solution of the equation on `ℝ`, the
sum of its Fourier series, with a holomorphic extension to `|Im z| < log (6/5)`; the uniqueness
stays among coefficient zeros in the `ℓ²_{6/5}` ball).

`Examples/Fourier/Duffing/Even/{Numbers,Certificate,Analytic}` is the second instance
(PlasmaLean's `u'' − u + u² = (4/5) cos t`, Apache-2.0, in the convention `v = −u`:
`c = (0, −1, −4/5)`, `N = 10`, `ν = 6/5`): the generated leaf (generator copy
`U-B/gen/fb1/`; `check_even`; no `Algebra` layer: the even subfamily step is the family's
`Applications/Fourier/Duffing.duffing_existsUnique_even`), the certificate through the adapter with `T2` from the family producer at `c₂ = −1`, the endpoints
`even_l2_{existsUnique,existsUnique_r1,enclosure,real,even}` and the analytic end theorem
`even_analytic_solution` (`u = −v` real-analytic, even, `2π`-periodic, the sum of its Fourier
series, holomorphic on `|Im z| < log (6/5)`, `u'' − u + u² = (4/5) cos t`; evenness of the
realization by `Fourier.realization_neg_of_even`).

`Examples/Fourier/Riccati/{Certificate,Analytic}` is the second consumer of the family: the
forced Riccati equation `u′ + u − u² = cos (2t) / 100` (`μₙ = 1 + i n`, `F = Icc (−2) 2`,
`ν = 6/5`, `M = diag (1_F μ⁻¹)`, `ā = M g`, `g_{±2} = 1/200`). `Certificate` proves the four
bounds, the unique raw zero in the closed ball of radius `1/100` and its conjugate symmetry
(`raw_existsUnique`, `raw_existsUnique_real`, with the pins `coefficient_{ball,zero,reality,error}`
and `equation_semantics`); `Analytic` reads it through `Applications/Fourier/Realization`
(`realRealization_firstOrder`) as `riccati_analytic_solution`: a real-analytic `2π`-periodic
solution on `ℝ`, the sum of its Fourier series, holomorphic on `|Im z| < log (6/5)`; uniqueness
among coefficient zeros in the ball. It uses no Duffing declaration and no rational leaf; its
reality step is the symmetry layer (`isometry_conjRefl.mapsTo_closedBall`, `rawF_conjRefl`).

`Examples/Fourier/Exponential/{Numbers,Algebra,Certificate,Analytic}` is the exponential Fourier
consumer: PlasmaLean's slab equation `ψ'' + (51/50)(e^ψ − 1) = 0` on the registered algebra
`ℓ¹_{6/5}(ℤ; ℂ)`. `Numbers` is generated (`exterior/tmp/lp_api_campaign_20261017/POST_MERGE/promotion_20261104/U-A/gen/`;
nine `native_decide` chunk checks, twelve `decide +kernel` checks); `Algebra` is the family level
(parametric in `ν ≥ 1` and `a : ℂ`: the symbol, `Λ`, the reflection and the even part, `F̃`, `DF̃`,
the symmetries and the raw coefficient equation); `Certificate` proves the four bounds on the
finite-matrix approximate inverse (`lpOneAlg.finMatrixCLM`), the enclosure of `e^ū` by the
finite-Taylor contract and the unique even real zero (`exponential_l1_solution`); `Analytic` reads it
through `Applications/Fourier/Realization` as `exponential_analytic_solution` (real-analytic, even,
`2π`-periodic, the sum of its Fourier series, holomorphic on `|Im z| < log (6/5)`; uniqueness among
the zeros of `F̃` in the closed ball of radius `1/100`). It consumes `Analysis/Norm/Exponential`, the
`WeightedL1` head/tail, conjugation and reflection faces, `WeightedLp/Compatibility/FiniteBlockTransport`
and `Applications/Fourier/Realization`.

### M1 fix-forward scope

The consumer calls the operator series directly; the specialized `Fourier.L` round trip is
retired. Canonical finite-sum coordinate laws `coeff_sum` and `coeff_sum_single` live in Carrier,
and FiniteBlock uses them. The density theorem `dense_span_single` lives with the
generic LiftBound contract, exposed through Example81 after U37a; the p=∞ obstruction
`not_dense_finsupp_top`, which records the finite-p limitation, is staged in
`B5RecordFiniteSynthesisP2`. The two scalarized/p=2 Schur faces `norm_kernelCLM_two_le` and
`schurBound_weightedScalar_iff` of the pending Taylor ℓ² chain are staged with the removed
`WeightedLp/Taylor/TailKernel` module; pending slices remain outside the
root. Unused producer specializations are recoverable in the M1-FIX archive. The curvature socket lives in Core `Quadratic` (`comp_quadDeriv_sub`, `norm_quadComp_add_flip_le`); the geometry supplies `norm_AY_le_sqrt_tsum` over any nontrivially normed field (no completeness, no `1 ≤ ν`) with the tail upper bound `norm_tailDiagInf_le`. The
exact-attainment classification is superseded by the M1-PARK disposition below.

## Row-bounded convolution product and the polynomial carrier (U1, 2026-10-23)

The carrier definition does not select a convolution product on an arbitrary state
`X = ℓ^p_m`. A separately proved bounded self-product may equip a chosen framed state with an
explicit algebra service; the bilateral geometric ℓ² state has no such bounded self-product, while
the admissible polynomial ℓ² states considered here do. Coefficient algebra, state and operator
image remain different roles even when two roles use the same carrier.

| Module | Role |
| --- | --- |
| `Analysis/SequenceSpace/WeightedLp/Convolution` | The ratio rows `ratioRow w n (a, b) = w_n / (w_a w_b)` on Mathlib's addition fibres and the supplied bound `RowBound w q K` (rows in `ℓ^q(addFiber n)`, norm `≤ K`; sufficient, not a characterization), with the finite-exponent producer `RowBound.of_tsum_rpow_le` (at `q = 2`: summable ratio-square rows `∑_{a+b=n} (m_n/(m_a m_b))² ≤ K²`). For an additive monoid index, any frame, `1 ≤ p ≤ ∞` and the Hölder conjugate `q` over a complete nontrivially normed field, `convCLM h : X →L[𝕜] X →L[𝕜] X` is the bounded bilinear convolution in the physical norm: `coeff_convCLM` (Mathlib's `⋆ᵣ₊`), absolute fibre convergence `summable_norm_coeff_mul`, `norm_convCLM_le`/`norm_convCLM_apply_le` (`K` an upper bound), `convCLM_single_single`, determination by unit atoms `eq_convCLM_of_single` (`p ≠ ∞`), the unit `single 0 1` (`convCLM_unit_left/right`, no normalization), `convCLM_comm` (commutative index) and `convCLM_assoc` (`p ≠ ∞`, by atom density; no reciprocal-mass summability, no Fubini). `convCLM_eq_symbolAction₀` identifies left multiplication by `a` with the shipped ℓ¹ action `symbolAction₀ hC b` when `rawSymbol b = coeff a` (additive commutative group index); no second module action. No `Mul`/`NormedRing` instance on `WeightedLp`. The reciprocal-mass embedding `ℓ²_m → ℓ¹` is parked: `m_n = (1+|n|)² 2ⁿ` has the polynomial ratio rows but `∑ m_n⁻² = ∞`. Imports `Module`, `Operators/LiftBound`, `Algebra/Convolution/Ring` and Mathlib's `lpHolder`. |
| `Analysis/SequenceSpace/WeightedLp/Operators/Reweight` | The coefficient-preserving reweighting `reweightCLM hC hw : WeightedLp I E p →L[𝕜] WeightedLp I F p` under `ω^F ≤ C ω^E`, `0 ≤ C`, on an arbitrary index and the same exponent `1 ≤ p ≤ ∞` (`coeff_reweightCLM`; `norm_reweightCLM_le : ‖·‖ ≤ C`, an upper bound). Construction over a normed field, operator norm over a nontrivially normed field, no completeness; not an algebra homomorphism. Imports `Module` only. |
| `Analysis/SequenceSpace/WeightedLp/Operators/Reality` | On `X = WeightedLp M (WeightedScalar ℂ w) 2` with `hw : w (−n) = w n`: the conjugate reflection `conjReflL hw : X →L[ℝ] X` (`(Kx)ₙ = conj x₋ₙ`, `conjReflL_smul`), an involution (`conjReflL_conjReflL`) and an isometry (`norm_conjReflL`, `isometry_conjReflL`) with fixed points `conjReflL_eq_self_iff_coeff` (`K x = x ↔ x₋ₙ = conj xₙ`), the real subspace `realSub hw` (`mem_realSub_iff_coeff`, through the fixed-point face; complete), `restrictReal` of a `K`-commuting operator, `single_zero_mem_realSub`, and the commutations with `diagCLM`/`tailDiag` (conjugate-symmetric symbol, `tailSymbol_neg`), `headProj`/`tailProj` (symmetric head) and `finMatrixCLM` (`A (−i) (−j) = conj (A i j)`). Carrier faces only: imports `Operators/FiniteBlock`, not `Convolution`. The generic owner of the conjugate reflection: `Fourier.Quadratic.conjRefl` on `X₂ ℂ ν` is its geometric specialization; the ℓ¹ factors `lpOneAlg.coeffConj` (conjugation) and `lpOneAlg.refl` (reindexing) stay separate, with their ring/algebra laws |
| `Analysis/SequenceSpace/WeightedLp/Operators/RealityConvolution` | On a commutative index (`AddCommGroup M`): `conjReflL_convCLM`, `K (x ⋆ y) = K x ⋆ K y` for the row-bounded product `convCLM h` (`h : RowBound … 2 K`), the one face of the reflection that needs a product on `X`. Imports `Operators/Reality`, `WeightedLp/Convolution`; consumed by `Applications/Fourier/Eigenpair` (`conjReflL_eigenPot`, `conjReflL_eigenHeadJac`) |
| `Analysis/SequenceSpace/WeightedLp/Pairing` | For `h1 : ∀ n, 1 ≤ w n` (decisive): `embedL2 h1 : X →L[ℂ] ℓ²(M; ℂ)` (`‖·‖ ≤ 1`), the real pairing `pairing h1 x y = ∑ Re (conj xₙ yₙ)` (`pairing_eq_tsum`, `pairing_comm`, `abs_pairing_le`), the head forms, `pairing_finMatrixCLM`, `pairingR` on `XR` and `ofReal_pairing_headProj_eq_sum`. Imports `Operators/Reality`, Mathlib `l2Space` |
| `Analysis/SequenceSpace/WeightedL1/Bootstrap` | Geometric decay by nested contraction (namespace `RadiiPolynomial.Bootstrap`): the transfer `fixedPt_eq_of_semiconj`, `contractingWith_affine`, `affine_fixedPt_mem_range` (carrier-free; here because `Analysis` imports no `Core` and the bootstrap is its only consumer), the weight-lowering inclusion `l1Incl : ℓ¹_ρ →L ℓ¹_ν′` (`ν′ ≤ ρ`), the tail operator `diagMulCLM`, the head lift `headLift`, `memL1v_of_eq_zero_off`, and the bootstrap `exists_toRealSeq_eq_of_tail_gap` (finite gap `‖σₙ‖ ≥ c > ‖q‖` off a finite set, `q ∈ ℓ¹_ρ`, `∑‖vₙ‖ < ∞`, `σₙvₙ + (q ⋆ v)ₙ = 0` off a finite set ⇒ `v ∈ ℓ¹_ρ`; the strict gap is sharp for this norm criterion: `q = δ₀`, `σ = −1`, `c = 1`, `ρ = 2`, `vₙ = 2^{−|n|}` fails) with its growth corollary `exists_toRealSeq_eq_of_growth`. Imports `WeightedLp/Module`, `Chebyshev/Scalar` (`geomFiberZ`), `WeightedL1/Diagonal`; no other `WeightedL1` module imports `WeightedLp`. In the `WeightedL1` facade, which therefore also imports `WeightedLp/Module` and `Chebyshev/Scalar` (no module imports that facade, so no cycle) |
| `Analysis/SequenceSpace/WeightedLp/Compatibility/WeightedL1Iso` (amended) | Beside `toLpₗᵢ` (`p = 1`): the bounded inclusion `lpOneAlg.toLinf : lpOneAlg M E →L[𝕜] WeightedLp M E ∞` (`coeff_toLinf`), the one home of the ℓ¹ → ℓ^∞ inclusion (it replaces `Fourier.toY`) |
| `Analysis/SequenceSpace/WeightedLp/Operators/{FiniteBlock,TailDefect}` (amended) | `finMatrixCLM_comp_headProj` (`A ∘ P_F = A`) in `FiniteBlock`; the disjoint-support aggregation `norm_comp_headProj_add_diagCLM_le` (`‖H P_S + diag r‖ ≤ max a t` under `P_S H P_S = H P_S`: head inputs land in the head; the identity with a proper head separates this from `P_S H = H`) in `TailDefect` beside `coeff_disjoint` |
| `Analysis/SequenceSpace/WeightedLp/{Carrier,Operators/HeadProj}` (amended) | In `Carrier`, beside `coeff_smul`/`coeff_single_self`: `single_ne_zero` (`r ≠ 0 → single m r ≠ 0`; any normed field, frame and exponent) and `coeff_real_smul` (`coeff (r • x) n = (r : ℂ) * coeff x n` for `r : ℝ` on any complex framed carrier, any exponent). In `HeadProj` (section `ProjectionApplyNorm`): `norm_headProj_apply_le` (`‖P_S x‖ ≤ ‖x‖`; any normed field, frame and exponent `1 ≤ p`, by `lp.norm_mono`); the operator-norm face `‖P_S‖ ≤ 1` is a probe (no consumer once the apply face is direct) |
| `Examples/Fourier/Duffing/Polynomial/Eigenpair/{Numbers,Certificate,Analytic}` | The certified right eigenpair of the polynomial-carrier Duffing linearization and its analytic eigenfunction. `Numbers` is generated (`exterior/tmp/lp_api_campaign_20261017/POST_MERGE/promotion_20261104/U-E/gen/`): the candidate `(v̄, λ̄)`, `λ̄ = 839043344273/200000000000`, the bordered head inverse, the face constants, `checks_data`, `checks_radii` (`decide +kernel`) and `checks_Y0`, `checks_Z0`, `checks_Z1`, `checks_Z2` (one `native_decide` each); `Certificate`: `duffEigen : EigenData polyWeight_neg` at `μ = duffing (1/10) 4`, `S = headF 10`, `q = −2 xPoly`, the rational-to-real bridges, `duff_{Y0,Z0,Z1,Z2}_le`, `duffing_eigenpair` (ball of radius `1/20` about `ybar`, (E1) ∧ (E2), invertible real derivative, uniqueness in the closed ball) and `duffing_eigenpair_enclosure` (`\|λ − λ̄\| < 1/20`, `4 < λ`, `v ≠ 0`); `Analytic`: the bootstrap glue (`uStarL1 ∈ ℓ¹_{11/10}`, `duff_E1_shifted`, `exists_toRealSeq_eq_of_E1`) and the endpoint `duffing_eigenfunction_analytic` (`V = realRealization (coeff v)` real-analytic on `ℝ`, `2π`-periodic, nonzero, `V″ + V′/10 + 4V − 2uV = λV` with `u = FourierDuffing.Polynomial.solution`, and every conjunct of the two companions). Polynomial weight facts `polyWeight_neg`, `one_le_polyWeight` in `Polynomial/Algebra`; `coeff_embed`, `coeff_xPoly_eq_coeff_aTilde` public in `Polynomial/Analytic` |
| `Examples/Fourier/Duffing/Polynomial/{Numbers,Algebra,Certificate,Analytic}` | The second end consumer of the same Duffing problem on the physical polynomial carrier `ℓ²_m(ℤ;ℂ)`, `m_n = (1+|n|)²`: the numerical bundle `Numbers.Checks` (ONE `native_decide`; every clause consumed), the producer `polyRowBound : RowBound (weight) 2 10` and `polyModerate` with `polyProd = convCLM polyRowBound` (`Algebra`), the independent certificate (`Z₂ = 2κ‖A‖` from `norm_convCLM_le`, `Z₁` through `convCLM_eq_symbolAction₀` and `TailDefect`) giving the unique raw zero `xPoly` in the ball of radius `1/10000` (`Certificate`; reuses only the carrier-free rational bridges of the adapter `Certification/Fourier/Quadratic` and the leaf-parametric mirror at the instance-1 leaf, with one `decide +kernel` coverage check `Numbers.idx2_eq_chunks`; the zero of `G` transfers to the raw zero through the finite-head solver service of `Operators/FiniteBlock` and `Core/Transport.existsUnique_zero_transport`), and (`Analytic`) the comparison `(1+|n|)² ≤ 20 (6/5)^|n|`, `embed = reweightCLM …`, the identification companion `embed_aTilde_eq_xPoly` and the end theorem `certified_analytic_solution`, whose analytic conjuncts are `duffing_analytic_solution` of the realization bridge transported along `coeff xPoly = coeff aTilde`. |

## Post-U37a exact-attainment disposition (M1-PARK migration)

This successor delta supersedes only the exact-attainment classification in the earlier M1-FIX
record. The Fourier consumer retains the cross-exponent upper bound `norm_tailDiagInf_le` and
its NormedField construction/coordinate laws. It does not consume the exact-attainment theorem.
`norm_tailDiagInf_eq` and the exclusively used unit-magnitude, empty-index and linear-application
support are proved in the frozen records and parked from the shipped API. Their exact source,
elaborated types and axiom references remain recoverable; parking is not loss of proof history.

The reciprocal-weight witnesses are the generic `invWeightSeq`, `norm_apply_invWeightSeq` and necessary
`norm_equiv_inv_weight` (unchanged FQNs, RCLike hypotheses). At M1-PARK the reciprocal-weight witnesses moved to LiftBound.
B5 subsequently staged them in `B5RecordFiniteSynthesisP2` (staged record: `exterior/api_v2/probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean`); they are not part of the current shipped interface.
The unused `invWeightSeq_apply` and `coeff_invWeightSeq` coordinate views are parked. The
production upper-bound Fourier route and U37a's kernel-column migration are unchanged. The exact source, type and execution records are under the local campaign’s
`codex/W2_INTEGRATION_v1/M1_PARK_v1/` evidence directory.

After U37a, LiftBound is exposed through the production Taylor consumer. The three
boundary-support faces are staged in `B5RecordFiniteSynthesisP2` (above) and are reachable from no production root. The parked support
was not uniformly RCLike: the two linear application laws used NormedField and the empty-index
law used NontriviallyNormedField; their archived statements retain those weaker assumptions.

## Recoverable mathematical records

The cross-geometry character countermodels, four selected semantic/degree Hessian faces,
and finite-fiber wrapper/embedding/ring-equivalence layer with its three exclusive CV tests
are recorded in the [typed recovery record](../probes/records/B2_staged_services/MANIFEST.json)
outside the shipped interface. The raw finite convolution core, generic Cauchy product and
`toPowerSeries` coefficient view, first degree-drop bound and numeral simp service remain shipped.
The additional finite-fiber laws and bundled power-series bridge belong to
`B5RecordFiniteFiberConvolution` and `B5RecordPowerSeriesBridge`. The retained Taylor
power-series-on-ball and full-disc analyticity services remain shipped; the converse local
analytic representation and extensionality family belongs to `B5RecordTaylorAnalytic`. The bounded Taylor evaluator is the universal arrow in `Geometric/Aeval`;
`Geometric/Evaluation` identifies its real specialization with the coordinate series. Bound task records carry execution,
acceptance, source-generation and declaration-disposition facts.

Chebyshev boundary-character separation, local physical determination and the specific reverse-map
injectivity exit are also in that recovery record. The bounded coefficient map
`CrossGeometry.chebyshevToTaylorCLM` is staged in the Joukowski cross-geometry record, at `exterior/api_v2/probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean`. Additional character and inverse-map laws
are recovered by `B5RecordJoukowski` and `B5RecordPhysicalSpectrum`; their presence in recovery
does not add them to the shipped interface.

B4 stages the generated-only `IVP.TaylorCertQ` contract, its slot-choice supports and the
former Taylor `AllGenerated` test together in the outside-source record's
[`staged/U42bGeneratedContract.lean`](../probes/records/B4_weight_and_generated_services/staged/U42bGeneratedContract.lean)
and [`staged/AllGenerated.lean`](../probes/records/B4_weight_and_generated_services/staged/AllGenerated.lean).
`StdIVPDataQ`, `ofStd`, realization, the per-bound checks and soundness services, and the
production Example81 kernel-column route remain. The unused `RadiiPolynomial.SeqL1`
spelling retires; the weighted-ℓ¹ carrier and block-diagonal services remain. Positive,
submultiplicative and unit-normalized weight assumptions stay separate, and extraction
retains its explicit lower bound. The [B4 binding record](../probes/records/B4_weight_and_generated_services/AFTER_ACCEPTANCE.json)
binds installation, execution evidence and declaration status.

## Universal geometric evaluation (U25)

`Geometric/Aeval` constructs the bounded algebra arrow from `Geometric/Basic` and
`WeightedL1/UniversalProperty`. `Geometric/Evaluation` imports that arrow and first proves
`l1Weighted.aeval_of_norm_le_apply_real` directly from its series. Real multiplicativity then
follows from `map_mul`; it does not construct another algebra hom. Linear and algebraic
views are the standard projections of `aeval_of_norm_le`. Termwise differentiation remains
in `EvaluationDerivative`.

The coordinate function is defined at every real input; its agreement with the bounded
arrow carries the closed-disc admissibility condition. Generic target estimates retain
`max (1) ‖1‖` without a new `NormOneClass` assumption. Zero trace and the anchored primitive
remain available at every positive weight, including weights below one; evaluation at minus
one retains its separate admissibility condition. The cross-geometry transport
`CrossGeometry.chebyshevToTaylorCLM` and its naturality are staged (the Joukowski cross-geometry record named above);
the live physical-character statements of `Chebyshev/Spectrum/*` retain their geometric hypotheses.

At installation, [`AFTER_ACCEPTANCE.json`](../probes/records/U25_universal_geometric_evaluation/AFTER_ACCEPTANCE.json) binds the accepted source/object generation, executed owner/consumer and independent model/data checks, and declaration dispositions.
