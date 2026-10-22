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
| `Analysis/Norm` | Carrier-neutral finite-sum inequalities in `RadiiPolynomial.NormHelpers` (`FiniteSum`, Mathlib-only imports): real-valued (weighted triangle, uniform factor, index swap) and normed-ring (`norm_sum_mul_pi_le`: `‖∑ i, f i * h i‖ ≤ (∑ i, ‖f i‖) * ‖h‖` over any `NonUnitalSeminormedRing`), the single proof home of that bound, invoked directly by polynomial, Galerkin and Taylor Jacobian consumers |
| `Analysis/SequenceSpace/WeightedL1` | The frame-free `lpOneAlg M E` carrier, chosen `FiberTrivialization 𝕜 M E`, fiber atoms, scalar coordinates and weighted norm identities form the base. A frame is explicit mathematical data: equal weights need not give equal convolution products. `Algebra` registers one additive-index operation family globally; `instMulMul`, `instMulOne`, `instMulRing`, `instMulNormedRing` remain named explicit data. Both convolution-compatibility families retain their own instances. Arbitrary multiplicative monoids use the `Additive M` index/fiber presentation. The tsum and finite-antidiagonal routes retain their distinct completeness hypotheses. Submultiplicativity, unit normalization and an explicit coefficient-extraction lower bound remain separate assumptions. `UniversalProperty` retains the bounded `liftCLM`/`liftAlgHom` contracts, atom computation and extensionality; `Diagonal` retains bounded diagonals and finite head/tail projections, including tail contractivity under `NormedField` without a frame or completeness assumption. Exact column/multilinear and head/tail aggregation families belong to staged records, not shipped `Columns`/`Multilinear` modules. |
| `Analysis/SequenceSpace/CharacterTopology` | The pointwise character-topology family is owned by the staged topology record; the former shipped owner module is removed. |
| `Analysis/SequenceSpace/Geometric` | Taylor coefficient algebras, retained differentiation/evaluation and full-disc complex power-series synthesis (`Analytic`) use the canonical additive-index weighted ℓ¹ structure on `ℕ`. The geometric fibers are `WeightedScalar` abbreviations with the standard frame. Analytic extensionality, radius-restriction and character-spectrum families are owned by staged recovery records; they are not shipped owners. |
| `Analysis/SequenceSpace/Chebyshev` | Bilateral storage with fiber `geomFiberZ`, the flip-fixed physical algebra, symmetrization and retained evaluation/U-conversion primitives, bordered storage and retraction, and the finite Galerkin carrier `FνN` with padding `ιN` and projection `πN`. The full one-sided cosine principle, physical/bordered isometric equivalence and Laurent/physical spectrum families have staged record ownership. Retained one-sided restriction/embedding primitives used by the IVP remain shipped; record ownership does not restore the full old interface. |
| `Analysis/SequenceSpace/CrossGeometry` | The Joukowski map `CrossGeometry.joukowski z = (z + z⁻¹) / 2` and the symmetric Laurent generator `joukowskiGen ν = (e₁ + e₋₁) / 2` in `l1Chebyshev ν`, symmetric by `joukowskiGen_isSymmetric` and, for `1 ≤ ν`, an element `joukowskiGenSymm ν` of the physical algebra (`Joukowski`; consumed by `Chebyshev/Spectrum`). `Derivative` has no public declaration. The bounded maps between coefficient geometries (`joukowskiAeval`, `chebyshevToTaylorCLM`), their evaluation and character naturality and the derivative naturality square are staged in `B5RecordJoukowski` (`exterior/api_v2/probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/`), not shipped. |
| `Core` | Abstract Newton map and radii polynomial with local and finite-dimensional faces (`Theorem`), canonical bounds (`Bounds`), the degree-general `Z₂` engine (`AlgebraZ2`), and finite-dimensional pulled-back-norm and isometric zero transport (`Transport`); every declaration of the four modules lies in namespace `RadiiPolynomial` (the former root family of `Theorem` — `I_E`, `NewtonLikeMap`, `generalRadiiPolynomial`/`radiiPolynomial`/`simpleRadiiPolynomial`, `general_radii_polynomial_theorem`, … — moved there in the DEFER round, no aliases) |
| `Operators/Matrix` | Finite weighted matrices and their continuous-linear realizations, bundled as the algebra equivalence `FinWeightedMatrix.toWeightedCLMAlgEquiv` (units correspond: `isUnit_toWeightedCLM_iff`); matrices over a normed real algebra acting on `R^n` with the sup norm (`SupNorm`: `matCLM` and the row-sum operator-norm bound `opNorm_le_of_rowSum`) |
| `Operators/BlockDiagonal` | Finite-plus-tail operators, lifts, composition, and scalar specialization; `Basic` imports only `Geometric/Scalar`, `Norm/FiniteSum`, `Matrix/WeightedNorm` and Mathlib's `FDeriv.Add`/`FDeriv.Mul`, while `WeightedL1` imports `Core/Bounds` and `Geometric/Basic` |
| `Certification` | RadiiPolynomial witness reductions, adapters to external LeanCert, with the residual/Neumann and finite-support completeness families owned by staged recovery records; the LeanCert-free exact-rational finite-matrix layer `Rational/Matrix` (stored ℚ columns, the `I − A B` defect, weighted and block matrix norms in exact ℚ, `activeBlockNormQ`, the shared `blockActionQ` with its cast bridge `SystemBlockDiagData.action_eq_blockActionQ`, used by the Chebyshev `Y₀` soundness `ChebyshevIVP.StdChebIVPData.Y₀_le_of_Q` at tail multiplier `(2n)⁻¹` (the Taylor `Y₀` clause at `n⁻¹` is staged in `B5RecordTaylorY0P1`), and the CLM-norm and entry bridges; imports only `Operators/BlockDiagonal/Scalar` and `Mathlib.Data.List.GetD`), imported by `Rational/Grid`, `LeanCertAdapter`, the facade and the family faces `IVP/Taylor`, `IVP/Chebyshev`, `PowerSeries/PolynomialZero`; `IVP/Chebyshev` is the facade of the eight modules `IVP/Chebyshev/{QLayer, Common, Y0Z0, TC, Z1, Face, Kernel/QLayer, Kernel/Face}`, whose imports form the DAG `QLayer → Y0Z0 → {TC, Z1} → Face → Kernel/Face`, `Common → {TC, Z1} → Kernel/QLayer → Kernel/Face` (`TC` and `Z1` independent), with `QLayer` importing `Rational/Matrix` and `Applications/IVP/Chebyshev/Polynomial` (the narrow owner, not the facade), `Common` importing `Applications/IVP/Chebyshev/Polynomial`, `Y0Z0` importing `Rational/Grid` and `Face` importing `RadiiPolynomialQ`; the retained Taylor family face `IVP.StdIVPData.ivpCoeffs_abar_eq_zero_of_compPoly`; the specialized Chebyshev semi-major certificate family has staged record ownership |
| `Tactic` | `finmatrix_bound` (`FinMatrixBound`, importing `LeanCertAdapter`) applies a supplied bridge and closes its rational certificate check through the configured LeanCert verification route. Polynomial derivative macros and `compPolyOf%` reification are retired service interfaces with historical recovery material. Dyadic syntax, elaboration, evaluators and the dyadic self-test have staged ownership; production `finmatrix_bound`, Taylor `t_bound` and their shared data remain shipped. |
| `Applications/IVP/VectorField.lean` | Geometry-free ODE right-hand side `IVP.vectorField` of a `CompPoly` system and the retained syntactic Lipschitz faces (`vectorField_lipschitzOnWith`, `lipschitzOnWith_vectorField_closedBall`, `exists_lipschitz_vectorField_closedBall`); imports `CompPoly/{Core,Bounds,Derivative}` only (no ℓ¹ carrier); both discretizations state their function-space conclusions through it |
| `Applications/IVP/Taylor` | Taylor-coefficient IVP operator, Jacobian (with the syntactic `ivp_Dφ_norm_le_of_compPoly` socket), theorem, analytic bridge (`Analytic`: the ball-solution predicate `IVP.IsBallSolution` — initial value, trajectory in `closedBall 0 R` and the ODE on `(-ν, ν)`, with no analyticity hypothesis — met by the canonical solution `x_analytic` and unique on the interval), real analyticity of the canonical trajectory (`Analyticity`: `IVP.analyticOnNhd_x_analytic`), complex time (`ComplexTime`: complex trajectory and vector field), and the example-facing polynomial faces `StdIVPData.existsUnique_of_compPoly`, `Z₁_le_of_compPoly`, `Z₂_le_of_compPoly`, `analytic_existsUnique_of_compPoly_of_radii`, `StdIVPData.existsUnique_ivpCoeffs_of_compPoly`, `StdIVPData.analytic_existsUnique_of_compPoly` |
| `Applications/IVP/Chebyshev` | Chebyshev-coefficient IVP operator, block-diagonal realization, polynomial residual/Jacobian adapter (`ChebyshevIVP.banachField` and syntactic Z₁/Z₂ constants), return to the IVP, analyticity of the canonical realization across `[-1, 1]` for `ν > 1` (`Analyticity`), and the example-facing faces `StdChebIVPData.existsUnique_of_compPoly`, `StdChebIVPData.Z₂_le_of_compPoly_max`, `StdChebIVPData.defect_finBlockNorm_lt_one_of_radii`, and (`AnalyticPolynomial`) the canonical-witness face `exists_canonical_solution_of_compPoly_of_evalBound` (a uniform evaluator bound `C` on `[-1, 1]` and `C · (‖ā‖ + r₀) ≤ R` give a coefficient witness `xTilde` whose `x_sol xTilde` is the unique solution on `[-1, 1]`) with its consumers `solution_existsUnique_of_compPoly` (`C = 2`), `solution_existsUnique_of_two_le_of_compPoly`, `analytic_solution_existsUnique_of_two_le_of_compPoly` (`C = 1` at `2 ≤ ν`); `chebyshevShiftDiv` is by definition the U-factorization `-(uIntegrate (chebyshevToU c))`, and the specialized shift-div and semi-major families are recovered in staged records; the XCheb defect lift is the XL1 lift transported along `OneSided.restr`/`natEmbed`, and `composedApproxCheb` abbreviates `BlockDiagLift.composedApproxCLM` (`BlockDiagonal`, imports `Chebyshev/OneSided`); `TCtail` is componentwise `lpOneAlg.tailProj (Icc 0 N) ∘ chebyshevShiftDiv_CLM` and `TCtailElem_norm_le_tail` lives with it (`Lambda`, imports `WeightedL1/Diagonal`); row 0 of `F` is endpoint evaluation (`chebyshevIvpCoeffs_zero_eq_eval`, `FAseq_zero_eq_eval`), the additional `IVP.chebyshevBoundary` and split-boundary family belong to staged IVP-boundary records |
| `Applications/IVP/Boundary.lean` | The split-boundary and anchored-primitive family has staged IVP-boundary record ownership; this former shipped module is removed. |
| `Applications/PowerSeries` | Polynomial zeros `P(x) - c = 0` on `ℓ¹_ν` for a univariate `CompPoly` of any degree: the approximate inverse and derivative and the `Z₁`, `Z₂` bounds (`PolynomialZero`); `Z₂` bounds for maps whose derivative is affine in `leftMul`, as a corollary of the degree-general engine (`AffineZ2`) |
| `Applications/FiniteDimensional` | The row-sum enclosure face on finite-dimensional normed real algebras, rational polynomial certificates (`StdFinDimData`, `ChecksC`) and scalar specialization remain shipped. The periodic-point family is owned by a staged record. |
| `Applications/Galerkin` | The polynomial Galerkin face (`Face`): a `CompPoly` system between a lift, a projection and continuous linear parts (`polyFace`), its derivative `DpolyFace` from the syntactic Jacobian, the centred bounds from `derivativeCentredBound`, with consumers using the generic bound `norm_DpolyFace_sub_le`; the componentwise maps `Galerkin.I`/`Galerkin.Pi'` are `ContinuousLinearMap.piMap` of `ιN`/`πN` |
| `Examples` | End-to-end mathematical applications and numerical certificates |

The external LeanCert library remains a Lake dependency. `Certification/LeanCertAdapter.lean`
keeps weighted-term and system block-diagonal action evaluators with their correctness proofs.
The exact-ℚ layer lives in `Certification/Rational/Matrix.lean`; the production matrix tactic is
`finmatrix_bound`. Dyadic checker support is recovered outside shipped imports.

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
probes `tests/FT/ImportOrderA.lean`/`ImportOrderB.lean`), `TC` (tactic quotation tests,
`tests/TC/FinMatrixBound.lean`) and `WL` (weighted-ℓᵖ regression checks, including `LiftBoundChecks`). `TailKernelChecks` and the full `Example81L2/` caller chain
belong to the staged R30 finite-tail-kernel record. The finite-fiber convolution law probes
belong to `B5RecordFiniteFiberConvolution`. The former `Example81L1NewAPI` witness is retained in
the early-U37a recovery record after its production migration.


## API-v2 finite-p integration (2026-10-19)

This section describes the isolated API-v2 copy. `WeightedLp/Carrier` and `Module` provide framed scalar coordinates, atoms and completeness on Mathlib lp. `Operators/LiftBound` specifies bounded finite synthesis by its extension, atom computation, pointwise bound and uniqueness/converse laws. Construction uses a normed field and a complete target; operator-norm statements retain a nontrivially normed field. `Operators/Schur` supplies an independent sufficient producer, with the coefficient identity relating its operator to the canonical extension. Absolute row summability inferred from unconditional convergence remains a separate real/complex assertion.

`Compatibility/WeightedL1Iso` identifies the p=1 carrier; bounds for an already supplied operator require no scalar completeness. `Compatibility/TaylorTailL1` owns the coefficient/operator bridge. The family numerical certificate and its shared per-pair assembly are in `Certification/IVP/Taylor`; analysis has no certification dependency. `WeightedScalar.instCompleteSpace` now transfers completeness through the existing scalar equivalence and works for complete trivially normed fields.

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
`q : X × X → Y` at ν ≥ 1. `TailDiagonal` supplies the return map Y → X, the separate X → X
diagonal, and the single coefficient-disjoint square-norm identity. `Bilateral.Quadratic`
composes the product with a return map. `Fourier.ConvolutionAction` owns only the geometric moderation constant; `TailDefect` and `FiniteBlock` own the full shared-input defect and finite
matrix composition before entrywise modulus. The resulting operator-norm aggregation is an
upper bound, not an equality of independently optimized summands. The physical matrix map
`matrixOf T n k = coeff (T (single k 1)) n` belongs to `FiniteBlock`.

`Examples/Fourier/Duffing/{IkData,Numbers,Algebra,Certificate}` gives the quadratic
Helmholtz–Duffing coefficient problem `u'' + c₁ u' + c₂ u − u² = c₃ cos t`.
The numerical candidate and four bounds give a radii-polynomial certificate, raw coefficient
zeros, a local uniqueness/enclosure statement and conjugate-reflection reality. The raw residual
is sequence-valued: the identity with the bounded map is coefficientwise through `rawA`, not
an unsupported assertion that the residual itself belongs to Y. The head certificate has no
phantom c₃ parameter; forcing and its residual bound retain c₃. The default Examples facade
imports this actual certificate. Reconstruction as a periodic C² function is a separate result.

### M1 fix-forward scope

The consumer calls the operator series directly; the specialized `Fourier.L` round trip is
retired. Canonical finite-sum coordinate laws `coeff_sum` and `coeff_sum_single` live in Carrier,
and FiniteBlock uses them. The density theorem `dense_span_single` lives with the
generic LiftBound contract, exposed through Example81 after U37a; the p=∞ obstruction
`not_dense_finsupp_top`, which records the finite-p limitation, is staged in
`B5RecordFiniteSynthesisP2`. The two scalarized/p=2 Schur faces `norm_kernelCLM_two_le` and
`schurBound_weightedScalar_iff` of the pending Taylor ℓ² chain are staged with the removed
`WeightedLp/Taylor/TailKernel` module; pending slices remain outside the
root. Unused producer specializations are recoverable in the M1-FIX archive. The derivative
Lipschitz bounds `Bilateral.norm_Dquad_sub_le` and `norm_Dquad_sub_le_AY` require a complete
nontrivially normed field and use ‖2‖≤2 and the tail upper bound `norm_tailDiagInf_le`. The
exact-attainment classification is superseded by the M1-PARK disposition below.

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
