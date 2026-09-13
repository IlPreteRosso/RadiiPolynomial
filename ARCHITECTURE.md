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
| `Algebra/Convolution` | Discrete convolution, ring convolution, and Cauchy products |
| `Algebra/Polynomial` | Semantic `MvPolynomial` calculus and computable `CompPoly` syntax, with Taylor and finite Laurent/Chebyshev interpreters, and certificate constants read off the syntax (`CompPoly/Bounds`, `CompPoly/Chebyshev/Bounds`: `normBound`, `lipschitzBound`, `derivativeBound`) |
| `Analysis/SequenceSpace/WeightedL1` | Generic weighted `l1` sequence algebras and their universal-property API (`liftCLM`, atom extensionality) |
| `Analysis/SequenceSpace/CharacterTopology` | Carrier-independent topology of pointwise convergence on continuous characters (`Gelfand.pointwiseTopology`) and the one continuity fact the spectrum modules need (`Gelfand.continuous_character_apply`) |
| `Analysis/SequenceSpace/Geometric` | Taylor coefficient algebras, differentiation, evaluation, analytic extensionality, radius restriction, full-disc power series and complex synthesis (`Analytic`), and the character space as the closed disc (`Spectrum`, which installs the shared `Gelfand.pointwiseTopology` as a `local instance`) |
| `Analysis/SequenceSpace/Chebyshev` | Bilateral storage, the flip-fixed physical algebra, evaluation, analytic extensionality, the Laurent character space as the closed annulus (`LaurentSpectrum`), and the physical spectrum: classification, Bernstein ellipse, series, topology, holomorphy on the open ellipse with endpoint analyticity (`Spectrum/*`); both character spaces install the shared `Gelfand.pointwiseTopology` as a `local instance` |
| `Analysis/SequenceSpace/CrossGeometry` | Bounded maps between coefficient geometries, their evaluation and differentiation naturality, and the character obstructions (`CharacterObstruction`: no real extension of the zero physical character, two complex extensions) |
| `Core` | Abstract Newton map, radii polynomial, canonical bounds, and reusable bounds |
| `Operators/Matrix` | Finite weighted matrices and their continuous-linear realizations |
| `Operators/BlockDiagonal` | Finite-plus-tail operators, lifts, composition, and scalar specialization |
| `Certification` | RadiiPolynomial witness reductions, residual (Neumann) certificates for approximate inverses and finite Bézout identities with finite-support completeness, and adapters to external LeanCert |
| `Applications/IVP/VectorField.lean` | Geometry-free ODE right-hand side `IVP.vectorField` of a `CompPoly` system; both discretizations state their function-space conclusions through it |
| `Applications/IVP/Taylor` | Taylor-coefficient IVP operator, Jacobian (with the syntactic `ivp_Dφ_norm_le_of_compPoly` socket), theorem, analytic bridge, real analyticity of the canonical trajectory (`Analyticity`: `IVP.analyticOnNhd_x_analytic`), complex time (`ComplexTime`: complex trajectory and vector field), and the example-facing polynomial faces `StdIVPData.existsUnique_of_compPoly`, `Z₁_le_of_compPoly`, `Z₂_le_of_compPoly`, `analytic_existsUnique_of_compPoly_of_radii`, `StdIVPData.existsUnique_ivpCoeffs_of_compPoly`, `StdIVPData.analytic_existsUnique_of_compPoly` |
| `Applications/IVP/Chebyshev` | Chebyshev-coefficient IVP operator, block-diagonal realization, polynomial residual/Jacobian adapter (`ChebyshevIVP.banachField` and syntactic Z₁/Z₂ constants), return to the IVP, analyticity of the canonical realization across `[-1, 1]` for `ν > 1` (`Analyticity`), and the example-facing faces `StdChebIVPData.existsUnique_of_compPoly`, `StdChebIVPData.Z₂_le_of_compPoly_max`, `StdChebIVPData.defect_finBlockNorm_lt_one_of_radii`, and (`AnalyticPolynomial`) `solution_existsUnique_of_compPoly`, `solution_existsUnique_of_two_le_of_compPoly`, `analytic_solution_existsUnique_of_two_le_of_compPoly` |
| `Applications/IVP/Boundary.lean` | Shared split-boundary and anchored-primitive mechanism for IVP realizations |
| `Examples` | End-to-end mathematical applications and numerical certificates |

The external LeanCert library remains a Lake dependency. `Certification/LeanCertAdapter.lean`
contains only project-specific bridges into that dependency.

## Import Rules

1. `Algebra` and `Analysis` do not import `Core`, `Operators`, `Certification`,
   `Applications`, or `Examples`.
2. `Core` may import `Algebra` and `Analysis`, but not application or certificate modules.
3. `Operators` may import `Core`, `Algebra`, and `Analysis`.
4. `Certification` may import reusable operators and the external LeanCert dependency.
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
- `RadiiPolynomial.Analysis.SequenceSpace.WeightedL1`
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
  `MvPolynomial.Calculus`.
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
  `Analysis/SequenceSpace/CharacterTopology.lean`, together with the single continuity fact
  `Gelfand.continuous_character_apply`. The three character-space modules
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
```

Book example numbers remain in paths and namespaces, while the parent directories expose
the mathematical problem family and discretization.
