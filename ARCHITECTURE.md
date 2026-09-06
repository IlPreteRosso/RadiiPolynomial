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
| `Algebra/Polynomial` | Semantic `MvPolynomial` bridges and computable `CompPoly` syntax |
| `Analysis/SequenceSpace/WeightedL1` | Generic weighted `l1` sequence algebras and their universal-property API (`liftCLM`, atom extensionality) |
| `Analysis/SequenceSpace/Geometric` | Taylor coefficient algebras, differentiation, evaluation, analytic extensionality, and radius restriction |
| `Analysis/SequenceSpace/Chebyshev` | Bilateral storage, the flip-fixed physical algebra, evaluation, and analytic extensionality |
| `Analysis/SequenceSpace/CrossGeometry` | Bounded maps between coefficient geometries and their evaluation and differentiation naturality |
| `Core` | Abstract Newton map, radii polynomial, canonical bounds, and reusable bounds |
| `Operators/Matrix` | Finite weighted matrices and their continuous-linear realizations |
| `Operators/BlockDiagonal` | Finite-plus-tail operators, lifts, composition, and scalar specialization |
| `Certification` | RadiiPolynomial witness reductions and adapters to external LeanCert |
| `Applications/IVP/Taylor` | Taylor-coefficient IVP operator, Jacobian, theorem, and analytic bridge |
| `Applications/IVP/Chebyshev` | Chebyshev-coefficient IVP operator and block-diagonal realization |
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
- Power-series evaluation and termwise differentiation remain separate modules.
- Taylor and Chebyshev residual coefficients remain raw `Nat -> Real` values that are
  immediately consumed by the approximate inverse.
- `SystemBlockDiagData.composedApprox` is shared operator infrastructure; Taylor's
  `IVP.ivpComposedApprox` name is retained as a compatibility alias.
- Each production example preserves the progression
  `Numbers -> Algebra -> Certificate -> Analytic` when all four layers apply.

## Example Groups

```text
Examples/
  FiniteDimensional/Example245
  PowerSeries/Example77
  IVP/Taylor/Example81
  IVP/Taylor/Example83
  IVP/Chebyshev/Example1421
```

Book example numbers remain in paths and namespaces, while the parent directories expose
the mathematical problem family and discretization.
