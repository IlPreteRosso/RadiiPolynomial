---
name: radii-poly-api-design
description: Design and refactor the RadiiPolynomial Lean API while preserving its mathematical layering, reusable-module boundaries, and compiling examples (project-specific rules; the formalization PROCESS — unit pipeline, worker assignment, peer harnesses, Aristotle, research gaps — is the sibling skill lean-api-design). Use for new formalizations, API extraction, proof cleanup, module moves, typeclass design, polynomial evaluation bridges, IVP or Chebyshev infrastructure, and certificate integration.
---

# RadiiPolynomial API Design

Treat the tracked repository copy of this skill as canonical. Keep the installed Claude,
Codex and Antigravity mirrors byte-identical to it (symlinks under `~/.claude/skills/`,
`~/.agents/skills/` and `~/.gemini/antigravity-cli/skills/`).

## Establish Live Context

- Work in the nested Git/Lake checkout. Read its `ARCHITECTURE.md` for current
  module boundaries, import rules, and public facades; avoid duplicating that inventory here.
- Read the curated project-memory index identified by `AGENTS.md`, then only relevant notes.
  Verify dated status and declaration names against the live source and pinned Mathlib.
- Inspect Git state and preserve concurrent edits. Keep feasibility investigations in the
  agreed ignored `tmp/` folder until concrete consumers justify promotion within the user's scope.
- Search existing APIs before adding declarations. Consult `docs/reference_book/` when extending
  a book theorem or certificate. Do not commit or push unless asked.

## Universal Properties Specify the API

- For a universal construction, expose the induced arrow, its computation on generators,
  and extensionality on generators. Include the converse identifying every eligible arrow
  with its lift; a constructor alone does not express the full specification.
- Let the determining data set the parameters and assumptions: indices, weights, fibers,
  scalars, and targets remain general where the proof permits. Pass varying bounds or
  summability witnesses explicitly rather than strengthening typeclasses.
- Use universal properties at design time and ordinary algebra/linear maps at proof time.
  Do not introduce categorical packaging when the existing lift/ext API expresses the result.
- Reuse the weighted `l1` lift and column-bound APIs for operators, and algebra lifts for
  multiplicative evaluation. Pointwise bounds can require weaker assumptions than operator norms.

## Use Friction Carefully

Work from a concrete consumer through repeated friction to a reusable bridge and a second
consumer. Classify obligations as equation-specific, representation-specific, or structural.
Keep incidental finite/numeric cleanup in examples; extract reusable mathematics at its owning
layer. Proof ugliness alone does not justify an abstraction. Preserve public interfaces
by default; record authorized renames and retirements in `RENAMES.md`.

## Preserve Core Boundaries

- Follow `Algebra/Analysis → Core/Operators → Applications → Examples`.
  `Certification` and `Tactic` are adapter layers; reusable modules never import `Examples`.
  Use facades at application boundaries and narrow owning imports inside the library.
- Keep `general_radii_polynomial_theorem` in `RadiiPolynomial.Core` as the basis-independent
  anchor. Application layers should reduce their work to its bounds and hypotheses.
- Keep `CompPoly` as the computable certificate representation and `MvPolynomial` as the
  semantic algebraic representation.
- Keep `CompPoly.evalBanach` as the public completed evaluator. Treat lower construction stages
  such as `evalAlg` as implementation bridges unless a genuine consumer requires them.
- Use the `evalBanach`/`toMvPoly` bridge and the universal property of `MvPolynomial` for
  equational statements such as substitution and composition.
- For regularity statements, induct at the most algebraic suitable layer, normally
  `MvPolynomial.induction_on`, rather than over the larger `CompPoly` syntax.
- Keep power-series evaluation and termwise differentiation in separate modules.
- Keep Taylor and Chebyshev as sibling discretizations. Raw IVP residual coefficients
  remain raw sequences; the preconditioned map `G` is the Banach self-map. Do not invent a
  bounded approximate-inverse map on the unrestricted raw codomain.
- Distinguish bilateral Chebyshev storage from its flip-fixed physical algebra.
  With nonnegative storage, polynomial evaluation uses the symmetric extension `S(a)`
  and differentiation uses `S(h)`, where `(S(a))_k = a_|k|`.
  Chebyshev evaluation is multiplicative on the physical algebra, not arbitrary bilateral data.
- Reuse the generic `CompPoly` AST and semantic evaluator across geometries. Its Nat Cauchy
  coefficient interpreter is Taylor-specific; finite Laurent computation needs support evidence,
  since high Chebyshev modes can contribute to low output modes.
- Use `SystemBlockDiagData.composedApprox` as shared Taylor/Chebyshev operator
  infrastructure. The former `IVP.ivpComposedApprox` compatibility alias is retired.
- Reuse the Chebyshev `G = constG + TA(a) + TC(φ(a))` decomposition and derivative bridge.
  Use the shared split-boundary mechanism for return to the IVP.
- Residual correction belongs to `Certification/Residual`: a residual norm bound below one
  gives the matching one-sided inverse, including in noncommutative rings. Finite-support completeness
  does not by itself provide rational candidates or an effective search. Spectral
  classification is separate from these certificate consumers.
- Spectrum modules specialize `Gelfand.pointwiseTopology` through local instances;
  do not install a global topology on the character types.
- Keep the external LeanCert package as a dependency. Put only project-specific bridges in
  `Certification/LeanCertAdapter.lean`; never copy LeanCert into this repository.

## Typeclasses And Mathlib Alignment

Separate assumptions by mathematical strength (`SubMulWeightBase` versus `SubMulWeight`).
Use `lpOneAlgConvCompat` for alternative convolution-summability witnesses behind one ring
instance. Follow pinned Mathlib conventions; use `@[to_additive]` for faithful translations,
protecting fiber/scalar parameters with `dont_translate` where needed.

## Polynomial And Certificate Automation

Use the existing `compPolyOf%`, `pderiv_simp`, and `auto_poly_fderiv` where supported;
use `decide +kernel` for exact finite identities (`native_decide` only as a named, dispositioned exception; see the Trust policy below) and `finmatrix_bound` for weighted matrix bounds.
The current polynomial IVPs keep literal `f_cpoly` definitions. Examples 8.1 and 14.2.1
use `f_cpoly_reified` as a `rfl` witness for the elaborator, outside the certificate's
dependency path.

If automation cannot cross a representation boundary, add a reusable correctness bridge at
the owning layer. Do not expose internal representations merely to make a certificate reduce.

Use `CompPoly.normBound`, `lipschitzBound`, and `derivativeBound` and their Taylor/Chebyshev
faces for syntax-derived constants. These proofs follow the computable syntax; semantic
calculus still belongs at the `MvPolynomial` layer. The constants use triangle inequalities:
keep exact-arithmetic bounds when evaluated coefficients cancel, as in Example 8.1's Z₁.
Radius-independent second-derivative bounds concern syntactically quadratic expressions;
algebraic cancellation to a quadratic polynomial does not make its syntactic bound quadratic.

Reuse the Taylor `StdIVPData.Z₁_le_of_compPoly` / `Z₂_le_of_compPoly` and Chebyshev
`StdChebIVPData.Z₂_le_of_compPoly_max` faces. Per-example derivative or operator norm bounds
remain inputs where needed. Chebyshev still needs its full Z₁ column/leakage calculation and
a bound on `TC`; `norm_compPolyDerivative_le` bounds the nonlinearity's derivative, not Z₁.

## Example Layers

For polynomial IVPs use `Numbers → Algebra → Certificate → Analytic → Analyticity`
where applicable: data, equation-specific structure, bounds, function-space existence and
uniqueness, then proved analyticity. Keep complex-time results in their own layer.
Examples 7.7 and 2.4.5 have their own problem-specific routes; do not force them into the
polynomial IVP interface. Claim analyticity only when the theorem proves it.

Supply `f_cpoly`, the initial condition, numerical data and certificate bounds. Use
`StdIVPData.existsUnique_of_compPoly` / `StdChebIVPData.existsUnique_of_compPoly` for
coefficient zeros, Taylor's `analytic_existsUnique_of_compPoly_of_radii`, and Chebyshev's
`solution_existsUnique_of_compPoly` or its contractive/analytic variants for function-space
results. Coefficient faces derive differentiability; function-space faces also derive
evaluation compatibility and the vector-field Lipschitz witness. The radii-based faces
derive the defect bound below one.

Both geometries use `IVP.vectorField f_cpoly` for the real vector field and their respective
`banachField f_cpoly` for the coefficient nonlinearity. Retain per-example aliases and
explicit derivative formulas when certificate consumers need them, as in the Taylor examples.
Use `x₀` for Taylor initial data at time zero and `p₀` for Chebyshev initial data at
time minus one. Keep the numerical pipeline radius `r_minus` distinct from theorem
parameter `r₀`.
Use `f` for the vector field and `F` for the coefficient operator in new interfaces.

## Verification

Check focused targets while iterating; after changing reusable production modules or imports,
run `lake build` from the nested checkout, including all production examples. Reject new
`sorry`/`admit`, forbidden upward imports, and project-local warnings.
When rewiring certificates, compare final theorem axiom sets; a separate finite audit
does not enter a theorem's trust surface merely because its module is imported.

For isolated experiments, compile their dependency chain and audit theorem axioms; distinguish
experimental conclusions from production results. Documentation-only edits need their own
validation, not a Lean rebuild.

## Process

The formalization process (unit pipeline, worker assignment, peer harnesses, Aristotle,
research-level gaps) is the sibling skill `lean-api-design`; load both for formalization work.

## Project-Specific Lean Practice (2026-09-24, from the FILTER rounds; moved here from the universal set on Codex's review)

- **ν-free ℚ records**: `StdIVPDataQ L N` (A_col, DF_col, abar_Q, ν_q, stored `habar_size`) with
  `toStdIVPData q ν (hν : (ν:ℝ) = (q.ν_q:ℝ))`, default `toStd` from `0 < ν_q`, and the round trip
  `toStdIVPData_ofStd … = d := rfl` as the replay hook; `Checks` on the ℚ record, per-slot soundness at every realization,
  `certified_of_checks` derived from the override face `certified_of_bounds`.
- **Radii-polynomial faces**: `_of_le` override slot per bound; `anchoredBound c ρ p` (product rule
  Aₚ|q(c)| + |p(c)|A_q + AₚA_qρ) for Z₂ — it matches the book's constants on 2.4.5/2.4.7/2.4.9, and on 2.4.8 with the exact inverse;
  three-layer local theorem (local fixed point → single-Z zero theorem → four-bound corollary; the
  four-bound layer cannot serve a single-Z statement: f(x) = x − (0.4/π) sin(πx)); Z = Z₀ + Z₂(r₀)r₀
  for the direct-Jacobian form vs Z₀ + Z₁ + Z₂(r₀)r₀ for four bounds; `Enclosure`/`PairEnclosure`
  Prop records (IsUnit A derived by the finite-dim Neumann rung); EI face with `existenceInterval`
  = the anchored order-connected component of {r | radiiPolynomial … r < 0} and `def_2_4_4` as a
  forwarding definition.
- **Carriers and polynomials**: `FνN` (a `def` synonym of Fin (N+1) → ℝ with `inferInstanceAs`
  algebra and the weighted norm |x₀| + 2Σ|x_k|ν^k), `ιN` isometry into `symmetricSubalgebra ν`, `πN`
  contraction with ‖πN‖ = 1; multiply in Aν BEFORE projecting (πN is not an algebra hom);
  `evalBanach = aeval ∘ toMvPoly` gives Df from `pderiv`; "cast commutes with evaluation" gives ℚ
  mirrors; `supportBound`/`laurentRadius` give far-column cutoffs (Mfar = 82 = 2N + 2 for 14.2.1);
  `clm_apply_eq_sum` decomposes CLMs on `Fin L → X` into blocks (no Fin-1 collapse).
- **Trust policy (reconciles the older "native_decide for exact finite identities" default)**:
  kernel-checked closure is primary (`decide +kernel` on the unchanged ℚ Checks: 0.1–0.2 s per
  finite-dimensional certificate, 15 s for the L = 2 Chebyshev set on the pinned toolchain);
  `native_decide` only as a named, dispositioned exception (today only the library's `Example1421.data.habar_size := by native_decide`, a proposed
  trust-reducing wave-A fix; Example 14.2.1's Checks, > 900 s as one `decide +kernel`, has closed
  with 15 per-conjunct kernel lemmas in ≈ 110–121 s since round 5). The proposed FILTER budget (target 60 s, ceiling 300 s
  total per certificate) needs explicit acceptance before it is quoted as agreed.
- Toolchain-specific measurements and troubleshooting notes live in
  `FILTER-20260924/LEAN_PRACTICE_DISTILLED.md` §7–§8 with their evidence class; quote them with
  the class, never as laws.

### Generality and placement (user rulings 2026-09-25, D145/D146)

- **Generalize before a filter or landing decision.** Audit every API-side candidate for ad-hocness: a fixed number where a parameter belongs (dimension, degree, truncation N, weight ν, grid base, tolerance) or a particular algebraic expression form (x² − c, Fisher u − u², a cube-only face, a degree-2-only Z₂). A general `CompPoly` of any degree and any `L` is NOT particular; fixed numbers inside an example instance are fine. Write the general form as an experiment first; the decision waits for it.
- **Placement rule.** An inherited or example-level ad hoc helper is either generalized or moved in or near the family of examples that consume it (`Applications/<family>`, `Certification/<family>`, or the example directory), never left in the API core (`Core/`, `Algebra/`, `Analysis/`, `Operators/` general modules). Anything in the core is general over the family-neutral engine. Every new helper carries a placement statement (target module + why); consumers of an inherited helper are listed by grep in a migration table (generalize in place | move beside consumers | move into the example | delete after migration).
- Evidence: FILTER-20260924/ADHOC_AUDIT.md (the PS bundle was x∗x − c end to end; Core/AffineZ2 served only degree ≤ 2 on one carrier; the Z₀ checkers baked in base 10).
