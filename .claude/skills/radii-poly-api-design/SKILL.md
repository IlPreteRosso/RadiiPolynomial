---
name: radii-poly-api-design
description: Design and refactor the RadiiPolynomial Lean API while preserving its mathematical layering, reusable-module boundaries, and compiling examples (project-specific rules; the formalization PROCESS — unit pipeline, worker assignment, peer harnesses, Aristotle, research gaps — is the sibling skill lean-api-design). Use for new formalizations, API extraction, proof cleanup, module moves, typeclass design, polynomial evaluation bridges, IVP or Chebyshev infrastructure, weighted ℓ^p/ℓ² carriers and operator membership, Fourier consumers, and certificate integration.
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
  with its lift; a constructor alone does not express the full specification. For a shipped arrow advertised as
  universal, its computation and uniqueness/converse laws specify the actual canonical service and belong to its
  verified API contract; do not require manufactured proof-term references merely to retain that contract.
  Further faces ship only when they provide a justified endpoint service under the semantic production gate;
  elegance, historical capability, and an unused specialization are not shipping reasons.
- Let the determining data set the parameters and assumptions: indices, weights, fibers,
  scalars, and targets remain general where the proof permits. Pass varying bounds or
  summability witnesses explicitly rather than strengthening typeclasses.
- Explicit-data criterion: if a downstream statement must use a particular bound, radius or rate, expose
  it as a parameter or as data with its specification. Executable certificate inputs belong in a
  computable Type-level representation, with a Prop-valued correctness predicate or soundness theorem
  over that data; an existential proof or noncomputable choice is not an executable witness. Preserve
  qualitative existence interfaces when the consumer needs only existence, and hide implementation
  witnesses that no public specification or computation needs. When a quantitative interface is
  requested, identify whether the witness is already supplied, constructible from the existing
  assumptions, or needs a new mathematical/effectivity hypothesis.
- Use universal properties at design time and ordinary algebra/linear maps at proof time.
  Do not introduce categorical packaging when the existing lift/ext API expresses the result.
- Bridge first: identify the eligible coefficient families, including convergence and closure where needed. Prove one coefficient
  bridge expressing compatibility with the corresponding bundled operation, then derive laws through the bridge and the required
  injectivity/extensionality. Bundle a bijection with the structure proved: additive or linear compatibility gives ≃+ or ≃ₗ;
  a ring or algebra equivalence additionally needs the relevant multiplication, unit and scalar laws. A linear equivalence alone
  supplies no multiplication law. Do not assert a ring structure on all raw functions from a membership-qualified result.
- Soft layout preference: a section's lemmas build up to the instance or consuming declaration that ends it.
- For operators out of ℓ¹_v, reuse the weighted `l1` lift and column-bound APIs: the weighted column criterion is exact analytic
  admissibility. For operators out of ℓ^p_m, 1 ≤ p < ∞, use finite synthesis and its labelled producers with the complete-target
  hypotheses ("Two layers for membership and operators" below). Use algebra lifts for multiplicative evaluation. Pointwise bounds
  can require weaker assumptions than operator norms.

## Use Friction Carefully

Work from a concrete consumer through repeated friction to a reusable bridge and a second
consumer. Classify obligations as equation-specific, representation-specific, or structural.
Keep incidental finite/numeric cleanup in examples; extract reusable mathematics at its owning
layer. Proof ugliness alone does not justify an abstraction. Treat repeated consumer dependence on an internal representation as possible
structural friction: name the stable property needed and its owning layer before proposing an
interface lemma; distinguish this from intended public computation and witness use. Preserve intended mathematics and soundness while adapting essential consumers to the canonical API; existing public names and
representations have no backwards-compatibility veto. Record authorized renames and retirements in `RENAMES.md`.

## Preserve Core Boundaries

- Follow `Algebra/Analysis → Core/Operators → Applications → Examples`.
  `Certification` and `Tactic` are adapter layers; reusable modules never import `Examples`.
  Use facades at application boundaries and narrow owning imports inside the library.
- Boundary test: for a proposed module or face, name its coherent mathematical capability and public
  contract, the representation or design choice it hides where applicable, and the consumers/dependencies
  it simplifies. Likely changes in carrier implementation, norm registration, computable-versus-semantic
  representation or checker implementation are useful tests, not the only justification. Keep
  mathematically relevant parameters and trust assumptions visible. A file split alone does not establish
  a new abstraction boundary. A second consumer is useful evidence of reuse, but a concrete first
  application can already justify a boundary when it removes irrelevant dependencies.
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
  infrastructure.
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
use `decide +kernel` for exact finite identities where it is cheap and `native_decide` otherwise (accepted in certificates; see the Trust policy below), and `finmatrix_bound` for weighted matrix bounds.
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
research-level gaps) is the sibling skill `lean-api-design`; load both for formalization work. Handoff and re-entry (research
compass, proportional re-entry check, scoped readback, PROPOSAL labels): `lean-api-design` §Handoff and re-entry.

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
- **Trust policy (user ruling 2026-09-25/26)**:
  `decide +kernel` is preferred where it is cheap (0.1–0.2 s per finite-dimensional certificate, 15 s
  for the L = 2 Chebyshev set on the pinned toolchain; Example 14.2.1's Checks close with 15
  per-conjunct kernel lemmas in ≈ 110–121 s). `native_decide` is accepted in certificates and
  examples (standard Lean-community practice); `finmatrix_bound` itself closes through
  `closeBridgeWithVerificationTyped` (LeanCert's configured kernel/native/auto route), and a
  declaration's actual axioms are read from its `#print axioms` record, not from source hits. Records
  list the inherited `…._native.native_decide.ax_*` axioms as facts; talks and notes carry no
  caveat. New general API-side lemmas prefer kernel-checkable `decide`. Inventory =
  `grep -rn native_decide RadiiPolynomial --include='*.lean'`, never a hand-kept list. The proposed
  FILTER budget (target 60 s, ceiling 300 s per certificate) needs explicit acceptance before it is
  quoted as agreed.
- Toolchain-specific measurements and troubleshooting notes live in
  `FILTER-20260924/LEAN_PRACTICE_DISTILLED.md` §7–§8 with their evidence class; quote them with
  the class, never as laws.

### Generality and placement (user rulings 2026-09-25, D145/D146)

- **Family.** A family is a class of problems or discretizations sharing mathematical assumptions and interfaces (polynomial systems; Taylor polynomial equations, Taylor IVPs, Chebyshev IVPs; the ℓ¹, ℓ² and ℓ^p sequence-space and operator families — nothing equation-specific in a family module); its reusable statements quantify over the family's varying data rather than fix one example.
- **Generalize before a filter or landing decision.** Audit every API-side candidate for ad-hocness: a fixed number where a parameter belongs (dimension, degree, truncation N, weight ν, grid base, tolerance) or a particular algebraic expression form (x² − c, Fisher u − u², a cube-only face, a degree-2-only Z₂). A general `CompPoly` of any degree and any `L` is NOT particular; fixed numbers inside an example instance are fine. Write the general form as an experiment first; the decision waits for it and is the ship gate's (§The one goal and the production gate): generalizing removes fixed numbers and particular forms from a face an endpoint reaches; it is never a shipping reason by itself, and a general form with no endpoint stays a probe.
- **Placement rule.** An inherited or example-level ad hoc helper is either generalized to its family and placed in the family module (`Applications/<family>`, `Certification/<family>`; these are family-level reusable modules, not example-adjacent), or, while still specific to one example, kept in that example's directory under `Examples/`; it is never left in the API core (`Core/`, `Algebra/`, `Analysis/`, `Operators/` general modules) while ad hoc. A helper that generalizes past the family (family-neutral) may enter the core once an endpoint reaches it; anything in the core is general over the family-neutral engine. Every new helper carries a placement statement (target module + why); consumers of an inherited helper are listed by grep in a migration table (generalize in place | move beside consumers | move into the example | delete after migration).
- Evidence: FILTER-20260924/ADHOC_AUDIT.md (the PS bundle was x∗x − c end to end; Core/AffineZ2 served only degree ≤ 2 on one carrier; the Z₀ checkers baked in base 10).

## Effective API — measured definition (2026-10-18, from the ℓ^p campaign; user-prompted; consensus with Codex 30bc9849 and the M9 v2 evidence card; Codex review R1 amendments A1–A3 applied)

- **Consumers supply the mathematical data and hypotheses they own.** They choose the equation, spaces and weights, candidate,
  finite data and verifiable inequalities. The API supplies representation coherence, bounded extensions, coefficient transport
  and operator assembly from those declared choices and hypotheses. Production certificates and book chapters demonstrate the abstraction. Record local instances, `haveI`/`letI`,
  `inferInstanceAs` and named-argument pins (`(p := …)`, `(𝕜 := …)`, `(E := …)`, `(ν := …)`) as source signals; classify each as
  mathematical input, representation/coherence work, or avoidable inference scaffolding, and reduce the latter two at fixed
  endpoints without hiding meaningful choices (measured by the campaign tool `measure.py` v1.1). Use typeclasses for coherent
  structural facts; keep varying bounds, radii and certificates explicit (the skill's explicit-data rule). A `Fact` whose parameter
  is absent from the conclusion is legal; recovering that parameter is the inference problem. Select `Fact`, `outParam` or
  `semiOutParam` only after checking which parameters are determined, how synthesis finds them, and whether competing instances
  preserve the intended semantics (X1b's scratch-prototype `HasRowBound` semiOutParam class is one such check, not a universal cure).
- **Same-endpoint comparisons only.** Before/after claims compare the same fully elaborated theorem, norm convention, equation, data and radius, with reusable-API cost and
  consumer cost in separate columns; a matched problem in another norm is an analogue, labelled as such. Report per final theorem: the obligations the caller discharges
  (interface arity, not "effort"), bound quality (constants, radius, margin, checker time) and the axiom set (a file's union is not the theorem's).
- **Instructive vs decorative abstraction is a reviewed card, not a score.** Six fields: pinned scope; observed reach from endpoint families with witness paths (unreached in
  scope ≠ useless as mathematics, but an unreached face does not ship and keeps a probe record); the exact mathematical service checked against types; caller evidence, including a bounded same-endpoint
  replacement trial when claiming savings or resolving disputed replacement value; explanation evidence as a
  separate claim; cost and one disposition (for a reached face: retain / retain provisionally with a named check / simplify or merge after a
  replacement review / investigate; for an unreached face: to probe, not shipped). One concrete
  application can justify a boundary. Dependency trails are descriptive card inputs (reach with witness paths, short direct dependents, construction sites), never utility verdicts by themselves; reach is necessary for shipping, not sufficient
  (§The one goal and the production gate); module placement follows the module rule below.
- **Prospective guard for a new layer** (class, structure, wrapper, categorical packaging): name the independently specified consumer endpoint it supplies; the actual map,
  identity or hypothesis its boundary hides; what the existing simpler route fails to provide or makes the caller repeat; the bounded experiment that would show or falsify
  the benefit. Without an endpoint and a bounded experiment, keep the work exploratory in scratch or a probe, make no utility or promotion claim,
  and do not ship it in the API.
- **Module placement and consumption.** Consumption is reach from a named production certification pipeline or book chapter,
  directly or transitively, including actual instance use and simp lemmas that fire; imports and file proximity alone do not count.
  Create shipped API modules only where those consumers need them; each shipped declaration passes the ship gate (§The one goal
  and the production gate). A construction calling another unconsumed construction is not
  itself an end-consumer trail. Preserve the weakest valid hypotheses and generic parameters of canonical declarations on a real
  trail. For a reached non-canonical face, demonstrate its canonical replacement at the same endpoint, migrate the consumers and
  retire by capability inventory. Old names, representations and module layout have no backwards-compatibility veto; no compatibility
  aliases. Work with only a prospective consumer remains exploratory outside the shipped API.
- **Two layers for membership and operators.** Separate the admissibility predicate a construction consumes from the sufficient
  ways of proving it, and keep ambient structures (field, frame, normed-space data) and completeness/range hypotheses explicit.
  Algebras: `lpOneAlgConvCompat` (library) / `lpConvCompat` (scratch WeightedLp prototype) is the additional admissibility premise behind one ring instance, not a
  replacement for the algebraic data. Framed ℓ^p operators with 1 ≤ p < ∞ and a complete target: a nonnegative finite-synthesis
  bound on the span of the atoms characterizes the unique bounded extension. At p = ∞ the atoms determine only their closed span;
  the absolute-row realization is a separate interface. Producers may combine finite numerical witnesses (row bounds, rational
  Schur sums, an LDLᵀ witness at p = 2) with proved support, tail, summability and geometry facts; the ℓ¹ column criterion is the
  exact analytic admissibility condition, not a general finite decision procedure (an infinite column family is not a finite
  check). Label each producer exact/sufficient and implemented/reviewed/proposed; a two-circle or PSD route named here is not
  thereby available. Scope operator claims to the scalars, weights, target and geometry actually proved. For p = 2 over ℝ or ℂ and a Hilbert
  target H, the finite-synthesis condition for atom images y_j is equivalent to
  Σ_{j∈s}|⟪y_j,h⟫|²/m_j² ≤ C²‖h‖² for every finite s and h : H (m_j > 0, C ≥ 0).
  This Bessel characterization is mathematical; its named general Lean interface is currently deferred. Producers include Schur
  bounds with test-vector hypotheses, finite weighted Gram/PSD witnesses (the current rational LDLᵀ producer is real), exact
  diagonals, module estimates, compatible block-diagonal head⊕tail max bounds and direct composite bounds. Schur is sufficient,
  never the characterization. Exact norm, upper enclosure and attainment are distinct claims. The convolution-algebra design
  is uniform over 1 ≤ p ≤ ∞ under explicit convolution-compatibility hypotheses, not for arbitrary weights; scratch prototypes
  and a pending API-v2 port are not installed interfaces.
- Retirement of an API follows a capability inventory (what each consumer takes from it), never constant agreement alone, and never
  with compatibility aliases.
- **Three objects, kept distinct.** The coefficient algebra ℓ¹_v of a positive submultiplicative weight (the literature's Beurling weight; name the two conditions, not the person — they are all the algebra uses, and v(0) = 1 is only the unit-norm normalization), the state space ℓ^p_m and its represented convolution
  operators have different roles. For eligible scalar/frame/index structures, positive weights and 1 ≤ p ≤ ∞, moderation
  m(j+l) ≤ C v(l)m(j) gives a bounded ℓ¹_v action with its explicit constant; the algebra's hypotheses and convolution/unit
  relations also enter the representation laws. The linear ℓ¹ lift is characterized by weighted atom bounds; its algebra lift
  additionally verifies the multiplicative and unit relations. The represented image is one operator class, alongside diagonals,
  projections, finite heads and composites; do not assume it is closed in operator norm. Bilateral geometric X₂, with
  m_n = ν^|n| and ν ≥ 1, has no bounded convolution self-product in general; the bounded product X₂×X₂→Y instead takes values
  in the corresponding weighted ℓ∞ coefficient carrier. This gives neither carrier an algebra structure. An admissible ambient
  algebra with multiplication bound κ supports polynomial evaluation; it is one route, not a necessity for every smoothed cubic.
  Keep κ₀ as consumer-side data/hypotheses, separate from the algebra and operator representation.
- **Symbols.** m is the positive amplitude weight (‖x‖² = Σ|x_n|²m_n² at p = 2); ω = m² is the mass weight in this convention
  (use another symbol for a codomain weight; book ch10 uses ϖ). v is the positive submultiplicative weight of ℓ¹_v, w the Lean carrier weight and ν the
  geometric base. Name new weight hypotheses by content; a literature label adds no extra mathematical condition
  (§The one goal and the production gate). κ denotes a multiplication-bound witness, not automatically the optimal
  constant. If Σ1/ω is finite, its
  nonnegative square root may be defined as κ₀; a supplied K₀ ≥ 0 generally witnesses Σ1/ω ≤ K₀², not equality.
  `psi1 N` = ψ₁(N+1) = Σ_{k>N}k⁻².
- **Keep the current design distinct from archived experiments.** Consult the project's live research compass and capability
  inventory for current endpoints and retired routes; historical notes do not revive them. The selected convolution realization
  uses a tagged carrier with coherent global instances under its compatibility hypotheses, distinct from pointwise ℓ∞ operations;
  `ConvLp` is the scratch name, and its pending port is not an installed API. Keep residual codomains at their specified raw or
  bundled boundary; do not infer closure from formal coefficient expressions. Automation handles are opt-in, not default global
  `grind` attributes.

## The one goal and the production gate (user rulings 2026-10-19, from the ℓ^p campaign)

User rulings (2026-10-19), verbatim: "what we should *present* and *ship with API* is the, even though we looked at many possible abstraction, minimal effective abstraction and its consumer as examples." and "what remains from these should be the ones distilled by our philosophy of effective abstraction. Only this together with its consumer goes into the API."

The user's governing statement, which followed them (2026-10-19), verbatim: "This is the ultimate goal, all the explorations and probing all serve this one goal. Don't go astray when doing the span out. No matter what, when we are deciding something that goes into production, we need to ask clearly, is this effective, or decorative. Spanning out is very helpful and even essential as a process, but it is never the target."

- **Ship gate = REACH ∧ MINIMALITY.** A declaration ships only on a justified route to an independently specified example or
  book endpoint, with no avoidable mathematical hypothesis in its public face within the fixed frame. Record actual use
  (direct, transitive, instance or simp) and the map, identity or obligation the abstraction supplies or removes. Reach alone
  does not justify an extra wrapper. Field-use counts are diagnostic, not a proof of necessity or minimality: inspect source
  and full types, and use a weakening trial or separating model where disputed. A missing projection can hide recursor,
  opaque or definitional use. Keep coherent ambient structures required by the frame; do not split every class merely
  because one proof projects fewer fields. "Retained for capability" is not a shipping reason; probes keep the record.
- **Unit briefs open with "EFFECTIVE or DECORATIVE?".** Every brief for a unit that touches production (the API-v2 copy) opens
  with this section, listing each shipped declaration, instance and hypothesis with (a) the endpoints that reach it (trail census)
  and (b) the hypotheses its proof uses (field-use census). Anything without both answers is PROBE.
- **Names by content.** Name new weight hypotheses by their mathematical content: "positive submultiplicative weight";
  a literature label such as "Beurling weight" adds no extra condition and belongs, if useful, in a remark. This does not
  rename established ambient structures or Mathlib interfaces, or remove proper source attribution.
- **Hypothesis minimality in every review.** Every review and checker carries a HYPOTHESIS-MINIMALITY item: does the proof use each
  hypothesis and class field the declaration carries? Fidelity to the source does not answer it. The mechanical tool is the
  field-use census (campaign tool `API_V2/FIELD_USE_CENSUS/`): per class, which fields each taker's proof reaches. Evidence
  (2026-10-19): the library class `lpOneAlgWeightMul` bundled v(0) = 1 with submultiplicativity although only its `NormOneClass`
  instance used v(0) = 1; four review passes missed it: all checked fidelity to the source, none asked whether the source asks
  for more than the proof uses.
