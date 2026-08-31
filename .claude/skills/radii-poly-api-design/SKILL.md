---
name: radii-poly-api-design
description: Design and refactor the RadiiPolynomial Lean API while preserving its mathematical layering, reusable-module boundaries, and compiling examples. Use for new formalizations, API extraction, proof cleanup, module moves, typeclass design, polynomial evaluation bridges, IVP or Chebyshev infrastructure, and certificate integration.
---

# RadiiPolynomial API Design

Treat the tracked repository copy of this skill as canonical. Keep any Codex mirror
byte-identical to it.

## Establish Live Context

- Work in the nested Git repository at `RadiiPolynomial/RadiiPolynomial`.
- Read `ARCHITECTURE.md` before changing module boundaries or imports.
- Inspect the current Git state and preserve unrelated work. Do not commit or push unless asked.
- Search the live project with `rg` before introducing declarations or files.
- Check the pinned Mathlib dependency for an existing result before rebuilding it locally.
- Consult `docs/reference_book/` for the mathematical theorem, Banach space, operator,
  and bounds when extending the formalization.
- Treat old handoffs and memory as design history; verify paths and declarations against the
  current checkout.

## Design From Mathematical Layers

Keep the dependency direction documented in `ARCHITECTURE.md`:

```text
Algebra + Analysis
        |
        v
Core + reusable Operators
        |
        v
Applications
        |
        v
Examples + Certificates
```

`Certification` and `Tactic` are adapter layers. Reusable mathematical modules never import
`Examples`; applications never import their concrete examples.

At public application boundaries, prefer the facade modules listed in `ARCHITECTURE.md`.
Inside the library, import the narrow module that owns the declaration.

## Use Friction Carefully

Use this cycle:

```text
Concrete example -> repeated friction -> generic lemma -> abstract API -> second consumer
```

- Classify every obligation as equation-specific, representation-specific, or structural.
- Keep finite numeric cleanup and one-off case analysis in the example or certificate.
- Promote a lemma only when it expresses reusable mathematics or removes repeated structural
  plumbing.
- Do not add ad hoc example-specific lemmas to a reusable API merely to shorten one proof.
- Prefer the weakest coherent assumptions. Parameterize a generic proof by the witness that
  varies between constructions instead of duplicating the proof or strengthening typeclasses.
- Preserve public declaration names and compatibility aliases when the mathematics has not
  changed; module imports may evolve with the architecture.

Proof ugliness is evidence, not proof, of a missing abstraction. First search Mathlib and the
project, then determine whether the friction recurs across consumers.

## Preserve Core Boundaries

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
- Keep `SystemBlockDiagData.composedApprox` as shared Taylor/Chebyshev operator
  infrastructure; retain `IVP.ivpComposedApprox` only as a compatibility name.
- Keep the external LeanCert package as a dependency. Put only project-specific bridges in
  `Certification/LeanCertAdapter.lean`; never copy LeanCert into this repository.

## Typeclasses And Mathlib Alignment

- Separate assumptions by mathematical strength, as with `SubMulWeightBase` and
  `SubMulWeight`.
- Use `lpOneAlgConvCompat` to hide alternative convolution-summability constructions behind
  one ring instance. The current paths are weight multiplication and finite antidiagonals.
- Extract shared proofs by passing summability or finiteness witnesses explicitly.
- Define multiplicative declarations first and generate additive analogues with
  `@[to_additive]` when the translation is mathematically faithful.
- Protect nontranslated fiber and scalar parameters with `dont_translate` as needed.
- Do not force ring instances through `to_additive` when multiplication names conflict; state
  those instances explicitly.
- Follow the pinned Mathlib discrete-convolution API for names, assumptions, and docstrings.

## Polynomial And Certificate Automation

Prefer computation over handwritten finite proofs:

- Use `native_decide` for rational and finite decidable identities.
- Use `pderiv_simp` for `MvPolynomial.pderiv` normalization.
- Use `finmatrix_bound` for finite weighted matrix bounds.
- Use `compPolyOf%` to reify supported polynomial lambdas.
- Use `auto_poly_fderiv` for supported polynomial Frechet derivatives.

If automation cannot cross a representation boundary, add a reusable correctness bridge at
the owning layer. Do not expose internal representations merely to make a certificate reduce.

## Current API Landmarks

- Abstract theorem and bounds: `RadiiPolynomial/Core/`.
- Polynomial semantics and syntax: `RadiiPolynomial/Algebra/Polynomial/MvPolynomial/` and
  `RadiiPolynomial/Algebra/Polynomial/CompPoly/`.
- Weighted sequence algebras: `RadiiPolynomial/Analysis/SequenceSpace/`.
- Matrix and finite-plus-tail operators: `RadiiPolynomial/Operators/`.
- Taylor IVP infrastructure: `RadiiPolynomial/Applications/IVP/Taylor/`.
- Chebyshev IVP infrastructure: `RadiiPolynomial/Applications/IVP/Chebyshev/`.
- Certificate adapters: `RadiiPolynomial/Certification/`.
- Automation: `RadiiPolynomial/Tactic/`.
- Concrete applications: `RadiiPolynomial/Examples/`.

Important live patterns include `StdIVPData`, `StdChebIVPData`, `BlockDiagLift`,
`ivp_hDF_block_nat`, `CompPoly.toSeq_evalBanach`, and
`StdIVPData.composedApprox_eq_fderiv_G_fin_of_compPoly`.

## Example Layers

Use the layers that apply to the problem:

- `Numbers.lean`: imported numerical data, without mathematical proof plumbing.
- `Algebra.lean`: equation-specific maps, symbolic derivatives, and representation bridges.
- `Certificate.lean`: verified bounds and the radii-polynomial application.
- `Analytic.lean`: function-space interpretation and analytic existence or uniqueness.

Not every example needs every layer. Use `f` and `F` consistently for the vector field and
operator; avoid introducing alternate names without a mathematical distinction.

## Verification

After changing reusable modules or imports:

1. Run focused checks while iterating.
2. Run `lake build` from the nested repository.
3. Confirm every production example imported by `RadiiPolynomial.Examples` compiles.
4. Until Example 14.2.1 has exported numerical data and a certificate, also run
   `lake build RadiiPolynomial.Examples.IVP.Chebyshev.Example1421.Algebra`.
5. Reject new `sorry` or `admit`, forbidden upward imports, and project-local warnings.

The final acceptance criterion is mathematical layering plus compilation of all current
examples after any import-path updates.
