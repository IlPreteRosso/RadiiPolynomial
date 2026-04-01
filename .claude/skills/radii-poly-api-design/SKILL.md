---
name: radii-poly-api-design
description: Design philosophy for the RadiiPolynomial Lean formalization project. Guides API design through the cycle of reference-book → examples → friction → generalization → abstraction. Use when starting a new formalization task, refactoring existing proofs, or extending the library to new mathematical domains.
---

# RadiiPolynomial API Design

Design and extend the RadiiPolynomial Lean library by following the friction-driven generalization cycle. The goal: a single `general_radii_polynomial_theorem` that handles arbitrary Banach-space zero-finding, with domain-specific infrastructure (IVP, BVP, Chebyshev) as thin layers on top.

## Philosophy

### 1. Start from the reference book

The reference book (`exterior/reference book/computationalODE_split/`) is the source of truth. Before implementing anything:
- Read the relevant chapter (use `pdftotext` or the Read tool on PDFs)
- Identify the theorem statement, the Banach space, the operator, and the bounds (Y0, Z0, Z1, Z2)
- Understand what's equation-specific vs structurally generic

### 2. Check what's available before writing anything

Before creating new files or definitions:
- Search the existing codebase (`Grep`, `Glob`) for related lemmas
- Check Mathlib for relevant theory (normed rings, lp spaces, convolution, MVT)
- If a result exists, USE IT — even if the interface isn't perfect, adapt rather than rebuild

### 3. Build examples first, then extract the API

The design cycle:
```
Example (with friction) → Generic lemma → Abstract API → Apply to more examples
```

- **Start with a concrete example** (e.g., scalar IVP x'=x(x-1))
- **Notice friction**: where does the proof require manual unfolding, fin_cases + nlinarith, or 80-line chain rule boilerplate?
- **Extract the pattern**: if the same proof structure repeats, it should be a library lemma
- **Generalize**: parameterize over the equation-specific data (phi_spec, numerical arrays, etc.)
- **Validate**: apply the API to a second example (e.g., Lorenz system) — if it eliminates boilerplate, the API is right

### 4. Friction IS the signal

When a proof is ugly, DON'T push through with `show`/`change`/`conv`. Instead:
- Ask: "Is there a lemma that would make this one line?"
- Ask: "Does this pattern repeat across examples?"
- Ask: "Can the hypothesis be weakened or the conclusion strengthened?"

Examples of friction → API improvements from this project:
- `fin_cases l` + `nlinarith` for Dphi norms → `ivp_Dphi_norm_le`, `norm_fderiv_diff_evalInBanach_of_const_second_pderiv`
- 80-line manual chain rule proof → `ivp_hDF_block_nat` (single `native_decide`)
- Per-example `approxInverse`/`abar`/`G` boilerplate → `StdIVPData` bundle
- `simp` can't reduce `pderiv` after `fin_cases` → `pderiv_simp` tactic

### 5. Prefer `native_decide` and `simp` over manual proofs

Numerical verification should be automated:
- Rational arithmetic (Q matrix entries, coefficient bounds) → `native_decide`
- Polynomial pderiv computation → `pderiv_simp`
- Finite matrix norm bounds → `finmatrix_bound`
- Weighted sum bounds → `finsum_bound`

If a verification step can't be automated, that's a sign the API needs a computable bridge lemma (e.g., `pderiv_ofNat`, `norm_evalInBanach_C`).

### 6. Separate concerns: data, algebra, certificate

Each example has three layers:
- **Numbers.lean**: Pure Q data (auto-generated from Julia). No proofs, no imports beyond `Mathlib.Data.Rat.Defs`
- **Algebra.lean**: Equation-specific structure (phi, Dphi, fderiv proofs, Q bridges). Imports library + Numbers
- **Certificate.lean**: Numerical verification (Y0, Z0, Z1, Z2 bounds, radii polynomial). Imports Algebra

The library (`source/`) should never import from examples.

### 7. The abstract theorem is the anchor

`general_radii_polynomial_theorem` (Thm 7.6.2) is basis-independent and equation-independent. Everything else — IVP setup, Chebyshev algebra, block-diagonal operators — is infrastructure to APPLY this theorem to specific problems. When designing new infrastructure, always check: does this layer reduce to providing the four bounds (Y0, Z0, Z1, Z2) to the abstract theorem?

## Process for a new formalization task

1. **Read the book chapter** — identify theorem, Banach space, operator structure
2. **Search existing code** — what infrastructure already exists? What Mathlib lemmas apply?
3. **Write the example** — Numbers + Algebra + Certificate, accepting friction
4. **Identify friction** — what's boilerplate? What's manual that should be automatic?
5. **Extract API** — generic lemmas, bundles, tactics
6. **Apply to second example** — validates the API eliminates the friction
7. **Clean up** — remove dead code, check for duplication

## Key design patterns

- **`StdIVPData` bundle**: numerical arrays in, auto-derived constructions out
- **`pderiv_simp [phi_spec]`**: `dsimp` (match reduction) + `simp` (pderiv rules) + `ring`/`norm_cast`
- **`D2` Hessian table**: system-level second-pderiv coefficients, verified by `pderiv_simp`
- **`ivp_hDF_block_nat`**: Fin-bounded `native_decide` for Jacobian verification
- **`norm_fderiv_diff_evalInBanach_of_const_second_pderiv`**: Z2 from polynomial structure
