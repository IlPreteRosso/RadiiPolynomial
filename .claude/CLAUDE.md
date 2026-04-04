# RadiiPolynomial — Project Instructions

This is a Lean 4 formalization of radii polynomial methods for rigorous ODE solution verification, based on the reference book at `docs/reference_book/`.

## Project structure

```
RadiiPolynomial/
  RadiiPolynomial.lean           -- root import (all source + examples, builds all oleans)
  RadiiPolynomial/
    source/
      lpSpace/                   -- lpOneAlg (ℓ¹ Banach algebra), WeightedScalar, l1Weighted
        CauchyProduct.lean       -- antidiagonal-sum Cauchy product formula
        Eval.lean                -- l1Weighted.toPowerSeries, eval, eval_mul (Mertens)
      BlockDiag/                 -- block-diagonal operators (toMatrix, system Neumann, injectivity)
      IVP/                       -- equation-independent IVP infrastructure
        Setup.lean               -- ivpCoeffs, ivpMap, ivpTail, differentiable_ivpMap, ivp_Z1/Y0/Z2_le
        Theorem.lean             -- Thm 8.2.2: ivp_system_theorem
        DFBlock.lean             -- ivp_hDF_block_nat: generic DF verification
        StandardIVP.lean         -- StdIVPData bundle
      Chebyshev/                 -- Chebyshev polynomial algebra + ChebyshevIVP
      MvPolyBridge/              -- multivariate polynomial bridge + system Z2 norm bounds
        POC.lean                 -- proof-of-concept tests (evalInBanach, pderiv↔fderiv)
      Tactic/                    -- auto_poly_fderiv, pderiv_simp, FinMatrixBound
      Core.lean                  -- canonical bounds (Y0_norm, Z0_norm, Z1_norm, Z2_norm)
      RadiiPolyGeneral.lean      -- general_radii_polynomial_theorem (Thm 7.6.2)
      LeanCertEval.lean          -- ℚ evaluators + ℝ→ℚ norm bridges for certificates
      WitnessSpec.lean, Z2Affine.lean
    examples/
      Example81/                 -- Scalar IVP x'=x(x-1), Taylor basis (L=1, N=10)
      Example83/                 -- Lorenz IVP, Taylor basis (L=3, N=30)
      Example77/                 -- parameterized zero-finding (section 7.7, scalar l1_nu)
      Example245/                -- algebraic fixed point (section 2.4.5, scalar R)
      Example1421/               -- Chebyshev IVP x'=x(x-1) (scaffolding, needs Julia data)
      TestQuadratic/             -- f-F bridge test: x² - λ = 0 (pipeline skeleton)
      TestCubic/                 -- f-F bridge test: x³ - λ = 0
      TestCrossProduct/          -- f-F bridge test: xy - λ = 0, x + y - 2 = 0
```

**Theorem hierarchy:**
- `general_radii_polynomial_theorem` (Thm 7.6.2) — abstract, any Banach space zero-finding
- `ivp_system_theorem` (Thm 8.2.2) — system IVP specialization (Taylor), calls 7.6.2
- `chebyshev_system_theorem` — system IVP specialization (Chebyshev), calls 7.6.2
- Example77 uses 7.6.2 directly (parameterized zero-finding, NOT an IVP)
- Example81/83 use `StdIVPData.existsUnique` which calls 8.2.2 internally

**f-F bridge (Test examples):**
The pipeline from original equation to coefficient recurrence:
1. Substitute Taylor expansion into ODE/equation
2. Match coefficients of like powers (formal PowerSeries equality)
3. Define F(a) = 0 on ℓ¹_ν (Banach algebra operations)
4. Semantic bridge: F(a)=0 ⟹ eval(a,z) satisfies the original equation
Test files (TestQuadratic/TestCubic/TestCrossProduct) exercise this pipeline with sorried proofs.

**Algebra architecture:**
- `lpOneAlg M E` (`LpOneAlg.lean`) — generic ℓ¹ Banach algebra with non-uniform fibers
- `WeightedScalar w m` — parameterized fiber ℝ with norm `|x|·w(m)`
- `l1Weighted ν := lpOneAlg ℕ (ScaledReal ν)` — Taylor power series
- `l1Chebyshev ν := lpOneAlg ℤ (ScaledRealZ ν)` — Chebyshev bilateral series

**The library (`source/`) should never import from examples.**

## Build

- `lake build` for clean builds or when dependencies changed
- `lake env lean <file>` for fast single-file checks when only that file changed and its dependencies are already built

`lake env lean` uses cached oleans, so if a dependency was modified it may use stale oleans and produce false errors. After editing an imported file, use `lake build`.

## Lean proof patterns and gotchas

### fderiv rewriting friction

Mathlib's `fderiv_const`, `fderiv_add`, `fderiv_fun_mul` etc. use patterns like `Function.const`, `f + g` that Lean4 can't unify with lambda expressions `fun x => ...`. Workaround: use `HasFDerivAt.fderiv` via explicit `have` statements:

```lean
have hfd : fderiv R (fun x => f x + g x) a = fderiv R f a + fderiv R g a :=
  (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv
rw [hfd]
```

Also: `ext` on `l1Weighted` CLMs goes too deep into `ScaledReal` — always use `ext1 h` instead.

### totalDegree is noncomputable

Don't try to prove `totalDegree (phi_spec l) <= 2` by structural decomposition — it's extremely verbose. Instead verify the CONSEQUENCE directly:
- `simp` with `pderiv_X`, `pderiv_mul`, `pderiv_C_mul` reduces iterated pderivs to constants
- `auto_poly_fderiv` handles the Banach-space fderiv layer

### tsum subtype performance

Lean's elaborator blows up (800k+ heartbeats) checking definitional equality through `Equiv` / `comp_injective` on Z-indexed `lpOneAlg` types.

- Use `tsum_of_norm_bounded hg.hasSum (fun ab => ...)` instead of `norm_tsum_le_tsum_norm`
- Use `refine (...).trans ?_` instead of `calc` blocks
- Prove `summable_norm_shift` at the generic lpOneAlg level where `||f m||` is opaque
- Provide `Summable` witnesses as separate `have` statements — avoid chaining `.add`, `.const_smul` in one expression

### Equiv.tsum_eq needs type annotation

`Equiv.tsum_eq` returns a tsum with `Equiv.addRight` internally, not `k + 1`. Always provide an explicit type annotation:

```lean
-- GOOD: type annotation forces definitional check, rw works later
have ht1 : sum' k : Z, ||c (k + 1)|| = sum' k : Z, ||c k|| :=
  (Equiv.addRight (1 : Z)).tsum_eq (fun k => ||c k||)
```

### API over unfolding

When there's friction in proofs (rw can't match, type mismatch between abbrevs), resolve by creating a better API lemma rather than inlining `show`, `change`, `conv`. A clean API lemma is reusable and makes downstream proofs simpler.

For `Fin 1`, use `Subsingleton.elim l 0; subst` instead of `fin_cases l` to avoid `(fun i => i) {0, ...}` pattern mismatch.

## Design decisions

### IVP codomain: raw N -> R, not typed omega space

`ivpCoeffs` and `chebyshevIvpCoeffs` return raw `N -> R`, not elements of the omega-weighted space. The omega space is never formalized as a type for F's output because:
1. F(a) is immediately fed to A then discarded — no one manipulates F(a) as an l1_omega element
2. Proving `F(a) in l1_omega` for every `a` would be significant extra work with zero downstream benefit
3. All bounds (Y0, Z0, Z1, Z2) work at the raw coefficient level
4. Matches the reference book: computations never use `||F(a)||_omega`

### Matrix norm verification via `finmatrix_bound`

Certificate matrix norm bounds use `finmatrix_bound` (single `native_decide`) rather than per-column `finsum_bound`. The bridge lemmas compute the full norm in exact ℚ arithmetic:

```lean
-- Scalar matrix norm: finWeightedMatrixNorm ν M ≤ C
finmatrix_bound
  (finWeightedMatrixNorm_le_of_Q_le _ cols ν_q hcols hν)

-- Block matrix norm: finiteBlockMatrixNorm ν A ≤ C
finmatrix_bound
  (finiteBlockMatrixNorm_le_of_Q_le _ blockCols ν_q hcols hν)

-- Scalar CLM norm: ‖A.toScalarCLM‖ ≤ C
finmatrix_bound
  (norm_toScalarCLM_le_of_Q A cols ν_q |tailCoeff| hcols hν htail)

-- System CLM norm: ‖A.toCLM‖ ≤ C
finmatrix_bound
  (norm_toCLM_le_of_Q A blockCols ν_q tailBound_q hcols hν htail)
```

The certificate provides: ℚ column arrays, `hcols` (ℝ entries = ℚ cast), `hν` (ℝ weight = ℚ cast).
When the goal bound involves ℝ division (e.g., `≤ (C : ℝ) / 2`), rewrite first:
`rw [show (C : ℝ) / 2 = ((C / 2 : ℚ) : ℝ) from by push_cast; ring]`

### Generic DF verification API

The `ivp_hDF_block_nat` + `MvPolyBridge` API eliminates equation-specific Jacobian definitions. The user provides `phi_spec : Fin L -> MvPolynomial (Fin L) Q` and the API:
- Computes Jacobian entries via `mvPolyCoeffQ(pderiv m (phi_spec j))`
- Verifies numerical Jacobian against symbolic one via `native_decide`

New IVP examples should use `ivp_hDF_block_nat`, not manual Jacobian definitions.

## Reference book

The reference book is at `docs/reference_book/`, split into PDFs by page range:
- 1-48.pdf (includes table of contents)
- 49-72.pdf, 73-120.pdf, 121-138.pdf, 139-182.pdf
- 183-220.pdf, 221-254.pdf, 255-290.pdf, 291-312.pdf, 313-382.pdf

Use `pdftotext` for more efficient text output. Check the TOC in 1-48.pdf first to find the right page range.

## Relationship to GitHub

This is a restructured version of https://github.com/IlPreteRosso/LEANearized-RadiiPolynomial. Only the `RadiiPolynomial/` directory is scoped for GitHub — everything outside it (e.g. `exterior/`) is local-only.
