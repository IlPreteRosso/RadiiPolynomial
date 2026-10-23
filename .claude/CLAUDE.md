@../../AGENTS.md

# RadiiPolynomial — Project Instructions

This is a Lean 4 formalization of radii polynomial methods for rigorous ODE solution verification, based on the reference book at `docs/reference_book/`.

## Project structure

```
RadiiPolynomial/
  ARCHITECTURE.md                -- module roles, public facades, and import rules (the inventory of record)
  RadiiPolynomial.lean           -- root import (library + production examples)
  RadiiPolynomial/
    Algebra/                     -- convolution and polynomial representations
    Analysis/                    -- weighted sequence spaces, evaluation, and calculus
    Core/                        -- abstract theorem and canonical bounds
    Operators/                   -- finite matrices and finite-plus-tail block operators
    Certification/               -- witness reductions, the LeanCert adapter, and the IVP/, PowerSeries/,
                                    Rational/ certificate faces (residual correction, formerly Residual/, is staged in
                                    exterior/api_v2/probes/records/B5_universal_api_retirement/staged/B5RecordResidualP{1,2}.lean)
    Tactic/                      -- no shipped module (finmatrix_bound deleted 2026-10-23, RENAMES; pderiv_simp: B4/U34, RENAMES B4; auto_poly_fderiv and compPolyOf%: B5; all retired)
    Applications/IVP/            -- shared vector field (VectorField.lean); the split boundary `IVP.SplitBoundary` (formerly Boundary.lean) is staged (staged record: `exterior/api_v2/probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean`);
      Taylor/                    --   Taylor IVP operator, theorem, Jacobian, and analytic bridge
      Chebyshev/                 --   Chebyshev IVP operator and block-diagonal realization
    Applications/PowerSeries/    -- polynomial zeros on l1_nu (operators, bounds, affine Z2 transition)
    Applications/FiniteDimensional/ -- the row-sum face on R^n and rational polynomial systems
    Applications/Galerkin/       -- the polynomial Galerkin face on the finite Chebyshev carrier
    Applications/Fourier/        -- general-symbol semilinear ℓ¹ layer: no end consumer; archived at the API-v2 merge (user 2026-10-18); the Fourier consumer of record is book §10.1 Duffing on ℓ²
  (2026-10-23: `Applications/Fourier/Realization.lean` is LIVE again — the Fourier realization bridge: circle algebra lift, ℓ²→Y→ℓ¹ chain, moment-form derivatives, strip analyticity, parameter-generic Duffing glue; end consumer `Examples/Fourier/Duffing/Analytic.lean`.)
    Examples/                    -- grouped by problem family and discretization
```

**Theorem hierarchy:**
- `general_radii_polynomial_theorem` (Thm 7.6.2) — abstract, any Banach space zero-finding
- `ivp_system_theorem` (Thm 8.2.2, book-faithful global IVP theorem) and its ball-local form `ivp_system_theorem_local` — retired at the API-v2 merge (B5 DELETE, no staged record; neither was used by the examples)
- `chebyshev_system_theorem` — system IVP specialization (Chebyshev), calls 7.6.2
- Example77 uses 7.6.2 directly (parameterized zero-finding, NOT an IVP)
- Example81/83 use `StdIVPData.existsUnique` which calls 7.6.2 directly (not 8.2.2)

**f-F bridge (formalized end-to-end, sorry-free):**
The semantic bridge from the sequence-space zero F(a) = 0 back to the original equation:
- `Applications/IVP/Taylor/Trajectory.lean` — forward bridge (book Lemma 8.1.4):
  `solves_ODE_of_F_zero` (F(a)=0 ⟹ t ↦ eval(a,t) solves the ODE), plus the
  Picard–Lindelöf uniqueness lift `analytic_solution_unique` (the RP trajectory bound
  supplies the Lipschitz radius)
- `Applications/IVP/Taylor/Analytic.lean` — packages both for any `StdIVPData`:
  `IsBallSolution`, canonical solution `x_analytic`, and `analytic_existsUnique`
  on (-ν, ν)
- Example81/83 `Analytic.lean` instantiate `analytic_existsUnique`; Example77 `Analytic.lean` proves the pinning theorem `x_analytic_sq_eq` (eval(x̃,t)² = λ₀ + t via `eval_mul`/Mertens)

**Algebra architecture:**
- `lpOneAlg M E` (`Analysis/SequenceSpace/WeightedL1/Carrier.lean`; the convolution ring in `Algebra.lean`) — generic ℓ¹
  Banach algebra with non-uniform fibers
- `WeightedScalar 𝕜 w m` — the fiber `𝕜` (any `NormedField`) with positive weight `w` (`[PosWeight w]`), norm `‖x‖ * w(m)` and the standard `FiberTrivialization` frame; `ScaledReal ν` / `ScaledRealZ ν` are its real specializations, `geomFiber 𝕜 ν` / `geomFiberZ 𝕜 ν` the scalar-general geometric fibers
- `l1Weighted ν := lpOneAlg ℕ (ScaledReal ν)` — Taylor power series
- `l1Chebyshev ν := lpOneAlg ℤ (ScaledRealZ ν)` — Chebyshev bilateral series

**Reusable modules should never import from `Examples`. Follow `ARCHITECTURE.md`.**

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

### Polynomial constants come from the syntax

For example certificate constants, use the `CompPoly` bounds rather than proving an ad hoc degree bound by structural decomposition. Norm, Lipschitz and derivative constants are read off the `CompPoly` syntax (`normBound`, `lipschitzBound`, `derivativeBound`; UBIQUITOUS_LANGUAGE "Bounds from syntax"). Where a consequence must still be checked directly:
- `simp` with `pderiv_X`, `pderiv_mul`, `pderiv_C_mul` reduces iterated pderivs to constants
- the Banach-space fderiv macro `auto_poly_fderiv` is retired at the API-v2 merge (RENAMES B5: polynomial derivative macros)

### tsum subtype performance

Lean's elaborator blows up (800k+ heartbeats) checking definitional equality through `Equiv` / `comp_injective` on Z-indexed `lpOneAlg` types.

- Use `tsum_of_norm_bounded hg.hasSum (fun ab => ...)` instead of `norm_tsum_le_tsum_norm`
- Use `refine (...).trans ?_` instead of `calc` blocks
- Prove shift-summability facts at the generic lpOneAlg level where `||f m||` is opaque (the former `lpOneAlg.summable_norm_shift` is retired, B5 DELETE)
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

Do not put ad hoc example-specific facts into the library API. If the fact only exists because one certificate has a particular finite case or numeral, keep the cleanup local/private at the proof site. For example, a global `C_two_eq` lemma is too narrow; normalize a concrete `C 2` locally at the proof site. (The general bridge `MvPolynomial.C_ofNat_eq` formerly cited here is retired at the API-v2 merge: A29 R-ELAB, executed DELETE with `Algebra/Polynomial/MvPolynomial/Core.lean`, superseding K14; RENAMES records no replacement.)

For `Fin 1`, use `Subsingleton.elim l 0; subst` instead of `fin_cases l` to avoid `(fun i => i) {0, ...}` pattern mismatch.

### Finset.Icc on ℤ is noncomputable

`Finset.Icc (a b : ℤ)` picks up `Int.instConditionallyCompleteLinearOrder` and is
noncomputable — any ℚ mirror folded over it breaks `native_decide` / `finsum_bound`
compilation. Index computable bilateral folds by `Finset.range` plus an explicit
shift (`i = j − N`), and bridge to the analytic side with
`Finset.image (fun j => (j : ℤ) − N) (Finset.range (2*N + 1))` + `Finset.sum_image`.

## Design decisions

API design philosophy of record (effective API, two-layer operator membership, module rule and ship test, what not to revive): the `radii-poly-api-design` skill, section "Effective API — measured definition" and the bullets after it; dated priorities live in the project memory index.

### IVP codomain: raw N -> R, not typed ϖ space

`ivpCoeffs` and `chebyshevIvpCoeffs` return raw `N -> R`, not elements of the ϖ-weighted space (ϖ is the IVP codomain weight; Lean names and the code-formatted expressions below spell it `omega`). The ϖ space is never formalized as a type for F's output because:
1. F(a) is immediately fed to A then discarded — no one manipulates F(a) as an ℓ¹_ϖ element
2. Proving `F(a) in l1_omega` for every `a` would be significant extra work with zero downstream benefit
3. All bounds (Y0, Z0, Z1, Z2) work at the raw coefficient level
4. Matches the reference book: computations never use `||F(a)||_omega`

### Certificate checks

Every bound of a certificate is decided by ONE call: the family checker (`data.Checks`, `dataQ.ChecksZ₀By`, `dataQ.ChecksZ₂`, … by `decide +kernel`) or a LeanCert tactic (`finsum_bound`, `native_decide`), whichever makes the EXAMPLE CALL simpler (user rule 2026-10-23). The exact-ℚ bridges in `Certification/Rational/Matrix.lean` (`finWeightedMatrixNorm_le_of_Q_le`, `finiteBlockMatrixNorm_le_of_Q_le`, `norm_toScalarCLM_le_of_Q`) are soundness lemmas consumed directly by the certification faces (`Certification/PowerSeries/PolynomialZero.lean`). The tactic-wrapper-over-a-bridge pattern (`finmatrix_bound`) is RETIRED as technical debt (user 2026-10-23).

### Example-facing IVP interface

An IVP example supplies only what it owns: the polynomial system `f_cpoly : Fin L → CompPoly L`, the initial condition, the numbers (candidate, finite blocks, rational bounds) and the radii inequality. It uses the `_of_compPoly` faces directly or through the family certificate checkers (`StdIVPData.existsUnique_of_compPoly`, `StdIVPData.composedApprox_eq_fderiv_G_fin_of_compPoly`, `StdChebIVPData.existsUnique_of_compPoly`; UBIQUITOUS_LANGUAGE "End-consumer interface"); the library derives differentiability, the Fréchet derivative and the symbolic Jacobian. `ivp_hDF_block_nat` is an internal step (`Applications/IVP/Taylor/Standard.lean`), not an example-facing API.
The finite Jacobian remains a checked certificate obligation. Example 8.3 supplies `hDF_nat` by `native_decide` and uses `composedApprox_eq_fderiv_G_fin_of_compPoly`. Example 8.1 packages `ChecksDF` with `ChecksZ₁ker` in `z1_checks`, proved by `decide +kernel`, and consumes `Z₁ker_sound`. The numerical bounds and radii inequality remain certificate obligations.

## Reference book

Primary: the errata-corrected rewrite edition at `../exterior/book/` (`chapters/ch02–ch19.tex`, `alignment/` hubs), which follows the Lean formalization; search it with `grep -n`.
The original edition, for original page numbers or for citing the published text, is at `docs/reference_book/`, split into PDFs by page range (1-48 with the table of contents, 49-72, 73-120, 121-138, 139-182, 183-220, 221-254, 255-290, 291-312, 313-382). Use `pdftotext`; check the TOC in 1-48.pdf first to find the right range.

**Key sections for formalization:**
- Section 7.4 (p.158): Banach algebra — `lpOneAlg`, Cauchy product
- Section 7.6 (p.165): Radii polynomial theorem (Thm 7.6.2) — abstract zero-finding
- Section 7.7 (p.168): Parameterized zero-finding — Example77 (x² - λ = 0), f-F bridge
- Section 8.1 (p.185): Scalar IVP — Example81 (x' = x(x-1)), Taylor coefficient setup
- Section 8.2 (p.194): System IVP — ivpCoeffs formula (Eq. 8.15), fixed point formulation (p.202)
- Section 8.3 (p.211): Lorenz system — Example83
- Section 8.4 (p.211): Taylor transform — how ODE → coefficient recurrence (f → F bridge)

## Relationship to GitHub

This is a restructured version of https://github.com/IlPreteRosso/LEANearized-RadiiPolynomial. Only the `RadiiPolynomial/` directory is scoped for GitHub — everything outside it (e.g. `exterior/`) is local-only.
