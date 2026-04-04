import RadiiPolynomial.source.IVP.StandardIVP
import RadiiPolynomial.source.IVP.DFBlock
import RadiiPolynomial.source.MvPolyBridge.Basic

/-!
# Hard Test: Simple Scalar IVP — x' = x², x(0) = 1/2

## Input (the original ODE)

Scalar IVP: x'(t) = x(t)², x(0) = 1/2.
Exact solution: x(t) = 1/(2 - t), blows up at t = 2.

## What the autoformalizer should produce

This test focuses on the **f → φ → StdIVPData** pipeline only.
Certificate bounds are out of scope (already tested by Example81/83).

### Step 1: Define φ (nonlinearity at coefficient level)

- Recognize x² as self-Cauchy-product: `φ(a)₀ = a₀ * a₀` on `l1Weighted ν`
- Scalar IVP: L = 1, so `φ : XL1 ν 1 → Fin 1 → l1Weighted ν`
- Define `φ_spec : Fin 1 → MvPolynomial (Fin 1) ℚ` for automated Jacobian verification
  (should be `fun _ => X 0 * X 0`)
- Prove differentiability: `differentiable_φ_component`
- Prove Dφ bound: `Dφ_norm_le` (for Z₁)
- Prove D²φ bound: `Dφ_diff_norm_le` (for Z₂)

### Step 2: Build StdIVPData (Algebra.lean pattern)

- Choose N (truncation order) and ν (weight)
- Provide numerical arrays from solver: A_col, DF_col, abar_Q
- Bundle into `StdIVPData` — auto-derives approxInverse, approxDeriv, tailCancel, etc.

### Step 3: Semantic bridge (optional, currently unformalized)

The f-F gap: ivpCoeffs gives F(a) = 0, but connecting back to the original ODE
x' = x² requires showing eval(a, t) satisfies the ODE. This is NOT done in
Example81/83 — they work purely with F. See `tests/easy/` for scaffolding.

## Where to find patterns

### IVP pipeline (formalized references)
- **Example81** (`L=1, N=10`): Closest — scalar IVP x' = x(x-1)
  - `Algebra.lean`: φ_scalar, φ_spec, differentiability, Dφ/D²φ bounds
  - `Certificate.lean`: StdIVPData, numerical arrays, all 4 bounds, existsUnique
- **Example83** (`L=3, N=30`): System IVP (Lorenz) — multi-component pattern

### Key infrastructure for the f → φ step
- `ivpCoeffs`: `source/IVP/Setup.lean` — generic F formula (equation-independent)
  F(a)_0 = a_0 - x₀, F(a)_{k+1} = (k+1)·a_{k+1} - φ(a)_k
- `StdIVPData`: `source/IVP/StandardIVP.lean` — bundles numerical data
- `ivp_hDF_block_nat`: `source/IVP/DFBlock.lean` — automated Jacobian verification
- `φ_spec` polynomial: `source/MvPolyBridge/Basic.lean` — MvPolynomial bridge
- `auto_poly_fderiv`: `source/Tactic/AutoPolyFDeriv.lean` — automatic differentiation
- `pderiv_simp`: `source/Tactic/PDerivSimp.lean` — polynomial derivative normalization

### What differs from Example81
- φ: `a₀ * a₀` (self-product) vs `a₀ * a₀ - a₀` (product minus identity)
- φ_spec: `X 0 * X 0` vs `X 0 * X 0 - X 0`
- D²φ: constant bilinear form vs affine — simpler Lipschitz bound
- x₀ = 1/2 vs x₀ = 1/2 (same initial condition, coincidentally)
-/

-- The autoformalizer should fill in everything below this line.
-- Only the ODE x' = x², x(0) = 1/2 is given.
