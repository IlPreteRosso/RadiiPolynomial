import RadiiPolynomial.source.IVP.StandardIVP
import RadiiPolynomial.source.IVP.DFBlock
import RadiiPolynomial.source.MvPolyBridge.Basic

/-!
# Hard Test: 2-Component IVP with Cross Product — Lotka-Volterra

## Input (the original ODE system)

Lotka-Volterra predator-prey system:
  x₁' = α·x₁ - β·x₁·x₂
  x₂' = δ·x₁·x₂ - γ·x₂

with parameters α = 2/3, β = 4/3, γ = 1, δ = 1
and initial conditions x₁(0) = 1, x₂(0) = 1.

This is a 2-component system (L = 2) with cross-product nonlinearity x₁·x₂.

## What the autoformalizer should produce

This test focuses on the **f → φ → StdIVPData** pipeline only.

### Step 1: Define φ (nonlinearity at coefficient level)

- L = 2 components, so `φ : XL1 ν 2 → Fin 2 → l1Weighted ν`
- Component 0: `α • a 0 - β • (a 0 * a 1)` — linear + cross-product
- Component 1: `δ • (a 0 * a 1) - γ • a 1` — cross-product + linear
- The cross product `a 0 * a 1` is a Cauchy product between different components
- Define `φ_spec : Fin 2 → MvPolynomial (Fin 2) ℚ`:
  - Component 0: `C (2/3) * X 0 - C (4/3) * X 0 * X 1`
  - Component 1: `X 0 * X 1 - X 1`

### Step 2: Differentiability and bounds

- `differentiable_φ_component`: from `auto_poly_fderiv` / `fun_prop`
- Dφ bound (for Z₁): per-component operator norm of fderiv(φ)
- D²φ bound (for Z₂): Lipschitz constant — uses `active` set
  - Both components have cross-product → `active = {0, 1}` (all components active)
  - D²φ is constant bilinear (degree 2 polynomial)

### Step 3: Build StdIVPData

- Choose N (truncation order) and ν (weight)
- Provide numerical arrays: A_col, DF_col, abar_Q (from solver)
- Bundle into `StdIVPData`

## Where to find patterns

### IVP pipeline (formalized references)
- **Example83** (`L=3, N=30`): Closest — Lorenz system (3-component, cross products)
  - `Algebra.lean`: φ_lorenz with `a 0 * a 2`, `a 0 * a 1` cross products
  - Shows how `active` set handles sparse nonlinearity (component 0 is linear → inactive)
  - `Certificate.lean`: D₂_lorenz (Hessian), `pderiv_simp` for verification
- **Example81** (`L=1, N=10`): Scalar IVP (simpler, no cross products)

### Key differences from Example83 (Lorenz)
- L = 2 (not 3) — smaller system
- ALL components have cross products → `active = {0, 1} = Finset.univ`
  (Lorenz has component 0 linear → `active = {1, 2}`)
- Parameters are rational (2/3, 4/3) — need ℚ encoding in φ_spec
- Simpler Jacobian: 2×2 blocks (not 3×3)

### Key API
- `ivpCoeffs`: `source/IVP/Setup.lean` — generic F(a)_{k+1} = (k+1)·a_{k+1} - φ(a)_k
- `StdIVPData`: `source/IVP/StandardIVP.lean`
- `ivp_hDF_block_nat`: `source/IVP/DFBlock.lean` — Jacobian from φ_spec via native_decide
- `pderiv_simp`: `source/Tactic/PDerivSimp.lean` — verifies D²φ (Hessian entries)
- `auto_poly_fderiv`: `source/Tactic/AutoPolyFDeriv.lean`

## Difficulty notes

Compared to SimpleIVP (scalar):
- Multi-component (L = 2): φ takes `XL1 ν 2`, cross products between components
- Jacobian is 2×2 block matrix (not scalar)
- Active set is full (`Finset.univ`) — no sparsity simplification
- Rational parameters in φ_spec need `C (2/3 : ℚ)` encoding
-/

-- The autoformalizer should fill in everything below this line.
-- Only the ODE system is given: x₁' = (2/3)x₁ - (4/3)x₁x₂, x₂' = x₁x₂ - x₂.
