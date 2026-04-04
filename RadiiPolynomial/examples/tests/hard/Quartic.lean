import RadiiPolynomial.source.lpSpace.Eval
import RadiiPolynomial.source.lpSpace.CauchyProduct

/-!
# Hard Test: Quartic Zero-Finding — x⁴ - λ = 0

## Input (the original equation)

Find analytic families of solutions to f(x, λ) = x⁴ - λ = 0 near (x₀, λ₀) = (1, 1).

## What the autoformalizer should produce

This test focuses on the **f → F → semantic bridge** pipeline only.
Bounds and `general_radii_polynomial_theorem` are out of scope (already tested by Example77).

### Step 1: Define F on ℓ¹_ν (Part A — Algebraic)

- Recognize x⁴ as a 4-fold Cauchy product `a * a * a * a` on `l1Weighted ν`
- Define `F(λ₀, a) = a⁴ - c(λ₀)` where `c(λ₀)` encodes the parameterized RHS
  (λ₀ at index 0, 1 at index 1, 0 elsewhere)
- State `F_toSeq`: the explicit coefficient-level formula
- Prove differentiability and fderiv structure (`HasFDerivAt`, `fderiv`)

### Step 2: PowerSeries coefficient matching (Part PS)

- Define `paramPowerSeries` for the RHS λ₀ + z
- Show F(a) = 0 ⟹ power series coefficient matching
- Yields recurrence: a₀⁴ = λ₀, 4a₀³·a₁ = 1, higher terms from Cauchy convolution

### Step 3: Semantic bridge (Part B)

- Show: F(a) = 0 ⟹ eval(a, z)⁴ = λ₀ + z for |z| ≤ ν
- Uses `l1Weighted.eval_mul` (Mertens' theorem) from `source/lpSpace/Eval.lean`

### Step 4: Branch selection (Part C) — optional

- Show: eval(a, z) = (λ₀ + z)^(1/4) (positive real fourth root)
- Requires continuity + positivity at z = 0

## Where to find patterns

### Formalized reference (non-IVP zero-finding)
- `examples/Example77/Algebra.lean` — FULL pipeline for x² - λ = 0
  - Defines F = sq(a) - c(λ₀), proves HasFDerivAt, fderiv_F
  - Parts A, PS, B, C all formalized (zero sorries)

### Easy test skeletons (all sorried, same pipeline structure)
- `examples/tests/easy/TestQuadratic/Algebra.lean` — x² - λ = 0 (closest pattern)
- `examples/tests/easy/TestCubic/Algebra.lean` — x³ - λ = 0 (higher degree)

### Key API for the f-F bridge
- `l1Weighted.eval` + `eval_mul`: `source/lpSpace/Eval.lean` — Mertens' theorem
- `l1Weighted.toPowerSeries`: formal power series from ℓ¹ sequence
- Cauchy product (`mul` on `l1Weighted`): `source/lpSpace/CauchyProduct.lean`
- `auto_poly_fderiv`: `source/Tactic/AutoPolyFDeriv.lean` — automatic differentiation

## Difficulty notes

Compared to quadratic/cubic easy tests:
- 4-fold Cauchy product (iterated `eval_mul`)
- fderiv of x⁴ involves 4·x³ (degree 3 — `auto_poly_fderiv` should handle)
- Part C needs 4th-root continuity (harder than sqrt)
-/

-- The autoformalizer should fill in everything below this line.
-- Only the equation f(x, λ) = x⁴ - λ = 0 is given.
