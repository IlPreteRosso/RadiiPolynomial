import RadiiPolynomial.source.BlockDiag.Scalar
import RadiiPolynomial.source.lpSpace.Eval

/-!
# Test Example: Cross-Product System

## Original System

  f₁(x, y, λ) = xy - λ = 0
  f₂(x, y, λ) = x + y - 2 = 0

This is a 2-variable parameterized equilibrium problem. The bilinear term `xy`
introduces the CROSS Cauchy product — the key new element beyond Example77.

## Background

In Example77, the scalar equation f(x) = x² - λ leads to a single zero-finding
equation F(a) = a*a - c in ℓ¹_ν, where `a * a` is the SELF Cauchy product
(same sequence convolved with itself).

Here we have two unknowns x(λ) and y(λ), each with Taylor expansions:
  x(λ) = Σₙ aₙ (λ - λ₀)ⁿ
  y(λ) = Σₙ bₙ (λ - λ₀)ⁿ

Substituting into each equation and matching powers of (λ - λ₀) yields a
system of two zero-finding equations in (ℓ¹_ν)².

## Your Tasks

### Part A — Algebraic: Define the component maps

1. Define F₁ and F₂ in ℓ¹_ν
2. Prove the sequence-level bridge formulas

### Part B — Semantic: Bridge F(a,b) = 0 back to f(x,y,λ) = 0

3. Show `eval(c, z) = λ₀ + z` and `eval(d, z) = 2`
4. Show that if F₁(a,b) = 0 then `eval(a,z) * eval(b,z) = λ₀ + z`
5. Show that if F₂(a,b) = 0 then `eval(a,z) + eval(b,z) = 2`

Part B uses `l1Weighted.eval` and `l1Weighted.eval_mul` from `source/lpSpace/Eval.lean`.

## Key Observation

The product xy becomes the CROSS Cauchy product of two different sequences:
  (a * b)ₙ = Σⱼ₌₀ⁿ aⱼ · bₙ₋ⱼ

This is the Banach algebra multiplication applied to two DIFFERENT elements,
unlike Example77's self-product `a * a`.

## Concrete Equilibrium

For λ₀ = 3/4: x₀ + y₀ = 2 and x₀y₀ = 3/4, giving
  x₀ = 3/2, y₀ = 1/2   (roots of t² - 2t + 3/4 = 0)
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial
open RadiiPolynomial.l1Weighted (leftMul leftMul_apply norm_leftMul_le)

noncomputable section

variable {ν : PosReal}

namespace TestCrossProduct

/-! ## Part A — Algebraic -/

/-! ### 1. Constant Sequences

Each equation contributes its own constant sequence from the RHS:

  Equation xy = λ:   λ = λ₀ + (λ-λ₀), encoded as c = (λ₀, 1, 0, ...)
  Equation x+y = 2:  the constant 2, encoded as d = (2, 0, 0, ...)
-/

def paramSeq (lam0 : ℝ) : ℕ → ℝ := fun n =>
  match n with | 0 => lam0 | 1 => 1 | _ => 0

def constSeq : ℕ → ℝ := fun n =>
  match n with | 0 => 2 | _ => 0

lemma paramSeq_mem (lam0 : ℝ) : l1Weighted.Mem ν (paramSeq lam0) := by
  rw [l1Weighted.mem_iff]
  apply summable_of_ne_finset_zero (s := {0, 1})
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [paramSeq, hn.1, hn.2]

lemma constSeq_mem : l1Weighted.Mem ν (constSeq : ℕ → ℝ) := by
  rw [l1Weighted.mem_iff]
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [constSeq]

def c (lam0 : ℝ) : l1Weighted ν := l1Weighted.mk (paramSeq lam0) (paramSeq_mem lam0)
def d : l1Weighted ν := l1Weighted.mk constSeq constSeq_mem

/-! ### 2. Component Maps

Derive F₁ and F₂ by substituting Taylor expansions into the original equations.

**Equation 1**: xy - λ = 0
  (Σ aₙ tⁿ)(Σ bₙ tⁿ) - (λ₀ + t) = 0
  → F₁(a, b) = a * b - c    (cross Cauchy product minus parameter sequence)

**Equation 2**: x + y - 2 = 0
  (Σ aₙ tⁿ) + (Σ bₙ tⁿ) - 2 = 0
  → F₂(a, b) = a + b - d    (pointwise sum minus constant sequence)
-/

-- TASK: Define the first component of F.
-- Hint: xy becomes the cross Cauchy product `a * b` in the Banach algebra.
def F₁ (lam0 : ℝ) (a b : l1Weighted ν) : l1Weighted ν := sorry

-- TASK: Define the second component of F.
-- Hint: x + y is pointwise addition of sequences.
def F₂ (a b : l1Weighted ν) : l1Weighted ν := sorry

/-! ### 3. Sequence-Level Formulas

These lemmas serve as specifications: once your definitions of F₁ and F₂ are
correct, these should be provable. -/

-- Equation 1: the cross Cauchy product formula
lemma F₁_toSeq (lam0 : ℝ) (a b : l1Weighted ν) (n : ℕ) :
    l1Weighted.toSeq (F₁ lam0 a b) n =
    CauchyProduct (l1Weighted.toSeq a) (l1Weighted.toSeq b) n -
      paramSeq lam0 n := by
  sorry

-- Equation 2: pointwise addition formula
lemma F₂_toSeq (a b : l1Weighted ν) (n : ℕ) :
    l1Weighted.toSeq (F₂ a b) n =
    l1Weighted.toSeq a n + l1Weighted.toSeq b n - constSeq n := by
  sorry

/-! ## Part PS — Formal Power Series (Coefficient Matching)

This is the "matching coefficients of like degrees" step from the book (§9.2, p.226).

Substituting x(λ) = Σ aₙ tⁿ, y(λ) = Σ bₙ tⁿ into the original system and
matching coefficients of like powers of t gives:

  Equation 1 (xy = λ):  coeff_n(x·y) = coeff_n(λ₀ + t)
    ⟹ (a ⋆ b)ₙ = cₙ  for all n
    ⟹ toPowerSeries(a) · toPowerSeries(b) = paramPowerSeries(λ₀)

  Equation 2 (x+y = 2): coeff_n(x+y) = coeff_n(2)
    ⟹ aₙ + bₙ = dₙ  for all n
    ⟹ toPowerSeries(a) + toPowerSeries(b) = constPowerSeries

The key principle: two formal power series are equal iff their coefficients agree
at every degree. This justifies that F(a,b) = 0 is the CORRECT equation to solve. -/

/-- The parameter sequence λ₀ + t as a formal power series. -/
def paramPowerSeries (lam0 : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (paramSeq lam0)

@[simp]
theorem coeff_paramPowerSeries (lam0 : ℝ) (n : ℕ) :
    (PowerSeries.coeff n) (paramPowerSeries lam0) = paramSeq lam0 n :=
  PowerSeries.coeff_mk n _

/-- paramPowerSeries(λ₀) = C(λ₀) + X in the power series ring. -/
theorem paramPowerSeries_eq (lam0 : ℝ) :
    paramPowerSeries lam0 = PowerSeries.C lam0 + PowerSeries.X := by
  sorry

/-- The constant 2 as a formal power series. -/
def constPowerSeries : PowerSeries ℝ :=
  PowerSeries.mk constSeq

@[simp]
theorem coeff_constPowerSeries (n : ℕ) :
    (PowerSeries.coeff n) (constPowerSeries : PowerSeries ℝ) = constSeq n :=
  PowerSeries.coeff_mk n _

/-- constPowerSeries = C(2) in the power series ring. -/
theorem constPowerSeries_eq :
    (constPowerSeries : PowerSeries ℝ) = PowerSeries.C 2 := by
  sorry

/-- **Coefficient matching for equation 1**: F₁(a,b) = 0 implies the formal
power series for x·y equals the formal power series for λ. -/
-- TASK: Prove by ext + coeff_mul + F₁_toSeq.
theorem toPowerSeries_mul_eq_param (a b : l1Weighted ν) (lam0 : ℝ)
    (hF : F₁ lam0 a b = 0) :
    l1Weighted.toPowerSeries a * l1Weighted.toPowerSeries b =
      paramPowerSeries lam0 := by
  sorry

/-- **Coefficient matching for equation 2**: F₂(a,b) = 0 implies the formal
power series for x+y equals the formal power series for 2. -/
-- TASK: Prove by ext + map_add + F₂_toSeq.
theorem toPowerSeries_add_eq_const (a b : l1Weighted ν)
    (hF : F₂ a b = 0) :
    l1Weighted.toPowerSeries a + l1Weighted.toPowerSeries b =
      constPowerSeries := by
  sorry

/-! ## Part B — Semantic Bridge

Using `l1Weighted.eval` from `Eval.lean`:
  eval(a, z) = Σₙ aₙ zⁿ    (converges for |z| ≤ ν)

Key property: `eval_mul` gives eval(a * b, z) = eval(a, z) * eval(b, z).

### Goal: Show F₁(a,b) = 0 ∧ F₂(a,b) = 0 implies the original system holds

For equation 1 (xy - λ = 0):
  eval(a,z) * eval(b,z) = eval(a*b, z)           -- by eval_mul
                        = eval(c + F₁(a,b), z)    -- since a*b = c + F₁
                        = eval(c, z) + eval(F₁, z) -- by eval_add
                        = (λ₀ + z) + 0 = λ₀ + z   -- by eval_paramSeq + F₁=0

For equation 2 (x + y - 2 = 0):
  eval(a,z) + eval(b,z) = eval(a+b, z)            -- by eval_add
                        = eval(d + F₂(a,b), z)     -- since a+b = d + F₂
                        = eval(d, z) + eval(F₂, z)  -- by eval_add
                        = 2 + 0 = 2                  -- by eval_constSeq + F₂=0
-/

/-- Evaluation of the parameter sequence: Σ cₙ zⁿ = λ₀ + z. -/
-- TASK: Prove this. Hint: c has finite support {0, 1}, so use tsum_eq_sum.
theorem eval_paramSeq (lam0 z : ℝ) :
    l1Weighted.eval (c lam0 : l1Weighted ν) z = lam0 + z := by
  sorry

/-- Evaluation of the constant sequence: Σ dₙ zⁿ = 2. -/
-- TASK: Prove this. Hint: d has finite support {0}, so use tsum_eq_single.
theorem eval_constSeq (z : ℝ) :
    l1Weighted.eval (d : l1Weighted ν) z = 2 := by
  sorry

/-- **Semantic bridge for equation 1**: F₁(a,b) = 0 ⟹ eval(a,z) * eval(b,z) = λ₀ + z.
This says: if the coefficient equation holds, then xy = λ holds analytically. -/
-- TASK: Prove using eval_mul, eval_sub, and eval_paramSeq.
theorem eval_cross_eq (a b : l1Weighted ν) (lam0 : ℝ) {z : ℝ} (hz : |z| ≤ ν)
    (hF₁ : F₁ lam0 a b = 0) :
    l1Weighted.eval a z * l1Weighted.eval b z = lam0 + z := by
  sorry

/-- **Semantic bridge for equation 2**: F₂(a,b) = 0 ⟹ eval(a,z) + eval(b,z) = 2.
This says: if the coefficient equation holds, then x + y = 2 holds analytically. -/
-- TASK: Prove using eval_add, eval_sub, and eval_constSeq.
theorem eval_sum_eq (a b : l1Weighted ν) {z : ℝ} (hz : |z| ≤ ν)
    (hF₂ : F₂ a b = 0) :
    l1Weighted.eval a z + l1Weighted.eval b z = 2 := by
  sorry

/-! ## Notes

### Fréchet Derivatives (bonus)

  DF(ā, b̄) = | leftMul(b̄)   leftMul(ā) |
              |      I              I      |

### Z₂ structure

F₁ is bilinear, so DF₁ is affine:
  ‖DF₁(a,b) - DF₁(ā,b̄)‖ ≤ ‖b - b̄‖ + ‖a - ā‖ ≤ 2r₀
DF₂ is constant, so its contribution to Z₂ is 0.

### Concrete values

For λ₀ = 3/4: x₀ = 3/2, y₀ = 1/2, so
  a₀ = 3/2, b₀ = 1/2
  eval(a, 0) * eval(b, 0) = (3/2)(1/2) = 3/4 = λ₀  ✓
  eval(a, 0) + eval(b, 0) = 3/2 + 1/2 = 2           ✓
-/

end TestCrossProduct
