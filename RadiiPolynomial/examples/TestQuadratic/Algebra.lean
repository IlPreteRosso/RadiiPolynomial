import RadiiPolynomial.source.BlockDiag.Scalar
import RadiiPolynomial.source.lpSpace.Eval

/-!
# Test Example: Quadratic Parameterized Equilibrium  f(x, λ) = x² - λ = 0

## Background

Section 7.7 of the reference book. Given an equilibrium (x₀, λ₀) with x₀² = λ₀
and 2x₀ ≠ 0, the implicit function theorem gives a smooth branch x(λ) near λ₀.

Substituting the Taylor expansion x(λ) = Σₙ aₙ (λ - λ₀)ⁿ into f(x(λ), λ) = 0
and matching powers of (λ - λ₀) yields F(a) = 0 in ℓ¹_ν.

This is the simplest case of the f-F bridge and serves as the template for
TestCubic (x³ - λ = 0) and TestCrossProduct (xy - λ = 0, x + y - 2 = 0).

## Pipeline

1. Part A  — Algebraic: Define F = a*a - c in the Banach algebra
2. Part PS — Formal Power Series: F(a)=0 ⟹ a² = c (coefficient matching)
3. Part B  — Semantic: F(a)=0 ⟹ eval(a,z)² = λ₀ + z (analytic evaluation)
4. Part C  — Branch Selection: eval(a, λ-λ₀) = √λ (IVT + positivity)

See `examples/Example77/` for the full formalized proof, and the reference
pipeline at `Example_7_7_Analytic.lean`.
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial
open RadiiPolynomial.l1Weighted (leftMul leftMul_apply norm_leftMul_le)

noncomputable section

variable {ν : PosReal}

namespace TestQuadratic

/-! ## Part A — Algebraic -/

/-! ### 1. The Squaring Map

The nonlinearity f(x) = x² becomes the Banach algebra multiplication a * a. -/

-- TASK: Define sq(a) in terms of Banach algebra multiplication.
def sq (a : l1Weighted ν) : l1Weighted ν := sorry

lemma sq_eq_pow (a : l1Weighted ν) : sq a = a ^ 2 := by sorry

lemma sq_eq_fun : (sq : l1Weighted ν → l1Weighted ν) = fun x => x ^ 2 :=
  funext sq_eq_pow

/-! ### 2. The Zero-Finding Map F

The parameter λ = λ₀ + (λ - λ₀) is encoded as the sequence c = (λ₀, 1, 0, 0, ...).
Substituting x = Σ aₙ tⁿ into x² - λ = 0 and matching powers of t gives
F(a) = a*a - c. -/

def paramSeq (lam0 : ℝ) : ℕ → ℝ := fun n =>
  match n with | 0 => lam0 | 1 => 1 | _ => 0

lemma paramSeq_mem (lam0 : ℝ) : l1Weighted.Mem ν (paramSeq lam0) := by
  rw [l1Weighted.mem_iff]
  apply summable_of_ne_finset_zero (s := {0, 1})
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [paramSeq, hn.1, hn.2]

def c (lam0 : ℝ) : l1Weighted ν := l1Weighted.mk (paramSeq lam0) (paramSeq_mem lam0)

-- TASK: Define F(a) = a*a - c(lam0).
def F (lam0 : ℝ) (a : l1Weighted ν) : l1Weighted ν := sorry

/-! ### 3. Fréchet Derivative

For sq(a) = a², d/dt (a + th)² |_{t=0} = 2ah, so DF = 2 • leftMul(a). -/

-- TASK: Prove the Fréchet derivative of sq.
theorem hasFDerivAt_sq (a : l1Weighted ν) :
    HasFDerivAt sq ((2 : ℝ) • leftMul a) a := by
  sorry

theorem fderiv_sq (a : l1Weighted ν) :
    fderiv ℝ sq a = (2 : ℝ) • leftMul a :=
  sorry

theorem differentiable_sq :
    Differentiable ℝ (sq : l1Weighted ν → l1Weighted ν) :=
  sorry

theorem hasFDerivAt_F (lam0 : ℝ) (a : l1Weighted ν) :
    HasFDerivAt (F lam0) ((2 : ℝ) • leftMul a) a := by
  sorry

theorem fderiv_F (lam0 : ℝ) (a : l1Weighted ν) :
    fderiv ℝ (F lam0) a = (2 : ℝ) • leftMul a :=
  sorry

theorem differentiable_F (lam0 : ℝ) :
    Differentiable ℝ (F lam0 : l1Weighted ν → l1Weighted ν) :=
  sorry

/-! ### 4. Sequence-Level Formula

Bridge the abstract F to Cauchy products for numerical verification. -/

lemma F_toSeq (lam0 : ℝ) (a : l1Weighted ν) (n : ℕ) :
    l1Weighted.toSeq (F lam0 a) n =
    CauchyProduct (l1Weighted.toSeq a) (l1Weighted.toSeq a) n -
      paramSeq lam0 n := by
  sorry

/-! ## Part PS — Formal Power Series (Coefficient Matching)

This is the "matching coefficients of like degrees" step from the book (§7.7).

Substituting x(λ) = Σ aₙ tⁿ into x² - λ = 0 and matching coefficients of
like powers of t:

  coeff_n(x²) = coeff_n(λ₀ + t)
  ⟹ (a ⋆ a)ₙ = cₙ  for all n
  ⟹ toPowerSeries(a)² = paramPowerSeries(λ₀)  as formal power series

The key principle: two formal power series are equal iff their coefficients agree
at every degree. This justifies that F(a) = 0 is the CORRECT equation to solve. -/

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

/-- PowerSeries squaring agrees with self-convolution. -/
-- TASK: Prove using l1Weighted.coeff_mul_eq_cauchyProduct.
theorem coeff_sq_eq_cauchyProduct (a : l1Weighted ν) (n : ℕ) :
    (PowerSeries.coeff n) (l1Weighted.toPowerSeries a ^ 2) =
    CauchyProduct (l1Weighted.toSeq a) (l1Weighted.toSeq a) n := by
  sorry

/-- **Coefficient matching**: F(a) = 0 implies the formal power series for x²
equals the formal power series for λ. This IS the "matching coefficients of
like degrees" step — we go from F(a)=0 (componentwise) to an equality of
formal power series. -/
-- TASK: Prove by ext + coeff_sq_eq_cauchyProduct + F_toSeq.
theorem toPowerSeries_sq_eq_param (a : l1Weighted ν) (lam0 : ℝ)
    (hF : F lam0 a = 0) :
    l1Weighted.toPowerSeries a ^ 2 = paramPowerSeries lam0 := by
  sorry

/-! ## Part B — Semantic Bridge

Using `l1Weighted.eval` from `Eval.lean`:
  eval(a, z) = Σₙ aₙ zⁿ    (converges for |z| ≤ ν)

The chain of reasoning:
  f(eval(a,z), λ₀+z) = eval(a,z)² - (λ₀+z)
                      = eval(a*a, z) - eval(c, z)     -- by eval_mul + eval_paramSeq
                      = eval(a*a - c, z)               -- by eval_sub
                      = eval(F(a), z)                   -- by definition of F
                      = eval(0, z) = 0                  -- since F(a) = 0
-/

/-- Evaluation of the parameter sequence: Σ cₙ zⁿ = λ₀ + z. -/
-- TASK: Prove. Hint: c has finite support {0, 1}, so use tsum_eq_sum.
theorem eval_paramSeq (lam0 z : ℝ) :
    l1Weighted.eval (c lam0 : l1Weighted ν) z = lam0 + z := by
  sorry

/-- **The semantic bridge**: If F(a) = 0, then eval(a, z)² = λ₀ + z.
This connects the coefficient equation F(a) = 0 back to the original
equation f(x, λ) = x² - λ = 0 via the analytic evaluation map. -/
-- TASK: Prove using eval_mul, eval_sub, and eval_paramSeq.
theorem eval_sq_eq (a : l1Weighted ν) (lam0 : ℝ) {z : ℝ} (hz : |z| ≤ ν)
    (hF : F lam0 a = 0) :
    l1Weighted.eval a z ^ 2 = lam0 + z := by
  sorry

/-! ## Part C — Branch Selection

The equation x² = λ has two branches (±√λ). To identify WHICH branch our
solution corresponds to, we use:
  1. eval(a, 0) = a₀       (evaluation at zero extracts the leading coefficient)
  2. a₀ > 0                (numerical check on the approximate solution)
  3. Continuity + IVT       (the branch stays positive on the disk)
-/

/-- eval(a, 0) = a₀. -/
-- TASK: Prove. Hint: all terms with z^n vanish for n ≥ 1.
theorem eval_at_zero (a : l1Weighted ν) :
    l1Weighted.eval a 0 = l1Weighted.toSeq a 0 := by
  sorry

/-- The analytic function satisfies x̃(λ)² = λ. -/
-- TASK: Prove using eval_sq_eq with z = λ - λ₀.
theorem analyticSolution_is_sqrt (a : l1Weighted ν) (lam0 : ℝ)
    (hF : F lam0 a = 0) {lam : ℝ} (hlam : |lam - lam0| ≤ ν) :
    l1Weighted.eval a (lam - lam0) ^ 2 = lam := by
  sorry

/-- **Branch selection**: With a₀ > 0, the solution is the positive branch √λ.

The argument:
1. a₀² = λ₀ and a₀ > 0 ⟹ a₀ = √λ₀
2. eval is continuous on the disk |z| ≤ ν
3. eval(0) = a₀ = √λ₀ > 0, so by IVT eval cannot reach 0 on the disk
4. Therefore eval(z) > 0, and since eval(z)² = λ₀ + z, we get eval(z) = √(λ₀ + z) -/
-- TASK: This is the hardest part. Requires continuity of eval + IVT.
theorem analyticSolution_eq_sqrt (a : l1Weighted ν) (lam0 : ℝ)
    (hF : F lam0 a = 0) (hlam0_pos : 0 < lam0)
    {lam : ℝ} (hlam : |lam - lam0| ≤ ν) (hlam_pos : 0 < lam)
    (ha0_pos : 0 < l1Weighted.toSeq a 0) :
    l1Weighted.eval a (lam - lam0) = Real.sqrt lam := by
  sorry

/-! ## Notes

### Z₂ Bound Structure (bonus reading, no tasks)

For x², DF(a) = 2 • leftMul(a) is AFFINE in a, so
  ‖DF(a) - DF(ā)‖ ≤ 2‖a - ā‖ ≤ 2r₀
giving a CONSTANT Z₂ bound and a QUADRATIC radii polynomial.

### Concrete values

For λ₀ = 1: x₀ = 1, so a₀ = 1, and
  eval(a, 0)² = 1² = 1 = λ₀  ✓
  eval(a, λ - 1) = √λ  for |λ - 1| ≤ ν  ✓
-/

end TestQuadratic

end
