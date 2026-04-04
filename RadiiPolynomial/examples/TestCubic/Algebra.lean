import RadiiPolynomial.source.BlockDiag.Scalar
import RadiiPolynomial.source.Tactic.AutoPolyFDeriv
import RadiiPolynomial.source.lpSpace.Eval

/-!
# Test Example: Cubic Parameterized Equilibrium  f(x, λ) = x³ - λ = 0

## Background

Section 7.7 of the reference book treats f(x, λ) = x² - λ = 0 (see `examples/Example77/`).
Here we consider the cubic analogue: f(x, λ) = x³ - λ = 0.

Given an equilibrium (x₀, λ₀) with x₀³ = λ₀ and 3x₀² ≠ 0, the implicit function
theorem gives a smooth branch x(λ) near λ₀. Substituting the Taylor expansion

  x(λ) = Σₙ aₙ (λ - λ₀)ⁿ

into f(x(λ), λ) = 0 and matching powers of (λ - λ₀) yields a zero-finding
problem F(a) = 0 in the sequence space ℓ¹_ν.

## Your Tasks

### Part A — Algebraic: Define F in the Banach algebra

1. Define the cubing map and F in ℓ¹_ν (what does x³ become in the Banach algebra?)
2. Prove the Fréchet derivative of the cubing map
3. State the sequence-level formula for F (bridge to Cauchy products)

### Part B — Semantic: Bridge F(a) = 0 back to f(x,λ) = 0

4. Show that `eval(c, z) = λ₀ + z` (evaluation of the parameter sequence)
5. Show that if F(a) = 0 then `eval(a, z)³ = λ₀ + z` (the f-to-F bridge!)

Part B uses `l1Weighted.eval` and `l1Weighted.eval_mul` from `source/lpSpace/Eval.lean`.

## Hints

- In Example77, x² becomes `a * a` (one Cauchy product). What does x³ become?
- The Banach algebra `l1Weighted ν` is commutative, so `(a * a) * a = a * (a * a)`.
- For the Fréchet derivative: `d/dt (a + th)³ |_{t=0} = ?` (use the product rule).
- For Part B: `eval_mul` gives `eval(a*b, z) = eval(a, z) * eval(b, z)`.
-/

open scoped BigOperators Topology
open Metric Set Filter ContinuousLinearMap RadiiPolynomial
open RadiiPolynomial.l1Weighted (leftMul leftMul_apply norm_leftMul_le)

noncomputable section

variable {ν : PosReal}

namespace TestCubic

/-! ## Part A — Algebraic -/

/-! ### 1. The Cubing Map

In Example77, the squaring map is `sq(a) = a * a`.
Define the analogous cubing map for x³. -/

-- TASK: Define cube(a) in terms of Banach algebra multiplication.
def cube (a : l1Weighted ν) : l1Weighted ν := sorry

lemma cube_eq_pow (a : l1Weighted ν) : cube a = a ^ 3 := by sorry

lemma cube_eq_fun : (cube : l1Weighted ν → l1Weighted ν) = fun x => x ^ 3 :=
  funext cube_eq_pow

/-! ### 2. The Zero-Finding Map F

The parameter λ = λ₀ + (λ - λ₀) is encoded as the sequence c = (λ₀, 1, 0, 0, ...).
This is the same encoding as Example77 — it depends only on how λ enters the
equation (linearly), not on the nonlinearity f. -/

def paramSeq (lam0 : ℝ) : ℕ → ℝ := fun n =>
  match n with | 0 => lam0 | 1 => 1 | _ => 0

lemma paramSeq_mem (lam0 : ℝ) : l1Weighted.Mem ν (paramSeq lam0) := by
  rw [l1Weighted.mem_iff]
  apply summable_of_ne_finset_zero (s := {0, 1})
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [paramSeq, hn.1, hn.2]

def c (lam0 : ℝ) : l1Weighted ν := l1Weighted.mk (paramSeq lam0) (paramSeq_mem lam0)

-- TASK: Define F(a). Compare: Example77 defines `F lam0 a = sq a - c lam0`.
def F (lam0 : ℝ) (a : l1Weighted ν) : l1Weighted ν := sorry

/-! ### 3. Fréchet Derivative

For sq(a) = a², the derivative is `2 • leftMul a` (i.e., h ↦ 2·a·h).
For cube(a) = a³, compute d/dt (a + th)³ |_{t=0}.

Recall: `leftMul b` is the continuous linear map `h ↦ b * h`. -/

-- TASK: Prove the Fréchet derivative of cube.
-- Hint: d/dt (a + th)³|_{t=0} = 3a²h, so DF = 3 • leftMul(a * a).
theorem hasFDerivAt_cube (a : l1Weighted ν) :
    HasFDerivAt cube ((3 : ℝ) • leftMul (a * a)) a := by
  sorry

theorem fderiv_cube (a : l1Weighted ν) :
    fderiv ℝ cube a = (3 : ℝ) • leftMul (a * a) :=
  sorry

theorem differentiable_cube :
    Differentiable ℝ (cube : l1Weighted ν → l1Weighted ν) :=
  sorry

theorem hasFDerivAt_F (lam0 : ℝ) (a : l1Weighted ν) :
    HasFDerivAt (F lam0) ((3 : ℝ) • leftMul (a * a)) a := by
  sorry

theorem fderiv_F (lam0 : ℝ) (a : l1Weighted ν) :
    fderiv ℝ (F lam0) a = (3 : ℝ) • leftMul (a * a) :=
  sorry

theorem differentiable_F (lam0 : ℝ) :
    Differentiable ℝ (F lam0 : l1Weighted ν → l1Weighted ν) :=
  sorry

/-! ### 4. Sequence-Level Formula

Bridge the abstract F to Cauchy products for numerical verification.
The triple product (a*a*a)ₙ is a double convolution:

  (a * a * a)ₙ = Σᵢ (a * a)ᵢ · aₙ₋ᵢ = Σᵢ (Σⱼ aⱼ · aᵢ₋ⱼ) · aₙ₋ᵢ
-/

lemma F_toSeq (lam0 : ℝ) (a : l1Weighted ν) (n : ℕ) :
    l1Weighted.toSeq (F lam0 a) n =
    CauchyProduct (CauchyProduct (l1Weighted.toSeq a) (l1Weighted.toSeq a))
      (l1Weighted.toSeq a) n - paramSeq lam0 n := by
  sorry

/-! ## Part B — Semantic Bridge

This is the f-to-F connection. Using `l1Weighted.eval` from `Eval.lean`:
  eval(a, z) = Σₙ aₙ zⁿ

The key property is `eval_mul`: eval(a * b, z) = eval(a, z) * eval(b, z).

### Goal: Show F(a) = 0 implies f(eval(a,z), λ₀+z) = 0

The chain of reasoning:
  f(eval(a,z), λ₀+z) = eval(a,z)³ - (λ₀+z)
                      = eval(a,z) * eval(a,z) * eval(a,z) - (λ₀+z)
                      = eval(a*a*a, z) - eval(c, z)         -- by eval_mul + eval_paramSeq
                      = eval(a*a*a - c, z)                   -- by eval_sub
                      = eval(F(a), z)                        -- by definition of F
                      = eval(0, z) = 0                       -- since F(a) = 0
-/

/-- Evaluation of the parameter sequence: Σ cₙ zⁿ = λ₀ + z. -/
-- TASK: Prove this. Hint: c has finite support {0, 1}, so use tsum_eq_sum.
theorem eval_paramSeq (lam0 z : ℝ) :
    l1Weighted.eval (c lam0 : l1Weighted ν) z = lam0 + z := by
  sorry

/-- **The semantic bridge**: If F(a) = 0, then eval(a, z)³ = λ₀ + z.
This connects the coefficient equation F(a) = 0 back to the original
equation f(x, λ) = x³ - λ = 0 via the analytic evaluation map.

Compare with `l1Weighted.eval_sq_eq` in the old Example 7.7 analytic file,
which proves: F(a) = 0 ⟹ eval(a, z)² = λ₀ + z  for the quadratic case. -/
-- TASK: Prove this using eval_mul, eval_sub, and eval_paramSeq.
theorem eval_cube_eq (a : l1Weighted ν) (lam0 : ℝ) {z : ℝ} (hz : |z| ≤ ν)
    (hF : F lam0 a = 0) :
    l1Weighted.eval a z ^ 3 = lam0 + z := by
  sorry

/-! ## Notes

### Z₂ Bound Structure (bonus reading, no tasks)

Unlike x² where DF(a) = 2 • leftMul(a) is AFFINE in a (so Z₂ is constant),
for x³ the derivative DF(a) = 3 • leftMul(a²) is QUADRATIC in a.

This means Z₂(r₀) ≤ 3‖A‖ · (2‖ā‖ + r₀), a LINEAR function of r₀,
making the radii polynomial CUBIC. The `generalRadiiPolynomial` framework
handles this since Z₂ is allowed to depend on r.

### Branch Selection

The equation x³ = λ has a unique real root (∛λ for λ > 0), so unlike the
quadratic case (which requires IVT to select the positive branch), the
cubic case needs no branch selection argument. -/

end TestCubic
