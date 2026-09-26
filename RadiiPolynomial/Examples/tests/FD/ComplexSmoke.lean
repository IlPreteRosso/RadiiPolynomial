import RadiiPolynomial.Applications.FiniteDimensional.Scalar
import RadiiPolynomial.Algebra.Polynomial.CompPoly.Derivative
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Test (family FD): the finite-dimensional polynomial face over `ℂ`

Not part of the default build (imported by no module); build it with
`lake build RadiiPolynomial.Examples.tests.FD.ComplexSmoke`.

The coordinate ring of the faces is any normed commutative real algebra. The same syntax
`z² − 2` and the same kernel-checked rational certificate `ChecksC` (x̄ = 13/10, `A = 19/50`,
r₀ = 3/20) give, over `R = ℂ`, the derivative formula `D(z²−2)(x) h = 2 x h` and a unique complex
zero in the complex disc `|z − 1.3| ≤ 0.15`.
-/

open Metric
open RadiiPolynomial MvPolyBridge MvPolyBridge.CompPoly

namespace Tests.FD

/-- `f(x) = x² − 2` reified. -/
def f_cpoly : CompPoly 1 := .sub (.mul (.X 0) (.X 0)) (.C 2)

/-- x̄, `A`, r₀; the bounds are computed (`tightC`). -/
def dataC : StdFinDimData 1 := .tightC ![f_cpoly] ![13 / 10] !![19 / 50] (3 / 20)

theorem checksC : dataC.ChecksC := by decide +kernel

/-- The derivative formula at a point, over `ℂ`. -/
theorem hasFDerivAt_f_cpoly_complex (x : Fin 1 → ℂ) :
    HasFDerivAt (fun u : Fin 1 → ℂ => f_cpoly.evalBanach u) (gradCLM f_cpoly x) x ∧
      ∀ h : Fin 1 → ℂ, gradCLM f_cpoly x h = 2 * x 0 * h 0 := by
  refine ⟨hasFDerivAt_evalBanach f_cpoly x, fun h => ?_⟩
  rw [gradCLM_apply, Fin.sum_univ_one]
  simp [f_cpoly, CompPoly.pderiv, CompPoly.evalBanach, two_mul]

/-- The unique complex zero of `z² − 2` in the complex disc `|z − 1.3| ≤ 0.15`, from the same
kernel-checked `ChecksC`. -/
theorem sqrt_two_complex :
    ∃! z ∈ closedBall (13 / 10 : ℂ) (3 / 20), (fun z : ℂ => z ^ 2 - 2) z = 0 :=
  StdFinDimData.existsUnique_scalar_of ℂ dataC (dataC.existsUniqueC ℂ checksC)
    (fun x => by simp [dataC, StdFinDimData.tightC, f_cpoly, CompPoly.evalBanach]; ring)
    (by simp [dataC, StdFinDimData.tightC])
    (by norm_num [dataC, StdFinDimData.tightC])

end Tests.FD
