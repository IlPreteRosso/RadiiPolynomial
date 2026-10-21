import RadiiPolynomial.Core
import RadiiPolynomial.Certification.LeanCertAdapter
import RadiiPolynomial.Applications.FiniteDimensional.Scalar

/-!
# Example 2.4.5 — Certificate

Verification of f(x) = x² - 2 near x̄ = 13/10 on the closed ball of radius r₀ = 3/20.
The polynomial is reified as a `CompPoly 1`; `StdFinDimData.tightC` computes the bounds
`Y₀`, `Z₀`, `Z₂` in exact rational arithmetic from x̄, `A = 19/50` and r₀, and the certificate
`ChecksC` is checked by `decide +kernel`.

`main_theorem` goes through the centred polynomial face `StdFinDimData.existsUniqueC` at
`R = ℝ` and the scalar instance `StdFinDimData.existsUnique_scalar_of`. The public parameter
abbreviations keep the example's hand-derived constants.
-/

open scoped Topology BigOperators
open Metric Set Filter ContinuousLinearMap
open RadiiPolynomial
open MvPolyBridge

namespace Example245.Cert

/-! ## Parameter definitions -/

noncomputable abbrev f     : ℝ → ℝ := fun x => x ^ 2 - 2
noncomputable abbrev xBar  : ℝ := 13 / 10
noncomputable abbrev r₀    : ℝ := 3 / 20

/-! ## Certificate data -/

/-- `f(x) = x² − 2` reified. -/
private def f_cpoly : CompPoly 1 := .sub (.mul (.X 0) (.X 0)) (.C 2)

/-- x̄, `A`, r₀; the bounds are computed (`tightC`). -/
private def dataC : StdFinDimData 1 := .tightC ![f_cpoly] ![13 / 10] !![19 / 50] (3 / 20)

private theorem checksC : dataC.ChecksC := by decide +kernel

/-! ## Main Theorem -/

theorem main_theorem :
    ∃! xTilde ∈ closedBall xBar r₀, f xTilde = 0 :=
  StdFinDimData.existsUnique_scalar_of ℝ dataC (dataC.existsUniqueC ℝ checksC)
    (fun x => by simp [dataC, StdFinDimData.tightC, f_cpoly, CompPoly.evalBanach]; ring)
    (by simp [dataC, StdFinDimData.tightC])
    (by norm_num [dataC, StdFinDimData.tightC])

theorem sqrt2 :
    ∃! xTilde ∈ closedBall (xBar : ℝ) r₀, xTilde ^ 2 = 2 := by
  obtain ⟨xTilde, ⟨hMem, hZero⟩, hUniq⟩ := main_theorem
  refine ⟨xTilde, ⟨hMem, ?_⟩, ?_⟩
  · simp only [f] at hZero; linarith
  · intro y ⟨hyMem, hySq⟩
    exact hUniq y ⟨hyMem, by simp only [f]; linarith⟩

end Example245.Cert
