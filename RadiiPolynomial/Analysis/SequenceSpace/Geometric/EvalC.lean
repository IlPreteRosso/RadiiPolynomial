import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Aeval
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation
import Mathlib.Analysis.Complex.Basic

/-!
# Complex evaluation of the real Taylor carrier

`l1Weighted.evalC ν z hz` evaluates the real geometric ℓ¹ algebra into `ℂ` for
`‖z‖ ≤ ν`, using `aeval_of_norm_le` at `C = 1`. The shipped computation faces are
`evalC_apply`, `evalC_gen` and `evalC_ofReal`, relating the series, generator and real
coordinate evaluator. The generic bound is `lpOneAlg.norm_geomAeval_of_norm_le_apply_le`
in `Geometric/Aeval.lean`.

The classification of all continuous characters and its topological consequences belong
to `B5RecordTaylorSpectrum`, not to this shipped evaluator module. The coefficient carrier
stays real; only the evaluation target is complex.
-/

noncomputable section

namespace RadiiPolynomial

namespace l1Weighted

section EvalC

variable (ν : PosReal)

/-- **Complex evaluation** of the real Taylor carrier at a point `z` of the closed
complex disc of radius `ν`: the `C = 1` evaluation of the `aeval` API at the target
`ℂ` viewed as a real Banach algebra. -/
def evalC (z : ℂ) (hz : ‖z‖ ≤ (ν : ℝ)) : l1Weighted ν →A[ℝ] ℂ :=
  aeval_of_norm_le ν z hz

variable (z : ℂ) (hz : ‖z‖ ≤ (ν : ℝ))

/-- The series formula: `evalC ν z hz a = ∑' n, aₙ zⁿ`. -/
theorem evalC_apply (a : l1Weighted ν) :
    evalC ν z hz a = ∑' n, (l1Weighted.toSeq a n : ℂ) * z ^ n := by
  simp only [evalC, aeval_of_norm_le, lpOneAlg.geomAeval_of_norm_le, lpOneAlg.geomAeval_apply,
    Complex.real_smul]
  rfl

/-- Computation face on the generator: `e₁ ↦ z`. -/
@[simp] theorem evalC_gen : evalC ν z hz (lpOneAlg.single 1 1) = z :=
  aeval_of_norm_le_gen ν z hz

/-- At a real point the complex evaluation is the library's real evaluation `eval`
(Evaluation.lean), coerced into `ℂ`, by canonical uniqueness on the generator
and the direct real series formula. -/
theorem evalC_ofReal (x : ℝ) (hx : |x| ≤ ν) (a : l1Weighted ν) :
    evalC ν (x : ℂ) (by simpa [Complex.norm_real] using hx) a
      = ((l1Weighted.eval a x : ℝ) : ℂ) := by
  have h : evalC ν (x : ℂ) (by simpa [Complex.norm_real] using hx)
      = (ContinuousAlgHom.mk Complex.ofRealAm Complex.continuous_ofReal).comp
          (l1Weighted.aeval_of_norm_le ν x hx) :=
    algHom_ext ν (by rw [evalC_gen, ContinuousAlgHom.comp_apply, aeval_of_norm_le_gen]; rfl)
  exact (DFunLike.congr_fun h a).trans
    (congrArg (fun r : ℝ => (r : ℂ)) (aeval_of_norm_le_apply_real x hx a))


end EvalC

section Classification

variable {ν : PosReal}


end Classification

end l1Weighted

end RadiiPolynomial

end
