import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Aeval
import Mathlib.Analysis.Complex.Basic

/-!
# Complex evaluation of the real Taylor carrier: the Gelfand transform as `aeval`

The real geometric ℓ¹ algebra `l1Weighted ν` evaluates at every point of the closed
complex disc of radius `ν`: `evalC ν z hz : l1Weighted ν →A[ℝ] ℂ` is the `C = 1`
evaluation `aeval_of_norm_le ν z hz` of the `aeval` API (Aeval.lean) at the target
`B = ℂ` viewed as a real algebra. Nothing is re-proved here — the faces are the
`aeval` faces read at `B = ℂ`:

* introduction — `evalC` with the series formula `evalC_apply`;
* computation — `@[simp] evalC_gen : evalC ν z hz (single 1 1) = z`;
* the real bridge — `evalC_ofReal`: at a real point the complex evaluation is the
  library's `eval` (Evaluation.lean) coerced into `ℂ`, by uniqueness on the generator;
* contractivity — `norm_evalC_le : ‖evalC ν z hz a‖ ≤ ‖a‖` (Gelfand contractivity,
  book Prop. 8.1.3);
* classification — `character_classification_evalC`: every continuous ℝ-algebra
  homomorphism `l1Weighted ν →A[ℝ] ℂ` is `evalC` at a point of the closed disc.

Consequences for the real evaluation (`eval_mul` = `map_mul` of `evalC` read through
`evalC_ofReal`; `abs_eval_le` = `norm_evalC_le` at a real point) are re-derivable
in three steps each; Evaluation.lean keeps its own proofs (bridge, not migration).

Main declarations:
* `l1Weighted.evalC`, `evalC_apply`, `evalC_gen`, `evalC_ofReal`, `norm_evalC_le`
* `l1Weighted.character_classification_evalC`
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
(Evaluation.lean, multiplicativity by Mertens), coerced into `ℂ` — by uniqueness
on the generator alone. -/
theorem evalC_ofReal (x : ℝ) (hx : |x| ≤ ν) (a : l1Weighted ν) :
    evalC ν (x : ℂ) (by simpa [Complex.norm_real] using hx) a
      = ((l1Weighted.eval a x : ℝ) : ℂ) := by
  have h : evalC ν (x : ℂ) (by simpa [Complex.norm_real] using hx)
      = (ContinuousAlgHom.mk Complex.ofRealAm Complex.continuous_ofReal).comp
          (l1Weighted.evalContinuousAlgHom x hx) :=
    algHom_ext ν (by rw [evalC_gen, ContinuousAlgHom.comp_apply, evalContinuousAlgHom_gen]; rfl)
  rw [h]; rfl

/-- **Gelfand contractivity of the transform**: the sup over the closed complex disc
of radius `ν` of `|â|` is at most `‖a‖_ν`. Book Prop. 8.1.3 (p. 187) states exactly
this on the complex disc (primary pin); cf. Kaniuth, Thm 2.2.7(i). In the audit
(tmp/gelfand_design/Z_AUDIT.md) this is the *spectral floor*: the transform's sup is
a certificate-independent lower bound on every element norm entering a bound. The
trajectory bound `eval_traj_in_closedBall` (Applications/IVP/Taylor/Trajectory.lean)
is this inequality on the real segment plus the triangle inequality on the certified
ball. -/
theorem norm_evalC_le (a : l1Weighted ν) : ‖evalC ν z hz a‖ ≤ ‖a‖ :=
  norm_aeval_of_norm_le_apply_le ν z hz a

end EvalC

section Classification

variable {ν : PosReal}

/-- NEW theorem (not a promotion of the tmp complex-carrier classification, whose
domain is the ℂ-carrier): the continuous ℝ-algebra homomorphisms of the real ℓ¹_ν
into ℂ are exactly the evaluations at the points of the closed complex disc of radius
`ν` — the Gelfand spectrum of the complexification, stated as a hom identity without
a `Spec` object. The disc membership is the generator gate `norm_gen_le`; the
identity is uniqueness on the generator. -/
theorem character_classification_evalC (ψ : l1Weighted ν →A[ℝ] ℂ) :
    ∃ z : ℂ, ∃ hz : ‖z‖ ≤ (ν : ℝ), ψ = evalC ν z hz :=
  ⟨ψ (lpOneAlg.single 1 1), norm_gen_le ν ψ, algHom_ext ν (by rw [evalC_gen])⟩

end Classification

end l1Weighted

end RadiiPolynomial

end
