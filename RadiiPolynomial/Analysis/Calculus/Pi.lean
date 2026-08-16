import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Calculus on Pi Types

Small bridge lemmas for coordinate projections, shared by polynomial semantics and tactics.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι : Type*} {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Fréchet derivative of a coordinate projection on a non-dependent Pi type. -/
@[simp]
theorem fderiv_pi_apply (i : ι) (x : ι → F) :
    fderiv 𝕜 (fun a : ι → F => a i) x = ContinuousLinearMap.proj i := by
  show fderiv 𝕜 (⇑(ContinuousLinearMap.proj (R := 𝕜) i)) x = _
  exact ContinuousLinearMap.fderiv _

/-- Differentiability of a coordinate projection. -/
@[fun_prop]
theorem differentiable_pi_apply (i : ι) :
    Differentiable 𝕜 (fun a : ι → F => a i) :=
  (ContinuousLinearMap.proj i : (ι → F) →L[𝕜] F).differentiable
