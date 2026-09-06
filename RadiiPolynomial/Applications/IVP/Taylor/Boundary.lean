import RadiiPolynomial.Applications.IVP.Boundary
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Aeval

/-!
# The Taylor IVP boundary character

Taylor coefficients are anchored at the expansion centre.  Evaluation at
`0` is a continuous algebra character, and `shiftDivN` is already the
primitive normalized to vanish there.
-/

noncomputable section

namespace RadiiPolynomial

namespace IVP

variable (ν : PosReal)

/-- Evaluation at the Taylor expansion centre. -/
def taylorBoundaryCharacter : l1Weighted ν →A[ℝ] ℝ :=
  l1Weighted.evalContinuousAlgHom 0 (by simp)

@[simp]
theorem taylorBoundaryCharacter_apply (a : l1Weighted ν) :
    taylorBoundaryCharacter ν a = l1Weighted.toSeq a 0 := by
  rw [taylorBoundaryCharacter, l1Weighted.evalContinuousAlgHom_apply,
    l1Weighted.eval_at_zero]

/-! ### Changing the boundary point -/

/-- Evaluation at the left endpoint, when the Taylor disc contains it. -/
def taylorEndpointCharacter (hν : (1 : ℝ) ≤ (ν : ℝ)) : l1Weighted ν →A[ℝ] ℝ :=
  l1Weighted.evalContinuousAlgHom (-1) (by simpa using hν)

@[simp]
theorem taylorEndpointCharacter_apply (hν : (1 : ℝ) ≤ (ν : ℝ))
    (a : l1Weighted ν) :
    taylorEndpointCharacter ν hν a = l1Weighted.eval a (-1) :=
  rfl

/-- The change from Taylor centre bordering to left-endpoint bordering. -/
def taylorReborderingDefect (hν : (1 : ℝ) ≤ (ν : ℝ)) : l1Weighted ν →L[ℝ] ℝ :=
  (taylorEndpointCharacter ν hν).toContinuousLinearMap -
    (taylorBoundaryCharacter ν).toContinuousLinearMap

@[simp]
theorem taylorReborderingDefect_apply (hν : (1 : ℝ) ≤ (ν : ℝ))
    (a : l1Weighted ν) :
    taylorReborderingDefect ν hν a =
      l1Weighted.eval a (-1) - l1Weighted.toSeq a 0 := by
  rw [taylorReborderingDefect, sub_apply, ContinuousAlgHom.coe_toContinuousLinearMap]
  change taylorEndpointCharacter ν hν a - taylorBoundaryCharacter ν a = _
  rw [taylorEndpointCharacter_apply, taylorBoundaryCharacter_apply]

/-- Re-bordering is `1/ν`-Lipschitz: changing the boundary point ignores the
constant coefficient, so its first possible contribution occurs at mode one. -/
theorem norm_taylorReborderingDefect_apply_le (hν : (1 : ℝ) ≤ (ν : ℝ))
    (a : l1Weighted ν) :
    ‖taylorReborderingDefect ν hν a‖ ≤ (ν : ℝ)⁻¹ * ‖a‖ := by
  apply lpOneAlg.norm_le_of_cols
  intro n
  rw [← l1Weighted.single_eq_lpOneAlg_single]
  cases n with
  | zero =>
      rw [taylorReborderingDefect_apply, l1Weighted.eval_single,
        l1Weighted.single_toSeq_same, geomFiber_weight]
      norm_num
  | succ n =>
      rw [taylorReborderingDefect_apply, l1Weighted.eval_single,
        l1Weighted.single_toSeq_of_ne (n + 1) 0 1 (by omega), sub_zero,
        geomFiber_weight]
      simp only [one_mul, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow]
      rw [show (ν : ℝ)⁻¹ * (ν : ℝ) ^ (n + 1) = (ν : ℝ) ^ n by
        field_simp
        ring]
      exact one_le_pow₀ hν

theorem norm_taylorReborderingDefect_le (hν : (1 : ℝ) ≤ (ν : ℝ)) :
    ‖taylorReborderingDefect ν hν‖ ≤ (ν : ℝ)⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr ν.2.le)
    (norm_taylorReborderingDefect_apply_le ν hν)

/-- The re-bordering constant is sharp: the first Taylor mode attains it. -/
theorem norm_taylorReborderingDefect (hν : (1 : ℝ) ≤ (ν : ℝ)) :
    ‖taylorReborderingDefect ν hν‖ = (ν : ℝ)⁻¹ := by
  apply le_antisymm (norm_taylorReborderingDefect_le ν hν)
  have h := (taylorReborderingDefect ν hν).le_opNorm (l1Weighted.single 1 1)
  rw [taylorReborderingDefect_apply, l1Weighted.eval_single,
    l1Weighted.single_toSeq_of_ne 1 0 1 (by omega), sub_zero,
    l1Weighted.norm_single] at h
  norm_num at h
  exact (inv_le_iff_one_le_mul₀ ν.2).2 h

/-- The canonical splitting into the initial value and the coefficients
vanishing at the expansion centre. -/
def taylorSplitBoundary : SplitBoundary ℝ (l1Weighted ν) ℝ where
  trace := (taylorBoundaryCharacter ν).toContinuousLinearMap
  extension := algebraMapCLM ℝ (l1Weighted ν)
  trace_extension r := by
    rw [ContinuousAlgHom.coe_toContinuousLinearMap, coe_algebraMapCLM]
    exact (taylorBoundaryCharacter ν).commutes r

@[simp]
theorem taylorSplitBoundary_trace (a : l1Weighted ν) :
    (taylorSplitBoundary ν).trace a = l1Weighted.toSeq a 0 :=
  taylorBoundaryCharacter_apply ν a

/-- Taylor integration has zero boundary value at the expansion centre. -/
theorem taylorBoundary_shiftDivN (a : l1Weighted ν) :
    (taylorSplitBoundary ν).trace (shiftDivN a) = 0 := by
  rw [taylorSplitBoundary_trace, shiftDivN_zero_mode]

/-- `shiftDivN`, bundled through the common anchored-primitive API. -/
def taylorAnchoredPrimitive :
    l1Weighted ν →L[ℝ] (taylorSplitBoundary ν).trace.ker :=
  (taylorSplitBoundary ν).anchoredPrimitive shiftDivN_CLM

@[simp]
theorem taylorAnchoredPrimitive_coe (a : l1Weighted ν) :
    (taylorAnchoredPrimitive ν a : l1Weighted ν) = shiftDivN a := by
  rw [taylorAnchoredPrimitive, SplitBoundary.anchoredPrimitive,
    ContinuousLinearMap.comp_apply, SplitBoundary.zeroPart_coe]
  rw [shiftDivN_CLM_apply, taylorBoundary_shiftDivN]
  simp

end IVP

end RadiiPolynomial
