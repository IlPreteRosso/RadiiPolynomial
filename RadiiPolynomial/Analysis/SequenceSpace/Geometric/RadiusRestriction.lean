import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Aeval
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.AnalyticExt

/-!
# Restriction between Taylor radii

A Taylor coefficient sequence summable at radius `r` is summable at every
smaller radius `σ`.  The resulting coefficient-preserving map is a contractive
continuous algebra homomorphism.  Evaluation naturality and analytic
extensionality make the restriction injective.
-/

open Filter

noncomputable section

namespace RadiiPolynomial

namespace l1Weighted

private theorem radiusRestrict_power_bound {σ r : PosReal}
    (hσr : (σ : ℝ) ≤ (r : ℝ)) (n : ℕ) :
    ‖(l1Weighted.single 1 1 : l1Weighted σ) ^ n‖ ≤ 1 * (r : ℝ) ^ n := by
  rw [one_mul]
  calc
    ‖(l1Weighted.single 1 1 : l1Weighted σ) ^ n‖
        ≤ ‖(l1Weighted.single 1 1 : l1Weighted σ)‖ ^ n := norm_pow_le _ _
    _ = (σ : ℝ) ^ n := by rw [l1Weighted.norm_single]; norm_num
    _ ≤ (r : ℝ) ^ n := pow_le_pow_left₀ σ.coe_nonneg hσr n

/-- Coefficient-preserving restriction from a Taylor algebra at radius `r` to
one at a smaller radius `σ`. -/
def radiusRestrict {σ r : PosReal} (hσr : (σ : ℝ) ≤ (r : ℝ)) :
    l1Weighted r →A[ℝ] l1Weighted σ :=
  l1Weighted.aeval r (l1Weighted.single 1 1 : l1Weighted σ) 1
    (radiusRestrict_power_bound hσr)

@[simp]
theorem radiusRestrict_gen {σ r : PosReal} (hσr : (σ : ℝ) ≤ (r : ℝ)) :
    radiusRestrict hσr (lpOneAlg.single 1 1) =
      (lpOneAlg.single 1 1 : l1Weighted σ) := by
  rw [radiusRestrict, l1Weighted.aeval_gen]
  exact l1Weighted.single_eq_lpOneAlg_single 1 1

theorem norm_radiusRestrict_apply_le {σ r : PosReal}
    (hσr : (σ : ℝ) ≤ (r : ℝ)) (a : l1Weighted r) :
    ‖radiusRestrict hσr a‖ ≤ ‖a‖ := by
  have h := l1Weighted.norm_aeval_apply_le r
    (l1Weighted.single 1 1 : l1Weighted σ) 1 (radiusRestrict_power_bound hσr) a
  rwa [one_mul] at h

theorem norm_radiusRestrict_le {σ r : PosReal} (hσr : (σ : ℝ) ≤ (r : ℝ)) :
    ‖(radiusRestrict hσr).toContinuousLinearMap‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    simpa using norm_radiusRestrict_apply_le hσr a

/-- The radius restriction has norm exactly one, attained on the unit. -/
theorem norm_radiusRestrict {σ r : PosReal} (hσr : (σ : ℝ) ≤ (r : ℝ)) :
    ‖(radiusRestrict hσr).toContinuousLinearMap‖ = 1 := by
  apply le_antisymm (norm_radiusRestrict_le hσr)
  have h := (radiusRestrict hσr).toContinuousLinearMap.le_opNorm (1 : l1Weighted r)
  rw [ContinuousAlgHom.coe_toContinuousLinearMap, map_one, norm_one, norm_one,
    mul_one] at h
  exact h

/-- Evaluation commutes with coefficient-preserving radius restriction. -/
theorem evalContinuousAlgHom_comp_radiusRestrict {σ r : PosReal}
    (hσr : (σ : ℝ) ≤ (r : ℝ)) (t : ℝ) (htσ : |t| ≤ (σ : ℝ)) :
    (l1Weighted.evalContinuousAlgHom t htσ).comp (radiusRestrict hσr) =
      l1Weighted.evalContinuousAlgHom t (htσ.trans hσr) := by
  apply l1Weighted.algHom_ext r
  rw [ContinuousAlgHom.comp_apply, radiusRestrict_gen,
    l1Weighted.evalContinuousAlgHom_gen, l1Weighted.evalContinuousAlgHom_gen]

@[simp]
theorem radiusRestrict_refl (r : PosReal) :
    radiusRestrict (show (r : ℝ) ≤ (r : ℝ) by rfl) =
      ContinuousAlgHom.id ℝ (l1Weighted r) := by
  apply l1Weighted.algHom_ext r
  rw [radiusRestrict_gen, ContinuousAlgHom.id_apply]

/-- Radius restriction is functorial along a chain of decreasing radii. -/
theorem radiusRestrict_comp {τ σ r : PosReal}
    (hτσ : (τ : ℝ) ≤ (σ : ℝ)) (hσr : (σ : ℝ) ≤ (r : ℝ)) :
    (radiusRestrict hτσ).comp (radiusRestrict hσr) =
      radiusRestrict (hτσ.trans hσr) := by
  apply l1Weighted.algHom_ext r
  rw [ContinuousAlgHom.comp_apply, radiusRestrict_gen, radiusRestrict_gen,
    radiusRestrict_gen]

/-- Restriction to a smaller Taylor radius loses norm control but not
coefficients: agreement after restriction implies agreement at the larger
radius. -/
theorem radiusRestrict_injective {σ r : PosReal}
    (hσr : (σ : ℝ) ≤ (r : ℝ)) : Function.Injective (radiusRestrict hσr) := by
  intro a b hab
  apply l1Weighted.ext_of_eventuallyEq_eval
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) σ.coe_pos] with t ht
  have htσ : |t| ≤ (σ : ℝ) := by
    simpa [Real.dist_eq] using (Metric.mem_ball.mp ht).le
  have hsquare := evalContinuousAlgHom_comp_radiusRestrict hσr t htσ
  have ha := DFunLike.congr_fun hsquare a
  have hb := DFunLike.congr_fun hsquare b
  simp only [ContinuousAlgHom.comp_apply, l1Weighted.evalContinuousAlgHom_apply] at ha hb
  rw [← ha, ← hb, hab]

end l1Weighted

end RadiiPolynomial

end
