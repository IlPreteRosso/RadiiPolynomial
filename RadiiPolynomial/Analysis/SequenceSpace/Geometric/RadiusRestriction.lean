import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Aeval
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.AnalyticExt

/-!
# Restriction between Taylor radii

A Taylor coefficient sequence summable at radius `r` is summable at every
smaller radius `σ`.  The resulting coefficient-preserving map (built as the
evaluation at the generator, `radiusRestrict_gen`; mode by mode it keeps every coefficient,
`toSeq_radiusRestrict`) is a contractive continuous algebra homomorphism.
Evaluation at a point of the smaller admissible radius commutes with it, in every complete
normed target (`aeval_of_norm_le_comp_radiusRestrict`); with analytic extensionality this
makes the restriction injective.
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
one at a smaller radius `σ`, built as the evaluation `l1Weighted.aeval` at the generator
of the smaller algebra; its mode-by-mode identity is `toSeq_radiusRestrict`. -/
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

/-- Radius restriction keeps every coefficient: the `n`-th coefficient of
`radiusRestrict hσr a` is the `n`-th coefficient of `a`. -/
@[simp]
theorem toSeq_radiusRestrict {σ r : PosReal} (hσr : (σ : ℝ) ≤ (r : ℝ)) (a : l1Weighted r)
    (n : ℕ) : l1Weighted.toSeq (radiusRestrict hσr a) n = l1Weighted.toSeq a n := by
  have h : (l1Weighted.toSeq_CLM (ν := σ) n).comp (radiusRestrict hσr).toContinuousLinearMap
      = l1Weighted.toSeq_CLM (ν := r) n := by
    refine lpOneAlg.continuousLinearMap_ext fun m => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousAlgHom.coe_toContinuousLinearMap,
      ← lpOneAlg.gen_pow_eq_single (𝕜 := ℝ) r m, map_pow, radiusRestrict_gen,
      lpOneAlg.gen_pow_eq_single, lpOneAlg.gen_pow_eq_single, ← single_eq_lpOneAlg_single,
      ← single_eq_lpOneAlg_single]
    show l1Weighted.toSeq (l1Weighted.single m 1 : l1Weighted σ) n
      = l1Weighted.toSeq (l1Weighted.single m 1 : l1Weighted r) n
    simp only [l1Weighted.single_toSeq]
  exact DFunLike.congr_fun h a

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

/-- **Naturality of evaluation along radius restriction.** In every complete normed
`ℝ`-algebra `B` with `‖1‖ = 1`, evaluating at `x` with `‖x‖ ≤ σ` after restricting from
radius `r` to radius `σ` is evaluating at `x` at radius `r`. The real square
`evalContinuousAlgHom_comp_radiusRestrict` is its instance at `B = ℝ`, and the complex square is
its instance at `B = ℂ` (`evalC` is `aeval_of_norm_le` by definition). -/
theorem aeval_of_norm_le_comp_radiusRestrict {B : Type*} [NormedRing B] [NormOneClass B]
    [NormedAlgebra ℝ B] [CompleteSpace B] {σ r : PosReal} (hσr : (σ : ℝ) ≤ (r : ℝ))
    (x : B) (hx : ‖x‖ ≤ (σ : ℝ)) :
    (aeval_of_norm_le σ x hx).comp (radiusRestrict hσr) =
      aeval_of_norm_le r x (hx.trans hσr) :=
  algHom_ext r (by rw [ContinuousAlgHom.comp_apply, radiusRestrict_gen, aeval_of_norm_le_gen,
    aeval_of_norm_le_gen])

/-- Evaluation commutes with coefficient-preserving radius restriction: the real instance of
`aeval_of_norm_le_comp_radiusRestrict`. -/
theorem evalContinuousAlgHom_comp_radiusRestrict {σ r : PosReal}
    (hσr : (σ : ℝ) ≤ (r : ℝ)) (t : ℝ) (htσ : |t| ≤ (σ : ℝ)) :
    (l1Weighted.evalContinuousAlgHom t htσ).comp (radiusRestrict hσr) =
      l1Weighted.evalContinuousAlgHom t (htσ.trans hσr) := by
  have h := aeval_of_norm_le_comp_radiusRestrict hσr t htσ
  rwa [aeval_eq_evalContinuousAlgHom, aeval_eq_evalContinuousAlgHom] at h

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
