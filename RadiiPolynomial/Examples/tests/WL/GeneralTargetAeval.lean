import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Aeval

/-! Evaluation into a general normed algebra, without a norm-one hypothesis. -/

noncomputable section

open RadiiPolynomial

namespace Tests.WL.GeneralTargetAeval

private theorem powerBound {B : Type*} [NormedRing B] (ν : PosReal)
    {x : B} (hx : ‖x‖ ≤ (ν : ℝ)) (n : ℕ) :
    ‖x ^ n‖ ≤ max 1 ‖(1 : B)‖ * (ν : ℝ) ^ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [pow_zero, pow_zero, mul_one]
    exact le_max_right _ _
  · exact (norm_pow_le' x hn).trans <| (pow_le_pow_left₀ (norm_nonneg x) hx n).trans <|
      le_mul_of_one_le_left (pow_pos ν.coe_pos n).le (le_max_left _ _)

variable {𝕜 : Type*} [NormedField 𝕜] (ν : PosReal)
variable {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B]

example (x : B) (hx : ‖x‖ ≤ (ν : ℝ)) :
    lpOneAlg.geomAeval 𝕜 ν x (max 1 ‖(1 : B)‖) (powerBound ν hx)
      (lpOneAlg.single 1 1) = x :=
  lpOneAlg.geomAeval_gen 𝕜 ν x _ _

example (x : B) (hx : ‖x‖ ≤ (ν : ℝ)) (a : lpOneAlg ℕ (geomFiber 𝕜 ν)) :
    ‖lpOneAlg.geomAeval 𝕜 ν x (max 1 ‖(1 : B)‖) (powerBound ν hx) a‖ ≤
      max 1 ‖(1 : B)‖ * ‖a‖ :=
  lpOneAlg.norm_liftAlgHom_apply_le (fun n => x ^ n) _
    (lpOneAlg.pow_le_geomFiber_weight 𝕜 ν x _ (powerBound ν hx))
    (pow_zero x) (pow_add x) a

end Tests.WL.GeneralTargetAeval
