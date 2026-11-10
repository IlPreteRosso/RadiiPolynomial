import RadiiPolynomial.Examples.Fourier.Duffing.Combined.Analytic
import RadiiPolynomial.Examples.Fourier.Duffing.Analytic

/-!
# Book §10.1 Helmholtz–Duffing: the combined zero is the geometric zero

The combined-carrier certificate (`Combined/Certificate.lean`) and the geometric certificate
(`Duffing/Certificate.lean`) are independent proofs. This leaf, which nothing in the combined
chain imports, compares their chosen zeros:

* `toX₂` sends the combined centre to the geometric centre (`center_transport`) and has norm
  `≤ 1` (`norm_toX₂_le`), so `toX₂ xC` lies within `3/10000` of the geometric centre
  (`image_enclosure`), hence in the geometric uniqueness ball of radius `1/25`
  (`image_large_ball`), and it is a raw zero there (`image_raw_zero`);
* the geometric chosen zero `aTilde` lies in the same ball (`geom_large_ball`), so the geometric
  uniqueness `duffing_l2_existsUnique_r1` gives `toX₂ xC = aTilde` (`identify_zero`), equal
  coefficient families (`identify_coefficients`) and equal named real-time solutions
  (`identify_solution`).

Neither small enclosure is compared: the identification goes through the radius `1/25` only.
-/

noncomputable section

namespace FourierDuffing.Combined.Comparison

open RadiiPolynomial RadiiPolynomial.WeightedLp
open RadiiPolynomial.Fourier.Duffing (duffing forcing)

/-- The combined centre transports to the geometric centre, coefficientwise. -/
theorem center_transport : toX₂ Certificate.abar = FourierDuffing.Certificate.abar :=
  ext_coeff <| funext fun n => by
    rw [coeff_toX₂, Certificate.coeff_abar, FourierDuffing.Certificate.coeff_abar]

/-- The reweighting `toX₂` is contractive. No numerical certificate is used here. -/
theorem norm_toX₂_le : ‖toX₂‖ ≤ 1 := norm_reweightCLM_le _ _

/-- The combined enclosure transports with the same radius `3/10000`. -/
theorem image_enclosure : toX₂ Certificate.xC ∈
    Metric.closedBall FourierDuffing.Certificate.abar (3 / 10000) := by
  rw [mem_closedBall_iff_norm, ← center_transport, ← map_sub]
  have hx := mem_closedBall_iff_norm.mp Certificate.xC_ball
  refine (toX₂.le_opNorm _).trans ((mul_le_mul norm_toX₂_le hx (norm_nonneg _)
    zero_le_one).trans_eq ?_)
  norm_num [Numbers.radiusQ]

/-- The image lies in the geometric certificate's uniqueness ball of radius `1/25`. -/
theorem image_large_ball : toX₂ Certificate.xC ∈
    Metric.closedBall FourierDuffing.Certificate.abar (1 / 25) := by
  apply mem_closedBall_iff_norm.mpr
  exact (mem_closedBall_iff_norm.mp image_enclosure).trans (by norm_num)

/-- The combined raw zero is a raw zero of the geometric map, through `toX₂`. -/
theorem image_raw_zero (n : ℤ) :
    Fourier.Quadratic.rawF (duffing (1 / 10) 4) (forcing 1) (toX₂ Certificate.xC) n = 0 :=
  (Analytic.rawF_eq_toX₂ Certificate.xC n).symm.trans (congrFun Certificate.xC_zero n)

/-- The geometric chosen zero also lies in the ball of radius `1/25`. -/
theorem geom_large_ball : FourierDuffing.Certificate.aTilde ∈
    Metric.closedBall FourierDuffing.Certificate.abar (1 / 25) := by
  apply mem_closedBall_iff_norm.mpr
  exact (mem_closedBall_iff_norm.mp FourierDuffing.Certificate.duffing_analytic_solution.1).trans
    (by norm_num)

/-- **The identification**: the combined certified zero, transported by `toX₂`, is the geometric
chosen zero (uniqueness at radius `1/25`). -/
theorem identify_zero : toX₂ Certificate.xC = FourierDuffing.Certificate.aTilde :=
  FourierDuffing.Certificate.duffing_l2_existsUnique_r1.unique
    ⟨image_large_ball, image_raw_zero⟩
    ⟨geom_large_ball, FourierDuffing.Certificate.duffing_analytic_solution.2.1⟩

/-- The two independently chosen zeros have the same Fourier coefficients. -/
theorem identify_coefficients : coeff Certificate.xC = coeff FourierDuffing.Certificate.aTilde :=
  Analytic.coeff_toX₂_xC.symm.trans (congrArg coeff identify_zero)

/-- Their named real-time solutions agree. -/
theorem identify_solution : Analytic.solution = FourierDuffing.Certificate.solution := by
  unfold Analytic.solution FourierDuffing.Certificate.solution
  rw [identify_coefficients]

end FourierDuffing.Combined.Comparison
