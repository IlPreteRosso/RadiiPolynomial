import RadiiPolynomial.Examples.Fourier.Duffing.Polynomial.Algebra

/-!
# Book §10.1 Helmholtz–Duffing on the combined carrier: weight and product

The combined amplitude `m_n = (6/5)^{|n|} (1 + |n|)² = (6/5)^{|n|} polyWeight n` on `ℤ` is the
concrete producer of the services consumed by the combined-carrier certificate:

* the row bound `combRowBound` at `p = q = 2` with the constant `K = 10` of the polynomial
  producer `polyRowBound`, transferred by `RowBound.mul_submul` along the positive
  submultiplicative geometric factor `geoW n = (6/5)^{|n|}` (`geoW_submul`), so the carrier
  `X = ℓ²_m(ℤ; ℂ)` carries the bounded product `combProd = convCLM combRowBound`;
* the self-moderation `combModerate` (`m` is submultiplicative, constant `1`), for the ℓ¹ symbol
  action of the derivative at the centre, and its raw-weight form `combModerate_raw`, for the
  bounded product `X → X → ℓ^∞_m` of the curvature bound;
* the negation invariance `combWeight_neg`, for the conjugate reflection of the reality argument.

The weight comparison with the geometric carrier and the reweighting map live in
`Combined/Analytic.lean`, the only consumer.
-/

open scoped ENNReal NNReal DiscreteConvolution

noncomputable section

namespace FourierDuffing.Combined

open RadiiPolynomial RadiiPolynomial.WeightedLp FourierDuffing.Polynomial

/-! ### The geometric factor -/

/-- The geometric factor `(6/5)^{|n|}`. -/
def geoW (n : ℤ) : ℝ := (6 / 5 : ℝ) ^ n.natAbs

theorem geoW_pos (n : ℤ) : 0 < geoW n := by unfold geoW; positivity

/-- The geometric factor is submultiplicative. -/
theorem geoW_submul (i j : ℤ) : geoW (i + j) ≤ geoW i * geoW j := by
  unfold geoW
  rw [← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (Int.natAbs_add_le i j)

/-! ### The weight and its services -/

/-- **The combined amplitude weight** `m_n = (6/5)^{|n|} (1 + |n|)²`. -/
def combWeight (n : ℤ) : ℝ := (6 / 5 : ℝ) ^ n.natAbs * polyWeight n

instance instPosWeightCombWeight : PosWeight combWeight where
  weight_pos n := mul_pos (geoW_pos n) (PosWeight.weight_pos n)

/-- **The combined carrier** `X = ℓ²_m(ℤ; ℂ)`, `m_n = (6/5)^{|n|} (1 + |n|)²`. -/
abbrev X := WeightedLp ℤ (WeightedScalar ℂ combWeight) 2

/-- **The row bound** of the combined frame at `p = q = 2` with `K = 10`. -/
theorem combRowBound :
    RowBound (FiberTrivialization.weight (E := WeightedScalar ℂ combWeight)) 2 10 := by
  rw [show FiberTrivialization.weight (E := WeightedScalar ℂ combWeight) =
      fun m => polyWeight m * geoW m from
    funext fun m => (WeightedScalar.fiberTrivialization_weight m).trans (mul_comm _ _)]
  have h := polyRowBound
  rw [show FiberTrivialization.weight (E := WeightedScalar ℂ polyWeight) = polyWeight from
    funext WeightedScalar.fiberTrivialization_weight] at h
  exact RowBound.mul_submul (by norm_num) PosWeight.weight_pos geoW_pos geoW_submul h

/-- The combined weight is submultiplicative. -/
theorem combWeight_submul (i j : ℤ) : combWeight (i + j) ≤ combWeight i * combWeight j := by
  have hp : polyWeight (i + j) ≤ polyWeight i * polyWeight j := by
    have h := polyModerate_raw i j
    rwa [one_mul, mul_comm] at h
  refine (mul_le_mul (geoW_submul i j) hp (PosWeight.weight_pos _).le
    (mul_pos (geoW_pos i) (geoW_pos j)).le).trans_eq ?_
  simp only [combWeight, geoW]
  ring

/-- **Self-moderation at the raw weight** (constant `1`), consumed by `Bilateral.prodCLM`. -/
theorem combModerate_raw : Moderate combWeight combWeight 1 :=
  Moderate.of_submul combWeight_submul

/-- **Self-moderation** of the combined frame: `combModerate_raw` in the frame form. -/
theorem combModerate :
    Moderate (FiberTrivialization.weight (E := WeightedScalar ℂ combWeight)) combWeight 1 :=
  Moderate.weightedScalar_iff.mpr combModerate_raw

/-- The combined weight is negation-invariant (the `hw` of `conjReflL`). -/
theorem combWeight_neg : ∀ n : ℤ, combWeight (-n) = combWeight n := fun n => by
  rw [combWeight, combWeight, Int.natAbs_neg, polyWeight_neg]

/-- **The product** of the combined carrier: `convCLM` at the row bound `K = 10`. -/
abbrev combProd : X →L[ℂ] X →L[ℂ] X := convCLM combRowBound

end FourierDuffing.Combined
