import RadiiPolynomial.Core
import RadiiPolynomial.Certification

/-!
# Test (family K): generality witness for the finite-dimensional face, `Z₂` of degree 2

Not part of the default build (imported by no module); build it with
`lake build RadiiPolynomial.Examples.tests.K.QuarticWitness`.

`g x = x⁴ − 2x + 1/3`, `x̄ = 6/5`, `A = g'(x̄)⁻¹ = 125/614` (so `Z₀ = 0`),
`Y₀ = |A g(x̄)| ≤ 13/9210`. With `h = c − x̄`,
`A (g'(c) − g'(x̄)) = (250/307)(h³ + (18/5) h² + (108/25) h)`, whence the ball bound
`Z₂(r) = 1080/307 + (900/307) r + (250/307) r²`, quadratic in `r`. The per-radius face
`enclosure_Icc_poly` with two `decide +kernel` endpoint checks on the length-3 list `csQ`
certifies every radius of `[3/2000, 233/1000]`; the `ℚ` check fails at `234/1000`.
-/

open Metric RadiiPolynomial

namespace Tests.K

/-- The field. -/
noncomputable def g (x : ℝ) : ℝ := x ^ 4 - 2 * x + 1 / 3

/-- Its derivative, as a scalar operator. -/
noncomputable def Dg (x : ℝ) : ℝ →L[ℝ] ℝ := (4 * x ^ 3 - 2) • ContinuousLinearMap.id ℝ ℝ

/-- The approximate inverse `A = g'(6/5)⁻¹`. -/
noncomputable def A : ℝ →L[ℝ] ℝ := (125 / 614 : ℝ) • ContinuousLinearMap.id ℝ ℝ

/-- The `Z₂` coefficient list (length 3), exact rationals. -/
def csQ : List ℚ := [1080 / 307, 900 / 307, 250 / 307]

/-- `Z₂ = Σ csQ[k] r^k` on `ℝ`. -/
noncomputable def Z₂ : ℝ → ℝ := hornerEval (csQ.map (Rat.cast : ℚ → ℝ))

theorem norm_smul_id (k : ℝ) : ‖k • ContinuousLinearMap.id ℝ ℝ‖ = |k| := by
  rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs]

theorem hasFDerivAt_g (x : ℝ) : HasFDerivAt g (Dg x) x := by
  have h := (((hasDerivAt_pow 4 x).sub ((hasDerivAt_id x).const_mul 2)).add_const
    (1 / 3 : ℝ)).hasFDerivAt
  refine h.congr_fderiv ?_
  ext; simp [Dg]

theorem hY₀ : ‖A (g (6 / 5))‖ ≤ 13 / 9210 := by
  simp only [A, g, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, Real.norm_eq_abs]
  rw [abs_le]; constructor <;> norm_num

theorem hZ₀ : ‖ContinuousLinearMap.id ℝ ℝ - A.comp (Dg (6 / 5))‖ ≤ 0 := by
  have h0 : ContinuousLinearMap.id ℝ ℝ - A.comp (Dg (6 / 5)) = 0 := by
    ext; simp [A, Dg]; norm_num
  rw [h0, norm_zero]

theorem hZ₂ (r : ℝ) : ∀ c ∈ closedBall (6 / 5 : ℝ) r,
    ‖A.comp (Dg c - Dg (6 / 5))‖ ≤ Z₂ r * r := fun c hc => by
  have hcomp : A.comp (Dg c - Dg (6 / 5)) =
      ((125 / 614 : ℝ) * ((4 * c ^ 3 - 2) - (4 * (6 / 5) ^ 3 - 2))) •
        ContinuousLinearMap.id ℝ ℝ := by
    ext; simp [A, Dg]; ring
  have hh : |c - 6 / 5| ≤ r := by simpa [Real.dist_eq] using hc
  obtain ⟨hl, hu⟩ := abs_le.1 hh
  rw [hcomp, norm_smul_id, abs_le]
  simp only [Z₂, csQ, List.map_cons, List.map_nil, hornerEval_cons, hornerEval_nil]
  push_cast
  constructor
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ c - 6 / 5 + r)
      (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) (sq_nonneg (c - 6 / 5 - r + 12 / 5)))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (sq_nonneg (c - 6 / 5 + r)))), sq_nonneg r]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r - (c - 6 / 5))
      (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) (sq_nonneg (r + (c - 6 / 5) + 12 / 5)))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (sq_nonneg (r - (c - 6 / 5)))))]

/-- **T5 witness.** Every radius `r ∈ [3/2000, 233/1000]` is certified: `p(r) < 0` and the zero
of `g` in `B̄_r(6/5)` exists, is unique and `A`, `g'` are invertible there.  Degree-2 `Z₂`, closed
by `enclosure_Icc_poly` + two `decide +kernel` checks on the length-3 list `csQ`. -/
theorem quartic_enclosure : ∀ r ∈ Set.Icc (3 / 2000 : ℝ) (233 / 1000),
    radiiPolynomial (13 / 9210) 0 Z₂ r < 0 ∧ Enclosure g Dg A (6 / 5) r :=
  enclosure_Icc_poly (cs := csQ.map (Rat.cast : ℚ → ℝ)) (by norm_num [csQ])
    (fun _ _ => rfl) (by norm_num) hY₀ hZ₀ (fun r _ => hZ₂ r)
    (fun x _ => (hasFDerivAt_g x).hasFDerivWithinAt)
    (radiiPolynomial_neg_of_Q (y := 13 / 9210) (z := 0) (q := 3 / 2000) (by norm_num)
      (by norm_num) rfl (by norm_num) (by decide +kernel))
    (radiiPolynomial_neg_of_Q (y := 13 / 9210) (z := 0) (q := 233 / 1000) (by norm_num)
      (by norm_num) rfl (by norm_num) (by decide +kernel))

theorem quartic_existsUnique : ∀ r ∈ Set.Icc (3 / 2000 : ℝ) (233 / 1000),
    ∃! x ∈ closedBall (6 / 5 : ℝ) r, g x = 0 := fun r hr =>
  (quartic_enclosure r hr).2.existsUnique

/-- The `ℚ` check fails just outside the interval on the right (sharpness of the right end at
the `10⁻³` grid). -/
example : ¬ radiiPolyQ (13 / 9210) 0 csQ (234 / 1000) < 0 := by decide +kernel

end Tests.K
