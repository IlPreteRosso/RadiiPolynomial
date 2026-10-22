import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum.Classification

/-!
# The filled Bernstein ellipse and its physical characters

`Ellipse ν` is the focal-sum region `‖w - 1‖ + ‖w + 1‖ ≤ ν + ν⁻¹`.
`focal_sum_eq` and `exists_annular_preimage` relate it to the Joukowski image of the
closed annulus. `existsUnique_character` gives the unique physical character at each
ellipse point, and `ellipseCharacter`/`ellipseCharacter_gen` expose that construction.
The degenerate-interval identification at `ν = 1` is not proved here.
-/

noncomputable section

namespace RadiiPolynomial.PhysicalSpectrum

open lpOneAlg CrossGeometry

/-- Focal-distance description of the closed filled Bernstein ellipse.
At `ν = 1` this includes the degenerate ellipse, the interval `[-1,1]` (that identification
is not proved here). -/
abbrev Ellipse (ν : PosReal) :=
  {w : ℂ // ‖w - 1‖ + ‖w + 1‖ ≤ (ν : ℝ) + (ν : ℝ)⁻¹}



private theorem joukowski_sub_one {z : ℂ} (hz : z ≠ 0) :
    joukowski z - 1 = (z - 1) ^ 2 / (2 * z) := by
  unfold joukowski
  field_simp
  ring

private theorem joukowski_add_one {z : ℂ} (hz : z ≠ 0) :
    joukowski z + 1 = (z + 1) ^ 2 / (2 * z) := by
  unfold joukowski
  field_simp
  ring

theorem focal_sum_eq {z : ℂ} (hz : z ≠ 0) :
    ‖joukowski z - 1‖ + ‖joukowski z + 1‖ = ‖z‖ + ‖z‖⁻¹ := by
  have hz' : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have h2 : ‖(2 : ℂ) * z‖ = 2 * ‖z‖ := by rw [norm_mul]; norm_num
  rw [joukowski_sub_one hz, joukowski_add_one hz, norm_div, norm_div,
    norm_pow, norm_pow, h2]
  have hpar := parallelogram_law_with_norm ℝ z (1 : ℂ)
  rw [norm_one] at hpar
  field_simp
  linarith

private theorem annulus_of_focal_le {t : ℝ} (ht : 0 < t) {ν : ℝ} (hν : 1 ≤ ν)
    (h : t + t⁻¹ ≤ ν + ν⁻¹) : ν⁻¹ ≤ t ∧ t ≤ ν := by
  have hν0 : (0 : ℝ) < ν := lt_of_lt_of_le one_pos hν
  have hti : t * t⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt ht)
  have hνi : ν * ν⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hν0)
  have hquad : (t - ν) * (t - ν⁻¹) ≤ 0 := by
    have h1 := mul_le_mul_of_nonneg_left h ht.le
    nlinarith
  have hcmp : ν⁻¹ ≤ ν := by nlinarith
  constructor
  · by_contra hlt
    have h1 : t < ν⁻¹ := not_le.mp hlt
    have h2 : t - ν < 0 := by linarith
    have h3 : t - ν⁻¹ < 0 := by linarith
    nlinarith
  · by_contra hlt
    have h1 : ν < t := not_le.mp hlt
    have h2 : 0 < t - ν := by linarith
    have h3 : 0 < t - ν⁻¹ := by linarith
    nlinarith

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]


theorem exists_annular_preimage (w : Ellipse ν) :
    ∃ (z : ℂ) (_hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)), joukowski z = w.val := by
  obtain ⟨z, hz0, hj⟩ := exists_joukowski_preimage w.val
  refine ⟨z, ?_, hj⟩
  apply annulus_of_focal_le (norm_pos_iff.mpr hz0) Fact.out
  rw [← focal_sum_eq hz0, hj]
  exact w.property


/-- Every point of the filled ellipse occurs as the normalized coordinate
of exactly one continuous complex-valued physical character. -/
theorem existsUnique_character (w : Ellipse ν) :
    ∃! χ : Character ν, χ (joukowskiGenSymm ν) = w.val := by
  obtain ⟨z, hz, hj⟩ := exists_annular_preimage ν w
  refine ⟨restriction ν z hz, ?_, ?_⟩
  · change restriction ν z hz (joukowskiGenSymm ν) = w.val
    rw [restriction_gen, hj]
  · intro χ hχ
    apply character_ext ν
    rw [hχ, restriction_gen, hj]


/-- Choice only selects a quadratic preimage; uniqueness makes the resulting
physical character independent of that choice. -/
def ellipseCharacter (w : Ellipse ν) : Character ν :=
  (existsUnique_character ν w).exists.choose

@[simp] theorem ellipseCharacter_gen (w : Ellipse ν) :
    ellipseCharacter ν w (joukowskiGenSymm ν) = w.val :=
  (existsUnique_character ν w).exists.choose_spec




end RadiiPolynomial.PhysicalSpectrum
