import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum.Classification

/-!
# The character space as the filled Bernstein ellipse

Parameterization layer. `Ellipse ν` is the closed filled Bernstein ellipse in
focal-sum form `‖w - 1‖ + ‖w + 1‖ ≤ ν + ν⁻¹` (degenerating to `[-1,1]` at `ν = 1`);
`focal_sum_eq` identifies it as the Joukowski image of the closed annulus, by the
parallelogram law. Every point of the ellipse is the normalized coordinate `χ ↦ χ(g)`
of exactly one continuous complex character (`existsUnique_character`,
`exists_character_iff`), which packages the classification into the set-level
bijection `characterEquivEllipse : Character ν ≃ Ellipse ν`.

Closes the "no packaged ellipse classification" half of the spectrum gap; the
topological upgrade is in `Spectrum/Topology.lean`.
-/

noncomputable section

namespace RadiiPolynomial.PhysicalSpectrum

open lpOneAlg CrossGeometry

/-- Focal-distance description of the closed filled Bernstein ellipse.
At `ν = 1` this includes the degenerate ellipse, the interval `[-1,1]`. -/
abbrev Ellipse (ν : PosReal) :=
  {w : ℂ // ‖w - 1‖ + ‖w + 1‖ ≤ (ν : ℝ) + (ν : ℝ)⁻¹}

/-- The focal-sum threshold is twice the semi-major axis of `CrossGeometry.semiMajor`,
so this ellipse is the one of `CrossGeometry/Joukowski.lean` in axis form. -/
theorem two_mul_semiMajor (ν : PosReal) : 2 * semiMajor ν = (ν : ℝ) + (ν : ℝ)⁻¹ := by
  unfold semiMajor
  ring

theorem focal_sum_le_iff_le_two_mul_semiMajor (ν : PosReal) (w : ℂ) :
    ‖w - 1‖ + ‖w + 1‖ ≤ (ν : ℝ) + (ν : ℝ)⁻¹ ↔ ‖w - 1‖ + ‖w + 1‖ ≤ 2 * semiMajor ν := by
  rw [two_mul_semiMajor]

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

private theorem focal_le_of_annulus {t ν : ℝ} (ht : 0 < t) (hν0 : 0 < ν)
    (h1 : ν⁻¹ ≤ t) (h2 : t ≤ ν) : t + t⁻¹ ≤ ν + ν⁻¹ := by
  have hkey : 0 ≤ (ν - t) * (t * ν - 1) := by
    have h3 : (1 : ℝ) ≤ t * ν := by
      have h4 := mul_le_mul_of_nonneg_right h1 hν0.le
      rwa [inv_mul_cancel₀ (ne_of_gt hν0)] at h4
    exact mul_nonneg (by linarith) (by linarith)
  have hexpand : (ν + ν⁻¹) - (t + t⁻¹) = (ν - t) * (t * ν - 1) / (t * ν) := by
    field_simp
    ring
  have hnn : 0 ≤ (ν - t) * (t * ν - 1) / (t * ν) :=
    div_nonneg hkey (mul_pos ht hν0).le
  linarith [hexpand ▸ hnn]

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]

omit [Fact (1 ≤ (ν : ℝ))] in
theorem joukowski_mem_ellipse {z : ℂ}
    (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)) :
    ‖joukowski z - 1‖ + ‖joukowski z + 1‖ ≤ (ν : ℝ) + (ν : ℝ)⁻¹ := by
  have hz0 := lpOneAlg.ne_zero_of_annulus ν hz
  rw [focal_sum_eq hz0]
  exact focal_le_of_annulus (norm_pos_iff.mpr hz0) ν.coe_pos hz.1 hz.2

theorem exists_annular_preimage (w : Ellipse ν) :
    ∃ (z : ℂ) (_hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)), joukowski z = w.val := by
  obtain ⟨z, hz0, hj⟩ := exists_joukowski_preimage w.val
  refine ⟨z, ?_, hj⟩
  apply annulus_of_focal_le (norm_pos_iff.mpr hz0) Fact.out
  rw [← focal_sum_eq hz0, hj]
  exact w.property

/-- The normalized physical coordinate of any character lies in the ellipse. -/
theorem character_gen_mem_ellipse (χ : Character ν) :
    ‖χ (joukowskiGenSymm ν) - 1‖ + ‖χ (joukowskiGenSymm ν) + 1‖ ≤
      (ν : ℝ) + (ν : ℝ)⁻¹ := by
  obtain ⟨z, hz, rfl⟩ := character_eq_restriction ν χ
  rw [restriction_gen]
  exact joukowski_mem_ellipse ν hz

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

/-- Exact classification criterion on the original real carrier. -/
theorem exists_character_iff (w : ℂ) :
    (∃ χ : Character ν, χ (joukowskiGenSymm ν) = w) ↔
      ‖w - 1‖ + ‖w + 1‖ ≤ (ν : ℝ) + (ν : ℝ)⁻¹ := by
  constructor
  · rintro ⟨χ, rfl⟩
    exact character_gen_mem_ellipse ν χ
  · intro hw
    exact (existsUnique_character ν ⟨w, hw⟩).exists

/-- Choice only selects a quadratic preimage; uniqueness makes the resulting
physical character independent of that choice. -/
def ellipseCharacter (w : Ellipse ν) : Character ν :=
  (existsUnique_character ν w).exists.choose

@[simp] theorem ellipseCharacter_gen (w : Ellipse ν) :
    ellipseCharacter ν w (joukowskiGenSymm ν) = w.val :=
  (existsUnique_character ν w).exists.choose_spec

/-- A set-level equivalence, with actual characters and normalized physical
coordinates. No topology or complexified algebra is implicit in this type. -/
def characterEquivEllipse : Character ν ≃ Ellipse ν where
  toFun χ := ⟨χ (joukowskiGenSymm ν), character_gen_mem_ellipse ν χ⟩
  invFun := ellipseCharacter ν
  left_inv _χ := character_ext ν (ellipseCharacter_gen ν _)
  right_inv w := Subtype.ext (ellipseCharacter_gen ν w)

@[simp] theorem characterEquivEllipse_apply (χ : Character ν) :
    (characterEquivEllipse ν χ).val = χ (joukowskiGenSymm ν) := rfl

/-- The exact quotient parameter of annular Laurent evaluation. -/
@[simp] theorem characterEquivEllipse_restriction (z : ℂ)
    (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)) :
    (characterEquivEllipse ν (restriction ν z hz)).val = joukowski z :=
  restriction_gen ν z hz

end RadiiPolynomial.PhysicalSpectrum
