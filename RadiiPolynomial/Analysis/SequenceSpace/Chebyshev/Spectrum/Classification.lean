import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Spectrum.Basic

/-!
# Classification of the complex characters of the physical Chebyshev algebra

Gelfand layer. Every continuous `ℂ`-valued character of the production carrier
`l1Chebyshev.symmetricSubalgebra ν` is a Laurent evaluation at a point of the closed
annulus `ν⁻¹ ≤ ‖z‖ ≤ ν` (`character_eq_restriction`), the argument running through the
Joukowski preimage and an exponential-growth bound on the symmetric power sums
(`norm_le_of_power_sum_bound`). Two consequences: every physical character is
automatically contractive (`norm_character_apply_le`), and Laurent characters restrict
onto physical characters surjectively over `ℂ` (`restriction_surjective`).

Closes the Chebyshev half of the "no Gelfand theory for this geometry" gap: production
had only the single point-evaluation constructor `l1Chebyshev.symmetricEvalCharacter`.
-/

noncomputable section

namespace RadiiPolynomial.PhysicalSpectrum

open lpOneAlg CrossGeometry

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]

/-- Every complex coordinate has a nonzero Joukowski preimage. -/
theorem exists_joukowski_preimage (w : ℂ) :
    ∃ z : ℂ, z ≠ 0 ∧ joukowski z = w := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) (w ^ 2 - 1)
    (n := 2) (by norm_num)
  have hmul : (w + s) * (w - s) = 1 := by
    linear_combination -hs
  have hz0 : w + s ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  refine ⟨w + s, hz0, ?_⟩
  have hinv : (w + s)⁻¹ = w - s := (eq_inv_of_mul_eq_one_right hmul).symm
  rw [joukowski, hinv]
  ring

/-- Generator values force the entire symmetric-mode recurrence. -/
theorem character_mode_eq_powers (χ : Character ν) (z : ℂ) (hz0 : z ≠ 0)
    (hgen : joukowski z = χ (joukowskiGenSymm ν)) (n : ℕ) :
    χ (mode ν n) = z ^ n + z⁻¹ ^ n := by
  have h1 : χ (mode ν 1) = z + z⁻¹ := by
    rw [mode_one, map_smul, ← hgen, joukowski, Complex.real_smul]
    norm_num
    ring
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using h1
  | more n h0 hsucc =>
    have hm := congrArg χ (mode_recurrence ν n)
    simp only [map_mul, map_add] at hm
    rw [h1, h0, hsucc] at hm
    have hi : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
    linear_combination -hm + (z ^ n + z⁻¹ ^ n) * hi

/-- Exponential growth rules out roots outside the weight radius. This
argument needs only a bound on the symmetric power sums. -/
theorem norm_le_of_power_sum_bound (z : ℂ) (M : ℝ)
    (hbound : ∀ n : ℕ, ‖z ^ n + z⁻¹ ^ n‖ ≤ 2 * M * (ν : ℝ) ^ n) :
    ‖z‖ ≤ (ν : ℝ) := by
  by_contra hnot
  have hlarge : (ν : ℝ) < ‖z‖ := not_le.mp hnot
  have hν : 1 ≤ (ν : ℝ) := Fact.out
  have hz1 : 1 ≤ ‖z‖ := hν.trans hlarge.le
  have hzi : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hz1
  have hq : 1 < ‖z‖ / (ν : ℝ) := (one_lt_div ν.coe_pos).mpr hlarge
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * M + 1) hq
  have htriangle : ‖z ^ n‖ ≤ ‖z ^ n + z⁻¹ ^ n‖ + ‖z⁻¹ ^ n‖ :=
    norm_le_add_norm_add (z ^ n) (z⁻¹ ^ n)
  rw [norm_pow, norm_pow] at htriangle
  have hi : ‖z⁻¹‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hzi
  have hνn : 1 ≤ (ν : ℝ) ^ n := one_le_pow₀ hν
  rw [div_pow, lt_div_iff₀ (pow_pos ν.coe_pos n)] at hn
  nlinarith [hbound n]

/-- Every continuous complex-valued character of the ACTUAL real physical
algebra extends to a complex-valued Laurent character. -/
theorem character_eq_restriction (χ : Character ν) :
    ∃ (z : ℂ) (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)),
      χ = restriction ν z hz := by
  obtain ⟨z, hz0, hgen⟩ := exists_joukowski_preimage (χ (joukowskiGenSymm ν))
  have hbound : ∀ n : ℕ, ‖z ^ n + z⁻¹ ^ n‖ ≤
      2 * ‖χ.toContinuousLinearMap‖ * (ν : ℝ) ^ n := by
    intro n
    rw [← character_mode_eq_powers ν χ z hz0 hgen n]
    have h := χ.toContinuousLinearMap.le_opNorm (mode ν n)
    have hm := mul_le_mul_of_nonneg_left (norm_mode_le ν n)
      (norm_nonneg χ.toContinuousLinearMap)
    exact h.trans (by nlinarith)
  have hzhi := norm_le_of_power_sum_bound ν z ‖χ.toContinuousLinearMap‖ hbound
  have hzihi : ‖z⁻¹‖ ≤ (ν : ℝ) :=
    norm_le_of_power_sum_bound ν z⁻¹ ‖χ.toContinuousLinearMap‖ (by
      intro n
      simpa only [inv_inv, add_comm] using hbound n)
  have hzlo : (ν : ℝ)⁻¹ ≤ ‖z‖ := by
    rw [norm_inv] at hzihi
    exact inv_le_of_inv_le₀ (norm_pos_iff.mpr hz0) hzihi
  refine ⟨z, ⟨hzlo, hzhi⟩, character_ext ν ?_⟩
  rw [restriction_gen, hgen]

/-- All continuous physical characters are contractive; the initial
continuity constant disappears in the spectral classification. -/
theorem norm_character_apply_le (χ : Character ν) (a : Physical ν) : ‖χ a‖ ≤ ‖a‖ := by
  obtain ⟨z, hz, rfl⟩ := character_eq_restriction ν χ
  exact l1Chebyshev.norm_evalLaurentC_apply_le ν z hz a.val

/-- The restriction map from Laurent characters onto physical characters is
surjective over ℂ, although the corresponding real map is not. -/
theorem restriction_surjective :
    Function.Surjective (fun χ : l1Chebyshev ν →A[ℝ] ℂ =>
      χ.comp (l1Chebyshev.symmetricSubalgebra ν).valA) := by
  intro χ
  obtain ⟨z, hz, h⟩ := character_eq_restriction ν χ
  exact ⟨l1Chebyshev.evalLaurentC ν z hz, h.symm⟩

end RadiiPolynomial.PhysicalSpectrum
