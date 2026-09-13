import RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Joukowski

/-!
# Character obstructions across the Joukowski bridge

Sequence-space layer, cross-geometry. Six negative results about the characters
of the production carriers: no real algebra character of the bilateral carrier
kills the Joukowski generator, so the physical character at `0` has *no* real
continuous extension to the Laurent carrier (the obstruction is algebraic, before
continuity); it does have two distinct complex extensions, at `±I`, so restriction
of complex Laurent characters to the physical subalgebra is not injective.

These are the documentary counterexamples behind the physical spectrum and the
Laurent restriction fibers (`Chebyshev/Spectrum/*`): they pin why the real-character
route is dead and why the complex route is two-to-one.
-/

noncomputable section

namespace RadiiPolynomial.CrossGeometry

open lpOneAlg

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]

/-- No real algebra character of the Laurent carrier vanishes on the
physical Joukowski generator. Continuity is not needed. -/
theorem real_laurent_character_joukowski_ne_zero
    (χ : l1Chebyshev ν →ₐ[ℝ] ℝ) : χ (joukowskiGen ν) ≠ 0 := by
  intro hz
  have hsum : χ (single 1 1) + χ (single (-1) 1) = 0 := by
    simp only [joukowskiGen, map_smul, map_add, smul_eq_mul] at hz
    linarith
  have hinv : χ (single 1 1) * χ (single (-1) 1) = 1 := by
    rw [← map_mul, single_mul_single]
    norm_num [← one_eq_single_zero]
  have hneg : χ (single (-1) 1) = -χ (single 1 1) := by linarith
  rw [hneg] at hinv
  nlinarith [sq_nonneg (χ (single 1 1))]

/-- The actual production physical character at zero cannot be obtained by
restricting a real continuous character of the Laurent carrier. -/
theorem physical_zero_character_has_no_real_extension :
    ¬ ∃ χ : l1Chebyshev ν →A[ℝ] ℝ,
      χ.comp (l1Chebyshev.symmetricSubalgebra ν).valA =
        l1Chebyshev.symmetricEvalCharacter ν 0 (by norm_num) := by
  rintro ⟨χ, hχ⟩
  have hg := DFunLike.congr_fun hχ (joukowskiGenSymm ν)
  have hz : χ (joukowskiGen ν) = 0 := by
    simpa only [ContinuousAlgHom.comp_apply,
      l1Chebyshev.symmetricEvalCharacter_apply,
      joukowskiGenSymm, Subalgebra.valA_apply,
      eval_joukowskiGen ν 0 (by norm_num)] using hg
  exact real_laurent_character_joukowski_ne_zero ν χ.toAlgHom hz

/-- Complex circle evaluation restricts to real physical evaluation. -/
theorem circle_character_restriction (θ : ℝ) :
    (l1Chebyshev.evalLaurentC ν (Complex.exp (θ * Complex.I))
      (l1Chebyshev.evalLaurentC_circle ν θ)).comp
      (l1Chebyshev.symmetricSubalgebra ν).valA =
    (ContinuousAlgHom.mk Complex.ofRealAm Complex.continuous_ofReal).comp
      (l1Chebyshev.symmetricEvalCharacter ν (Real.cos θ)
        (Real.abs_cos_le_one θ)) := by
  ext a
  exact l1Chebyshev.evalLaurentC_circle_eq_eval ν a.val a.property θ

/-- The physical zero character does have a complex-valued Laurent extension. -/
theorem physical_zero_character_has_complex_extension :
    ∃ χ : l1Chebyshev ν →A[ℝ] ℂ,
      χ (single 1 1) = Complex.I ∧
      χ.comp (l1Chebyshev.symmetricSubalgebra ν).valA =
        (ContinuousAlgHom.mk Complex.ofRealAm Complex.continuous_ofReal).comp
          (l1Chebyshev.symmetricEvalCharacter ν 0 (by norm_num)) := by
  refine ⟨l1Chebyshev.evalLaurentC ν (Complex.exp ((Real.pi / 2 : ℝ) * Complex.I))
    (l1Chebyshev.evalLaurentC_circle ν (Real.pi / 2)), ?_, ?_⟩
  · simp [Complex.exp_mul_I]
  · simpa using circle_character_restriction ν (Real.pi / 2)

/-- The other lift of zero under Joukowski is the distinct character at `-I`. -/
theorem physical_zero_character_has_second_complex_extension :
    ∃ χ : l1Chebyshev ν →A[ℝ] ℂ,
      χ (single 1 1) = -Complex.I ∧
      χ.comp (l1Chebyshev.symmetricSubalgebra ν).valA =
        (ContinuousAlgHom.mk Complex.ofRealAm Complex.continuous_ofReal).comp
          (l1Chebyshev.symmetricEvalCharacter ν 0 (by norm_num)) := by
  refine ⟨l1Chebyshev.evalLaurentC ν (Complex.exp ((-(Real.pi / 2) : ℝ) * Complex.I))
    (l1Chebyshev.evalLaurentC_circle ν (-(Real.pi / 2))), ?_, ?_⟩
  · simp [Complex.exp_neg]
  · simpa using circle_character_restriction ν (-(Real.pi / 2))

/-- Restriction of complex Laurent characters to the physical algebra is
not injective: the two characters above zero are different. -/
theorem complex_restriction_not_injective :
    ¬ Function.Injective
      (fun χ : l1Chebyshev ν →A[ℝ] ℂ =>
        χ.comp (l1Chebyshev.symmetricSubalgebra ν).valA) := by
  intro hinj
  obtain ⟨chiP, hplus, hrestplus⟩ := physical_zero_character_has_complex_extension ν
  obtain ⟨chiM, hminus, hrestminus⟩ :=
    physical_zero_character_has_second_complex_extension ν
  have heq := hinj (hrestplus.trans hrestminus.symm)
  have hI : Complex.I = -Complex.I := by
    simpa [hplus, hminus] using DFunLike.congr_fun heq (single 1 1)
  have him := congrArg Complex.im hI
  norm_num at him

end RadiiPolynomial.CrossGeometry
