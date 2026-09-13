import RadiiPolynomial.Certification.Residual
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Algebra

/-!
# Finite-support completeness for residual certificates

The norm-convergent expansion of a weighted `ℓ¹` element into single modes gives
density of finite-support candidates. Applied to a finite right Bézout identity,
this proves the converse to residual correction without using spectra or
changing the coefficient weight. The result asserts existence, not computability
or rationality of the candidate coefficients.
-/

noncomputable section

namespace RadiiPolynomial.Residual

variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]

/-- Finite-support data are dense in weighted `ℓ¹`, independently of multiplication. -/
theorem dense_lpOneAlg_finiteSupport :
    Dense {a : lpOneAlg M E | Set.Finite {m | a m ≠ 0}} := by
  classical
  intro a
  have h := (lp.hasSum_single (by norm_num) a.toLp).map
    (lpOneAlg.mkAddHom (E := E)) (lpOneAlg.isometry_mk (E := E)).continuous
  refine mem_closure_of_tendsto h (.of_forall fun s => ?_)
  simp only [Function.comp_apply]
  rw [← map_sum]
  refine s.finite_toSet.subset ?_
  intro k hk
  by_contra hks
  apply hk
  change (∑ m ∈ s, lp.single 1 m (a.toLp m)) k = 0
  simp only [lp.coeFn_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun m hm => lp.single_apply_ne _ _ _ (by
    intro he
    exact hks (he ▸ hm))

variable {𝕜 ι : Type*} [NormedField 𝕜] [Fintype ι]
variable [AddMonoid M] [DecidableEq M] [lpAlgRingData 𝕜 M E]
variable [lpOneAlgConvCompat 𝕜 M E]

/-- An exact weighted `ℓ¹` Bézout identity has finite-support candidates with any
prescribed positive residual tolerance. No convergence assumption on the ring is needed. -/
theorem exists_finiteSupport_candidate_of_bezout
    (f b : ι → lpOneAlg M E) (hb : ∑ i, f i * b i = 1) {η : ℝ} (hη : 0 < η) :
    ∃ b₀ : ι → lpOneAlg M E,
      (∀ i, Set.Finite {m | b₀ i m ≠ 0}) ∧ ‖residual f b₀‖ < η := by
  exact exists_dense_candidate_of_bezout dense_lpOneAlg_finiteSupport f b hb hη

variable [HasSummableGeomSeries (lpOneAlg M E)]

/-- A finite right Bézout identity in a weighted `ℓ¹` algebra exists exactly when
some finite-support candidate has residual norm below one. -/
theorem exists_bezout_iff_finiteSupport_certificate (f : ι → lpOneAlg M E) :
    (∃ b : ι → lpOneAlg M E, ∑ i, f i * b i = 1) ↔
      ∃ b₀ : ι → lpOneAlg M E,
        (∀ i, Set.Finite {m | b₀ i m ≠ 0}) ∧ ‖residual f b₀‖ < 1 := by
  exact exists_bezout_iff_dense_certificate dense_lpOneAlg_finiteSupport f

end RadiiPolynomial.Residual
