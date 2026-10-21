import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Galerkin

/-!
# Test (family GC): the Galerkin carrier at `N = 1`

Not part of the default build (imported by no module); build it with
`lake build RadiiPolynomial.Examples.tests.GC.NOne`.

Witnesses on the smallest nontrivial carrier `FνN ν 1`:

* `norm_mk_single_one`: the weighted norm charges mode `1` with `2 ν`, where the Pi sup-norm
  charges `1` (the carrier is a distinct normed space).
* The product must be formed in the flip-fixed algebra before projecting: `πN` is not
  multiplicative. With `u = z + z⁻¹` (`zz`), `πN(u³) = (0, 3)` (`πN_cube_zz`), while projecting after
  the first product gives `πN(ιN(πN(u²)) · u) = (0, 2)` (`πN_truncated_zz`, `πN_not_multiplicative`).
* `Icc_one`: the window `[-1, 1]` as an explicit finset, by `decide +kernel`.
-/

noncomputable section

namespace Tests.GC

open RadiiPolynomial RadiiPolynomial.Galerkin l1Chebyshev

theorem norm_mk_single_one {ν : PosReal} :
    ‖(FνN.mk (Pi.single 1 1) : FνN ν 1)‖ = 2 * (ν : ℝ) ∧ ‖(Pi.single 1 1 : Fin 2 → ℝ)‖ = 1 := by
  refine ⟨?_, by rw [Pi.norm_single, norm_one]⟩
  rw [FνN.norm_def]
  change (∑ k : Fin 2, |((Pi.single 1 1 : Fin 2 → ℝ)) k| * wt ν k) = 2 * (ν : ℝ)
  rw [Finset.sum_eq_single (1 : Fin 2)
    (fun j _ hj => by rw [Pi.single_eq_of_ne hj, abs_zero, zero_mul])
    (fun h => absurd (Finset.mem_univ (1 : Fin 2)) h), Pi.single_eq_same]
  simp [wt]

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- `z + z⁻¹` stored on `N = 1`. -/
def zz : FνN ν 1 := FνN.mk ![0, 1]

/-- The window `[-1, 1]`, kernel-checked. -/
theorem Icc_one : Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by
  decide +kernel

/-- The product must be formed in the flip-fixed algebra before projecting: `πN` is not
multiplicative.  With `u = z + z⁻¹` and `N = 1`, `πN(u³) = (0, 3)`, while projecting after
the first product gives `πN(ιN(πN(u²)) · u) = (0, 2)`. -/
theorem πN_cube_zz :
    (πN (ιN (zz (ν := ν)) * ιN zz * ιN zz : symmetricSubalgebra ν) : FνN ν 1) = FνN.mk ![0, 3] := by
  refine FνN.ext fun k => ?_
  rw [πN_apply]
  change toSeq (((ιN (zz (ν := ν)) * ιN zz : symmetricSubalgebra ν) : l1Chebyshev ν) *
    (ιN (zz (ν := ν)) : l1Chebyshev ν)) _ = _
  rw [toSeq_mul_eq_finsum _ _ _ (Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)) (fun i hi => by
    rw [ιN_toSeq]; exact evenLift_eq_zero_of_not_mem _ hi)]
  simp only [toSeq_mul_ιN, ιN_toSeq, Icc_one]
  fin_cases k <;> norm_num [evenLift, zz, FνN.mk, Finset.sum_insert, Finset.sum_singleton]

/-- `πN(u²) = (2, 0)`: the mode `2` of `u² = z² + 2 + z⁻²` is cut. -/
theorem πN_sq_zz :
    (πN (ιN (zz (ν := ν)) * ιN zz : symmetricSubalgebra ν) : FνN ν 1) = FνN.mk ![2, 0] := by
  refine FνN.ext fun k => ?_
  rw [πN_apply, toSeq_mul_ιN, Icc_one]
  fin_cases k <;> norm_num [evenLift, zz, FνN.mk, Finset.sum_filter, Finset.sum_insert]

theorem πN_truncated_zz :
    (πN (ιN (πN (N := 1) (ιN (zz (ν := ν)) * ιN zz : symmetricSubalgebra ν)) * ιN zz :
      symmetricSubalgebra ν) : FνN ν 1) = FνN.mk ![0, 2] := by
  rw [πN_sq_zz]
  refine FνN.ext fun k => ?_
  rw [πN_apply, toSeq_mul_ιN, Icc_one]
  fin_cases k <;> norm_num [evenLift, zz, FνN.mk, Finset.sum_filter, Finset.sum_insert]

theorem πN_not_multiplicative :
    (πN (ιN (zz (ν := ν)) * ιN zz * ιN zz : symmetricSubalgebra ν) : FνN ν 1) ≠
      πN (ιN (πN (N := 1) (ιN (zz (ν := ν)) * ιN zz : symmetricSubalgebra ν)) * ιN zz :
        symmetricSubalgebra ν) := by
  rw [πN_cube_zz, πN_truncated_zz]
  intro h
  have := congrFun h 1
  simp [FνN.mk] at this

end Tests.GC

end
