import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.TailKernel
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Compatibility.WeightedL1Iso
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega

/-!
# The exact `Z₁` tail bound of the Taylor family through the `p = 1` kernel test

The `Z₁` tail operator of the Taylor IVP family is `T_b = π_{>N} ∘ shiftDivN ∘ (b ·)` on
`ℓ¹_ν = lpOneAlg ℕ (ScaledReal ν)`. On the library atoms its coefficients are the tail kernel of
`Operators/TailKernel.lean` with symbol `b`:

  `coeff (T_b δ_j) i = tailKernel N (coeff b) i j = [N < i ∧ j < i] b_{i-1-j} / i`
  (`toRealSeq_tailOp_single`).

At `p = 1` the kernel test is the weighted column bound (`kernelLiftBound_one_iff`), and the
column masses of the tail kernel are the finite sums `colMass` with the infinite remainder
covered by antitonicity (`colSum_tailKernel_of_le`). The column principle on the library carrier
(`opNorm_le_of_kernelLiftBound_one`, `Compatibility/WeightedL1Iso.lean`) then gives
`‖T_b‖ ≤ C` for any `C` above the head columns `j ≤ N` (`norm_tailOp_le_of_colMass`), and its
tail-sum form `tailTsum_shiftDivN_mul_le_of_colMass` is the hypothesis shape of the library face
`StdIVPData.Z₁_le_exact_of_compPoly`.

The computable IVP certificate adapter is in `Certification/IVP/Taylor.lean`.
This Analysis compatibility module imports only Analysis dependencies.
-/

open scoped BigOperators Topology
open Finset

noncomputable section

namespace RadiiPolynomial.WeightedLp

section TaylorTail

variable {ν : PosReal} {N d : ℕ}

/-- The `Z₁` tail operator `π_{>N} ∘ shiftDivN ∘ (b ·)` on `ℓ¹_ν`. -/
abbrev tailOp (N : ℕ) (b : l1Weighted ν) : l1Weighted ν →L[ℝ] l1Weighted ν :=
  (l1Weighted.tailProj_CLM N).comp (shiftDivN_CLM.comp (l1Weighted.leftMul b))

/-- **The atom identity**: on the library atom `δ_j` the tail operator has the coordinates of the
tail kernel, `coeff (T_b δ_j) i = tailKernel N (coeff b) i j`. -/
theorem toRealSeq_tailOp_single (N : ℕ) (b : l1Weighted ν) (j i : ℕ) :
    lpOneAlg.toRealSeq (tailOp N b (lpOneAlg.single j 1)) i =
      tailKernel N (l1Weighted.toSeq b) i j := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, l1Weighted.leftMul_apply,
    shiftDivN_CLM_apply, l1Weighted.tailProj_CLM_apply, ← l1Weighted.toSeq_eq_toRealSeq,
    ← l1Weighted.single_eq_lpOneAlg_single, l1Weighted.coeff_tailProj, tailKernel]
  rcases i with _ | n
  · rw [ite_eq_right (Nat.not_lt_zero N), ite_eq_right fun h => Nat.not_lt_zero N h.1]
  · rw [shiftDivN_succ_mode, l1Weighted.toSeq_mul_single]
    by_cases hN : N < n + 1
    · by_cases hj : j ≤ n
      · rw [ite_eq_left hN, ite_eq_left hj, ite_eq_left ⟨hN, by omega⟩,
          show n + 1 - 1 - j = n - j by omega]
      · rw [ite_eq_left hN, ite_eq_right hj, ite_eq_right (by omega), zero_div]
    · rw [ite_eq_right hN, ite_eq_right fun h => hN h.1]

/-- The frame weight of the geometric fibre is `ν^n`. -/
theorem weight_scaledReal :
    FiberTrivialization.weight (E := ScaledReal ν) = fun n : ℕ => (ν : ℝ) ^ n :=
  funext fun n => WeightedScalar.fiberTrivialization_weight n

/-- The `p = 1` kernel test of the tail kernel on `ℓ¹_ν`, from a bound `C` on the head columns
`j ≤ N` (`colSum_tailKernel_of_le`, frame weight rewritten by `weight_scaledReal`). -/
theorem kernelLiftBound_tailKernel_one (b : l1Weighted ν)
    (hβ : ∀ k, d < k → l1Weighted.toSeq b k = 0) {C : ℝ}
    (hC : ∀ j ≤ N, colMass (symbolMass (ν : ℝ) (l1Weighted.toSeq b)) N d j ≤ C) :
    KernelLiftBound (ScaledReal ν) (ScaledReal ν) 1 (tailKernel N (l1Weighted.toSeq b)) C := by
  have : Fact (0 < (ν : ℝ)) := ⟨ν.2⟩
  have hcol := colSum_tailKernel_of_le (ν := (ν : ℝ)) (N := N) hβ hC
  rw [← weight_scaledReal] at hcol
  exact kernelLiftBound_one_iff.2 ⟨hcol.col_nonneg, hcol⟩

/-- **The `Z₁` tail operator norm from the head columns**: `‖π_{>N} ∘ shiftDivN ∘ (b ·)‖ ≤ C`. -/
theorem norm_tailOp_le_of_colMass (b : l1Weighted ν)
    (hβ : ∀ k, d < k → l1Weighted.toSeq b k = 0) {C : ℝ}
    (hC : ∀ j ≤ N, colMass (symbolMass (ν : ℝ) (l1Weighted.toSeq b)) N d j ≤ C) :
    ‖tailOp N b‖ ≤ C :=
  opNorm_le_of_kernelLiftBound_one (tailOp N b) (kernelLiftBound_tailKernel_one b hβ hC)
    (toRealSeq_tailOp_single N b)

/-- The tail-sum form, the `hDtail` shape of `StdIVPData.Z₁_le_exact_of_compPoly`. -/
theorem tailTsum_shiftDivN_mul_le_of_colMass (b : l1Weighted ν)
    (hβ : ∀ k, d < k → l1Weighted.toSeq b k = 0) {C : ℝ}
    (hC : ∀ j ≤ N, colMass (symbolMass (ν : ℝ) (l1Weighted.toSeq b)) N d j ≤ C)
    (x : l1Weighted ν) :
    ∑' n, |l1Weighted.toSeq (shiftDivN (b * x)) (n + (N + 1))| * (ν : ℝ) ^ (n + (N + 1)) ≤
      C * ‖x‖ := by
  rw [← l1Weighted.norm_tailProj_eq_tailTsum]
  exact ((tailOp N b).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (norm_tailOp_le_of_colMass b hβ hC) (norm_nonneg x))

/-- The rational form: masses `q k ≥ ‖b_k‖ ν^(k+1)` (`k ≤ d`) whose head columns pass the
rational check `colMass q N d j ≤ C` (`j ≤ N`). -/
theorem tailTsum_shiftDivN_mul_le_of_check (b : l1Weighted ν)
    (hβ : ∀ k, d < k → l1Weighted.toSeq b k = 0) (q : ℕ → ℚ)
    (hq : ∀ k ≤ d, symbolMass (ν : ℝ) (l1Weighted.toSeq b) k ≤ q k) {C : ℚ}
    (hC : ∀ j ≤ N, colMass q N d j ≤ C) (x : l1Weighted ν) :
    ∑' n, |l1Weighted.toSeq (shiftDivN (b * x)) (n + (N + 1))| * (ν : ℝ) ^ (n + (N + 1)) ≤
      (C : ℝ) * ‖x‖ :=
  tailTsum_shiftDivN_mul_le_of_colMass b hβ (fun j hj => (colMass_mono hq j).trans
    (by rw [← cast_colMass]; exact_mod_cast hC j hj)) x

end TaylorTail

end RadiiPolynomial.WeightedLp

end
