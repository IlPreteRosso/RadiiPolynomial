import Mathlib.Topology.Algebra.Module.FiniteDimension
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic
import RadiiPolynomial.Operators.Matrix.WeightedNorm
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Finite Matrix-to-CLM Bridge on Weighted `ℓ¹`

This file provides the structural bridge from finite matrices to continuous linear
maps on the finite weighted `ℓ¹` space:

- `FinWeighted.Space ν N`: finite weighted `ℓ¹` via `PiLp 1 (ScaledReal ν ·)`
- `FinWeighted.toVec` / `FinWeighted.ofVec`: identity bridge to `Fin (N+1) → ℝ`
- `FinWeighted.stdBasis`: standard basis with weighted norm `ν^j`
- `FinWeighted.vecEquiv`: the bridge `toVec`/`ofVec` as a linear equivalence
- `FinWeightedMatrix.toWeightedCLM`: matrix action as a CLM on `FinWeighted.Space`, built with
  the explicit bound `finWeightedMatrixNorm`
- `FinWeightedMatrix.toWeightedCLMAlgEquiv`: the same map as an algebra equivalence
  `Matrix ≃ₐ[ℝ] (Space →L[ℝ] Space)` (`toWeightedCLMAlgEquiv_apply`)

The algebra equivalence is purely algebraic: no norm on matrices enters it. The norm identity
for the weighted matrix norm is the separate theorem `finWeightedMatrixNorm_eq_opNorm`
(`Operators/Matrix/OperatorNorm.lean`). The transport lemmas (`toWeightedCLM_one`,
`toWeightedCLM_mul`, `toWeightedCLM_one_sub`, `isUnit_toWeightedCLM_iff`) are its `map_*`
corollaries.
-/

open scoped BigOperators Topology NNReal ENNReal Matrix
open Metric Set Filter ContinuousLinearMap

noncomputable section

namespace RadiiPolynomial

namespace FinWeighted

variable {ν : PosReal} {N : ℕ}

/-- Finite weighted `ℓ¹` space on `Fin (N+1)`. -/
abbrev Space (ν : PosReal) (N : ℕ) := PiLp 1 (fun n : Fin (N + 1) => ScaledReal ν n)

section VecBridge

/-- Extract the underlying real vector. Identity under the hood
(`ScaledReal ν n := ℝ`), but bridges the dependent fiber type to `Fin → ℝ`. -/
def toVec (x : Space ν N) : Fin (N + 1) → ℝ :=
  fun i => ScaledReal.toReal (x i)

/-- Construct a `Space ν N` element from a real vector. -/
def ofVec (v : Fin (N + 1) → ℝ) : Space ν N :=
  WithLp.toLp 1 (fun i => ScaledReal.ofReal (v i))

@[simp] lemma toVec_ofVec (v : Fin (N + 1) → ℝ) : toVec (ofVec v : Space ν N) = v := rfl
@[simp] lemma ofVec_toVec (x : Space ν N) : ofVec (toVec x) = x := rfl

@[simp] lemma toVec_add (x y : Space ν N) : toVec (x + y) = toVec x + toVec y := rfl
@[simp] lemma toVec_smul (c : ℝ) (x : Space ν N) : toVec (c • x) = c • toVec x := rfl

/-- The identity bridge `toVec`/`ofVec` as a linear equivalence. -/
def vecEquiv : Space ν N ≃ₗ[ℝ] (Fin (N + 1) → ℝ) where
  toFun := toVec
  invFun := ofVec
  map_add' := toVec_add
  map_smul' := toVec_smul
  left_inv := ofVec_toVec
  right_inv := toVec_ofVec

end VecBridge

section Norm

lemma norm_eq_sum (x : Space ν N) :
    ‖x‖ = ∑ n : Fin (N + 1), |toVec x n| * (ν : ℝ) ^ (n : ℕ) := by
  rw [PiLp.norm_eq_sum (p := 1) (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one]
  rfl

lemma norm_eq_finl1WeightedNorm (x : Space ν N) :
    ‖x‖ = FiniteWeightedNorm.finl1WeightedNorm ν.toNNReal (toVec x) := by
  rw [norm_eq_sum, FiniteWeightedNorm.finl1WeightedNorm]
  rfl

end Norm

section StdBasis

/-- Standard basis vector `eⱼ`. -/
def stdBasis (j : Fin (N + 1)) : Space ν N :=
  ofVec (fun n => if n = j then 1 else 0)


lemma norm_stdBasis (j : Fin (N + 1)) :
    ‖stdBasis (ν := ν) j‖ = (ν : ℝ) ^ (j : ℕ) := by
  rw [norm_eq_sum]
  simp only [stdBasis, toVec_ofVec]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

end StdBasis

end FinWeighted

namespace FinWeightedMatrix

open FinWeighted

variable {ν : PosReal} {N : ℕ}

/-- Matrix action on finite weighted `ℓ¹` space (internal). -/
private def mulVecWeightedLinear
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    FinWeighted.Space ν N →ₗ[ℝ] FinWeighted.Space ν N where
  toFun x := ofVec (A *ᵥ toVec x)
  map_add' x y := by
    exact congr_arg ofVec (Matrix.mulVec_add A (toVec x) (toVec y))
  map_smul' c x := by
    exact congr_arg ofVec (Matrix.mulVec_smul A c (toVec x))

private lemma mulVecWeightedLinear_norm_le
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (x : FinWeighted.Space ν N) :
    ‖mulVecWeightedLinear A x‖ ≤ FiniteWeightedNorm.finWeightedMatrixNorm ν A * ‖x‖ := by
  change ‖ofVec (A *ᵥ toVec x)‖ ≤ _
  rw [norm_eq_finl1WeightedNorm, toVec_ofVec, norm_eq_finl1WeightedNorm]
  exact FiniteWeightedNorm.finWeightedMatrixNorm_mulVec_le A (toVec x)

/-- Matrix as CLM on finite weighted `ℓ¹`.

Ref: Exercise 2.7.2 (weighted operator norm). -/
def toWeightedCLM
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    FinWeighted.Space ν N →L[ℝ] FinWeighted.Space ν N :=
  LinearMap.mkContinuous (mulVecWeightedLinear A)
    (FiniteWeightedNorm.finWeightedMatrixNorm ν A) (mulVecWeightedLinear_norm_le A)


lemma opNorm_toWeightedCLM_le
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ‖toWeightedCLM (ν := ν) A‖ ≤ FiniteWeightedNorm.finWeightedMatrixNorm ν A := by
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · exact FiniteWeightedNorm.finWeightedMatrixNorm_nonneg (ν := ν) A
  · intro x
    exact mulVecWeightedLinear_norm_le A x

/-- Matrices are the bounded operators on the finite weighted space: the algebra
equivalence `Matrix.toLinAlgEquiv'`, conjugated by `vecEquiv` and followed by
`Module.End.toContinuousLinearMap` (finite dimension). Its forward map is `toWeightedCLM`
(`toWeightedCLMAlgEquiv_apply`); multiplication goes to composition in the same order,
`toWeightedCLM (A * B) = toWeightedCLM A ∘L toWeightedCLM B`. This is an algebra
equivalence, not an isometry statement: no matrix norm enters it. -/
def toWeightedCLMAlgEquiv :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ ≃ₐ[ℝ]
      (FinWeighted.Space ν N →L[ℝ] FinWeighted.Space ν N) :=
  Matrix.toLinAlgEquiv'.trans
    (((vecEquiv (ν := ν) (N := N)).symm.conjAlgEquiv ℝ).trans
      (Module.End.toContinuousLinearMap (FinWeighted.Space ν N)))

/-- The forward map of `toWeightedCLMAlgEquiv` is `toWeightedCLM`. -/
lemma toWeightedCLMAlgEquiv_apply (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    toWeightedCLMAlgEquiv (ν := ν) A = toWeightedCLM A := by
  ext x i; rfl



/-- `toWeightedCLM` sends `1 - M` to `id - toWeightedCLM M`.

Used by Neumann-series invertibility arguments (Proposition 2.7.1). -/
lemma toWeightedCLM_one_sub
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    toWeightedCLM (ν := ν) (1 - M) =
      ContinuousLinearMap.id ℝ (FinWeighted.Space ν N) - toWeightedCLM (ν := ν) M := by
  simp only [← toWeightedCLMAlgEquiv_apply, map_sub, map_one, ContinuousLinearMap.one_def]

/-- A matrix is a unit iff its weighted CLM is (`isUnit_map_iff` along
`toWeightedCLMAlgEquiv`). -/
lemma isUnit_toWeightedCLM_iff (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    IsUnit (toWeightedCLM (ν := ν) M) ↔ IsUnit M := by
  rw [← toWeightedCLMAlgEquiv_apply, isUnit_map_iff]

end FinWeightedMatrix

end RadiiPolynomial

end
