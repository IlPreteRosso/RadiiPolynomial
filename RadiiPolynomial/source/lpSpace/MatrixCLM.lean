import RadiiPolynomial.source.lpSpace.lpWeighted
import RadiiPolynomial.source.lpSpace.FiniteWeightedNorm
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
- `FinWeightedMatrix.toWeightedCLM`: matrix action as a CLM on `FinWeighted.Space`

Transport lemmas (`toWeightedCLM_one`, `toWeightedCLM_mul`, `toWeightedCLM_one_sub`)
connect matrix algebra to CLM algebra.
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
@[simp] lemma toVec_apply (x : Space ν N) (i : Fin (N + 1)) :
    toVec x i = ScaledReal.toReal (x i) := rfl

@[simp] lemma toVec_add (x y : Space ν N) : toVec (x + y) = toVec x + toVec y := rfl
@[simp] lemma toVec_smul (c : ℝ) (x : Space ν N) : toVec (c • x) = c • toVec x := rfl
@[simp] lemma ofVec_add (u v : Fin (N + 1) → ℝ) :
    ofVec (u + v) = (ofVec u : Space ν N) + ofVec v := rfl
@[simp] lemma ofVec_sub (u v : Fin (N + 1) → ℝ) :
    ofVec (u - v) = (ofVec u : Space ν N) - ofVec v := rfl
@[simp] lemma ofVec_smul (c : ℝ) (v : Fin (N + 1) → ℝ) :
    ofVec (c • v) = c • (ofVec v : Space ν N) := rfl

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

@[simp]
lemma stdBasis_apply_self (j : Fin (N + 1)) :
    stdBasis (ν := ν) j j = 1 := by
  simp [stdBasis, ofVec]

@[simp]
lemma stdBasis_apply_ne (i j : Fin (N + 1)) (h : i ≠ j) :
    stdBasis (ν := ν) j i = 0 := by
  simp [stdBasis, ofVec, h]

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

/-- The CLM acts as matrix–vector multiplication on the underlying real vectors. -/
@[simp] lemma toVec_toWeightedCLM
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (x : FinWeighted.Space ν N) :
    toVec (toWeightedCLM (ν := ν) A x) = A *ᵥ toVec x := rfl

lemma opNorm_toWeightedCLM_le
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ‖toWeightedCLM (ν := ν) A‖ ≤ FiniteWeightedNorm.finWeightedMatrixNorm ν A := by
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · exact FiniteWeightedNorm.finWeightedMatrixNorm_nonneg (ν := ν) A
  · intro x
    exact mulVecWeightedLinear_norm_le A x

lemma toWeightedCLM_one :
    toWeightedCLM (ν := ν) (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) =
      ContinuousLinearMap.id ℝ (FinWeighted.Space ν N) := by
  ext x i
  change ((1 : Matrix _ _ ℝ) *ᵥ toVec x) i = (toVec x) i
  rw [Matrix.one_mulVec]

lemma toWeightedCLM_mul
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    toWeightedCLM (ν := ν) (A * B) =
      (toWeightedCLM (ν := ν) A).comp (toWeightedCLM (ν := ν) B) := by
  ext x i
  change ((A * B) *ᵥ toVec x) i = (A *ᵥ (B *ᵥ toVec x)) i
  rw [Matrix.mulVec_mulVec]

/-- `toWeightedCLM` sends `1 - M` to `id - toWeightedCLM M`.

Used by Neumann-series invertibility arguments (Proposition 2.7.1). -/
lemma toWeightedCLM_one_sub
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    toWeightedCLM (ν := ν) (1 - M) =
      ContinuousLinearMap.id ℝ (FinWeighted.Space ν N) - toWeightedCLM (ν := ν) M := by
  ext x i
  change ((1 - M) *ᵥ toVec x) i = (toVec x - M *ᵥ toVec x) i
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]

end FinWeightedMatrix

end RadiiPolynomial

end
