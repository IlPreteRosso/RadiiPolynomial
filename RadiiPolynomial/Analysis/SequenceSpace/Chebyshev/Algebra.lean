import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Scalar
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Multilinear
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Chebyshev ℓ¹ Banach Algebra

`l1Chebyshev ν = lpOneAlg ℤ (ScaledRealZ ν)` — ℤ-indexed sequences with
bilateral weighted norm `∑|a_k|·ν^{|k|}` and convolution product.

Ring and algebra instances flow from `lpOneAlg` + the standard frame of `WeightedScalar`
(`SubMulWeightBase` → `WeightedScalar.instLpOneAlgWeightMul` → `instConvCompatOfWeightMul`)
via the generic instances in `WeightedL1/ScalarInstances.lean`.
-/

open scoped BigOperators Topology

noncomputable section

namespace RadiiPolynomial

/-! ### l1Chebyshev: the Chebyshev Banach algebra -/

/-- Chebyshev ℓ¹ Banach algebra: ℤ-indexed sequences with norm `∑|a_k|·ν^{|k|}`
and bilateral Cauchy product. All instances from `lpOneAlg` with the standard frame and its
submultiplicative weight (`SubMulWeightBase`). -/
abbrev l1Chebyshev (ν : PosReal) := lpOneAlg ℤ (ScaledRealZ ν)

namespace l1Chebyshev

variable {ν : PosReal}

/-- Extract underlying ℝ-valued sequence. -/
def toSeq (f : l1Chebyshev ν) : ℤ → ℝ := lpOneAlg.toRealSeq f

/-- The Chebyshev coefficient map is the generic `lpOneAlg.toRealSeq` (definitionally). -/
lemma toSeq_eq_toRealSeq (a : l1Chebyshev ν) : toSeq a = lpOneAlg.toRealSeq a := rfl

@[simp] lemma toSeq_add (f g : l1Chebyshev ν) (m : ℤ) :
    toSeq (f + g) m = toSeq f m + toSeq g m :=
  congr_fun (lpOneAlg.toRealSeq_add f g) m

-- Instances automatically available from lpOneAlg + the standard frame (SubMulWeightBase):
-- NormedAddCommGroup, Ring, NormedRing (always)
-- CommRing, NormedCommRing (ℤ is AddCommGroup ✓)
-- NormedSpace ℝ, Algebra ℝ, NormedAlgebra ℝ (ScaledRealZ has NormedSpace ℝ ✓)
-- All require [Fact (1 ≤ (ν : ℝ))] for Ring (via SubMulWeightBase: submul on ℤ needs ν ≥ 1)

-- Verify the key instances synthesize:
example [Fact (1 ≤ (ν : ℝ))] : NormedRing (l1Chebyshev ν) := inferInstance
example [Fact (1 ≤ (ν : ℝ))] : NormedCommRing (l1Chebyshev ν) := inferInstance
example [Fact (1 ≤ (ν : ℝ))] : NormedAlgebra ℝ (l1Chebyshev ν) := inferInstance

/-! ### toSeq bridges -/

@[simp] lemma toSeq_zero (m : ℤ) : toSeq (0 : l1Chebyshev ν) m = 0 :=
  congr_fun lpOneAlg.toRealSeq_zero m

@[simp] lemma toSeq_neg (f : l1Chebyshev ν) (m : ℤ) :
    toSeq (-f) m = -(toSeq f m) :=
  congr_fun (lpOneAlg.toRealSeq_neg f) m

@[simp] lemma toSeq_sub (f g : l1Chebyshev ν) (m : ℤ) :
    toSeq (f - g) m = toSeq f m - toSeq g m :=
  congr_fun (lpOneAlg.toRealSeq_sub f g) m

@[simp] lemma toSeq_smul (r : ℝ) (f : l1Chebyshev ν) (m : ℤ) :
    toSeq (r • f) m = r * toSeq f m :=
  congr_fun (lpOneAlg.toRealSeq_smul r f) m

/-- Extensionality split along `ℤ = ℕ ⊔ negSucc ℕ`: two elements with the same coefficients
at the nonnegative and at the strictly negative modes are equal. -/
theorem ext_natCast_negSucc {f g : l1Chebyshev ν}
    (hn : ∀ n : ℕ, toSeq f n = toSeq g n)
    (hm : ∀ m : ℕ, toSeq f (Int.negSucc m) = toSeq g (Int.negSucc m)) : f = g :=
  lpOneAlg.ext_toRealSeq (funext fun k => by
    cases k with
    | ofNat n => exact hn n
    | negSucc m => exact hm m)

/-- The fiber norm in `toSeq` form: `‖a k‖ = |toSeq a k| · ν^{|k|}`. -/
lemma norm_fiber (a : l1Chebyshev ν) (k : ℤ) :
    ‖a k‖ = |toSeq a k| * (ν : ℝ) ^ k.natAbs := by
  rw [lpOneAlg.norm_eq_abs_toReal_mul_weight]
  simp [Real.norm_eq_abs, toSeq]

end l1Chebyshev

/-! ### Nonnegative modes -/

/-- Norm sums restricted to nonnegative modes are summable. -/
lemma summable_norm_natCast {ν : PosReal} (c : l1Chebyshev ν) :
    Summable (fun n : ℕ => ‖c (↑n : ℤ)‖) :=
  (lpOneAlg.summable_norm c).comp_injective Nat.cast_injective

/-- Fiber norm at a nonnegative mode: `‖c_m‖ = |c_m|·ν^m` (`l1Chebyshev.norm_fiber` at `k = m`). -/
lemma norm_fiber_natCast {ν : PosReal} (c : l1Chebyshev ν) (m : ℕ) :
    ‖c (↑m : ℤ)‖ = |l1Chebyshev.toSeq c ↑m| * (ν : ℝ) ^ m := by
  rw [l1Chebyshev.norm_fiber, Int.natAbs_natCast]

namespace l1Chebyshev

variable {ν : PosReal}

/-! ### Singles -/

/-- The element with value `x` at mode `j` and `0` elsewhere. -/
abbrev single (j : ℤ) (x : ℝ) : l1Chebyshev ν := lpOneAlg.single j x

lemma toSeq_single (j : ℤ) (x : ℝ) (k : ℤ) :
    toSeq (single (ν := ν) j x) k = if k = j then x else 0 :=
  lpOneAlg.toRealSeq_single j x k

lemma norm_single (j : ℤ) (x : ℝ) :
    ‖(single (ν := ν) j x)‖ = |x| * (ν : ℝ) ^ j.natAbs := by
  rw [lpOneAlg.norm_single, WeightedScalar.fiberTrivialization_weight, Real.norm_eq_abs]

lemma single_smul (j : ℤ) (x : ℝ) :
    single (ν := ν) j x = x • single j 1 :=
  lpOneAlg.single_smul j x

/-- Every element is the norm-convergent sum of its modes. -/
lemma hasSum_single (h : l1Chebyshev ν) :
    HasSum (fun m : ℤ => single (ν := ν) m (toSeq h m)) h :=
  lpOneAlg.hasSum_single h

/-- Mode expansion pushed through a continuous linear map. -/
lemma hasSum_single_mapCLM {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (W : l1Chebyshev ν →L[ℝ] F) (h : l1Chebyshev ν) :
    HasSum (fun m : ℤ => W (single m (toSeq h m))) (W h) :=
  lpOneAlg.hasSum_single_mapCLM W h

/-! ### Column-norm bounds (`ν^{|m|}` weights) -/

/-- **Column-norm bound.** Out of `l1Chebyshev`, an operator norm is controlled
by the weighted column norms: `‖W (single m 1)‖ ≤ C·ν^{|m|}` for all `m` gives
`‖W h‖ ≤ C‖h‖`. -/
lemma norm_le_of_cols {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (W : l1Chebyshev ν →L[ℝ] F) {C : ℝ}
    (hcol : ∀ m : ℤ, ‖W (single m 1)‖ ≤ C * (ν : ℝ) ^ m.natAbs)
    (h : l1Chebyshev ν) : ‖W h‖ ≤ C * ‖h‖ :=
  lpOneAlg.norm_le_of_cols W
    (fun m => by
      rw [WeightedScalar.fiberTrivialization_weight]
      exact hcol m) h

/-- **Finite-part column-norm bound** over the nonnegative output modes
`0..N`: columns bounded by `ε·ν^{|m|}` give `∑_{n ≤ N} ‖(W h)(n)‖ ≤ ε‖h‖`. -/
lemma finsum_norm_le_of_cols (W : l1Chebyshev ν →L[ℝ] l1Chebyshev ν) (N : ℕ) {ε : ℝ}
    (hcol : ∀ m : ℤ, ∑ n : Fin (N + 1), ‖(W (single m 1)) ((n : ℕ) : ℤ)‖
      ≤ ε * (ν : ℝ) ^ m.natAbs)
    (h : l1Chebyshev ν) :
    ∑ n : Fin (N + 1), ‖(W h) ((n : ℕ) : ℤ)‖ ≤ ε * ‖h‖ :=
  lpOneAlg.finsum_norm_le_of_cols W Finset.univ (fun n : Fin (N + 1) => ((n : ℕ) : ℤ))
    (fun m => by
      rw [WeightedScalar.fiberTrivialization_weight]
      exact hcol m) h

/-! ### Finite sums -/

/-- `toSeq` commutes with finite sums: the generic `lpOneAlg.toRealSeq_finset_sum` read through
`toSeq_eq_toRealSeq`. -/
theorem toSeq_finset_sum {ι : Type*} (s : Finset ι) (x : ι → l1Chebyshev ν) (k : ℤ) :
    l1Chebyshev.toSeq (∑ i ∈ s, x i) k = ∑ i ∈ s, l1Chebyshev.toSeq (x i) k :=
  lpOneAlg.toRealSeq_finset_sum s x k

/-- Nonnegative-mode subseries bound: `∑_{k ≤ N} |a_k| ν^k ≤ ‖a‖`, for every `ν`. -/
theorem finSum_le_norm {N : ℕ} (f : l1Chebyshev ν) :
    ∑ k : Fin (N + 1), |toSeq f (↑(k : ℕ) : ℤ)| * (ν : ℝ) ^ (k : ℕ) ≤ ‖f‖ := by
  simp_rw [← norm_fiber_natCast]
  calc ∑ k : Fin (N + 1), ‖f (↑(k : ℕ) : ℤ)‖
      = ∑' k : Fin (N + 1), ‖f (↑(k : ℕ) : ℤ)‖ := (tsum_fintype _).symm
    _ ≤ ∑' m : ℤ, ‖f m‖ := tsum_comp_le_tsum_of_inj (lpOneAlg.summable_norm f)
        (fun _ => norm_nonneg _) fun a b h => Fin.ext (Nat.cast_injective h)
    _ = ‖f‖ := (lpOneAlg.norm_eq_tsum f).symm

/-- Fiberwise triangle inequality over a finite sum. -/
theorem norm_fiber_sum_le {ι : Type*} (s : Finset ι) (x : ι → l1Chebyshev ν) (k : ℤ) :
    ‖(∑ i ∈ s, x i) k‖ ≤ ∑ i ∈ s, ‖(x i) k‖ := by
  simp_rw [l1Chebyshev.norm_fiber, toSeq_finset_sum, ← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _)
    (pow_nonneg ν.2.le _)

/-! ### Convolution evaluation -/

variable [Fact (1 ≤ (ν : ℝ))]

/-- The bilateral convolution as a `ℤ`-tsum. -/
lemma toSeq_mul_tsum (x y : l1Chebyshev ν) (k : ℤ) :
    toSeq (x * y) k = ∑' i : ℤ, toSeq x (k - i) * toSeq y i :=
  lpOneAlg.toRealSeq_mul_tsum x y k

/-- Convolution against a finitely-supported factor is a finite sum. -/
lemma toSeq_mul_eq_finsum (x y : l1Chebyshev ν) (k : ℤ) (s : Finset ℤ)
    (hy : ∀ i ∉ s, toSeq y i = 0) :
    toSeq (x * y) k = ∑ i ∈ s, toSeq x (k - i) * toSeq y i :=
  lpOneAlg.toRealSeq_mul_eq_finsum x y k s hy

end l1Chebyshev

end RadiiPolynomial

end

namespace RadiiPolynomial

namespace l1Chebyshev

variable {ν : PosReal}

section OpNorm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The bilinear operator norm on `l1Chebyshev ν` as an atom supremum.** For
every `ν : PosReal` (no `1 ≤ ν`), `‖B‖` is the supremum of the ratios
`‖B e_i e_j‖ / (ν^{|i|} ν^{|j|})`. The case `M = M' = ℤ` of
`lpOneAlg.opNorm_eq_iSup_cols₂`. -/
theorem opNorm_eq_iSup_cols₂ (B : l1Chebyshev ν →L[ℝ] l1Chebyshev ν →L[ℝ] F) :
    ‖B‖ = ⨆ p : ℤ × ℤ, ‖B (lpOneAlg.single p.1 1) (lpOneAlg.single p.2 1)‖
      / ((ν : ℝ) ^ p.1.natAbs * (ν : ℝ) ^ p.2.natAbs) := by
  rw [lpOneAlg.opNorm_eq_iSup_cols₂ B]
  simp only [WeightedScalar.fiberTrivialization_weight]

set_option maxSynthPendingDepth 2 in
/-- **The trilinear operator norm on `l1Chebyshev ν` as an atom supremum.** For
every `ν : PosReal`, `‖T‖` is the supremum of the ratios
`‖T e_i e_j e_k‖ / (ν^{|i|} ν^{|j|} ν^{|k|})`. The case `M = M' = M'' = ℤ` of
`lpOneAlg.opNorm_eq_iSup_cols₃`. (Declared under `set_option maxSynthPendingDepth 2 in`:
at the default depth the norm does not synthesize on the three-level type; a
consumer who restates `‖T‖` for such a map needs the same local option; see
`WeightedL1/Multilinear.lean`.) -/
theorem opNorm_eq_iSup_cols₃
    (T : l1Chebyshev ν →L[ℝ] l1Chebyshev ν →L[ℝ] l1Chebyshev ν →L[ℝ] F) :
    ‖T‖ = ⨆ p : ℤ × ℤ × ℤ, ‖T (lpOneAlg.single p.1 1) (lpOneAlg.single p.2.1 1)
        (lpOneAlg.single p.2.2 1)‖
      / ((ν : ℝ) ^ p.1.natAbs * (ν : ℝ) ^ p.2.1.natAbs * (ν : ℝ) ^ p.2.2.natAbs) := by
  rw [lpOneAlg.opNorm_eq_iSup_cols₃ T]
  simp only [WeightedScalar.fiberTrivialization_weight]

end OpNorm

end l1Chebyshev

end RadiiPolynomial
