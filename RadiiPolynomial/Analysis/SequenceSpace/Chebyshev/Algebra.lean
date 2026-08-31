import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Scalar
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Chebyshev ℓ¹ Banach Algebra

`l1Chebyshev ν = lpOneAlg ℤ (ScaledRealZ ν)` — ℤ-indexed sequences with
bilateral weighted norm `∑|a_k|·ν^{|k|}` and convolution product.

Ring and algebra instances flow from `lpOneAlg` + `SubMulWeight` via
generic `WeightedScalar` instances in `WeightedScalar.lean`.
-/

open scoped BigOperators Topology

noncomputable section

namespace RadiiPolynomial

/-! ### Bridge lemma for downstream use -/

/-- The fiber norm of `lpAlgRingData.ofReal k r` for ScaledRealZ equals `|r| * ν^{|k|}`. -/
@[simp] theorem ScaledRealZ.norm_lpAlgRingData_ofReal (ν : PosReal) (k : ℤ) (r : ℝ) :
    ‖lpAlgRingData.ofReal (E := ScaledRealZ ν) k r‖ = |r| * (ν : ℝ) ^ k.natAbs :=
  WeightedScalar.norm_ofReal r

/-! ### Bilateral finite-support norm (index ℤ, any fibers) -/

/-- The norm of an element supported in `|k| ≤ N` as a finite bilateral sum. -/
theorem lpOneAlg.norm_eq_bilatFinSum {E : ℤ → Type*} [∀ k, NormedAddCommGroup (E k)]
    (f : lpOneAlg ℤ E) (N : ℕ)
    (h_tail : ∀ n : ℕ, N < n → ‖f (↑n : ℤ)‖ = 0)
    (h_negtail : ∀ n : ℕ, N < n + 1 → ‖f (Int.negSucc n)‖ = 0) :
    ‖f‖ = (∑ n : Fin (N + 1), ‖f (↑(n : ℕ) : ℤ)‖)
      + ∑ n : Fin N, ‖f (Int.negSucc (n : ℕ))‖ := by
  set g : ℤ → ℝ := fun k => ‖f k‖ with hg_def
  have hg_summ : Summable g := lpOneAlg.summable_norm f
  have h_nat : Summable (fun n : ℕ => g ↑n) :=
    hg_summ.comp_injective fun _ _ h => by omega
  have h_neg : Summable (fun n : ℕ => g (-(↑n + 1))) :=
    hg_summ.comp_injective fun _ _ h => by omega
  rw [lpOneAlg.norm_eq_tsum f, tsum_of_nat_of_neg_add_one h_nat h_neg]
  congr 1
  · rw [tsum_eq_sum (s := Finset.range (N + 1))
      (fun n hn => h_tail n (by simp [Finset.mem_range] at hn; omega))]
    rw [← Fin.sum_univ_eq_sum_range]
  · rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by
      show ‖f (-(↑n + 1 : ℤ))‖ = 0
      rw [show -(↑n + 1 : ℤ) = Int.negSucc n from by omega]
      exact h_negtail n (by simp [Finset.mem_range] at hn; omega))]
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun n _ => by
      show ‖f (-(↑(n : ℕ) + 1 : ℤ))‖ = _
      rw [show -(↑(n : ℕ) + 1 : ℤ) = Int.negSucc n from by omega]

/-! ### l1Chebyshev: the Chebyshev Banach algebra -/

/-- Chebyshev ℓ¹ Banach algebra: ℤ-indexed sequences with norm `∑|a_k|·ν^{|k|}`
and bilateral Cauchy product. All instances from generalized `lpOneAlg` + `SubMulWeight`. -/
abbrev l1Chebyshev (ν : PosReal) := lpOneAlg ℤ (ScaledRealZ ν)

namespace l1Chebyshev

variable {ν : PosReal}

/-- Extract underlying ℝ-valued sequence. -/
def toSeq (f : l1Chebyshev ν) : ℤ → ℝ := lpOneAlg.toRealSeq f

@[simp] lemma toSeq_add (f g : l1Chebyshev ν) (m : ℤ) :
    toSeq (f + g) m = toSeq f m + toSeq g m :=
  congr_fun (lpOneAlg.toRealSeq_add f g) m

-- Instances automatically available from lpOneAlg + SubMulWeight:
-- NormedAddCommGroup, Ring, NormedRing (always)
-- CommRing, NormedCommRing (ℤ is AddCommGroup ✓)
-- NormedSpace ℝ, Algebra ℝ, NormedAlgebra ℝ (ScaledRealZ has NormedSpace ℝ ✓)
-- All require [Fact (1 ≤ (ν : ℝ))] for Ring (via SubMulWeightBase: submul on ℤ needs ν ≥ 1)

-- Verify the key instances synthesize:
example [Fact (1 ≤ (ν : ℝ))] : NormedRing (l1Chebyshev ν) := inferInstance
example [Fact (1 ≤ (ν : ℝ))] : NormedCommRing (l1Chebyshev ν) := inferInstance
example [Fact (1 ≤ (ν : ℝ))] : NormedAlgebra ℝ (l1Chebyshev ν) := inferInstance

/-- Left multiplication CLM. -/
noncomputable abbrev leftMul [Fact (1 ≤ (ν : ℝ))] (a : l1Chebyshev ν) :
    l1Chebyshev ν →L[ℝ] l1Chebyshev ν :=
  letI : Algebra ℝ (l1Chebyshev ν) := lpOneAlg.instAlgebra
  letI : IsScalarTower ℝ (l1Chebyshev ν) (l1Chebyshev ν) := IsScalarTower.right
  letI : SMulCommClass ℝ (l1Chebyshev ν) (l1Chebyshev ν) := Algebra.to_smulCommClass
  ContinuousLinearMap.mul ℝ (l1Chebyshev ν) a

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

/-- The fiber norm in `toSeq` form: `‖a k‖ = |toSeq a k| · ν^{|k|}`. -/
lemma norm_fiber (a : l1Chebyshev ν) (k : ℤ) :
    ‖a k‖ = |toSeq a k| * (ν : ℝ) ^ k.natAbs := by
  rw [lpOneAlg.norm_eq_abs_toReal_mul_weight]
  simp [Real.norm_eq_abs, toSeq]

/-! ### Singles -/

/-- The element with value `x` at mode `j` and `0` elsewhere. -/
abbrev single (j : ℤ) (x : ℝ) : l1Chebyshev ν := lpOneAlg.single j x

lemma toSeq_single (j : ℤ) (x : ℝ) (k : ℤ) :
    toSeq (single (ν := ν) j x) k = if k = j then x else 0 :=
  lpOneAlg.toRealSeq_single j x k

lemma norm_single (j : ℤ) (x : ℝ) :
    ‖(single (ν := ν) j x)‖ = |x| * (ν : ℝ) ^ j.natAbs := by
  rw [lpOneAlg.norm_single, ScaledRealZ.norm_lpAlgRingData_ofReal]
  simp [Real.norm_eq_abs]

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
      rw [ScaledRealZ.norm_lpAlgRingData_ofReal, abs_one, one_mul]
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
      rw [ScaledRealZ.norm_lpAlgRingData_ofReal, abs_one, one_mul]
      exact hcol m) h

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
