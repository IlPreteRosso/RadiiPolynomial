import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import RadiiPolynomial.source.lpSpace.ScaledReal

/-!
# ℤ-indexed Scaled Real for Chebyshev Series

`ScaledRealZ ν k` is `ℝ` equipped with norm `|x| * ν^{|k|}` for `k : ℤ` and `ν > 0`.

This is the bilateral analogue of `ScaledReal ν n` (which uses `ν^n` for `n : ℕ`).
For Chebyshev series, `ν > 1` encodes the exponential decay rate of coefficients.

## Architecture

The Chebyshev Banach algebra `l1Chebyshev ν` is built as `lp (ScaledRealZ ν) 1`,
parallel to `l1Weighted ν = lp (ScaledReal ν) 1` for Taylor series.
-/

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace RadiiPolynomial

/-- `ScaledRealZ ν k` is `ℝ` equipped with norm `|x| * ν^{|k|}` for `k : ℤ`. -/
def ScaledRealZ (_ν : PosReal) (_k : ℤ) := ℝ

namespace ScaledRealZ

variable {ν : PosReal} {k : ℤ}

instance : AddCommGroup (ScaledRealZ ν k) := inferInstanceAs (AddCommGroup ℝ)
instance : Module ℝ (ScaledRealZ ν k) := inferInstanceAs (Module ℝ ℝ)
instance : Ring (ScaledRealZ ν k) := inferInstanceAs (Ring ℝ)
instance : Lattice (ScaledRealZ ν k) := inferInstanceAs (Lattice ℝ)
instance : LinearOrder (ScaledRealZ ν k) := inferInstanceAs (LinearOrder ℝ)
instance : AddLeftMono (ScaledRealZ ν k) := inferInstanceAs (AddLeftMono ℝ)

/-- Identity map to `ℝ`. -/
@[coe] def toReal (x : ScaledRealZ ν k) : ℝ := x

instance : CoeOut (ScaledRealZ ν k) ℝ := ⟨toReal⟩

instance instNorm : Norm (ScaledRealZ ν k) where
  norm x := |toReal x| * (ν : ℝ) ^ k.natAbs

lemma norm_def (x : ScaledRealZ ν k) : ‖x‖ = |toReal x| * (ν : ℝ) ^ k.natAbs := rfl

lemma norm_nonneg' (x : ScaledRealZ ν k) : 0 ≤ ‖x‖ :=
  mul_nonneg (abs_nonneg (toReal x)) (pow_nonneg (PosReal.coe_nonneg ν) k.natAbs)

@[simp] lemma norm_zero' : ‖(0 : ScaledRealZ ν k)‖ = 0 := by simp [norm_def, toReal]

@[simp] lemma norm_neg' (x : ScaledRealZ ν k) : ‖-x‖ = ‖x‖ := by
  simp [norm_def, toReal, abs_neg]

lemma norm_add_le' (x y : ScaledRealZ ν k) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  simp only [norm_def]
  have h : toReal (x + y) = toReal x + toReal y := rfl
  calc |toReal (x + y)| * (ν : ℝ) ^ k.natAbs
      ≤ (|toReal x| + |toReal y|) * (ν : ℝ) ^ k.natAbs := by
        rw [h]
        exact mul_le_mul_of_nonneg_right (abs_add_le _ _)
          (pow_nonneg (PosReal.coe_nonneg ν) k.natAbs)
    _ = |toReal x| * (ν : ℝ) ^ k.natAbs + |toReal y| * (ν : ℝ) ^ k.natAbs := by ring

lemma norm_smul' (c : ℝ) (x : ScaledRealZ ν k) : ‖c • x‖ = |c| * ‖x‖ := by
  simp only [norm_def]
  have h : toReal (c • x) = c * toReal x := rfl
  rw [h, abs_mul]; ring

lemma norm_eq_zero' (x : ScaledRealZ ν k) : ‖x‖ = 0 ↔ x = 0 := by
  simp only [norm_def, mul_eq_zero, pow_eq_zero_iff', ne_eq]
  constructor
  · intro h
    cases h with
    | inl h => exact abs_eq_zero.mp h
    | inr h => exact absurd h.1 (PosReal.coe_ne_zero ν)
  · intro h; left; simp [h, toReal]

instance instNormedAddCommGroup : NormedAddCommGroup (ScaledRealZ ν k) where
  dist x y := ‖x - y‖
  dist_self x := by simp [norm_zero']
  dist_comm x y := by
    simp only [norm_def]
    rw [show toReal (x - y) = toReal x - toReal y from rfl,
        show toReal (y - x) = toReal y - toReal x from rfl,
        abs_sub_comm]
  dist_triangle x y z := by
    have h : x - z = (x - y) + (y - z) := by abel_nf
    rw [h]; exact norm_add_le' _ _
  edist_dist x y := by simp only [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg' _)]
  eq_of_dist_eq_zero h := by rwa [norm_eq_zero', sub_eq_zero] at h
  norm := (‖·‖)
  dist_eq _ _ := rfl

instance instNormedSpace : NormedSpace ℝ (ScaledRealZ ν k) where
  norm_smul_le c x := by rw [norm_smul']; rfl

instance instFiniteDimensional : FiniteDimensional ℝ (ScaledRealZ ν k) :=
  inferInstanceAs (FiniteDimensional ℝ ℝ)

instance instCompleteSpace : CompleteSpace (ScaledRealZ ν k) := by
  simpa using (FiniteDimensional.complete (𝕜 := ℝ) (E := ScaledRealZ ν k))

/-- Additive equivalence from `ℝ`. -/
def ofReal : ℝ ≃+ ScaledRealZ ν k := AddEquiv.refl ℝ

@[simp] lemma toReal_apply (x : ScaledRealZ ν k) : toReal x = x := rfl
@[simp] lemma ofReal_apply (x : ℝ) : (ofReal x : ScaledRealZ ν k) = x := rfl

@[simp] lemma coe_zero : ((0 : ScaledRealZ ν k) : ℝ) = 0 := rfl
@[simp] lemma coe_one : ((1 : ScaledRealZ ν k) : ℝ) = 1 := rfl
@[simp] lemma coe_add (x y : ScaledRealZ ν k) : ((x + y : ScaledRealZ ν k) : ℝ) = x + y := rfl
@[simp] lemma coe_sub (x y : ScaledRealZ ν k) : ((x - y : ScaledRealZ ν k) : ℝ) = x - y := rfl
@[simp] lemma coe_neg (x : ScaledRealZ ν k) : ((-x : ScaledRealZ ν k) : ℝ) = -x := rfl
@[simp] lemma coe_smul (r : ℝ) (x : ScaledRealZ ν k) :
    ((r • x : ScaledRealZ ν k) : ℝ) = r • ↑x := rfl

/-- Key inequality for Chebyshev submultiplicativity: `ν^{|j+l|} ≤ ν^{|j|} * ν^{|l|}`
when `ν ≥ 1`. Uses `|j+l| ≤ |j| + |l|` (triangle inequality on ℤ). -/
lemma pow_natAbs_add_le (ν : PosReal) (hν : 1 ≤ (ν : ℝ)) (j l : ℤ) :
    (ν : ℝ) ^ (j + l).natAbs ≤ (ν : ℝ) ^ j.natAbs * (ν : ℝ) ^ l.natAbs := by
  rw [← pow_add]
  exact pow_le_pow_right₀ hν (Int.natAbs_add_le j l)

end ScaledRealZ

end RadiiPolynomial
