import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.SymmetricSubalgebra
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.UniversalProperty
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Restriction from bilateral and bordered storage to one-sided coefficients

For every `ν : PosReal`, this shipped module provides
`OneSided.borderedToWeighted : l1Bordered ν →L[ℝ] l1Weighted ν` and
`OneSided.restr : l1Chebyshev ν →L[ℝ] l1Weighted ν`, with coordinate face `restr_toSeq`,
norm identity `norm_restr_eq_tsum` and the sharp bound `norm_restr_le`.
The bordered weights are `1, 2ν, 2ν², …`; the target uses the unnormalized weights `νⁿ`.
These linear restriction constructions require no hypothesis `1 ≤ ν`.

The symmetric extension, reflected bilinear/trilinear products, their laws and exact
constants `C₂ = 1 + 2ν⁻²` and `C₃ = max(1 + 3ν⁻², 1 + 2ν⁻² + 2ν⁻⁴)` belong to the
recovery module `B5RecordOneSidedCosine`, with column bounds from
`B5RecordL1ColumnPrinciple`. They are not exports of this shipped file. Their bilateral
multiplication hypotheses remain in the recovery statements. The standard multiplication
on `l1Weighted ν` remains the Taylor Cauchy product; the reflected product is separate data.
The retained nonnegative-mode embedding `l1Chebyshev.natEmbed` is in `Chebyshev/Symmetrize.lean`.
-/

open scoped BigOperators Topology

noncomputable section

namespace RadiiPolynomial

namespace l1Chebyshev

namespace OneSided

variable {ν : PosReal}

/-! ### One-sided atoms -/



/-! ### The symmetric extension -/










/-! ### From the bordered carrier to the one-sided carrier -/

/-- The one-sided fiber is dominated by the bordered fiber (`pow_le_borderedWeight`). -/
private theorem fiber_bordered_le (a : l1Bordered ν) (n : ℕ) :
    |lpOneAlg.toRealSeq a n| * (ν : ℝ) ^ n ≤ ‖a n‖ := by
  rw [lpOneAlg.norm_eq_abs_toReal_mul_weight a n]
  simp only [WeightedScalar.fiberTrivialization_weight, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (pow_le_borderedWeight ν n) (abs_nonneg _)

/-- The coefficients of a bordered element have finite one-sided norm. -/
private theorem borderedToWeighted_mem (a : l1Bordered ν) :
    l1Weighted.Mem ν (fun n => lpOneAlg.toRealSeq a n) := by
  rw [l1Weighted.mem_iff]
  exact Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))
    (fiber_bordered_le a) (lpOneAlg.summable_norm a)

/-- The coefficient identity from the bordered to the one-sided carrier, as an element. -/
private def borderedToWeightedFun (a : l1Bordered ν) : l1Weighted ν :=
  l1Weighted.mk (fun n => lpOneAlg.toRealSeq a n) (borderedToWeighted_mem a)

/-- `borderedToWeightedFun` does not increase the norm. -/
private theorem norm_borderedToWeightedFun_le (a : l1Bordered ν) :
    ‖borderedToWeightedFun a‖ ≤ ‖a‖ := by
  rw [l1Weighted.norm_eq_tsum, lpOneAlg.norm_eq_tsum]
  exact (l1Weighted.summable_weighted _).tsum_le_tsum (fiber_bordered_le a)
    (lpOneAlg.summable_norm a)

/-- The identity on coefficients from the bordered carrier `l1Bordered ν` (weights `1`,
`2νⁿ`) to the one-sided carrier `l1Weighted ν` (weights `νⁿ`); norm at most `1` by
`pow_le_borderedWeight`. -/
def borderedToWeighted : l1Bordered ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := borderedToWeightedFun
      map_add' := fun a b => l1Weighted.ext fun n => by
        show lpOneAlg.toRealSeq (a + b) n = lpOneAlg.toRealSeq a n + lpOneAlg.toRealSeq b n
        exact congr_fun (lpOneAlg.toRealSeq_add a b) n
      map_smul' := fun r a => l1Weighted.ext fun n => by
        show lpOneAlg.toRealSeq (r • a) n = r * lpOneAlg.toRealSeq a n
        exact congr_fun (lpOneAlg.toRealSeq_smul r a) n }
    1 (fun a => by rw [one_mul]; exact norm_borderedToWeightedFun_le a)




/-! ### Restriction to the nonnegative modes -/

/-- **Restriction to the nonnegative modes**, `ℓ¹_ν(ℤ) → ℓ¹_ν(ℕ)`, `(restr x)_n = x_n`: the
library's `nonnegRestrictCLM` into the bordered carrier followed by `borderedToWeighted`. The
composite's inherited bound is `2`; the sharp bound `‖restr x‖ ≤ ‖x‖` is `norm_restr_le`. -/
def restr : l1Chebyshev ν →L[ℝ] l1Weighted ν := borderedToWeighted ∘L nonnegRestrictCLM ν

/-- Coefficients of the restriction. This is the explicit-rewrite form in `l1Weighted.toSeq`;
it is not a simp rule, because `l1Weighted.toSeq_apply` rewrites its left-hand side first. The
simp rule is `restr_apply`. -/
theorem restr_toSeq (x : l1Chebyshev ν) (n : ℕ) :
    l1Weighted.toSeq (restr x) n = toSeq x n := by
  show lpOneAlg.toRealSeq (nonnegRestrict x) n = _
  rw [nonnegRestrict_toSeq]
  rfl


/-- The one-sided norm of the restriction is the sum of the nonnegative-mode fiber norms. -/
theorem norm_restr_eq_tsum (x : l1Chebyshev ν) : ‖restr x‖ = ∑' n : ℕ, ‖x (n : ℤ)‖ := by
  rw [l1Weighted.norm_eq_tsum]
  exact tsum_congr fun n => by rw [restr_toSeq, norm_fiber_natCast]

/-- `‖restr x‖ ≤ ‖x‖`, directly from `norm_restr_eq_tsum` (the nonnegative modes are a
sub-sum of the bilateral norm). -/
theorem norm_restr_le (x : l1Chebyshev ν) : ‖restr x‖ ≤ ‖x‖ := by
  rw [norm_restr_eq_tsum, lpOneAlg.norm_eq_tsum]
  exact tsum_comp_le_tsum_of_inj (lpOneAlg.summable_norm x) (fun _ => norm_nonneg _)
    Nat.cast_injective








/-! ### The constants -/














/-! ### Real helpers (private) -/












/-! ### The reflected product -/

section Product

variable [Fact (1 ≤ (ν : ℝ))]












/-! ### Bilinear atoms and the constant `C₂` -/









/-! ### Trilinear atoms and the constant `C₃` -/






end Product

end OneSided

end l1Chebyshev

end RadiiPolynomial
