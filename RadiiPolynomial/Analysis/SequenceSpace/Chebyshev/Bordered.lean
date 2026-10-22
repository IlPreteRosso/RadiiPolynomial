import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Symmetrize

/-!
# Bordered Chebyshev carrier and symmetric storage

The repo's physical T-series `u = a₀ + 2·Σ_{k≥1} a_k T_k` lives in symmetric bilateral
storage; its norm counts every mode doubled except the zero mode. This file realizes that
storage as an honest one-sided weighted space:

- `borderedWeight ν` — `1` at mode 0, `2ν^n` at modes `n ≥ 1`: the pushforward of the
  bilateral weight `ν^{|k|}` along the index cover `k ↦ |k|`, ramified at `0`.
- `l1Bordered ν` — the physical one-sided T-coefficient space.
- `nonnegRestrict : l1Chebyshev ν → l1Bordered ν` — restriction to the nonnegative modes,
  `2`-bounded by `nonnegRestrict_norm_le`; its bundle `nonnegRestrictCLM` is in
  `Chebyshev/SymmetricSubalgebra.lean`.


`l1Chebyshev.IsSymmetric`, `symmetrize` and `natEmbed` live in `Chebyshev/Symmetrize.lean`.
-/

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace RadiiPolynomial

/-! ### The bordered carrier: physical one-sided T-storage

`borderedWeight ν` is the pushforward of the bilateral weight `ν^{|k|}` along the
quotient `k ↦ |k|`: each unramified fiber `{±m}` contributes `2ν^m`, the ramified
fiber `{0}` contributes `1`. On the symmetric subspace of `l1Chebyshev ν` (physical T-series
`a₀ + 2Σ_{k≥1} a_k T_k`) restriction to the nonnegative modes preserves the norm, with values in
`l1Bordered ν`, an honest one-sided weighted space — the "bordering" datum as a weight. This
file does not state that isometry; it proves the bound `nonnegRestrict_norm_le` on all of
`l1Chebyshev ν`.

 -/

section BorderedWeight

/-- The bordered geometric weight: `1` at mode `0`, `2ν^n` at modes `n ≥ 1`. -/
def borderedWeight (ν : PosReal) : ℕ → ℝ :=
  fun n => if n = 0 then 1 else 2 * (ν : ℝ) ^ n

@[simp] lemma borderedWeight_zero (ν : PosReal) : borderedWeight ν 0 = 1 := rfl

@[simp] lemma borderedWeight_succ (ν : PosReal) (n : ℕ) :
    borderedWeight ν (n + 1) = 2 * (ν : ℝ) ^ (n + 1) := rfl

lemma borderedWeight_pos (ν : PosReal) (n : ℕ) : 0 < borderedWeight ν n := by
  cases n with
  | zero => norm_num [borderedWeight]
  | succ n => rw [borderedWeight_succ]; exact mul_pos two_pos (pow_pos ν.2 _)

/-- `ν^n ≤ borderedWeight ν n` — for every `ν > 0`. -/
lemma pow_le_borderedWeight (ν : PosReal) (n : ℕ) :
    (ν : ℝ) ^ n ≤ borderedWeight ν n := by
  cases n with
  | zero => norm_num [borderedWeight]
  | succ n =>
    rw [borderedWeight_succ]
    have h : (0 : ℝ) < (ν : ℝ) ^ (n + 1) := pow_pos ν.2 _
    linarith

/-- `borderedWeight ν n ≤ 2ν^n` — for every `ν > 0`. -/
lemma borderedWeight_le_two_mul (ν : PosReal) (n : ℕ) :
    borderedWeight ν n ≤ 2 * (ν : ℝ) ^ n := by
  cases n with
  | zero => norm_num [borderedWeight]
  | succ n => rw [borderedWeight_succ]

instance borderedWeight.instPosWeight (ν : PosReal) : PosWeight (borderedWeight ν) where
  weight_pos n := borderedWeight_pos ν n

/-- Submultiplicativity holds for every `ν > 0` (with slack `2 ≤ 4` in the interior). -/
instance borderedWeight.instSubMulWeightBase (ν : PosReal) :
    SubMulWeightBase (borderedWeight ν) where
  weight_pos n := borderedWeight_pos ν n
  submul m n := by
    cases m with
    | zero => rw [Nat.zero_add, borderedWeight_zero, one_mul]
    | succ m =>
      cases n with
      | zero => rw [Nat.add_zero, borderedWeight_zero, mul_one]
      | succ n =>
        rw [show m + 1 + (n + 1) = (m + n + 1) + 1 from by omega, borderedWeight_succ,
          borderedWeight_succ, borderedWeight_succ]
        have h1 : (0 : ℝ) < (ν : ℝ) ^ (m + n + 1 + 1) := pow_pos ν.2 _
        have h2 : (ν : ℝ) ^ (m + 1) * (ν : ℝ) ^ (n + 1) = (ν : ℝ) ^ (m + n + 1 + 1) := by
          rw [← pow_add]; congr 1; omega
        nlinarith [h1, h2]

/-- `BorderedScaledReal ν n` is `ℝ` with norm `|x| · borderedWeight ν n`.

WARNING: the automatic `Ring` on `lpOneAlg ℕ (BorderedScaledReal ν)` is the plain
ℕ-Cauchy-product ring, NOT the physical Chebyshev product
`T_m·T_n = (T_{m+n} + T_{|m-n|})/2` (a folded/hypergroup convolution outside the
monoid-algebra frame). This carrier is used at the normed-space level only. -/
abbrev BorderedScaledReal (ν : PosReal) := WeightedScalar ℝ (borderedWeight ν)

/-- Physical one-sided T-coefficient space: `‖a‖ = |a₀| + 2Σ_{n≥1}|a_n|ν^n`. -/
abbrev l1Bordered (ν : PosReal) := lpOneAlg ℕ (BorderedScaledReal ν)

@[simp] theorem BorderedScaledReal.norm_equiv_apply (ν : PosReal) (n : ℕ) (r : ℝ) :
    ‖FiberTrivialization.equiv (E := BorderedScaledReal ν) n r‖ = |r| * borderedWeight ν n :=
  WeightedScalar.norm_ofReal r

variable {ν : PosReal}

/-- Fiber norm on the bordered carrier. -/
private lemma l1Bordered_norm_fiber (a : l1Bordered ν) (n : ℕ) :
    ‖a n‖ = |lpOneAlg.toRealSeq a n| * borderedWeight ν n := by
  rw [lpOneAlg.norm_eq_abs_toReal_mul_weight a n]
  simp only [WeightedScalar.fiberTrivialization_weight, Real.norm_eq_abs]

end BorderedWeight

/-! #### Restriction of bilateral storage to the nonnegative modes -/

section SymmetricBridge

variable {ν : PosReal}

private lemma nonnegRestrict_fiber_le (a : l1Chebyshev ν) (n : ℕ) :
    |lpOneAlg.toRealSeq a (↑n : ℤ)| * borderedWeight ν n ≤ 2 * ‖a (↑n : ℤ)‖ := by
  rw [norm_fiber_natCast]
  have he : |l1Chebyshev.toSeq a (↑n : ℤ)| = |lpOneAlg.toRealSeq a (↑n : ℤ)| := rfl
  rw [he]
  refine (mul_le_mul_of_nonneg_left (borderedWeight_le_two_mul ν n) (abs_nonneg _)).trans
    (le_of_eq ?_)
  ring

private lemma nonnegRestrict_mem (a : l1Chebyshev ν) :
    Memℓp (fun n : ℕ => FiberTrivialization.equiv (E := BorderedScaledReal ν) n
      (lpOneAlg.toRealSeq a (↑n : ℤ))) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_norm_natCast a).mul_left 2)
  rw [BorderedScaledReal.norm_equiv_apply]
  exact nonnegRestrict_fiber_le a n

/-- Restriction of a bilateral sequence to its nonnegative modes, viewed in the
bordered carrier. -/
def nonnegRestrict (a : l1Chebyshev ν) : l1Bordered ν :=
  ⟨⟨fun n => FiberTrivialization.equiv (E := BorderedScaledReal ν) n
      (lpOneAlg.toRealSeq a (↑n : ℤ)),
    nonnegRestrict_mem a⟩⟩

@[simp] lemma nonnegRestrict_toSeq (a : l1Chebyshev ν) (n : ℕ) :
    lpOneAlg.toRealSeq (nonnegRestrict a) n = lpOneAlg.toRealSeq a (↑n : ℤ) :=
  FiberTrivialization.equiv_symm_apply_equiv n _


/-- Restriction to the nonnegative modes is `2`-bounded on all of `l1Chebyshev ν`, for every
`ν`: each stored mode `n ≥ 1` carries the bordered weight `2νⁿ`. -/
theorem nonnegRestrict_norm_le (a : l1Chebyshev ν) : ‖nonnegRestrict a‖ ≤ 2 * ‖a‖ := by
  have hfib : ∀ n : ℕ, ‖(nonnegRestrict a) n‖ ≤ 2 * ‖a (n : ℤ)‖ := fun n => by
    rw [l1Bordered_norm_fiber, nonnegRestrict_toSeq]
    exact nonnegRestrict_fiber_le a n
  rw [lpOneAlg.norm_eq_tsum, lpOneAlg.norm_eq_tsum]
  refine (Summable.tsum_le_tsum hfib (lpOneAlg.summable_norm _)
    ((summable_norm_natCast a).mul_left 2)).trans ?_
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj (lpOneAlg.summable_norm a)
    (fun _ => norm_nonneg _) Nat.cast_injective) zero_le_two

end SymmetricBridge



end RadiiPolynomial

end
