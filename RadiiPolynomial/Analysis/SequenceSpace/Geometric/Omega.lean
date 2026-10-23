import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.UniversalProperty
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Omega-weighted sequence space for IVP problems

The IVP zero-finding map `F(a)_k = k·a_k − φ(a)_{k−1}` does not map `ℓ¹_ν → ℓ¹_ν`
because the factor `k` breaks summability. The book (Proposition 8.1.5) resolves this
with range space `Y = ℓ¹_ω` where `ω_n = ν^{n+1}/(n+1)`.

This file provides:
- `OmegaScaledReal ν n`: `WeightedScalar (omegaWeight ν) n` with PosWeight
- `l1Omega ν`: omega-weighted `ℓ¹` space
- Key embedding/summability lemmas connecting `l1Weighted` and `l1Omega`
- the shift-and-divide operator `shiftDivN` on `l1Weighted ν` (`shiftDivN_CLM`) with its norm
  and tail bounds, the derivative shift `derivShift : ℓ¹_ν → ℓ¹_ω`, and the evaluation
  `l1Omega.eval`
- the absolute derivative series `l1Weighted.summable_abs_mul_pow_pred` (`0 ≤ r < ν`)
-/

open scoped BigOperators Topology NNReal ENNReal

noncomputable section

namespace RadiiPolynomial

/-! ### Omega weight function (defined before the abbrev) -/

namespace OmegaScaledReal

variable {ν : PosReal} {n : ℕ}

/-- The omega weight at mode `n`: `ν^(n+1) / (n+1)`. -/
def omegaWeight (ν : PosReal) (n : ℕ) : ℝ := (ν : ℝ) ^ (n + 1) / (↑(n + 1) : ℝ)

lemma omegaWeight_pos : 0 < omegaWeight ν n := by
  unfold omegaWeight
  exact div_pos (pow_pos ν.coe_pos _) (Nat.cast_pos.mpr (Nat.succ_pos n))


end OmegaScaledReal

/-! ### OmegaScaledReal as WeightedScalar specialization -/

/-- `OmegaScaledReal ν n` is `ℝ` with norm `|x| * ν^(n+1)/(n+1)` — IVP range weight.
Ref: §8.1, Proposition 8.1.5. PosWeight only (not submultiplicative). -/
abbrev OmegaScaledReal (ν : PosReal) := WeightedScalar ℝ (OmegaScaledReal.omegaWeight ν)

instance OmegaScaledReal.instPosWeight (ν : PosReal) :
    PosWeight (OmegaScaledReal.omegaWeight ν) where
  weight_pos _ := OmegaScaledReal.omegaWeight_pos

/-! ### Compatibility aliases -/

namespace OmegaScaledReal

variable {ν : PosReal} {n : ℕ}

abbrev toReal (x : OmegaScaledReal ν n) : ℝ := WeightedScalar.toReal x
abbrev ofReal : ℝ ≃+ OmegaScaledReal ν n := WeightedScalar.ofReal

end OmegaScaledReal

/-- Omega-weighted `ℓ¹` space: `ℓ¹_ω` with `ω_n = ν^{n+1}/(n+1)`. -/
abbrev l1Omega (ν : PosReal) := lp (OmegaScaledReal ν) 1

namespace l1Omega

variable {ν : PosReal}

-- UniformSpace and CompleteSpace are inherited from lp's NormedAddCommGroup.

/-- Underlying real sequence. -/
def toSeq (a : l1Omega ν) : ℕ → ℝ := fun n => OmegaScaledReal.toReal (a n)


/-- Membership predicate for omega-weighted `ℓ¹`. -/
def Mem (ν : PosReal) (a : ℕ → ℝ) : Prop :=
  Memℓp (fun n => OmegaScaledReal.ofReal (a n) : ∀ n, OmegaScaledReal ν n) 1

/-- Construct an element from a sequence with finite omega-weighted norm. -/
def mk (a : ℕ → ℝ) (ha : Mem ν a) : l1Omega ν :=
  ⟨fun n => OmegaScaledReal.ofReal (a n), ha⟩



lemma mem_iff (a : ℕ → ℝ) :
    Mem ν a ↔ Summable (fun n => |a n| * OmegaScaledReal.omegaWeight ν n) := by
  simp only [Mem, Memℓp, ne_eq]
  simp only [show (1 : ℝ≥0∞) ≠ 0 from one_ne_zero, ENNReal.one_ne_top, ↓reduceIte,
    WeightedScalar.norm_ofReal, Real.norm_eq_abs, ENNReal.toReal_one, Real.rpow_one]

end l1Omega

section Bridges

variable {ν : PosReal}

/-- Key weight identity: `(n+1) * ω_n = ν^{n+1}`, i.e., multiplying by the mode index
is exactly compensated by the omega weight. This is the fundamental property
that makes IVP maps well-typed. Ref: Proposition 8.1.5. -/
lemma omegaWeight_mul_index (n : ℕ) :
    (↑(n + 1) : ℝ) * OmegaScaledReal.omegaWeight ν n = (ν : ℝ) ^ (n + 1) := by
  unfold OmegaScaledReal.omegaWeight
  rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))]


/-- If `a ∈ ℓ¹_ν`, then the derivative-shifted sequence `{(n+1)·a_{n+1}}` belongs to `ℓ¹_ω`.
This is the key membership lemma for IVP zero-finding maps.
Ref: Proposition 8.1.5 — `b = {(n+1)a_{n+1}} ∈ ℓ¹_ω`. -/
lemma l1Omega.deriv_shift_mem (a : l1Weighted ν) :
    l1Omega.Mem ν (fun (n : ℕ) => ((n : ℝ) + 1) * l1Weighted.toSeq a (n + 1)) := by
  rw [l1Omega.mem_iff]
  -- |b_n| · ω_n = |(n+1) · a_{n+1}| · ν^{n+1}/(n+1) = |a_{n+1}| · ν^{n+1}
  have h : ∀ (n : ℕ), |((n : ℝ) + 1) * l1Weighted.toSeq a (n + 1)| *
      OmegaScaledReal.omegaWeight ν n =
      |l1Weighted.toSeq a (n + 1)| * (ν : ℝ) ^ (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [abs_mul, abs_of_pos hpos, mul_comm ((n : ℝ) + 1) _, mul_assoc,
      show (n : ℝ) + 1 = ↑(n + 1) from by push_cast; ring, omegaWeight_mul_index]
  simp_rw [h]
  exact ((l1Weighted.mem_iff (ν := ν) (l1Weighted.toSeq a)).mp a.toLp.2).comp_injective
    (fun (n m : ℕ) (h : n + 1 = m + 1) => by omega)



end Bridges

section ShiftDivN

variable {ν : PosReal}

/-- The shift-and-divide operator: maps sequence `b` to `{0, b_0/1, b_1/2, b_2/3, ...}`.
This is the key IVP tail operator: `(shiftDivN b)_n = b_{n-1}/n` for `n ≥ 1`, zero at `n = 0`.
Bounded: `‖shiftDivN b‖ ≤ ν · ‖b‖` since `|b_{n-1}|/n · ν^n ≤ |b_{n-1}| · ν^n ≤ ν · |b_{n-1}| · ν^{n-1}`. -/
private def shiftDivN_seq (b : l1Weighted ν) : ℕ → ℝ
  | 0 => 0
  | n + 1 => l1Weighted.toSeq b n / (↑(n + 1) : ℝ)

private lemma shiftDivN_shifted_term_le (b : l1Weighted ν) (n : ℕ) :
    |shiftDivN_seq b (n + 1)| * (ν : ℝ) ^ (n + 1) ≤
    (ν : ℝ) * (|l1Weighted.toSeq b n| * (ν : ℝ) ^ n) := by
  simp only [shiftDivN_seq]
  have hn1 : (1 : ℝ) ≤ (↑(n + 1) : ℝ) := by exact_mod_cast Nat.succ_pos n
  rw [abs_div, abs_of_nonneg (le_of_lt (lt_of_lt_of_le one_pos hn1))]
  rw [div_mul_eq_mul_div, pow_succ, ← mul_assoc]
  exact (div_le_self (mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _)) ν.2.le) hn1).trans_eq
    (mul_comm _ (ν : ℝ))

private lemma shiftDivN_mem (b : l1Weighted ν) : l1Weighted.Mem ν (shiftDivN_seq b) := by
  rw [l1Weighted.mem_iff]
  have hb : Summable (fun n => |l1Weighted.toSeq b n| * (ν : ℝ) ^ n) :=
    (l1Weighted.mem_iff (l1Weighted.toSeq b)).mp b.toLp.2
  -- Suffices to show the shifted series n ↦ f(n+1) is summable
  let f : ℕ → ℝ := fun n => |shiftDivN_seq b n| * (ν : ℝ) ^ n
  show Summable f
  rw [← summable_nat_add_iff (k := 1)]
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))
    (shiftDivN_shifted_term_le b)
    (hb.mul_left (ν : ℝ))

/-- The shift-and-divide operator as an element of `l1Weighted ν`. -/
noncomputable def shiftDivN (b : l1Weighted ν) : l1Weighted ν :=
  l1Weighted.mk (shiftDivN_seq b) (shiftDivN_mem b)


@[simp] lemma shiftDivN_succ_mode (b : l1Weighted ν) (n : ℕ) :
    l1Weighted.toSeq (shiftDivN b) (n + 1) =
      l1Weighted.toSeq b n / (↑(n + 1) : ℝ) := by
  show shiftDivN_seq b (n + 1) = l1Weighted.toSeq b n / (↑(n + 1) : ℝ)
  simp [shiftDivN_seq]

private lemma shiftDivN_toSeq (b : l1Weighted ν) (n : ℕ) :
    l1Weighted.toSeq (shiftDivN b) n = shiftDivN_seq b n := rfl

lemma shiftDivN_linear_add (b c : l1Weighted ν) :
    shiftDivN (b + c) = shiftDivN b + shiftDivN c := by
  apply l1Weighted.ext; intro n
  simp only [shiftDivN_toSeq, l1Weighted.add_toSeq]
  cases n with
  | zero => simp [shiftDivN_seq]
  | succ n => simp only [shiftDivN_seq]; exact add_div _ _ _

lemma shiftDivN_linear_smul (r : ℝ) (b : l1Weighted ν) :
    shiftDivN (r • b) = r • shiftDivN b := by
  apply l1Weighted.ext; intro n
  simp only [shiftDivN_toSeq, l1Weighted.smul_toSeq]
  cases n with
  | zero => simp [shiftDivN_seq]
  | succ n => simp only [shiftDivN_seq]; exact mul_div_assoc _ _ _

lemma shiftDivN_norm_le (b : l1Weighted ν) :
    ‖shiftDivN b‖ ≤ (ν : ℝ) * ‖b‖ := by
  rw [l1Weighted.norm_eq_tsum, l1Weighted.norm_eq_tsum]
  -- Bridge: toSeq (shiftDivN b) n = shiftDivN_seq b n (via simp lemmas)
  conv_lhs => arg 1; ext n; rw [show l1Weighted.toSeq (shiftDivN b) n = shiftDivN_seq b n
    from shiftDivN_toSeq b n]
  have hsumm : Summable (fun n => |shiftDivN_seq b n| * (ν : ℝ) ^ n) :=
    (l1Weighted.mem_iff _).mp (shiftDivN_mem b)
  have hb : Summable (fun n => |l1Weighted.toSeq b n| * (ν : ℝ) ^ n) :=
    (l1Weighted.mem_iff _).mp b.toLp.2
  -- Split: Σ f(n) = f(0) + Σ f(n+1), then bound shifted terms by ν * g(n)
  rw [hsumm.tsum_eq_zero_add]
  simp only [shiftDivN_seq, abs_zero, zero_mul, zero_add]
  rw [← tsum_mul_left]
  exact ((summable_nat_add_iff (k := 1)).mpr hsumm).tsum_le_tsum
    (shiftDivN_shifted_term_le b) (hb.mul_left _)

/-- Termwise form of the tail bound: the weighted mode-`n + (N+1)` term of `shiftDivN b` is at
most `ν/(N+1)` times the weighted mode-`n + N` term of `b`, because on tail modes
`1/n ≤ 1/(N+1)`.
Summed in `shiftDivN_tailTsum_le_div`. -/
private lemma shiftDivN_shifted_term_tight_le (b : l1Weighted ν) (N n : ℕ) :
    |shiftDivN_seq b (n + (N + 1))| * (ν : ℝ) ^ (n + (N + 1)) ≤
    (ν : ℝ) / (↑N + 1) * (|l1Weighted.toSeq b (n + N)| * (ν : ℝ) ^ (n + N)) := by
  -- Rewrite n + (N+1) = n + N + 1 to enable pattern match
  rw [(Nat.add_assoc n N 1).symm]
  -- Now shiftDivN_seq b (n + N + 1) reduces since n+N+1 = (n+N).succ
  simp only [shiftDivN_seq]
  -- Goal: |toSeq b (n+N) / ↑(n+N+1)| * ν^(n+N+1) ≤ ν/(N+1) * (|toSeq b (n+N)| * ν^(n+N))
  have hn1 : (1 : ℝ) ≤ ↑(n + N + 1) := by exact_mod_cast Nat.succ_pos (n + N)
  rw [abs_div, abs_of_nonneg (le_of_lt (lt_of_lt_of_le one_pos hn1))]
  rw [div_mul_eq_mul_div, pow_succ, ← mul_assoc]
  -- LHS: |b_m| * ν^m * ν / (m+1);  RHS: ν/(N+1) * (|b_m| * ν^m)
  -- Factor: both are |b_m| * ν^m * (ν / denominator)
  have hterm := mul_nonneg (mul_nonneg (abs_nonneg (l1Weighted.toSeq b (n + N)))
    (pow_nonneg ν.2.le (n + N))) ν.2.le
  exact (div_le_div_of_nonneg_left hterm (by positivity : (0 : ℝ) < ↑N + 1)
    (by exact_mod_cast (show N + 1 ≤ n + N + 1 by omega))).trans_eq
    (by rw [mul_div_assoc]; exact mul_comm _ _)

/-- Tail of `shiftDivN b` starting from mode `N+1` is bounded by `ν/(N+1) · ‖b‖`.
Tighter than `shiftDivN_norm_le` (`≤ ν · ‖b‖`) because `1/n ≤ 1/(N+1)` on tail.
Used for IVP Z₁ tail error bounds. -/
lemma shiftDivN_tailTsum_le_div (b : l1Weighted ν) (N : ℕ) :
    ∑' n, |l1Weighted.toSeq (shiftDivN b) (n + (N + 1))| * (ν : ℝ) ^ (n + (N + 1)) ≤
      (ν : ℝ) / (↑N + 1) * ‖b‖ := by
  simp only [show ∀ n, l1Weighted.toSeq (shiftDivN b) n = shiftDivN_seq b n
    from shiftDivN_toSeq b]
  have hsumm := (summable_nat_add_iff (k := N + 1)).mpr
    ((l1Weighted.mem_iff _).mp (shiftDivN_mem b))
  have hb_shift := ((summable_nat_add_iff (k := N)).mpr
    (l1Weighted.summable_weighted b)).mul_left ((ν : ℝ) / (↑N + 1))
  calc ∑' n, |shiftDivN_seq b (n + (N + 1))| * (ν : ℝ) ^ (n + (N + 1))
      ≤ ∑' n, ((ν : ℝ) / (↑N + 1) * (|l1Weighted.toSeq b (n + N)| * (ν : ℝ) ^ (n + N))) :=
        hsumm.tsum_le_tsum (shiftDivN_shifted_term_tight_le b N) hb_shift
    _ = (ν : ℝ) / (↑N + 1) * ∑' n, (|l1Weighted.toSeq b (n + N)| * (ν : ℝ) ^ (n + N)) :=
        tsum_mul_left
    _ ≤ (ν : ℝ) / (↑N + 1) * ‖b‖ :=
        mul_le_mul_of_nonneg_left (l1Weighted.tailTsum_le_norm_of_eq b b N (fun _ _ => rfl))
          (div_nonneg ν.2.le (by positivity))

/-- The shift-and-divide operator as a CLM on `l1Weighted ν`. -/
noncomputable def shiftDivN_CLM : l1Weighted ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := shiftDivN
      map_add' := shiftDivN_linear_add
      map_smul' := fun r b => by simp [shiftDivN_linear_smul] }
    (ν : ℝ)
    shiftDivN_norm_le

@[simp] lemma shiftDivN_CLM_apply (b : l1Weighted ν) :
    shiftDivN_CLM b = shiftDivN b := rfl

/-! ### Tail mass of the Z₁ tail operator

The Z₁ tail operator is `T_N(b) := π_{>N} ∘ shiftDivN ∘ leftMul b`. The tail mass of
`shiftDivN` is subadditive over finite sums (`tail_shiftDivN_sum_le`), so a tail bound for
`shiftDivN (Σ_m b_m · h_m)` splits into per-pair bounds; the head-column bound of each pair is
`WeightedLp.tailTsum_shiftDivN_mul_le_of_colMass` (`WeightedLp/Compatibility/TaylorTailL1.lean`).
Hygiene: `ν : PosReal` only. -/

/-- The tail mass of `shiftDivN` is subadditive over finite sums. -/
theorem tail_shiftDivN_sum_le {N : ℕ} {ι : Type*} (s : Finset ι) (x : ι → l1Weighted ν) :
    ∑' n, |l1Weighted.toSeq (shiftDivN (∑ i ∈ s, x i)) (n + (N + 1))| *
        (ν : ℝ) ^ (n + (N + 1)) ≤
      ∑ i ∈ s, ∑' n, |l1Weighted.toSeq (shiftDivN (x i)) (n + (N + 1))| *
        (ν : ℝ) ^ (n + (N + 1)) := by
  simp_rw [← l1Weighted.norm_tailProj_eq_tailTsum]
  have hmap := map_sum ((l1Weighted.tailProj_CLM (ν := ν) N).comp shiftDivN_CLM) x s
  simp only [ContinuousLinearMap.comp_apply, l1Weighted.tailProj_CLM_apply,
    shiftDivN_CLM_apply] at hmap
  rw [hmap]
  exact norm_sum_le _ _



end ShiftDivN

section DerivShift

variable {ν : PosReal}

/-- The derivative-shift sequence: `(D a)_n = (n+1) · a_{n+1}`.
Coefficient sequence of `dx/dt` when `x(t) = Σ a_n t^n`. -/
private def derivShift_seq (a : l1Weighted ν) : ℕ → ℝ :=
  fun n => ((n : ℝ) + 1) * l1Weighted.toSeq a (n + 1)

private lemma derivShift_mem (a : l1Weighted ν) :
    l1Omega.Mem ν (derivShift_seq a) :=
  l1Omega.deriv_shift_mem a

/-- The derivative-shift operator `D : ℓ¹_ν → ℓ¹_ω`.
The `(n+1)` factor is exactly compensated by `ω_n = ν^{n+1}/(n+1)`, so the operator
maps into ℓ¹_ω rather than ℓ¹_ν. Term-by-term differentiation:
`d/dt eval(a, t) = eval(D a, t)` for `|t| < ν` (proved as `l1Weighted.hasDerivAt_eval` in
`Geometric/EvaluationDerivative.lean`).
Ref: Proposition 8.1.5. -/
noncomputable def derivShift (a : l1Weighted ν) : l1Omega ν :=
  l1Omega.mk (derivShift_seq a) (derivShift_mem a)

@[simp] lemma derivShift_apply (a : l1Weighted ν) (n : ℕ) :
    l1Omega.toSeq (derivShift a) n = ((n : ℝ) + 1) * l1Weighted.toSeq a (n + 1) := rfl






end DerivShift

section Eval

variable {ν : PosReal}

/-- Summability of `Σ b_n · t^n` for `b ∈ ℓ¹_ω` and `|t| < ν` (strict); the absolute form
`Σ |b_n| · |t|^n` is `l1Omega.summable_abs_eval`.
The bound `(n+1) · (|t|/ν)^n` is used as the conversion factor between `ω_n` and `|t|^n`. -/
theorem l1Omega.summable_eval (b : l1Omega ν) {t : ℝ} (ht : |t| < ν) :
    Summable fun n => l1Omega.toSeq b n * t ^ n := by
  have hν : (0 : ℝ) < ν := ν.2
  set r : ℝ := |t| / ν with hr_def
  have hr_lt : r < 1 := (div_lt_one hν).mpr ht
  have hr_nn : (0 : ℝ) ≤ r := div_nonneg (abs_nonneg _) hν.le
  have hr_norm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr_nn] using hr_lt
  -- Σ (n+1) · r^n is summable for r < 1
  have h_geom_summable : Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
    simpa using
      (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr_norm)
  -- Each term bounded by the tsum
  set M : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) * r ^ n
  -- Bound |b_n · t^n| by (M/ν) · (|b_n| · ω_n)
  refine Summable.of_norm_bounded
    (g := fun n => (M / ν) * (|l1Omega.toSeq b n| * OmegaScaledReal.omegaWeight ν n))
    (((l1Omega.mem_iff _).mp b.2).mul_left (M / ν)) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have h_t_pow_eq : |t| ^ n = r ^ n * (ν : ℝ) ^ n := by
    rw [hr_def, div_pow, div_mul_cancel₀ _ (pow_ne_zero n hν.ne')]
  rw [h_t_pow_eq]
  unfold OmegaScaledReal.omegaWeight
  rw [pow_succ, mul_left_comm (M / ν) |l1Omega.toSeq b n|]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  field_simp
  simpa [Nat.cast_add, Nat.cast_one, mul_comm] using
    h_geom_summable.le_tsum n (fun k _ => by positivity)

/-- Absolute summability for `ℓ¹_ω` evaluation, used as a uniform bound on the disk. -/
theorem l1Omega.summable_abs_eval (b : l1Omega ν) {t : ℝ} (ht : |t| < ν) :
    Summable fun n => |l1Omega.toSeq b n| * |t| ^ n := by
  have h := l1Omega.summable_eval b (t := |t|) (by rwa [abs_abs])
  refine (h.abs).congr fun n => ?_
  rw [abs_mul, abs_pow, abs_abs]

/-- **Absolute derivative series.** For `a ∈ ℓ¹_ν` and `0 ≤ r < ν` the series
`∑ₙ |aₙ| · n · r ^ (n - 1)` converges; the endpoint `r = 0` is included. It dominates the
termwise derivative of `l1Weighted.eval a` on `[-r, r]`, and it is `l1Omega.summable_abs_eval`
for `derivShift a` shifted by one index. -/
theorem l1Weighted.summable_abs_mul_pow_pred (a : l1Weighted ν) {r : ℝ} (hr : 0 ≤ r)
    (hrν : r < (ν : ℝ)) :
    Summable (fun n : ℕ => |l1Weighted.toSeq a n| * (n : ℝ) * r ^ (n - 1)) := by
  have hs := l1Omega.summable_abs_eval (derivShift a)
    (show |r| < (ν : ℝ) by simpa only [abs_of_nonneg hr] using hrν)
  have ht : Summable (fun n : ℕ =>
      |l1Weighted.toSeq a (n + 1)| * ((n : ℝ) + 1) * r ^ n) := by
    refine hs.congr fun n => ?_
    rw [derivShift_apply, abs_mul, abs_of_pos (by positivity : 0 < (n : ℝ) + 1),
      abs_of_nonneg hr]
    ring
  exact (summable_nat_add_iff 1).mp (by simpa only [Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel] using ht)

/-- Evaluate an `ℓ¹_ω` sequence as a power series at `t ∈ ℝ` (defined for every `t` by
`tsum`; convergence is proved for `|t| < ν`, `l1Omega.summable_eval`).
Convergence is strict (`|t| < ν`, not `≤`) because the `(n+1)` factor in `ω_n` doesn't
quite control the boundary. Used to express the time-derivative of `l1Weighted.eval`. -/
def l1Omega.eval (b : l1Omega ν) (t : ℝ) : ℝ :=
  ∑' n, l1Omega.toSeq b n * t ^ n




end Eval

end RadiiPolynomial
