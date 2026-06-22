import RadiiPolynomial.source.lpSpace.lpWeighted
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

lemma omegaWeight_nonneg : 0 ≤ omegaWeight ν n := le_of_lt omegaWeight_pos

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

lemma norm_def (x : OmegaScaledReal ν n) :
    ‖x‖ = |toReal x| * omegaWeight ν n := rfl

@[simp] lemma toReal_apply (x : OmegaScaledReal ν n) : toReal x = x := rfl
@[simp] lemma ofReal_apply (x : ℝ) : (ofReal x : OmegaScaledReal ν n) = x := rfl

end OmegaScaledReal

/-- Omega-weighted `ℓ¹` space: `ℓ¹_ω` with `ω_n = ν^{n+1}/(n+1)`. -/
abbrev l1Omega (ν : PosReal) := lp (OmegaScaledReal ν) 1

namespace l1Omega

variable {ν : PosReal}

instance : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩

-- UniformSpace and CompleteSpace are inherited from lp's NormedAddCommGroup.

/-- Underlying real sequence. -/
def toSeq (a : l1Omega ν) : ℕ → ℝ := fun n => OmegaScaledReal.toReal (a n)

/-- Extensionality through coefficients. -/
lemma ext {a b : l1Omega ν} (h : ∀ n, toSeq a n = toSeq b n) : a = b :=
  lp.ext (funext h)

/-- Membership predicate for omega-weighted `ℓ¹`. -/
def Mem (ν : PosReal) (a : ℕ → ℝ) : Prop :=
  Memℓp (fun n => OmegaScaledReal.ofReal (a n) : ∀ n, OmegaScaledReal ν n) 1

/-- Construct an element from a sequence with finite omega-weighted norm. -/
def mk (a : ℕ → ℝ) (ha : Mem ν a) : l1Omega ν :=
  ⟨fun n => OmegaScaledReal.ofReal (a n), ha⟩

@[simp] lemma toSeq_apply (a : l1Omega ν) (n : ℕ) : toSeq a n = a n := rfl
@[simp] lemma mk_apply (a : ℕ → ℝ) (ha : Mem ν a) (n : ℕ) : toSeq (mk a ha) n = a n := rfl
@[simp] lemma zero_toSeq (n : ℕ) : toSeq (0 : l1Omega ν) n = 0 := rfl
@[simp] lemma neg_toSeq (a : l1Omega ν) (n : ℕ) : toSeq (-a) n = -toSeq a n := rfl
@[simp] lemma add_toSeq (a b : l1Omega ν) (n : ℕ) :
    toSeq (a + b) n = toSeq a n + toSeq b n := rfl
@[simp] lemma sub_toSeq (a b : l1Omega ν) (n : ℕ) :
    toSeq (a - b) n = toSeq a n - toSeq b n := rfl
@[simp] lemma smul_toSeq (c : ℝ) (a : l1Omega ν) (n : ℕ) :
    toSeq (c • a) n = c * toSeq a n := rfl

lemma norm_eq_tsum (a : l1Omega ν) :
    ‖a‖ = ∑' n, |toSeq a n| * OmegaScaledReal.omegaWeight ν n := by
  have h := lp.norm_eq_tsum_rpow (p := (1 : ℝ≥0∞)) (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one] at h
  exact h

lemma mem_iff (a : ℕ → ℝ) :
    Mem ν a ↔ Summable (fun n => |a n| * OmegaScaledReal.omegaWeight ν n) := by
  simp only [Mem, Memℓp, OmegaScaledReal.ofReal_apply, ne_eq]
  simp only [show (1 : ℝ≥0∞) ≠ 0 from one_ne_zero, ENNReal.one_ne_top, ↓reduceIte,
    OmegaScaledReal.norm_def, OmegaScaledReal.toReal_apply, ENNReal.toReal_one, Real.rpow_one]

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

/-- Omega weight bounded by geometric weight: `ω_n ≤ ν^n` for all `n`.
Since `ω_n = ν^{n+1}/(n+1) ≤ ν^{n+1} ≤ ν^n` only when `ν ≤ 1`, we use a
weaker but unconditional bound: `ω_n ≤ ν · ν^n` (factor of ν). -/
lemma omegaWeight_le_nu_mul_pow (n : ℕ) :
    OmegaScaledReal.omegaWeight ν n ≤ (ν : ℝ) * (ν : ℝ) ^ n := by
  unfold OmegaScaledReal.omegaWeight
  rw [pow_succ, mul_comm ((ν : ℝ) ^ n) (ν : ℝ)]
  exact div_le_self (mul_nonneg ν.coe_nonneg (pow_nonneg ν.coe_nonneg _))
    (Nat.one_le_cast.mpr (Nat.succ_pos n))

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

/-- If `a ∈ ℓ¹_ν`, then `a ∈ ℓ¹_ω` (with norm bounded by `ν · ‖a‖_ν`).
Since `ω_n ≤ ν · ν^n`, geometric summability implies omega summability. -/
lemma l1Omega.geom_to_omega_mem (a : l1Weighted ν) :
    l1Omega.Mem ν (l1Weighted.toSeq a) := by
  rw [l1Omega.mem_iff]
  apply Summable.of_nonneg_of_le
  · intro n; exact mul_nonneg (abs_nonneg _) OmegaScaledReal.omegaWeight_nonneg
  · intro n
    exact mul_le_mul_of_nonneg_left (omegaWeight_le_nu_mul_pow n) (abs_nonneg _)
  · have hsm := ((l1Weighted.mem_iff (ν := ν) (l1Weighted.toSeq a)).mp a.toLp.2).mul_left (ν : ℝ)
    simp_rw [show ∀ n, (ν : ℝ) * (|l1Weighted.toSeq a n| * (ν : ℝ) ^ n) =
      |l1Weighted.toSeq a n| * ((ν : ℝ) * (ν : ℝ) ^ n) from fun n => by ring] at hsm
    exact hsm

/-- `ℓ¹_ω` membership is closed under subtraction. -/
lemma l1Omega.mem_sub {f g : ℕ → ℝ} (hf : l1Omega.Mem ν f) (hg : l1Omega.Mem ν g) :
    l1Omega.Mem ν (fun n => f n - g n) := by
  rw [l1Omega.mem_iff] at hf hg ⊢
  refine (hf.add hg).of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) OmegaScaledReal.omegaWeight_nonneg)
    fun n => ?_
  have hab : |f n - g n| ≤ |f n| + |g n| :=
    abs_le.mpr ⟨by linarith [neg_abs_le (f n), le_abs_self (g n)],
      by linarith [le_abs_self (f n), neg_abs_le (g n)]⟩
  exact (mul_le_mul_of_nonneg_right hab OmegaScaledReal.omegaWeight_nonneg).trans_eq
    (add_mul _ _ _)

end Bridges

section Shift

variable {ν : PosReal}

/-- Right-shift sequence: `(S a)_0 = 0`, `(S a)_{k+1} = a_k`.
Ref: §8.2, eq. (8.25). -/
private def shift_seq (a : l1Weighted ν) : ℕ → ℝ
  | 0 => 0
  | n + 1 => l1Weighted.toSeq a n

private lemma shift_mem (a : l1Weighted ν) : l1Weighted.Mem ν (shift_seq a) := by
  rw [l1Weighted.mem_iff, ← summable_nat_add_iff (k := 1)]
  have h : ∀ n, |shift_seq a (n + 1)| * (ν : ℝ) ^ (n + 1) =
      (ν : ℝ) * (|l1Weighted.toSeq a n| * (ν : ℝ) ^ n) := by
    intro n; simp only [shift_seq, pow_succ]; ring
  simp_rw [h]
  exact (l1Weighted.summable_weighted a).mul_left _

/-- The right-shift operator on `l1Weighted ν`.
Ref: §8.2, eq. (8.25) — `(S a)_k = a_{k-1}` for `k ≥ 1`, zero at `k = 0`.
Bounded: `‖S a‖ ≤ ν · ‖a‖`. -/
noncomputable def shift (a : l1Weighted ν) : l1Weighted ν :=
  l1Weighted.mk (shift_seq a) (shift_mem a)

@[simp] lemma shift_zero_mode (a : l1Weighted ν) :
    l1Weighted.toSeq (shift a) 0 = 0 := by
  simp [shift, shift_seq, l1Weighted.toSeq, l1Weighted.toSeq, l1Weighted.mk]

@[simp] lemma shift_succ_mode (a : l1Weighted ν) (n : ℕ) :
    l1Weighted.toSeq (shift a) (n + 1) = l1Weighted.toSeq a n := by
  simp [shift, shift_seq, l1Weighted.toSeq, l1Weighted.toSeq, l1Weighted.mk]

private lemma shift_toSeq (a : l1Weighted ν) (n : ℕ) :
    l1Weighted.toSeq (shift a) n = shift_seq a n := by
  simp [shift, l1Weighted.toSeq, l1Weighted.mk]

lemma shift_linear_add (a b : l1Weighted ν) :
    shift (a + b) = shift a + shift b := by
  apply l1Weighted.ext; intro n
  simp only [shift_toSeq, l1Weighted.add_toSeq]
  cases n with
  | zero => simp [shift_seq]
  | succ n => rfl

lemma shift_linear_smul (r : ℝ) (a : l1Weighted ν) :
    shift (r • a) = r • shift a := by
  apply l1Weighted.ext; intro n
  simp only [shift_toSeq, l1Weighted.smul_toSeq]
  cases n with
  | zero => simp [shift_seq]
  | succ n => rfl

lemma shift_norm_le (a : l1Weighted ν) :
    ‖shift a‖ ≤ (ν : ℝ) * ‖a‖ := by
  rw [l1Weighted.norm_eq_tsum, l1Weighted.norm_eq_tsum]
  conv_lhs => arg 1; ext n; rw [show l1Weighted.toSeq (shift a) n = shift_seq a n
    from shift_toSeq a n]
  have hsumm : Summable (fun n => |shift_seq a n| * (ν : ℝ) ^ n) :=
    (l1Weighted.mem_iff _).mp (shift_mem a)
  have hb : Summable (fun n => |l1Weighted.toSeq a n| * (ν : ℝ) ^ n) :=
    l1Weighted.summable_weighted a
  rw [hsumm.tsum_eq_zero_add]
  simp only [shift_seq, abs_zero, zero_mul, zero_add]
  rw [← tsum_mul_left]
  exact ((summable_nat_add_iff (k := 1)).mpr hsumm).tsum_le_tsum
    (fun n => le_of_eq (by simp only [pow_succ]; ring))
    (hb.mul_left _)

/-- The right-shift operator as a CLM on `l1Weighted ν`.
Ref: §8.2, eq. (8.25) — `‖S‖ = ν`. -/
noncomputable def shift_CLM : l1Weighted ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := shift
      map_add' := shift_linear_add
      map_smul' := fun r a => by simp [shift_linear_smul] }
    (ν : ℝ)
    shift_norm_le

@[simp] lemma shift_CLM_apply (a : l1Weighted ν) :
    shift_CLM a = shift a := rfl

end Shift

section ShiftDivN

variable {ν : PosReal}

/-- The shift-and-divide operator: maps sequence `b` to `{0, b_0/1, b_1/2, b_2/3, ...}`.
This is the key IVP tail operator: `(shift_div_n b)_n = b_{n-1}/n` for `n ≥ 1`, zero at `n = 0`.
Bounded: `‖shift_div_n b‖ ≤ ν · ‖b‖` since `|b_{n-1}|/n · ν^n ≤ |b_{n-1}| · ν^n ≤ ν · |b_{n-1}| · ν^{n-1}`. -/
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

@[simp] lemma shiftDivN_zero_mode (b : l1Weighted ν) :
    l1Weighted.toSeq (shiftDivN b) 0 = 0 := by
  simp [shiftDivN, shiftDivN_seq, l1Weighted.toSeq, l1Weighted.toSeq, l1Weighted.mk]

@[simp] lemma shiftDivN_succ_mode (b : l1Weighted ν) (n : ℕ) :
    l1Weighted.toSeq (shiftDivN b) (n + 1) =
      l1Weighted.toSeq b n / (↑(n + 1) : ℝ) := by
  simp [shiftDivN, shiftDivN_seq, l1Weighted.toSeq, l1Weighted.toSeq, l1Weighted.mk]

private lemma shiftDivN_toSeq (b : l1Weighted ν) (n : ℕ) :
    l1Weighted.toSeq (shiftDivN b) n = shiftDivN_seq b n := by
  simp [shiftDivN, l1Weighted.toSeq, l1Weighted.mk]

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

/-- Tail of `shiftDivN b` starting from mode `N+1` is bounded by `ν/(N+1) · ‖b‖`.
This is tighter than the full norm bound `‖shiftDivN b‖ ≤ ν · ‖b‖` because
on tail modes `1/n ≤ 1/(N+1)`. Used for IVP Z₁ tail error bounds. -/
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

end ShiftDivN

section LambdaN

variable {ν : PosReal}

/-- Tail divide-by-index sequence: 0 for `k ≤ N`, `a_k / k` for `k ≥ N + 1`.
Ref: §8.2, eq. (8.26). -/
private def lambdaN_seq (N : ℕ) (a : l1Weighted ν) (n : ℕ) : ℝ :=
  if N < n then l1Weighted.toSeq a n / (n : ℝ) else 0

private lemma lambdaN_mem (N : ℕ) (a : l1Weighted ν) :
    l1Weighted.Mem ν (lambdaN_seq N a) := by
  rw [l1Weighted.mem_iff]
  refine (l1Weighted.summable_weighted a).of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _))
    fun n => ?_
  simp only [lambdaN_seq]
  split_ifs with hn
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr (by omega)
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg ν.2.le _)
    rw [abs_div, abs_of_pos (lt_of_lt_of_le one_pos hn1)]
    exact div_le_self (abs_nonneg _) hn1
  · simp only [abs_zero, zero_mul]
    exact mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _)

/-- Tail divide-by-index operator on `l1Weighted ν`.
Ref: §8.2, eq. (8.26) — `(Λ_N a)_k = 0` for `k ≤ N`, `a_k / k` for `k ≥ N + 1`.
Bounded: `‖Λ_N a‖ ≤ 1/(N+1) · ‖a‖` (Lemma 8.2.4). -/
noncomputable def lambdaN (N : ℕ) (a : l1Weighted ν) : l1Weighted ν :=
  l1Weighted.mk (lambdaN_seq N a) (lambdaN_mem N a)

@[simp] lemma lambdaN_le_mode (N : ℕ) (a : l1Weighted ν) (n : ℕ) (hn : n ≤ N) :
    l1Weighted.toSeq (lambdaN N a) n = 0 := by
  simp [lambdaN, lambdaN_seq, l1Weighted.toSeq, l1Weighted.toSeq, l1Weighted.mk,
    not_lt.mpr hn]

@[simp] lemma lambdaN_gt_mode (N : ℕ) (a : l1Weighted ν) (n : ℕ) (hn : N < n) :
    l1Weighted.toSeq (lambdaN N a) n = l1Weighted.toSeq a n / (n : ℝ) := by
  simp [lambdaN, lambdaN_seq, l1Weighted.toSeq, l1Weighted.toSeq, l1Weighted.mk, hn]

private lemma lambdaN_toSeq (N : ℕ) (a : l1Weighted ν) (n : ℕ) :
    l1Weighted.toSeq (lambdaN N a) n = lambdaN_seq N a n := by
  simp [lambdaN, l1Weighted.toSeq, l1Weighted.mk]

lemma lambdaN_linear_add (N : ℕ) (a b : l1Weighted ν) :
    lambdaN N (a + b) = lambdaN N a + lambdaN N b := by
  apply l1Weighted.ext; intro n
  simp only [lambdaN_toSeq, l1Weighted.add_toSeq, lambdaN_seq]
  split_ifs <;> simp [add_div]

lemma lambdaN_linear_smul (N : ℕ) (r : ℝ) (a : l1Weighted ν) :
    lambdaN N (r • a) = r • lambdaN N a := by
  apply l1Weighted.ext; intro n
  simp only [lambdaN_toSeq, l1Weighted.smul_toSeq, lambdaN_seq]
  split_ifs <;> simp [mul_div_assoc]

lemma lambdaN_norm_le (N : ℕ) (a : l1Weighted ν) :
    ‖lambdaN N a‖ ≤ 1 / (↑(N + 1) : ℝ) * ‖a‖ := by
  unfold lambdaN
  refine l1Weighted.norm_mk_le_of_pointwise _ _ a _ fun n => ?_
  simp only [lambdaN_seq]
  split_ifs with hn
  · have hn1 : (0 : ℝ) < ↑(N + 1) := by positivity
    have hle : (↑(N + 1) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (by omega)
    have hn_pos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hn1 hle
    rw [abs_div, abs_of_pos hn_pos]
    calc |l1Weighted.toSeq a n| / (n : ℝ)
        = |l1Weighted.toSeq a n| * ((n : ℝ)⁻¹) := div_eq_mul_inv _ _
      _ ≤ |l1Weighted.toSeq a n| * ((↑(N + 1) : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left (by rwa [inv_le_inv₀ hn_pos hn1]) (abs_nonneg _)
      _ = 1 / (↑(N + 1) : ℝ) * |l1Weighted.toSeq a n| := by rw [one_div]; ring
  · simp only [abs_zero]
    exact mul_nonneg (by positivity) (abs_nonneg _)

/-- Tail divide-by-index as a CLM on `l1Weighted ν`.
Ref: §8.2, eq. (8.26) — `‖Λ_N‖ ≤ 1/(N+1)` (Lemma 8.2.4). -/
noncomputable def lambdaN_CLM (N : ℕ) : l1Weighted ν →L[ℝ] l1Weighted ν :=
  LinearMap.mkContinuous
    { toFun := lambdaN N
      map_add' := lambdaN_linear_add N
      map_smul' := fun r a => by simp [lambdaN_linear_smul] }
    (1 / (↑(N + 1) : ℝ))
    (lambdaN_norm_le N)

@[simp] lemma lambdaN_CLM_apply (N : ℕ) (a : l1Weighted ν) :
    lambdaN_CLM N a = lambdaN N a := rfl

end LambdaN

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
`d/dt eval(a, t) = eval(D a, t)` for `|t| < ν` (proved in `Eval.lean`).
Ref: Proposition 8.1.5. -/
noncomputable def derivShift (a : l1Weighted ν) : l1Omega ν :=
  l1Omega.mk (derivShift_seq a) (derivShift_mem a)

@[simp] lemma derivShift_apply (a : l1Weighted ν) (n : ℕ) :
    l1Omega.toSeq (derivShift a) n = ((n : ℝ) + 1) * l1Weighted.toSeq a (n + 1) := rfl

lemma derivShift_linear_add (a b : l1Weighted ν) :
    derivShift (a + b) = derivShift a + derivShift b := by
  apply l1Omega.ext; intro n
  show ((n : ℝ) + 1) * l1Weighted.toSeq (a + b) (n + 1) =
       ((n : ℝ) + 1) * l1Weighted.toSeq a (n + 1) +
       ((n : ℝ) + 1) * l1Weighted.toSeq b (n + 1)
  rw [l1Weighted.add_toSeq]; ring

lemma derivShift_linear_smul (r : ℝ) (a : l1Weighted ν) :
    derivShift (r • a) = r • derivShift a := by
  apply l1Omega.ext; intro n
  show ((n : ℝ) + 1) * l1Weighted.toSeq (r • a) (n + 1) =
       r * (((n : ℝ) + 1) * l1Weighted.toSeq a (n + 1))
  rw [l1Weighted.smul_toSeq]; ring

lemma derivShift_norm_le (a : l1Weighted ν) :
    ‖derivShift a‖ ≤ ‖a‖ := by
  rw [l1Omega.norm_eq_tsum, l1Weighted.norm_eq_tsum]
  -- Each term: |D(a)_n| · ω_n = (n+1)·|a_{n+1}|·ω_n = |a_{n+1}|·ν^{n+1}
  have h_term_eq : ∀ n, |l1Omega.toSeq (derivShift a) n| * OmegaScaledReal.omegaWeight ν n
                  = |l1Weighted.toSeq a (n + 1)| * (ν : ℝ) ^ (n + 1) := fun n => by
    have hcast : (n : ℝ) + 1 = ↑(n + 1) := by push_cast; ring
    have hpos : (0 : ℝ) < ↑(n + 1) := by positivity
    rw [derivShift_apply, hcast, abs_mul, abs_of_pos hpos,
        mul_comm (↑(n + 1) : ℝ) _, mul_assoc, omegaWeight_mul_index]
  have hb : Summable (fun n => |l1Weighted.toSeq a n| * (ν : ℝ) ^ n) :=
    l1Weighted.summable_weighted a
  rw [show (fun n => |l1Omega.toSeq (derivShift a) n| * OmegaScaledReal.omegaWeight ν n) =
      (fun n => |l1Weighted.toSeq a (n + 1)| * (ν : ℝ) ^ (n + 1)) from funext h_term_eq]
  -- Σ |a_{n+1}|·ν^{n+1} = (Σ |a_n|·ν^n) - |a_0|·ν^0 ≤ Σ |a_n|·ν^n
  rw [hb.tsum_eq_zero_add]
  linarith [mul_nonneg (abs_nonneg (l1Weighted.toSeq a 0)) (pow_nonneg ν.2.le 0)]

/-- The derivative-shift operator as a CLM `ℓ¹_ν →L[ℝ] ℓ¹_ω`.
Operator norm ≤ 1.
Ref: Proposition 8.1.5. -/
noncomputable def derivShift_CLM : l1Weighted ν →L[ℝ] l1Omega ν :=
  LinearMap.mkContinuous
    { toFun := derivShift
      map_add' := derivShift_linear_add
      map_smul' := fun r a => by simp [derivShift_linear_smul] }
    1
    (fun a => by rw [one_mul]; exact derivShift_norm_le a)

@[simp] lemma derivShift_CLM_apply (a : l1Weighted ν) :
    derivShift_CLM a = derivShift a := rfl

end DerivShift

section Eval

variable {ν : PosReal}

/-- Summability of `Σ |b_n| · |t|^n` for `b ∈ ℓ¹_ω` and `|t| < ν` (strict).
The bound `(n+1) · (|t|/ν)^n` is used as the conversion factor between `ω_n` and `|t|^n`. -/
theorem l1Omega.summable_eval (b : l1Omega ν) {t : ℝ} (ht : |t| < ν) :
    Summable fun n => l1Omega.toSeq b n * t ^ n := by
  have hν : (0 : ℝ) < ν := ν.2
  set r : ℝ := |t| / ν with hr_def
  have hr_lt : r < 1 := (div_lt_one hν).mpr ht
  have hr_nn : (0 : ℝ) ≤ r := div_nonneg (abs_nonneg _) hν.le
  have hr_norm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]; exact hr_lt
  -- Σ (n+1) · r^n is summable for r < 1
  have h_geom_summable : Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
    have h_n : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
      simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one (k := 1) hr_norm
    have h_0 : Summable (fun n : ℕ => r ^ n) :=
      summable_geometric_of_lt_one hr_nn hr_lt
    refine (h_n.add h_0).congr fun n => ?_
    ring
  -- Each term bounded by the tsum
  set M : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) * r ^ n with hM_def
  have h_term_le : ∀ n : ℕ, ((n : ℝ) + 1) * r ^ n ≤ M :=
    fun n => h_geom_summable.le_tsum n (fun k _ => by positivity)
  -- Bound |b_n · t^n| by (M/ν) · (|b_n| · ω_n)
  refine Summable.of_norm_bounded
    (g := fun n => (M / ν) * (|l1Omega.toSeq b n| * OmegaScaledReal.omegaWeight ν n))
    (((l1Omega.mem_iff _).mp b.2).mul_left (M / ν)) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  -- Want: |b_n| · |t|^n ≤ M/ν · |b_n| · ω_n
  -- ω_n = ν^{n+1}/(n+1), and (n+1) · r^n ≤ M ⟹ |t|^n ≤ M/ν · ω_n
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hbn_nn : 0 ≤ |l1Omega.toSeq b n| := abs_nonneg _
  have h_t_pow_eq : |t|^n = r^n * (ν : ℝ)^n := by
    rw [hr_def, div_pow, div_mul_cancel₀ _ (pow_ne_zero n hν.ne')]
  -- |t|^n ≤ M · ν^n / (n+1)
  have h_t_le : |t|^n ≤ M * (ν : ℝ)^n / ((n : ℝ) + 1) := by
    rw [h_t_pow_eq, le_div_iff₀ hn1]
    have heq : r^n * (ν : ℝ)^n * ((n : ℝ) + 1) = (((n : ℝ) + 1) * r^n) * (ν : ℝ)^n := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (h_term_le n) (pow_nonneg hν.le n)
  calc |l1Omega.toSeq b n| * |t|^n
      ≤ |l1Omega.toSeq b n| * (M * (ν : ℝ)^n / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h_t_le hbn_nn
    _ = M / ν * (|l1Omega.toSeq b n| * OmegaScaledReal.omegaWeight ν n) := by
        unfold OmegaScaledReal.omegaWeight
        rw [pow_succ]
        field_simp
        push_cast
        ring

/-- Absolute summability for `ℓ¹_ω` evaluation, used as a uniform bound on the disk. -/
theorem l1Omega.summable_abs_eval (b : l1Omega ν) {t : ℝ} (ht : |t| < ν) :
    Summable fun n => |l1Omega.toSeq b n| * |t| ^ n := by
  have h := l1Omega.summable_eval b (t := |t|) (by rwa [abs_abs])
  refine (h.abs).congr fun n => ?_
  rw [abs_mul, abs_pow, abs_abs]

/-- Evaluate an `ℓ¹_ω` sequence as a power series at `t ∈ ℝ` with `|t| < ν`.
Convergence is strict (`|t| < ν`, not `≤`) because the `(n+1)` factor in `ω_n` doesn't
quite control the boundary. Used to express the time-derivative of `l1Weighted.eval`. -/
def l1Omega.eval (b : l1Omega ν) (t : ℝ) : ℝ :=
  ∑' n, l1Omega.toSeq b n * t ^ n

theorem l1Omega.eval_at_zero (b : l1Omega ν) : l1Omega.eval b 0 = l1Omega.toSeq b 0 := by
  unfold l1Omega.eval
  rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp

theorem l1Omega.eval_add (b c : l1Omega ν) {t : ℝ} (ht : |t| < ν) :
    l1Omega.eval (b + c) t = l1Omega.eval b t + l1Omega.eval c t := by
  show ∑' n, l1Omega.toSeq (b + c) n * t ^ n =
       (∑' n, l1Omega.toSeq b n * t ^ n) + ∑' n, l1Omega.toSeq c n * t ^ n
  simp_rw [show ∀ n, l1Omega.toSeq (b + c) n = l1Omega.toSeq b n + l1Omega.toSeq c n
    from l1Omega.add_toSeq b c, add_mul]
  exact (l1Omega.summable_eval b ht).tsum_add (l1Omega.summable_eval c ht)

theorem l1Omega.eval_smul (r : ℝ) (b : l1Omega ν) (t : ℝ) :
    l1Omega.eval (r • b) t = r * l1Omega.eval b t := by
  show ∑' n, l1Omega.toSeq (r • b) n * t ^ n = r * ∑' n, l1Omega.toSeq b n * t ^ n
  simp_rw [show ∀ n, l1Omega.toSeq (r • b) n = r * l1Omega.toSeq b n
    from l1Omega.smul_toSeq r b, mul_assoc]
  rw [tsum_mul_left]

end Eval

end RadiiPolynomial
