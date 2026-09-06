import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Algebra
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import RadiiPolynomial.Operators.BlockDiagonal.WeightedL1
import RadiiPolynomial.Core.Theorem

/-!
# Chebyshev IVP Operator

Equation-independent definitions for Chebyshev-series IVP zero-finding (Ref: Eq. 14.11).

## The Chebyshev IVP Zero-Finding Problem

Given `u̇ = f(u)` on `[-1,1]` with `u(-1) = p`, the Chebyshev coefficient zero-finding map is:

```
  F(a)_{l,0}   = p_l - (a_l)_0 - 2 ∑_{n≥1} (-1)^n (a_l)_n
  F(a)_{l,k}   = 2k · (a_l)_k + (c_l)_{k+1} - (c_l)_{k-1}    (k ≥ 1)
```

where `c_l = φ_l(a)` encodes the nonlinearity `f` at the coefficient level via bilateral
Cauchy products, and the `2k` factor comes from the Chebyshev derivative formula `T'_k(t)`.

## Key differences from Taylor IVP (Eq. 8.15)

- Index space: ℤ-indexed (bilateral) domain, ℕ-indexed output
- Mode 0: alternating sum `∑ (-1)^n a_n` (evaluation at `t = -1`) vs simple `a_0 - x_0`
- Modes k ≥ 1: couples `c_{k+1} - c_{k-1}` (Chebyshev integration) vs `(k+1)a_{k+1} - c_k`
-/

open scoped BigOperators Topology NNReal ENNReal
open RadiiPolynomial

noncomputable section

namespace ChebyshevIVP

variable {ν : PosReal} {L : ℕ} [NeZero L] [Fact (1 ≤ (ν : ℝ))]

/-! ## System Space -/

/-- Chebyshev system space: `L` components of `l1Chebyshev ν` sequences. -/
abbrev XCheb (ν : PosReal) (L : ℕ) [Fact (1 ≤ (ν : ℝ))] :=
  Fin L → l1Chebyshev ν

/-! ## Summability Helpers -/

/-- Absolute values of `l1Chebyshev` coefficients are summable (from ℓ¹ membership). -/
theorem summable_abs_toSeq (a : l1Chebyshev ν) :
    Summable (fun k : ℤ => |l1Chebyshev.toSeq a k|) :=
  lpOneAlg.summable_abs_toRealSeq a

/-- The alternating sum `∑_{n≥1} (-1)^n a_n` converges for `a ∈ l1Chebyshev ν`.
This is the Chebyshev series evaluated at `t = -1`: `u(-1) = a_0 + 2∑ (-1)^n a_n`. -/
theorem summable_alternating_toSeq (a : l1Chebyshev ν) :
    Summable (fun n : ℕ => (-1 : ℝ) ^ (n + 1) * l1Chebyshev.toSeq a (↑(n + 1) : ℤ)) := by
  have habs : Summable (fun n : ℕ => |l1Chebyshev.toSeq a (↑(n + 1) : ℤ)|) :=
    (summable_abs_toSeq a).comp_injective (fun n m h => by omega)
  exact habs.of_norm_bounded fun n => by
    simp [Real.norm_eq_abs]

/-! ## IVP Coefficient Formula (Eq. 14.11) -/

/-- Chebyshev IVP zero-finding coefficients (Ref: Eq. 14.11, p.328).

- `F(a)_{l,0} = p_l - (a_l)_0 - 2 ∑_{n≥1} (-1)^n (a_l)_n`
- `F(a)_{l,k+1} = 2(k+1) · (a_l)_{k+1} + (c_l)_{k+2} - (c_l)_k`

where `c_l = φ_l(a)` is the nonlinearity at the coefficient level.

The output is ℕ-indexed: the IVP operator maps ℤ-indexed Chebyshev sequences
to ℕ-indexed coefficient equations. -/
def chebyshevIvpCoeffs
    (φ : XCheb ν L → Fin L → l1Chebyshev ν)
    (p : Fin L → ℝ)
    (a : XCheb ν L) (l : Fin L) : ℕ → ℝ
  | 0 => p l - l1Chebyshev.toSeq (a l) 0 -
      2 * ∑' (n : ℕ), (-1 : ℝ) ^ (n + 1) * l1Chebyshev.toSeq (a l) (↑(n + 1) : ℤ)
  | k + 1 => 2 * ((k : ℝ) + 1) * l1Chebyshev.toSeq (a l) (↑(k + 1) : ℤ) +
      l1Chebyshev.toSeq (φ a l) (↑(k + 2) : ℤ) -
      l1Chebyshev.toSeq (φ a l) (↑k : ℤ)

/-! ## Chebyshev Shift-Divide Operator

The Chebyshev analogue of `shiftDivN`: integrates Chebyshev coefficients.

For `k ≥ 1`: `(chebyshevShiftDiv c)_k = (c_{k+1} - c_{k-1}) / (2k)`
For `k ≤ 0`: `(chebyshevShiftDiv c)_k = 0`

This arises from the Chebyshev integration formula:
`∫ T_k(s) ds = (T_{k+1}/(k+1) - T_{k-1}/(k-1)) / 2` for `k ≥ 2`.

On tail modes `k > N`, the composed map `G(a)_k = a_k + chebyshevShiftDiv(φ(a))_k`. -/

/-- The raw shift-divide sequence for Chebyshev integration. -/
private def chebyshevShiftDiv_seq (c : l1Chebyshev ν) : ℤ → ℝ
  | (k : ℕ) =>
    if k = 0 then 0
    else (l1Chebyshev.toSeq c (↑k + 1) - l1Chebyshev.toSeq c (↑k - 1)) / (2 * (k : ℝ))
  | (Int.negSucc _) => 0

omit [Fact (1 ≤ (ν : ℝ))] in
@[simp] lemma chebyshevShiftDiv_seq_zero (c : l1Chebyshev ν) :
    chebyshevShiftDiv_seq c 0 = 0 := by simp [chebyshevShiftDiv_seq]

omit [Fact (1 ≤ (ν : ℝ))] in
@[simp] lemma chebyshevShiftDiv_seq_neg (c : l1Chebyshev ν) (n : ℕ) :
    chebyshevShiftDiv_seq c (Int.negSucc n) = 0 := by simp [chebyshevShiftDiv_seq]

omit [Fact (1 ≤ (ν : ℝ))] in
@[simp] lemma chebyshevShiftDiv_seq_pos (c : l1Chebyshev ν) (k : ℕ) (hk : k ≠ 0) :
    chebyshevShiftDiv_seq c (↑k) =
      (l1Chebyshev.toSeq c (↑k + 1) - l1Chebyshev.toSeq c (↑k - 1)) / (2 * (k : ℝ)) := by
  simp [chebyshevShiftDiv_seq, hk]

/-! ### Membership and norm bound for chebyshevShiftDiv

Per-element bound for `k ≥ 1`:
```
  |(c_{k+1} - c_{k-1}) / (2k)| * ν^k
    ≤ |c_{k+1}| * ν^k / (2k) + |c_{k-1}| * ν^k / (2k)
    ≤ (1/(2ν)) * ‖c_{k+1}‖_fiber + (ν/2) * ‖c_{k-1}‖_fiber
```
where `‖c_m‖_fiber = |c_m| * ν^{|m|}`. Both are subsequences of `‖c‖`.

Operator norm: `‖chebyshevShiftDiv c‖ ≤ ν * ‖c‖` (since `1/(2ν) + ν/2 ≤ ν` for `ν ≥ 1`).
-/

omit [Fact (1 ≤ (ν : ℝ))] in
/-- Shifted subseries of `l1Chebyshev` norms are summable (shift invariance). -/
private lemma summable_norm_shift (c : l1Chebyshev ν) (s : ℤ) :
    Summable (fun n : ℕ => ‖c (↑n + s)‖) :=
  (lpOneAlg.summable_norm c).comp_injective (fun n m h => by omega)

-- Per-element bound: |(a-b)/(2k)| * ν^k ≤ (ν/2)*(‖c(k+1)‖ + ‖c(k-1)‖).
private lemma chebyshevShiftDiv_fiber_le (c : l1Chebyshev ν) (k : ℕ) (hk : 0 < k) :
    ‖lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑k)
      (chebyshevShiftDiv_seq c (↑k))‖ ≤
    (ν : ℝ) / 2 * (‖c ((↑k : ℤ) + 1)‖ + ‖c ((↑k : ℤ) + (-1))‖) := by
  -- Unfold to real arithmetic
  rw [chebyshevShiftDiv_seq_pos c k (by omega)]
  simp only [ScaledRealZ.norm_lpAlgRingData_ofReal]
  rw [abs_div, abs_of_pos (show (0:ℝ) < 2 * (k:ℝ) by positivity)]
  rw [lpOneAlg.norm_eq_abs_toReal_mul_weight c ((↑k : ℤ) + 1),
      lpOneAlg.norm_eq_abs_toReal_mul_weight c ((↑k : ℤ) + (-1))]
  simp only [ScaledRealZ.norm_lpAlgRingData_ofReal, abs_one, one_mul]
  have hk1 : ((↑k : ℤ) + 1).natAbs = k + 1 := by omega
  have hk2 : ((↑k : ℤ) + (-1)).natAbs = k - 1 := by omega
  have hk0' : (↑k : ℤ).natAbs = k := by omega
  rw [hk1, hk2, hk0']
  -- Now goal is pure ℝ arithmetic with abs, pow, div
  set a := |lpOneAlg.toRealSeq c ((↑k : ℤ) + 1)|
  set b := |lpOneAlg.toRealSeq c ((↑k : ℤ) + (-1))|
  -- Key facts for nlinarith
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have hν1 : (1 : ℝ) ≤ ν := Fact.out
  have hν0 : (0 : ℝ) < ν := ν.2
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have htri : |lpOneAlg.toRealSeq c ((↑k : ℤ) + 1) -
      lpOneAlg.toRealSeq c ((↑k : ℤ) + (-1))| ≤ a + b := by
    have := norm_sub_le (lpOneAlg.toRealSeq c ((↑k : ℤ) + 1))
      (lpOneAlg.toRealSeq c ((↑k : ℤ) + (-1)))
    simp only [Real.norm_eq_abs] at this; exact this
  have hpk : (0 : ℝ) < (ν : ℝ) ^ k := pow_pos hν0 _
  have hpk_le : (ν : ℝ) ^ k ≤ (ν : ℝ) ^ (k + 1) :=
    pow_le_pow_right₀ hν1 (by omega)
  have heq : (ν : ℝ) ^ (k - 1) * ν = (ν : ℝ) ^ k := by
    rw [← pow_succ]; congr 1; omega
  -- Clear denominators and finish
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * k) two_pos]
  -- Goal: |x-y| * ν^k * 2 ≤ ν * (a * ν^{k+1} + b * ν^{k-1}) * (2*k)
  -- Key: (a+b)*ν^k ≤ a*ν^{k+2} + b*ν^k ≤ k*(a*ν^{k+2}+b*ν^k) = k*ν*(a*ν^{k+1}+b*ν^{k-1})
  have h1 : |lpOneAlg.toRealSeq c ((↑k : ℤ) + 1) - lpOneAlg.toRealSeq c ((↑k : ℤ) + (-1))| *
      (ν : ℝ) ^ k ≤ (a + b) * (ν : ℝ) ^ k :=
    mul_le_mul_of_nonneg_right htri hpk.le
  have h2 : a * (ν : ℝ) ^ k ≤ a * (ν : ℝ) ^ (k + 1) :=
    mul_le_mul_of_nonneg_left hpk_le ha
  have h3 : (ν : ℝ) * (b * (ν : ℝ) ^ (k - 1)) = b * (ν : ℝ) ^ k := by
    linear_combination b * heq
  have h4 : (ν : ℝ) * (ν : ℝ) ^ (k + 1) = (ν : ℝ) ^ (k + 2) :=
    (mul_comm _ _).trans (pow_succ (ν : ℝ) (k + 1)).symm
  have h5 : a * (ν : ℝ) ^ k ≤ a * (ν : ℝ) ^ (k + 2) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hν1 (by omega)) ha
  -- Expand RHS: ν*(a*ν^{k+1}+b*ν^{k-1}) = a*ν^{k+2}+b*ν^k
  have h6 : (ν : ℝ) * (a * (ν : ℝ) ^ (k + 1) + b * (ν : ℝ) ^ (k - 1)) =
      a * (ν : ℝ) ^ (k + 2) + b * (ν : ℝ) ^ k := by linear_combination a * h4 + h3
  -- Chain: LHS ≤ (a+b)*ν^k * 2 ≤ (a*ν^{k+2}+b*ν^k) * 2 ≤ ... * (2k)
  have h7 : a * (ν : ℝ) ^ (k + 2) + b * (ν : ℝ) ^ k ≥ 0 :=
    add_nonneg (mul_nonneg ha (pow_nonneg hν0.le _)) (mul_nonneg hb (pow_nonneg hν0.le _))
  -- Step-by-step chain avoiding nlinarith on products
  -- (1) |..|*ν^k*2 ≤ (a+b)*ν^k*2
  have s1 : |lpOneAlg.toRealSeq c ((↑k : ℤ) + 1) - lpOneAlg.toRealSeq c ((↑k : ℤ) + (-1))| *
      (ν : ℝ) ^ k * 2 ≤ (a + b) * (ν : ℝ) ^ k * 2 := by linarith [h1]
  -- (2) (a+b)*ν^k ≤ a*ν^{k+2}+b*ν^k
  have s2 : (a + b) * (ν : ℝ) ^ k ≤ a * (ν : ℝ) ^ (k + 2) + b * (ν : ℝ) ^ k := by linarith [h5]
  -- (3) ...*(2) ≤ ...*2k
  have s3 : (a * (ν : ℝ) ^ (k + 2) + b * (ν : ℝ) ^ k) * 2 ≤
      (a * (ν : ℝ) ^ (k + 2) + b * (ν : ℝ) ^ k) * (2 * ↑k) :=
    mul_le_mul_of_nonneg_left (by linarith [hk1']) h7
  -- (4) Chain via calc
  calc |lpOneAlg.toRealSeq c ((↑k : ℤ) + 1) -
          lpOneAlg.toRealSeq c ((↑k : ℤ) + (-1))| * (ν : ℝ) ^ k * 2
      ≤ (a + b) * (ν : ℝ) ^ k * 2 := s1
    _ ≤ (a * (ν : ℝ) ^ (k + 2) + b * (ν : ℝ) ^ k) * 2 := by linarith [s2]
    _ ≤ (a * (ν : ℝ) ^ (k + 2) + b * (ν : ℝ) ^ k) * (2 * ↑k) := s3
    _ = (ν : ℝ) * (a * (ν : ℝ) ^ (k + 1) + b * (ν : ℝ) ^ (k - 1)) * (2 * ↑k) := by
        linear_combination -(2 * (↑k : ℝ)) * h6


private lemma chebyshevShiftDiv_memℓp (c : l1Chebyshev ν) :
    Memℓp (fun k : ℤ => lpAlgRingData.ofReal (E := ScaledRealZ ν) k
      (chebyshevShiftDiv_seq c k)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  have h1 := lpOneAlg.summable_norm_shift c (1 : ℤ)
  have h2 := lpOneAlg.summable_norm_shift c (-1 : ℤ)
  have hsum := h1.add h2
  -- Each ‖shifted(k)‖ ≤ (ν/2)*(‖c(k+1)‖+‖c(k-1)‖) ≤ ν*(‖c(k+1)‖+‖c(k-1)‖)
  -- Bound by ν * summable, which is summable
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (hsum.const_smul (ν : ℝ))
  -- Goal: ‖shifted(k)‖ ≤ ν • (‖c(k+1)‖ + ‖c(k+(-1))‖)
  simp only [smul_eq_mul]
  cases k with
  | ofNat k =>
    cases k with
    | zero =>
      have : chebyshevShiftDiv_seq c (Int.ofNat 0) = 0 := chebyshevShiftDiv_seq_zero c
      rw [this, lpAlgRingData.ofReal_zero, norm_zero]
      exact mul_nonneg ν.2.le (add_nonneg (norm_nonneg _) (norm_nonneg _))
    | succ k =>
      refine (chebyshevShiftDiv_fiber_le c (k+1) (by omega)).trans ?_
      exact mul_le_mul_of_nonneg_right
        (div_le_self ν.2.le (by norm_num : (1:ℝ) ≤ 2))
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
  | negSucc n =>
    have : chebyshevShiftDiv_seq c (Int.negSucc n) = 0 := chebyshevShiftDiv_seq_neg c n
    rw [this, lpAlgRingData.ofReal_zero, norm_zero]
    exact mul_nonneg ν.2.le (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The Chebyshev shift-divide operator as an `l1Chebyshev ν` element. -/
def chebyshevShiftDiv (c : l1Chebyshev ν) : l1Chebyshev ν :=
  ⟨⟨fun k => lpAlgRingData.ofReal (E := ScaledRealZ ν) k (chebyshevShiftDiv_seq c k),
    chebyshevShiftDiv_memℓp c⟩⟩

@[simp] lemma chebyshevShiftDiv_toSeq (c : l1Chebyshev ν) (k : ℤ) :
    lpOneAlg.toRealSeq (chebyshevShiftDiv c) k = chebyshevShiftDiv_seq c k := by
  simp [chebyshevShiftDiv, lpOneAlg.toRealSeq, lpAlgRingData.toReal_ofReal]

/-! ### Linearity of chebyshevShiftDiv -/

lemma chebyshevShiftDiv_add (c d : l1Chebyshev ν) :
    chebyshevShiftDiv (c + d) = chebyshevShiftDiv c + chebyshevShiftDiv d := by
  apply lpOneAlg.ext_toRealSeq; funext k
  simp only [chebyshevShiftDiv_toSeq, lpOneAlg.toRealSeq_add, Pi.add_apply]
  unfold chebyshevShiftDiv_seq
  cases k with
  | ofNat k => cases k with
    | zero => simp
    | succ k => simp; ring
  | negSucc _ => simp

lemma chebyshevShiftDiv_smul (r : ℝ) (c : l1Chebyshev ν) :
    chebyshevShiftDiv (r • c) = r • chebyshevShiftDiv c := by
  apply lpOneAlg.ext_toRealSeq
  rw [lpOneAlg.toRealSeq_smul]; funext k
  simp only [Pi.smul_apply, smul_eq_mul, chebyshevShiftDiv_toSeq]
  -- chebyshevShiftDiv_seq (r • c) k = r * chebyshevShiftDiv_seq c k
  have hsmul : ∀ m : ℤ, l1Chebyshev.toSeq (r • c) m = r * l1Chebyshev.toSeq c m :=
    fun m => congr_fun (lpOneAlg.toRealSeq_smul r c) m
  cases k with
  | ofNat k => cases k with
    | zero => simp [chebyshevShiftDiv_seq]
    | succ k => simp only [chebyshevShiftDiv_seq, Nat.succ_ne_zero, ↓reduceIte, hsmul]; ring
  | negSucc _ => simp [chebyshevShiftDiv_seq]

/-! ### Norm bound -/

private lemma chebyshevShiftDiv_elem_le (c : l1Chebyshev ν) (k : ℤ) :
    ‖(chebyshevShiftDiv c) k‖ ≤
      (ν : ℝ) / 2 * (‖c (k + 1)‖ + ‖c (k + (-1))‖) := by
  cases k with
  | ofNat k => cases k with
    | zero =>
      have : (chebyshevShiftDiv c) (Int.ofNat 0) = 0 := by
        show lpAlgRingData.ofReal (E := ScaledRealZ ν) 0 (chebyshevShiftDiv_seq c 0) = 0
        rw [chebyshevShiftDiv_seq_zero, lpAlgRingData.ofReal_zero]
      rw [this, norm_zero]
      exact mul_nonneg (div_nonneg ν.2.le two_pos.le) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    | succ k => exact chebyshevShiftDiv_fiber_le c (k + 1) (by omega)
  | negSucc n =>
    have : (chebyshevShiftDiv c) (Int.negSucc n) = 0 := by
      show lpAlgRingData.ofReal (E := ScaledRealZ ν) _ (chebyshevShiftDiv_seq c _) = 0
      rw [chebyshevShiftDiv_seq_neg, lpAlgRingData.ofReal_zero]
    rw [this, norm_zero]
    exact mul_nonneg (div_nonneg ν.2.le two_pos.le) (add_nonneg (norm_nonneg _) (norm_nonneg _))

lemma chebyshevShiftDiv_norm_le (c : l1Chebyshev ν) :
    ‖chebyshevShiftDiv c‖ ≤ (ν : ℝ) * ‖c‖ := by
  rw [lpOneAlg.norm_eq_tsum, lpOneAlg.norm_eq_tsum]
  have h1 := lpOneAlg.summable_norm_shift c (1 : ℤ)
  have h2 := lpOneAlg.summable_norm_shift c (-1 : ℤ)
  -- NB: explicit type annotation is critical — Equiv.tsum_eq returns a tsum with
  -- Equiv.addRight internally, which rw can't match against `k + 1`. The annotation
  -- forces the definitional check here so rw works later.
  have ht1 : ∑' k : ℤ, ‖c (k + 1)‖ = ∑' k : ℤ, ‖c k‖ :=
    (Equiv.addRight (1 : ℤ)).tsum_eq (fun k => ‖c k‖)
  have ht2 : ∑' k : ℤ, ‖c (k + (-1))‖ = ∑' k : ℤ, ‖c k‖ :=
    (Equiv.addRight (-1 : ℤ)).tsum_eq (fun k => ‖c k‖)
  have hsb : Summable (fun k : ℤ =>
      (ν : ℝ) / 2 * (‖c (k + 1)‖ + ‖c (k + (-1))‖)) := by
    simpa only [smul_eq_mul] using (h1.add h2).const_smul ((ν : ℝ) / 2)
  have hstep := Summable.tsum_le_tsum (chebyshevShiftDiv_elem_le c)
    (lpOneAlg.summable_norm (chebyshevShiftDiv c)) hsb
  refine hstep.trans (le_of_eq ?_)
  -- Pull out constant
  have e1 : ∑' k : ℤ, ((ν : ℝ) / 2 * (‖c (k + 1)‖ + ‖c (k + (-1))‖)) =
      (ν : ℝ) / 2 * ∑' k, (‖c (k + 1)‖ + ‖c (k + (-1))‖) := tsum_mul_left
  -- Split sum
  have e2 : ∑' k : ℤ, (‖c (k + 1)‖ + ‖c (k + (-1))‖) =
      (∑' k, ‖c (k + 1)‖) + ∑' k, ‖c (k + (-1))‖ := h1.tsum_add h2
  rw [e1, e2, ht1, ht2]; ring

/-! ### CLM construction -/

/-- The Chebyshev shift-divide as a continuous linear map. Analogue of `shiftDivN_CLM`.
Maps `l1Chebyshev ν → l1Chebyshev ν` with `‖chebyshevShiftDiv_CLM‖ ≤ ν`. -/
-- Verify Module ℝ (l1Chebyshev ν) is available
example : Module ℝ (l1Chebyshev ν) := inferInstance

noncomputable def chebyshevShiftDiv_CLM : l1Chebyshev ν →L[ℝ] l1Chebyshev ν := by
  exact LinearMap.mkContinuous
    { toFun := chebyshevShiftDiv
      map_add' := chebyshevShiftDiv_add
      map_smul' := fun r c => chebyshevShiftDiv_smul r c }
    (ν : ℝ)
    chebyshevShiftDiv_norm_le

/-! ## Tail Decomposition

On tail modes `k > N`, the composed map `G(a)_{l,k}` simplifies to:
`G(a)_{l,k} = (1/(2k)) * F(a)_{l,k} = a_k + (c_{k+1} - c_{k-1})/(2k)`
where `A.tailDiag l k = 1/(2k)` for the Chebyshev approximate inverse.

From Eq. 14.11: `F(a)_{l,k} = 2k·a_k + c_{k+1} - c_{k-1}`.
With `A.tailDiag = 1/(2k)`, `G_k = (1/(2k))·F_k = a_k + (c_{k+1} - c_{k-1})/(2k)`. -/

/-- The Chebyshev IVP tail: `a l + chebyshevShiftDiv_CLM(φ(a) l)`.
On modes `k > N`, this equals the full composed map `G` (up to finite corrections). -/
def chebyshevIvpTail (φ : XCheb ν L → Fin L → l1Chebyshev ν)
    (a : XCheb ν L) : XCheb ν L := fun l =>
  a l + chebyshevShiftDiv_CLM (φ a l)

omit [NeZero L] in
lemma differentiable_chebyshevIvpTail (φ : XCheb ν L → Fin L → l1Chebyshev ν)
    (hφ : ∀ l, Differentiable ℝ (fun a : XCheb ν L => φ a l)) :
    Differentiable ℝ (chebyshevIvpTail φ) := by
  intro a; rw [differentiableAt_pi]; intro l
  show DifferentiableAt ℝ (fun a : XCheb ν L => a l + chebyshevShiftDiv_CLM (φ a l)) a
  have h1 : DifferentiableAt ℝ (fun a : XCheb ν L => a l) a :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Chebyshev ν) l).differentiableAt
  have h2 : DifferentiableAt ℝ (fun a : XCheb ν L => chebyshevShiftDiv_CLM (φ a l)) a :=
    (chebyshevShiftDiv_CLM (ν := ν)).differentiableAt.comp a (hφ l a)
  exact DifferentiableAt.add h1 h2

/-! ## Fréchet Derivative of Tail -/

omit [NeZero L] in
/-- Fderiv of `chebyshevIvpTail` at `ā` applied to `h`:
`(fderiv(tail)(ā)(h)) l = h l + chebyshevShiftDiv_CLM((fderiv(φ·l)(ā))(h))`.
Used for Z₁ bound (tail difference = chebyshevShiftDiv of Dφ). -/
lemma fderiv_chebyshevIvpTail (φ : XCheb ν L → Fin L → l1Chebyshev ν)
    (hφ : ∀ l, Differentiable ℝ (fun a : XCheb ν L => φ a l))
    (ā h : XCheb ν L) (l : Fin L) :
    (fderiv ℝ (chebyshevIvpTail φ) ā h) l =
      h l + chebyshevShiftDiv_CLM ((fderiv ℝ (fun a => φ a l) ā) h) := by
  have hd : HasFDerivAt (fun a : XCheb ν L => (chebyshevIvpTail φ a) l)
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin L => l1Chebyshev ν) l +
       (chebyshevShiftDiv_CLM (ν := ν)).comp (fderiv ℝ (fun a => φ a l) ā)) ā := by
    show HasFDerivAt ((fun a : XCheb ν L => a l) + fun a => chebyshevShiftDiv_CLM (φ a l)) _ ā
    exact ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin L => l1Chebyshev ν) l).hasFDerivAt).add
      ((chebyshevShiftDiv_CLM (ν := ν)).hasFDerivAt.comp ā (hφ l ā).hasFDerivAt)
  rw [show (fderiv ℝ (chebyshevIvpTail φ) ā h) l =
      (fderiv ℝ (fun a => (chebyshevIvpTail φ a) l) ā) h from by
    rw [fderiv_pi (fun i => differentiableAt_pi.mp
      (differentiable_chebyshevIvpTail φ hφ ā) i)]; rfl]
  rw [hd.fderiv]; simp

/-! ## ℕ → ℤ Embedding for Composed Map

The IVP coefficients `F(a)` and `A.action(F(a))` are ℕ-indexed.
To get back to `l1Chebyshev ν` (ℤ-indexed), embed by mapping `n : ℕ ↦ (n : ℤ)`
with zeros on negative indices. -/

/-- Embed an ℕ-indexed coefficient sequence into ℤ-indexed `ScaledRealZ ν`.
Maps `n : ℕ ↦ ofReal (↑n) (seq n)` for non-negative ℤ, and `0` for negative. -/
def embedNatToInt (seq : ℕ → ℝ) : ∀ k : ℤ, ScaledRealZ ν k :=
  fun k => match k with
  | (n : ℕ) => lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑n) (seq n)
  | (Int.negSucc _) => 0

/-! ## Composed Map G = A ∘ F -/

/-- Embed ℕ-indexed IVP result into ℤ, **passing through** negative modes from `base`.

On non-negative modes `k ≥ 0`: applies `ofReal` to the ℕ-indexed `seq`.
On negative modes `k < 0`: preserves the value from `base`.

Negative modes are structural invariants of the Chebyshev/Fourier symmetry
(`a_{-k} = a_k`). The IVP operator only acts on ℕ-modes; negative modes are inert. -/
def embedWithPassThrough (seq : ℕ → ℝ) (base : l1Chebyshev ν) :
    ∀ k : ℤ, ScaledRealZ ν k :=
  fun k => match k with
  | (n : ℕ) => lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑n) (seq n)
  | Int.negSucc m => base (Int.negSucc m)

/-! ### Fiber values, membership, and norms of the embeddings

Promoted from Example 14.2.1 (2026-08-25). -/

omit [Fact (1 ≤ (ν : ℝ))] in
@[simp] lemma embedNatToInt_natCast (seq : ℕ → ℝ) (n : ℕ) :
    embedNatToInt (ν := ν) seq (↑n : ℤ)
      = lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑n) (seq n) := rfl

omit [Fact (1 ≤ (ν : ℝ))] in
@[simp] lemma embedNatToInt_negSucc (seq : ℕ → ℝ) (m : ℕ) :
    embedNatToInt (ν := ν) seq (Int.negSucc m) = 0 := rfl

omit [Fact (1 ≤ (ν : ℝ))] in
@[simp] lemma embedWithPassThrough_natCast (seq : ℕ → ℝ) (base : l1Chebyshev ν)
    (n : ℕ) : embedWithPassThrough seq base (↑n : ℤ)
      = lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑n) (seq n) := rfl

omit [Fact (1 ≤ (ν : ℝ))] in
@[simp] lemma embedWithPassThrough_negSucc (seq : ℕ → ℝ) (base : l1Chebyshev ν)
    (m : ℕ) : embedWithPassThrough seq base (Int.negSucc m)
      = base (Int.negSucc m) := rfl

omit [Fact (1 ≤ (ν : ℝ))] in
/-- A finitely-supported `embedNatToInt` sequence is in ℓ¹. -/
lemma embedNatToInt_memℓp_of_finSupp (seq : ℕ → ℝ) (N : ℕ)
    (htail : ∀ n : ℕ, N < n → seq n = 0) :
    Memℓp (embedNatToInt (ν := ν) seq : ∀ k : ℤ, ScaledRealZ ν k) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  apply Summable.of_nat_of_neg_add_one
  · refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => ?_
    have hlt : N < n := by simp [Finset.mem_range] at hn; omega
    show ‖embedNatToInt (ν := ν) seq (↑n : ℤ)‖ = 0
    simp [htail n hlt, lpAlgRingData.ofReal_zero]
  · have h0 : (fun n : ℕ => ‖embedNatToInt (ν := ν) seq (-(↑n + 1 : ℤ))‖)
        = fun _ => (0 : ℝ) := by
      ext n
      have h : -(↑n + 1 : ℤ) = Int.negSucc n := by omega
      rw [h]
      simp
    rw [h0]
    exact summable_zero

/-- Norm of a finitely-supported `embedNatToInt` element as a finite-sum bound. -/
lemma embedNatToInt_norm_le (seq : ℕ → ℝ) (N : ℕ)
    (hmem : Memℓp (embedNatToInt (ν := ν) seq : ∀ k : ℤ, ScaledRealZ ν k) 1)
    (htail : ∀ n : ℕ, N < n → seq n = 0) {B : ℝ}
    (hfin : ∑ n : Fin (N + 1), |seq (n : ℕ)| * (ν : ℝ) ^ (n : ℕ) ≤ B) :
    ‖(⟨⟨embedNatToInt seq, hmem⟩⟩ : l1Chebyshev ν)‖ ≤ B := by
  rw [lpOneAlg.norm_eq_bilatFinSum (⟨⟨embedNatToInt seq, hmem⟩⟩ : l1Chebyshev ν) N
    (fun n hn => by
      show ‖lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑n) (seq n)‖ = 0
      rw [htail n hn, lpAlgRingData.ofReal_zero, norm_zero])
    (fun n _ => by
      show ‖(0 : ScaledRealZ ν (Int.negSucc n))‖ = 0
      exact norm_zero)]
  have hzero : (∑ n : Fin N,
      ‖(⟨⟨embedNatToInt (ν := ν) seq, hmem⟩⟩ : l1Chebyshev ν)
        (Int.negSucc (n : ℕ))‖) = 0 :=
    Finset.sum_eq_zero fun n _ => by
      show ‖(0 : ScaledRealZ ν (Int.negSucc (n : ℕ)))‖ = 0
      exact norm_zero
  rw [hzero, add_zero]
  refine le_trans (le_of_eq ?_) hfin
  refine Finset.sum_congr rfl fun n _ => ?_
  show ‖lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑(n : ℕ)) (seq (n : ℕ))‖ = _
  rw [ScaledRealZ.norm_lpAlgRingData_ofReal]
  simp

/-- Norm bound for an `embedWithPassThrough` element whose tail is the base:
finite window bounded by `B`, negatives and tail each at most `‖base‖`. -/
lemma embedWithPassThrough_norm_le (seq : ℕ → ℝ) (base : l1Chebyshev ν) (N : ℕ)
    (hmem : Memℓp (embedWithPassThrough seq base : ∀ k : ℤ, ScaledRealZ ν k) 1)
    {B : ℝ}
    (hfin : ∑ n : Fin (N + 1), |seq (n : ℕ)| * (ν : ℝ) ^ (n : ℕ) ≤ B)
    (htail : ∀ n : ℕ, N < n → seq n = l1Chebyshev.toSeq base (↑n : ℤ)) :
    ‖(⟨⟨embedWithPassThrough seq base, hmem⟩⟩ : l1Chebyshev ν)‖
      ≤ B + 2 * ‖base‖ := by
  set g : ℤ → ℝ := fun k =>
    ‖(⟨⟨embedWithPassThrough seq base, hmem⟩⟩ : l1Chebyshev ν) k‖
    with hg_def
  have hg_summ : Summable g :=
    lpOneAlg.summable_norm
      (⟨⟨embedWithPassThrough seq base, hmem⟩⟩ : l1Chebyshev ν)
  have h_nat : Summable (fun n : ℕ => g ↑n) :=
    hg_summ.comp_injective fun n m h => by simpa using h
  have h_neg : Summable (fun n : ℕ => g (-(↑n + 1))) :=
    hg_summ.comp_injective fun n m h => by simpa using h
  have hg_natval : ∀ n : ℕ, g ↑n
      = ‖lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑n : ℤ) (seq n)‖ := fun n => rfl
  have hg_negval : ∀ n : ℕ, g (-(↑n + 1)) = ‖base (Int.negSucc n)‖ := by
    intro n
    show g (-(↑n + 1 : ℤ)) = _
    rw [show -(↑n + 1 : ℤ) = Int.negSucc n from by omega]
    rfl
  have h_norm : ‖(⟨⟨embedWithPassThrough seq base, hmem⟩⟩
      : l1Chebyshev ν)‖ = ∑' k : ℤ, g k :=
    lpOneAlg.norm_eq_tsum _
  have h_decomp : ∑' k : ℤ, g k = (∑' n : ℕ, g ↑n) + ∑' n : ℕ, g (-(↑n + 1)) :=
    tsum_of_nat_of_neg_add_one h_nat h_neg
  have hneg_le : (∑' n : ℕ, g (-(↑n + 1))) ≤ ‖base‖ := by
    rw [tsum_congr hg_negval, lpOneAlg.norm_eq_tsum]
    exact tsum_comp_le_tsum_of_inj (lpOneAlg.summable_norm base)
      (fun _ => norm_nonneg _) fun n m h => by simpa using h
  have h_split : ∑' n : ℕ, g ↑n
      = (∑ i ∈ Finset.range (N + 1), g ↑i) + ∑' n : ℕ, g ↑(n + (N + 1)) :=
    (h_nat.sum_add_tsum_nat_add (N + 1)).symm
  have hfin_le : ∑ i ∈ Finset.range (N + 1), g ↑i ≤ B := by
    refine le_trans (le_of_eq ?_) hfin
    rw [← Fin.sum_univ_eq_sum_range (f := fun i => g ↑i)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hg_natval, ScaledRealZ.norm_lpAlgRingData_ofReal]
    simp
  have htail_le : (∑' n : ℕ, g ↑(n + (N + 1))) ≤ ‖base‖ := by
    rw [tsum_congr (fun n : ℕ => show g ↑(n + (N + 1)) = ‖base (↑(n + (N + 1)) : ℤ)‖ by
      rw [hg_natval, htail _ (by omega), ScaledRealZ.norm_lpAlgRingData_ofReal,
        ← l1Chebyshev.norm_fiber])]
    rw [lpOneAlg.norm_eq_tsum]
    exact tsum_comp_le_tsum_of_inj (lpOneAlg.summable_norm base)
      (fun _ => norm_nonneg _) fun n m h => by simpa using h
  rw [h_norm, h_decomp, h_split]
  linarith

/-- The composed Chebyshev IVP map `G = A ∘ F : XCheb → XCheb`.
Applies `A.action` to the ℕ-indexed `chebyshevIvpCoeffs`, then embeds
into ℤ-indexed `l1Chebyshev ν` with negative modes passed through from input.

Negative modes are inert: `G(a)_k = a_k` for `k < 0`. The IVP equations
only constrain non-negative modes (see Ref: Eq. 14.11, Ch.14 p.328).

The `hmem` hypothesis proves the result is in ℓ¹. In practice, this follows
from `A.tailDiag = 1/(2k)` cancelling the `2k` factor in eq. 14.11. -/
def chebyshevIvpMap (A : SystemBlockDiagData L N)
    (φ : XCheb ν L → Fin L → l1Chebyshev ν)
    (p : Fin L → ℝ)
    (hmem : ∀ a : XCheb ν L, ∀ l : Fin L,
      Memℓp (embedWithPassThrough (A.action (chebyshevIvpCoeffs φ p a) l) (a l)
        : ∀ k : ℤ, ScaledRealZ ν k) 1)
    (a : XCheb ν L) : XCheb ν L := fun l =>
  ⟨⟨embedWithPassThrough (A.action (chebyshevIvpCoeffs φ p a) l) (a l), hmem a l⟩⟩

/-! ## Membership Proof for chebyshevIvpMap

On tail modes (n > N) with `A.tailDiag = 1/(2k)`, the Chebyshev IVP action simplifies:
`A.action(F(a))_n = (1/(2n)) · (2n·a_n + c_{n+1} - c_{n-1}) = a_n + chebyshevShiftDiv_seq(c)_n`
where `c = φ(a)`. Both `a` and `chebyshevShiftDiv(c)` are in ℓ¹, so the result is in ℓ¹. -/

omit [NeZero L] in
/-- On tail modes, the action with tailDiag = 1/(2k) equals a_k + chebyshevShiftDiv_seq(c)_k. -/
private lemma action_chebyshev_tail_eq {N : ℕ}
    (A : SystemBlockDiagData L N)
    (φ : XCheb ν L → Fin L → l1Chebyshev ν)
    (p : Fin L → ℝ)
    (htail : ∀ l : Fin L, ∀ n, N < n → A.tailDiag l n = 1 / (2 * (↑n : ℝ)))
    (a : XCheb ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    A.action (chebyshevIvpCoeffs φ p a) l n =
      l1Chebyshev.toSeq (a l) (↑n : ℤ) + chebyshevShiftDiv_seq (φ a l) (↑n : ℤ) := by
  rw [SystemBlockDiagData.action_tail _ _ _ _ hn, htail l n hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [chebyshevIvpCoeffs]
  rw [chebyshevShiftDiv_seq_pos (φ a l) (m + 1) (by omega)]
  have h1 : (↑(m + 1) : ℤ) + 1 = (↑(m + 2) : ℤ) := by push_cast; ring
  have h2 : (↑(m + 1) : ℤ) - 1 = (↑m : ℤ) := by push_cast; ring
  rw [h1, h2]
  have hne : (2 * ((m : ℝ) + 1)) ≠ 0 := by positivity
  have hne' : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  push_cast; ring

omit [NeZero L] in
/-- Membership proof: `embedWithPassThrough(A.action(F(a)), a l)` is in ℓ¹
when `A.tailDiag = 1/(2k)`. On tail modes, the ℕ-part equals
`a_k + chebyshevShiftDiv(φ(a))_k`, both in ℓ¹. Negative modes come from `a l`
which is already in ℓ¹. Used to auto-derive `hmem` in `StdChebIVPData`. -/
lemma chebyshevIvpMap_mem_of_tailDiag_half {N : ℕ}
    (A : SystemBlockDiagData L N)
    (φ : XCheb ν L → Fin L → l1Chebyshev ν)
    (p : Fin L → ℝ)
    (htail : ∀ l : Fin L, ∀ n, N < n → A.tailDiag l n = 1 / (2 * (↑n : ℝ)))
    (a : XCheb ν L) (l : Fin L) :
    Memℓp (embedWithPassThrough (ν := ν)
      (A.action (chebyshevIvpCoeffs φ p a) l) (a l)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  set seq := A.action (chebyshevIvpCoeffs φ p a) l
  set c := φ a l
  -- On tail modes, embed(seq)(↑n) = (a l)(↑n) + chebyshevShiftDiv(c)(↑n)
  have h_elem_eq : ∀ n : ℕ, N < n →
      (embedWithPassThrough (ν := ν) seq (a l)) (↑n : ℤ) =
        (a l) (↑n : ℤ) + (chebyshevShiftDiv c) (↑n : ℤ) := by
    intro n hn
    show lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑n) (seq n) = _
    have hseq : seq n = l1Chebyshev.toSeq (a l) (↑n : ℤ) +
        chebyshevShiftDiv_seq (φ a l) (↑n : ℤ) :=
      action_chebyshev_tail_eq A φ p htail a l n hn
    rw [hseq, lpAlgRingData.ofReal_add]; congr 1
  -- Decompose ℤ = ℕ+ ⊔ ℕ- via Summable.of_nat_of_neg_add_one
  apply Summable.of_nat_of_neg_add_one
  · -- Positive part: eventually bounded by ‖(a l)(↑n)‖ + ‖shiftDiv(c)(↑n)‖
    have h_bound : Summable (fun n : ℕ =>
        ‖(a l) (↑n : ℤ)‖ + ‖chebyshevShiftDiv c (↑n : ℤ)‖) :=
      ((lpOneAlg.summable_norm (a l)).comp_injective (fun n m h => by omega)).add
        ((lpOneAlg.summable_norm (chebyshevShiftDiv c)).comp_injective
          (fun n m h => by omega))
    exact Summable.of_norm_bounded_eventually_nat h_bound
      (Filter.eventually_atTop.mpr ⟨N + 1, fun n hn => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        rw [h_elem_eq n (by omega)]
        exact norm_add_le _ _⟩)
  · -- Negative part: from a l, which is in ℓ¹
    have : (fun n : ℕ => ‖(embedWithPassThrough (ν := ν) seq (a l)) (-(↑n + 1 : ℤ))‖) =
        fun n => ‖(a l) (Int.negSucc n)‖ := by
      ext n; have h : -(↑n + 1 : ℤ) = Int.negSucc n := by omega
      rw [h]; simp [embedWithPassThrough]
    rw [this]
    exact (lpOneAlg.summable_norm (a l)).comp_injective (fun n m h => by omega)

/-! ## Tight Tail Bound for chebyshevShiftDiv

On tail modes `k ≥ N+1`, `1/(2k) ≤ 1/(2(N+1))` gives a tighter tail estimate
than the global `≤ ν · ‖c‖`. Used for Z₁ bounds.
Analogous to `shiftDivN_tailTsum_le_div` in
`Analysis/SequenceSpace/Geometric/Omega.lean`. -/

/-- Per-element tight bound:
`‖shift(c)(k)‖ ≤ 1/(2k) · (ν⁻¹ · ‖c(k+1)‖ + ν · ‖c(k-1)‖)` for k ≥ 1.
The key improvement over `chebyshevShiftDiv_fiber_le` is the `1/(2k)` factor instead of `1/2`,
giving a tail-dependent estimate that tightens as modes grow. The `ν⁻¹` weight on the
`c(k+1)` term is exact (`|c_{k+1}| ν^k = ν⁻¹ · |c_{k+1}| ν^{k+1}`, needs only `0 < ν`). -/
private lemma chebyshevShiftDiv_elem_tight_le (c : l1Chebyshev ν) (k : ℕ) (hk : 0 < k) :
    ‖(chebyshevShiftDiv c) (↑k : ℤ)‖ ≤
    1 / (2 * (k : ℝ)) *
      ((ν : ℝ)⁻¹ * ‖c ((↑k : ℤ) + 1)‖ + (ν : ℝ) * ‖c ((↑k : ℤ) + (-1))‖) := by
  -- Same norm unfolding as chebyshevShiftDiv_fiber_le
  show ‖lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑k) (chebyshevShiftDiv_seq c ↑k)‖ ≤ _
  rw [chebyshevShiftDiv_seq_pos c k (by omega)]
  simp only [ScaledRealZ.norm_lpAlgRingData_ofReal]
  rw [abs_div, abs_of_pos (show (0:ℝ) < 2 * (k:ℝ) by positivity)]
  rw [lpOneAlg.norm_eq_abs_toReal_mul_weight c ((↑k : ℤ) + 1),
      lpOneAlg.norm_eq_abs_toReal_mul_weight c ((↑k : ℤ) + (-1))]
  simp only [ScaledRealZ.norm_lpAlgRingData_ofReal, abs_one, one_mul]
  have hk1 : ((↑k : ℤ) + 1).natAbs = k + 1 := by omega
  have hk2 : ((↑k : ℤ) + (-1)).natAbs = k - 1 := by omega
  have hk0 : (↑k : ℤ).natAbs = k := by omega
  rw [hk1, hk2, hk0]
  -- Now pure ℝ arithmetic with a = |c_{k+1}|, b = |c_{k-1}|
  set a := |lpOneAlg.toRealSeq c ((↑k : ℤ) + 1)|
  set b := |lpOneAlg.toRealSeq c ((↑k : ℤ) + (-1))|
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have hν0 : (0 : ℝ) < (ν : ℝ) := ν.2
  have hνne : (ν : ℝ) ≠ 0 := hν0.ne'
  have hpk : (0 : ℝ) ≤ (ν : ℝ) ^ k := pow_nonneg hν0.le k
  -- Exact identity: a * ν^k = ν⁻¹ * (a * ν^{k+1}); replaces the former ν^k ≤ ν^{k+1} relaxation
  have hainv : (ν : ℝ)⁻¹ * (a * (ν : ℝ) ^ (k + 1)) = a * (ν : ℝ) ^ k := by
    linear_combination a * (ν : ℝ) ^ k * mul_inv_cancel₀ hνne
  have heq_pow : (ν : ℝ) * (ν : ℝ) ^ (k - 1) = (ν : ℝ) ^ k := by
    rw [mul_comm, ← pow_succ]; congr 1; omega
  have htri : |lpOneAlg.toRealSeq c ((↑k : ℤ) + 1) -
      lpOneAlg.toRealSeq c ((↑k : ℤ) + (-1))| ≤ a + b := by
    have := norm_sub_le (lpOneAlg.toRealSeq c ((↑k : ℤ) + 1))
      (lpOneAlg.toRealSeq c ((↑k : ℤ) + (-1)))
    simp only [Real.norm_eq_abs] at this; exact this
  have h2k : (0 : ℝ) < 2 * (k : ℝ) := by positivity
  -- Numerator bound: |x-y| * ν^k ≤ (a+b) * ν^k = ν⁻¹ * (a * ν^{k+1}) + ν * (b * ν^{k-1})
  have h_num : |lpOneAlg.toRealSeq c ((↑k : ℤ) + 1) - lpOneAlg.toRealSeq c ((↑k : ℤ) + (-1))| *
      (ν : ℝ) ^ k ≤ (ν : ℝ)⁻¹ * (a * (ν : ℝ) ^ (k + 1)) + (ν : ℝ) * (b * (ν : ℝ) ^ (k - 1)) := by
    have hbν : (ν : ℝ) * (b * (ν : ℝ) ^ (k - 1)) = b * (ν : ℝ) ^ k := by
      linear_combination b * heq_pow
    linarith [mul_le_mul_of_nonneg_right htri hpk, mul_add a b ((ν:ℝ)^k),
      add_mul a b ((ν:ℝ)^k), hainv, hbν]
  -- Factor 1/(2k) from both sides via calc
  calc |lpOneAlg.toRealSeq c ((↑k : ℤ) + 1) - lpOneAlg.toRealSeq c ((↑k : ℤ) + (-1))| /
        (2 * (k : ℝ)) * (ν : ℝ) ^ k
      = |lpOneAlg.toRealSeq c ((↑k : ℤ) + 1) - lpOneAlg.toRealSeq c ((↑k : ℤ) + (-1))| *
          (ν : ℝ) ^ k / (2 * (k : ℝ)) := div_mul_eq_mul_div _ _ _
    _ ≤ ((ν : ℝ)⁻¹ * (a * (ν : ℝ) ^ (k + 1)) + (ν : ℝ) * (b * (ν : ℝ) ^ (k - 1))) /
          (2 * (k : ℝ)) :=
        div_le_div_of_nonneg_right h_num h2k.le
    _ = 1 / (2 * (k : ℝ)) *
          ((ν : ℝ)⁻¹ * (a * (ν : ℝ) ^ (k + 1)) + (ν : ℝ) * (b * (ν : ℝ) ^ (k - 1))) :=
        by ring

/-- **Semi-major tail tsum bound**:
`∑' n, ‖chebyshevShiftDiv(c)(n+N+1)‖ ≤ (ν⁻¹ + ν)/(2(N+1)) · ‖c‖`.

The prefactor `(ν⁻¹ + ν)/2` is the semi-major axis of the Bernstein ellipse `E_ν`:
the bound equals `CrossGeometry.semiMajor ν / (N + 1)` (production since 2026-09-03,
`Analysis/SequenceSpace/CrossGeometry/Joukowski.lean`); this file states the literal
`((ν:ℝ)⁻¹ + ν)/2` because it does not import that module.
Needs only `0 < ν` beyond what `chebyshevShiftDiv` itself requires; the relaxations
`chebyshevShiftDiv_tailTsum_le_half` ((1+ν)/(2(N+1))) and
`chebyshevShiftDiv_tailTsum_le_div` (ν/(N+1)) are corollaries under `1 ≤ ν`.

Proof chain: per-element tight (exact ν⁻¹/ν weights) → tighten 1/(2k) ≤ 1/(2(N+1))
→ sum → factor → subseries ≤ ‖c‖. -/
lemma chebyshevShiftDiv_tailTsum_le_semiMajor_div (c : l1Chebyshev ν) (N : ℕ) :
    ∑' n, ‖(chebyshevShiftDiv c) (↑(n + (N + 1)) : ℤ)‖ ≤
      ((ν : ℝ)⁻¹ + (ν : ℝ)) / (2 * ((N : ℝ) + 1)) * ‖c‖ := by
  have hν0 : (0 : ℝ) < (ν : ℝ) := ν.2
  have hνinv : (0 : ℝ) ≤ (ν : ℝ)⁻¹ := (inv_pos.mpr hν0).le
  -- Per-element: tighten 1/(2(n+N+1)) ≤ 1/(2(N+1))
  have hper : ∀ n : ℕ, ‖(chebyshevShiftDiv c) (↑(n + (N + 1)) : ℤ)‖ ≤
      1 / (2 * ((N : ℝ) + 1)) *
        ((ν : ℝ)⁻¹ * ‖c ((↑(n + (N + 1)) : ℤ) + 1)‖ +
          (ν : ℝ) * ‖c ((↑(n + (N + 1)) : ℤ) + (-1))‖) := by
    intro n
    refine (chebyshevShiftDiv_elem_tight_le c (n + (N + 1)) (by omega)).trans ?_
    apply mul_le_mul_of_nonneg_right _ (add_nonneg (mul_nonneg hνinv (norm_nonneg _))
      (mul_nonneg ν.2.le (norm_nonneg _)))
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (show
      2 * (N + 1) ≤ 2 * (n + (N + 1)) by omega))
  -- Summability
  have hsumm : Summable (fun n : ℕ =>
      ‖(chebyshevShiftDiv c) (↑(n + (N + 1)) : ℤ)‖) :=
    (lpOneAlg.summable_norm (chebyshevShiftDiv c)).comp_injective (fun n m h => by omega)
  have h1 : Summable (fun n : ℕ => (ν : ℝ)⁻¹ * ‖c ((↑(n + (N + 1)) : ℤ) + 1)‖) :=
    ((lpOneAlg.summable_norm c).comp_injective (fun n m h => by omega)).mul_left _
  have h2 : Summable (fun n : ℕ => (ν : ℝ) * ‖c ((↑(n + (N + 1)) : ℤ) + (-1))‖) := by
    exact ((lpOneAlg.summable_norm c).comp_injective
      (fun n m h => by omega)).mul_left _
  calc ∑' n, ‖(chebyshevShiftDiv c) (↑(n + (N + 1)) : ℤ)‖
      ≤ ∑' n, (1 / (2 * ((N : ℝ) + 1)) *
        ((ν : ℝ)⁻¹ * ‖c ((↑(n + (N + 1)) : ℤ) + 1)‖ +
          (ν : ℝ) * ‖c ((↑(n + (N + 1)) : ℤ) + (-1))‖)) :=
        hsumm.tsum_le_tsum hper ((h1.add h2).mul_left _)
    _ = 1 / (2 * ((N : ℝ) + 1)) *
        ∑' n, ((ν : ℝ)⁻¹ * ‖c ((↑(n + (N + 1)) : ℤ) + 1)‖ +
          (ν : ℝ) * ‖c ((↑(n + (N + 1)) : ℤ) + (-1))‖) := tsum_mul_left
    _ = 1 / (2 * ((N : ℝ) + 1)) *
        ((ν : ℝ)⁻¹ * (∑' n, ‖c ((↑(n + (N + 1)) : ℤ) + 1)‖) +
          (ν : ℝ) * ∑' n, ‖c ((↑(n + (N + 1)) : ℤ) + (-1))‖) := by
        congr 1; rw [← tsum_mul_left, ← tsum_mul_left]; exact h1.tsum_add h2
    _ ≤ 1 / (2 * ((N : ℝ) + 1)) * ((ν : ℝ)⁻¹ * ‖c‖ + (ν : ℝ) * ‖c‖) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ hνinv
          rw [lpOneAlg.norm_eq_tsum c]
          exact tsum_comp_le_tsum_of_inj (lpOneAlg.summable_norm c)
            (fun _ => norm_nonneg _) (fun n m h => by omega)
        · apply mul_le_mul_of_nonneg_left _ ν.2.le
          rw [lpOneAlg.norm_eq_tsum c]
          exact tsum_comp_le_tsum_of_inj (lpOneAlg.summable_norm c)
            (fun _ => norm_nonneg _) (fun n m h => by omega)
    _ = ((ν : ℝ)⁻¹ + (ν : ℝ)) / (2 * ((N : ℝ) + 1)) * ‖c‖ := by ring

/-- Tail tsum bound, half form: `∑' n, ‖chebyshevShiftDiv(c)(n+N+1)‖ ≤ (1+ν)/(2(N+1)) · ‖c‖`.
Corollary of `chebyshevShiftDiv_tailTsum_le_semiMajor_div` via `ν⁻¹ ≤ 1` (from `1 ≤ ν`). -/
lemma chebyshevShiftDiv_tailTsum_le_half (c : l1Chebyshev ν) (N : ℕ) :
    ∑' n, ‖(chebyshevShiftDiv c) (↑(n + (N + 1)) : ℤ)‖ ≤
      (1 + (ν : ℝ)) / (2 * ((N : ℝ) + 1)) * ‖c‖ := by
  refine (chebyshevShiftDiv_tailTsum_le_semiMajor_div c N).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have h2N : (0 : ℝ) < 2 * ((N : ℝ) + 1) := by positivity
  rw [div_le_div_iff₀ h2N h2N]
  have hν1 : (1 : ℝ) ≤ (ν : ℝ) := Fact.out
  have hinv : (ν : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hν1
  exact mul_le_mul_of_nonneg_right (by linarith) h2N.le

/-- Tight tail tsum bound: `∑' n, ‖chebyshevShiftDiv(c)(n+N+1)‖ ≤ ν/(N+1) · ‖c‖`.
Tighter than `chebyshevShiftDiv_norm_le` (`≤ ν · ‖c‖`) because `1/(2k) ≤ 1/(2(N+1))`
on tail modes `k ≥ N+1`. Used for IVP Z₁ tail error bounds.

Corollary of `chebyshevShiftDiv_tailTsum_le_half` via `(1+ν)/(2(N+1)) ≤ ν/(N+1)`
(i.e. `1 ≤ ν`); the sharpest form is `chebyshevShiftDiv_tailTsum_le_semiMajor_div`. -/
lemma chebyshevShiftDiv_tailTsum_le_div (c : l1Chebyshev ν) (N : ℕ) :
    ∑' n, ‖(chebyshevShiftDiv c) (↑(n + (N + 1)) : ℤ)‖ ≤
      (ν : ℝ) / ((N : ℝ) + 1) * ‖c‖ := by
  refine (chebyshevShiftDiv_tailTsum_le_half c N).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * ((N:ℝ) + 1))
    (by positivity : (0:ℝ) < (N:ℝ) + 1)]
  have hν : (1:ℝ) ≤ ν := Fact.out
  have hN : (0:ℝ) ≤ (N:ℝ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hν hN]

/-! ## Norm Splitting for l1Chebyshev

If `d : l1Chebyshev ν` vanishes for modes `k ≤ N`, its norm equals the ℕ-indexed tail tsum
starting from mode `N+1`. Uses ℤ = ℕ₊ ⊔ ℕ₋ decomposition + finite/tail splitting for ℕ.

This is the ℤ-indexed analogue of `l1Weighted.norm_eq_tailTsum_of_fin_zero`. -/

/-- If `d : l1Chebyshev` is zero for `k ≤ N`, its norm equals the ℕ-tail tsum from `N+1`. -/
private lemma l1Chebyshev_norm_eq_nat_tailTsum (d : l1Chebyshev ν) (N : ℕ)
    (hfin : ∀ k : ℤ, k ≤ ↑N → d k = 0) :
    ‖d‖ = ∑' n : ℕ, ‖d (↑(n + (N + 1)) : ℤ)‖ := by
  -- Work at generic lpOneAlg level to avoid subtype elaboration blowup
  set f : ℤ → ℝ := fun k => ‖d k‖ with hf_def
  -- Summability
  have hf_summ : Summable f := lpOneAlg.summable_norm d
  have h_nat : Summable (fun n : ℕ => f ↑n) :=
    hf_summ.comp_injective (fun n m h => by omega)
  have h_neg : Summable (fun n : ℕ => f (-(↑n + 1))) :=
    hf_summ.comp_injective (fun n m h => by omega)
  -- Step 1: ‖d‖ = ∑' k : ℤ, f k
  have h_norm : ‖d‖ = ∑' k : ℤ, f k := lpOneAlg.norm_eq_tsum d
  -- Step 2: Decompose ℤ-tsum = ℕ₊ + ℕ₋ (use have to avoid rw matching blowup)
  have h_decomp : ∑' k : ℤ, f k =
      (∑' n : ℕ, f ↑n) + (∑' n : ℕ, f (-(↑n + 1))) :=
    tsum_of_nat_of_neg_add_one h_nat h_neg
  -- Step 3: Negative part = 0
  have h_neg_zero : (fun n : ℕ => f (-(↑n + 1))) = fun _ => 0 :=
    funext (fun n => show ‖d (-(↑n + 1 : ℤ))‖ = 0 from
      norm_eq_zero.mpr (hfin _ (by omega)))
  -- Step 4: Split ℕ₊ = finite [0,N] + tail [N+1, ∞)
  have h_split : ∑' n : ℕ, f ↑n =
      (∑ i ∈ Finset.range (N + 1), f ↑i) + ∑' n, f ↑(n + (N + 1)) :=
    (h_nat.sum_add_tsum_nat_add (N + 1)).symm
  -- Step 5: Finite range = 0
  have h_fin_zero : ∑ i ∈ Finset.range (N + 1), f ↑i = 0 :=
    Finset.sum_eq_zero (fun i hi => show ‖d (↑i : ℤ)‖ = 0 from
      norm_eq_zero.mpr (hfin ↑i (by
        have := Finset.mem_range.mp hi; omega)))
  -- Combine
  rw [h_norm, h_decomp, h_neg_zero, tsum_zero, add_zero, h_split, h_fin_zero, zero_add]

/-! ## Chebyshev Z₁ Component Bound

Combines norm-splitting + `chebyshevShiftDiv_tailTsum_le_div` to get the per-component
Z₁ bound: if `d` is zero on finite modes and equals `chebyshevShiftDiv(w)` on tail modes,
then `‖d‖ ≤ ν/(N+1) · ‖w‖`.

This is the ℤ-indexed analogue of `Z₁_component_le` from `IVP/Setup.lean`. -/

/-- Chebyshev Z₁ per-component bound.
If `d : l1Chebyshev` vanishes for `k ≤ N` and equals `chebyshevShiftDiv(w)` for `k > N`,
then `‖d‖ ≤ ν/(N+1) · ‖w‖`. -/
lemma chebyshev_Z₁_component_le (d w : l1Chebyshev ν) (N : ℕ)
    (hfin : ∀ k : ℤ, k ≤ ↑N → d k = 0)
    (htail : ∀ m : ℕ, N < m → d (↑m : ℤ) = (chebyshevShiftDiv w) (↑m : ℤ)) :
    ‖d‖ ≤ (ν : ℝ) / ((N : ℝ) + 1) * ‖w‖ := by
  rw [l1Chebyshev_norm_eq_nat_tailTsum d N hfin]
  -- Rewrite d terms as chebyshevShiftDiv terms
  simp_rw [show ∀ n : ℕ, ‖d (↑(n + (N + 1)) : ℤ)‖ =
      ‖(chebyshevShiftDiv w) (↑(n + (N + 1)) : ℤ)‖ from
    fun n => congrArg (‖·‖) (htail (n + (N + 1)) (by omega))]
  exact chebyshevShiftDiv_tailTsum_le_div w N

/-- Variant using norm equality on tail (handles sign: works when tail difference
is `±chebyshevShiftDiv(w)`, not just `+`). -/
lemma chebyshev_Z₁_component_norm_le (d w : l1Chebyshev ν) (N : ℕ)
    (hfin : ∀ k : ℤ, k ≤ ↑N → d k = 0)
    (htail : ∀ m : ℕ, N < m → ‖d (↑m : ℤ)‖ = ‖(chebyshevShiftDiv w) (↑m : ℤ)‖) :
    ‖d‖ ≤ (ν : ℝ) / ((N : ℝ) + 1) * ‖w‖ := by
  rw [l1Chebyshev_norm_eq_nat_tailTsum d N hfin]
  simp_rw [show ∀ n : ℕ, ‖d (↑(n + (N + 1)) : ℤ)‖ =
      ‖(chebyshevShiftDiv w) (↑(n + (N + 1)) : ℤ)‖ from
    fun n => htail (n + (N + 1)) (by omega)]
  exact chebyshevShiftDiv_tailTsum_le_div w N

/-! ## Relaxed Chebyshev Z₁ Component Bound

Handles the Chebyshev IVP case where the mode-0 alternating sum couples all modes,
preventing `d` from vanishing on finite modes. Instead of requiring `d = 0` on `k ≤ N`,
takes separate bounds for negative, finite, and tail contributions. -/

/-- **Relaxed** Chebyshev Z₁ per-component bound.
Replaces the `hfin` (zero on all k ≤ N) assumption with separate bounds:
- `hneg`: d = 0 on negative modes (from pass-through)
- `hfin_le`: finite-mode contribution bounded by ε
- `htail`: tail matches chebyshevShiftDiv(w)

Result: `‖d‖ ≤ ε + ν/(N+1) · ‖w‖`. -/
lemma chebyshev_Z₁_component_le_relaxed (d w : l1Chebyshev ν) (N : ℕ)
    (hneg : ∀ m : ℕ, d (Int.negSucc m) = 0)
    {ε : ℝ}
    (hfin_le : ∑ k : Fin (N + 1), ‖d (↑(k : ℕ) : ℤ)‖ ≤ ε)
    (htail : ∀ m : ℕ, N < m →
      ‖d (↑m : ℤ)‖ = ‖(chebyshevShiftDiv w) (↑m : ℤ)‖) :
    ‖d‖ ≤ ε + (ν : ℝ) / ((N : ℝ) + 1) * ‖w‖ := by
  -- set f to avoid subtype elaboration blowup on tsum operations
  set f : ℤ → ℝ := fun k => ‖d k‖ with hf_def
  have hf_summ : Summable f := lpOneAlg.summable_norm d
  have h_nat : Summable (fun n : ℕ => f ↑n) :=
    hf_summ.comp_injective (fun n m h => by omega)
  have h_neg : Summable (fun n : ℕ => f (-(↑n + 1))) :=
    hf_summ.comp_injective (fun n m h => by omega)
  -- Decompose ℤ = ℕ₊ + ℕ₋, neg part = 0, split ℕ into [0,N] + [N+1,∞)
  rw [lpOneAlg.norm_eq_tsum d, tsum_of_nat_of_neg_add_one h_nat h_neg]
  rw [show (fun n : ℕ => f (-(↑n + 1))) = fun _ => (0 : ℝ) from
    funext (fun n => norm_eq_zero.mpr (by
      show d (-(↑n + 1 : ℤ)) = 0
      rw [show -(↑n + 1 : ℤ) = Int.negSucc n from by omega, hneg]))]
  rw [tsum_zero, add_zero, (h_nat.sum_add_tsum_nat_add (N + 1)).symm]
  refine add_le_add ?_ ?_
  · rw [← Fin.sum_univ_eq_sum_range (f := fun n => f ↑n)]; exact hfin_le
  · exact (tsum_congr fun n => htail (n + (N + 1)) (by omega)) ▸
      chebyshevShiftDiv_tailTsum_le_div w N

/-- **Semi-major** relaxed Chebyshev Z₁ per-component bound.
Same hypotheses as `chebyshev_Z₁_component_le_relaxed`, with the sharper tail factor
`(ν⁻¹ + ν)/(2(N+1))` from `chebyshevShiftDiv_tailTsum_le_semiMajor_div`
(= `semiMajor ν / (N+1)`) in place of `ν/(N+1)`.

Result: `‖d‖ ≤ ε + (ν⁻¹ + ν)/(2(N+1)) · ‖w‖`. -/
lemma chebyshev_Z₁_component_le_semiMajor (d w : l1Chebyshev ν) (N : ℕ)
    (hneg : ∀ m : ℕ, d (Int.negSucc m) = 0)
    {ε : ℝ}
    (hfin_le : ∑ k : Fin (N + 1), ‖d (↑(k : ℕ) : ℤ)‖ ≤ ε)
    (htail : ∀ m : ℕ, N < m →
      ‖d (↑m : ℤ)‖ = ‖(chebyshevShiftDiv w) (↑m : ℤ)‖) :
    ‖d‖ ≤ ε + ((ν : ℝ)⁻¹ + (ν : ℝ)) / (2 * ((N : ℝ) + 1)) * ‖w‖ := by
  -- set f to avoid subtype elaboration blowup on tsum operations
  set f : ℤ → ℝ := fun k => ‖d k‖ with hf_def
  have hf_summ : Summable f := lpOneAlg.summable_norm d
  have h_nat : Summable (fun n : ℕ => f ↑n) :=
    hf_summ.comp_injective (fun n m h => by omega)
  have h_neg : Summable (fun n : ℕ => f (-(↑n + 1))) :=
    hf_summ.comp_injective (fun n m h => by omega)
  -- Decompose ℤ = ℕ₊ + ℕ₋, neg part = 0, split ℕ into [0,N] + [N+1,∞)
  rw [lpOneAlg.norm_eq_tsum d, tsum_of_nat_of_neg_add_one h_nat h_neg]
  rw [show (fun n : ℕ => f (-(↑n + 1))) = fun _ => (0 : ℝ) from
    funext (fun n => norm_eq_zero.mpr (by
      show d (-(↑n + 1 : ℤ)) = 0
      rw [show -(↑n + 1 : ℤ) = Int.negSucc n from by omega, hneg]))]
  rw [tsum_zero, add_zero, (h_nat.sum_add_tsum_nat_add (N + 1)).symm]
  refine add_le_add ?_ ?_
  · rw [← Fin.sum_univ_eq_sum_range (f := fun n => f ↑n)]; exact hfin_le
  · exact (tsum_congr fun n => htail (n + (N + 1)) (by omega)) ▸
      chebyshevShiftDiv_tailTsum_le_semiMajor_div w N

/-! ## Chebyshev Z₁ Operator Norm Bound

Assembles per-component Z₁ bounds into `‖composedApprox - fderiv G ā‖ ≤ Z₁`.
Analogous to `ivp_Z₁_le` from IVP/Setup.lean. -/

omit [NeZero L] in
/-- **Chebyshev Z₁ bound**: `‖composedApprox - fderiv G ā‖ ≤ Z₁`.
Chains `chebyshev_Z₁_component_norm_le` with per-component Dφ norm bound.

Hypotheses:
- `hfin`: finite modes cancel (composedApprox = fderiv G on k ≤ N)
- `htail`: tail difference norms = chebyshevShiftDiv(Dφ) norms
- `hDφ`: per-component `‖Dφ h l‖ ≤ K · ‖h‖`
- `hZ₁`: `ν/(N+1) · K ≤ Z₁` -/
lemma chebyshev_Z₁_le
    (N : ℕ) (composedApprox : XCheb ν L →L[ℝ] XCheb ν L)
    (G : XCheb ν L → XCheb ν L) (ā : XCheb ν L)
    (Dφ : XCheb ν L → Fin L → l1Chebyshev ν)
    (hfin : ∀ h : XCheb ν L, ∀ l : Fin L, ∀ k : ℤ, k ≤ ↑N →
      ((composedApprox - fderiv ℝ G ā) h l) k = 0)
    (htail : ∀ h : XCheb ν L, ∀ l : Fin L, ∀ m : ℕ, N < m →
      ‖((composedApprox - fderiv ℝ G ā) h l) (↑m : ℤ)‖ =
        ‖(chebyshevShiftDiv (Dφ h l)) (↑m : ℤ)‖)
    {K : ℝ} (hK : 0 ≤ K)
    (hDφ : ∀ h : XCheb ν L, ∀ l : Fin L, ‖Dφ h l‖ ≤ K * ‖h‖)
    {Z₁ : ℝ} (hZ₁ : (ν : ℝ) / ((N : ℝ) + 1) * K ≤ Z₁) :
    ‖composedApprox - fderiv ℝ G ā‖ ≤ Z₁ := by
  have hν : (0 : ℝ) ≤ (ν : ℝ) / ((N : ℝ) + 1) := div_nonneg ν.2.le (by positivity)
  apply ContinuousLinearMap.opNorm_le_bound _ (le_trans (mul_nonneg hν hK) hZ₁)
  intro h
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (le_trans (mul_nonneg hν hK) hZ₁)
    (norm_nonneg _))).mpr fun l => ?_
  calc ‖((composedApprox - fderiv ℝ G ā) h) l‖
      ≤ (ν : ℝ) / ((N : ℝ) + 1) * ‖Dφ h l‖ :=
        chebyshev_Z₁_component_norm_le _ _ N (hfin h l) (htail h l)
    _ ≤ (ν : ℝ) / ((N : ℝ) + 1) * (K * ‖h‖) :=
        mul_le_mul_of_nonneg_left (hDφ h l) hν
    _ ≤ Z₁ * ‖h‖ := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hZ₁ (norm_nonneg _)

omit [NeZero L] in
/-- **Relaxed Chebyshev Z₁ bound** for IVPs where mode-0 couples all modes.

Unlike `chebyshev_Z₁_le`, does NOT require `hfin` (composedApprox = fderiv G on k ≤ N).
Instead, takes separate bounds for the finite-mode contribution (ε per component)
and the tail contribution (via Dφ norm bound K).

Total: `Z₁ ≤ ε + ν/(N+1) · K`.

Use when the IVP derivative DF is not lower-triangular (Chebyshev mode-0 alternating sum
couples all modes, creating O(1/ν^{N+1}) leakage into finite modes). -/
lemma chebyshev_Z₁_le_relaxed
    (N : ℕ) (composedApprox : XCheb ν L →L[ℝ] XCheb ν L)
    (G : XCheb ν L → XCheb ν L) (ā : XCheb ν L)
    (Dφ : XCheb ν L → Fin L → l1Chebyshev ν)
    -- Negative: difference is zero (from pass-through)
    (hneg : ∀ h : XCheb ν L, ∀ l : Fin L, ∀ m : ℕ,
      ((composedApprox - fderiv ℝ G ā) h l) (Int.negSucc m) = 0)
    -- Finite: per-component bound
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfin_le : ∀ h : XCheb ν L, ∀ l : Fin L,
      ∑ k : Fin (N + 1),
        ‖((composedApprox - fderiv ℝ G ā) h l) (↑(k : ℕ) : ℤ)‖ ≤ ε * ‖h‖)
    -- Tail: norm matches chebyshevShiftDiv(Dφ)
    (htail : ∀ h : XCheb ν L, ∀ l : Fin L, ∀ m : ℕ, N < m →
      ‖((composedApprox - fderiv ℝ G ā) h l) (↑m : ℤ)‖ =
        ‖(chebyshevShiftDiv (Dφ h l)) (↑m : ℤ)‖)
    -- Dφ norm bound
    {K : ℝ} (hK : 0 ≤ K)
    (hDφ : ∀ h : XCheb ν L, ∀ l : Fin L, ‖Dφ h l‖ ≤ K * ‖h‖)
    -- Total bound
    {Z₁ : ℝ} (hZ₁ : ε + (ν : ℝ) / ((N : ℝ) + 1) * K ≤ Z₁) :
    ‖composedApprox - fderiv ℝ G ā‖ ≤ Z₁ := by
  have hν : (0 : ℝ) ≤ (ν : ℝ) / ((N : ℝ) + 1) := div_nonneg ν.2.le (by positivity)
  apply ContinuousLinearMap.opNorm_le_bound _
    (le_trans (add_nonneg hε (mul_nonneg hν hK)) hZ₁)
  intro h
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg
    (le_trans (add_nonneg hε (mul_nonneg hν hK)) hZ₁) (norm_nonneg _))).mpr fun l => ?_
  refine ((chebyshev_Z₁_component_le_relaxed _ _ N (hneg h l) (hfin_le h l)
    (htail h l)).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hDφ h l) hν))).trans ?_
  have h1 := mul_le_mul_of_nonneg_right hZ₁ (norm_nonneg h)
  nlinarith [h1]

omit [NeZero L] in
/-- **Semi-major relaxed Chebyshev Z₁ bound**: `chebyshev_Z₁_le_relaxed` with the
sharper tail factor `(ν⁻¹ + ν)/(2(N+1))` (= `semiMajor ν / (N+1)`) in place of `ν/(N+1)`.

All hypotheses except the total bound `hZ₁` are identical to `chebyshev_Z₁_le_relaxed`,
so existing certificate obligations can be reused verbatim.

Total: `Z₁ ≤ ε + (ν⁻¹ + ν)/(2(N+1)) · K`. -/
lemma chebyshev_Z₁_le_semiMajor
    (N : ℕ) (composedApprox : XCheb ν L →L[ℝ] XCheb ν L)
    (G : XCheb ν L → XCheb ν L) (ā : XCheb ν L)
    (Dφ : XCheb ν L → Fin L → l1Chebyshev ν)
    -- Negative: difference is zero (from pass-through)
    (hneg : ∀ h : XCheb ν L, ∀ l : Fin L, ∀ m : ℕ,
      ((composedApprox - fderiv ℝ G ā) h l) (Int.negSucc m) = 0)
    -- Finite: per-component bound
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfin_le : ∀ h : XCheb ν L, ∀ l : Fin L,
      ∑ k : Fin (N + 1),
        ‖((composedApprox - fderiv ℝ G ā) h l) (↑(k : ℕ) : ℤ)‖ ≤ ε * ‖h‖)
    -- Tail: norm matches chebyshevShiftDiv(Dφ)
    (htail : ∀ h : XCheb ν L, ∀ l : Fin L, ∀ m : ℕ, N < m →
      ‖((composedApprox - fderiv ℝ G ā) h l) (↑m : ℤ)‖ =
        ‖(chebyshevShiftDiv (Dφ h l)) (↑m : ℤ)‖)
    -- Dφ norm bound
    {K : ℝ} (hK : 0 ≤ K)
    (hDφ : ∀ h : XCheb ν L, ∀ l : Fin L, ‖Dφ h l‖ ≤ K * ‖h‖)
    -- Total bound
    {Z₁ : ℝ} (hZ₁ : ε + ((ν : ℝ)⁻¹ + (ν : ℝ)) / (2 * ((N : ℝ) + 1)) * K ≤ Z₁) :
    ‖composedApprox - fderiv ℝ G ā‖ ≤ Z₁ := by
  have hν0 : (0 : ℝ) < (ν : ℝ) := ν.2
  have hν : (0 : ℝ) ≤ ((ν : ℝ)⁻¹ + (ν : ℝ)) / (2 * ((N : ℝ) + 1)) :=
    div_nonneg (add_nonneg (inv_pos.mpr hν0).le hν0.le) (by positivity)
  apply ContinuousLinearMap.opNorm_le_bound _
    (le_trans (add_nonneg hε (mul_nonneg hν hK)) hZ₁)
  intro h
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg
    (le_trans (add_nonneg hε (mul_nonneg hν hK)) hZ₁) (norm_nonneg _))).mpr fun l => ?_
  refine ((chebyshev_Z₁_component_le_semiMajor _ _ N (hneg h l) (hfin_le h l)
    (htail h l)).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hDφ h l) hν))).trans ?_
  have h1 := mul_le_mul_of_nonneg_right hZ₁ (norm_nonneg h)
  nlinarith [h1]

/-! ## Chebyshev System Theorem

Existence and uniqueness of a zero of the composed Chebyshev IVP map,
via `general_radii_polynomial_theorem` with `A = identity`.

The key bound `hZ₁` is assembled using `chebyshev_Z₁_le`, which chains:
  `chebyshevShiftDiv_tailTsum_le_div` → `chebyshev_Z₁_component_norm_le` → operator norm

The user provides the composed map `G`, composed approximate derivative `composedApprox`,
approximate solution `ā`, and the four numerical bounds Y₀, Z₀, Z₁, Z₂. -/

omit [NeZero L] in
/-- **Chebyshev System Theorem**: existence and uniqueness of a zero of `G`
in `closedBall ā r₀`, given the radii polynomial `Z₂·r₀² - (1 - Z₀ - Z₁)·r₀ + Y₀ < 0`.

Instantiates `general_radii_polynomial_theorem` (Theorem 7.6.2) with `A = identity`.
The Z₁ bound is typically supplied by `chebyshev_Z₁_le`. -/
theorem chebyshev_system_theorem
    (G : XCheb ν L → XCheb ν L) (ā : XCheb ν L)
    (hG_diff : Differentiable ℝ G)
    (composedApprox : XCheb ν L →L[ℝ] XCheb ν L)
    {Y₀ Z₀ Z₁ Z₂_val r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : ‖G ā‖ ≤ Y₀)
    (hZ₀ : ‖ContinuousLinearMap.id ℝ (XCheb ν L) - composedApprox‖ ≤ Z₀)
    (hZ₁ : ‖composedApprox - fderiv ℝ G ā‖ ≤ Z₁)
    (hZ₂ : ∀ c ∈ Metric.closedBall ā r₀,
      ‖fderiv ℝ G c - fderiv ℝ G ā‖ ≤ Z₂_val * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂_val) r₀ < 0) :
    ∃! xTilde ∈ Metric.closedBall ā r₀, G xTilde = 0 :=
  general_radii_polynomial_theorem
    (A := ContinuousLinearMap.id ℝ _)
    (A_dagger := composedApprox)
    hr₀ hY₀ hZ₀ hZ₁
    (fun c hc => by simp only [ContinuousLinearMap.id_comp]; exact hZ₂ c hc)
    hG_diff h_radii (fun _ _ h => h)

/-! ## Factorization through the U-basis

`chebyshevShiftDiv` is not primitive: it factors exactly (every mode, including
`k = 1`) through the T→U basis conversion and U-integration,

  `chebyshevShiftDiv = -(uIntegrate ∘ chebyshevToU)`,

which is the coefficient-level statement of `∫ T'_k dt`-inversion via
`T_m = (U_m - U_{m-2})/2` and `∫ U_{k-1} = T_k/k`. The `1/(2k)` in `tailDiag`
is the product of the conversion's `1/2` and the U-integration's `1/k`.

This section lives here (not in `UConversion.lean`) because `chebyshevShiftDiv_seq`
is private to this file. -/

/-- **U-factorization of the Chebyshev integration tail**:
`chebyshevShiftDiv c = -(uIntegrate (chebyshevToU c))`, exactly, mode by mode. -/
theorem chebyshevShiftDiv_eq_neg_uIntegrate_chebyshevToU (c : l1Chebyshev ν) :
    chebyshevShiftDiv c = -(uIntegrate (chebyshevToU c)) := by
  apply lpOneAlg.ext_toRealSeq; funext k
  have hneg : lpOneAlg.toRealSeq (-(uIntegrate (chebyshevToU c))) k =
      -(lpOneAlg.toRealSeq (uIntegrate (chebyshevToU c)) k) := rfl
  rw [chebyshevShiftDiv_toSeq, hneg]
  cases k with
  | ofNat n =>
    cases n with
    | zero =>
      have h1 : chebyshevShiftDiv_seq c (Int.ofNat 0) = 0 := chebyshevShiftDiv_seq_zero c
      have h2 : lpOneAlg.toRealSeq (uIntegrate (chebyshevToU c)) (Int.ofNat 0) = 0 :=
        uIntegrate_toSeq_zero (chebyshevToU c)
      rw [h1, h2, neg_zero]
    | succ n =>
      have h1 : chebyshevShiftDiv_seq c (Int.ofNat (n + 1)) =
          (l1Chebyshev.toSeq c (↑(n + 1) + 1) - l1Chebyshev.toSeq c (↑(n + 1) - 1)) /
            (2 * ((n + 1 : ℕ) : ℝ)) :=
        chebyshevShiftDiv_seq_pos c (n + 1) (by omega)
      have h2 : lpOneAlg.toRealSeq (uIntegrate (chebyshevToU c)) (Int.ofNat (n + 1)) =
          l1Weighted.toSeq (chebyshevToU c) n / (↑n + 1) :=
        uIntegrate_toSeq_succ (chebyshevToU c) n
      rw [h1, h2, chebyshevToU_toSeq]
      have e1 : ((↑(n + 1) : ℤ)) + 1 = (↑n : ℤ) + 2 := by omega
      have e2 : ((↑(n + 1) : ℤ)) - 1 = (↑n : ℤ) := by omega
      rw [e1, e2]
      have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  | negSucc m =>
    have h1 : chebyshevShiftDiv_seq c (Int.negSucc m) = 0 := chebyshevShiftDiv_seq_neg c m
    have h2 : lpOneAlg.toRealSeq (uIntegrate (chebyshevToU c)) (Int.negSucc m) = 0 :=
      uIntegrate_toSeq_negSucc (chebyshevToU c) m
    rw [h1, h2, neg_zero]

/-- Sharper norm bound from the U-factorization:
`‖chebyshevShiftDiv c‖ ≤ (ν/2 + 1/(2ν))·‖c‖`, the product of `‖uIntegrate‖ ≤ ν`
and `‖chebyshevToU‖ ≤ (1 + ν⁻²)/2`. Strictly sharper than the direct bound
`chebyshevShiftDiv_norm_le` (`≤ ν·‖c‖`), which it recovers since `1/(2ν) ≤ ν/2`
for `ν ≥ 1`. -/
theorem chebyshevShiftDiv_norm_le' (c : l1Chebyshev ν) :
    ‖chebyshevShiftDiv c‖ ≤ ((ν : ℝ) / 2 + 1 / (2 * ν)) * ‖c‖ := by
  rw [chebyshevShiftDiv_eq_neg_uIntegrate_chebyshevToU, norm_neg]
  refine (uIntegrate_norm_le (chebyshevToU c)).trans ?_
  have h1 : (ν : ℝ) * ‖chebyshevToU c‖ ≤
      (ν : ℝ) * ((1 + ((ν : ℝ) ^ 2)⁻¹) / 2 * ‖c‖) :=
    mul_le_mul_of_nonneg_left (chebyshevToU_norm_le_sharp c) ν.2.le
  refine h1.trans (le_of_eq ?_)
  have hν : (ν : ℝ) ≠ 0 := ν.2.ne'
  field_simp

end ChebyshevIVP

end
