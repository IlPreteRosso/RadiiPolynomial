import RadiiPolynomial.source.Chebyshev.L1ChebyshevAlgebra
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import RadiiPolynomial.source.BlockDiag.Concrete

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
  AddLp.summable_abs_toRealSeq a

/-- The alternating sum `∑_{n≥1} (-1)^n a_n` converges for `a ∈ l1Chebyshev ν`.
This is the Chebyshev series evaluated at `t = -1`: `u(-1) = a_0 + 2∑ (-1)^n a_n`. -/
theorem summable_alternating_toSeq (a : l1Chebyshev ν) :
    Summable (fun n : ℕ => (-1 : ℝ) ^ (n + 1) * l1Chebyshev.toSeq a (↑(n + 1) : ℤ)) := by
  have habs : Summable (fun n : ℕ => |l1Chebyshev.toSeq a (↑(n + 1) : ℤ)|) :=
    (summable_abs_toSeq a).comp_injective (fun n m h => by omega)
  exact habs.of_norm_bounded fun n => by
    simp [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one]

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

@[simp] lemma chebyshevShiftDiv_seq_zero (c : l1Chebyshev ν) :
    chebyshevShiftDiv_seq c 0 = 0 := by simp [chebyshevShiftDiv_seq]

@[simp] lemma chebyshevShiftDiv_seq_neg (c : l1Chebyshev ν) (n : ℕ) :
    chebyshevShiftDiv_seq c (Int.negSucc n) = 0 := by simp [chebyshevShiftDiv_seq]

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

/-- Shifted subseries of `l1Chebyshev` norms are summable (shift invariance). -/
private lemma summable_norm_shift (c : l1Chebyshev ν) (s : ℤ) :
    Summable (fun n : ℕ => ‖c (↑n + s)‖) :=
  (AddLp.summable_norm c).comp_injective (fun n m h => by omega)

-- Per-element bound: |(a-b)/(2k)| * ν^k ≤ (ν/2)*(‖c(k+1)‖ + ‖c(k-1)‖).
private lemma chebyshevShiftDiv_fiber_le (c : l1Chebyshev ν) (k : ℕ) (hk : 0 < k) :
    ‖AddLpRingData.ofReal (E := ScaledRealZ ν) (↑k)
      (chebyshevShiftDiv_seq c (↑k))‖ ≤
    (ν : ℝ) / 2 * (‖c ((↑k : ℤ) + 1)‖ + ‖c ((↑k : ℤ) + (-1))‖) := by
  -- Unfold to real arithmetic
  rw [chebyshevShiftDiv_seq_pos c k (by omega)]
  simp only [ScaledRealZ.norm_addLpRingData_ofReal]
  rw [abs_div, abs_of_pos (show (0:ℝ) < 2 * (k:ℝ) by positivity)]
  rw [AddLp.norm_eq_abs_toReal_mul_weight c ((↑k : ℤ) + 1),
      AddLp.norm_eq_abs_toReal_mul_weight c ((↑k : ℤ) + (-1))]
  simp only [ScaledRealZ.norm_addLpRingData_ofReal, abs_one, one_mul]
  have hk1 : ((↑k : ℤ) + 1).natAbs = k + 1 := by omega
  have hk2 : ((↑k : ℤ) + (-1)).natAbs = k - 1 := by omega
  have hk0' : (↑k : ℤ).natAbs = k := by omega
  rw [hk1, hk2, hk0']
  -- Now goal is pure ℝ arithmetic with abs, pow, div
  set a := |AddLp.toRealSeq c ((↑k : ℤ) + 1)|
  set b := |AddLp.toRealSeq c ((↑k : ℤ) + (-1))|
  -- Key facts for nlinarith
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have hν1 : (1 : ℝ) ≤ ν := Fact.out
  have hν0 : (0 : ℝ) < ν := ν.2
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have htri : |AddLp.toRealSeq c ((↑k : ℤ) + 1) -
      AddLp.toRealSeq c ((↑k : ℤ) + (-1))| ≤ a + b := by
    have := norm_sub_le (AddLp.toRealSeq c ((↑k : ℤ) + 1))
      (AddLp.toRealSeq c ((↑k : ℤ) + (-1)))
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
  have h1 : |AddLp.toRealSeq c ((↑k : ℤ) + 1) - AddLp.toRealSeq c ((↑k : ℤ) + (-1))| *
      (ν : ℝ) ^ k ≤ (a + b) * (ν : ℝ) ^ k :=
    mul_le_mul_of_nonneg_right htri hpk.le
  have h2 : a * (ν : ℝ) ^ k ≤ a * (ν : ℝ) ^ (k + 1) :=
    mul_le_mul_of_nonneg_left hpk_le ha
  have h3 : (ν : ℝ) * (b * (ν : ℝ) ^ (k - 1)) = b * (ν : ℝ) ^ k := by
    nlinarith [heq]
  have h4 : (ν : ℝ) * (ν : ℝ) ^ (k + 1) = (ν : ℝ) ^ (k + 2) :=
    (mul_comm _ _).trans (pow_succ (ν : ℝ) (k + 1)).symm
  have h5 : a * (ν : ℝ) ^ k ≤ a * (ν : ℝ) ^ (k + 2) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hν1 (by omega)) ha
  -- Expand RHS: ν*(a*ν^{k+1}+b*ν^{k-1}) = a*ν^{k+2}+b*ν^k
  have h6 : (ν : ℝ) * (a * (ν : ℝ) ^ (k + 1) + b * (ν : ℝ) ^ (k - 1)) =
      a * (ν : ℝ) ^ (k + 2) + b * (ν : ℝ) ^ k := by nlinarith [h3, h4]
  -- Chain: LHS ≤ (a+b)*ν^k * 2 ≤ (a*ν^{k+2}+b*ν^k) * 2 ≤ ... * (2k)
  have h7 : a * (ν : ℝ) ^ (k + 2) + b * (ν : ℝ) ^ k ≥ 0 :=
    add_nonneg (mul_nonneg ha (pow_nonneg hν0.le _)) (mul_nonneg hb (pow_nonneg hν0.le _))
  -- Step-by-step chain avoiding nlinarith on products
  -- (1) |..|*ν^k*2 ≤ (a+b)*ν^k*2
  have s1 : |AddLp.toRealSeq c ((↑k : ℤ) + 1) - AddLp.toRealSeq c ((↑k : ℤ) + (-1))| *
      (ν : ℝ) ^ k * 2 ≤ (a + b) * (ν : ℝ) ^ k * 2 := by nlinarith [h1]
  -- (2) (a+b)*ν^k ≤ a*ν^{k+2}+b*ν^k
  have s2 : (a + b) * (ν : ℝ) ^ k ≤ a * (ν : ℝ) ^ (k + 2) + b * (ν : ℝ) ^ k := by linarith [h5]
  -- (3) ...*(2) ≤ ...*2k
  have s3 : (a * (ν : ℝ) ^ (k + 2) + b * (ν : ℝ) ^ k) * 2 ≤
      (a * (ν : ℝ) ^ (k + 2) + b * (ν : ℝ) ^ k) * (2 * ↑k) :=
    mul_le_mul_of_nonneg_left (by linarith [hk1']) h7
  -- (4) Chain via calc
  calc |AddLp.toRealSeq c ((↑k : ℤ) + 1) -
          AddLp.toRealSeq c ((↑k : ℤ) + (-1))| * (ν : ℝ) ^ k * 2
      ≤ (a + b) * (ν : ℝ) ^ k * 2 := s1
    _ ≤ (a * (ν : ℝ) ^ (k + 2) + b * (ν : ℝ) ^ k) * 2 := by nlinarith [s2]
    _ ≤ (a * (ν : ℝ) ^ (k + 2) + b * (ν : ℝ) ^ k) * (2 * ↑k) := s3
    _ = (ν : ℝ) * (a * (ν : ℝ) ^ (k + 1) + b * (ν : ℝ) ^ (k - 1)) * (2 * ↑k) := by
        nlinarith [h6]


private lemma chebyshevShiftDiv_memℓp (c : l1Chebyshev ν) :
    Memℓp (fun k : ℤ => AddLpRingData.ofReal (E := ScaledRealZ ν) k
      (chebyshevShiftDiv_seq c k)) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  have h1 := AddLp.summable_norm_shift c (1 : ℤ)
  have h2 := AddLp.summable_norm_shift c (-1 : ℤ)
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
      rw [this, AddLpRingData.ofReal_zero, norm_zero]
      exact mul_nonneg ν.2.le (add_nonneg (norm_nonneg _) (norm_nonneg _))
    | succ k =>
      refine (chebyshevShiftDiv_fiber_le c (k+1) (by omega)).trans ?_
      exact mul_le_mul_of_nonneg_right
        (div_le_self ν.2.le (by norm_num : (1:ℝ) ≤ 2))
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
  | negSucc n =>
    have : chebyshevShiftDiv_seq c (Int.negSucc n) = 0 := chebyshevShiftDiv_seq_neg c n
    rw [this, AddLpRingData.ofReal_zero, norm_zero]
    exact mul_nonneg ν.2.le (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The Chebyshev shift-divide operator as an `l1Chebyshev ν` element. -/
def chebyshevShiftDiv (c : l1Chebyshev ν) : l1Chebyshev ν :=
  ⟨⟨fun k => AddLpRingData.ofReal (E := ScaledRealZ ν) k (chebyshevShiftDiv_seq c k),
    chebyshevShiftDiv_memℓp c⟩⟩

@[simp] lemma chebyshevShiftDiv_toSeq (c : l1Chebyshev ν) (k : ℤ) :
    AddLp.toRealSeq (chebyshevShiftDiv c) k = chebyshevShiftDiv_seq c k := by
  simp [chebyshevShiftDiv, l1Chebyshev.toSeq, AddLp.toRealSeq, AddLpRingData.toReal_ofReal]

/-! ### Linearity of chebyshevShiftDiv -/

lemma chebyshevShiftDiv_add (c d : l1Chebyshev ν) :
    chebyshevShiftDiv (c + d) = chebyshevShiftDiv c + chebyshevShiftDiv d := by
  apply AddLp.ext_toRealSeq; funext k
  simp only [chebyshevShiftDiv_toSeq, AddLp.toRealSeq_add, Pi.add_apply]
  unfold chebyshevShiftDiv_seq l1Chebyshev.toSeq AddLp.toRealSeq
  cases k with
  | ofNat k => cases k with
    | zero => simp
    | succ k => simp [AddLpRingData.toReal_add]; ring
  | negSucc _ => simp

lemma chebyshevShiftDiv_smul (r : ℝ) (c : l1Chebyshev ν) :
    chebyshevShiftDiv (r • c) = r • chebyshevShiftDiv c := by
  apply AddLp.ext_toRealSeq
  rw [AddLp.toRealSeq_smul]; funext k
  simp only [Pi.smul_apply, smul_eq_mul, chebyshevShiftDiv_toSeq]
  -- chebyshevShiftDiv_seq (r • c) k = r * chebyshevShiftDiv_seq c k
  have hsmul : ∀ m : ℤ, l1Chebyshev.toSeq (r • c) m = r * l1Chebyshev.toSeq c m :=
    fun m => congr_fun (AddLp.toRealSeq_smul r c) m
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
        show AddLpRingData.ofReal (E := ScaledRealZ ν) 0 (chebyshevShiftDiv_seq c 0) = 0
        rw [chebyshevShiftDiv_seq_zero, AddLpRingData.ofReal_zero]
      rw [this, norm_zero]
      exact mul_nonneg (div_nonneg ν.2.le two_pos.le) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    | succ k => exact chebyshevShiftDiv_fiber_le c (k + 1) (by omega)
  | negSucc n =>
    have : (chebyshevShiftDiv c) (Int.negSucc n) = 0 := by
      show AddLpRingData.ofReal (E := ScaledRealZ ν) _ (chebyshevShiftDiv_seq c _) = 0
      rw [chebyshevShiftDiv_seq_neg, AddLpRingData.ofReal_zero]
    rw [this, norm_zero]
    exact mul_nonneg (div_nonneg ν.2.le two_pos.le) (add_nonneg (norm_nonneg _) (norm_nonneg _))

lemma chebyshevShiftDiv_norm_le (c : l1Chebyshev ν) :
    ‖chebyshevShiftDiv c‖ ≤ (ν : ℝ) * ‖c‖ := by
  rw [AddLp.norm_eq_tsum, AddLp.norm_eq_tsum]
  have h1 := AddLp.summable_norm_shift c (1 : ℤ)
  have h2 := AddLp.summable_norm_shift c (-1 : ℤ)
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
    (AddLp.summable_norm (chebyshevShiftDiv c)) hsb
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

lemma differentiable_chebyshevIvpTail (φ : XCheb ν L → Fin L → l1Chebyshev ν)
    (hφ : ∀ l, Differentiable ℝ (fun a : XCheb ν L => φ a l)) :
    Differentiable ℝ (chebyshevIvpTail φ) := by
  intro a; rw [differentiableAt_pi]; intro l
  show DifferentiableAt ℝ (fun a : XCheb ν L => a l + chebyshevShiftDiv_CLM (φ a l)) a
  have h1 : DifferentiableAt ℝ (fun a : XCheb ν L => a l) a :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => l1Chebyshev ν) l).differentiableAt
  have h2 : DifferentiableAt ℝ (fun a : XCheb ν L => chebyshevShiftDiv_CLM (φ a l)) a :=
    chebyshevShiftDiv_CLM.differentiableAt.comp a (hφ l a)
  exact DifferentiableAt.add h1 h2

/-! ## Fréchet Derivative of Tail -/

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
       chebyshevShiftDiv_CLM.comp (fderiv ℝ (fun a => φ a l) ā)) ā := by
    show HasFDerivAt ((fun a : XCheb ν L => a l) + fun a => chebyshevShiftDiv_CLM (φ a l)) _ ā
    exact ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin L => l1Chebyshev ν) l).hasFDerivAt).add
      (chebyshevShiftDiv_CLM.hasFDerivAt.comp ā (hφ l ā).hasFDerivAt)
  rw [show (fderiv ℝ (chebyshevIvpTail φ) ā h) l =
      (fderiv ℝ (fun a => (chebyshevIvpTail φ a) l) ā) h from by
    rw [fderiv_pi (fun i => differentiableAt_pi.mp
      (differentiable_chebyshevIvpTail φ hφ ā) i)]; rfl]
  rw [hd.fderiv]; simp [chebyshevIvpTail]

/-! ## ℕ → ℤ Embedding for Composed Map

The IVP coefficients `F(a)` and `A.action(F(a))` are ℕ-indexed.
To get back to `l1Chebyshev ν` (ℤ-indexed), embed by mapping `n : ℕ ↦ (n : ℤ)`
with zeros on negative indices. -/

/-- Embed an ℕ-indexed coefficient sequence into ℤ-indexed `ScaledRealZ ν`.
Maps `n : ℕ ↦ ofReal (↑n) (seq n)` for non-negative ℤ, and `0` for negative. -/
private def embedNatToInt (seq : ℕ → ℝ) : ∀ k : ℤ, ScaledRealZ ν k :=
  fun k => match k with
  | (n : ℕ) => AddLpRingData.ofReal (E := ScaledRealZ ν) (↑n) (seq n)
  | (Int.negSucc _) => 0

/-! ## Composed Map G = A ∘ F -/

/-- The composed Chebyshev IVP map `G = A ∘ F : XCheb → XCheb`.
Applies `A.action` to the ℕ-indexed `chebyshevIvpCoeffs`, then embeds
into ℤ-indexed `l1Chebyshev ν` via `embedNatToInt`.

The `hmem` hypothesis proves the result is in ℓ¹. In practice, this follows
from `A.tailDiag = 1/(2k)` cancelling the `2k` factor in eq. 14.11. -/
def chebyshevIvpMap (A : SystemBlockDiagData L N)
    (φ : XCheb ν L → Fin L → l1Chebyshev ν)
    (p : Fin L → ℝ)
    (hmem : ∀ a : XCheb ν L, ∀ l : Fin L,
      Memℓp (embedNatToInt (A.action (chebyshevIvpCoeffs φ p a) l) : ∀ k : ℤ, ScaledRealZ ν k) 1)
    (a : XCheb ν L) : XCheb ν L := fun l =>
  ⟨⟨embedNatToInt (A.action (chebyshevIvpCoeffs φ p a) l), hmem a l⟩⟩

end ChebyshevIVP

end
