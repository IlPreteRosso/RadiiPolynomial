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
(`chebyshevShiftDiv_toSeq_natCast`); for `k ≤ 0`: `(chebyshevShiftDiv c)_k = 0`
(`chebyshevShiftDiv_toSeq_zero`, `chebyshevShiftDiv_toSeq_negSucc`).

This arises from the Chebyshev integration formula:
`∫ T_k(s) ds = (T_{k+1}/(k+1) - T_{k-1}/(k-1)) / 2` for `k ≥ 2`.

The operator is defined by its factorization through the U-basis,

  `chebyshevShiftDiv = -(uIntegrate ∘ chebyshevToU)`,

the coefficient-level statement of `∫ T'_k dt`-inversion via `T_m = (U_m - U_{m-2})/2` and
`∫ U_{k-1} = T_k/k`. The `1/(2k)` in `tailDiag` is the product of the conversion's `1/2` and
the U-integration's `1/k`. Linearity and the norm bounds come from the two bundled
U-conversion maps (`chebyshevShiftDiv_CLM`, `chebyshevShiftDiv_norm_le'`).

On tail modes `k > N`, when `A.tailDiag = 1/(2k)`, the composed map is
`G(a)_k = a_k + chebyshevShiftDiv(φ(a))_k` (`chebyshevIvpMap_mem_of_tailDiag_half` below). -/

/-- The Chebyshev shift-divide operator as an `l1Chebyshev ν` element: by definition the
U-factorization `-(uIntegrate (chebyshevToU c))`. -/
def chebyshevShiftDiv (c : l1Chebyshev ν) : l1Chebyshev ν :=
  -(uIntegrate (chebyshevToU c))


/-- Mode `0` of the shift-divide operator vanishes. -/
theorem chebyshevShiftDiv_toSeq_zero (c : l1Chebyshev ν) :
    l1Chebyshev.toSeq (chebyshevShiftDiv c) 0 = 0 := by
  rw [chebyshevShiftDiv, l1Chebyshev.toSeq_neg]
  show -(lpOneAlg.toRealSeq (uIntegrate (chebyshevToU c)) 0) = 0
  rw [uIntegrate_toSeq_zero, neg_zero]

/-- The negative modes of the shift-divide operator vanish. -/
theorem chebyshevShiftDiv_toSeq_negSucc (c : l1Chebyshev ν) (m : ℕ) :
    l1Chebyshev.toSeq (chebyshevShiftDiv c) (Int.negSucc m) = 0 := by
  rw [chebyshevShiftDiv, l1Chebyshev.toSeq_neg]
  show -(lpOneAlg.toRealSeq (uIntegrate (chebyshevToU c)) _) = 0
  rw [uIntegrate_toSeq_negSucc, neg_zero]

/-- The positive modes of the shift-divide operator:
`(chebyshevShiftDiv c)_k = (c_{k+1} - c_{k-1}) / (2k)` for `k ≥ 1`. -/
theorem chebyshevShiftDiv_toSeq_natCast (c : l1Chebyshev ν) (k : ℕ) (hk : k ≠ 0) :
    l1Chebyshev.toSeq (chebyshevShiftDiv c) (k : ℤ) =
      (l1Chebyshev.toSeq c (↑k + 1) - l1Chebyshev.toSeq c (↑k - 1)) / (2 * (k : ℝ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [chebyshevShiftDiv, l1Chebyshev.toSeq_neg]
  show -(lpOneAlg.toRealSeq (uIntegrate (chebyshevToU c)) (↑(n + 1) : ℤ)) = _
  rw [uIntegrate_toSeq_succ, chebyshevToU_toSeq,
    show ((↑(n + 1) : ℕ) : ℤ) + 1 = (↑n : ℤ) + 2 by push_cast; ring,
    show ((↑(n + 1) : ℕ) : ℤ) - 1 = (↑n : ℤ) by push_cast; ring]
  push_cast
  field_simp
  ring

/-- The Chebyshev shift-divide as a continuous linear map: the composite of the bundled
U-conversion maps. Analogue of `shiftDivN_CLM`; `chebyshevShiftDiv_CLM c = chebyshevShiftDiv c`
holds by `rfl`. -/
noncomputable def chebyshevShiftDiv_CLM : l1Chebyshev ν →L[ℝ] l1Chebyshev ν :=
  -((uIntegrate_CLM (ν := ν)).comp chebyshevToU_CLM)

/-! ### Linearity of chebyshevShiftDiv -/



/-! ### Norm bounds -/



/-! ## ℕ → ℤ Embedding for Composed Map

The IVP coefficients `F(a)` and `A.action(F(a))` are ℕ-indexed.
To get back to `l1Chebyshev ν` (ℤ-indexed), embed by mapping `n : ℕ ↦ (n : ℤ)`
with zeros on negative indices. -/

/-- Embed an ℕ-indexed coefficient sequence into ℤ-indexed `ScaledRealZ ν`.
Maps `n : ℕ ↦ ofReal (↑n) (seq n)` for non-negative ℤ, and `0` for negative. -/
def embedNatToInt (seq : ℕ → ℝ) : ∀ k : ℤ, ScaledRealZ ν k :=
  fun k => match k with
  | (n : ℕ) => FiberTrivialization.equiv (E := ScaledRealZ ν) (↑n) (seq n)
  | (Int.negSucc _) => 0

/-! ## Composed Map G = A ∘ F -/

/-- Embed ℕ-indexed IVP result into ℤ, **passing through** negative modes from `base`.

On non-negative modes `k ≥ 0`: applies `ofReal` to the ℕ-indexed `seq`.
On negative modes `k < 0`: preserves the value from `base`.

The IVP equations do not constrain the negative modes: the IVP operator only acts on
ℕ-modes, and negative modes are inert. -/
def embedWithPassThrough (seq : ℕ → ℝ) (base : l1Chebyshev ν) :
    ∀ k : ℤ, ScaledRealZ ν k :=
  fun k => match k with
  | (n : ℕ) => FiberTrivialization.equiv (E := ScaledRealZ ν) (↑n) (seq n)
  | Int.negSucc m => base (Int.negSucc m)

/-! ### Fiber values, membership, and norms of the embeddings -/

omit [Fact (1 ≤ (ν : ℝ))] in
@[simp] lemma embedNatToInt_natCast (seq : ℕ → ℝ) (n : ℕ) :
    embedNatToInt (ν := ν) seq (↑n : ℤ)
      = FiberTrivialization.equiv (E := ScaledRealZ ν) (↑n) (seq n) := rfl

omit [Fact (1 ≤ (ν : ℝ))] in
@[simp] lemma embedNatToInt_negSucc (seq : ℕ → ℝ) (m : ℕ) :
    embedNatToInt (ν := ν) seq (Int.negSucc m) = 0 := rfl

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
    simp [htail n hlt]
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
      show ‖FiberTrivialization.equiv (E := ScaledRealZ ν) (↑n) (seq n)‖ = 0
      rw [htail n hn, FiberTrivialization.equiv_zero, norm_zero])
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
  show ‖FiberTrivialization.equiv (E := ScaledRealZ ν) (↑(n : ℕ)) (seq (n : ℕ))‖ = _
  rw [ScaledRealZ.norm_equiv_apply]
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
  have hg_natval : ∀ n : ℕ, g ↑n
      = ‖FiberTrivialization.equiv (E := ScaledRealZ ν) (↑n : ℤ) (seq n)‖ := fun n => rfl
  have hg_negval : ∀ n : ℕ, g (-(↑n + 1)) = ‖base (Int.negSucc n)‖ := by
    intro n
    show g (-(↑n + 1 : ℤ)) = _
    rw [show -(↑n + 1 : ℤ) = Int.negSucc n from by omega]
    rfl
  have h_decomp : ‖(⟨⟨embedWithPassThrough seq base, hmem⟩⟩ : l1Chebyshev ν)‖
      = (∑' n : ℕ, g ↑n) + ∑' n : ℕ, g (-(↑n + 1)) :=
    lpOneAlg.norm_eq_tsum_natCast_add_tsum_neg _
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
    rw [hg_natval, ScaledRealZ.norm_equiv_apply]
    simp
  have htail_le : (∑' n : ℕ, g ↑(n + (N + 1))) ≤ ‖base‖ := by
    rw [tsum_congr (fun n : ℕ => show g ↑(n + (N + 1)) = ‖base (↑(n + (N + 1)) : ℤ)‖ by
      rw [hg_natval, htail _ (by omega), ScaledRealZ.norm_equiv_apply,
        ← l1Chebyshev.norm_fiber])]
    rw [lpOneAlg.norm_eq_tsum]
    exact tsum_comp_le_tsum_of_inj (lpOneAlg.summable_norm base)
      (fun _ => norm_nonneg _) fun n m h => by simpa using h
  rw [h_decomp, h_split]
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
`A.action(F(a))_n = (1/(2n)) · (2n·a_n + c_{n+1} - c_{n-1}) = a_n + (chebyshevShiftDiv c)_n`
where `c = φ(a)`. Both `a` and `chebyshevShiftDiv(c)` are in ℓ¹, so the result is in ℓ¹. -/

omit [NeZero L] in
/-- On tail modes, the action with tailDiag = 1/(2k) equals `a_k + (chebyshevShiftDiv c)_k`. -/
private lemma action_chebyshev_tail_eq {N : ℕ}
    (A : SystemBlockDiagData L N)
    (φ : XCheb ν L → Fin L → l1Chebyshev ν)
    (p : Fin L → ℝ)
    (htail : ∀ l : Fin L, ∀ n, N < n → A.tailDiag l n = 1 / (2 * (↑n : ℝ)))
    (a : XCheb ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    A.action (chebyshevIvpCoeffs φ p a) l n =
      l1Chebyshev.toSeq (a l) (↑n : ℤ) +
        l1Chebyshev.toSeq (chebyshevShiftDiv (φ a l)) (↑n : ℤ) := by
  rw [SystemBlockDiagData.action_tail _ _ _ _ hn, htail l n hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [chebyshevIvpCoeffs]
  rw [chebyshevShiftDiv_toSeq_natCast (φ a l) (m + 1) (by omega)]
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
    show FiberTrivialization.equiv (E := ScaledRealZ ν) (↑n) (seq n) = _
    rw [show seq n = _ from action_chebyshev_tail_eq A φ p htail a l n hn,
      FiberTrivialization.equiv_add]
    congr 1
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
The `1/(2k)` factor gives a tail-dependent estimate that tightens as modes grow.
The `ν⁻¹` weight on the
`c(k+1)` term is exact (`|c_{k+1}| ν^k = ν⁻¹ · |c_{k+1}| ν^{k+1}`, needs only `0 < ν`). -/
private lemma chebyshevShiftDiv_elem_tight_le (c : l1Chebyshev ν) (k : ℕ) (hk : 0 < k) :
    ‖(chebyshevShiftDiv c) (↑k : ℤ)‖ ≤
    1 / (2 * (k : ℝ)) *
      ((ν : ℝ)⁻¹ * ‖c ((↑k : ℤ) + 1)‖ + (ν : ℝ) * ‖c ((↑k : ℤ) + (-1))‖) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have e1 : ((↑(n + 1) : ℕ) : ℤ) + 1 = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
  have e2 : ((↑(n + 1) : ℕ) : ℤ) + (-1) = ((n : ℕ) : ℤ) := by push_cast; ring
  rw [norm_fiber_natCast, chebyshevShiftDiv_toSeq_natCast c (n + 1) (by omega), e1, e2,
    norm_fiber_natCast, norm_fiber_natCast,
    show ((↑(n + 1) : ℕ) : ℤ) - 1 = ((n : ℕ) : ℤ) by push_cast; ring]
  set a := l1Chebyshev.toSeq c ((n + 2 : ℕ) : ℤ)
  set b := l1Chebyshev.toSeq c ((n : ℕ) : ℤ)
  have hν0 : (0 : ℝ) < ν := ν.2
  have h2k : (0 : ℝ) < 2 * ((n + 1 : ℕ) : ℝ) := by positivity
  rw [abs_div, abs_of_pos h2k, div_mul_eq_mul_div, one_div_mul_eq_div,
    div_le_div_iff_of_pos_right h2k]
  have hpow : (ν : ℝ) ^ (n + 1) = ν ^ n * ν := pow_succ _ _
  have hpow2 : (ν : ℝ) ^ (n + 2) = ν ^ n * ν * ν := by ring
  rw [hpow, hpow2]
  have hinv : (ν : ℝ)⁻¹ * (|a| * (ν ^ n * ν * ν)) = |a| * (ν ^ n * ν) := by
    field_simp
  rw [hinv]
  have := abs_sub a b
  have hp : (0 : ℝ) ≤ ν ^ n * ν := by positivity
  nlinarith [abs_nonneg a, abs_nonneg b]

/-- **Semi-major tail tsum bound**:
`∑' n, ‖chebyshevShiftDiv(c)(n+N+1)‖ ≤ (ν⁻¹ + ν)/(2(N+1)) · ‖c‖`.

The prefactor `(ν⁻¹ + ν)/2` is the semi-major axis of the Bernstein ellipse `E_ν`:
the bound equals `CrossGeometry.semiMajor ν / (N + 1)`; the statement keeps the literal
`((ν:ℝ)⁻¹ + ν)/2`.
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



/-- The semi-major tail factor is at most the `ν/(N+1)` factor (`1 ≤ ν`, so `ν⁻¹ ≤ ν`).
It derives the `ν/(N+1)` Z₁ faces from the semi-major ones. -/
theorem semiMajor_div_le_div (N : ℕ) :
    ((ν : ℝ)⁻¹ + (ν : ℝ)) / (2 * ((N : ℝ) + 1)) ≤ (ν : ℝ) / ((N : ℝ) + 1) := by
  have hν : (1 : ℝ) ≤ ν := Fact.out
  have hinv : (ν : ℝ)⁻¹ ≤ ν := (inv_le_one_of_one_le₀ hν).trans hν
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [show (0 : ℝ) ≤ (N : ℝ) + 1 by positivity]

/-! ## Chebyshev Z₁ Component Bounds

Per-component Z₁ bounds for `d` vanishing on the negative modes, with a finite-mode
contribution `ε` and a tail equal in norm to `chebyshevShiftDiv w`. The core is the
semi-major form (`chebyshev_Z₁_component_le_semiMajor`, tail factor `(ν⁻¹ + ν)/(2(N+1))`);
the `ν/(N+1)` forms follow from `semiMajor_div_le_div`, and the forms with `d = 0` on the
modes `k ≤ N` are their `ε = 0` cases.

This is the ℤ-indexed analogue of the Taylor recipe bound (`shiftDivN_tailTsum_le_div` fed into
the private `Z₁_component_le_exact` behind `IVP.ivp_Z₁_le`,
`Applications/IVP/Taylor/Operator.lean`). -/

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
  have h_nat : Summable (fun n : ℕ => ‖d (n : ℤ)‖) :=
    (lpOneAlg.summable_norm d).comp_injective fun _ _ h => by omega
  rw [lpOneAlg.norm_eq_tsum_natCast_of_neg d fun n => by
      rw [show -((n : ℤ) + 1) = Int.negSucc n by omega]; exact hneg n,
    ← h_nat.sum_add_tsum_nat_add (N + 1),
    ← Fin.sum_univ_eq_sum_range (f := fun n => ‖d (n : ℤ)‖)]
  exact add_le_add hfin_le ((tsum_congr fun n => htail (n + (N + 1)) (by omega)).trans_le
    (chebyshevShiftDiv_tailTsum_le_semiMajor_div w N))

/-- **Relaxed** Chebyshev Z₁ per-component bound.
Replaces the `hfin` (zero on all k ≤ N) assumption with separate bounds:
- `hneg`: d = 0 on negative modes (from pass-through)
- `hfin_le`: finite-mode contribution bounded by ε
- `htail`: tail matches chebyshevShiftDiv(w)

Result: `‖d‖ ≤ ε + ν/(N+1) · ‖w‖`. Handles the Chebyshev IVP case where the mode-0
alternating sum couples all modes, preventing `d` from vanishing on finite modes. -/
lemma chebyshev_Z₁_component_le_relaxed (d w : l1Chebyshev ν) (N : ℕ)
    (hneg : ∀ m : ℕ, d (Int.negSucc m) = 0)
    {ε : ℝ}
    (hfin_le : ∑ k : Fin (N + 1), ‖d (↑(k : ℕ) : ℤ)‖ ≤ ε)
    (htail : ∀ m : ℕ, N < m →
      ‖d (↑m : ℤ)‖ = ‖(chebyshevShiftDiv w) (↑m : ℤ)‖) :
    ‖d‖ ≤ ε + (ν : ℝ) / ((N : ℝ) + 1) * ‖w‖ :=
  (chebyshev_Z₁_component_le_semiMajor d w N hneg hfin_le htail).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (semiMajor_div_le_div N) (norm_nonneg w)))

/-- Variant using norm equality on tail (handles sign: works when tail difference
is `±chebyshevShiftDiv(w)`, not just `+`). The `ε = 0` case of
`chebyshev_Z₁_component_le_relaxed`. -/
lemma chebyshev_Z₁_component_norm_le (d w : l1Chebyshev ν) (N : ℕ)
    (hfin : ∀ k : ℤ, k ≤ ↑N → d k = 0)
    (htail : ∀ m : ℕ, N < m → ‖d (↑m : ℤ)‖ = ‖(chebyshevShiftDiv w) (↑m : ℤ)‖) :
    ‖d‖ ≤ (ν : ℝ) / ((N : ℝ) + 1) * ‖w‖ := by
  simpa using chebyshev_Z₁_component_le_relaxed d w N (fun m => hfin _ (by omega)) (ε := 0)
    (Finset.sum_eq_zero fun k _ => by rw [hfin _ (by omega), norm_zero]).le htail

/-- Chebyshev Z₁ per-component bound.
If `d : l1Chebyshev` vanishes for `k ≤ N` and equals `chebyshevShiftDiv(w)` for `k > N`,
then `‖d‖ ≤ ν/(N+1) · ‖w‖`. -/
lemma chebyshev_Z₁_component_le (d w : l1Chebyshev ν) (N : ℕ)
    (hfin : ∀ k : ℤ, k ≤ ↑N → d k = 0)
    (htail : ∀ m : ℕ, N < m → d (↑m : ℤ) = (chebyshevShiftDiv w) (↑m : ℤ)) :
    ‖d‖ ≤ (ν : ℝ) / ((N : ℝ) + 1) * ‖w‖ :=
  chebyshev_Z₁_component_norm_le d w N hfin fun m hm => congrArg (‖·‖) (htail m hm)

/-! ## Chebyshev Z₁ Operator Norm Bound

Assembles per-component Z₁ bounds into `‖composedApprox - fderiv G ā‖ ≤ Z₁`.
Analogous to `ivp_Z₁_le` from `Applications/IVP/Taylor/Operator.lean`. -/

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

omit [NeZero L] in
/-- **Relaxed Chebyshev Z₁ bound** for IVPs where mode-0 couples all modes.

Unlike `chebyshev_Z₁_le`, does NOT require `hfin` (composedApprox = fderiv G on k ≤ N).
Instead, takes separate bounds for the finite-mode contribution (ε per component)
and the tail contribution (via Dφ norm bound K).

Total: `Z₁ ≤ ε + ν/(N+1) · K`; a corollary of `chebyshev_Z₁_le_semiMajor` through
`semiMajor_div_le_div` (same hypotheses).

Use when the IVP derivative DF is not lower-triangular (Chebyshev mode-0 alternating sum
couples all modes, creating a leakage into finite modes, heuristically of size O(1/ν^{N+1});
that estimate is not a statement of this file). -/
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
    ‖composedApprox - fderiv ℝ G ā‖ ≤ Z₁ :=
  chebyshev_Z₁_le_semiMajor N composedApprox G ā Dφ hneg hε hfin_le htail hK hDφ
    ((add_le_add le_rfl (mul_le_mul_of_nonneg_right (semiMajor_div_le_div N) hK)).trans hZ₁)


/-! ## Chebyshev System Theorem

Existence and uniqueness of a zero of the composed Chebyshev IVP map,
via `general_radii_polynomial_theorem` with `A = identity`.

The key bound `hZ₁` can be assembled using `chebyshev_Z₁_le` (finite modes cancel) or,
when they do not, `chebyshev_Z₁_le_relaxed` / `chebyshev_Z₁_le_semiMajor`; all three rest on
`chebyshevShiftDiv_tailTsum_le_semiMajor_div` through `chebyshev_Z₁_component_le_semiMajor`.

The user provides the composed map `G`, composed approximate derivative `composedApprox`,
approximate solution `ā`, and the four numerical bounds Y₀, Z₀, Z₁, Z₂. -/

omit [NeZero L] in
/-- **Chebyshev System Theorem**: existence and uniqueness of a zero of `G`
in `closedBall ā r₀`, given the radii polynomial `Z₂·r₀² - (1 - Z₀ - Z₁)·r₀ + Y₀ < 0`.

Instantiates `general_radii_polynomial_theorem` (Theorem 7.6.2) with `A = identity`.
The Z₁ bound can be supplied by `chebyshev_Z₁_le`; the library's Chebyshev certificates,
whose row 0 couples all modes, use `chebyshev_Z₁_le_relaxed`. -/
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

end ChebyshevIVP

end
