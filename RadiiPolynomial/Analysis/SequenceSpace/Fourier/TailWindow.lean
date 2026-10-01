import RadiiPolynomial.Analysis.SequenceSpace.Fourier.Support
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Diagonal

/-!
# The exact finite-window norm of the tail-diagonal defect

On the bilateral geometric carrier `E = lpOneAlg ℤ (geomFiberZ 𝕜 ν)` over a complete normed
field with `ν ≥ 1`, fix a head window `P = headProj (winZ N)`, `Q = tailProj (winZ N)`, a
multiplier `b ∈ E` with band `m` (`b_i = 0` for `|i| > m`), a bounded tail diagonal
`R = diagCLM r C hr` and any bounded operator `M`. The bounded preconditioned defect is

`defect N M r C hr b = M P L_b Q + R L_b = defectHead N M b + defectTail r C hr b`.

Its columns are read through the weighted column ratio of `WeightedL1/Columns.lean`
(`colRatio_geom`: `‖T e_j‖ / ν^|j|`). Beyond the shell `N + m` the defect column is the tail
column (`colRatio_defect_far_eq_defectTail`), so once `‖r‖` is two-ray nonincreasing beyond
`max (N + 1) K₀` the columns are antitone outward and the full operator norm is the finite
maximum over `|j| ≤ m + max (N + 1) K₀` (`opNorm_defect_eq_sup'`), attained as a weighted column
ratio at an atom (`defect_attained`). This holds for every bounded `M` and `r`. Under range
(`P M = M`) and head vanishing (`r = 0` on the head) the columns split as `headCol + tailCol`
(`colRatio_defect_explicit`, `opNorm_defect_eq_sup'_explicit`), also in the joint form with a
head block `Z` (`opNorm_joint_defect_eq_sup'`, `opNorm_joint_defect_sub_eq_sup'`).

The aggregation laws are the L001 faces `lpOneAlg.colRatio_add_of_head_tail`,
`lpOneAlg.opNorm_add_eq_iSup`, `lpOneAlg.opNorm_joint_eq_iSup`; the window maximum principle is
`iSup_eq_sup'_of_far_antitone` (`Fourier/Support.lean`).

`defect_attained` is attainment of the weighted column ratio at `single j 1`: over a general
complete nontrivially normed field it does not assert a scalar multiple of that atom of norm one.

Operator-norm statements need `[NontriviallyNormedField 𝕜]`; the remaining statements hold over
`[NormedField 𝕜] [CompleteSpace 𝕜]` (completeness carries the `ℤ`-convolution); `tailCol` needs
no multiplication and lives over a bare `[NormedField 𝕜]`.
-/

noncomputable section

namespace RadiiPolynomial.Fourier

/-! ### The column ratio on the geometric carrier -/

section Columns

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **(T14, L002.)** On the geometric carrier the weighted column ratio is
`‖T e_j‖ / ν^|j|`. -/
theorem colRatio_geom (T : lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] F) (j : ℤ) :
    lpOneAlg.colRatio T j = ‖T (lpOneAlg.single j 1)‖ / (ν : ℝ) ^ j.natAbs := by
  rw [lpOneAlg.colRatio, geomFiberZ_weight]

end Columns

/-! ### The explicit tail column (no multiplication) -/

section TailCol

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}

/-- **(T21, L002.)** The explicit tail column
`s_j = (Σ_{|i| ≤ m} ‖r_{j+i}‖ ‖b_i‖ ν^{|j+i|}) / ν^{|j|}`. -/
def tailCol (m : ℕ) (r : ℤ → 𝕜) (b : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (j : ℤ) : ℝ :=
  (∑ i ∈ winZ m, ‖r (j + i)‖ * ‖lpOneAlg.toRealSeq b i‖ * (ν : ℝ) ^ (j + i).natAbs)
    / (ν : ℝ) ^ j.natAbs

end TailCol

/-! ### The defect and its columns -/

section Defect

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

local notation "𝓔" => lpOneAlg ℤ (geomFiberZ 𝕜 ν)
local notation "𝓟[" N "]" => (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : 𝓔 →L[𝕜] 𝓔)
local notation "𝓠[" N "]" => (lpOneAlg.tailProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : 𝓔 →L[𝕜] 𝓔)
local notation "𝓡[" r ", " C ",
    " hr "]" => (lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) r C hr : 𝓔 →L[𝕜] 𝓔)
local notation "𝓛[" b "]" => (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) b : 𝓔 →L[𝕜] 𝓔)

/-- **(T15, L002.)** The head (leakage) term `M P L_b Q`. -/
def defectHead (N : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (b : 𝓔) : 𝓔 →L[𝕜] 𝓔 :=
  M ∘L 𝓟[N] ∘L 𝓛[b] ∘L 𝓠[N]

/-- **(T16, L002.)** The tail term `R L_b`. -/
def defectTail (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔) : 𝓔 →L[𝕜] 𝓔 :=
  𝓡[r, C, hr] ∘L 𝓛[b]

/-- **(T17, L002.)** The bounded preconditioned defect `M P L_b Q + R L_b`. -/
def defect (N : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔) :
    𝓔 →L[𝕜] 𝓔 :=
  M ∘L 𝓟[N] ∘L 𝓛[b] ∘L 𝓠[N] + 𝓡[r, C, hr] ∘L 𝓛[b]

/-- **(T17, L002.)** The defect is the sum of its head and tail terms. -/
theorem defect_eq (N : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔) :
    defect N M r C hr b = defectHead N M b + defectTail r C hr b :=
  rfl

/-- **(T18, L002.)** The head-term column at an atom. -/
theorem defectHead_single (N : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (b : 𝓔) (j : ℤ) :
    defectHead N M b (lpOneAlg.single j 1)
      = if j.natAbs ≤ N then 0 else M (𝓟[N] (b * lpOneAlg.single j 1)) := by
  simp only [defectHead, ContinuousLinearMap.comp_apply, lpOneAlg.tailProj_single, mem_winZ]
  split_ifs
  · simp only [map_zero]
  · rfl

/-- **(T18, L002.)** The tail-term column at an atom. -/
theorem defectTail_single (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔) (j : ℤ) :
    defectTail r C hr b (lpOneAlg.single j 1) = 𝓡[r, C, hr] (b * lpOneAlg.single j 1) :=
  rfl

/-- **(T19, L002.)** The head term has zero head columns. -/
theorem colRatio_defectHead_head (N : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (b : 𝓔) (j : ℤ) (hj : j.natAbs ≤ N) :
    lpOneAlg.colRatio (defectHead N M b) j = 0 := by
  rw [colRatio_geom, defectHead_single, ite_eq_left hj, norm_zero, zero_div]

/-- **(T19, L002.)** The head-term column for a tail input. -/
theorem colRatio_defectHead_eq (N : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (b : 𝓔) (j : ℤ) (hj : N < j.natAbs) :
    lpOneAlg.colRatio (defectHead N M b) j
      = ‖M (𝓟[N] (b * lpOneAlg.single j 1))‖ / (ν : ℝ) ^ j.natAbs := by
  rw [colRatio_geom, defectHead_single, ite_eq_right (show ¬j.natAbs ≤ N by omega)]

/-- **(T19, L002.)** Under the band of `b`, the head term vanishes beyond the shell `N + m`. -/
theorem colRatio_defectHead_far (N m : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (b : 𝓔)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0) (j : ℤ) (hj : N + m < j.natAbs) :
    lpOneAlg.colRatio (defectHead N M b) j = 0 := by
  have h0 : 𝓟[N] (b * lpOneAlg.single j 1) = 0 := by
    refine lpOneAlg.ext_toRealSeq (funext fun k => ?_)
    rw [lpOneAlg.toRealSeq_headProj, lpOneAlg.toRealSeq_zero, Pi.zero_apply]
    split_ifs with hk
    · rw [mem_winZ] at hk
      rw [toRealSeq_mul_single, hb (k - j) (by omega)]
    · rfl
  rw [colRatio_defectHead_eq N M b j (by omega), h0, map_zero, norm_zero, zero_div]

/-- **(T20, L002.)** The explicit head column `a_j = 1_{|j|>N} ‖M P (b e_j)‖ / ν^{|j|}`. -/
def headCol (N : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (b : 𝓔) (j : ℤ) : ℝ :=
  if j.natAbs ≤ N then 0 else ‖M (𝓟[N] (b * lpOneAlg.single j 1))‖ / (ν : ℝ) ^ j.natAbs

/-- **(T20, L002.)** The head-term column is the explicit head column. -/
theorem colRatio_defectHead_eq_headCol (N : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (b : 𝓔) (j : ℤ) :
    lpOneAlg.colRatio (defectHead N M b) j = headCol N M b j := by
  unfold headCol
  split_ifs with hj
  · exact colRatio_defectHead_head N M b j hj
  · exact colRatio_defectHead_eq N M b j (by omega)

/-- **(T21, L002.)** Under the band of `b`, the tail-term column is the explicit tail column. -/
theorem colRatio_defectTail (m : ℕ) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0) (j : ℤ) :
    lpOneAlg.colRatio (defectTail r C hr b) j = tailCol m r b j := by
  rw [colRatio_geom, defectTail_single, tailCol, norm_eq_tsum_coeff]
  congr 1
  have hre : (∑' k : ℤ, ‖lpOneAlg.toRealSeq (𝓡[r, C, hr] (b * lpOneAlg.single j 1)) k‖
        * (ν : ℝ) ^ k.natAbs)
      = ∑' i : ℤ, ‖lpOneAlg.toRealSeq (𝓡[r, C, hr] (b * lpOneAlg.single j 1)) (j + i)‖
        * (ν : ℝ) ^ (j + i).natAbs :=
    ((Equiv.addLeft j).tsum_eq (fun k : ℤ =>
      ‖lpOneAlg.toRealSeq (𝓡[r, C, hr] (b * lpOneAlg.single j 1)) k‖
        * (ν : ℝ) ^ k.natAbs)).symm
  rw [hre, tsum_eq_sum (s := winZ m) fun i hi => by
    rw [lpOneAlg.toRealSeq_diagCLM, toRealSeq_mul_single, add_sub_cancel_left,
      hb i (by rw [mem_winZ] at hi; omega), mul_zero, norm_zero, zero_mul]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lpOneAlg.toRealSeq_diagCLM, toRealSeq_mul_single, add_sub_cancel_left, norm_mul]

/-- **(T22, L002.)** The right far ray `m ≤ j`: `colRatio (R L_b) j = Σ_i ‖r_{j+i}‖ ‖b_i‖ ν^i`. -/
theorem colRatio_defectTail_far_pos (m : ℕ) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0) (j : ℤ) (hj : (m : ℤ) ≤ j) :
    lpOneAlg.colRatio (defectTail r C hr b) j
      = ∑ i ∈ winZ m, ‖r (j + i)‖ * ‖lpOneAlg.toRealSeq b i‖ * (ν : ℝ) ^ i := by
  have hν : (0 : ℝ) < ν := ν.2
  rw [colRatio_defectTail m r C hr b hb j, tailCol, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mem_winZ] at hi
  have e2 : (ν : ℝ) ^ (j + i).natAbs / (ν : ℝ) ^ j.natAbs = (ν : ℝ) ^ i := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hν.ne',
      show (((j + i).natAbs : ℕ) : ℤ) - (j.natAbs : ℕ) = i by omega]
  rw [← e2, mul_div_assoc]

/-- **(T22, L002.)** The left far ray `j ≤ −m`:
`colRatio (R L_b) j = Σ_i ‖r_{j+i}‖ ‖b_i‖ ν^{−i}`. -/
theorem colRatio_defectTail_far_neg (m : ℕ) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0) (j : ℤ) (hj : j ≤ -(m : ℤ)) :
    lpOneAlg.colRatio (defectTail r C hr b) j
      = ∑ i ∈ winZ m, ‖r (j + i)‖ * ‖lpOneAlg.toRealSeq b i‖ * (ν : ℝ) ^ (-i) := by
  have hν : (0 : ℝ) < ν := ν.2
  rw [colRatio_defectTail m r C hr b hb j, tailCol, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mem_winZ] at hi
  have e2 : (ν : ℝ) ^ (j + i).natAbs / (ν : ℝ) ^ j.natAbs = (ν : ℝ) ^ (-i) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hν.ne',
      show (((j + i).natAbs : ℕ) : ℤ) - (j.natAbs : ℕ) = -i by omega]
  rw [← e2, mul_div_assoc]

/-- **(T23, L002.)** `P (M P L_b Q) = M P L_b Q` when `P M = M`. -/
theorem headProj_comp_defectHead (N : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (b : 𝓔) (hPM : 𝓟[N] ∘L M = M) :
    𝓟[N] ∘L defectHead N M b = defectHead N M b := by
  rw [defectHead, ← ContinuousLinearMap.comp_assoc, hPM]

/-- **(T23, L002.)** `(M P L_b Q) P = 0`: the input side of the head term is the tail. -/
theorem defectHead_comp_headProj (N : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (b : 𝓔) :
    defectHead N M b ∘L 𝓟[N] = 0 := by
  simp only [defectHead, ContinuousLinearMap.comp_assoc, lpOneAlg.tailProj_comp_headProj,
    ContinuousLinearMap.comp_zero]

/-- **(T23, L002.)** `Q (R L_b) = R L_b` when `r` vanishes on the head. -/
theorem tailProj_comp_defectTail (N : ℕ) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔)
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0) :
    𝓠[N] ∘L defectTail r C hr b = defectTail r C hr b := by
  rw [defectTail, ← ContinuousLinearMap.comp_assoc,
    lpOneAlg.tailProj_comp_diagCLM (winZ N) r C hr fun k hk => hr0 k (mem_winZ.mp hk)]

/-- **(T24, L002.)** Under range (`P M = M`) and head vanishing, the defect columns are the sums
of the head-term and tail-term columns. -/
theorem colRatio_defect (N : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C)
    (b : 𝓔) (hPM : 𝓟[N] ∘L M = M) (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0) (j : ℤ) :
    lpOneAlg.colRatio (defect N M r C hr b) j
      = lpOneAlg.colRatio (defectHead N M b) j + lpOneAlg.colRatio (defectTail r C hr b) j :=
  lpOneAlg.colRatio_add_of_head_tail (winZ N) _ _ (headProj_comp_defectHead N M b hPM)
    (tailProj_comp_defectTail N r C hr b hr0) j

/-- **(T26, L002.)** Beyond the shell `N + m` the defect column is the tail column, for every
bounded `M` and `r` (only the band of `b` is used). -/
theorem colRatio_defect_far_eq_defectTail (N m : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔) (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0)
    (j : ℤ) (hj : N + m < j.natAbs) :
    lpOneAlg.colRatio (defect N M r C hr b) j = lpOneAlg.colRatio (defectTail r C hr b) j := by
  have h0 : defectHead N M b (lpOneAlg.single j 1) = 0 := by
    have h := colRatio_defectHead_far N m M b hb j hj
    rw [colRatio_geom, div_eq_zero_iff] at h
    exact norm_eq_zero.mp (h.resolve_right (pow_pos ν.2 _).ne')
  rw [colRatio_geom, colRatio_geom, defect_eq, add_apply, h0, zero_add]

/-- **(T27, L002.)** The far tail columns are antitone outward on the right (window `W ≥ m`). -/
theorem colRatio_defectTail_succ_le (m W : ℕ) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0) (hmW : m ≤ W)
    (hmono : ∀ n : ℕ, W ≤ n + m →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖)
    (j : ℤ) (hj : (W : ℤ) ≤ j) :
    lpOneAlg.colRatio (defectTail r C hr b) (j + 1)
      ≤ lpOneAlg.colRatio (defectTail r C hr b) j := by
  have hν : (0 : ℝ) < ν := ν.2
  rw [colRatio_defectTail_far_pos m r C hr b hb (j + 1) (by omega),
    colRatio_defectTail_far_pos m r C hr b hb j (by omega)]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [mem_winZ] at hi
  have hn := (hmono (j + i).toNat (by omega)).1
  rw [show ((j + i).toNat : ℤ) = j + i by omega] at hn
  rw [show j + 1 + i = j + i + 1 by ring]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    (zpow_nonneg hν.le _)

/-- **(T27, L002.)** The far tail columns are antitone outward on the left. -/
theorem colRatio_defectTail_pred_le (m W : ℕ) (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0) (hmW : m ≤ W)
    (hmono : ∀ n : ℕ, W ≤ n + m →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖)
    (j : ℤ) (hj : j ≤ -(W : ℤ)) :
    lpOneAlg.colRatio (defectTail r C hr b) (j - 1)
      ≤ lpOneAlg.colRatio (defectTail r C hr b) j := by
  have hν : (0 : ℝ) < ν := ν.2
  rw [colRatio_defectTail_far_neg m r C hr b hb (j - 1) (by omega),
    colRatio_defectTail_far_neg m r C hr b hb j (by omega)]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [mem_winZ] at hi
  have hn := (hmono (-(j + i)).toNat (by omega)).2
  rw [show ((-(j + i)).toNat : ℤ) = -(j + i) by omega, neg_neg,
    show -(-(j + i) + 1) = j - 1 + i by ring] at hn
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    (zpow_nonneg hν.le _)

/-- **(T28, L002.)** Far antitonicity of the defect columns on the right, any window
`W > N + m` beyond which the moduli are monotone. -/
theorem colRatio_defect_succ_le_of (N m W : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔) (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0)
    (hWN : N + m < W)
    (hmono : ∀ n : ℕ, W ≤ n + m →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖)
    (j : ℤ) (hj : (W : ℤ) ≤ j) :
    lpOneAlg.colRatio (defect N M r C hr b) (j + 1)
      ≤ lpOneAlg.colRatio (defect N M r C hr b) j := by
  rw [colRatio_defect_far_eq_defectTail N m M r C hr b hb (j + 1) (by omega),
    colRatio_defect_far_eq_defectTail N m M r C hr b hb j (by omega)]
  exact colRatio_defectTail_succ_le m W r C hr b hb (by omega) hmono j hj

/-- **(T28, L002.)** Far antitonicity of the defect columns on the left. -/
theorem colRatio_defect_pred_le_of (N m W : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔) (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0)
    (hWN : N + m < W)
    (hmono : ∀ n : ℕ, W ≤ n + m →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖)
    (j : ℤ) (hj : j ≤ -(W : ℤ)) :
    lpOneAlg.colRatio (defect N M r C hr b) (j - 1)
      ≤ lpOneAlg.colRatio (defect N M r C hr b) j := by
  rw [colRatio_defect_far_eq_defectTail N m M r C hr b hb (j - 1) (by omega),
    colRatio_defect_far_eq_defectTail N m M r C hr b hb j (by omega)]
  exact colRatio_defectTail_pred_le m W r C hr b hb (by omega) hmono j hj

/-- **(T30, L002.)** The defect columns are antitone outward beyond
`W = m + max (N + 1) K₀`, on both rays. -/
theorem colRatio_defect_far_antitone (N m K₀ : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔) (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    (∀ j : ℤ, ((m + max (N + 1) K₀ : ℕ) : ℤ) ≤ j →
        lpOneAlg.colRatio (defect N M r C hr b) (j + 1)
          ≤ lpOneAlg.colRatio (defect N M r C hr b) j) ∧
      (∀ j : ℤ, j ≤ -((m + max (N + 1) K₀ : ℕ) : ℤ) →
        lpOneAlg.colRatio (defect N M r C hr b) (j - 1)
          ≤ lpOneAlg.colRatio (defect N M r C hr b) j) := by
  have hWN : N + m < m + max (N + 1) K₀ := by have := le_max_left (N + 1) K₀; omega
  have hm : ∀ n : ℕ, m + max (N + 1) K₀ ≤ n + m →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖ :=
    fun n hn => hmono n (by omega)
  exact ⟨colRatio_defect_succ_le_of N m _ M r C hr b hb hWN hm,
    colRatio_defect_pred_le_of N m _ M r C hr b hb hWN hm⟩

/-- **(T32, L002.)** Under band, range and head vanishing, the defect columns in explicit form
`a_j + s_j`. -/
theorem colRatio_defect_explicit (N m : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔) (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0)
    (hPM : 𝓟[N] ∘L M = M) (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0) (j : ℤ) :
    lpOneAlg.colRatio (defect N M r C hr b) j = headCol N M b j + tailCol m r b j := by
  rw [colRatio_defect N M r C hr b hPM hr0, colRatio_defectHead_eq_headCol,
    colRatio_defectTail m r C hr b hb]

end Defect

/-! ### Operator norms: the exact finite window -/

section OpNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal}
  [Fact (1 ≤ (ν : ℝ))]

local notation "𝓔" => lpOneAlg ℤ (geomFiberZ 𝕜 ν)
local notation "𝓟[" N "]" => (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : 𝓔 →L[𝕜] 𝓔)
local notation "𝓠[" N "]" => (lpOneAlg.tailProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : 𝓔 →L[𝕜] 𝓔)

/-- **(T25, L002.)** Under range and head vanishing, `‖D‖ = ⨆ j (a_j + s_j)` in column-ratio
form (the exact aggregate of a head-valued and a tail-valued map). -/
theorem opNorm_defect_eq_iSup (N : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔) (hPM : 𝓟[N] ∘L M = M)
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0) :
    ‖defect N M r C hr b‖
      = ⨆ j : ℤ, (lpOneAlg.colRatio (defectHead N M b) j
          + lpOneAlg.colRatio (defectTail r C hr b) j) :=
  lpOneAlg.opNorm_add_eq_iSup (winZ N) _ _ (headProj_comp_defectHead N M b hPM)
    (tailProj_comp_defectTail N r C hr b hr0)

/-- **(T29, L002.)** The operator norm of the defect is the finite maximum of its column ratios
over `winZ W`, any window `W > N + m` beyond which the moduli are monotone. -/
theorem opNorm_defect_eq_sup'_of (N m W : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔) (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0)
    (hWN : N + m < W)
    (hmono : ∀ n : ℕ, W ≤ n + m →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖defect N M r C hr b‖
      = (winZ W).sup' (winZ_nonempty W) (fun j => lpOneAlg.colRatio (defect N M r C hr b) j) :=
  (lpOneAlg.opNorm_eq_iSup_cols _).trans (iSup_eq_sup'_of_far_antitone _ W
    (colRatio_defect_succ_le_of N m W M r C hr b hb hWN hmono)
    (colRatio_defect_pred_le_of N m W M r C hr b hb hWN hmono))

/-- **(T31, L002; the statement of record.)** Under the band of `b`, a bounded tail diagonal and
moduli `‖r‖` two-ray nonincreasing from `max (N + 1) K₀` on, the full operator norm of the
defect is the finite maximum of its column ratios over `|j| ≤ m + max (N + 1) K₀`. For every
bounded `M` and `r`. -/
theorem opNorm_defect_eq_sup' (N m K₀ : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖defect N M r C hr b‖
      = (winZ (m + max (N + 1) K₀)).sup' (winZ_nonempty _)
          (fun j => lpOneAlg.colRatio (defect N M r C hr b) j) :=
  (lpOneAlg.opNorm_eq_iSup_cols _).trans (iSup_eq_sup'_of_far_antitone _ _
    (colRatio_defect_far_antitone N m K₀ M r C hr b hb hmono).1
    (colRatio_defect_far_antitone N m K₀ M r C hr b hb hmono).2)

/-- **(T33, L002.)** The exact finite window in explicit form: under band, range and head
vanishing, `‖D‖ = max_{|j| ≤ W} (a_j + s_j)`. -/
theorem opNorm_defect_eq_sup'_explicit (N m K₀ : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜)
    (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0) (hPM : 𝓟[N] ∘L M = M)
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖defect N M r C hr b‖
      = (winZ (m + max (N + 1) K₀)).sup' (winZ_nonempty _)
          (fun j => headCol N M b j + tailCol m r b j) := by
  rw [opNorm_defect_eq_sup' N m K₀ M r C hr b hb hmono]
  exact Finset.sup'_congr _ rfl fun j _ => colRatio_defect_explicit N m M r C hr b hb hPM hr0 j

/-- **(T34, L002.)** The operator norm is attained as a weighted column ratio at an atom inside
the window: `‖D e_j‖ = ‖D‖ ν^|j|` for some `|j| ≤ m + max (N + 1) K₀`. This is attainment of
the column ratio at `single j 1`, not a unit-norm atom (a scalar of norm `ν^(-|j|)` need not
exist over a general field). -/
theorem defect_attained (N m K₀ : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ∃ j ∈ winZ (m + max (N + 1) K₀),
      ‖defect N M r C hr b (lpOneAlg.single j 1)‖ = ‖defect N M r C hr b‖ * (ν : ℝ) ^ j.natAbs := by
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' (winZ_nonempty (m + max (N + 1) K₀))
    (fun j => lpOneAlg.colRatio (defect N M r C hr b) j)
  have hν : (0 : ℝ) < ν := ν.2
  refine ⟨j, hj, ?_⟩
  rw [opNorm_defect_eq_sup' N m K₀ M r C hr b hb hmono, heq, colRatio_geom,
    div_mul_cancel₀ _ (pow_pos hν _).ne']

/-- **(T36, L002.)** Moduli monotone from the first tail index give the window
`|j| ≤ N + m + 1`. -/
theorem opNorm_defect_eq_sup'_first (N m : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0)
    (hmono : ∀ n : ℕ, N + 1 ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖defect N M r C hr b‖
      = (winZ (N + m + 1)).sup' (winZ_nonempty _)
          (fun j => lpOneAlg.colRatio (defect N M r C hr b) j) :=
  opNorm_defect_eq_sup'_of N m _ M r C hr b hb (by omega) fun n hn => hmono n (by omega)

/-- **(T37, L002.)** Joint form with a head block `Z` (`P Z = Z`, `Z Q = 0`): under band, range
and head vanishing, `‖Z + D‖ = max_{|j| ≤ W} (z_j + a_j + s_j)` in column-ratio form. A norm
identity only: it does not replace injectivity of `A` or the `Z₀` obligations. -/
theorem opNorm_joint_defect_eq_sup' (N m K₀ : ℕ) (Z M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜)
    (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔)
    (hPZ : 𝓟[N] ∘L Z = Z) (hZQ : Z ∘L 𝓠[N] = 0)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0) (hPM : 𝓟[N] ∘L M = M)
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖Z + defect N M r C hr b‖
      = (winZ (m + max (N + 1) K₀)).sup' (winZ_nonempty _)
          (fun j => lpOneAlg.colRatio Z j + lpOneAlg.colRatio (defectHead N M b) j
            + lpOneAlg.colRatio (defectTail r C hr b) j) := by
  have hWN : N + m < m + max (N + 1) K₀ := by have := le_max_left (N + 1) K₀; omega
  have hm : ∀ n : ℕ, m + max (N + 1) K₀ ≤ n + m →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖ :=
    fun n hn => hmono n (by omega)
  have hZ : ∀ i : ℤ, N < i.natAbs → lpOneAlg.colRatio Z i = 0 := fun i hi =>
    lpOneAlg.colRatio_eq_zero_of_comp_tailProj (winZ N) Z hZQ i fun h => by
      rw [mem_winZ] at h; omega
  rw [defect_eq, ← add_assoc, lpOneAlg.opNorm_joint_eq_iSup (winZ N) (winZ N) Z (defectHead N M b)
    (defectTail r C hr b) hPZ hZQ (headProj_comp_defectHead N M b hPM)
    (defectHead_comp_headProj N M b) (tailProj_comp_defectTail N r C hr b hr0)]
  refine iSup_eq_sup'_of_far_antitone _ _ (fun j hj => ?_) (fun j hj => ?_)
  · rw [hZ (j + 1) (by omega), hZ j (by omega),
      colRatio_defectHead_far N m M b hb (j + 1) (by omega),
      colRatio_defectHead_far N m M b hb j (by omega)]
    simp only [zero_add]
    exact colRatio_defectTail_succ_le m _ r C hr b hb (by omega) hm j hj
  · rw [hZ (j - 1) (by omega), hZ j (by omega),
      colRatio_defectHead_far N m M b hb (j - 1) (by omega),
      colRatio_defectHead_far N m M b hb j (by omega)]
    simp only [zero_add]
    exact colRatio_defectTail_pred_le m _ r C hr b hb (by omega) hm j hj

/-- **(T38, L002.)** The joint form for `Z − D` (the joint operator `I − A·DF = Z − D`): the same
finite maximum, from T37 at `(−M, −r)`. -/
theorem opNorm_joint_defect_sub_eq_sup' (N m K₀ : ℕ) (Z M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜)
    (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (b : 𝓔)
    (hPZ : 𝓟[N] ∘L Z = Z) (hZQ : Z ∘L 𝓠[N] = 0)
    (hb : ∀ i : ℤ, m < i.natAbs → lpOneAlg.toRealSeq b i = 0) (hPM : 𝓟[N] ∘L M = M)
    (hr0 : ∀ k : ℤ, k.natAbs ≤ N → r k = 0)
    (hmono : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖r ((n : ℤ) + 1)‖ ≤ ‖r (n : ℤ)‖ ∧ ‖r (-((n : ℤ) + 1))‖ ≤ ‖r (-(n : ℤ))‖) :
    ‖Z - defect N M r C hr b‖
      = (winZ (m + max (N + 1) K₀)).sup' (winZ_nonempty _)
          (fun j => lpOneAlg.colRatio Z j + lpOneAlg.colRatio (defectHead N M b) j
            + lpOneAlg.colRatio (defectTail r C hr b) j) := by
  have hr' : ∀ k, ‖(-r) k‖ ≤ C := fun k => by rw [Pi.neg_apply, norm_neg]; exact hr k
  have hdiag : (lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) (-r) C hr' : 𝓔 →L[𝕜] 𝓔)
      = -lpOneAlg.diagCLM r C hr := by
    refine ContinuousLinearMap.ext fun a => lpOneAlg.ext_toRealSeq (funext fun k => ?_)
    rw [lpOneAlg.toRealSeq_diagCLM, neg_apply, lpOneAlg.toRealSeq_neg,
      Pi.neg_apply, Pi.neg_apply, lpOneAlg.toRealSeq_diagCLM, neg_mul]
  have hHd : defectHead N (-M) b = -defectHead N M b := by
    rw [defectHead, defectHead, ContinuousLinearMap.neg_comp]
  have hTl : defectTail (-r) C hr' b = -defectTail r C hr b := by
    rw [defectTail, defectTail, hdiag, ContinuousLinearMap.neg_comp]
  have hD : defect N (-M) (-r) C hr' b = -defect N M r C hr b := by
    rw [defect_eq, defect_eq, hHd, hTl, neg_add]
  have hcol : ∀ (T : 𝓔 →L[𝕜] 𝓔) (j : ℤ), lpOneAlg.colRatio (-T) j = lpOneAlg.colRatio T j :=
    fun T j => by rw [colRatio_geom, colRatio_geom, neg_apply, norm_neg]
  have hPM' : 𝓟[N] ∘L (-M) = -M := by rw [ContinuousLinearMap.comp_neg, hPM]
  have hr0' : ∀ k : ℤ, k.natAbs ≤ N → (-r) k = 0 := fun k hk => by
    rw [Pi.neg_apply, hr0 k hk, neg_zero]
  have hmono' : ∀ n : ℕ, max (N + 1) K₀ ≤ n →
      ‖(-r) ((n : ℤ) + 1)‖ ≤ ‖(-r) (n : ℤ)‖ ∧ ‖(-r) (-((n : ℤ) + 1))‖ ≤ ‖(-r) (-(n : ℤ))‖ :=
    fun n hn => by simp only [Pi.neg_apply, norm_neg]; exact hmono n hn
  have h := opNorm_joint_defect_eq_sup' N m K₀ Z (-M) (-r) C hr' b hPZ hZQ hb hPM' hr0' hmono'
  rw [hD, ← sub_eq_add_neg] at h
  rw [h]
  exact Finset.sup'_congr _ rfl fun j _ => by rw [hHd, hTl, hcol, hcol]

end OpNorm

/-! ### Window arithmetic -/

/-- **(T35, L002.)** `m + max (N + 1) K₀ = N + m + 1` when `K₀ ≤ N + 1`. -/
theorem window_eq_of_le (N m K₀ : ℕ) (hK : K₀ ≤ N + 1) : m + max (N + 1) K₀ = N + m + 1 := by
  rw [max_eq_left hK]; omega

end RadiiPolynomial.Fourier
