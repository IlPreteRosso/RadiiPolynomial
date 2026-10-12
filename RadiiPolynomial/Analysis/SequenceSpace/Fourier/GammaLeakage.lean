import RadiiPolynomial.Analysis.SequenceSpace.Fourier.TailWindow
import RadiiPolynomial.Algebra.Rees.Laurent.Gamma

/-!
# The Γ leakage layer on the bilateral geometric carrier

On `E = lpOneAlg ℤ (geomFiberZ 𝕜 ν)` with the head window `P = headProj (winZ N)`, the tail
projection `Q = tailProj (winZ N)` and left multiplication `L_c = mulLeftCLM c`, this file proves
the all-coefficient leakage estimates of the head/tail split:

* the Γ scalar `gammaScalar ν N k = algebraMap ℝ 𝕜 (γ_N(k))` with `‖gammaScalar ν N k‖ = γ_N(k)`
  for every real `ν` (`norm_gammaScalar`), nonzero for `ν > 0`;
* the head diagonals `gammaDiag N = diag(1_{W_N} γ_N)` (symbols of norm `≤ 1`,
  `norm_gamma_head_le`) and `gammaInvDiag N = diag(1_{W_N} γ_N⁻¹)` (symbols of norm
  `≤ ν ^ (2(N + 1))`, `norm_gamma_inv_head_le`; no operator-norm lemma is stated here), with
  `gammaDiag N ∘L gammaInvDiag N = P` and the Rees identification of the head entries
  `γ_N(k) = eval_{1/ν} (X ^ aN N k)` (`gammaDiag_entry_eq_rees`);
* `‖L_c‖ ≤ ‖c‖` (`norm_mulLeftCLM_le`);
* for every `c`: `‖Γ⁺ P L_c Q‖ ≤ ‖c‖` (`norm_gammaInvDiag_leak_le`),
  `‖M P L_c Q‖ ≤ ‖M P Γ‖ ‖c‖` for every bounded `M` (`norm_head_leak_le_coeff`),
  `‖D_r L_c‖ ≤ C ‖c‖` for every bounded diagonal `‖r_k‖ ≤ C` (`norm_tail_leak_le_coeff`), and
  the Γ majorant of the defect `‖defect N M r C hr c‖ ≤ (‖M P Γ‖ + C) ‖c‖`
  (`norm_defect_le_gamma`).

The Γ entries are real numbers inserted through `algebraMap ℝ 𝕜`, so the Γ faces are stated over a
real-scalar field `[NormedAlgebra ℝ 𝕜]` (ℝ, ℂ, any `RCLike` field); `norm_mulLeftCLM_le` and the
tail estimate need no real structure. The Γ majorant is a universal head bound: it is not the exact
fixed-defect norm, which is the finite window formula `opNorm_defect_eq_sup'` of
`Fourier/TailWindow.lean`.
-/

noncomputable section

namespace RadiiPolynomial.Fourier

/-! ### The Γ scalar (real-scalar field) -/

section Scalar

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]

/-- The Γ scalar `γ_N(k) = ν^{2|k|} / ν^{2(N+1)}` inserted into a real-scalar
field. -/
def gammaScalar (ν : ℝ) (N : ℕ) (k : ℤ) : 𝕜 :=
    algebraMap ℝ 𝕜 (Rees.Laurent.gammaW ν N k)

/-- The Γ scalar has norm `γ_N(k)`, for every real `ν` (the even exponents make
`γ_N(k)` nonnegative). -/
theorem norm_gammaScalar (ν : ℝ) (N : ℕ) (k : ℤ) :
    ‖(gammaScalar ν N k : 𝕜)‖ = Rees.Laurent.gammaW ν N k := by
  rw [gammaScalar, norm_algebraMap', Real.norm_eq_abs, abs_of_nonneg]
  rw [Rees.Laurent.gammaW]
  exact div_nonneg ((even_two_mul _).pow_nonneg ν) ((even_two_mul _).pow_nonneg ν)

/-- The Γ scalar is nonzero for `ν > 0`. -/
theorem gammaScalar_ne_zero {ν : ℝ} (hν : 0 < ν) (N : ℕ) (k : ℤ) :
    (gammaScalar ν N k : 𝕜) ≠ 0 := by
  intro hg
  have hn := congr_arg norm hg
  rw [norm_gammaScalar, norm_zero] at hn
  exact (ne_of_gt (Rees.Laurent.gammaW_pos hν N k)) hn

end Scalar

/-! ### The head symbols (real-scalar field, `ν ≥ 1`) -/

section HeadSymbols

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- The head symbol of Γ is bounded by `1`. -/
theorem norm_gamma_head_le (N : ℕ) :
    ∀ k : ℤ, ‖(if k ∈ winZ N then (gammaScalar (ν : ℝ) N k : 𝕜) else 0)‖ ≤ 1 := by
  intro k
  split_ifs with hk
  · rw [norm_gammaScalar, Rees.Laurent.gammaW]
    exact (div_le_one (pow_pos ν.coe_pos _)).mpr
      (pow_le_pow_right₀ (show (1 : ℝ) ≤ ν from Fact.out) (by
        have := mem_winZ.mp hk
        omega))
  · rw [norm_zero]
    exact zero_le_one

/-- The head symbol of Γ⁺ is bounded by `ν ^ (2(N + 1))`. -/
theorem norm_gamma_inv_head_le (N : ℕ) :
    ∀ k : ℤ, ‖(if k ∈ winZ N then (gammaScalar (ν : ℝ) N k : 𝕜)⁻¹ else 0)‖ ≤
      (ν : ℝ) ^ (2 * (N + 1)) := by
  intro k
  split_ifs
  · rw [norm_inv, norm_gammaScalar]
    exact Rees.Laurent.gammaW_inv_le Fact.out N k
  · rw [norm_zero]
    exact (pow_pos ν.coe_pos _).le

end HeadSymbols

/-! ### The head diagonals (explicit binder headers: the header alone fixes the type) -/

/-- The head diagonal `Γ = diag(1_{W_N} γ_N)`. -/
def gammaDiag {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] (N : ℕ) :
    lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν) :=
    lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) (fun k => if k ∈ winZ N then (gammaScalar (ν : ℝ) N k : 𝕜) else 0) 1
      (norm_gamma_head_le N)

/-- The inverse head diagonal `Γ⁺ = diag(1_{W_N} γ_N⁻¹)`. -/
def gammaInvDiag {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] (N : ℕ) :
    lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν) :=
    lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) (fun k => if k ∈ winZ N then (gammaScalar (ν : ℝ) N k : 𝕜)⁻¹ else 0)
      ((ν : ℝ) ^ (2 * (N + 1))) (norm_gamma_inv_head_le N)

section HeadDiagonals

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

local notation "𝓔" => lpOneAlg ℤ (geomFiberZ 𝕜 ν)
local notation "𝓟[" N "]" => (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : 𝓔 →L[𝕜] 𝓔)

/-- `Γ Γ⁺ = P_N`. -/
theorem gammaDiag_comp_gammaInvDiag (N : ℕ) :
    (gammaDiag N : 𝓔 →L[𝕜] 𝓔) ∘L (gammaInvDiag N : 𝓔 →L[𝕜] 𝓔) = 𝓟[N] := by
  refine ContinuousLinearMap.ext fun a => lpOneAlg.ext_toRealSeq (funext fun k => ?_)
  rw [ContinuousLinearMap.comp_apply, gammaDiag, gammaInvDiag, lpOneAlg.toRealSeq_diagCLM,
    lpOneAlg.toRealSeq_diagCLM, lpOneAlg.toRealSeq_headProj]
  by_cases hk : k ∈ winZ N
  · rw [ite_eq_left hk, ite_eq_left hk, ite_eq_left hk, ← mul_assoc,
      mul_inv_cancel₀ (gammaScalar_ne_zero ν.coe_pos N k), one_mul]
  · rw [ite_eq_right hk, ite_eq_right hk, ite_eq_right hk, zero_mul]

/-- The head entries of Γ are the evaluated annihilator monomials:
`γ_N(k) = eval_{1/ν} (X ^ aN N k)` for `|k| ≤ N`. -/
theorem gammaDiag_entry_eq_rees (N : ℕ) :
    ∀ k ∈ winZ N, lpOneAlg.toRealSeq ((gammaDiag N : 𝓔 →L[𝕜] 𝓔) (lpOneAlg.single k 1)) k =
      algebraMap ℝ 𝕜 (Polynomial.eval (1 / (ν : ℝ)) ((Polynomial.X : Polynomial ℝ) ^ Rees.Laurent.aN N k)) := by
  intro k hk
  rw [gammaDiag, lpOneAlg.diagCLM_single, lpOneAlg.toRealSeq_single, ite_eq_left rfl, ite_eq_left hk,
    mul_one, gammaScalar,
    Rees.Laurent.gammaW_eq_eval_annihilator (ν : ℝ) ν.coe_pos (mem_winZ.mp hk)]

/-- Coefficient face of Γ. -/
theorem toRealSeq_gammaDiag (N : ℕ) (a : 𝓔) (k : ℤ) :
    lpOneAlg.toRealSeq ((gammaDiag N : 𝓔 →L[𝕜] 𝓔) a) k =
      (if k ∈ winZ N then (gammaScalar (ν : ℝ) N k : 𝕜) else 0) * lpOneAlg.toRealSeq a k :=
  lpOneAlg.toRealSeq_diagCLM _ _ _ a k

/-- Coefficient face of Γ⁺. -/
theorem toRealSeq_gammaInvDiag (N : ℕ) (a : 𝓔) (k : ℤ) :
    lpOneAlg.toRealSeq ((gammaInvDiag N : 𝓔 →L[𝕜] 𝓔) a) k =
      (if k ∈ winZ N then (gammaScalar (ν : ℝ) N k : 𝕜)⁻¹ else 0) * lpOneAlg.toRealSeq a k :=
  lpOneAlg.toRealSeq_diagCLM _ _ _ a k

end HeadDiagonals

/-! ### Left multiplication and the tail estimate (no real structure) -/

section Tail

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

local notation "𝓔" => lpOneAlg ℤ (geomFiberZ 𝕜 ν)
local notation "𝓛[" b "]" => (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) b : 𝓔 →L[𝕜] 𝓔)

/-- Left multiplication has operator norm at most `‖c‖` (the carrier instance of
`lpOneAlg.norm_mulLeftCLM_le`). -/
theorem norm_mulLeftCLM_le (c : 𝓔) :
    ‖𝓛[c]‖ ≤ ‖c‖ :=
  lpOneAlg.norm_mulLeftCLM_le c

/-- The tail term of any bounded diagonal `‖r_k‖ ≤ C`: `‖D_r L_c‖ ≤ C ‖c‖`. -/
theorem norm_tail_leak_le_coeff (r : ℤ → 𝕜) (C : ℝ) (hr : ∀ k, ‖r k‖ ≤ C) (c : 𝓔) :
    ‖(lpOneAlg.diagCLM (G := geomFiberZ 𝕜 ν) r C hr : 𝓔 →L[𝕜] 𝓔) ∘L 𝓛[c]‖ ≤ C * ‖c‖ := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hr 0)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (lpOneAlg.norm_diagCLM_le r C hr hC) (norm_mulLeftCLM_le c) (norm_nonneg _) hC)

end Tail

/-! ### The head leakage and the Γ majorant (real-scalar field) -/

section Leak

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAlgebra ℝ 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

local notation "𝓔" => lpOneAlg ℤ (geomFiberZ 𝕜 ν)
local notation "𝓟[" N "]" => (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : 𝓔 →L[𝕜] 𝓔)
local notation "𝓠[" N "]" => (lpOneAlg.tailProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N) : 𝓔 →L[𝕜] 𝓔)
local notation "𝓛[" b "]" => (lpOneAlg.mulLeftCLM (𝕜 := 𝕜) b : 𝓔 →L[𝕜] 𝓔)

/-- The inverse head diagonal cancels the worst tail-to-head weight transfer:
`‖Γ⁺ P L_c Q‖ ≤ ‖c‖` for every `c`. -/
theorem norm_gammaInvDiag_leak_le (N : ℕ) (c : 𝓔) :
    ‖(gammaInvDiag N : 𝓔 →L[𝕜] 𝓔) ∘L 𝓟[N] ∘L 𝓛[c] ∘L 𝓠[N]‖ ≤ ‖c‖ := by
  apply (lpOneAlg.opNorm_le_iff_cols _ (norm_nonneg c)).mpr
  intro j
  rw [geomFiberZ_weight]
  by_cases hj : j ∈ winZ N
  · simp only [ContinuousLinearMap.comp_apply, lpOneAlg.tailProj_single, ite_eq_left hj, map_zero,
      norm_zero]
    exact mul_nonneg (norm_nonneg c) (pow_pos ν.coe_pos _).le
  · have hjtail : N < j.natAbs := lt_of_not_ge (fun h => hj (mem_winZ.mpr h))
    simp only [ContinuousLinearMap.comp_apply, lpOneAlg.tailProj_single, ite_eq_right hj,
      lpOneAlg.mulLeftCLM_apply]
    rw [norm_eq_tsum_coeff]
    rw [tsum_eq_sum (s := winZ N) (fun k hk => by
      simp only [gammaInvDiag, lpOneAlg.toRealSeq_diagCLM, ite_eq_right hk, zero_mul, norm_zero])]
    refine (Finset.sum_le_sum (g := fun k => ‖lpOneAlg.toRealSeq c (k - j)‖ *
      (ν : ℝ) ^ (k - j).natAbs * (ν : ℝ) ^ j.natAbs) (fun k hk => ?_)).trans ?_
    · simp only [gammaInvDiag, lpOneAlg.toRealSeq_diagCLM, lpOneAlg.toRealSeq_headProj,
        ite_eq_left hk, toRealSeq_mul_single, norm_mul, norm_inv, norm_gammaScalar]
      have hν : (0 : ℝ) < ν := ν.coe_pos
      have hweight : (ν : ℝ) ^ k.natAbs /
          (Rees.Laurent.gammaW ν N k * (ν : ℝ) ^ j.natAbs) ≤ (ν : ℝ) ^ (k - j).natAbs := by
        rw [Rees.Laurent.weight_eq_rees (ν : ℝ) hν (mem_winZ.mp hk) hjtail]
        simp only [Polynomial.eval_pow, Polynomial.eval_X]
        apply mul_le_of_le_one_right (pow_nonneg hν.le _)
        exact pow_le_one₀ (div_nonneg zero_le_one hν.le) ((div_le_one hν).mpr Fact.out)
      have hscaled : (Rees.Laurent.gammaW ν N k)⁻¹ * (ν : ℝ) ^ k.natAbs ≤
          (ν : ℝ) ^ (k - j).natAbs * (ν : ℝ) ^ j.natAbs := by
        apply (div_le_iff₀ (pow_pos hν j.natAbs)).mp
        convert hweight using 1
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      convert mul_le_mul_of_nonneg_left hscaled (norm_nonneg (lpOneAlg.toRealSeq c (k - j))) using 1 <;> ring
    · rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (pow_pos ν.coe_pos j.natAbs).le
      have hs := (summable_coeff c).comp_injective
        (show Function.Injective (fun k : ℤ => k - j) from by
          intro x y h
          simp only at h
          omega)
      refine (hs.sum_le_tsum (winZ N) (fun k _ =>
        mul_nonneg (norm_nonneg _) (pow_pos ν.coe_pos _).le)).trans_eq ?_
      exact ((Equiv.subRight j).tsum_eq
        (fun i : ℤ => ‖lpOneAlg.toRealSeq c i‖ * (ν : ℝ) ^ i.natAbs)).trans
          (norm_eq_tsum_coeff c).symm

/-- The head leakage of every coefficient `c` and every bounded `M`:
`‖M P L_c Q‖ ≤ ‖M P Γ‖ ‖c‖` (`= ‖defectHead N M c‖ ≤ …`). -/
theorem norm_head_leak_le_coeff (N : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (c : 𝓔) :
    ‖M ∘L 𝓟[N] ∘L 𝓛[c] ∘L 𝓠[N]‖ ≤ ‖M ∘L 𝓟[N] ∘L (gammaDiag N : 𝓔 →L[𝕜] 𝓔)‖ * ‖c‖ := by
  have hfactor : M ∘L 𝓟[N] ∘L 𝓛[c] ∘L 𝓠[N] = (M ∘L 𝓟[N] ∘L (gammaDiag N : 𝓔 →L[𝕜] 𝓔)) ∘L
        ((gammaInvDiag N : 𝓔 →L[𝕜] 𝓔) ∘L 𝓟[N] ∘L 𝓛[c] ∘L 𝓠[N]) := by
    have hΓ := gammaDiag_comp_gammaInvDiag (𝕜 := 𝕜) (ν := ν) N
    have hP := lpOneAlg.headProj_comp_headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N)
    simp only [← ContinuousLinearMap.mul_def] at hΓ hP ⊢
    simp only [mul_assoc, ← mul_assoc (gammaDiag N : 𝓔 →L[𝕜] 𝓔)
      (gammaInvDiag N), hΓ,
      ← mul_assoc 𝓟[N]
        (lpOneAlg.headProj (𝕜 := 𝕜) (G := geomFiberZ 𝕜 ν) (winZ N)), hP]
  rw [hfactor]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_gammaInvDiag_leak_le N c) (norm_nonneg _))

/-- The Γ majorant of the defect, for every coefficient `c`:
`‖M P L_c Q + D_r L_c‖ ≤ (‖M P Γ‖ + C) ‖c‖`. This universal head bound is not the exact
fixed-defect norm (`opNorm_defect_eq_sup'`). -/
theorem norm_defect_le_gamma (N : ℕ) (M : 𝓔 →L[𝕜] 𝓔) (r : ℤ → 𝕜) (C : ℝ)
    (hr : ∀ k, ‖r k‖ ≤ C) (c : 𝓔) :
    ‖defect N M r C hr c‖ ≤ (‖M ∘L 𝓟[N] ∘L (gammaDiag N : 𝓔 →L[𝕜] 𝓔)‖ + C) * ‖c‖ := by
  rw [defect_eq, add_mul]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_head_leak_le_coeff N M c) (norm_tail_leak_le_coeff r C hr c))

end Leak

end RadiiPolynomial.Fourier
