import RadiiPolynomial.Examples.Fourier.Duffing.Polynomial.Eigenpair.Numbers
import RadiiPolynomial.Examples.Fourier.Duffing.Polynomial.Analytic
import RadiiPolynomial.Applications.Fourier.Eigenpair
import RadiiPolynomial.Applications.Fourier.Duffing

/-!
# The certified Duffing eigenpair on the polynomial carrier

At the certified Duffing zero `u* = xPoly` on `X = ℓ²_m(ℤ; ℂ)`, `m_n = (1 + |n|)²`, the right
eigenpair `(v, λ)` of the linearization `μ − 2 u* ⋆`, `μ = duffing (1/10) 4`, exists in the ball of
radius `1/20` around the rational candidate `ybar = (v̄, λ̄)` of `Eigenpair/Numbers`, solves
(E1) `μₙ vₙ − 2 (u* ⋆ v)ₙ − λ vₙ = 0` and (E2) `pairing v v = 1`, the real derivative of the
bordered map is invertible there, and it is unique in the closed ball (`duffing_eigenpair`).
`duffing_eigenpair_enclosure`: `|λ − λ̄| < 1/20`, `4 < λ`, `v ≠ 0`. The data `duffEigen`
(`EigenData` at `μ`, `S = headF 10`, `q = −2 u*`), the rational-to-real bridges and the four bounds
`duff_Y0_le`, `duff_Z0_le`, `duff_Z1_le`, `duff_Z2_le` feed `existsUnique_eigenpair`; each bound is
one check call of `Eigenpair/Numbers`.
-/

open scoped ENNReal NNReal DiscreteConvolution ComplexConjugate

noncomputable section

namespace FourierDuffing.Polynomial.Eigenpair

open RadiiPolynomial RadiiPolynomial.WeightedLp RadiiPolynomial.Fourier.Eigenpair
open RadiiPolynomial.Fourier.Duffing RadiiPolynomial.Fourier.IkData

section Centre

/-! ### The centre `ā ∈ XR` and the symmetric symbol `β = 2ā` -/

/-- The polynomial-carrier centre `ā` lies in `XR`. -/
theorem abar_mem_realSub : Certificate.abar ∈ realSub polyWeight_neg :=
  (mem_realSub_iff_coeff polyWeight_neg).2 fun n =>
    (Certificate.coeff_abar (-n)).trans <|
      (FourierDuffing.Certificate.coeff_abar (-n)).symm.trans <|
        ((conjReflL_eq_self_iff_coeff _ _).1 (FourierDuffing.Numbers.leaf.conjRefl_abar
          (ν := FourierDuffing.Certificate.ν₆₅) FourierDuffing.Numbers.checks) n).trans <|
          congrArg _ <|
            (FourierDuffing.Certificate.coeff_abar n).trans (Certificate.coeff_abar n).symm

end Centre

section Zero

/-! ### The certified zero `u* = xPoly ∈ XR` -/

/-- The certified zero `u* = xPoly` lies in `XR`. -/
theorem xPoly_mem_realSub : Certificate.xPoly ∈ realSub polyWeight_neg :=
  (mem_realSub_iff_coeff polyWeight_neg).2 fun n => by
    rw [← embed_aTilde_eq_xPoly, coeff_embed, coeff_embed]
    exact (conjReflL_eq_self_iff_coeff _ _).1
      FourierDuffing.Certificate.duffing_analytic_solution.2.2.1 n

/-- The potential `q = -2 u*` lies in `XR`. -/
theorem potential_mem_realSub : (-2 : ℝ) • Certificate.xPoly ∈ realSub polyWeight_neg :=
  Submodule.smul_mem _ _ xPoly_mem_realSub

end Zero

section Bounds

open FourierDuffing.Polynomial.Eigenpair.Numbers
open FourierDuffing.Numbers (muQ leaf)
open RadiiPolynomial.Certification.Fourier.Quadratic (idx idx2 leakRowsQ leakColsQ cadd csub cmul
  cscale cconj cnormSq cinv csum qsum qabs reim toC toC_zero toC_cadd toC_csub toC_cmul toC_cscale
  toC_cinv toC_cconj toC_csum toC_re toC_im sq_norm_toC cast_qsum sum_eq_list sum_headF_eq_list
  mem_idx mem_idx2 nodup_idx nodup_idx2 nodup_leakRowsQ nodup_leakColsQ leakRows_eq leakCols_eq
  mem_leakRows_iff mem_leakCols_iff qabs_eq)
open FourierDuffing.Certificate (duffing_eq_toC)

/-! ### Numeral forms of the head and index memberships (local to this consumer) -/

private theorem mem_headF10 {k : ℤ} : k ∈ headF 10 ↔ -10 ≤ k ∧ k ≤ 10 := by
  simp only [Finset.mem_Icc, Nat.cast_ofNat]

private theorem mem_headF7 {k : ℤ} : k ∈ headF 7 ↔ -7 ≤ k ∧ k ≤ 7 := by
  simp only [Finset.mem_Icc, Nat.cast_ofNat]

private theorem mem_idx10 {k : ℤ} : k ∈ idx 10 ↔ -10 ≤ k ∧ k ≤ 10 := by
  rw [mem_idx, Nat.cast_ofNat]

private theorem mem_idx2_10 {k : ℤ} : k ∈ idx2 10 ↔ -20 ≤ k ∧ k ≤ 20 := by
  rw [mem_idx2]
  norm_num

/-! ### The Duffing data -/

section Accessors

theorem vbarQ_eq_zero {n : ℤ} (hn : n ∉ headF 10) : vbarQ n = (0, 0) := by
  rw [vbarQ, ite_eq_right fun h => hn (mem_headF10.2 h)]

theorem mvQ_eq_zero {n : ℤ} (hn : n ∉ headF 10) : mvQ n = (0, 0) := by
  rw [mvQ, ite_eq_right fun h => hn (mem_headF10.2 h)]

theorem psiQ_eq_zero {n : ℤ} (hn : n ∉ headF 10) : psiQ n = (0, 0) := by
  rw [psiQ, ite_eq_right fun h => hn (mem_headF10.2 h)]

theorem MvQ_eq_zero {i j : ℤ} (hoff : ¬(i ∈ headF 10 ∧ j ∈ headF 10)) : MvQ i j = (0, 0) := by
  rw [MvQ, ite_eq_right fun hij => hoff ⟨mem_headF10.2 hij.1, mem_headF10.2 hij.2⟩]

theorem toC_one : toC (1, 0) = 1 := Complex.ext (by simp [toC]) (by simp [toC])

theorem toC_lbar : toC (lbarQ, 0) = ((lbarQ : ℝ) : ℂ) := Complex.ext (by simp [toC]) (by simp [toC])

theorem mem_headF20 {k : ℤ} : k ∈ headF 20 ↔ -20 ≤ k ∧ k ≤ 20 := by
  simp only [Finset.mem_Icc, Nat.cast_ofNat]

theorem mem_headF10_iff_idx (k : ℤ) : k ∈ headF 10 ↔ k ∈ (idx 10) := mem_headF10.trans
    mem_idx10.symm

end Accessors

section HeadVectors

/-- The shipped head realization, with the head written as `headF 10`. -/
theorem coeff_head_eq (v : ℤ → ℂ) (n : ℤ) :
    coeff (Polynomial.Certificate.head v) n = if n ∈ headF 10 then v n else 0 :=
  Polynomial.Certificate.coeff_head v n

theorem coeff_head_of_mem (v : ℤ → ℂ) {n : ℤ} (hn : n ∈ headF 10) :
    coeff (Polynomial.Certificate.head v) n = v n := by
  rw [coeff_head_eq, ite_eq_left hn]

theorem coeff_head_eq_zero (v : ℤ → ℂ) {n : ℤ} (hn : n ∉ headF 10) :
    coeff (Polynomial.Certificate.head v) n = 0 := by
  rw [coeff_head_eq, ite_eq_right hn]

/-- A rational head vector, zero off the head, has its rational coordinates everywhere. -/
theorem coeff_head_toC {f : ℤ → ℚ × ℚ} (hsupp : ∀ n ∉ headF 10, f n = (0, 0)) (n : ℤ) :
    coeff (Polynomial.Certificate.head fun n => toC (f n)) n = toC (f n) := by
  by_cases hn : n ∈ headF 10
  · exact coeff_head_of_mem _ hn
  · rw [coeff_head_eq_zero _ hn, hsupp n hn, toC_zero]

theorem headProj_head (v : ℤ → ℂ) :
    headProj (𝕜 := ℂ) (headF 10) (Polynomial.Certificate.head v) = Polynomial.Certificate.head v :=
  ext_coeff <| funext fun n => by
    rw [coeff_headProj]
    by_cases hn : n ∈ headF 10
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn, coeff_head_eq_zero v hn]

/-- A rational head vector with conjugate-symmetric coordinates lies in `XR`. -/
theorem head_toC_mem_realSub {f : ℤ → ℚ × ℚ} (hsymm : ∀ n ∈ (idx 10), f (-n) = cconj (f n)) :
    Polynomial.Certificate.head (fun n => toC (f n)) ∈ realSub polyWeight_neg := by
  refine (mem_realSub_iff_coeff polyWeight_neg).2 fun n => ?_
  by_cases hn : n ∈ headF 10
  · rw [coeff_head_of_mem _ ((neg_mem_headF 10 n).2 hn), coeff_head_of_mem _ hn,
      hsymm n (mem_idx10.2 (mem_headF10.1 hn)), toC_cconj]
  · rw [coeff_head_eq_zero _ (mt (neg_mem_headF 10 n).1 hn), coeff_head_eq_zero _ hn, map_zero]

end HeadVectors

section Data

/-- The candidate eigenvector `v̄ ∈ X` (head `|n| ≤ 10`). -/
def vbarX : X := Polynomial.Certificate.head fun n => toC (vbarQ n)

/-- The border column `m_v ∈ X`. -/
def mvX : X := Polynomial.Certificate.head fun n => toC (mvQ n)

/-- The border row `ψ ∈ X`. -/
def psiX : X := Polynomial.Certificate.head fun n => toC (psiQ n)

/-- The defect row `ψ_E ∈ X` (head part of `psiEQ`). -/
def psiEX : X := Polynomial.Certificate.head fun n => toC (psiEQ n)

/-- The head block `M_v` of the bordered head inverse, a finite matrix on `headF 10`. -/
def MvOp : X →L[ℂ] X := finMatrixCLM (headF 10) fun i j => toC (MvQ i j)

/-- The finite potential `q̄ = −2 ā`. -/
def qbarX : X := (-2 : ℝ) • Polynomial.Certificate.abar

theorem coeff_vbarX (n : ℤ) : coeff vbarX n = toC (vbarQ n) :=
  coeff_head_toC (fun _ hn => vbarQ_eq_zero hn) n

theorem coeff_mvX (n : ℤ) : coeff mvX n = toC (mvQ n) :=
  coeff_head_toC (fun _ hn => mvQ_eq_zero hn) n

theorem coeff_psiX (n : ℤ) : coeff psiX n = toC (psiQ n) :=
  coeff_head_toC (fun _ hn => psiQ_eq_zero hn) n

theorem coeff_qbarX (n : ℤ) : coeff qbarX n = toC (qbarQ n) := by
  rw [qbarX, coeff_real_smul, Polynomial.Certificate.coeff_abar, qbarQ, toC_cscale]
  push_cast
  ring

theorem headProj_vbarX : headProj (𝕜 := ℂ) (headF 10) vbarX = vbarX := headProj_head _

theorem headProj_mvX : headProj (𝕜 := ℂ) (headF 10) mvX = mvX := headProj_head _

theorem vbarX_mem_realSub : vbarX ∈ realSub polyWeight_neg :=
  head_toC_mem_realSub checks_data.2.2.2.1

theorem mvX_mem_realSub : mvX ∈ realSub polyWeight_neg := head_toC_mem_realSub checks_data.2.1

theorem qbarX_mem_realSub : qbarX ∈ realSub polyWeight_neg :=
  Submodule.smul_mem _ _ abar_mem_realSub

/-- `M_v` commutes with `K` (the `hKMv` of the face), from the data symmetry `checks_data`. -/
theorem conjReflL_MvOp (x : X) :
    conjReflL polyWeight_neg (MvOp x) = MvOp (conjReflL polyWeight_neg x) :=
  conjReflL_finMatrixCLM polyWeight_neg (headF 10) (neg_mem_headF 10)
    (fun i j => toC (MvQ i j)) (fun i hi j hj => by
      rw [checks_data.1 i (mem_idx10.2 (mem_headF10.1 hi)) j (mem_idx10.2 (mem_headF10.1 hj)),
        toC_cconj]) x

/-- The tail nonresonance at `λ̄`: `4 − λ̄ < 11²`. -/
theorem lbar_lt : (4 : ℝ) - (lbarQ : ℝ) < (((10 : ℕ) : ℝ) + 1) ^ 2 := by
  rw [lbarQ]
  norm_num

/-- **The Duffing eigenpair data** at `u* = xPoly`: `μ = duffing (1/10) 4`, `S = headF 10`,
`q = −2 u*`, the shift `λ̄`, and the bordered head inverse `(M_v, m_v, ψ, c)` of the generated
data. -/
def duffEigen : EigenData polyWeight_neg where
  μ := duffing (1 / 10) 4
  S := headF 10
  q := (-2 : ℝ) • Polynomial.Certificate.xPoly
  lbar := (lbarQ : ℝ)
  hr := bddAbove_tailSymbol_duffing_sub lbar_lt
  Mv := MvOp
  mv := mvX
  ψ := psiX
  c := (cQ : ℝ)
  hμ := duffing_conj _ _
  hS := neg_mem_headF 10
  hq := potential_mem_realSub
  hPMv := headProj_comp_finMatrixCLM _ _
  hKMv := conjReflL_MvOp
  hmv := mvX_mem_realSub

theorem duffEigen_S : duffEigen.S = headF 10 := rfl

theorem duffEigen_μ : duffEigen.μ = duffing (1 / 10) 4 := rfl

theorem duffEigen_lbar : duffEigen.lbar = (lbarQ : ℝ) := rfl

/-- The same data at the finite potential `q̄` (the structure update of `q`, `hq` only). -/
def duffEigenBar : EigenData polyWeight_neg :=
  { duffEigen with q := qbarX, hq := qbarX_mem_realSub }

/-- The candidate in `XR`. -/
def vbarR : realSub polyWeight_neg := ⟨vbarX, vbarX_mem_realSub⟩

/-- The centre `ȳ = (v̄, λ̄)` of the faces. -/
def ybar : realSub polyWeight_neg × ℝ := (vbarR, duffEigen.lbar)

/-- The centre is head-supported (`hvS`). -/
theorem headProj_vbarR : headProj (𝕜 := ℂ) duffEigen.S (vbarR : X) = vbarR := headProj_vbarX

/-- The potential split radius (`hδq`): `‖q − q̄‖ = 2 ‖u* − ā‖ ≤ 2 ρ₀`. -/
theorem norm_potential_sub_qbarX_le : ‖duffEigen.q - qbarX‖ ≤ (rhoqQ : ℝ) := by
  have hball := Polynomial.Certificate.xPoly_ball
  rw [Metric.mem_closedBall, dist_eq_norm] at hball
  change ‖(-2 : ℝ) • Polynomial.Certificate.xPoly - (-2 : ℝ) • Polynomial.Certificate.abar‖ ≤ _
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_neg, abs_two, rhoqQ, Rat.cast_mul,
    Rat.cast_ofNat]
  exact mul_le_mul_of_nonneg_left hball zero_le_two

/-- The symbol coherence (`hβ`): `L_β = −(q̄ ⋆ ·)`, `β = 2ā = −q̄`. -/
theorem symbolAction₀_β_eq_neg_convCLM_qbarX :
    symbolAction₀ (p := 2) polyModerate Polynomial.Certificate.β = -convCLM polyRowBound qbarX :=
  ContinuousLinearMap.ext fun h => by
    change Polynomial.Certificate.LB h = _
    rw [← Polynomial.Certificate.two_polyProd, neg_apply, qbarX,
      ContinuousLinearMap.map_smul_of_tower, smul_apply, neg_smul, neg_neg,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    norm_num

/-- The band of `q̄` (`hB`): `q̄_l = 0` for `|l| > 7`. -/
theorem coeff_qbarX_eq_zero : ∀ l ∉ headF 7, coeff qbarX l = 0 := fun l hl => by
  have hband := Polynomial.Certificate.band_beta l hl
  simp only [Polynomial.Certificate.raw_β] at hband
  rw [qbarX, coeff_real_smul, (mul_eq_zero.1 hband).resolve_left two_ne_zero, mul_zero]

/-- The tail-symbol bound (`ht`): `|μ_n − λ̄|⁻¹ ≤ (11² − (4 − λ̄))⁻¹ = (117 + λ̄)⁻¹` off the head.
-/
theorem norm_tailSymbol_duffEigen_le (n : ℤ) :
    ‖tailSymbol (↑duffEigen.S : Set ℤ) (fun n => duffEigen.μ n - (duffEigen.lbar : ℂ)) n‖ ≤
      (tQ : ℝ) :=
  (norm_tailSymbol_duffing_sub_le (c₁ := 1 / 10) lbar_lt n).trans
    ((inv_norm_duffing_succ_le lbar_lt).trans_eq (by rw [tQ]; push_cast; ring))

end Data

/-! ### The finite-vector toolkit and the coefficient bridges -/

section Toolkit

private theorem qsum_congr (l : List ℤ) {f g : ℤ → ℚ} (hfg : ∀ n ∈ l, f n = g n) :
    qsum l f = qsum l g := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    exact congrArg₂ (· + ·) (hfg k (by simp)) (ih fun n hn => hfg n (by simp [hn]))

/-- **The finite norm from a rational square bound** (the shipped `Certificate.Y0_le` pattern). -/
theorem norm_le_of_qsum (x : X) (T : Finset ℤ) (l : List ℤ) (hl : l.Nodup)
    (hT : ∀ k, k ∈ T ↔ k ∈ l) (hx : ∀ n ∉ T, coeff x n = 0) (f : ℤ → ℚ × ℚ)
    (hf : ∀ n ∈ T, coeff x n = toC (f n)) (B : ℚ) (hB0 : 0 ≤ B)
    (hB : qsum l (fun n => cnormSq (f n) * Numbers.weightQ n ^ 2) ≤ B ^ 2) : ‖x‖ ≤ (B : ℝ) := by
  have hnormSq : ‖x‖ ^ 2 = ((qsum l fun n => cnormSq (f n) * Numbers.weightQ n ^ 2 : ℚ) : ℝ) := by
    rw [norm_sq_eq_tsum, tsum_eq_sum (s := T) fun n hn => by
      rw [norm_apply_eq, hx n hn, norm_zero, zero_mul, sq, zero_mul], sum_eq_list hl hT, cast_qsum]
    refine congrArg List.sum (List.map_congr_left fun n hn => ?_)
    rw [norm_apply_eq, WeightedScalar.fiberTrivialization_weight, mul_pow, hf n ((hT n).2 hn),
      sq_norm_toC, Polynomial.Certificate.weight_cast]
    push_cast
    rfl
  refine (pow_le_pow_iff_left₀ (norm_nonneg x) (Rat.cast_nonneg.2 hB0) two_ne_zero).1 ?_
  rw [hnormSq]
  exact_mod_cast hB

/-- **The rational pairing** of two finitely supported vectors. -/
theorem pairing_eq_qsum (x y : X) (T : Finset ℤ) (l : List ℤ) (hl : l.Nodup)
    (hT : ∀ k, k ∈ T ↔ k ∈ l) (hx : ∀ n ∉ T, coeff x n = 0) (f g : ℤ → ℚ × ℚ)
    (hf : ∀ n ∈ T, coeff x n = toC (f n)) (hg : ∀ n ∈ T, coeff y n = toC (g n)) :
    pairing one_le_polyWeight x y = ((qsum l fun n => (cmul (cconj (f n)) (g n)).1 : ℚ) : ℝ) := by
  rw [pairing_eq_tsum, tsum_eq_sum (s := T) fun n hn => by
      rw [hx n hn, map_zero, zero_mul, Complex.zero_re], sum_eq_list hl hT, cast_qsum]
  refine congrArg List.sum (List.map_congr_left fun n hn => ?_)
  rw [hf n ((hT n).2 hn), hg n ((hT n).2 hn), ← toC_cconj, ← toC_cmul, toC_re]

/-- The norm of a rational head vector from its square bound over `(idx 10)`. -/
theorem norm_head_toC_le (f : ℤ → ℚ × ℚ) (B : ℚ) (hB0 : 0 ≤ B)
    (hB : qsum (idx 10) (fun n => cnormSq (f n) * Numbers.weightQ n ^ 2) ≤ B ^ 2) :
    ‖Polynomial.Certificate.head fun n => toC (f n)‖ ≤ (B : ℝ) :=
  norm_le_of_qsum _ (headF 10) (idx 10) (nodup_idx 10) mem_headF10_iff_idx
    (fun _ hn => coeff_head_eq_zero _ hn) f (fun _ hn => coeff_head_of_mem _ hn) B hB0 hB

theorem norm_vbarX_le (hB0 : 0 ≤ nvQ) (hB : nvSqQ ≤ nvQ ^ 2) : ‖vbarX‖ ≤ (nvQ : ℝ) :=
  norm_head_toC_le vbarQ nvQ hB0 hB

theorem norm_mvX_le (hB0 : 0 ≤ smQ) (hB : mvSqQ ≤ smQ ^ 2) : ‖mvX‖ ≤ (smQ : ℝ) :=
  norm_head_toC_le mvQ smQ hB0 hB

theorem norm_psiX_le (hB0 : 0 ≤ spsiQ) (hB : psiSqQ ≤ spsiQ ^ 2) : ‖psiX‖ ≤ (spsiQ : ℝ) :=
  norm_head_toC_le psiQ spsiQ hB0 hB

theorem norm_psiEX_le (hB0 : 0 ≤ z21Q) (hB : psiESqQ ≤ z21Q ^ 2) : ‖psiEX‖ ≤ (z21Q : ℝ) :=
  norm_head_toC_le psiEQ z21Q hB0 hB

/-- The border row on the leak rows `4 ≤ |n| ≤ 10`. -/
theorem norm_psiRows_le (hB0 : 0 ≤ nPsiRowsQ) (hB : psiRowsSqQ ≤ nPsiRowsQ ^ 2) :
    ‖headProj (𝕜 := ℂ) (leakRows (headF 10) (headF 7)) psiX‖ ≤ (nPsiRowsQ : ℝ) :=
  norm_le_of_qsum _ (leakRows (headF 10) (headF 7)) (leakRowsQ 10 7) (nodup_leakRowsQ (show 7 ≤ 10
      by norm_num)) (mem_leakRows_iff (show 7 ≤ 10 by norm_num))
    (fun n hn => by rw [coeff_headProj, ite_eq_right hn]) psiQ
    (fun n hn => by rw [coeff_headProj, ite_eq_left hn, coeff_psiX]) nPsiRowsQ hB0 hB

end Toolkit

section Bridges

/-- The product with `q̄` on a head vector: `(q̄ ⋆ x)_n = ∑_{j ∈ S} q̄_{n−j} x_j`. -/
theorem coeff_convCLM_qbarX_of_head (x : X) (hx : ∀ n ∉ headF 10, coeff x n = 0) (n : ℤ) :
    coeff (convCLM polyRowBound qbarX x) n =
      ∑ j ∈ headF 10, toC (qbarQ (n - j)) * coeff x j := by
  rw [convCLM_comm polyRowBound qbarX x, coeff_convCLM, FourierDuffing.Polynomial.conv_apply,
    tsum_eq_sum (s := headF 10) fun j hj => by rw [hx j hj, zero_mul]]
  exact Finset.sum_congr rfl fun j _ => by rw [coeff_qbarX, mul_comm]

/-- **The head Jacobian at `q̄`** is the finite matrix `jacQ`. -/
theorem eigenHeadJac_qbarX_eq :
    eigenHeadJac polyRowBound duffEigen.toEigenRaw qbarX =
      finMatrixCLM (headF 10) fun k j => toC (jacQ k j) := by
  refine ContinuousLinearMap.ext fun x => ext_coeff <| funext fun k => ?_
  have hPx : ∀ n ∉ headF 10, coeff (headProj (𝕜 := ℂ) (headF 10) x) n = 0 := fun n hn => by
    rw [coeff_headProj, ite_eq_right hn]
  rw [eigenHeadJac, duffEigen_S, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    coeff_headProj, coeff_finMatrixCLM]
  by_cases hk : k ∈ headF 10
  · rw [ite_eq_left hk, ite_eq_left hk, sub_apply,
      add_apply, coeff_sub, coeff_add, Pi.sub_apply, Pi.add_apply,
      coeff_eigenLam, duffEigen_S, headPart, ite_eq_left hk, duffEigen_μ,
      smul_apply, ContinuousLinearMap.id_apply, coeff_smul, Pi.smul_apply,
      smul_eq_mul, coeff_convCLM_qbarX_of_head _ hPx k, coeff_headProj, ite_eq_left hk,
      duffEigen_lbar]
    have hsplit : ∀ j, toC (jacQ k j) * coeff x j =
        (if k = j then (duffing (1 / 10) 4 k - ((lbarQ : ℝ) : ℂ)) * coeff x k else 0) +
          toC (qbarQ (k - j)) * coeff x j := fun j => by
      rw [jacQ, toC_cadd, add_mul]
      congr 1
      split_ifs with hkj
      · subst hkj
        rw [toC_csub, ← duffing_eq_toC, toC_lbar]
      · rw [toC_zero, zero_mul]
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, Finset.sum_ite_eq,
      ite_eq_left hk, Finset.sum_congr rfl fun j hj => by rw [coeff_headProj, ite_eq_left hj]]
    ring
  · rw [ite_eq_right hk, ite_eq_right hk]

/-- The head residual at the candidate is the head Jacobian applied to `v̄`. -/
theorem eigenHeadRes_bar :
    eigenHeadRes polyRowBound duffEigenBar.toEigenRaw vbarX duffEigen.lbar =
      eigenHeadJac polyRowBound duffEigen.toEigenRaw qbarX vbarX := by
  rw [eigenHeadJac, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, duffEigen_S,
    headProj_vbarX, sub_apply, add_apply,
    smul_apply, ContinuousLinearMap.id_apply,
    ← RCLike.ofReal_eq_complex_ofReal, ← RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- The head residual `ρ = J v̄` in coordinates. -/
theorem coeff_J_vbarX {k : ℤ} (hk : k ∈ headF 10) :
    coeff (eigenHeadJac polyRowBound duffEigen.toEigenRaw qbarX vbarX) k = toC (rhoQ k) := by
  rw [eigenHeadJac_qbarX_eq, coeff_finMatrixCLM, ite_eq_left hk, rhoQ, toC_csum,
    ← (sum_headF_eq_list 10)]
  exact Finset.sum_congr rfl fun j _ => by rw [coeff_vbarX, toC_cmul]

theorem pairing_vbarX_self : pairing one_le_polyWeight vbarX vbarX = ((1 + etaQ : ℚ) : ℝ) := by
  rw [pairing_eq_qsum vbarX vbarX (headF 10) (idx 10) (nodup_idx 10) mem_headF10_iff_idx
    (fun _ hn => coeff_head_eq_zero _ hn) vbarQ vbarQ (fun n _ => coeff_vbarX n)
    (fun n _ => coeff_vbarX n), etaQ, add_sub_cancel]
  exact congrArg _ (qsum_congr (idx 10) fun n _ => by simp only [cmul, cconj, cnormSq]; ring)

theorem pairing_psiX_vbarX : pairing one_le_polyWeight psiX vbarX = (bpsivQ : ℝ) :=
  pairing_eq_qsum psiX vbarX (headF 10) (idx 10) (nodup_idx 10) mem_headF10_iff_idx
    (fun _ hn => coeff_head_eq_zero _ hn) psiQ vbarQ (fun n _ => coeff_psiX n)
    (fun n _ => coeff_vbarX n)

/-- **The first residual component at `q̄`** in coordinates (`hfin₁`). -/
theorem coeff_eigenFst_bar (n : ℤ) :
    coeff (eigenFst one_le_polyWeight polyRowBound duffEigenBar.toEigenRaw (vbarR : X)
      duffEigen.lbar) n = toC (g1Q n) := by
  by_cases hn : n ∈ headF 10
  · rw [coeff_eigenFst_of_mem one_le_polyWeight polyRowBound duffEigenBar.toEigenRaw _ _ hn]
    change coeff (MvOp (eigenHeadRes polyRowBound duffEigenBar.toEigenRaw vbarX duffEigen.lbar)) n +
      ((pairing one_le_polyWeight vbarX vbarX - 1 : ℝ) : ℂ) * coeff mvX n = _
    rw [eigenHeadRes_bar, pairing_vbarX_self, MvOp, coeff_finMatrixCLM, ite_eq_left hn, g1Q,
      ite_eq_left (mem_headF10.1 hn), toC_cadd, toC_csum, ← (sum_headF_eq_list 10), toC_cscale,
      coeff_mvX]
    congr 1
    · exact Finset.sum_congr rfl fun k hk => by rw [coeff_J_vbarX hk, toC_cmul]
    · push_cast
      ring
  · rw [coeff_eigenFst_of_notMem polyWeight_neg one_le_polyWeight polyRowBound duffEigenBar
      headProj_mvX
      _ _ hn]
    change coeff vbarX n + (duffing (1 / 10) 4 n - ((lbarQ : ℝ) : ℂ))⁻¹ *
      (coeff (convCLM polyRowBound qbarX vbarX) n -
        (((lbarQ : ℝ) : ℂ) - ((lbarQ : ℝ) : ℂ)) * coeff vbarX n) = _
    rw [sub_self, zero_mul, sub_zero, coeff_vbarX, vbarQ_eq_zero hn, toC_zero, zero_add,
      coeff_convCLM_qbarX_of_head vbarX (fun _ hm => coeff_head_eq_zero _ hm) n, g1Q,
      ite_eq_right (fun h => hn (mem_headF10.2 h)), toC_cmul, toC_cinv, toC_csub,
      ← duffing_eq_toC, toC_lbar, convbQ, toC_csum, ← (sum_headF_eq_list 10)]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [coeff_vbarX, toC_cmul]

/-- The first residual component vanishes for `|n| > 20`. -/
theorem coeff_eigenFst_bar_eq_zero {n : ℤ} (hn : n ∉ headF 20) :
    coeff (eigenFst one_le_polyWeight polyRowBound duffEigenBar.toEigenRaw (vbarR : X)
      duffEigen.lbar) n = 0 := by
  have hn10 : n ∉ headF 10 := fun h => hn (mem_headF20.2 (by have := mem_headF10.1 h; omega))
  rw [coeff_eigenFst_bar, g1Q, ite_eq_right (fun h => hn10 (mem_headF10.2 h)), toC_cmul, convbQ,
    toC_csum, ← (sum_headF_eq_list 10), Finset.sum_eq_zero fun k hk => by
      rw [toC_cmul, ← coeff_qbarX, coeff_qbarX_eq_zero _ (fun h => hn (mem_headF20.2 (by
        have := mem_headF7.1 h; have := mem_headF10.1 hk; omega))), zero_mul], mul_zero]

theorem norm_eigenFst_bar_le (hY : g1SqQ ≤ YfinQ ^ 2) (hY0 : 0 ≤ YfinQ) :
    ‖eigenFst one_le_polyWeight polyRowBound duffEigenBar.toEigenRaw (vbarR : X)
      duffEigen.lbar‖ ≤ (YfinQ : ℝ) :=
  norm_le_of_qsum _ (headF 20) (idx2 10) (nodup_idx2 10) (fun _ => mem_headF20.trans
      mem_idx2_10.symm)
    (fun _ hn => coeff_eigenFst_bar_eq_zero hn) g1Q (fun n _ => coeff_eigenFst_bar n) YfinQ hY0 hY

/-- **The second residual component at `q̄`** (`hfin₂`). -/
theorem eigenSnd_bar :
    eigenSnd one_le_polyWeight polyRowBound duffEigenBar.toEigenRaw (vbarR : X) duffEigen.lbar =
      (g2Q : ℝ) := by
  change pairing one_le_polyWeight psiX
      (eigenHeadRes polyRowBound duffEigenBar.toEigenRaw vbarX duffEigen.lbar) +
    (cQ : ℝ) * (pairing one_le_polyWeight vbarX vbarX - 1) = _
  rw [eigenHeadRes_bar, pairing_vbarX_self,
      pairing_eq_qsum psiX _ (headF 10) (idx 10) (nodup_idx 10)
    mem_headF10_iff_idx (fun _ hn => coeff_head_eq_zero _ hn) psiQ rhoQ
    (fun n _ => coeff_psiX n) (fun _ hn => coeff_J_vbarX hn), g2Q]
  push_cast
  ring

theorem abs_eigenSnd_bar_le (hg2 : qabs g2Q ≤ YfinQ) :
    |eigenSnd one_le_polyWeight polyRowBound duffEigenBar.toEigenRaw (vbarR : X)
      duffEigen.lbar| ≤ (YfinQ : ℝ) := by
  rw [eigenSnd_bar, qabs_eq] at *
  exact_mod_cast hg2

theorem coeff_MvOp_vbarX (i : ℤ) : coeff (MvOp vbarX) i = toC (MvvQ i) := by
  rw [MvOp, coeff_finMatrixCLM, MvvQ, toC_csum, ← (sum_headF_eq_list 10)]
  by_cases hi : i ∈ headF 10
  · rw [ite_eq_left hi]
    exact Finset.sum_congr rfl fun j _ => by rw [coeff_vbarX, toC_cmul]
  · rw [ite_eq_right hi]
    exact (Finset.sum_eq_zero fun j _ => by
      rw [toC_cmul, MvQ_eq_zero fun hij => hi hij.1, toC_zero, zero_mul]).symm

theorem norm_MvOp_vbarX_le (hB0 : 0 ≤ nMvvQ) (hB : MvvSqQ ≤ nMvvQ ^ 2) :
    ‖MvOp vbarX‖ ≤ (nMvvQ : ℝ) :=
  norm_le_of_qsum _ (headF 10) (idx 10) (nodup_idx 10) mem_headF10_iff_idx
    (fun _ hn => by rw [MvOp, coeff_finMatrixCLM, ite_eq_right hn]) MvvQ
    (fun n _ => coeff_MvOp_vbarX n) nMvvQ hB0 hB

/-- The defect row as a vector: `ψ_E = Jᴴ ψ + 2 c v̄`. -/
theorem psiEX_eq : psiEX = finMatrixCLM (headF 10) (fun i j => starRingEnd ℂ (toC (jacQ j i))) psiX
    +
    (2 * (cQ : ℝ)) • vbarX := by
  refine ext_coeff <| funext fun n => ?_
  rw [coeff_add, Pi.add_apply, coeff_finMatrixCLM, coeff_real_smul]
  by_cases hn : n ∈ headF 10
  · rw [psiEX, coeff_head_of_mem _ hn, ite_eq_left hn, psiEQ, toC_cadd, toC_csum,
      ← (sum_headF_eq_list 10), toC_cscale, coeff_vbarX]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by rw [toC_cmul, toC_cconj, coeff_psiX]
    · push_cast
      ring
  · rw [psiEX, coeff_head_eq_zero _ hn, ite_eq_right hn, coeff_vbarX, vbarQ_eq_zero hn, toC_zero,
      mul_zero, add_zero]

/-- The matrix of `M_v` is the mirror (every `i`, `j`). -/
theorem matrixOf_MvOp (i j : ℤ) : matrixOf MvOp i j = toC (MvQ i j) := by
  rw [MvOp, matrixOf_finMatrixCLM]
  split_ifs with hij
  · rfl
  · rw [MvQ_eq_zero hij, toC_zero]

/-- The weighted Schur bound of a rational finite matrix on the head. -/
theorem norm_finMatrix_toC_le_of (K : ℤ → ℤ → ℚ × ℚ) {R C s : ℚ} (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (hs0 : 0 ≤ s)
    (hrow : ∀ i ∈ (idx 10),
        qsum (idx 10) (fun j => reim (K i j) * Numbers.weightQ i / Numbers.weightQ j) ≤ R)
    (hcol : ∀ j ∈ (idx 10),
        qsum (idx 10) (fun i => reim (K i j) * Numbers.weightQ i / Numbers.weightQ j) ≤ C)
    (hsq : R * C ≤ s ^ 2) :
    ‖(finMatrixCLM (headF 10) fun i j => toC (K i j) : X →L[ℂ] X)‖ ≤ (s : ℝ) := by
  have hblock : headProj (𝕜 := ℂ) (headF 10) ∘L
      (finMatrixCLM (headF 10) fun i j => toC (K i j) : X →L[ℂ] X) ∘L headProj (headF 10) =
        finMatrixCLM (headF 10) fun i j => toC (K i j) := by
    rw [finMatrixCLM_comp_headProj, headProj_comp_finMatrixCLM]
  have hentry : ∀ i ∈ headF 10, ∀ j ∈ headF 10,
      schurEntry (FiberTrivialization.weight (𝕜 := ℂ) (E := WeightedScalar ℂ polyWeight))
        (FiberTrivialization.weight (𝕜 := ℂ) (E := WeightedScalar ℂ polyWeight))
        (matrixOf (finMatrixCLM (headF 10) fun i j => toC (K i j) : X →L[ℂ] X)) i j ≤
      ((reim (K i j) * Numbers.weightQ i / Numbers.weightQ j : ℚ) : ℝ) := fun i hi j hj => by
    rw [schurEntry, matrixOf_finMatrixCLM, ite_eq_left ⟨hi, hj⟩,
      WeightedScalar.fiberTrivialization_weight, WeightedScalar.fiberTrivialization_weight]
    exact Polynomial.Certificate.weighted_le_reim _ i j
  refine (norm_le_sqrt_of_block _ hblock (R := (R : ℝ)) (C := (C : ℝ)) (Rat.cast_nonneg.2 hR0)
    (Rat.cast_nonneg.2 hC0) (fun i hi => ?_) (fun j hj => ?_)).trans ?_
  · refine (Finset.sum_le_sum fun j hj => hentry i hi j hj).trans ?_
    rw [(sum_headF_eq_list 10), ← cast_qsum]
    exact_mod_cast hrow i (mem_idx10.2 (mem_headF10.1 hi))
  · refine (Finset.sum_le_sum fun i hi => hentry i hi j hj).trans ?_
    rw [(sum_headF_eq_list 10), ← cast_qsum]
    exact_mod_cast hcol j (mem_idx10.2 (mem_headF10.1 hj))
  · exact (Real.sqrt_le_sqrt (by exact_mod_cast hsq)).trans_eq (Real.sqrt_sq (Rat.cast_nonneg.2
      hs0))

/-- The Schur bound of `M_v` from the `M_v` clauses. -/
theorem norm_MvOp_le_of (hR0 : 0 ≤ RMQ) (hC0 : 0 ≤ CMQ) (hs0 : 0 ≤ sMQ)
    (hrow : ∀ i ∈ (idx 10), mvRowQ i ≤ RMQ) (hcol : ∀ j ∈ (idx 10), mvColQ j ≤ CMQ)
    (hsq : RMQ * CMQ ≤ sMQ ^ 2) : ‖MvOp‖ ≤ (sMQ : ℝ) :=
  norm_finMatrix_toC_le_of MvQ hR0 hC0 hs0 hrow hcol hsq

/-- The Schur bound of the defect block `E_SS` from the `E` clauses. -/
theorem norm_defOp_le_of (hR0 : 0 ≤ REQ) (hC0 : 0 ≤ CEQ) (hs0 : 0 ≤ z11Q)
    (hrow : ∀ i ∈ (idx 10), defRowQ i ≤ REQ) (hcol : ∀ j ∈ (idx 10), defColQ j ≤ CEQ)
    (hsq : REQ * CEQ ≤ z11Q ^ 2) :
    ‖(finMatrixCLM (headF 10) fun i j => toC (defQ i j) : X →L[ℂ] X)‖ ≤ (z11Q : ℝ) :=
  norm_finMatrix_toC_le_of defQ hR0 hC0 hs0 hrow hcol hsq

/-- The composed leakage kernel of `M_v` with `β = 2ā` is the mirror `kmvQ`. -/
theorem composedLeakKernel_MvOp (i k : ℤ) :
    composedLeakKernel MvOp Polynomial.Certificate.β (headF 10) (headF 7) i k = toC (kmvQ i k) := by
  rw [composedLeakKernel, kmvQ, toC_csum, (leakRows_eq (show 7 ≤ 10 by norm_num)),
      List.sum_toFinset _ (nodup_leakRowsQ (show 7 ≤ 10 by norm_num))]
  refine congrArg List.sum (List.map_congr_left fun n _ => ?_)
  rw [matrixOf_MvOp, toC_cmul, toC_cscale]
  simp only [Polynomial.Certificate.raw_β, Polynomial.Certificate.coeff_abar]
  push_cast
  ring

/-- The composed leakage kernel of the head projection with `β` is the leak block `leakQ`. -/
theorem composedLeakKernel_headProj {i : ℤ} (hi : i ∈ headF 10) (k : ℤ) :
    composedLeakKernel (headProj (𝕜 := ℂ) (E := WeightedScalar ℂ polyWeight) (p := 2) (headF 10))
      Polynomial.Certificate.β (headF 10) (headF 7) i k = toC (leakQ i k) := by
  rw [composedLeakKernel, leakQ, toC_csum, (leakRows_eq (show 7 ≤ 10 by norm_num)),
      List.sum_toFinset _ (nodup_leakRowsQ (show 7 ≤ 10 by norm_num))]
  refine congrArg List.sum (List.map_congr_left fun n _ => ?_)
  rw [matrixOf_headProj, toC_cmul, toC_cscale]
  simp only [Polynomial.Certificate.raw_β, Polynomial.Certificate.coeff_abar]
  by_cases hin : i = n
  · rw [ite_eq_left ⟨hin, hi⟩, ite_eq_left hin, toC_one]
    push_cast
    ring
  · rw [ite_eq_right fun h' => hin h'.1, ite_eq_right hin, toC_zero, zero_mul, zero_mul]

/-- The head leakage of `M_v` (`hH`) from the `H` clauses. -/
theorem norm_head_term_MvOp_le_of (hR0 : 0 ≤ RHQ) (hC0 : 0 ≤ CHQ) (hH0 : 0 ≤ HeQ)
    (hrow : ∀ i ∈ (idx 10), kmvRowQ i ≤ RHQ) (hcol : ∀ k ∈ (leakColsQ 10 7), kmvColQ k ≤ CHQ)
    (hsq : RHQ * CHQ ≤ HeQ ^ 2) :
    ‖MvOp ∘L headProj (headF 10) ∘L symbolAction₀ (p := 2) polyModerate Polynomial.Certificate.β ∘L
      tailProj (headF 10)‖ ≤ (HeQ : ℝ) := by
  refine (norm_head_term_le_composed polyModerate Polynomial.Certificate.β (headF 10) (headF 7) MvOp
    Polynomial.Certificate.band_beta (headProj_comp_finMatrixCLM _ _) (Rm := (RHQ : ℝ))
    (Cm := (CHQ : ℝ)) (Rat.cast_nonneg.2 hR0) (Rat.cast_nonneg.2 hC0) (fun i hi => ?_)
    (fun k hk => ?_)).trans ?_
  · refine (Finset.sum_le_sum (g := fun k =>
      ((reim (kmvQ i k) * Numbers.weightQ i / Numbers.weightQ k : ℚ) : ℝ)) fun k _ => ?_).trans ?_
    · rw [composedLeakKernel_MvOp, WeightedScalar.fiberTrivialization_weight,
        WeightedScalar.fiberTrivialization_weight]
      exact Polynomial.Certificate.weighted_le_reim _ i k
    · rw [(leakCols_eq 10 7), List.sum_toFinset _ (nodup_leakColsQ 10 7), ← cast_qsum]
      exact_mod_cast hrow i (mem_idx10.2 (mem_headF10.1 hi))
  · refine (Finset.sum_le_sum (g := fun i =>
      ((reim (kmvQ i k) * Numbers.weightQ i / Numbers.weightQ k : ℚ) : ℝ)) fun i _ => ?_).trans ?_
    · rw [composedLeakKernel_MvOp, WeightedScalar.fiberTrivialization_weight,
        WeightedScalar.fiberTrivialization_weight]
      exact Polynomial.Certificate.weighted_le_reim _ i k
    · rw [(sum_headF_eq_list 10), ← cast_qsum]
      exact_mod_cast hcol k (((mem_leakCols_iff 10 7) k).1 hk)
  · exact (Real.sqrt_le_sqrt (by exact_mod_cast hsq)).trans_eq (Real.sqrt_sq (Rat.cast_nonneg.2
      hH0))

/-- The leak block `P_S (q̄ ⋆ ·) Q_S` (`hsL`) from the leak clauses, through `hβ`. -/
theorem norm_leakBlock_le_of (hR0 : 0 ≤ RLQ) (hC0 : 0 ≤ CLQ) (hs0 : 0 ≤ sLQ)
    (hrow : ∀ i ∈ (idx 10), leakRowQ i ≤ RLQ) (hcol : ∀ k ∈ (leakColsQ 10 7), leakColQ k ≤ CLQ)
    (hsq : RLQ * CLQ ≤ sLQ ^ 2) :
    ‖headProj (𝕜 := ℂ) (headF 10) ∘L convCLM polyRowBound qbarX ∘L tailProj (headF 10)‖ ≤
      (sLQ : ℝ) := by
  have hneg : convCLM polyRowBound qbarX =
      -symbolAction₀ (p := 2) polyModerate Polynomial.Certificate.β := by
    rw [symbolAction₀_β_eq_neg_convCLM_qbarX, neg_neg]
  have hP : headProj (𝕜 := ℂ) (headF 10) ∘L
      symbolAction₀ (p := 2) polyModerate Polynomial.Certificate.β ∘L tailProj (headF 10) =
      headProj (headF 10) ∘L headProj (headF 10) ∘L
        symbolAction₀ (p := 2) polyModerate Polynomial.Certificate.β ∘L tailProj (headF 10) := by
    rw [← ContinuousLinearMap.comp_assoc (headProj (headF 10)) (headProj (headF 10)),
      headProj_comp_headProj]
  rw [hneg, ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg, norm_neg, hP]
  refine (norm_head_term_le_composed polyModerate Polynomial.Certificate.β (headF 10) (headF 7)
    (headProj (headF 10)) Polynomial.Certificate.band_beta (headProj_comp_headProj _)
    (Rm := (RLQ : ℝ)) (Cm := (CLQ : ℝ)) (Rat.cast_nonneg.2 hR0) (Rat.cast_nonneg.2 hC0)
    (fun i hi => ?_) (fun k hk => ?_)).trans ?_
  · refine (Finset.sum_le_sum (g := fun k =>
      ((reim (leakQ i k) * Numbers.weightQ i / Numbers.weightQ k : ℚ) : ℝ)) fun k _ => ?_).trans ?_
    · rw [composedLeakKernel_headProj hi, WeightedScalar.fiberTrivialization_weight,
        WeightedScalar.fiberTrivialization_weight]
      exact Polynomial.Certificate.weighted_le_reim _ i k
    · rw [(leakCols_eq 10 7), List.sum_toFinset _ (nodup_leakColsQ 10 7), ← cast_qsum]
      exact_mod_cast hrow i (mem_idx10.2 (mem_headF10.1 hi))
  · refine (Finset.sum_le_sum (g := fun i =>
      ((reim (leakQ i k) * Numbers.weightQ i / Numbers.weightQ k : ℚ) : ℝ)) fun i hi => ?_).trans ?_
    · rw [composedLeakKernel_headProj hi, WeightedScalar.fiberTrivialization_weight,
        WeightedScalar.fiberTrivialization_weight]
      exact Polynomial.Certificate.weighted_le_reim _ i k
    · rw [(sum_headF_eq_list 10), ← cast_qsum]
      exact_mod_cast hcol k (((mem_leakCols_iff 10 7) k).1 hk)
  · exact (Real.sqrt_le_sqrt (by exact_mod_cast hsq)).trans_eq (Real.sqrt_sq (Rat.cast_nonneg.2
      hs0))

end Bridges

/-! ### `Y₀` -/

section Y0

theorem duff_Y0_le :
    ‖eigenMap polyWeight_neg one_le_polyWeight polyRowBound duffEigen ybar‖ ≤ (Y0eQ : ℝ) := by
  obtain ⟨hg1, hg2, hY0, hrow, hcol, hsq, hR0, hC0, hs0, hpsi, hpsi0, hnv, hnv0, hY⟩ := checks_Y0
  refine (norm_eigenMap_le polyWeight_neg one_le_polyWeight polyRowBound duffEigen qbarX ybar
    (norm_eigenFst_bar_le hg1 hY0) (abs_eigenSnd_bar_le hg2)
    (norm_MvOp_le_of hR0 hC0 hs0 hrow hcol hsq) norm_tailSymbol_duffEigen_le
    (norm_psiX_le hpsi0 hpsi) norm_potential_sub_qbarX_le (norm_vbarX_le hnv0 hnv)).trans ?_
  rw [KcQ] at hY
  exact_mod_cast hY

end Y0

/-! ### `Z₀` -/

section Z0

/-- The defect block on `XR`: `P x − M_v J x − 2 b(v̄, P x) m_v = E_SS x` (the realness step
consumes `x ∈ XR`). -/
theorem defect_eq (x : X) (hx : x ∈ realSub polyWeight_neg) :
    headProj (𝕜 := ℂ) (headF 10) x - MvOp (eigenHeadJac polyRowBound duffEigen.toEigenRaw qbarX x) -
      (2 * pairing one_le_polyWeight vbarX (headProj (𝕜 := ℂ) (headF 10) x)) • mvX =
    (finMatrixCLM (headF 10) fun i j => toC (defQ i j) : X →L[ℂ] X) x := by
  have hb : ((pairing one_le_polyWeight vbarX (headProj (𝕜 := ℂ) (headF 10) x) : ℝ) : ℂ) =
      ∑ j ∈ headF 10, starRingEnd ℂ (toC (vbarQ j)) * coeff x j :=
    (ofReal_pairing_headProj_eq_sum polyWeight_neg one_le_polyWeight (neg_mem_headF 10)
      vbarX_mem_realSub hx).trans (Finset.sum_congr rfl fun j _ => by rw [coeff_vbarX])
  refine ext_coeff <| funext fun i => ?_
  rw [coeff_sub, coeff_sub, Pi.sub_apply, Pi.sub_apply, coeff_real_smul, coeff_headProj,
    eigenHeadJac_qbarX_eq, MvOp, coeff_finMatrixCLM, coeff_finMatrixCLM, coeff_mvX]
  by_cases hi : i ∈ headF 10
  · rw [ite_eq_left hi, ite_eq_left hi, ite_eq_left hi, Complex.ofReal_mul, Complex.ofReal_ofNat,
      hb]
    have hD : ∀ j, toC (defQ i j) * coeff x j = (if i = j then coeff x j else 0) -
        ∑ k ∈ headF 10, toC (MvQ i k) * (toC (jacQ k j) * coeff x j) -
          2 * toC (mvQ i) * (starRingEnd ℂ (toC (vbarQ j)) * coeff x j) := fun j => by
      rw [defQ, toC_csub, toC_csub, toC_csum, ← (sum_headF_eq_list 10), toC_cscale, toC_cmul,
          toC_cconj,
        sub_mul, sub_mul, Finset.sum_mul]
      congr 1
      · congr 1
        · split_ifs
          · rw [toC_one, one_mul]
          · rw [toC_zero, zero_mul]
        · exact Finset.sum_congr rfl fun k _ => by rw [toC_cmul, mul_assoc]
      · push_cast
        ring
    have hJ : ∑ k ∈ headF 10, toC (MvQ i k) *
        coeff ((finMatrixCLM (headF 10) fun k j => toC (jacQ k j) : X →L[ℂ] X) x) k =
        ∑ j ∈ headF 10, ∑ k ∈ headF 10, toC (MvQ i k) * (toC (jacQ k j) * coeff x j) :=
      (Finset.sum_congr rfl fun k hk => by
        rw [coeff_finMatrixCLM, ite_eq_left hk, Finset.mul_sum]).trans Finset.sum_comm
    rw [Finset.sum_congr rfl fun j _ => hD j, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, ite_eq_left hi, hJ, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  · rw [ite_eq_right hi, ite_eq_right hi, ite_eq_right hi, mvQ_eq_zero hi, toC_zero, mul_zero,
      sub_zero, sub_zero]

theorem norm_defect_le (hR0 : 0 ≤ REQ) (hC0 : 0 ≤ CEQ) (hs0 : 0 ≤ z11Q)
    (hrow : ∀ i ∈ (idx 10), defRowQ i ≤ REQ) (hcol : ∀ j ∈ (idx 10), defColQ j ≤ CEQ)
    (hsq : REQ * CEQ ≤ z11Q ^ 2) (x : X) (hx : x ∈ realSub polyWeight_neg) :
    ‖headProj (𝕜 := ℂ) (headF 10) x - MvOp (eigenHeadJac polyRowBound duffEigen.toEigenRaw qbarX x)
        -
      (2 * pairing one_le_polyWeight vbarX (headProj (𝕜 := ℂ) (headF 10) x)) • mvX‖ ≤
      (z11Q : ℝ) * ‖x‖ := by
  rw [defect_eq x hx]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_defOp_le_of hR0 hC0 hs0 hrow hcol hsq) (norm_nonneg x))

/-- The defect row on all of `X`: `b(ψ, J x) + 2 c b(v̄, P x) = b(ψ_E, x)`. -/
theorem pairing_defect_row_eq (x : X) :
    pairing one_le_polyWeight psiX (eigenHeadJac polyRowBound duffEigen.toEigenRaw qbarX x) +
      2 * (cQ : ℝ) * pairing one_le_polyWeight vbarX (headProj (𝕜 := ℂ) (headF 10) x) =
    pairing one_le_polyWeight psiEX x := by
  rw [eigenHeadJac_qbarX_eq, pairing_finMatrixCLM, ← pairing_headProj_comm, headProj_vbarX,
    psiEX_eq, map_add, add_apply, map_smul, smul_apply,
    smul_eq_mul]

theorem abs_pairing_defect_row_le (hB0 : 0 ≤ z21Q) (hB : psiESqQ ≤ z21Q ^ 2) (x : X) :
    |pairing one_le_polyWeight psiX (eigenHeadJac polyRowBound duffEigen.toEigenRaw qbarX x) +
      2 * (cQ : ℝ) * pairing one_le_polyWeight vbarX (headProj (𝕜 := ℂ) (headF 10) x)| ≤
      (z21Q : ℝ) * ‖x‖ := by
  rw [pairing_defect_row_eq]
  exact (abs_pairing_le one_le_polyWeight psiEX x).trans
    (mul_le_mul_of_nonneg_right (norm_psiEX_le hB0 hB) (norm_nonneg x))

theorem duff_Z0_le :
    ‖ContinuousLinearMap.id ℝ (↥(realSub polyWeight_neg) × ℝ) -
      eigenB0 polyWeight_neg one_le_polyWeight polyRowBound duffEigen qbarX qbarX_mem_realSub
          vbarR‖ ≤
      (Z0eQ : ℝ) := by
  obtain ⟨hrow, hcol, hsq, hR0, hC0, hz0, hpsiE, hz21, hMvv, hMvv0, hess, hZ⟩ := checks_Z0
  refine (norm_id_sub_eigenB0_le polyWeight_neg one_le_polyWeight polyRowBound duffEigen qbarX
    qbarX_mem_realSub vbarR (z₁₁ := (z11Q : ℝ)) (z₂₁ := (z21Q : ℝ))
    (fun x hx => norm_defect_le hR0 hC0 hz0 hrow hcol hsq x hx)
    (fun x _ => abs_pairing_defect_row_le hz21 hpsiE x)).trans ?_
  have hMvvX : ‖duffEigen.Mv (vbarR : X)‖ ≤ (nMvvQ : ℝ) := norm_MvOp_vbarX_le hMvv0 hMvv
  have hessX : |1 + pairing one_le_polyWeight duffEigen.ψ (vbarR : X)| ≤ (essQ : ℝ) := by
    change |1 + pairing one_le_polyWeight psiX vbarX| ≤ _
    rw [pairing_psiX_vbarX]
    rw [qabs_eq] at hess
    exact_mod_cast hess
  have hZ' : max ((z11Q : ℝ) + nMvvQ) ((z21Q : ℝ) + essQ) ≤ (Z0eQ : ℝ) := by exact_mod_cast hZ
  exact (max_le_max (add_le_add le_rfl hMvvX) (add_le_add le_rfl hessX)).trans hZ'

end Z0

/-! ### `Z₁` -/

section Z1

/-- The tail term (`hT`): `‖T_t L_β‖ ≤ t ‖β‖ ≤ t · 103/10`. -/
theorem norm_tail_term_duffEigen_le (ht0 : 0 ≤ tQ) :
    ‖diagCLM (tailSymbol (↑duffEigen.S : Set ℤ) fun n => duffEigen.μ n - (duffEigen.lbar : ℂ))
        duffEigen.hr ∘L symbolAction₀ (p := 2) polyModerate Polynomial.Certificate.β‖ ≤
      (TeQ : ℝ) := by
  refine (norm_tail_term_le_of_bound polyModerate Polynomial.Certificate.β _ duffEigen.hr
    norm_tailSymbol_duffEigen_le (Rat.cast_nonneg.2 ht0)).trans ?_
  rw [mul_one, TeQ, Rat.cast_mul]
  exact mul_le_mul_of_nonneg_left Polynomial.Certificate.norm_beta (Rat.cast_nonneg.2 ht0)

/-- The scalar-row leakage through `abs_pairing_leak_le` (`hleak`, `ℓ_rows`). -/
theorem abs_pairing_leak_duffEigen_le (hR0 : 0 ≤ RLQ) (hC0 : 0 ≤ CLQ) (hs0 : 0 ≤ sLQ)
    (hrow : ∀ i ∈ (idx 10), leakRowQ i ≤ RLQ) (hcol : ∀ k ∈ (leakColsQ 10 7), leakColQ k ≤ CLQ)
    (hsq : RLQ * CLQ ≤ sLQ ^ 2) (hpr0 : 0 ≤ nPsiRowsQ) (hpr : psiRowsSqQ ≤ nPsiRowsQ ^ 2)
    (x : X) :
    |pairing one_le_polyWeight psiX
        (headProj (𝕜 := ℂ) (headF 10)
          (convCLM polyRowBound qbarX (tailProj (𝕜 := ℂ) (headF 10) x)))| ≤
      ((nPsiRowsQ * sLQ : ℚ) : ℝ) * ‖x‖ := by
  refine (abs_pairing_leak_le one_le_polyWeight polyRowBound (S := headF 10) (B := headF 7)
    coeff_qbarX_eq_zero psiX (norm_leakBlock_le_of hR0 hC0 hs0 hrow hcol hsq) x).trans ?_
  rw [Rat.cast_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (norm_psiRows_le hpr0 hpr)
    (Rat.cast_nonneg.2 hs0)) (norm_nonneg x)

theorem duff_Z1_le :
    ‖eigenB0 polyWeight_neg one_le_polyWeight polyRowBound duffEigen qbarX qbarX_mem_realSub vbarR -
      quadDeriv (LG polyWeight_neg one_le_polyWeight polyRowBound duffEigen)
        (BilG polyWeight_neg one_le_polyWeight duffEigen) ybar‖ ≤ (Z1eQ : ℝ) := by
  obtain ⟨hHrow, hHcol, hHsq, hRH0, hCH0, hHe0, hLrow, hLcol, hLsq, hRL0, hCL0, hsL0, hpr, hpr0,
    hzc, hzc2, hzc0, ht0, hrow, hcol, hsq, hR0, hC0, hs0, hpsi, hpsi0, hZ⟩ := checks_Z1
  refine (norm_eigenB0_sub_quadDeriv_le polyWeight_neg one_le_polyWeight polyRowBound duffEigen
    qbarX qbarX_mem_realSub vbarR headProj_vbarR polyModerate Polynomial.Certificate.β
    symbolAction₀_β_eq_neg_convCLM_qbarX (H := (HeQ : ℝ)) (T := (TeQ : ℝ))
    (ℓ := ((nPsiRowsQ * sLQ : ℚ) : ℝ)) (norm_head_term_MvOp_le_of hRH0 hCH0 hHe0 hHrow hHcol hHsq)
    (norm_tail_term_duffEigen_le ht0)
    (fun x _ => abs_pairing_leak_duffEigen_le hRL0 hCL0 hsL0 hLrow hLcol hLsq hpr0 hpr x)
    (norm_MvOp_le_of hR0 hC0 hs0 hrow hcol hsq) norm_tailSymbol_duffEigen_le
    (norm_psiX_le hpsi0 hpsi) norm_potential_sub_qbarX_le).trans ?_
  have hmax : max (√((HeQ : ℝ) ^ 2 + (TeQ : ℝ) ^ 2)) ((nPsiRowsQ * sLQ : ℚ) : ℝ) ≤ (zcQ : ℝ) :=
    max_le (Real.sqrt_le_iff.2 ⟨Rat.cast_nonneg.2 hzc0, by exact_mod_cast hzc⟩)
      (by exact_mod_cast hzc2)
  rw [KcQ] at hZ
  have hZ' : (zcQ : ℝ) + max (max (sMQ : ℝ) (tQ : ℝ)) (spsiQ : ℝ) * (10 * (rhoqQ : ℝ)) ≤
      (Z1eQ : ℝ) := by exact_mod_cast hZ
  exact (add_le_add hmax le_rfl).trans hZ'

end Z1

/-! ### `Z₂` and the radii inequality -/

section Z2

theorem duff_Z2_le :
    ‖quadComp (ContinuousLinearMap.id ℝ (↥(realSub polyWeight_neg) × ℝ))
        (BilG polyWeight_neg one_le_polyWeight duffEigen) +
      (quadComp (ContinuousLinearMap.id ℝ (↥(realSub polyWeight_neg) × ℝ))
        (BilG polyWeight_neg one_le_polyWeight duffEigen)).flip‖ ≤ (Z2eQ : ℝ) := by
  obtain ⟨hrow, hcol, hsq, hR0, hC0, hs0, hmv, hmv0, hpsi, hpsi0, hZ⟩ := checks_Z2
  refine (norm_quadComp_BilG_add_flip_le polyWeight_neg one_le_polyWeight duffEigen
    (norm_MvOp_le_of hR0 hC0 hs0 hrow hcol hsq) norm_tailSymbol_duffEigen_le (norm_mvX_le hmv0 hmv)
    (norm_psiX_le hpsi0 hpsi)).trans ?_
  have hc : |duffEigen.c| = ((qabs cQ : ℚ) : ℝ) := by
    rw [qabs_eq, Rat.cast_abs]
    rfl
  rw [hc]
  exact_mod_cast hZ

theorem duff_radii_neg :
    generalRadiiPolynomial (Y0eQ : ℝ) (Z0eQ : ℝ) (Z1eQ : ℝ) (fun _ => (Z2eQ : ℝ)) (r0Q : ℝ) < 0 :=
        by
  simp only [generalRadiiPolynomial]
  exact_mod_cast checks_radii.2.1

theorem duff_Z0_lt_one : (Z0eQ : ℝ) < 1 := by exact_mod_cast checks_radii.2.2

end Z2

end Bounds

section EigenpairTheorem

open FourierDuffing.Polynomial.Eigenpair.Numbers

/-! ### Border injectivity at the Duffing data (non-vacuity) -/

/-- `borderInj` at the Duffing data, from `Z₀ < 1` (nonzero `Mv`, `mv`, `ψ`, nontrivial `J̄`). -/
theorem duffEigen_borderInj : borderInj polyWeight_neg one_le_polyWeight duffEigen :=
  borderInj_of_eigenB0 polyWeight_neg one_le_polyWeight polyRowBound duffEigen qbarX
    qbarX_mem_realSub headProj_vbarR (duff_Z0_le.trans_lt duff_Z0_lt_one)

/-! ### The raw form of (E1) -/

/-- The potential of the Duffing data, `q = −2 u*` (a real multiple of the certified zero). -/
theorem duffEigen_q : duffEigen.q = (-2 : ℝ) • Certificate.xPoly := rfl

/-- (E1) at `q = −2 u*` in the raw form `μ_n v_n − 2 (u* ⋆ v)_n − λ v_n = 0`. -/
theorem duff_E1_iff (y : ↥(realSub polyWeight_neg) × ℝ) :
    (∀ n, duffEigen.μ n * coeff (y.1 : X) n + coeff (convCLM polyRowBound duffEigen.q (y.1 : X)) n -
      (y.2 : ℂ) * coeff (y.1 : X) n = 0) ↔
    ∀ n, duffing (1/10) 4 n * coeff (y.1 : X) n -
      2 * (coeff Certificate.xPoly ⋆ᵣ₊ coeff (y.1 : X)) n - (y.2 : ℂ) * coeff (y.1 : X) n = 0 :=
  forall_congr' fun n => by
    rw [duffEigen_q, ContinuousLinearMap.map_smul_of_tower, smul_apply,
      coeff_real_smul, coeff_convCLM, duffEigen_μ, Complex.ofReal_neg, Complex.ofReal_ofNat,
      neg_mul, ← sub_eq_add_neg]

/-! ### The end theorem -/

/-- **The eigenpair endpoint.** The right eigenpair `(v, λ)` of the Duffing linearization at `u* =
xPoly`
exists in the ball of radius `1/20` around `(v̄, λ̄)`, solves (E1) and (E2), the real derivative of
the bounded preconditioned map is invertible there, and it is unique in the closed ball. -/
theorem duffing_eigenpair :
    ∃ y ∈ Metric.ball ybar (1 / 20 : ℝ),
      ((∀ n : ℤ, duffing (1/10) 4 n * coeff (y.1 : X) n
          - 2 * (coeff Certificate.xPoly ⋆ᵣ₊ coeff (y.1 : X)) n - (y.2 : ℂ) * coeff (y.1 : X) n =
              0) ∧
        pairing one_le_polyWeight (y.1 : X) (y.1 : X) = 1) ∧
      (ContinuousLinearMap.restrictScalars ℝ
        (quadDeriv (LG polyWeight_neg one_le_polyWeight polyRowBound duffEigen)
          (BilG polyWeight_neg one_le_polyWeight duffEigen) y)).IsInvertible ∧
      ∀ z ∈ Metric.closedBall ybar (1 / 20 : ℝ),
        ((∀ n : ℤ, duffing (1/10) 4 n * coeff (z.1 : X) n
            - 2 * (coeff Certificate.xPoly ⋆ᵣ₊ coeff (z.1 : X)) n - (z.2 : ℂ) * coeff (z.1 : X) n =
                0) ∧
          pairing one_le_polyWeight (z.1 : X) (z.1 : X) = 1) → z = y := by
  have h20 : ((r0Q : ℚ) : ℝ) = 1 / 20 := by rw [r0Q]; norm_num
  obtain ⟨y, hy, hG, hinv, huniq⟩ := existsUnique_eigenpair polyWeight_neg one_le_polyWeight
    polyRowBound duffEigen
    (B₀ := eigenB0 polyWeight_neg one_le_polyWeight polyRowBound duffEigen qbarX qbarX_mem_realSub
      vbarR)
    (by norm_num : (0 : ℝ) < 1 / 20) duff_Y0_le duff_Z0_le duff_Z1_le duff_Z2_le
    (h20 ▸ duff_radii_neg)
  have hE := (eigenMap_eq_zero_iff polyWeight_neg one_le_polyWeight polyRowBound duffEigen
    (duffing_ne_ofReal lbar_lt) headProj_mvX duffEigen_borderInj y).1 hG
  refine ⟨y, hy, ⟨(duff_E1_iff y).1 hE.1, hE.2⟩, hinv, fun z hz hzE => huniq z hz ?_⟩
  exact eigenMap_eq_zero_of_eigen polyWeight_neg one_le_polyWeight polyRowBound duffEigen
    (duffing_ne_ofReal lbar_lt) z ((duff_E1_iff z).2 hzE.1) hzE.2

/-! ### The enclosure and non-vacuity -/

/-- **The enclosure.** The certified eigenvalue is real by type and lies in
`(λ̄ − 1/20, λ̄ + 1/20) ⊂ (4.145, 4.246)`; the eigenvector is nonzero (from (E2)). -/
theorem duffing_eigenpair_enclosure :
    ∃ y ∈ Metric.ball ybar (1 / 20 : ℝ),
      ((∀ n : ℤ, duffing (1/10) 4 n * coeff (y.1 : X) n
          - 2 * (coeff Certificate.xPoly ⋆ᵣ₊ coeff (y.1 : X)) n - (y.2 : ℂ) * coeff (y.1 : X) n =
              0) ∧
        pairing one_le_polyWeight (y.1 : X) (y.1 : X) = 1) ∧
      |y.2 - (lbarQ : ℝ)| < 1 / 20 ∧ 4 < y.2 ∧ (y.1 : X) ≠ 0 := by
  obtain ⟨y, hy, hE, -⟩ := duffing_eigenpair
  have hd : dist y.2 (lbarQ : ℝ) < 1 / 20 :=
    (le_max_right (dist y.1 ybar.1) _).trans_lt
      (Prod.dist_eq.symm.trans_lt (Metric.mem_ball.1 hy))
  rw [Real.dist_eq] at hd
  have h4 : (4 : ℝ) + 1 / 20 < (lbarQ : ℝ) := by rw [lbarQ]; norm_num
  refine ⟨y, hy, hE, hd, by linarith [(abs_lt.1 hd).1], fun h0 => ?_⟩
  have h2 := hE.2
  rw [h0, map_zero] at h2
  exact zero_ne_one h2

end EigenpairTheorem

end FourierDuffing.Polynomial.Eigenpair

end
