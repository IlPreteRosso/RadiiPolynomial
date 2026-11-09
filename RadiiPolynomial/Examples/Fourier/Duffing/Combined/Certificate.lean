import RadiiPolynomial.Examples.Fourier.Duffing.Combined.Algebra
import RadiiPolynomial.Examples.Fourier.Duffing.Combined.Numbers
import RadiiPolynomial.Examples.Fourier.Duffing.Certificate
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Compatibility.ProductConvolution

/-!
# Book §10.1 Helmholtz–Duffing on the combined carrier: the certificate

The original Duffing data (`u'' + u'/10 + 4u − u² = cos t`, forcing `1/2` at `±1`, centre `ā`
and head matrix `M` on `|n| ≤ 10`) on the combined carrier `X = ℓ²_m(ℤ; ℂ)`,
`m_n = (6/5)^{|n|} (1 + |n|)²`. The certificate is independent of the geometric existence
theorem and of the polynomial-carrier zero: only the carrier-free rational bridges of
`Examples/Fourier/Duffing/Certificate.lean` are reused, and the construction is that of
`Polynomial/Certificate.lean` with the polynomial weight replaced by the combined one.

The quadratic map is `G(x) = M (Λ_H x − x ⋆ x − g) + Q x − T (x ⋆ x + g)` with the bounded
self-product `x ⋆ x = combProd x x` of the carrier (`Combined/Algebra.lean`). The curvature
`C = A ∘ combProd` is bounded on the same operator through the bounded product to `ℓ^∞_m`: the
inclusion `ι` of `combProd` is `Bilateral.prodCLM combModerate_raw` (`incl_convCLM_eq_prodCLM`,
norm at most `1`), and `A = A_Y ∘ ι` with `A_Y = M H_S + T∞ : ℓ^∞_m → X`, whose head/tail split
gives `‖A_Y‖ ≤ √(UsqQ + t2Q)`; so the curvature norm is at most `2 √(UsqQ + t2Q) ≤ Z₂ = 42`
(`Numbers.CurvCheck`). The coherence of the product with the ℓ¹ symbol action
(`convCLM_eq_symbolAction₀`) turns the derivative at the centre into the tail-defect operator of
`Operators/TailDefect.lean` for `Z₁`. One application of `quadratic_radii_theorem_local` gives a
unique zero of `G` in the closed ball of radius `3/10000`; the finite-head injectivity of `M`
transfers it to the unique zero `xC` of the raw Fourier map `rawF` in that ball.
-/

open scoped ENNReal NNReal DiscreteConvolution
open RadiiPolynomial RadiiPolynomial.WeightedLp
open RadiiPolynomial.Fourier.IkData RadiiPolynomial.Fourier.Duffing FourierDuffing.Numbers
open FourierDuffing.Certificate (control_hN duffing_eq_toC coeff_forcing_eq ν₆₅)
open FourierDuffing.Polynomial (conv_apply polyWeight)
open RadiiPolynomial.Certification.Fourier.Quadratic (QuadFourierLeafQ toC toC_zero toC_cmul toC_csub
  toC_cscale toC_cinv norm_le_reim sq_norm_toC toC_csum cast_qsum qsum_append sum_eq_list mem_idx
  nodup_idx2 nodup_leakColsQ nodup_leakRowsQ sum_headF_eq_list mem_leakCols_iff leakCols_eq
  leakRows_eq mem_support_iff idx idx2 leakColsQ reim)

noncomputable section

namespace FourierDuffing.Combined.Certificate

abbrev E := WeightedScalar ℂ combWeight
abbrev S : Finset ℤ := headF 10
abbrev Band : Finset ℤ := headF 7
abbrev P : X →L[ℂ] X := headProj (𝕜 := ℂ) S
abbrev Q : X →L[ℂ] X := tailProj (𝕜 := ℂ) S
abbrev μ : ℤ → ℂ := duffing (1 / 10) 4

lemma weight_cast (n : ℤ) : combWeight n = (Numbers.wQ n : ℝ) := by
  have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  simp only [combWeight, Numbers.wQ, polyWeight, Rat.cast_mul, Rat.cast_pow, Rat.cast_add,
    Rat.cast_one, Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat]
  rw [habs]

def head (v : ℤ → ℂ) : X := ∑ n ∈ S, single n (v n)
@[simp] lemma coeff_head (v : ℤ → ℂ) (n : ℤ) : coeff (head v) n = if n ∈ S then v n else 0 :=
  coeff_sum_single S v n

def abar : X := head (fun n => toC (leaf.abarQ n))
def g : X := head (fun n => toC (forcQ n))
lemma abar_supp : ∀ n ∉ S, coeff abar n = 0 := fun n hn => by simp [abar, coeff_head, hn]
lemma coeff_abar (n : ℤ) : coeff abar n = toC (leaf.abarQ n) := by
  rw [abar, coeff_head]
  by_cases hn : n ∈ S
  · simp [hn]
  · simp [hn, leaf.abarQ_eq_zero hn, toC_zero]
lemma hg : ∀ n ∉ S, coeff g n = 0 := fun n hn => by simp [g, coeff_head, hn]
lemma coeff_g (n : ℤ) : coeff g n = toC (forcQ n) := by
  rw [g, coeff_head]
  by_cases hn : n ∈ S
  · simp [hn]
  · have hn' := mt Finset.mem_Icc.mpr hn
    have h1 : n ≠ 1 := by intro h; subst n; norm_num at hn'
    have h2 : n ≠ -1 := by intro h; subst n; norm_num at hn'
    simp [hn, forcQ, h1, h2, toC_zero]
private lemma μ_cast (n : ℤ) : μ n = toC (leaf.muQ n) := duffing_eq_toC n
lemma μ_tail_ne : ∀ n ∉ S, μ n ≠ 0 := duffing_ne_zero control_hN
lemma tail_bound (n : ℤ) : ‖tailSymbol (S : Set ℤ) μ n‖ ≤ (Polynomial.Numbers.tailQ : ℝ) := by
  have h := norm_tailSymbol_duffing_le (c₁ := (1 / 10 : ℝ)) control_hN n
  have hlo : (117 : ℝ) ≤ ‖μ (11 : ℤ)‖ := by
    have h0 := Complex.abs_re_le_norm (μ (11 : ℤ))
    norm_num [μ, duffing] at h0 ⊢
    exact h0
  exact h.trans (by
    change ‖μ (11 : ℤ)‖⁻¹ ≤ _
    norm_num [Polynomial.Numbers.tailQ]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 117) hlo)
lemma tail_bdd : BddAbove (Set.range fun n => ‖tailSymbol (S : Set ℤ) μ n‖) :=
  ⟨(Polynomial.Numbers.tailQ : ℝ), by rintro _ ⟨n, rfl⟩; exact tail_bound n⟩

def MC (i j : ℤ) : ℂ := toC (leaf.MQ i j)
def M : X →L[ℂ] X := finMatrixCLM S MC
def T : X →L[ℂ] X := diagCLM (tailSymbol (S : Set ℤ) μ) tail_bdd
def A : X →L[ℂ] X := M + T
lemma hPM : P ∘L M = M := headProj_comp_finMatrixCLM _ _
lemma hMP : M ∘L P = M := finMatrixCLM_comp_headProj _ _
lemma matrix_M (i j : ℤ) : matrixOf M i j = toC (leaf.MQ i j) := by
  rw [M, matrixOf_finMatrixCLM]
  split_ifs with h
  · rfl
  · rw [leaf.MQ_eq_zero h, toC_zero]
lemma coeff_T (x : X) (n : ℤ) : coeff (T x) n = tailSymbol (S : Set ℤ) μ n * coeff x n :=
  coeff_diagCLM _ _ _ _

def β : lpOneAlg ℤ E := ofRaw (fun n => 2 * coeff abar n)
  (summable_of_ne_finset_zero (s := S) fun n hn => by
    simp [abar_supp n hn])
@[simp] lemma raw_β : rawSymbol β = fun n => 2 * coeff abar n := rawSymbol_ofRaw _ _
def LB : X →L[ℂ] X := symbolAction₀ (p := 2) combModerate β
lemma band_beta : ∀ n ∉ Band, rawSymbol β n = 0 := fun n hn => by
  change 2 * coeff abar n = 0
  rw [coeff_abar]
  by_cases hs : n ∈ idx 10
  · have h7 : 7 < |n| := lt_abs.mpr (by rw [Finset.mem_Icc] at hn; omega)
    rw [FourierDuffing.Numbers.checks.2.1 n hs h7, toC_zero, mul_zero]
  · rw [leaf.abarQ_eq_zero (fun h => hs (mem_idx.mpr (Finset.mem_Icc.mp h))), toC_zero, mul_zero]

/-- The derivative at the centre through the coherence of the product with the symbol action:
`2 ā ⋆ h = L_β h`, `β = 2ā`. -/
lemma two_combProd (h : X) : (2 : ℂ) • combProd abar h = LB h := by
  have hb : rawSymbol β = coeff ((2 : ℂ) • abar) := by
    funext n
    simp only [raw_β, coeff_smul, Pi.smul_apply, smul_eq_mul]
  have heq := convCLM_eq_symbolAction₀ combRowBound combModerate hb h
  simpa only [map_smul, smul_apply, LB] using heq

def L : X →L[ℂ] X := M ∘L headDiag S μ + Q
def C : X →L[ℂ] X →L[ℂ] X := (ContinuousLinearMap.compL ℂ X X X A).comp combProd
def G : X → X := quadMap (-A g) L (-C)
def DG : X →L[ℂ] X := L - (2 : ℂ) • C abar
lemma C_apply (x y : X) : C x y = A (combProd x y) := rfl
lemma G_apply (x : X) : G x = M (headDiag S μ x - combProd x x - g) + Q x - T (combProd x x + g) := by
  simp only [G, quadMap, C_apply, L, A, add_apply, neg_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sub]
  abel
lemma DG_eq_quadDeriv : DG = quadDeriv L (-C) abar := by
  apply ContinuousLinearMap.ext; intro h
  simp only [DG, quadDeriv, sub_apply, add_apply, neg_apply, smul_apply, C_apply,
    ContinuousLinearMap.flip_apply, two_smul]
  rw [convCLM_comm combRowBound h abar]
  abel
lemma two_C : (2 : ℂ) • C abar = M ∘L P ∘L LB + T ∘L LB := by
  apply ContinuousLinearMap.ext; intro h
  simp only [smul_apply, C_apply]
  rw [← map_smul, two_combProd]
  simp only [A, add_apply, ContinuousLinearMap.comp_apply]
  rw [← DFunLike.congr_fun hMP (LB h)]
  rfl
lemma DG_sub_B0 : DG - blockMap S μ LB M = -tailDefect combModerate β S M
    (tailSymbol (S : Set ℤ) μ) tail_bdd := by
  apply ContinuousLinearMap.ext; intro h
  simp only [DG, two_C, L, blockMap, headBlock, tailDefect, tailProj_eq_id_sub_headProj, T,
    sub_apply, add_apply, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_sub, P, Q, LB]
  abel

/-! Rational matrix bridges. The formulas are independent of the carrier norm;
only `weighted_le_reim` below reads the combined weight. -/
lemma weighted_le_reim (z : ℚ × ℚ) (i j : ℤ) :
    ‖toC z‖ * combWeight i / combWeight j ≤
      ((reim z * Numbers.wQ i / Numbers.wQ j : ℚ) : ℝ) := by
  rw [Rat.cast_div, Rat.cast_mul, ← weight_cast, ← weight_cast]
  apply div_le_div_of_nonneg_right _ (PosWeight.weight_pos (w := combWeight) j).le
  exact mul_le_mul_of_nonneg_right (norm_le_reim z) (PosWeight.weight_pos (w := combWeight) i).le
lemma matrix_Kh (i j : ℤ) (hi : i ∈ S) (hj : j ∈ S) :
    matrixOf (headBlock S μ LB) i j = toC (leaf.DFQ i j) := by
  rw [headBlock, matrixOf_sub, headDiag, matrixOf_diagCLM, LB,
    matrixOf_headProj_symbolAction_headProj, ite_eq_left (show i ∈ S ∧ j ∈ S from ⟨hi, hj⟩),
    QuadFourierLeafQ.DFQ, toC_csub, toC_cscale]
  simp only [raw_β, coeff_abar, Set.indicator_apply, Finset.mem_coe]
  by_cases h : i = j
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left hi, μ_cast]
    push_cast; ring
  · rw [ite_eq_right h, ite_eq_right h, toC_zero]
    push_cast; ring
lemma matrix_defect (i j : ℤ) (hi : i ∈ S) (hj : j ∈ S) :
    matrixOf (P - M ∘L headBlock S μ LB) i j = toC (leaf.EQ i j) := by
  have hK : ∀ x, ∀ n ∉ S, coeff (headBlock S μ LB x) n = 0 := fun x n hn => by
    rw [← headProj_comp_headBlock S μ LB, ContinuousLinearMap.comp_apply, coeff_headProj, ite_eq_right hn]
  rw [matrixOf_sub, matrixOf_headProj, matrixOf_comp_of_support M _ hK,
    QuadFourierLeafQ.EQ, toC_csub, toC_csum, ← sum_headF_eq_list]
  congr 1
  · by_cases h : i = j
    · rw [ite_eq_left ⟨h, hi⟩, ite_eq_left h]
      exact Complex.ext (by simp [toC]) (by simp [toC])
    · rw [ite_eq_right (fun h' => h h'.1), ite_eq_right h, toC_zero]
  · exact Finset.sum_congr rfl fun n hn => by rw [matrix_M, matrix_Kh n j hn hj, toC_cmul]
lemma composedLeak_eq (i k : ℤ) :
    composedLeakKernel M β S Band i k = toC (leaf.KMQ i k) := by
  rw [composedLeakKernel, QuadFourierLeafQ.KMQ, toC_csum, leakRows_eq (show 7 ≤ 10 by norm_num),
    List.sum_toFinset _ (nodup_leakRowsQ (show 7 ≤ 10 by norm_num))]
  refine congrArg List.sum (List.map_congr_left fun n _ => ?_)
  rw [matrix_M, toC_cmul, toC_cscale]
  simp only [raw_β, coeff_abar]
  push_cast; ring
lemma norm_beta : ‖β‖ ≤ (Numbers.betaQ : ℝ) := by
  have hnum : (Numbers.betaBoundQ : ℝ) ≤ (Numbers.betaQ : ℝ) := by
    exact_mod_cast Numbers.check_beta
  refine le_trans ?_ hnum
  rw [norm_symbol_eq, tsum_eq_sum (s := S) fun n hn => by
    simp only [raw_β, abar_supp n hn, mul_zero, norm_zero, zero_mul],
    Numbers.betaBoundQ, Numbers.betaBoundW, cast_qsum, ← sum_headF_eq_list]
  refine Finset.sum_le_sum fun n _ => ?_
  change ‖2 * coeff abar n‖ * combWeight n ≤ _
  rw [coeff_abar, norm_mul, Complex.norm_two, weight_cast]
  push_cast
  have hw : (0 : ℝ) ≤ (Numbers.wQ n : ℝ) := by
    exact_mod_cast (Numbers.wQ_pos n).le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_le_reim _) (by norm_num)) hw
lemma Z0_le : ‖P - M ∘L headBlock S μ LB‖ ≤ (Numbers.Z0Q : ℝ) := by
  rcases Numbers.check_Z0 with ⟨hrow, hcol, hsq⟩
  refine (norm_le_sqrt_of_block _ (by simpa only [id_sub_blockMap] using
    headProj_comp_id_sub_blockMap_comp_headProj S μ LB M hPM) (R := (Numbers.RzQ : ℝ)) (C := (Numbers.CzQ : ℝ))
    (by norm_num [Numbers.RzQ]) (by norm_num [Numbers.CzQ]) ?_ ?_).trans ?_
  · intro i hi
    refine le_trans ?_ (show (Numbers.zRowQ i : ℝ) ≤ (Numbers.RzQ : ℝ) by
      exact_mod_cast hrow i (mem_idx.mpr (Finset.mem_Icc.mp hi)))
    rw [Numbers.zRowQ, Numbers.zRowW, cast_qsum, ← sum_headF_eq_list]
    apply Finset.sum_le_sum; intro j hj
    rw [schurEntry, matrix_defect i j hi hj, WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight]
    exact weighted_le_reim _ i j
  · intro j hj
    refine le_trans ?_ (show (Numbers.zColQ j : ℝ) ≤ (Numbers.CzQ : ℝ) by
      exact_mod_cast hcol j (mem_idx.mpr (Finset.mem_Icc.mp hj)))
    rw [Numbers.zColQ, Numbers.zColW, cast_qsum, ← sum_headF_eq_list]
    apply Finset.sum_le_sum; intro i hi
    rw [schurEntry, matrix_defect i j hi hj, WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight]
    exact weighted_le_reim _ i j
  · refine (Real.sqrt_le_sqrt (show (Numbers.RzQ : ℝ) * Numbers.CzQ ≤ (Numbers.Z0Q : ℝ)^2 by
      exact_mod_cast hsq)).trans_eq (Real.sqrt_sq (by norm_num [Numbers.Z0Q]))
lemma H_le : ‖M ∘L P ∘L LB ∘L Q‖ ≤ (Numbers.HQ : ℝ) := by
  rcases Numbers.check_H with ⟨hrow, hcol, hsq⟩
  refine (norm_head_term_le_composed combModerate β S Band M band_beta hPM
    (Rm := (Numbers.RhQ : ℝ)) (Cm := (Numbers.ChQ : ℝ))
    (by norm_num [Numbers.RhQ]) (by norm_num [Numbers.ChQ]) ?_ ?_).trans ?_
  · intro i hi
    refine le_trans ?_ (show (Numbers.hRowQ i : ℝ) ≤ (Numbers.RhQ : ℝ) by
      exact_mod_cast hrow i (mem_idx.mpr (Finset.mem_Icc.mp hi)))
    rw [Numbers.hRowQ, Numbers.hRowW, cast_qsum, ← List.sum_toFinset _ (nodup_leakColsQ 10 7), ← leakCols_eq]
    apply Finset.sum_le_sum; intro k hk
    rw [composedLeak_eq, WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight]
    exact weighted_le_reim _ i k
  · intro k hk
    refine le_trans ?_ (show (Numbers.hColQ k : ℝ) ≤ (Numbers.ChQ : ℝ) by
      exact_mod_cast hcol k ((mem_leakCols_iff 10 7 k).mp hk))
    rw [Numbers.hColQ, Numbers.hColW, cast_qsum, ← sum_headF_eq_list]
    apply Finset.sum_le_sum; intro i hi
    rw [composedLeak_eq, WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight]
    exact weighted_le_reim _ i k
  · refine (Real.sqrt_le_sqrt (show (Numbers.RhQ : ℝ) * Numbers.ChQ ≤ (Numbers.HQ : ℝ)^2 by
      exact_mod_cast hsq)).trans_eq (Real.sqrt_sq (by norm_num [Numbers.HQ]))
/-! The curvature through the bounded product to `ℓ^∞_m`, on the same operator `C`. -/

lemma hsS : Summable fun n => ‖tailSymbol (S : Set ℤ) μ n‖ ^ 2 :=
  summable_sq_tailSymbol_duffing_headF control_hN

/-- `A_Y ∘ ι = A` (`H_S ι = P`, `T∞ ι = T` and `M P = M`). -/
lemma AY_comp_incl : Bilateral.AY S M (S : Set ℤ) μ hsS ∘L Bilateral.incl = A := by
  rw [Bilateral.AY, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_assoc,
    Bilateral.headReal_comp_incl, Bilateral.tailInf_comp_incl, hMP]
  rfl

/-- `C x y = A_Y (prodCLM x y)`: the curvature read through the bounded product to `ℓ^∞_m`
(`ι (combProd x y) = prodCLM x y`, `A_Y ι = A`). -/
lemma C_apply_eq_AY (x y : X) :
    C x y = Bilateral.AY S M (S : Set ℤ) μ hsS (Bilateral.prodCLM combModerate_raw x y) := by
  rw [C_apply, ← Bilateral.incl_convCLM_eq_prodCLM combRowBound combModerate_raw,
    ← ContinuousLinearMap.comp_apply (Bilateral.AY S M (S : Set ℤ) μ hsS), AY_comp_incl]

/-- The `U_row` of `M` against `Numbers.aRowQ` (amplitude ratios `m_i / m_j`). -/
lemma urow_le_aRowQ (i : ℤ) :
    ∑ j ∈ S, ‖matrixOf M i j‖ * combWeight i / combWeight j ≤ (Numbers.aRowQ i : ℝ) := by
  rw [Numbers.aRowQ, Numbers.aRowW, cast_qsum, ← sum_headF_eq_list]
  exact Finset.sum_le_sum fun j _ => by rw [matrix_M]; exact weighted_le_reim _ i j

/-- `‖A_Y‖ ≤ √(UsqQ + t2Q)`: the `U_row` head bound and the tail sum bound. -/
lemma norm_AY_le : ‖Bilateral.AY S M (S : Set ℤ) μ hsS‖ ≤
    √((Numbers.UsqQ : ℝ) + Polynomial.Numbers.t2Q) := by
  refine (Bilateral.norm_AY_le_sqrt_tsum S M μ hsS hPM).trans
    (Real.sqrt_le_sqrt (add_le_add ?_ ?_))
  · refine ((pow_le_pow_left₀ (norm_nonneg _) (Bilateral.norm_comp_headReal_le_urow S M hPM)
      2).trans_eq (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _))).trans ?_
    rw [Numbers.UsqQ, Numbers.UsqW, cast_qsum, ← sum_headF_eq_list]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Rat.cast_pow]
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => div_nonneg
      (mul_nonneg (norm_nonneg _) (PosWeight.weight_nonneg (w := combWeight) i))
      (PosWeight.weight_nonneg (w := combWeight) j)) (urow_le_aRowQ i) 2
  · refine (tsum_sq_tailSymbol_duffing_le (c₁ := 1 / 10) control_hN (by norm_num)).trans_eq ?_
    norm_num [Polynomial.Numbers.t2Q]

/-- **The curvature bound** `‖C‖ ≤ √(UsqQ + t2Q)` (`‖prodCLM‖ ≤ 1`). -/
lemma norm_C : ‖C‖ ≤ √((Numbers.UsqQ : ℝ) + Polynomial.Numbers.t2Q) := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (Real.sqrt_nonneg _) fun x y => ?_
  rw [C_apply_eq_AY, mul_assoc]
  exact ((Bilateral.AY S M (S : Set ℤ) μ hsS).le_opNorm _).trans
    (mul_le_mul norm_AY_le (Bilateral.norm_prodCLM_apply_le combModerate_raw x y)
      (norm_nonneg _) (Real.sqrt_nonneg _))

lemma Z2_le : ‖quadComp (ContinuousLinearMap.id ℂ X) (-C) +
    (quadComp (ContinuousLinearMap.id ℂ X) (-C)).flip‖ ≤ (Numbers.Z2Q : ℝ) := by
  refine (norm_quadComp_add_flip_le _ _).trans ?_
  have hid : quadComp (ContinuousLinearMap.id ℂ X) (-C) = -C := by ext x y; rfl
  rw [hid, ContinuousLinearMap.opNorm_neg]
  have hcurv : 4 * ((Numbers.UsqQ : ℝ) + Polynomial.Numbers.t2Q) ≤ (Numbers.Z2Q : ℝ) ^ 2 := by
    exact_mod_cast (show 4 * (Numbers.UsqQ + Polynomial.Numbers.t2Q) ≤ Numbers.Z2Q ^ 2 from
      Numbers.check_curv)
  have h4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
  have h2 := Real.sqrt_le_sqrt hcurv
  rw [Real.sqrt_mul (by norm_num), h4, Real.sqrt_sq (by norm_num [Numbers.Z2Q])] at h2
  exact (mul_le_mul_of_nonneg_left norm_C zero_le_two).trans h2
lemma Z1_le : ‖blockMap S μ LB M - quadDeriv L (-C) abar‖ ≤ (Numbers.Z1Q : ℝ) := by
  rw [← DG_eq_quadDeriv, norm_sub_rev, DG_sub_B0, norm_neg]
  refine (norm_tailDefect_le combModerate β S M (tailSymbol (S : Set ℤ) μ) tail_bdd hPM
    (fun n hn => tailSymbol_of_mem (Finset.mem_coe.mpr hn)) H_le
    (norm_tail_term_le_of_bound combModerate β _ _ tail_bound (by norm_num [Polynomial.Numbers.tailQ]))).trans ?_
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num [Numbers.Z1Q]
  · have hn := norm_beta
    have hcheck : (Numbers.HQ : ℝ)^2 + ((Polynomial.Numbers.tailQ : ℝ)*(Numbers.betaQ : ℝ))^2 ≤
        (Numbers.Z1Q : ℝ)^2 := by exact_mod_cast Numbers.check_Z1
    norm_num [Numbers.HQ, Polynomial.Numbers.tailQ, Numbers.betaQ, Numbers.Z1Q] at hn hcheck ⊢
    nlinarith [norm_nonneg β]

/-! The bounded quadratic map is related to the raw, potentially unbounded, residual. -/
def rawF (x : X) (n : ℤ) : ℂ := μ n * coeff x n - (coeff x ⋆ᵣ₊ coeff x) n - coeff g n
def rawA (v : ℤ → ℂ) (n : ℤ) : ℂ := coeff (M (head v)) n + tailSymbol (S : Set ℤ) μ n * v n
lemma coeff_G (x : X) : coeff (G x) = rawA (rawF x) := by
  have hhead : head (rawF x) = headDiag S μ x - P (combProd x x) - g := by
    apply ext_coeff; funext n
    simp only [coeff_head, coeff_sub, Pi.sub_apply, coeff_headDiag,
      coeff_headProj, coeff_convCLM]
    by_cases hn : n ∈ S
    · simp [hn, rawF]
    · simp [hn, hg n hn]
  have hM : M (headDiag S μ x - P (combProd x x) - g) = M (headDiag S μ x - combProd x x - g) := by
    have hp := DFunLike.congr_fun hMP (combProd x x)
    simp only [ContinuousLinearMap.comp_apply] at hp
    simp only [map_sub]
    rw [hp]
  funext n
  rw [rawA, hhead, hM, G_apply]
  simp only [coeff_add, coeff_sub, Pi.add_apply, Pi.sub_apply, coeff_tailProj, coeff_T,
    coeff_convCLM]
  by_cases hn : n ∈ S
  · rw [tailSymbol_of_mem (Finset.mem_coe.mpr hn)]
    simp [hn]
  · rw [ite_eq_right hn, tailSymbol_of_notMem (fun h => hn (Finset.mem_coe.mp h)), rawF, hg n hn]
    have hz : coeff (M (headDiag S μ x - combProd x x - g)) n = 0 := by
      rw [M, coeff_finMatrixCLM, ite_eq_right hn]
    rw [hz]
    simp only [sub_zero, mul_sub, ← mul_assoc, inv_mul_cancel₀ (μ_tail_ne n hn), one_mul]
    ring
lemma conv_finite (x : X) (n : ℤ) :
    (coeff abar ⋆ᵣ₊ coeff x) n = ∑ k ∈ S, coeff abar k * coeff x (n-k) := by
  rw [conv_apply]
  exact tsum_eq_sum (fun k hk => by rw [abar_supp k hk, zero_mul])
lemma conv_abar (n : ℤ) : (coeff abar ⋆ᵣ₊ coeff abar) n = toC (leaf.convQ n) := by
  rw [conv_finite, QuadFourierLeafQ.convQ, toC_csum, sum_headF_eq_list]
  exact congrArg List.sum (List.map_congr_left fun k _ => by rw [coeff_abar, coeff_abar, toC_cmul])
lemma rawF_abar (n : ℤ) : rawF abar n = toC (leaf.residQ n) := by
  rw [rawF, μ_cast, coeff_abar, conv_abar, coeff_g, QuadFourierLeafQ.residQ, toC_csub, toC_csub,
    toC_cmul]
lemma coeff_G_abar (n : ℤ) : coeff (G abar) n = toC (leaf.GQ n) := by
  rw [congrFun (coeff_G abar) n, rawA, M, coeff_finMatrixCLM, QuadFourierLeafQ.GQ]
  by_cases hn : n ∈ S
  · rw [ite_eq_left hn, ite_eq_left (Finset.mem_Icc.mp hn),
      tailSymbol_of_mem (Finset.mem_coe.mpr hn),
      zero_mul, add_zero, toC_csum, ← sum_headF_eq_list]
    exact Finset.sum_congr rfl fun j hj => by
      rw [coeff_head, ite_eq_left hj, rawF_abar, MC, toC_cmul]
  · rw [ite_eq_right hn, ite_eq_right (fun h => hn (Finset.mem_Icc.mpr h)),
      tailSymbol_of_notMem (fun h => hn (Finset.mem_coe.mp h)), zero_add,
      rawF_abar, μ_cast, toC_cmul, toC_cinv]
lemma G_abar_support (n : ℤ) (hn : n ∉ S ∪ S.image₂ (·+·) S) : coeff (G abar) n = 0 := by
  have hnS : n ∉ S := fun h => hn (Finset.mem_union_left _ h)
  have hc : (coeff abar ⋆ᵣ₊ coeff abar) n = 0 := by
    rw [conv_finite]
    apply Finset.sum_eq_zero; intro j hj
    rw [abar_supp (n-j) (fun h => hn (Finset.mem_union_right _
      (Finset.mem_image₂.mpr ⟨j, hj, n-j, h, by omega⟩))), mul_zero]
  rw [congrFun (coeff_G abar) n, rawA, M, coeff_finMatrixCLM, ite_eq_right hnS, rawF,
    abar_supp n hnS, hc, hg n hnS]
  simp
lemma Y0_le : ‖G abar‖ ≤ (Numbers.Y0Q : ℝ) := by
  have heq : ‖G abar‖^2 = (Numbers.ySquaredQ : ℝ) := by
    rw [norm_sq_eq_tsum, tsum_eq_sum (s := S ∪ S.image₂ (·+·) S) (fun n hn => by
      rw [norm_apply_eq, G_abar_support n hn, norm_zero, zero_mul, sq, zero_mul]),
      sum_eq_list (nodup_idx2 10) (mem_support_iff 10)]
    rw [Numbers.ySquaredQ, Numbers.ySquaredW, Numbers.yPartW, Numbers.yPartW, Numbers.yPartW,
      ← qsum_append, ← qsum_append, ← Polynomial.Numbers.idx2_eq_chunks, cast_qsum]
    congr 1
    apply List.map_congr_left; intro n hn
    rw [norm_apply_eq, WeightedScalar.fiberTrivialization_weight, mul_pow, coeff_G_abar,
      sq_norm_toC, Numbers.yTermW, weight_cast]
    push_cast
    rfl
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num [Numbers.Y0Q]) two_ne_zero).mp
  rw [heq]
  exact_mod_cast Numbers.check_Y0
lemma radii_neg : generalRadiiPolynomial (Numbers.Y0Q : ℝ) (Numbers.Z0Q : ℝ)
    (Numbers.Z1Q : ℝ) (fun _ => (Numbers.Z2Q : ℝ)) (Numbers.radiusQ : ℝ) < 0 := by
  simp only [generalRadiiPolynomial]
  exact_mod_cast Numbers.check_radii.2
lemma existsUnique_G : ∃! x ∈ Metric.closedBall abar (Numbers.radiusQ : ℝ), G x = 0 := by
  exact quadratic_radii_theorem_local
    (c := -A g) (L := L) (B := -C) (xBar := abar)
    (A := ContinuousLinearMap.id ℂ X) (A_dagger := blockMap S μ LB M)
    (by exact_mod_cast Numbers.check_radii.1) (by simpa [G] using Y0_le)
    (by simpa only [ContinuousLinearMap.id_comp, id_sub_blockMap] using Z0_le)
    (by simpa only [ContinuousLinearMap.id_comp] using Z1_le) Z2_le radii_neg (fun _ _ h => h)

/-! Raw zero transfer through the finite-head solver service of `WeightedLp/Operators/FiniteBlock`. -/

/-- Local coefficient existence and uniqueness on the combined carrier, from the product
certificate; the geometric existence theorem does not enter. The unique zero of `G`
(`existsUnique_G`) is transported to the raw zero by `existsUnique_zero_transport` at the identity
isometry, along `eq_zero_iff_of_coeff_eq_headSolve` (solver identity `coeff_G`, head realization
`head`, `d = tailSymbol ↑S μ`) with head injectivity from `eq_zero_of_headProj_eq_of_norm_lt_one`
(`‖P − M K_H‖ < 1`, `P K_H = K_H`). -/
theorem existsUnique_raw : ∃! x ∈ Metric.closedBall abar (Numbers.radiusQ : ℝ), rawF x = 0 := by
  have hinj := eq_zero_of_headProj_eq_of_norm_lt_one S
    (by rw [← ContinuousLinearMap.comp_assoc, headProj_comp_headBlock])
    (Z0_le.trans_lt (by norm_num [Numbers.Z0Q]))
  refine existsUnique_zero_transport (IsometryEquiv.refl X) (fun x => ?_) existsUnique_G
  exact (eq_zero_iff_of_coeff_eq_headSolve S M (tailSymbol (S : Set ℤ) μ) coeff_head
    (by rw [← ContinuousLinearMap.comp_assoc, hPM]) hinj
    (fun k hk => tailSymbol_of_mem (Finset.mem_coe.2 hk))
    (fun k hk => by
      rw [tailSymbol_of_notMem (fun h => hk (Finset.mem_coe.1 h))]
      exact inv_ne_zero (μ_tail_ne k hk))
    (fun x k => congrFun (coeff_G x) k) x).symm

/-- **The combined-carrier zero**: the unique zero of the raw Fourier map in the closed ball of
radius `3/10000` around `ā`, certified on `X` without the geometric existence theorem. -/
def xC : X := existsUnique_raw.exists.choose

theorem xC_ball : xC ∈ Metric.closedBall abar (Numbers.radiusQ : ℝ) :=
  existsUnique_raw.exists.choose_spec.1

theorem xC_zero : rawF xC = 0 := existsUnique_raw.exists.choose_spec.2

theorem unique_eq_xC (x : X) (hx : x ∈ Metric.closedBall abar (Numbers.radiusQ : ℝ))
    (hF : rawF x = 0) : x = xC :=
  existsUnique_raw.unique ⟨hx, hF⟩ existsUnique_raw.exists.choose_spec

/-- The forcing coefficients are those of the geometric forcing `b_{±1} = 1/2`. -/
theorem coeff_g_eq_forcing (n : ℤ) : coeff g n = coeff (forcing (ν := ν₆₅) 1) n :=
  (coeff_g n).trans (coeff_forcing_eq n).symm

end FourierDuffing.Combined.Certificate
