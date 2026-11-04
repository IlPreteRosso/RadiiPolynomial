import RadiiPolynomial.Examples.Fourier.Duffing.Polynomial.Algebra
import RadiiPolynomial.Examples.Fourier.Duffing.Polynomial.Numbers
import RadiiPolynomial.Examples.Fourier.Duffing.Certificate

/-!
# Book §10.1 Helmholtz–Duffing on the polynomial carrier: the certificate

The original Duffing data (`u'' + u'/10 + 4u − u² = cos t`, forcing `1/2` at `±1`, centre `ā`
and head matrix `M` on `|n| ≤ 10`) on the physical polynomial carrier `X = ℓ²_m(ℤ; ℂ)`,
`m_n = (1 + |n|)²`. The certificate is independent of the geometric existence theorem: only the
carrier-free rational bridges of `Examples/Fourier/Duffing/Certificate.lean` are reused.

The quadratic map is `G(x) = M (Λ_H x − x ⋆ x − g) + Q x − T (x ⋆ x + g)` with the bounded
self-product `x ⋆ x = polyProd x x` of the carrier (`Polynomial/Algebra.lean`); the product
bound `κ = 10` enters `Z₂ = 2κ‖A‖`, and the coherence of the product with the ℓ¹ symbol action
(`convCLM_eq_symbolAction₀`) turns the derivative at the centre into the tail-defect operator of
`Operators/TailDefect.lean` for `Z₁`. One application of `quadratic_radii_theorem_local` gives a
unique zero of `G` in the closed ball of radius `1/10000`; the finite-head injectivity of `M`
transfers it to the unique zero `xPoly` of the raw Fourier map `rawF` in that ball.
-/

open scoped ENNReal NNReal DiscreteConvolution
open RadiiPolynomial RadiiPolynomial.WeightedLp
open RadiiPolynomial.Fourier.IkData RadiiPolynomial.Fourier.Duffing FourierDuffing.Numbers
open FourierDuffing.Certificate (control_hN duffing_eq_toC)
open RadiiPolynomial.Certification.Fourier.Quadratic (QuadFourierLeafQ toC toC_zero toC_cmul toC_csub
  toC_cscale toC_cinv norm_le_reim sq_norm_toC toC_csum cast_qsum qsum_append sum_eq_list mem_idx
  nodup_idx2 nodup_leakColsQ nodup_leakRowsQ sum_headF_eq_list mem_leakCols_iff leakCols_eq
  leakRows_eq mem_support_iff idx idx2 leakColsQ reim)

noncomputable section

namespace FourierDuffing.Polynomial.Certificate

abbrev E := WeightedScalar ℂ polyWeight
abbrev S : Finset ℤ := headF 10
abbrev Band : Finset ℤ := headF 7
abbrev P : X →L[ℂ] X := headProj (𝕜 := ℂ) S
abbrev Q : X →L[ℂ] X := tailProj (𝕜 := ℂ) S
abbrev μ : ℤ → ℂ := duffing (1 / 10) 4

lemma weight_cast (n : ℤ) : polyWeight n = (Numbers.weightQ n : ℝ) := by
  have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  simp only [polyWeight, Numbers.weightQ, Rat.cast_pow, Rat.cast_add, Rat.cast_one,
    Rat.cast_natCast]
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
lemma tail_bound (n : ℤ) : ‖tailSymbol (S : Set ℤ) μ n‖ ≤ (Numbers.tailQ : ℝ) := by
  have h := norm_tailSymbol_duffing_le (c₁ := (1 / 10 : ℝ)) control_hN n
  have hlo : (117 : ℝ) ≤ ‖μ (11 : ℤ)‖ := by
    have h0 := Complex.abs_re_le_norm (μ (11 : ℤ))
    norm_num [μ, duffing] at h0 ⊢
    exact h0
  exact h.trans (by
    change ‖μ (11 : ℤ)‖⁻¹ ≤ _
    norm_num [Numbers.tailQ]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 117) hlo)
lemma tail_bdd : BddAbove (Set.range fun n => ‖tailSymbol (S : Set ℤ) μ n‖) :=
  ⟨(Numbers.tailQ : ℝ), by rintro _ ⟨n, rfl⟩; exact tail_bound n⟩

def MC (i j : ℤ) : ℂ := toC (leaf.MQ i j)
def M : X →L[ℂ] X := finMatrixCLM S MC
def T : X →L[ℂ] X := diagCLM (tailSymbol (S : Set ℤ) μ) tail_bdd
def A : X →L[ℂ] X := M + T
lemma hPM : P ∘L M = M := headProj_comp_finMatrixCLM _ _
lemma hMP : M ∘L P = M := by
  apply ContinuousLinearMap.ext; intro x; apply ext_coeff; funext n
  simp only [M, ContinuousLinearMap.comp_apply, coeff_finMatrixCLM]
  split_ifs with hn
  · apply Finset.sum_congr rfl; intro j hj
    rw [coeff_headProj, ite_eq_left hj]
  · rfl
lemma matrix_M (i j : ℤ) : matrixOf M i j = toC (leaf.MQ i j) := by
  rw [M, matrixOf_finMatrixCLM]
  split_ifs with h
  · rfl
  · rw [leaf.MQ_eq_zero h, toC_zero]
lemma coeff_T (x : X) (n : ℤ) : coeff (T x) n = tailSymbol (S : Set ℤ) μ n * coeff x n :=
  coeff_diagCLM _ _ _ _
lemma norm_T : ‖T‖ ≤ (Numbers.tailQ : ℝ) :=
  norm_diagCLM_le _ _ tail_bound (by norm_num [Numbers.tailQ])

def β : lpOneAlg ℤ E := ofRaw (fun n => 2 * coeff abar n)
  (summable_of_ne_finset_zero (s := S) fun n hn => by
    simp [abar_supp n hn])
@[simp] lemma raw_β : rawSymbol β = fun n => 2 * coeff abar n := rawSymbol_ofRaw _ _
def LB : X →L[ℂ] X := symbolAction₀ (p := 2) polyModerate β
lemma band_beta : ∀ n ∉ Band, rawSymbol β n = 0 := fun n hn => by
  change 2 * coeff abar n = 0
  rw [coeff_abar]
  by_cases hs : n ∈ idx 10
  · have h7 : 7 < |n| := lt_abs.mpr (by rw [Finset.mem_Icc] at hn; omega)
    rw [checks.2.1 n hs h7, toC_zero, mul_zero]
  · rw [leaf.abarQ_eq_zero (fun h => hs (mem_idx.mpr (Finset.mem_Icc.mp h))), toC_zero, mul_zero]

/-- The derivative at the centre through the coherence of the product with the symbol action:
`2 ā ⋆ h = L_β h`, `β = 2ā`. -/
lemma two_polyProd (h : X) : (2 : ℂ) • polyProd abar h = LB h := by
  have hb : rawSymbol β = coeff ((2 : ℂ) • abar) := by
    funext n
    simp only [raw_β, coeff_smul, Pi.smul_apply, smul_eq_mul]
  have heq := convCLM_eq_symbolAction₀ polyRowBound polyModerate hb h
  simpa only [map_smul, smul_apply, LB] using heq

def hsSym (n : ℤ) : ℂ := if n ∈ S then μ n else 0
lemma hsSym_bdd : BddAbove (Set.range fun n => ‖hsSym n‖) := by
  refine ⟨∑ j ∈ S, ‖μ j‖, ?_⟩
  rintro _ ⟨n, rfl⟩
  change ‖if n ∈ S then μ n else 0‖ ≤ _
  split_ifs with hn
  · exact Finset.single_le_sum (fun j _ => norm_nonneg _) hn
  · simpa using (Finset.sum_nonneg (s := S) (fun j _ => norm_nonneg (μ j)))
def LamH : X →L[ℂ] X := diagCLM hsSym hsSym_bdd
lemma coeff_LamH (x : X) (n : ℤ) : coeff (LamH x) n = if n ∈ S then μ n * coeff x n else 0 := by
  simp only [LamH, coeff_diagCLM, hsSym]
  split_ifs <;> simp

def Kh : X →L[ℂ] X := LamH - P ∘L LB ∘L P
def B0 : X →L[ℂ] X := M ∘L Kh + Q
def L : X →L[ℂ] X := M ∘L LamH + Q
def C : X →L[ℂ] X →L[ℂ] X := (ContinuousLinearMap.compL ℂ X X X A).comp polyProd
def G : X → X := quadMap (-A g) L (-C)
def DG : X →L[ℂ] X := L - (2 : ℂ) • C abar
lemma C_apply (x y : X) : C x y = A (polyProd x y) := rfl
lemma G_apply (x : X) : G x = M (LamH x - polyProd x x - g) + Q x - T (polyProd x x + g) := by
  simp only [G, quadMap, C_apply, L, A, add_apply, neg_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sub]
  abel
lemma DG_eq_quadDeriv : DG = quadDeriv L (-C) abar := by
  apply ContinuousLinearMap.ext; intro h
  simp only [DG, quadDeriv, sub_apply, add_apply, neg_apply, smul_apply, C_apply,
    ContinuousLinearMap.flip_apply, two_smul]
  rw [convCLM_comm polyRowBound h abar]
  abel
lemma two_C : (2 : ℂ) • C abar = M ∘L P ∘L LB + T ∘L LB := by
  apply ContinuousLinearMap.ext; intro h
  simp only [smul_apply, C_apply]
  rw [← map_smul, two_polyProd]
  simp only [A, add_apply, ContinuousLinearMap.comp_apply]
  rw [← DFunLike.congr_fun hMP (LB h)]
  rfl
lemma DG_sub_B0 : DG - B0 = -tailDefect polyModerate β S M
    (tailSymbol (S : Set ℤ) μ) tail_bdd := by
  apply ContinuousLinearMap.ext; intro h
  simp only [DG, two_C, L, B0, Kh, tailDefect, tailProj_eq_id_sub_headProj, T,
    sub_apply, add_apply, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_sub, P, Q, LB]
  abel
private lemma one_sub_B0 : ContinuousLinearMap.id ℂ X - B0 = P - M ∘L Kh :=
  id_sub_add_tailProj S _
lemma P_LamH : P ∘L LamH = LamH := by
  apply ContinuousLinearMap.ext; intro x; apply ext_coeff; funext n
  rw [ContinuousLinearMap.comp_apply, coeff_headProj, coeff_LamH]
  split_ifs <;> rfl
lemma LamH_P : LamH ∘L P = LamH := by
  apply ContinuousLinearMap.ext; intro x; apply ext_coeff; funext n
  simp only [ContinuousLinearMap.comp_apply, coeff_LamH, coeff_headProj]
  split_ifs <;> simp
lemma P_Kh : P ∘L Kh = Kh := by
  rw [Kh, ContinuousLinearMap.comp_sub, P_LamH, ← ContinuousLinearMap.comp_assoc,
    headProj_comp_headProj]
lemma Kh_P : Kh ∘L P = Kh := by
  rw [Kh, ContinuousLinearMap.sub_comp, LamH_P, ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_assoc, headProj_comp_headProj]
lemma block_defect : P ∘L (P - M ∘L Kh) ∘L P = P - M ∘L Kh := by
  rw [ContinuousLinearMap.sub_comp, headProj_comp_headProj, ContinuousLinearMap.comp_assoc,
    Kh_P, ContinuousLinearMap.comp_sub, headProj_comp_headProj,
    ← ContinuousLinearMap.comp_assoc, hPM]

/-! Rational matrix bridges. The formulas are independent of the carrier norm;
only `weighted_le_reim` below changes from the original geometric certificate. -/
lemma weighted_le_reim (z : ℚ × ℚ) (i j : ℤ) :
    ‖toC z‖ * polyWeight i / polyWeight j ≤
      ((reim z * Numbers.weightQ i / Numbers.weightQ j : ℚ) : ℝ) := by
  rw [Rat.cast_div, Rat.cast_mul, ← weight_cast, ← weight_cast]
  apply div_le_div_of_nonneg_right _ (show 0 ≤ polyWeight j from sq_nonneg _)
  exact mul_le_mul_of_nonneg_right (norm_le_reim z) (show 0 ≤ polyWeight i from sq_nonneg _)
lemma matrix_Kh (i j : ℤ) (hi : i ∈ S) (hj : j ∈ S) :
    matrixOf Kh i j = toC (leaf.DFQ i j) := by
  rw [Kh, matrixOf_sub, LamH, matrixOf_diagCLM, LB,
    matrixOf_headProj_symbolAction_headProj, ite_eq_left (show i ∈ S ∧ j ∈ S from ⟨hi, hj⟩),
    QuadFourierLeafQ.DFQ, toC_csub, toC_cscale]
  simp only [raw_β, coeff_abar, hsSym]
  by_cases h : i = j
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left hi, μ_cast]
    push_cast; ring
  · rw [ite_eq_right h, ite_eq_right h, toC_zero]
    push_cast; ring
lemma matrix_defect (i j : ℤ) (hi : i ∈ S) (hj : j ∈ S) :
    matrixOf (P - M ∘L Kh) i j = toC (leaf.EQ i j) := by
  have hK : ∀ x, ∀ n ∉ S, coeff (Kh x) n = 0 := fun x n hn => by
    rw [← P_Kh, ContinuousLinearMap.comp_apply, coeff_headProj, ite_eq_right hn]
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
    Numbers.betaBoundQ, cast_qsum, ← sum_headF_eq_list]
  refine Finset.sum_le_sum fun n _ => ?_
  change ‖2 * coeff abar n‖ * polyWeight n ≤ _
  rw [coeff_abar, norm_mul, Complex.norm_two, weight_cast]
  push_cast
  have hw : (0 : ℝ) ≤ (Numbers.weightQ n : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ Numbers.weightQ n from sq_nonneg _)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_le_reim _) (by norm_num)) hw
lemma Z0_le : ‖P - M ∘L Kh‖ ≤ (Numbers.Z0Q : ℝ) := by
  rcases Numbers.check_Z0 with ⟨hrow, hcol, hsq⟩
  refine (norm_le_sqrt_of_block _ block_defect (R := (Numbers.RzQ : ℝ)) (C := (Numbers.CzQ : ℝ))
    (by norm_num [Numbers.RzQ]) (by norm_num [Numbers.CzQ]) ?_ ?_).trans ?_
  · intro i hi
    refine le_trans ?_ (show (Numbers.zRowQ i : ℝ) ≤ (Numbers.RzQ : ℝ) by
      exact_mod_cast hrow i (mem_idx.mpr (Finset.mem_Icc.mp hi)))
    rw [Numbers.zRowQ, cast_qsum, ← sum_headF_eq_list]
    apply Finset.sum_le_sum; intro j hj
    rw [schurEntry, matrix_defect i j hi hj, WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight]
    exact weighted_le_reim _ i j
  · intro j hj
    refine le_trans ?_ (show (Numbers.zColQ j : ℝ) ≤ (Numbers.CzQ : ℝ) by
      exact_mod_cast hcol j (mem_idx.mpr (Finset.mem_Icc.mp hj)))
    rw [Numbers.zColQ, cast_qsum, ← sum_headF_eq_list]
    apply Finset.sum_le_sum; intro i hi
    rw [schurEntry, matrix_defect i j hi hj, WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight]
    exact weighted_le_reim _ i j
  · refine (Real.sqrt_le_sqrt (show (Numbers.RzQ : ℝ) * Numbers.CzQ ≤ (Numbers.Z0Q : ℝ)^2 by
      exact_mod_cast hsq)).trans_eq (Real.sqrt_sq (by norm_num [Numbers.Z0Q]))
lemma H_le : ‖M ∘L P ∘L LB ∘L Q‖ ≤ (Numbers.HQ : ℝ) := by
  rcases Numbers.check_H with ⟨hrow, hcol, hsq⟩
  refine (norm_head_term_le_composed polyModerate β S Band M band_beta hPM
    (Rm := (Numbers.RhQ : ℝ)) (Cm := (Numbers.ChQ : ℝ))
    (by norm_num [Numbers.RhQ]) (by norm_num [Numbers.ChQ]) ?_ ?_).trans ?_
  · intro i hi
    refine le_trans ?_ (show (Numbers.hRowQ i : ℝ) ≤ (Numbers.RhQ : ℝ) by
      exact_mod_cast hrow i (mem_idx.mpr (Finset.mem_Icc.mp hi)))
    rw [Numbers.hRowQ, cast_qsum, ← List.sum_toFinset _ (nodup_leakColsQ 10 7), ← leakCols_eq]
    apply Finset.sum_le_sum; intro k hk
    rw [composedLeak_eq, WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight]
    exact weighted_le_reim _ i k
  · intro k hk
    refine le_trans ?_ (show (Numbers.hColQ k : ℝ) ≤ (Numbers.ChQ : ℝ) by
      exact_mod_cast hcol k ((mem_leakCols_iff 10 7 k).mp hk))
    rw [Numbers.hColQ, cast_qsum, ← sum_headF_eq_list]
    apply Finset.sum_le_sum; intro i hi
    rw [composedLeak_eq, WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight]
    exact weighted_le_reim _ i k
  · refine (Real.sqrt_le_sqrt (show (Numbers.RhQ : ℝ) * Numbers.ChQ ≤ (Numbers.HQ : ℝ)^2 by
      exact_mod_cast hsq)).trans_eq (Real.sqrt_sq (by norm_num [Numbers.HQ]))
lemma norm_M : ‖M‖ ≤ (Numbers.AQ : ℝ) := by
  rcases Numbers.check_A with ⟨hrow, hcol, hsq, _⟩
  have hblock : P ∘L M ∘L P = M := by rw [hMP, hPM]
  refine (norm_le_sqrt_of_block _ hblock (R := (Numbers.RaQ : ℝ)) (C := (Numbers.CaQ : ℝ))
    (by norm_num [Numbers.RaQ]) (by norm_num [Numbers.CaQ]) ?_ ?_).trans ?_
  · intro i hi
    refine le_trans ?_ (show (Numbers.aRowQ i : ℝ) ≤ (Numbers.RaQ : ℝ) by
      exact_mod_cast hrow i (mem_idx.mpr (Finset.mem_Icc.mp hi)))
    rw [Numbers.aRowQ, cast_qsum, ← sum_headF_eq_list]
    apply Finset.sum_le_sum; intro j hj
    rw [schurEntry, matrix_M, WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight]
    exact weighted_le_reim _ i j
  · intro j hj
    refine le_trans ?_ (show (Numbers.aColQ j : ℝ) ≤ (Numbers.CaQ : ℝ) by
      exact_mod_cast hcol j (mem_idx.mpr (Finset.mem_Icc.mp hj)))
    rw [Numbers.aColQ, cast_qsum, ← sum_headF_eq_list]
    apply Finset.sum_le_sum; intro i hi
    rw [schurEntry, matrix_M, WeightedScalar.fiberTrivialization_weight,
      WeightedScalar.fiberTrivialization_weight]
    exact weighted_le_reim _ i j
  · refine (Real.sqrt_le_sqrt (show (Numbers.RaQ : ℝ) * Numbers.CaQ ≤ (Numbers.AQ : ℝ)^2 by
      exact_mod_cast hsq)).trans_eq (Real.sqrt_sq (by norm_num [Numbers.AQ]))
lemma T_Q : T ∘L Q = T := by
  apply ContinuousLinearMap.ext; intro x; apply ext_coeff; funext n
  rw [ContinuousLinearMap.comp_apply, coeff_T, coeff_T, coeff_tailProj]
  by_cases hn : n ∈ S
  · rw [tailSymbol_of_mem (Finset.mem_coe.mpr hn)]
    simp [hn]
  · simp [hn]
lemma norm_A : ‖A‖ ≤ (Numbers.AQ : ℝ) := by
  have hT : ‖T‖ ≤ (Numbers.AQ : ℝ) := norm_T.trans (by exact_mod_cast Numbers.check_A.2.2.2)
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num [Numbers.AQ])
  intro x
  have hdis : ∀ n, coeff (M x) n = 0 ∨ coeff (T x) n = 0 := fun n => by
    by_cases hn : n ∈ S
    · exact Or.inr (by rw [coeff_T, tailSymbol_of_mem (Finset.mem_coe.mpr hn), zero_mul])
    · exact Or.inl (by rw [M, coeff_finMatrixCLM, ite_eq_right hn])
  have hdisPQ : ∀ n, coeff (P x) n = 0 ∨ coeff (Q x) n = 0 := fun n => by
    by_cases hn : n ∈ S
    · exact Or.inr (by rw [coeff_tailProj, ite_eq_left hn])
    · exact Or.inl (by rw [coeff_headProj, ite_eq_right hn])
  have hx : P x + Q x = x := by simp [Q, tailProj_eq_id_sub_headProj]
  have hsum : ‖P x‖^2 + ‖Q x‖^2 = ‖x‖^2 := by
    rw [← norm_add_sq_of_disjoint hdisPQ, hx]
  have hM : ‖M x‖ ≤ (Numbers.AQ : ℝ) * ‖P x‖ := by
    rw [← DFunLike.congr_fun hMP x]
    exact (M.le_opNorm _).trans (mul_le_mul_of_nonneg_right norm_M (norm_nonneg _))
  have hT' : ‖T x‖ ≤ (Numbers.AQ : ℝ) * ‖Q x‖ := by
    rw [← DFunLike.congr_fun T_Q x]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  apply (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (by norm_num [Numbers.AQ]) (norm_nonneg x)) two_ne_zero).mp
  rw [A, add_apply, norm_add_sq_of_disjoint hdis, mul_pow]
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) hM 2, pow_le_pow_left₀ (norm_nonneg _) hT' 2]
lemma norm_C : ‖C‖ ≤ (Numbers.AQ : ℝ) * 10 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have hcomp : ‖ContinuousLinearMap.compL ℂ X X X A‖ ≤ ‖A‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun B => ContinuousLinearMap.opNorm_comp_le A B
  exact mul_le_mul (hcomp.trans norm_A) (norm_convCLM_le polyRowBound) (norm_nonneg _)
    (by norm_num [Numbers.AQ])
lemma Z2_le : ‖quadComp (ContinuousLinearMap.id ℂ X) (-C) +
    (quadComp (ContinuousLinearMap.id ℂ X) (-C)).flip‖ ≤ (Numbers.Z2Q : ℝ) := by
  refine (norm_quadComp_add_flip_le _ _).trans ?_
  have hid : quadComp (ContinuousLinearMap.id ℂ X) (-C) = -C := by ext x y; rfl
  rw [hid, ContinuousLinearMap.opNorm_neg]
  have hnorm := norm_C
  norm_num [Numbers.Z2Q, Numbers.AQ] at hnorm ⊢
  linarith
lemma Z1_le : ‖B0 - quadDeriv L (-C) abar‖ ≤ (Numbers.Z1Q : ℝ) := by
  rw [← DG_eq_quadDeriv, norm_sub_rev, DG_sub_B0, norm_neg]
  refine (norm_tailDefect_le polyModerate β S M (tailSymbol (S : Set ℤ) μ) tail_bdd hPM
    (fun n hn => tailSymbol_of_mem (Finset.mem_coe.mpr hn)) H_le
    (norm_tail_term_le_of_bound polyModerate β _ _ tail_bound (by norm_num [Numbers.tailQ]))).trans ?_
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num [Numbers.Z1Q]
  · have hn := norm_beta
    have hcheck : (Numbers.HQ : ℝ)^2 + ((Numbers.tailQ : ℝ)*(Numbers.betaQ : ℝ))^2 ≤
        (Numbers.Z1Q : ℝ)^2 := by exact_mod_cast Numbers.check_Z1
    norm_num [Numbers.HQ, Numbers.tailQ, Numbers.betaQ, Numbers.Z1Q] at hn hcheck ⊢
    nlinarith [norm_nonneg β]

/-! The bounded quadratic map is related to the raw, potentially unbounded, residual. -/
def rawF (x : X) (n : ℤ) : ℂ := μ n * coeff x n - (coeff x ⋆ᵣ₊ coeff x) n - coeff g n
def rawA (v : ℤ → ℂ) (n : ℤ) : ℂ := coeff (M (head v)) n + tailSymbol (S : Set ℤ) μ n * v n
lemma coeff_G (x : X) : coeff (G x) = rawA (rawF x) := by
  have hhead : head (rawF x) = LamH x - P (polyProd x x) - g := by
    apply ext_coeff; funext n
    simp only [coeff_head, coeff_sub, Pi.sub_apply, coeff_LamH,
      coeff_headProj, coeff_convCLM]
    by_cases hn : n ∈ S
    · simp [hn, rawF]
    · simp [hn, hg n hn]
  have hM : M (LamH x - P (polyProd x x) - g) = M (LamH x - polyProd x x - g) := by
    have hp := DFunLike.congr_fun hMP (polyProd x x)
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
    have hz : coeff (M (LamH x - polyProd x x - g)) n = 0 := by
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
    rw [Numbers.ySquaredQ, Numbers.yPartQ, Numbers.yPartQ, Numbers.yPartQ,
      ← qsum_append, ← qsum_append, ← Numbers.idx2_eq_chunks, cast_qsum]
    congr 1
    apply List.map_congr_left; intro n hn
    rw [norm_apply_eq, WeightedScalar.fiberTrivialization_weight, mul_pow, coeff_G_abar,
      sq_norm_toC, Numbers.yTermQ, weight_cast]
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
    (A := ContinuousLinearMap.id ℂ X) (A_dagger := B0)
    (by exact_mod_cast Numbers.check_radii.1) (by simpa [G] using Y0_le)
    (by simpa [one_sub_B0] using Z0_le)
    (by simpa only [ContinuousLinearMap.id_comp] using Z1_le) Z2_le radii_neg (fun _ _ h => h)

/-! Raw zero transfer through the finite-head solver service of `WeightedLp/Operators/FiniteBlock`. -/

/-- Local coefficient existence and uniqueness on the polynomial carrier, from the product
certificate; the geometric existence theorem does not enter. The unique zero of `G`
(`existsUnique_G`) is transported to the raw zero by `existsUnique_zero_transport` at the identity
isometry, along `eq_zero_iff_of_coeff_eq_headSolve` (solver identity `coeff_G`, head realization
`head`, `d = tailSymbol ↑S μ`) with head injectivity from `eq_zero_of_headProj_eq_of_norm_lt_one`
(`‖P − M K_H‖ < 1`, `P K_H = K_H`). -/
theorem existsUnique_raw : ∃! x ∈ Metric.closedBall abar (Numbers.radiusQ : ℝ), rawF x = 0 := by
  have hinj := eq_zero_of_headProj_eq_of_norm_lt_one S
    (by rw [← ContinuousLinearMap.comp_assoc, P_Kh])
    (Z0_le.trans_lt (by norm_num [Numbers.Z0Q]))
  refine existsUnique_zero_transport (IsometryEquiv.refl X) (fun x => ?_) existsUnique_G
  exact (eq_zero_iff_of_coeff_eq_headSolve S M (tailSymbol (S : Set ℤ) μ) coeff_head
    (by rw [← ContinuousLinearMap.comp_assoc, hPM]) hinj
    (fun k hk => tailSymbol_of_mem (Finset.mem_coe.2 hk))
    (fun k hk => by
      rw [tailSymbol_of_notMem (fun h => hk (Finset.mem_coe.1 h))]
      exact inv_ne_zero (μ_tail_ne k hk))
    (fun x k => congrFun (coeff_G x) k) x).symm

/-- **The polynomial-carrier zero**: the unique zero of the raw Fourier map in the closed ball of
radius `1/10000` around `ā`, certified on `X` without the geometric existence theorem. -/
def xPoly : X := existsUnique_raw.exists.choose

theorem xPoly_ball : xPoly ∈ Metric.closedBall abar (Numbers.radiusQ : ℝ) :=
  existsUnique_raw.exists.choose_spec.1

theorem xPoly_zero : rawF xPoly = 0 := existsUnique_raw.exists.choose_spec.2

theorem unique_eq_xPoly (x : X) (hx : x ∈ Metric.closedBall abar (Numbers.radiusQ : ℝ))
    (hF : rawF x = 0) : x = xPoly :=
  existsUnique_raw.unique ⟨hx, hF⟩ existsUnique_raw.exists.choose_spec

end FourierDuffing.Polynomial.Certificate
