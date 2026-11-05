import RadiiPolynomial.Applications.Fourier.Quadratic
import RadiiPolynomial.Applications.Fourier.IkData
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.FiniteBlock

/-!
# The forced Riccati equation `u′ + u − u² = cos (2t) / 100` on `ℓ²_{6/5}`: the certificate

The quadratic Fourier family (`Applications/Fourier/Quadratic.lean`) at the first-order symbol
`μₙ = 1 + i n`, the head `F = Icc (−2) 2`, the forcing `g_{±2} = 1/200` and the diagonal head
inverse `M = diag (1_F μ⁻¹)` with centre `ā = M g`, on `X₂ ℂ ν`, `ν = 6/5`. The tail symbol is
compared with the first-order symbol data `ik` of `Applications/Fourier/IkData.lean`. The four
bounds `Y₀ = 1/1000`, `Z₀ = 1/20`, `Z₁ = 1/10`, `Z₂ = 8` satisfy the radii inequality at
`r₀ = 1/100`, so the raw Fourier map `rawF μ g a = (1 + i n) aₙ − (a ⋆ a)ₙ − gₙ` has a unique
zero in the closed ball (`raw_existsUnique`), which is conjugate-symmetric
(`raw_existsUnique_real`). Only the generic family is used: no Duffing symbol, forcing,
certificate or endpoint.
-/
open scoped ENNReal NNReal
open RadiiPolynomial RadiiPolynomial.WeightedLp
open RadiiPolynomial.WeightedLp.Bilateral RadiiPolynomial.Fourier.Quadratic
  RadiiPolynomial.Fourier.IkData
noncomputable section
namespace FourierRiccati

def ν : PosReal := ⟨6 / 5, by norm_num⟩
instance : Fact (1 ≤ (ν : ℝ)) := ⟨by change (1 : ℝ) ≤ 6 / 5; norm_num⟩
lemma coe_ν : (ν : ℝ) = 6 / 5 := rfl
def F : Finset ℤ := Finset.Icc (-2) 2
lemma F_eq : F = {-2, -1, 0, 1, 2} := by decide
lemma F_headZ : (F : Set ℤ) = headZ 2 := by
  ext n
  simp [F, headZ, abs_le]
def μ (n : ℤ) : ℂ := 1 + Complex.I * n
lemma μ_ne (n : ℤ) : μ n ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [μ] at this
lemma μ_norm_one (n : ℤ) : (1 : ℝ) ≤ ‖μ n‖ := by
  have h := Complex.abs_re_le_norm (μ n)
  simpa [μ] using h
lemma μ_norm_ik (n : ℤ) : ‖ik n‖ ≤ ‖μ n‖ := by
  have h := Complex.abs_im_le_norm (μ n)
  simpa [μ, norm_ik, Complex.norm_intCast] using h
lemma inv_norm_le (n : ℤ) : ‖(μ n)⁻¹‖ ≤ (1 : ℝ) := by
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ (μ_norm_one n)
lemma tail_norm_le (n : ℤ) : ‖tailSymbol (F : Set ℤ) μ n‖ ≤ (1 : ℝ) := by
  rw [norm_tailSymbol]
  split_ifs
  · norm_num
  · exact inv_le_one_of_one_le₀ (μ_norm_one n)
lemma tail_compare (n : ℤ) :
    ‖tailSymbol (F : Set ℤ) μ n‖ ^ 2 ≤ ‖tailSymbol (headZ 2) ik n‖ ^ 2 := by
  simp only [norm_tailSymbol]
  by_cases hn : n ∈ (F : Set ℤ)
  · have hn' : n ∈ headZ 2 := by simpa only [← F_headZ] using hn
    rw [ite_eq_left hn, ite_eq_left hn']
  · have hn' : n ∉ headZ 2 := by simpa only [← F_headZ] using hn
    rw [ite_eq_right hn, ite_eq_right hn']
    have hn0 : n ≠ 0 := by intro h; subst n; norm_num [F] at hn
    have hk : 0 < ‖ik n‖ := by rw [norm_ik]; positivity
    exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (inv_anti₀ hk (μ_norm_ik n)) 2
lemma hs : Summable fun n => ‖tailSymbol (F : Set ℤ) μ n‖ ^ 2 :=
  (summable_sq_tailSymbol_ik 2).of_nonneg_of_le (fun _ => sq_nonneg _) tail_compare
lemma tailT2 : ∑' n, ‖tailSymbol (F : Set ℤ) μ n‖ ^ 2 ≤ (1 : ℝ) := by
  have h := hs.tsum_le_tsum tail_compare (summable_sq_tailSymbol_ik 2)
  rw [(hasSum_sq_tailSymbol_ik 2).tsum_eq] at h
  exact h.trans (by nlinarith [psi1_le 2])

def d (n : ℤ) : ℂ := if n ∈ F then (μ n)⁻¹ else 0
lemma hd1 : ∀ n, ‖d n‖ ≤ 1 := by
  intro n; unfold d; split_ifs
  · exact inv_norm_le n
  · norm_num
lemma hd : BddAbove (Set.range fun n => ‖d n‖) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; exact hd1 n⟩
def M : X₂ ℂ ν →L[ℂ] X₂ ℂ ν := diagCLM d hd
lemma normM : ‖M‖ ≤ 1 := norm_diagCLM_le d hd hd1 (by norm_num)
lemma hPM : headProj (𝕜 := ℂ) F ∘L M = M := by
  apply ContinuousLinearMap.ext; intro x; apply ext_coeff; funext n
  simp only [ContinuousLinearMap.comp_apply, coeff_headProj, M, coeff_diagCLM]
  by_cases hn : n ∈ F <;> simp [d, hn]
lemma M_headDiag : M ∘L headDiag F μ = headProj (𝕜 := ℂ) F := by
  apply ContinuousLinearMap.ext; intro x; apply ext_coeff; funext n
  simp only [ContinuousLinearMap.comp_apply, M, coeff_diagCLM, coeff_headDiag, coeff_headProj]
  by_cases hn : n ∈ F
  · simp [d, hn, ← mul_assoc, inv_mul_cancel₀ (μ_ne n)]
  · simp [d, hn]

def gc (n : ℤ) : ℂ := if n = 2 ∨ n = -2 then 1 / 200 else 0
def g : X₂ ℂ ν := headOfRaw F gc
lemma hg : ∀ n ∉ F, coeff g n = 0 := fun n hn => by
  rw [g, coeff_headOfRaw, ite_eq_right hn]
lemma coeff_g (n : ℤ) : coeff g n = gc n := by
  rw [g, coeff_headOfRaw]
  by_cases hn : n ∈ F
  · simp [hn]
  · have hns : ¬(n = 2 ∨ n = -2) := by rw [F, Finset.mem_Icc] at hn; omega
    simp [hn, gc, hns]
lemma norm_g : ‖g‖ ≤ (9 / 625 : ℝ) := by
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 9 / 625) two_ne_zero).mp
  rw [norm_sq_X₂, tsum_eq_sum (s := F) (fun n hn => by simp [hg n hn])]
  norm_num [F_eq, coeff_g, gc, coe_ν]

def abar : X₂ ℂ ν := M g
lemma abar_supp : ∀ n ∉ F, coeff abar n = 0 := fun n hn => by
  simp [abar, M, coeff_diagCLM, d, hn]
lemma norm_abar : ‖abar‖ ≤ (9 / 625 : ℝ) :=
  (M.le_opNorm g).trans (by nlinarith [normM, norm_g, norm_nonneg g])
lemma coeff_abar_le (n : ℤ) : ‖coeff abar n‖ ≤ ‖gc n‖ := by
  rw [abar, M, coeff_diagCLM, coeff_g, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hd1 n)
abbrev β := betaOf F abar abar_supp
lemma normβ : ‖β‖ ≤ (18 / 625 : ℝ) := by
  rw [norm_symbol_eq, tsum_eq_sum (s := F) (fun n hn => by simp [rawSymbol_betaOf, abar_supp n hn])]
  have hb : (∑ n ∈ F, ‖rawSymbol β n‖ * (ν : ℝ) ^ n.natAbs) ≤
      ∑ n ∈ F, (2 * ‖gc n‖) * (ν : ℝ) ^ n.natAbs := by
    apply Finset.sum_le_sum; intro n hn
    simp only [β, rawSymbol_betaOf, norm_mul, Complex.norm_two]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (coeff_abar_le n) (by norm_num))
      (pow_nonneg ν.coe_pos.le _)
  refine hb.trans ?_
  norm_num [F_eq, gc, coe_ν]

private lemma normP : ‖headProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F‖ ≤ 1 :=
  norm_diagCLM_le _ (bddAbove_tailSymbol_one _) (norm_tailSymbol_one_le _) (by norm_num)
private lemma normQ : ‖tailProj (𝕜 := ℂ) (E := geomFiberZ ℂ ν) (p := 2) F‖ ≤ 1 :=
  norm_diagCLM_le _ (bddAbove_tailSymbol_one _) (norm_tailSymbol_one_le _) (by norm_num)
abbrev LB := symbolAction₀ (p := 2) Fourier.moderate_geomFiberZ β
lemma normLB : ‖LB‖ ≤ (18 / 625 : ℝ) := by
  have h := (symbolAction₀ (p := 2) Fourier.moderate_geomFiberZ).le_of_opNorm_le
    (norm_symbolAction₀_le Fourier.moderate_geomFiberZ) β
  have h' : ‖LB‖ ≤ ‖β‖ := by simpa only [one_mul] using h
  exact h'.trans normβ
lemma Z0_identity : headProj (𝕜 := ℂ) F - M ∘L headBlock F μ LB =
    M ∘L headProj (𝕜 := ℂ) F ∘L LB ∘L headProj (𝕜 := ℂ) F := by
  rw [headBlock, ContinuousLinearMap.comp_sub, M_headDiag]
  abel
private lemma head_action_bound (Q : X₂ ℂ ν →L[ℂ] X₂ ℂ ν) (hQ : ‖Q‖ ≤ 1) :
    ‖M ∘L headProj (𝕜 := ℂ) F ∘L LB ∘L Q‖ ≤ (1 / 20 : ℝ) := by
  have h1 : ‖M ∘L headProj (𝕜 := ℂ) F‖ ≤ 1 * 1 :=
    (M.opNorm_comp_le _).trans (mul_le_mul normM normP (norm_nonneg _) (by norm_num))
  have h2 : ‖(M ∘L headProj (𝕜 := ℂ) F) ∘L LB‖ ≤ (1 * 1) * (18 / 625) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul h1 normLB (norm_nonneg _) (by norm_num))
  have h3 : ‖((M ∘L headProj (𝕜 := ℂ) F) ∘L LB) ∘L Q‖ ≤ ((1 * 1) * (18 / 625)) * 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul h2 hQ (norm_nonneg _) (by norm_num))
  have h4 := h3.trans (by norm_num : ((1 * 1 : ℝ) * (18 / 625)) * 1 ≤ 1 / 20)
  simpa only [ContinuousLinearMap.comp_assoc] using h4
lemma Z0_le : ‖headProj (𝕜 := ℂ) F - M ∘L headBlock F μ LB‖ ≤ (1 / 20 : ℝ) := by
  rw [Z0_identity]
  exact head_action_bound _ normP
lemma H_le : ‖M ∘L headProj (𝕜 := ℂ) F ∘L LB ∘L tailProj (𝕜 := ℂ) F‖ ≤ (1 / 20 : ℝ) :=
  head_action_bound _ normQ
lemma U_le : ‖M ∘L headReal F‖ ≤ (3 : ℝ) := by
  refine (norm_comp_headReal_le_urow F M hPM).trans ?_
  have hrow (i : ℤ) (hi : i ∈ F) :
      (∑ j ∈ F, ‖matrixOf M i j‖ * (ν : ℝ) ^ i.natAbs / (ν : ℝ) ^ j.natAbs) = ‖d i‖ := by
    calc
      _ = ∑ j ∈ F, if i = j then ‖d i‖ else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i = j
        · subst j
          simp [M, matrixOf_diagCLM, pow_ne_zero _ ν.coe_pos.ne']
        · simp [M, matrixOf_diagCLM, hij]
      _ = ‖d i‖ := by simp [hi]
  have hsum : (∑ i ∈ F, (∑ j ∈ F, ‖matrixOf M i j‖ * (ν : ℝ) ^ i.natAbs /
      (ν : ℝ) ^ j.natAbs) ^ 2) ≤ (5 : ℝ) := by
    calc
      _ ≤ ∑ i ∈ F, (1 : ℝ) := Finset.sum_le_sum fun i hi => by
        rw [hrow i hi]
        nlinarith [hd1 i, norm_nonneg (d i)]
      _ = 5 := by norm_num [F_eq]
  exact (Real.sqrt_le_sqrt hsum).trans (by norm_num [Real.sqrt_le_iff])
lemma Z1_le : ‖DG F μ hs M abar - blockMap F μ LB M‖ ≤ (1 / 10 : ℝ) := by
  refine (norm_DG_sub_B0_le F μ hs M abar_supp hPM H_le tail_norm_le).trans ?_
  apply (Real.sqrt_le_iff).mpr
  constructor
  · norm_num
  · nlinarith [normβ, norm_nonneg β]
lemma Z2_le :
    ‖quadComp (ContinuousLinearMap.id ℂ (X₂ ℂ ν)) (-quadCLM (AY F M (F : Set ℤ) μ hs)) +
      (quadComp (ContinuousLinearMap.id ℂ (X₂ ℂ ν))
        (-quadCLM (AY F M (F : Set ℤ) μ hs))).flip‖ ≤ (8 : ℝ) := by
  refine (norm_quadComp_add_flip_le_of_bounds F μ hs M hPM U_le tailT2).trans ?_
  have h : Real.sqrt 10 ≤ 4 := by norm_num [Real.sqrt_le_iff]
  norm_num only [show (3 : ℝ) ^ 2 + 1 = 10 by norm_num]
  linarith

lemma headDiag_abar : headDiag F μ abar = g := by
  apply ext_coeff; funext n
  rw [coeff_headDiag, abar, M, coeff_diagCLM]
  by_cases hn : n ∈ F
  · simp [hn, d, ← mul_assoc, mul_inv_cancel₀ (μ_ne n)]
  · simp [hn, hg n hn]
lemma tail_abar : tailProj (𝕜 := ℂ) F abar = 0 := by
  apply ext_coeff; funext n
  rw [coeff_tailProj, coeff_zero]
  by_cases hn : n ∈ F <;> simp [hn, abar_supp n]
lemma G_abar :
    G F μ hs M g abar = -AY F M (F : Set ℤ) μ hs (prodCLM (geomSubmul ν) abar abar) := by
  rw [G, headDiag_abar, tail_abar, AY]
  simp only [map_sub, add_apply, ContinuousLinearMap.comp_apply]
  abel
lemma AY_norm : ‖AY F M (F : Set ℤ) μ hs‖ ≤ (4 : ℝ) := by
  refine (norm_AY_le_sqrt_tsum F M μ hs hPM).trans ?_
  have hsq : ‖M ∘L headReal F‖ ^ 2 + ∑' n, ‖tailSymbol (F : Set ℤ) μ n‖ ^ 2 ≤ (10 : ℝ) := by
    nlinarith [U_le, tailT2, norm_nonneg (M ∘L headReal F)]
  exact (Real.sqrt_le_sqrt hsq).trans (by norm_num [Real.sqrt_le_iff])
lemma Y0_le : ‖G F μ hs M g abar‖ ≤ (1 / 1000 : ℝ) := by
  rw [G_abar, norm_neg]
  have h1 := (AY F M (F : Set ℤ) μ hs).le_opNorm (prodCLM (geomSubmul ν) abar abar)
  have h2 := norm_prodCLM_apply_le (geomSubmul ν) abar abar
  have h3 : ‖prodCLM (geomSubmul ν) abar abar‖ ≤ (9 / 625 : ℝ) * (9 / 625) :=
    h2.trans (mul_le_mul norm_abar norm_abar (norm_nonneg _) (by norm_num))
  exact h1.trans ((mul_le_mul AY_norm h3 (norm_nonneg _) (by norm_num)).trans (by norm_num))

lemma radii_neg : generalRadiiPolynomial (1 / 1000 : ℝ) (1 / 20) (1 / 10)
    (fun _ => 8) (1 / 100) < 0 := by norm_num [generalRadiiPolynomial]

/-- Explicit coefficient meaning of the first-order equation and forcing. -/
theorem equation_semantics : (ν : ℝ) = 6 / 5 ∧
    (∀ n : ℤ, μ n = 1 + Complex.I * n) ∧
    (∀ n : ℤ, coeff g n = if n = 2 ∨ n = -2 then (1 / 200 : ℂ) else 0) :=
  ⟨coe_ν, fun _ => rfl, coeff_g⟩

/-- The generic Fourier face validates a raw coefficient zero near the candidate. -/
theorem raw_existsUnique : ∃! x ∈ Metric.closedBall abar (1 / 100 : ℝ), rawF μ g x = 0 :=
  existsUnique_rawF F μ hs M g abar_supp hPM hg (fun n _ => μ_ne n)
    (by norm_num) Y0_le Z0_le Z1_le Z2_le radii_neg

lemma μ_sym (n : ℤ) : μ (-n) = (starRingEnd ℂ) (μ n) := by
  apply Complex.ext <;> simp [μ]
lemma g_sym (n : ℤ) : coeff g (-n) = (starRingEnd ℂ) (coeff g n) := by
  rw [coeff_g, coeff_g]
  have hn : (-n = 2 ∨ -n = -2) ↔ (n = 2 ∨ n = -2) := by omega
  simp only [gc, hn]
  split_ifs <;> simp [map_ofNat]
lemma d_sym (n : ℤ) : d n = (starRingEnd ℂ) (d (-n)) := by
  have hn : (-n ∈ F) ↔ n ∈ F := by simp only [F, Finset.mem_Icc]; omega
  simp only [d, hn]
  split_ifs
  · rw [μ_sym, map_inv₀, Complex.conj_conj]
  · exact (map_zero _).symm
lemma real_abar : conjRefl abar = abar := by
  apply ext_coeff; funext n
  simp only [coeff_conjRefl, abar, M, coeff_diagCLM, map_mul]
  rw [← d_sym, g_sym, Complex.conj_conj]
/-- Conjugate-symmetric raw zero and uniqueness among all raw zeros in the coefficient ball (the
isometry `conjRefl` and the equivariance `rawF_conjRefl` at the conjugate-symmetric symbol and
forcing). -/
theorem raw_existsUnique_real :
    ∃ x ∈ Metric.closedBall abar (1 / 100 : ℝ), rawF μ g x = 0 ∧ conjRefl x = x ∧
      ∀ y ∈ Metric.closedBall abar (1 / 100 : ℝ), rawF μ g y = 0 → y = x := by
  obtain ⟨x, ⟨hx, hx0⟩, hu⟩ := raw_existsUnique
  refine ⟨x, hx, hx0, hu _ ⟨?_, funext fun n => ?_⟩, fun y hy hy0 => hu y ⟨hy, hy0⟩⟩
  · rw [← real_abar]
    exact isometry_conjRefl.mapsTo_closedBall _ _ hx
  · rw [rawF_conjRefl μ_sym g_sym, hx0]
    simp

def a : X₂ ℂ ν := raw_existsUnique_real.choose
private lemma a_spec : a ∈ Metric.closedBall abar (1 / 100 : ℝ) ∧
    rawF μ g a = 0 ∧ conjRefl a = a := by
  have h := raw_existsUnique_real.choose_spec
  exact ⟨h.1, h.2.1, h.2.2.1⟩
theorem coefficient_ball : a ∈ Metric.closedBall abar (1 / 100 : ℝ) := a_spec.1
theorem coefficient_zero : rawF μ g a = 0 := a_spec.2.1
theorem coefficient_reality : conjRefl a = a := a_spec.2.2
theorem coefficient_error (n : ℤ) :
    ‖coeff a n - coeff abar n‖ ≤ (1 / 100 : ℝ) / (ν : ℝ) ^ n.natAbs := by
  apply (le_div_iff₀ (pow_pos ν.coe_pos _)).mpr
  have hb : ‖a - abar‖ ≤ (1 / 100 : ℝ) := mem_closedBall_iff_norm.mp coefficient_ball
  have hn := norm_apply_le_norm (a - abar) n
  rw [norm_apply_X₂, coeff_sub, Pi.sub_apply] at hn
  exact hn.trans hb

end FourierRiccati
