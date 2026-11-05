import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Module
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Scalar
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Diagonal
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Geometric decay by nested contraction

The transfer lemma `fixedPt_eq_of_semiconj`: a fixed point of a map with at most one fixed point
that a contraction on a complete space semiconjugates into it comes from that space; for affine
maps `x ↦ c + T x` with `‖T‖ < 1` this is `affine_fixedPt_mem_range`. On the ℓ¹ rings
`ℓ¹_ρ = lpOneAlg ℤ (geomFiberZ 𝕜 ρ)`, the weight-lowering inclusion `l1Incl : ℓ¹_ρ →L ℓ¹_ν′`
(`ν′ ≤ ρ`), the tail operator `diagMulCLM u d = D_d ∘ L_u` and the head lift `headLift` give the
bootstrap `exists_toRealSeq_eq_of_tail_gap`: if `‖σₙ‖ ≥ c > ‖q‖` off a finite set, `q ∈ ℓ¹_ρ`,
`∑ ‖vₙ‖ < ∞` and `σₙ vₙ + (q ⋆ v)ₙ = 0`, then `v ∈ ℓ¹_ρ`. `exists_toRealSeq_eq_of_growth` reads
the gap off `‖σₙ‖ → ∞` along `cofinite`. Placement: the transfer is carrier-free, but its only
consumer is this bootstrap, and `Analysis` does not import `Core`; the inclusion, tail operator and
head lift need `WeightedLp.ofRaw` and `geomFiberZ`, which no other `WeightedL1` module imports.
-/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.Bootstrap

/-! ## The transfer lemma and its affine packaging -/

section Transfer

/-- If `f` contracts on a complete `A`, `g` has at most one fixed point, `ι` semiconjugates `f`
to `g` and `y` is fixed by `g`, then `y = ι (ContractingWith.fixedPoint f hf)`. -/
theorem fixedPt_eq_of_semiconj {A B : Type*} [MetricSpace A] [Nonempty A] [CompleteSpace A]
    {K : ℝ≥0} {f : A → A} {g : B → B} {ι : A → B} (hf : ContractingWith K f)
    (hg : (Function.fixedPoints g).Subsingleton) (hι : Function.Semiconj ι f g)
    {y : B} (hy : Function.IsFixedPt g y) : y = ι (ContractingWith.fixedPoint f hf) :=
  hg hy (hf.fixedPoint_isFixedPt.map hι)

/-- For `‖T‖ < 1`, the affine map `x ↦ c + T x` is `ContractingWith ‖T‖₊`. -/
theorem contractingWith_affine {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup A]
    [NormedSpace 𝕜 A] (c : A) {T : A →L[𝕜] A} (hT : ‖T‖ < 1) :
    ContractingWith ‖T‖₊ fun x => c + T x :=
  ⟨by rwa [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one],
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_add_left]; exact T.lipschitzWith.dist_le_mul x y⟩

/-- For `‖TA‖ < 1` on a complete `A`, `‖TB‖ < 1`, a map `ι : A → B` with
`ι (cA + TA a) = cB + TB (ι a)` for all `a`, and `y = cB + TB y`, there is `a` with
`a = cA + TA a` and `ι a = y`. -/
theorem affine_fixedPt_mem_range {𝕜 A B : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A] [CompleteSpace A]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    {cA : A} {TA : A →L[𝕜] A} {cB : B} {TB : B →L[𝕜] B} (hTA : ‖TA‖ < 1) (hTB : ‖TB‖ < 1)
    {ι : A → B} (hι : ∀ a, ι (cA + TA a) = cB + TB (ι a)) {y : B} (hy : y = cB + TB y) :
    ∃ a, a = cA + TA a ∧ ι a = y :=
  ⟨_, (contractingWith_affine cA hTA).fixedPoint_isFixedPt.symm,
    (fixedPt_eq_of_semiconj (contractingWith_affine cA hTA)
      (fun _ hx _ hz => (contractingWith_affine cB hTB).fixedPoint_unique' hx hz) hι
      hy.symm).symm⟩

end Transfer

/-! ## The coefficient-preserving inclusion `l1Incl : ℓ¹_ρ → ℓ¹_ν'` for `ν' ≤ ρ` -/

section Inclusion
variable {𝕜 : Type*} [NormedField 𝕜] {ρ ν' : PosReal}

/-- For `ν' ≤ ρ`, the coefficients of `a ∈ ℓ¹_ρ` satisfy `MemL1v (fun k => ν' ^ |k|)`. -/
private theorem memL1v_toRealSeq_of_le (hνρ : (ν' : ℝ) ≤ ρ) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ρ)) :
    WeightedLp.MemL1v (fun k : ℤ => (ν' : ℝ) ^ k.natAbs) (lpOneAlg.toRealSeq a) :=
  (WeightedLp.memL1v_rawSymbol a).of_nonneg_of_le
    (fun _ => mul_nonneg (norm_nonneg _) (pow_nonneg ν'.coe_pos.le _)) fun _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ν'.coe_pos.le hνρ _) (norm_nonneg _)

/-- For `ν' ≤ ρ`, the element of ℓ¹_ν' with the coefficients of `a ∈ ℓ¹_ρ` has norm at most
`‖a‖`. -/
private theorem norm_ofRaw_toRealSeq_le (hνρ : (ν' : ℝ) ≤ ρ) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ρ)) :
    ‖(WeightedLp.ofRaw (lpOneAlg.toRealSeq a) (memL1v_toRealSeq_of_le hνρ a) :
      lpOneAlg ℤ (geomFiberZ 𝕜 ν'))‖ ≤ ‖a‖ := by
  rw [WeightedLp.norm_symbol_eq, WeightedLp.norm_symbol_eq (v := fun k : ℤ => (ρ : ℝ) ^ k.natAbs)]
  exact (memL1v_toRealSeq_of_le hνρ a).tsum_le_tsum (fun _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ν'.coe_pos.le hνρ _) (norm_nonneg _))
    (WeightedLp.memL1v_rawSymbol a)

/-- For `ν' ≤ ρ`, the continuous `𝕜`-linear map `ℓ¹_ρ → ℓ¹_ν'` given by
`a ↦ WeightedLp.ofRaw (lpOneAlg.toRealSeq a) _` (`LinearMap.mkContinuous` at bound `1`); its
coefficient face is `toRealSeq_l1Incl`. -/
def l1Incl (hνρ : (ν' : ℝ) ≤ ρ) : lpOneAlg ℤ (geomFiberZ 𝕜 ρ) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν') :=
  LinearMap.mkContinuous
    { toFun := fun a => WeightedLp.ofRaw (lpOneAlg.toRealSeq a) (memL1v_toRealSeq_of_le hνρ a)
      map_add' := fun a b => lpOneAlg.ext_toRealSeq ((lpOneAlg.toRealSeq_add a b).trans
        (lpOneAlg.toRealSeq_add
          (WeightedLp.ofRaw (lpOneAlg.toRealSeq a) (memL1v_toRealSeq_of_le hνρ a) :
            lpOneAlg ℤ (geomFiberZ 𝕜 ν'))
          (WeightedLp.ofRaw (lpOneAlg.toRealSeq b) (memL1v_toRealSeq_of_le hνρ b))).symm)
      map_smul' := fun r a => lpOneAlg.ext_toRealSeq ((lpOneAlg.toRealSeq_smul r a).trans
        (lpOneAlg.toRealSeq_smul r
          (WeightedLp.ofRaw (lpOneAlg.toRealSeq a) (memL1v_toRealSeq_of_le hνρ a) :
            lpOneAlg ℤ (geomFiberZ 𝕜 ν'))).symm) }
    1 fun a => (norm_ofRaw_toRealSeq_le hνρ a).trans_eq (one_mul _).symm

/-- `toRealSeq (l1Incl hνρ a) = toRealSeq a`. -/
@[simp] theorem toRealSeq_l1Incl (hνρ : (ν' : ℝ) ≤ ρ) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ρ)) :
    lpOneAlg.toRealSeq (l1Incl hνρ a) = lpOneAlg.toRealSeq a := rfl

/-- `‖l1Incl hνρ a‖ ≤ ‖a‖`. -/
theorem norm_l1Incl_apply_le (hνρ : (ν' : ℝ) ≤ ρ) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ρ)) :
    ‖l1Incl hνρ a‖ ≤ ‖a‖ :=
  norm_ofRaw_toRealSeq_le hνρ a

end Inclusion

/-! ## The composite `diagMulCLM u d = D_d ∘ L_u` -/

section TailOperator
open scoped _root_.DiscreteConvolution
variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- The composite `lpOneAlg.diagCLM d C hd ∘L lpOneAlg.mulLeftCLM u` on ℓ¹_ν. -/
def diagMulCLM (u : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (d : ℤ → 𝕜) (C : ℝ) (hd : ∀ n, ‖d n‖ ≤ C) :
    lpOneAlg ℤ (geomFiberZ 𝕜 ν) →L[𝕜] lpOneAlg ℤ (geomFiberZ 𝕜 ν) :=
  lpOneAlg.diagCLM d C hd ∘L lpOneAlg.mulLeftCLM u

/-- `toRealSeq (diagMulCLM u d C hd z) n = d n * (toRealSeq u ⋆ᵣ₊ toRealSeq z) n`. -/
theorem toRealSeq_diagMulCLM (u : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (d : ℤ → 𝕜) (C : ℝ)
    (hd : ∀ n, ‖d n‖ ≤ C) (z : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (n : ℤ) :
    lpOneAlg.toRealSeq (diagMulCLM u d C hd z) n =
      d n * (lpOneAlg.toRealSeq u ⋆ᵣ₊ lpOneAlg.toRealSeq z) n := by
  rw [diagMulCLM, ContinuousLinearMap.comp_apply, lpOneAlg.toRealSeq_diagCLM,
    lpOneAlg.mulLeftCLM_apply, lpOneAlg.toRealSeq_mul_fun]

end TailOperator

section TailOperatorNorm
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal}
  [Fact (1 ≤ (ν : ℝ))]

/-- `‖diagMulCLM u d C hd‖ ≤ C * ‖u‖`. -/
theorem norm_diagMulCLM_le (u : lpOneAlg ℤ (geomFiberZ 𝕜 ν)) (d : ℤ → 𝕜) (C : ℝ)
    (hd : ∀ n, ‖d n‖ ≤ C) : ‖diagMulCLM u d C hd‖ ≤ C * ‖u‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (lpOneAlg.norm_diagCLM_le d C hd ((norm_nonneg _).trans (hd 0)))
      (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u) fun z =>
        (congrArg norm (lpOneAlg.mulLeftCLM_apply u z)).trans_le (norm_mul_le u z))
      (norm_nonneg _) ((norm_nonneg _).trans (hd 0)))

end TailOperatorNorm

section TailOperatorInclusion
variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {ρ ν' : PosReal}
  [Fact (1 ≤ (ρ : ℝ))] [Fact (1 ≤ (ν' : ℝ))]

/-- `l1Incl hνρ (diagMulCLM u d C hd z) = diagMulCLM (l1Incl hνρ u) d C hd (l1Incl hνρ z)`. -/
theorem l1Incl_diagMulCLM (hνρ : (ν' : ℝ) ≤ ρ) (u : lpOneAlg ℤ (geomFiberZ 𝕜 ρ)) (d : ℤ → 𝕜)
    (C : ℝ) (hd : ∀ n, ‖d n‖ ≤ C) (z : lpOneAlg ℤ (geomFiberZ 𝕜 ρ)) :
    l1Incl hνρ (diagMulCLM u d C hd z) = diagMulCLM (l1Incl hνρ u) d C hd (l1Incl hνρ z) :=
  lpOneAlg.ext_toRealSeq <| funext fun n => by
    rw [toRealSeq_l1Incl, toRealSeq_diagMulCLM, toRealSeq_diagMulCLM, toRealSeq_l1Incl,
      toRealSeq_l1Incl]

end TailOperatorInclusion

/-! ## Finite support and the head lift -/

section HeadLift
variable {𝕜 : Type*} [NormedField 𝕜]

/-- A coefficient sequence that vanishes off a finset `F` satisfies `MemL1v v` for every
weight `v`. -/
theorem memL1v_of_eq_zero_off {M : Type*} {v : M → ℝ} (F : Finset M) {c : M → 𝕜}
    (hc : ∀ k ∉ F, c k = 0) : WeightedLp.MemL1v v c :=
  summable_of_ne_finset_zero (s := F) fun k hk => by
    simp only [hc k hk, norm_zero, zero_mul]

variable {ν' : PosReal}

/-- For `a ∈ ℓ¹_ν'`, the element `WeightedLp.ofRaw (lpOneAlg.toRealSeq (lpOneAlg.headProj F a)) _`
of ℓ¹_ρ; its coefficient face is `toRealSeq_headLift`. -/
def headLift (ρ : PosReal) (F : Finset ℤ) (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν')) :
    lpOneAlg ℤ (geomFiberZ 𝕜 ρ) :=
  WeightedLp.ofRaw (lpOneAlg.toRealSeq (lpOneAlg.headProj (𝕜 := 𝕜) F a))
    (memL1v_of_eq_zero_off F fun k hk => by
      rw [lpOneAlg.toRealSeq_headProj, ite_eq_right hk])

/-- `toRealSeq (headLift ρ F a) = toRealSeq (lpOneAlg.headProj F a)`. -/
@[simp] theorem toRealSeq_headLift (ρ : PosReal) (F : Finset ℤ)
    (a : lpOneAlg ℤ (geomFiberZ 𝕜 ν')) :
    lpOneAlg.toRealSeq (headLift ρ F a) =
      lpOneAlg.toRealSeq (lpOneAlg.headProj (𝕜 := 𝕜) F a) := rfl

end HeadLift

/-! ## The bootstrap theorem and the growth producer -/

section Growth
open scoped _root_.DiscreteConvolution

/-- If `c ≤ ‖σ n‖` off a finite set for some `c > ‖q‖`, `q ∈ ℓ¹_ρ`, `∑ ‖v n‖ < ∞` and
`σ n * v n + (toRealSeq q ⋆ᵣ₊ v) n = 0` outside a finite set, then some `a ∈ ℓ¹_ρ` has
`toRealSeq a = v`. -/
theorem exists_toRealSeq_eq_of_tail_gap {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {ρ : PosReal} {σ : ℤ → 𝕜}
    (q : lpOneAlg ℤ (geomFiberZ 𝕜 ρ))
    {c : ℝ} (hc : ‖q‖ < c) (hgap : ∃ F : Finset ℤ, ∀ n ∉ F, c ≤ ‖σ n‖)
    {v : ℤ → 𝕜} (hv : Summable fun n => ‖v n‖)
    (hE : ∀ᶠ n in Filter.cofinite, σ n * v n + (lpOneAlg.toRealSeq q ⋆ᵣ₊ v) n = 0) :
    ∃ a : lpOneAlg ℤ (geomFiberZ 𝕜 ρ), lpOneAlg.toRealSeq a = v := by
  rcases le_total (ρ : ℝ) 1 with hρ | hρ
  · -- step 1: for `ρ ≤ 1` the conclusion follows from `hv`
    exact ⟨WeightedLp.ofRaw v (hv.of_nonneg_of_le
      (fun _ => mul_nonneg (norm_nonneg _) (pow_nonneg ρ.coe_pos.le _))
      fun _ => mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ ρ.coe_pos.le hρ)), rfl⟩
  -- step 2: the ring instances
  have : Fact (1 ≤ (ρ : ℝ)) := ⟨hρ⟩
  have : Fact (1 ≤ ((1 : PosReal) : ℝ)) := ⟨le_rfl⟩
  -- step 3: the finite head
  rcases hgap with ⟨F₀, hF₀⟩
  let G := (Filter.eventually_cofinite.1 hE).toFinset
  let F := F₀ ∪ G
  have hF : ∀ n ∉ F, c ≤ ‖σ n‖ := fun n hn =>
    hF₀ n (fun hn0 => hn (Finset.mem_union_left G hn0))
  have hEF : ∀ n ∉ F, σ n * v n + (lpOneAlg.toRealSeq q ⋆ᵣ₊ v) n = 0 := by
    intro n hn
    have hnG : n ∉ G := fun hnG => hn (Finset.mem_union_right F₀ hnG)
    simpa only [G, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hnG
  -- step 4: the multiplier and its bound
  have hq1 : 0 < c := (norm_nonneg q).trans_lt hc
  obtain ⟨d, hd_def⟩ : ∃ d : ℤ → 𝕜, ∀ n, d n = if n ∈ F then 0 else -(σ n)⁻¹ :=
    ⟨fun n => if n ∈ F then 0 else -(σ n)⁻¹, fun _ => rfl⟩
  have hd : ∀ n, ‖d n‖ ≤ c⁻¹ := fun n => by
    by_cases hn : n ∈ F
    · rw [hd_def, ite_eq_left hn, norm_zero]
      exact inv_nonneg.2 hq1.le
    · rw [hd_def, ite_eq_right hn, norm_neg, norm_inv]
      exact inv_anti₀ hq1 (hF n hn)
  have hCq := (inv_mul_lt_iff₀ hq1).2 (hc.trans_eq (mul_one _).symm)
  -- step 5: `v` in ℓ¹_1, the inclusion and the two contractions
  have hv1 : WeightedLp.MemL1v (fun k : ℤ => ((1 : PosReal) : ℝ) ^ k.natAbs) v :=
    hv.congr fun n => (mul_one _).symm.trans (congrArg _ (one_pow _).symm)
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : lpOneAlg ℤ (geomFiberZ 𝕜 1), lpOneAlg.toRealSeq v₁ = v :=
    ⟨WeightedLp.ofRaw v hv1, rfl⟩
  have hρ1 : ((1 : PosReal) : ℝ) ≤ ρ := hρ
  have hTρ := (norm_diagMulCLM_le q d _ hd).trans_lt hCq
  have hT₁ := ((norm_diagMulCLM_le _ d _ hd).trans (mul_le_mul_of_nonneg_left
      (norm_l1Incl_apply_le hρ1 q) (inv_nonneg.2 hq1.le))).trans_lt hCq
  -- step 6: the tail of `v₁` is a fixed point of the affine map on ℓ¹_1
  have htail : lpOneAlg.tailProj (𝕜 := 𝕜) F v₁ = diagMulCLM (l1Incl hρ1 q) d _ hd v₁ :=
    lpOneAlg.ext_toRealSeq <| funext fun n => by
      rw [lpOneAlg.toRealSeq_tailProj, toRealSeq_diagMulCLM, toRealSeq_l1Incl, hv₁, hd_def]
      by_cases hn : n ∈ F
      · rw [ite_eq_left hn, ite_eq_left hn, zero_mul]
      · rw [ite_eq_right hn, ite_eq_right hn]
        have hσn := norm_pos_iff.1 (hq1.trans_le (hF n hn))
        exact (inv_mul_cancel_left₀ hσn (v n)).symm.trans
          ((congrArg _ (eq_neg_of_add_eq_zero_left (hEF n hn))).trans
            ((mul_neg _ _).trans (neg_mul _ _).symm))
  have hsplit : lpOneAlg.headProj (𝕜 := 𝕜) F v₁ + lpOneAlg.tailProj (𝕜 := 𝕜) F v₁ = v₁ := by
    rw [lpOneAlg.tailProj_eq_one_sub, sub_apply, one_apply_eq_self, add_sub_cancel]
  have hy : lpOneAlg.tailProj (𝕜 := 𝕜) F v₁ =
      diagMulCLM (l1Incl hρ1 q) d _ hd (lpOneAlg.headProj (𝕜 := 𝕜) F v₁) +
        diagMulCLM (l1Incl hρ1 q) d _ hd (lpOneAlg.tailProj (𝕜 := 𝕜) F v₁) :=
    htail.trans ((congrArg _ hsplit.symm).trans (map_add _ _ _))
  -- step 7: the head lift and the semiconjugacy
  have hhead : l1Incl hρ1 (headLift ρ F v₁) = lpOneAlg.headProj (𝕜 := 𝕜) F v₁ :=
    lpOneAlg.ext_toRealSeq (by rw [toRealSeq_l1Incl, toRealSeq_headLift])
  have hι : ∀ a, l1Incl hρ1 (diagMulCLM q d _ hd (headLift ρ F v₁) + diagMulCLM q d _ hd a) =
      diagMulCLM (l1Incl hρ1 q) d _ hd (lpOneAlg.headProj (𝕜 := 𝕜) F v₁) +
        diagMulCLM (l1Incl hρ1 q) d _ hd (l1Incl hρ1 a) := fun a => by
    rw [map_add, l1Incl_diagMulCLM, l1Incl_diagMulCLM, hhead]
  -- step 8: the fixed point on ℓ¹_ρ and the witness
  obtain ⟨a, -, ha⟩ := affine_fixedPt_mem_range hTρ hT₁ hι hy
  refine ⟨headLift ρ F v₁ + a, ?_⟩
  rw [lpOneAlg.toRealSeq_add, toRealSeq_headLift, ← toRealSeq_l1Incl hρ1 a, ha,
    ← lpOneAlg.toRealSeq_add, hsplit, hv₁]

/-- If `‖σ n‖` tends to `atTop` along `cofinite`, `q ∈ ℓ¹_ρ`, `∑ ‖v n‖ < ∞` and
`σ n * v n + (toRealSeq q ⋆ᵣ₊ v) n = 0` for all `n`, then some `a ∈ ℓ¹_ρ` has
`toRealSeq a = v` (the growth form of `exists_toRealSeq_eq_of_tail_gap`). -/
theorem exists_toRealSeq_eq_of_growth {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {ρ : PosReal} {σ : ℤ → 𝕜}
    (hσ : Filter.Tendsto (fun n => ‖σ n‖) Filter.cofinite Filter.atTop)
    (q : lpOneAlg ℤ (geomFiberZ 𝕜 ρ)) {v : ℤ → 𝕜} (hv : Summable fun n => ‖v n‖)
    (hE : ∀ n, σ n * v n + (lpOneAlg.toRealSeq q ⋆ᵣ₊ v) n = 0) :
    ∃ a : lpOneAlg ℤ (geomFiberZ 𝕜 ρ), lpOneAlg.toRealSeq a = v :=
  exists_toRealSeq_eq_of_tail_gap q (lt_add_one _)
    ⟨(Filter.eventually_cofinite.1 (hσ.eventually_ge_atTop (‖q‖ + 1))).toFinset, fun n hn => by
      rwa [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hn⟩ hv (Filter.Eventually.of_forall hE)

end Growth

end RadiiPolynomial.Bootstrap

end
