import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Bilateral.Product
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.TailDiagonal
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.HeadProj
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.FiniteBlock
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Fourier.ConvolutionAction

/-! Quadratic smoothing T∘q with q:X₂×X₂→Y and T:Y→X₂. The return services (the tail diagonal `tailInf`, the finite-head realization `headReal`, the inclusion `incl` with its identities `tailInf_comp_incl`, `headReal_comp_incl`, the operator `AY` with its pointwise disjoint-output identity and upper operator-norm bounds, and the `U_row` head bound `norm_comp_headReal_le_urow`) hold at every positive weight `w` (`X_w = WeightedLp ℤ (WeightedScalar 𝕜 w) 2`, `Y_w = … ∞`). The geometry-specific product and smoothing bounds supply the quadratic theorem in Core. -/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp.Bilateral

section TailInf

variable {𝕜 : Type*} [NormedField 𝕜] {w : ℤ → ℝ} [PosWeight w]
variable (S : Set ℤ) [DecidablePred (· ∈ S)] (μ : ℤ → 𝕜)

/-- **The cross-exponent tail diagonal at the carrier**
`T∞ : WeightedLp ℤ (WeightedScalar 𝕜 w) ∞ → WeightedLp ℤ (WeightedScalar 𝕜 w) 2`: `tailDiagInf`
at the carrier weight `w` (the geometric carrier `Y 𝕜 ν → X₂ 𝕜 ν` at `w k = ν ^ |k|`), under
`Summable ‖d‖²`. -/
def tailInf (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2) :
    WeightedLp ℤ (WeightedScalar 𝕜 w) ∞ →L[𝕜] WeightedLp ℤ (WeightedScalar 𝕜 w) 2 :=
  tailDiagInf w S μ hs

/-- `T∞` in coordinates: `coeff (T∞ y) k = d k * coeff y k`. -/
@[simp] theorem coeff_tailInf (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2)
    (y : WeightedLp ℤ (WeightedScalar 𝕜 w) ∞) (k : ℤ) :
    coeff (tailInf S μ hs y) k = tailSymbol S μ k * coeff y k :=
  coeff_tailDiagInf hs y k

variable {S μ} in
/-- A square-summable tail symbol is bounded: `‖d k‖ ≤ √(∑' ‖d‖²)`. -/
theorem bddAbove_of_summable_sq (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2) :
    BddAbove (Set.range fun k => ‖tailSymbol S μ k‖) :=
  ⟨√(∑' k, ‖tailSymbol S μ k‖ ^ 2), by
    rintro _ ⟨k, rfl⟩
    exact (abs_norm _).symm.trans_le
      (Real.abs_le_sqrt (hs.le_tsum k fun _ _ => by positivity))⟩

end TailInf



section FiniteSupport

variable {𝕜 : Type*} [NormedField 𝕜]
variable {M : Type*} [DecidableEq M] (F : Finset M)

/-- The tail symbol of `1` on the complement head `(↑F)ᶜ` is square summable (finite support). -/
theorem summable_sq_tailSymbol_compl_one :
    Summable fun k => ‖tailSymbol ((F : Set M)ᶜ) (fun _ => (1 : 𝕜)) k‖ ^ 2 :=
  summable_of_ne_finset_zero (s := F) fun k hk => by
    rw [tailSymbol_compl_one, ite_eq_right hk, norm_zero, sq, zero_mul]

end FiniteSupport

section HeadReal

variable {𝕜 : Type*} [NormedField 𝕜] {w : ℤ → ℝ} [PosWeight w]
variable (F : Finset ℤ)

/-- **The finite-head realization**
`H_F : WeightedLp ℤ (WeightedScalar 𝕜 w) ∞ → WeightedLp ℤ (WeightedScalar 𝕜 w) 2`: `tailInf`
with the complement head `(↑F)ᶜ` and the constant symbol `1` (the tail symbol is the indicator
of `F`). -/
def headReal : WeightedLp ℤ (WeightedScalar 𝕜 w) ∞ →L[𝕜] WeightedLp ℤ (WeightedScalar 𝕜 w) 2 :=
  tailInf ((F : Set ℤ)ᶜ) (fun _ => (1 : 𝕜)) (summable_sq_tailSymbol_compl_one F)

/-- `H_F` in coordinates: `coeff (H_F y) k = 1_{k ∈ F} coeff y k`. -/
@[simp] theorem coeff_headReal (y : WeightedLp ℤ (WeightedScalar 𝕜 w) ∞) (k : ℤ) :
    coeff (headReal F y) k = if k ∈ F then coeff y k else 0 := by
  rw [headReal, coeff_tailInf, tailSymbol_compl_one, ite_mul, one_mul, zero_mul]

end HeadReal

section Inclusion

variable {𝕜 : Type*} [NormedField 𝕜] {w : ℤ → ℝ} [PosWeight w]

/-- The inclusion
`ι : WeightedLp ℤ (WeightedScalar 𝕜 w) 2 → WeightedLp ℤ (WeightedScalar 𝕜 w) ∞` as a linear map
(the same fibre family). -/
def inclₗ : WeightedLp ℤ (WeightedScalar 𝕜 w) 2 →ₗ[𝕜] WeightedLp ℤ (WeightedScalar 𝕜 w) ∞ where
  toFun x := ⟨x, (lp.memℓp x).of_exponent_ge le_top⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The bounded inclusion**
`ι : WeightedLp ℤ (WeightedScalar 𝕜 w) 2 →L[𝕜] WeightedLp ℤ (WeightedScalar 𝕜 w) ∞` (every
fibre norm is at most the ℓ² norm). -/
def incl : WeightedLp ℤ (WeightedScalar 𝕜 w) 2 →L[𝕜] WeightedLp ℤ (WeightedScalar 𝕜 w) ∞ :=
  inclₗ.mkContinuous 1 fun x =>
    (lp.norm_le_of_forall_le (norm_nonneg x) fun k => norm_apply_le_norm x k).trans_eq
      (one_mul _).symm

/-- `ι` keeps the fibre values. -/
theorem incl_apply (x : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k : ℤ) : incl x k = x k := rfl

/-- `ι` keeps the raw coefficients (through `incl_apply`). -/
@[simp] theorem coeff_incl (x : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) (k : ℤ) :
    coeff (incl x) k = coeff x k := by
  rw [coeff_apply, coeff_apply, incl_apply]

/-- **Bridge `T∞ ι = T₂`**: the cross-exponent diagonal restricted to the ℓ² carrier is the
same-exponent diagonal of the same symbol (`BddAbove` from `bddAbove_of_summable_sq`). -/
theorem tailInf_comp_incl (S : Set ℤ) [DecidablePred (· ∈ S)] (μ : ℤ → 𝕜)
    (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2) :
    tailInf S μ hs ∘L incl =
      tailDiag (E := WeightedScalar 𝕜 w) (p := 2) S μ (bddAbove_of_summable_sq hs) :=
  ContinuousLinearMap.ext fun x => ext_coeff <| funext fun k => by
    rw [ContinuousLinearMap.comp_apply, coeff_tailInf, coeff_incl, coeff_tailDiag]

end Inclusion

section HeadInclusion

variable {𝕜 : Type*} [NormedField 𝕜] {w : ℤ → ℝ} [PosWeight w]
variable (F : Finset ℤ)

/-- **Bridge `H_F ι = P_F`**: the specialization `S = (↑F)ᶜ`, `μ = 1` of `tailInf_comp_incl`. -/
theorem headReal_comp_incl :
    headReal F ∘L incl = headProj (E := WeightedScalar 𝕜 w) (p := 2) F :=
  tailInf_comp_incl _ _ _

end HeadInclusion

section AY

variable {𝕜 : Type*} [NormedField 𝕜] {w : ℤ → ℝ} [PosWeight w]
variable (F : Finset ℤ)
  (M : WeightedLp ℤ (WeightedScalar 𝕜 w) 2 →L[𝕜] WeightedLp ℤ (WeightedScalar 𝕜 w) 2)
  (S : Set ℤ) [DecidablePred (· ∈ S)] (μ : ℤ → 𝕜)

/-- **The operator `A_Y = M H_F + T∞`**
`: WeightedLp ℤ (WeightedScalar 𝕜 w) ∞ → WeightedLp ℤ (WeightedScalar 𝕜 w) 2` of the consumer,
for a bounded `M`. -/
def AY (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2) :
    WeightedLp ℤ (WeightedScalar 𝕜 w) ∞ →L[𝕜] WeightedLp ℤ (WeightedScalar 𝕜 w) 2 :=
  M ∘L headReal F + tailInf S μ hs

/-- A head-supported `M` (`P_F M = M`) has vanishing coordinates off `F`. -/
theorem coeff_eq_zero_of_headProj_comp
    (hPM : headProj (E := WeightedScalar 𝕜 w) (p := 2) F ∘L M = M)
    (x : WeightedLp ℤ (WeightedScalar 𝕜 w) 2) {k : ℤ} (hk : k ∉ F) : coeff (M x) k = 0 := by
  rw [← hPM, ContinuousLinearMap.comp_apply, coeff_headProj, ite_eq_right hk]

/-- **The pointwise exact split** at the head `S = ↑F` under `P_F M = M`:
`‖A_Y y‖² = ‖M (H_F y)‖² + ‖T∞ y‖²` (disjoint coordinate supports). -/
theorem norm_sq_AY_apply (hs : Summable fun k => ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2)
    (hPM : headProj (E := WeightedScalar 𝕜 w) (p := 2) F ∘L M = M)
    (y : WeightedLp ℤ (WeightedScalar 𝕜 w) ∞) :
    ‖AY F M (F : Set ℤ) μ hs y‖ ^ 2 =
      ‖M (headReal F y)‖ ^ 2 + ‖tailInf (F : Set ℤ) μ hs y‖ ^ 2 := by
  rw [AY, add_apply, ContinuousLinearMap.comp_apply]
  refine norm_add_sq_of_disjoint fun k => ?_
  by_cases hk : k ∈ F
  · exact Or.inr (by rw [coeff_tailInf, tailSymbol_of_mem (Finset.mem_coe.2 hk), zero_mul])
  · exact Or.inl (coeff_eq_zero_of_headProj_comp F M hPM _ hk)

end AY

section AYNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {w : ℤ → ℝ} [PosWeight w]
variable (F : Finset ℤ)
  (M : WeightedLp ℤ (WeightedScalar 𝕜 w) 2 →L[𝕜] WeightedLp ℤ (WeightedScalar 𝕜 w) 2)
  (S : Set ℤ) [DecidablePred (· ∈ S)] (μ : ℤ → 𝕜)

/-- **The UPPER bound of the split**: `‖A_Y‖ ≤ √(‖M H_F‖² + ‖T∞‖²)` at `S = ↑F` under
`P_F M = M` (equality of the operator-norm split is not claimed here). -/
theorem norm_AY_le (hs : Summable fun k => ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2)
    (hPM : headProj (E := WeightedScalar 𝕜 w) (p := 2) F ∘L M = M) :
    ‖AY F M (F : Set ℤ) μ hs‖ ≤
      √(‖M ∘L headReal F‖ ^ 2 + ‖tailInf (w := w) (F : Set ℤ) μ hs‖ ^ 2) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
  have hsq : ‖AY F M (F : Set ℤ) μ hs y‖ ^ 2 ≤
      (√(‖M ∘L headReal F‖ ^ 2 + ‖tailInf (w := w) (F : Set ℤ) μ hs‖ ^ 2) * ‖y‖) ^ 2 := by
    rw [norm_sq_AY_apply F M μ hs hPM y, mul_pow, Real.sq_sqrt (by positivity), add_mul]
    exact add_le_add
      ((pow_le_pow_left₀ (norm_nonneg _) ((M ∘L headReal F).le_opNorm y) 2).trans_eq
        (mul_pow _ _ _))
      ((pow_le_pow_left₀ (norm_nonneg _) ((tailInf (F : Set ℤ) μ hs).le_opNorm y) 2).trans_eq
        (mul_pow _ _ _))
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

end AYNorm

section URow

variable {w : ℤ → ℝ} [PosWeight w] (F : Finset ℤ)
  (M : WeightedLp ℤ (WeightedScalar ℂ w) 2 →L[ℂ] WeightedLp ℤ (WeightedScalar ℂ w) 2)

/-- **The `U_row` head certificate** (UPPER): with `B_ij = w_i M_ij / w_j`,
`‖M H_F‖ ≤ √(∑_{i ∈ F} (∑_{j ∈ F} |B_ij|)²)` under `P M = M`. -/
theorem norm_comp_headReal_le_urow
    (hPM : headProj (𝕜 := ℂ) (E := WeightedScalar ℂ w) (p := 2) F ∘L M = M) :
    ‖M ∘L headReal F‖ ≤ √(∑ i ∈ F, (∑ j ∈ F, ‖matrixOf M i j‖ * w i / w j) ^ 2) := by
  have hn (x : WeightedLp ℤ (WeightedScalar ℂ w) 2) (k : ℤ) : ‖x k‖ = ‖coeff x k‖ * w k := by
    rw [norm_apply_eq, WeightedScalar.fiberTrivialization_weight]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
  have hHy : ∀ k ∉ F, coeff (headReal F y) k = 0 := fun k hk => by
    rw [coeff_headReal, ite_eq_right hk]
  have hterm : ∀ i, ‖coeff (M (headReal F y)) i‖ * w i ≤
      (∑ j ∈ F, ‖matrixOf M i j‖ * w i / w j) * ‖y‖ := fun i => by
    rw [coeff_apply_of_coeff_eq_zero M hHy i, Finset.sum_mul]
    refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _)
      (PosWeight.weight_nonneg (w := w) i)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [norm_mul, coeff_headReal, ite_eq_left hj]
    have hwj : 0 < w j := PosWeight.weight_pos (w := w) j
    have hy := mul_le_mul_of_nonneg_left (normMag_le_norm_Y y j)
      (div_nonneg (mul_nonneg (norm_nonneg (matrixOf M i j)) (PosWeight.weight_nonneg (w := w) i))
        hwj.le)
    refine Eq.trans_le ?_ hy
    field_simp
  have hsq : ‖(M ∘L headReal F) y‖ ^ 2 ≤
      (√(∑ i ∈ F, (∑ j ∈ F, ‖matrixOf M i j‖ * w i / w j) ^ 2) * ‖y‖) ^ 2 := by
    rw [ContinuousLinearMap.comp_apply, norm_sq_eq_tsum, tsum_eq_sum (s := F) fun i hi => by
        rw [hn, coeff_eq_zero_of_headProj_comp F M hPM _ hi, norm_zero, zero_mul, sq,
          zero_mul],
      mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hn, ← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (PosWeight.weight_nonneg (w := w) i))
      (hterm i) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

end URow

section Quadratic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal}
variable [Fact (1 ≤ (ν : ℝ))] (T : Y 𝕜 ν →L[𝕜] X₂ 𝕜 ν)

/-- **The quadratic composite**
`quadCLM T = T ∘ prodCLM (geomSubmul ν) : X₂ 𝕜 ν →L X₂ 𝕜 ν →L X₂ 𝕜 ν` for a bounded
`T : Y 𝕜 ν → X₂ 𝕜 ν` (`quadCLM T a b = T (a ⋆ b)`). -/
def quadCLM : X₂ 𝕜 ν →L[𝕜] X₂ 𝕜 ν →L[𝕜] X₂ 𝕜 ν :=
  (ContinuousLinearMap.compL 𝕜 (X₂ 𝕜 ν) (Y 𝕜 ν) (X₂ 𝕜 ν) T).comp (prodCLM (geomSubmul ν))

theorem quadCLM_apply (a b : X₂ 𝕜 ν) : quadCLM T a b = T (prodCLM (geomSubmul ν) a b) := rfl

/-- The composite is symmetric (`prodCLM_comm`). -/
theorem quadCLM_comm (a b : X₂ 𝕜 ν) : quadCLM T a b = quadCLM T b a := by
  rw [quadCLM_apply, quadCLM_apply, prodCLM_comm (geomSubmul ν)]

/-- `‖quadCLM T‖ ≤ ‖T‖` (`‖compL T‖ ≤ ‖T‖` and `‖prodCLM (geomSubmul ν)‖ ≤ 1`,
`norm_prodCLM_le`). -/
theorem norm_quadCLM_le : ‖quadCLM T‖ ≤ ‖T‖ := by
  have hT : ‖ContinuousLinearMap.compL 𝕜 (X₂ 𝕜 ν) (Y 𝕜 ν) (X₂ 𝕜 ν) T‖ ≤ ‖T‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun g =>
      ContinuousLinearMap.opNorm_comp_le T g
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hT (norm_prodCLM_le (𝕜 := 𝕜) (geomSubmul ν))
      (ContinuousLinearMap.opNorm_nonneg _) (ContinuousLinearMap.opNorm_nonneg T)).trans_eq
      (mul_one _))

end Quadratic

section AYNormTail

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {w : ℤ → ℝ} [PosWeight w]
variable (F : Finset ℤ)
  (M : WeightedLp ℤ (WeightedScalar 𝕜 w) 2 →L[𝕜] WeightedLp ℤ (WeightedScalar 𝕜 w) 2)
  (μ : ℤ → 𝕜)

/-- The smoothing norm bound from the head norm and the square sum of the tail symbol. -/
theorem norm_AY_le_sqrt_tsum (hs : Summable fun k => ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2)
    (hPM : headProj (E := WeightedScalar 𝕜 w) (p := 2) F ∘L M = M) :
    ‖AY F M (F : Set ℤ) μ hs‖ ≤
      √(‖M ∘L headReal F‖ ^ 2 + ∑' k, ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2) := by
  have ht : ‖tailInf (w := w) (F : Set ℤ) μ hs‖ ≤
      √(∑' k, ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2) :=
    norm_tailDiagInf_le w hs
  refine (norm_AY_le F M μ hs hPM).trans
    (Real.sqrt_le_sqrt (add_le_add le_rfl ?_))
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans_eq
    (Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _))

end AYNormTail

section BetaBridge

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- The included operator-series action has raw convolution coefficients. -/
theorem coeff_incl_symbolAction₀ (β : lpOneAlg ℤ (geomFiberZ ℂ ν)) (h : X₂ ℂ ν) (k : ℤ) :
    coeff (incl (symbolAction₀ (p := 2) Fourier.moderate_geomFiberZ β h)) k = ∑' j, rawSymbol β j * coeff h (k - j) := by
  rw [coeff_incl, symbolAction₀_apply]
  exact coeff_symbolSeries _ _ h k

/-- **The bridge `q(a, h) = ι (symbolAction₀ β h)`**: when the raw symbol of `β` is the raw coefficient
family of `a`, the product with `a` is the symbol action of `β` followed by the inclusion. -/
theorem prodCLM_eq_incl_symbolAction₀ {β : lpOneAlg ℤ (geomFiberZ ℂ ν)} {a : X₂ ℂ ν}
    (hβ : rawSymbol β = coeff a) (h : X₂ ℂ ν) :
    prodCLM (geomSubmul ν) a h = incl (symbolAction₀ (p := 2) Fourier.moderate_geomFiberZ β h) :=
  ext_coeff <| funext fun k => by rw [coeff_prodCLM, coeff_incl_symbolAction₀, convCoeff, hβ]

omit [Fact (1 ≤ (ν : ℝ))] in
/-- A finitely supported raw coefficient family, doubled, lies in `ℓ¹_m`. -/
theorem memL1v_two_coeff (F : Finset ℤ) (a : X₂ ℂ ν) (hF : ∀ k ∉ F, coeff a k = 0) :
    MemL1v (fun k : ℤ => (ν : ℝ) ^ k.natAbs) (fun k => 2 * coeff a k) :=
  summable_of_ne_finset_zero (s := F) fun k hk => by
    beta_reduce
    rw [hF k hk, mul_zero, norm_zero, zero_mul]

omit [Fact (1 ≤ (ν : ℝ))] in
/-- **The symbol `β = 2a`** of a finitely supported `a ∈ X₂ ℂ ν`, as an element of `ℓ¹_m`. -/
def betaOf (F : Finset ℤ) (a : X₂ ℂ ν) (hF : ∀ k ∉ F, coeff a k = 0) :
    lpOneAlg ℤ (geomFiberZ ℂ ν) :=
  ofRaw (fun k => 2 * coeff a k) (memL1v_two_coeff F a hF)

omit [Fact (1 ≤ (ν : ℝ))] in
@[simp] theorem rawSymbol_betaOf (F : Finset ℤ) (a : X₂ ℂ ν) (hF : ∀ k ∉ F, coeff a k = 0) :
    rawSymbol (betaOf F a hF) = fun k => 2 * coeff a k :=
  rawSymbol_ofRaw _ _

/-- **The bridge `2 q(a, h) = ι (symbolAction₀ β h)` at `β = 2a`** (finitely supported `a`). -/
theorem two_smul_prodCLM_eq_incl_symbolAction₀ (F : Finset ℤ) (a : X₂ ℂ ν) (hF : ∀ k ∉ F, coeff a k = 0)
    (h : X₂ ℂ ν) : (2 : ℂ) • prodCLM (geomSubmul ν) a h =
      incl (symbolAction₀ (p := 2) Fourier.moderate_geomFiberZ (betaOf F a hF) h) := by
  rw [show (2 : ℂ) • prodCLM (geomSubmul ν) a h = prodCLM (geomSubmul ν) ((2 : ℂ) • a) h by
    rw [map_smul, smul_apply]]
  exact prodCLM_eq_incl_symbolAction₀ (funext fun k => by
    rw [rawSymbol_betaOf, coeff_smul, Pi.smul_apply, smul_eq_mul]) h

end BetaBridge

end RadiiPolynomial.WeightedLp.Bilateral

end
