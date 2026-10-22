import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Bilateral.Product
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.TailDiagonal
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.HeadProj
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Fourier.ConvolutionAction
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-! Quadratic smoothing T∘q with q:X₂×X₂→Y and T:Y→X₂. AY has a pointwise disjoint-output identity and an upper operator-norm bound. The Lipschitz bounds use norm(2) ≤ 2 over a complete NontriviallyNormedField. -/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp.Bilateral

section TailInf

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}
variable (S : Set ℤ) [DecidablePred (· ∈ S)] (μ : ℤ → 𝕜)

/-- **The cross-exponent tail diagonal at the carrier** `T∞ : Y 𝕜 ν → X₂ 𝕜 ν`:
`tailDiagInf` at the carrier weight `m_k = ν ^ |k|`, under `Summable ‖d‖²`. -/
def tailInf (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2) : Y 𝕜 ν →L[𝕜] X₂ 𝕜 ν :=
  tailDiagInf (fun k : ℤ => (ν : ℝ) ^ k.natAbs) S μ hs

/-- `T∞` in coordinates: `coeff (T∞ y) k = d k * coeff y k`. -/
@[simp] theorem coeff_tailInf (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2) (y : Y 𝕜 ν)
    (k : ℤ) : coeff (tailInf S μ hs y) k = tailSymbol S μ k * coeff y k :=
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

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}
variable {M : Type*} [DecidableEq M] (F : Finset M)

/-- The tail symbol of `1` on the complement head `(↑F)ᶜ` is square summable (finite support). -/
theorem summable_sq_tailSymbol_compl_one :
    Summable fun k => ‖tailSymbol ((F : Set M)ᶜ) (fun _ => (1 : 𝕜)) k‖ ^ 2 :=
  summable_of_ne_finset_zero (s := F) fun k hk => by
    rw [tailSymbol_compl_one, ite_eq_right hk, norm_zero, sq, zero_mul]

end FiniteSupport

section HeadReal

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}
variable (F : Finset ℤ)

/-- **The finite-head realization** `H_F : Y 𝕜 ν → X₂ 𝕜 ν`: `tailInf` with the complement
head `(↑F)ᶜ` and the constant symbol `1` (the tail symbol is the indicator of `F`). -/
def headReal : Y 𝕜 ν →L[𝕜] X₂ 𝕜 ν :=
  tailInf ((F : Set ℤ)ᶜ) (fun _ => (1 : 𝕜)) (summable_sq_tailSymbol_compl_one F)

/-- `H_F` in coordinates: `coeff (H_F y) k = 1_{k ∈ F} coeff y k`. -/
@[simp] theorem coeff_headReal (y : Y 𝕜 ν) (k : ℤ) :
    coeff (headReal F y) k = if k ∈ F then coeff y k else 0 := by
  rw [headReal, coeff_tailInf, tailSymbol_compl_one, ite_mul, one_mul, zero_mul]

end HeadReal

section Inclusion

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}

/-- The inclusion `ι : X₂ 𝕜 ν → Y 𝕜 ν` as a linear map (the same fibre family). -/
def inclₗ : X₂ 𝕜 ν →ₗ[𝕜] Y 𝕜 ν where
  toFun x := ⟨x, (lp.memℓp x).of_exponent_ge le_top⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The bounded inclusion** `ι : X₂ 𝕜 ν →L[𝕜] Y 𝕜 ν` (every fibre norm is at most the ℓ² norm). -/
def incl : X₂ 𝕜 ν →L[𝕜] Y 𝕜 ν :=
  inclₗ.mkContinuous 1 fun x =>
    (lp.norm_le_of_forall_le (norm_nonneg x) fun k => norm_apply_le_norm x k).trans_eq
      (one_mul _).symm

/-- `ι` keeps the raw coefficients. -/
@[simp] theorem coeff_incl (x : X₂ 𝕜 ν) (k : ℤ) : coeff (incl x) k = coeff x k := rfl

/-- **Bridge `T∞ ι = T₂`**: the cross-exponent diagonal restricted to `X₂` is the same-exponent
diagonal of the same symbol (`BddAbove` from `bddAbove_of_summable_sq`). -/
theorem tailInf_comp_incl (S : Set ℤ) [DecidablePred (· ∈ S)] (μ : ℤ → 𝕜)
    (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2) :
    tailInf S μ hs ∘L incl =
      tailDiag (E := geomFiberZ 𝕜 ν) (p := 2) S μ (bddAbove_of_summable_sq hs) :=
  ContinuousLinearMap.ext fun x => ext_coeff <| funext fun k => by
    rw [ContinuousLinearMap.comp_apply, coeff_tailInf, coeff_incl, coeff_tailDiag]

end Inclusion

section HeadInclusion

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}
variable (F : Finset ℤ)

/-- **Bridge `H_F ι = P_F`**: the specialization `S = (↑F)ᶜ`, `μ = 1` of `tailInf_comp_incl`. -/
theorem headReal_comp_incl :
    headReal F ∘L incl = headProj (E := geomFiberZ 𝕜 ν) (p := 2) F :=
  tailInf_comp_incl _ _ _

end HeadInclusion

section AY

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}
variable (F : Finset ℤ) (M : X₂ 𝕜 ν →L[𝕜] X₂ 𝕜 ν) (S : Set ℤ) [DecidablePred (· ∈ S)] (μ : ℤ → 𝕜)

/-- **The operator `A_Y = M H_F + T∞ : Y 𝕜 ν → X₂ 𝕜 ν`** of the consumer, for a bounded `M`. -/
def AY (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2) : Y 𝕜 ν →L[𝕜] X₂ 𝕜 ν :=
  M ∘L headReal F + tailInf S μ hs

/-- A head-supported `M` (`P_F M = M`) has vanishing coordinates off `F`. -/
theorem coeff_eq_zero_of_headProj_comp
    (hPM : headProj (E := geomFiberZ 𝕜 ν) (p := 2) F ∘L M = M) (x : X₂ 𝕜 ν) {k : ℤ}
    (hk : k ∉ F) : coeff (M x) k = 0 := by
  rw [← hPM, ContinuousLinearMap.comp_apply, coeff_headProj, ite_eq_right hk]

/-- **The pointwise exact split** at the head `S = ↑F` under `P_F M = M`:
`‖A_Y y‖² = ‖M (H_F y)‖² + ‖T∞ y‖²` (disjoint coordinate supports). -/
theorem norm_sq_AY_apply (hs : Summable fun k => ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2)
    (hPM : headProj (E := geomFiberZ 𝕜 ν) (p := 2) F ∘L M = M) (y : Y 𝕜 ν) :
    ‖AY F M (F : Set ℤ) μ hs y‖ ^ 2 =
      ‖M (headReal F y)‖ ^ 2 + ‖tailInf (F : Set ℤ) μ hs y‖ ^ 2 := by
  rw [AY, add_apply, ContinuousLinearMap.comp_apply]
  refine norm_add_sq_of_disjoint fun k => ?_
  by_cases hk : k ∈ F
  · exact Or.inr (by rw [coeff_tailInf, tailSymbol_of_mem (Finset.mem_coe.2 hk), zero_mul])
  · exact Or.inl (coeff_eq_zero_of_headProj_comp F M hPM _ hk)

end AY

section AYNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ν : PosReal}
variable (F : Finset ℤ) (M : X₂ 𝕜 ν →L[𝕜] X₂ 𝕜 ν) (S : Set ℤ) [DecidablePred (· ∈ S)] (μ : ℤ → 𝕜)

/-- **The UPPER bound of the split**: `‖A_Y‖ ≤ √(‖M H_F‖² + ‖T∞‖²)` at `S = ↑F` under
`P_F M = M` (equality of the operator-norm split is not claimed here). -/
theorem norm_AY_le (hs : Summable fun k => ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2)
    (hPM : headProj (E := geomFiberZ 𝕜 ν) (p := 2) F ∘L M = M) :
    ‖AY F M (F : Set ℤ) μ hs‖ ≤
      √(‖M ∘L headReal F‖ ^ 2 + ‖tailInf (ν := ν) (F : Set ℤ) μ hs‖ ^ 2) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
  have hsq : ‖AY F M (F : Set ℤ) μ hs y‖ ^ 2 ≤
      (√(‖M ∘L headReal F‖ ^ 2 + ‖tailInf (ν := ν) (F : Set ℤ) μ hs‖ ^ 2) * ‖y‖) ^ 2 := by
    rw [norm_sq_AY_apply F M μ hs hPM y, mul_pow, Real.sq_sqrt (by positivity), add_mul]
    exact add_le_add
      ((pow_le_pow_left₀ (norm_nonneg _) ((M ∘L headReal F).le_opNorm y) 2).trans_eq
        (mul_pow _ _ _))
      ((pow_le_pow_left₀ (norm_nonneg _) ((tailInf (F : Set ℤ) μ hs).le_opNorm y) 2).trans_eq
        (mul_pow _ _ _))
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

end AYNorm

section Quadratic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal}
variable [Fact (1 ≤ (ν : ℝ))] (T : Y 𝕜 ν →L[𝕜] X₂ 𝕜 ν)

/-- **The quadratic composite** `quadCLM T = T ∘ prodCLM : X₂ 𝕜 ν →L X₂ 𝕜 ν →L X₂ 𝕜 ν` for a
bounded `T : Y 𝕜 ν → X₂ 𝕜 ν` (`quadCLM T a b = T (a ⋆ b)`). -/
def quadCLM : X₂ 𝕜 ν →L[𝕜] X₂ 𝕜 ν →L[𝕜] X₂ 𝕜 ν :=
  (ContinuousLinearMap.compL 𝕜 (X₂ 𝕜 ν) (Y 𝕜 ν) (X₂ 𝕜 ν) T).comp prodCLM

theorem quadCLM_apply (a b : X₂ 𝕜 ν) : quadCLM T a b = T (prodCLM a b) := rfl

/-- The composite is symmetric (`prodCLM_comm`). -/
theorem quadCLM_comm (a b : X₂ 𝕜 ν) : quadCLM T a b = quadCLM T b a := by
  rw [quadCLM_apply, quadCLM_apply, prodCLM_comm]

/-- `‖quadCLM T‖ ≤ ‖T‖` (`‖compL T‖ ≤ ‖T‖` and `‖prodCLM‖ ≤ 1`, `norm_prodCLM_le`). -/
theorem norm_quadCLM_le : ‖quadCLM T‖ ≤ ‖T‖ := by
  have hT : ‖ContinuousLinearMap.compL 𝕜 (X₂ 𝕜 ν) (Y 𝕜 ν) (X₂ 𝕜 ν) T‖ ≤ ‖T‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun g =>
      ContinuousLinearMap.opNorm_comp_le T g
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hT (norm_prodCLM_le (𝕜 := 𝕜) (ν := ν)) (ContinuousLinearMap.opNorm_nonneg _)
      (ContinuousLinearMap.opNorm_nonneg T)).trans_eq
      (mul_one _))

/-- The quadratic map `quad T a = T (a ⋆ a)`. -/
def quad (a : X₂ 𝕜 ν) : X₂ 𝕜 ν := quadCLM T a a

/-- The derivative of `quad T` at `a`: `Dquad T a = 2 • quadCLM T a`, i.e. `h ↦ 2 T (a ⋆ h)`. -/
def Dquad (a : X₂ 𝕜 ν) : X₂ 𝕜 ν →L[𝕜] X₂ 𝕜 ν := (2 : 𝕜) • quadCLM T a

/-- `Dquad T a h = T (a ⋆ h) + T (h ⋆ a)`. -/
theorem Dquad_apply (a h : X₂ 𝕜 ν) : Dquad T a h = quadCLM T a h + quadCLM T h a := by
  rw [Dquad, smul_apply, two_smul, quadCLM_comm T h a]

/-- The derivative identity behind `hasFDerivAt_quad` (a CLM equality, proved by `ext` on the
CLM goal only): Mathlib's bilinear derivative at `f = g = id` is `Dquad T a`. -/
theorem precompR_add_precompL_eq_Dquad (a : X₂ 𝕜 ν) :
    (quadCLM T).precompR (X₂ 𝕜 ν) a (ContinuousLinearMap.id 𝕜 (X₂ 𝕜 ν)) +
        (quadCLM T).precompL (X₂ 𝕜 ν) (ContinuousLinearMap.id 𝕜 (X₂ 𝕜 ν)) a = Dquad T a :=
  ContinuousLinearMap.ext fun h => by
    rw [add_apply, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.id_apply, Dquad_apply]

/-- **The derivative of the quadratic map**: `HasFDerivAt (quad T) (Dquad T a) a`. -/
theorem hasFDerivAt_quad (a : X₂ 𝕜 ν) : HasFDerivAt (quad T) (Dquad T a) a :=
  ((quadCLM T).hasFDerivAt_of_bilinear (hasFDerivAt_id a) (hasFDerivAt_id a)).congr_fderiv
    (precompR_add_precompL_eq_Dquad T a)

/-- The derivative difference is the composite at the difference:
`Dquad T a - Dquad T b = 2 • quadCLM T (a - b)`. -/
theorem Dquad_sub (a b : X₂ 𝕜 ν) : Dquad T a - Dquad T b = (2 : 𝕜) • quadCLM T (a - b) := by
  rw [Dquad, Dquad, map_sub, smul_sub]

end Quadratic

section QuadraticLipschitz

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal}
variable [Fact (1 ≤ (ν : ℝ))] (T : Y 𝕜 ν →L[𝕜] X₂ 𝕜 ν)

/-- **The derivative Lipschitz bound** `‖Dquad T a - Dquad T b‖ ≤ 2 ‖T‖ ‖a - b‖` (the `Z₂`
ingredient; no optimality claim). -/
theorem norm_Dquad_sub_le (a b : X₂ 𝕜 ν) : ‖Dquad T a - Dquad T b‖ ≤ 2 * ‖T‖ * ‖a - b‖ := by
  rw [Dquad_sub, norm_smul]
  have htwo : ‖(2 : 𝕜)‖ ≤ (2 : ℝ) := by
    have h := norm_add_le (1 : 𝕜) 1
    simpa only [one_add_one_eq_two, norm_one] using h
  have hquad : ‖quadCLM T (a - b)‖ ≤ ‖T‖ * ‖a - b‖ :=
    ((quadCLM T).le_opNorm (a - b)).trans
      (mul_le_mul_of_nonneg_right (norm_quadCLM_le T) (norm_nonneg _))
  exact (mul_le_mul htwo hquad (norm_nonneg _) zero_le_two).trans_eq (mul_assoc _ _ _).symm

end QuadraticLipschitz

section AYLipschitz

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {ν : PosReal}
variable [Fact (1 ≤ (ν : ℝ))] (F : Finset ℤ) (M : X₂ 𝕜 ν →L[𝕜] X₂ 𝕜 ν) (μ : ℤ → 𝕜)

/-- **The derivative Lipschitz bound at `T = A_Y`** (`S = ↑F`, `P_F M = M`) with the explicit
constant `2 √(‖M H_F‖² + ∑' ‖d‖²)` (through the UPPER bound `norm_AY_le`): the `Z₂ = 2 ‖A_Y‖`
ingredient of the consumer. -/
theorem norm_Dquad_sub_le_AY (hs : Summable fun k => ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2)
    (hPM : headProj (E := geomFiberZ 𝕜 ν) (p := 2) F ∘L M = M) (a b : X₂ 𝕜 ν) :
    ‖Dquad (AY F M (F : Set ℤ) μ hs) a - Dquad (AY F M (F : Set ℤ) μ hs) b‖ ≤
      2 * √(‖M ∘L headReal F‖ ^ 2 + ∑' k, ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2) * ‖a - b‖ := by
  refine (norm_Dquad_sub_le _ a b).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ zero_le_two) (norm_nonneg _))
  have ht : ‖tailInf (ν := ν) (F : Set ℤ) μ hs‖ ≤
      √(∑' k, ‖tailSymbol (F : Set ℤ) μ k‖ ^ 2) :=
    norm_tailDiagInf_le (fun k : ℤ => (ν : ℝ) ^ k.natAbs) hs
  refine (norm_AY_le F M μ hs hPM).trans
    (Real.sqrt_le_sqrt (add_le_add le_rfl ?_))
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans_eq
    (Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _))

end AYLipschitz

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
    (hβ : rawSymbol β = coeff a) (h : X₂ ℂ ν) : prodCLM a h = incl (symbolAction₀ (p := 2) Fourier.moderate_geomFiberZ β h) :=
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
    (h : X₂ ℂ ν) : (2 : ℂ) • prodCLM a h = incl (symbolAction₀ (p := 2) Fourier.moderate_geomFiberZ (betaOf F a hF) h) := by
  rw [show (2 : ℂ) • prodCLM a h = prodCLM ((2 : ℂ) • a) h by rw [map_smul, smul_apply]]
  exact prodCLM_eq_incl_symbolAction₀ (funext fun k => by
    rw [rawSymbol_betaOf, coeff_smul, Pi.smul_apply, smul_eq_mul]) h

end BetaBridge

end RadiiPolynomial.WeightedLp.Bilateral

end
