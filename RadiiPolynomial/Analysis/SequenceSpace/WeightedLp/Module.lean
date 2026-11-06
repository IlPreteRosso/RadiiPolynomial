import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Carrier
import Mathlib.Topology.UniformSpace.UniformEmbedding
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.UniversalProperty
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.ScalarInstances
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Coordinates, completeness and the bounded symbol action on weighted ℓᵖ

The frame reconstruction/completeness faces, translation along a reindexing
(`memℓp_norm_le_of_le_comp`) and the raw symbols assume no operation on the index. The shift
`shift`, its coordinate faces, `shift_zero` and the shift norm bounds are stated over an
additive group; the composition law `shift_add` and the symbol series, action and lift are
stated over an additive commutative group. The moderate-weight symbol series acts on the ℓᵖ
state under a positive symbol weight. When that weight is submultiplicative, its symbols form
the distinct weighted ℓ¹ algebra, and the series/lift comparison specifies its universal algebra
action at every exponent. The lift
`symbolAction` comes with its computation (`symbolAction_single`), algebra (`symbolAction₀_mul`,
`symbolAction₀_one`), bound (`norm_symbolAction_le`) and identification (`symbolAction₀_eq`)
statements.

Scalar assumptions are separated by service: pointwise construction and coordinates use NormedField;
operator-norm/function-space packaging uses NontriviallyNormedField, with complete scalars for
convergent operator series and the algebra lift. Unit normalization of the symbol weight is not
required by these services. Completeness transfers from the fibers (`completeSpace_carrier`).
-/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial
namespace WeightedLp

section CoordinateCompleteness

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
  [FiberTrivialization 𝕜 M E]

/-- The coordinates of a family given in the frame recover the scalar family. -/
theorem coeff_mk_equiv {p : ℝ≥0∞} (g : M → 𝕜)
    (h : Memℓp (fun n => FiberTrivialization.equiv (E := E) n (g n)) p) (n : M) :
    coeff (⟨_, h⟩ : WeightedLp M E p) n = g n :=
  FiberTrivialization.equiv_symm_apply_equiv _ _

variable [CompleteSpace 𝕜]

include 𝕜 in
/-- Every fibre of a frame over a complete normed field is complete. -/
theorem completeSpace_fiber (m : M) : CompleteSpace (E m) :=
  ((FiberTrivialization.equivL (E := E) m).isUniformEmbedding.isUniformInducing.completeSpace_congr
    (FiberTrivialization.equiv (E := E) m).surjective).mp inferInstance

include 𝕜 in
/-- The normed carrier over a frame on a complete normed field is complete. -/
theorem completeSpace_carrier {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    CompleteSpace (WeightedLp M E p) :=
  haveI : ∀ m, CompleteSpace (E m) := completeSpace_fiber (𝕜 := 𝕜)
  inferInstance

end CoordinateCompleteness


section Translation

variable {M : Type*} {E F : M → Type*} [∀ m, NormedAddCommGroup (E m)]
  [∀ m, NormedAddCommGroup (F m)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- If `‖f n‖ ≤ c ‖x (σ n)‖` along an injective reindexing `σ` of `M`, then `f ∈ ℓᵖ` with
`‖f‖ ≤ c ‖x‖`. -/
theorem memℓp_norm_le_of_le_comp {σ : M → M} (hσ : Function.Injective σ) (x : WeightedLp M E p)
    (f : ∀ n, F n) {c : ℝ} (hc : 0 ≤ c) (hf : ∀ n, ‖f n‖ ≤ c * ‖x (σ n)‖) :
    ∃ h : Memℓp f p, ‖(⟨f, h⟩ : WeightedLp M F p)‖ ≤ c * ‖x‖ := by
  have hcx : 0 ≤ c * ‖x‖ := mul_nonneg hc (norm_nonneg _)
  rcases p.dichotomy with rfl | hp
  · have hle : ∀ n, ‖f n‖ ≤ c * ‖x‖ := fun n =>
      (hf n).trans (mul_le_mul_of_nonneg_left (norm_apply_le_norm x _) hc)
    exact ⟨memℓp_infty_iff.2 ⟨c * ‖x‖, by rintro _ ⟨n, rfl⟩; exact hle n⟩,
      lp.norm_le_of_forall_le hcx hle⟩
  · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
    have key : ∀ s : Finset M, ∑ n ∈ s, ‖f n‖ ^ p.toReal ≤ (c * ‖x‖) ^ p.toReal := fun s => by
      refine (Finset.sum_le_sum fun n _ =>
        Real.rpow_le_rpow (norm_nonneg _) (hf n) hp0.le).trans ?_
      simp_rw [Real.mul_rpow hc (norm_nonneg _)]
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hc _)
      have := lp.sum_rpow_le_norm_rpow hp0 x (s.map ⟨σ, hσ⟩)
      rwa [Finset.sum_map] at this
    exact ⟨memℓp_gen' key, lp.norm_le_of_forall_sum_le hp0 hcx key⟩

end Translation

section Moderate

variable {M : Type*}

/-- Moderateness of a carrier weight `w` with respect to a symbol weight `v`, with constant `C`:
`w (j + l) ≤ C v_l w_j`. -/
def Moderate [Add M] (w v : M → ℝ) (C : ℝ) : Prop := ∀ j l, w (j + l) ≤ C * v l * w j

variable [Add M] {w v : M → ℝ} {C : ℝ}

/-- On a positive carrier weight, moderateness forces `C v_l > 0` (no sign hypothesis on `v`). -/
theorem Moderate.mul_pos (hw : ∀ m, 0 < w m) (hC : Moderate w v C) (l : M) : 0 < C * v l :=
  (mul_pos_iff_of_pos_right (hw l)).1 ((hw (l + l)).trans_le (hC l l))

/-- On positive weights over an inhabited index, the moderateness constant is positive (on the
empty index every `C` is a moderateness constant). -/
theorem Moderate.const_pos [Nonempty M] (hw : ∀ m, 0 < w m) (hv : ∀ l, 0 < v l)
    (hC : Moderate w v C) : 0 < C :=
  Nonempty.elim ‹Nonempty M› fun l => (mul_pos_iff_of_pos_right (hv l)).1 (hC.mul_pos hw l)

/-- A submultiplicative weight is moderate with respect to itself, with constant `1`. -/
theorem Moderate.of_submul {M : Type*} [Add M] {w : M → ℝ}
    (hs : ∀ i j, w (i + j) ≤ w i * w j) : Moderate w w 1 := fun j l =>
  (hs j l).trans_eq (by ring)

/-- Moderateness of the standard frame weight of `WeightedScalar 𝕜 w` is moderateness of `w`. -/
theorem Moderate.weightedScalar_iff {𝕜 : Type*} [NormedField 𝕜] [PosWeight w] :
    Moderate (FiberTrivialization.weight (E := WeightedScalar 𝕜 w)) v C ↔ Moderate w v C := by
  rw [show FiberTrivialization.weight (E := WeightedScalar 𝕜 w) = w from
    funext WeightedScalar.fiberTrivialization_weight]

end Moderate

section Symbols

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*}

/-- Membership of a raw symbol in `ℓ¹_v`: `∑' l, ‖a l‖ v_l < ∞`. -/
def MemL1v (v : M → ℝ) (a : M → 𝕜) : Prop := Summable fun l => ‖a l‖ * v l

/-- The `ℓ¹_v` norm of a raw symbol: `∑' l, ‖a l‖ v_l`. -/
def normL1v (v : M → ℝ) (a : M → 𝕜) : ℝ := ∑' l, ‖a l‖ * v l

end Symbols

section Shift

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [AddGroup M] {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {v : M → ℝ} {C : ℝ}

/-- The shifted family `n ↦ θ_n (coeff y (n - l))` lies in the carrier, with norm at most
`C v_l ‖y‖`. -/
theorem shift_memℓp (hC : Moderate (FiberTrivialization.weight (E := E)) v C) (l : M)
    (y : WeightedLp M E p) :
    ∃ h : Memℓp (fun n => FiberTrivialization.equiv (E := E) n (coeff y (n - l))) p,
      ‖(⟨_, h⟩ : WeightedLp M E p)‖ ≤ C * v l * ‖y‖ := by
  refine memℓp_norm_le_of_le_comp (sub_left_injective (b := l)) y _
    (hC.mul_pos FiberTrivialization.weight_pos l).le fun n => ?_
  rw [FiberTrivialization.norm_equiv_apply, norm_apply_eq]
  have hmod := hC (n - l) l
  rw [sub_add_cancel] at hmod
  exact (mul_le_mul_of_nonneg_left hmod (norm_nonneg _)).trans_eq (by ring)

/-- The shift `S_l` as a linear map. -/
def shiftLM (hC : Moderate (FiberTrivialization.weight (E := E)) v C) (l : M) :
    WeightedLp M E p →ₗ[𝕜] WeightedLp M E p where
  toFun y := ⟨_, (shift_memℓp hC l y).1⟩
  map_add' y z := ext_coeff <| funext fun n => (coeff_mk_equiv _ _ n).trans <| by
    simp only [coeff_add, Pi.add_apply, coeff_mk_equiv]
  map_smul' c y := ext_coeff <| funext fun n => (coeff_mk_equiv _ _ n).trans <| by
    simp only [coeff_smul, Pi.smul_apply, coeff_mk_equiv, RingHom.id_apply]

/-- The shift `S_l : WeightedLp M E p →L[𝕜] WeightedLp M E p`, `(S_l y)_n = θ_n (coeff y (n - l))`,
with constant `C v_l`. -/
def shift (hC : Moderate (FiberTrivialization.weight (E := E)) v C) (l : M) :
    WeightedLp M E p →L[𝕜] WeightedLp M E p :=
  (shiftLM hC l).mkContinuous (C * v l) fun y => (shift_memℓp hC l y).2

variable (hC : Moderate (FiberTrivialization.weight (E := E)) v C)

/-- The shift in coordinates: `coeff (S_l y) n = coeff y (n - l)`. -/
@[simp] theorem coeff_shift (l : M) (y : WeightedLp M E p) (n : M) :
    coeff (shift hC l y) n = coeff y (n - l) :=
  coeff_mk_equiv _ _ n

/-- `S_0 = 1`. -/
theorem shift_zero : shift (p := p) hC 0 = 1 :=
  ContinuousLinearMap.ext fun y => ext_coeff <| funext fun n => by
    rw [coeff_shift, sub_zero, one_apply_eq_self]

end Shift

section ShiftAdd

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [AddCommGroup M] {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {v : M → ℝ} {C : ℝ}

variable (hC : Moderate (FiberTrivialization.weight (E := E)) v C)

/-- `S_{j + l} = S_j S_l` (composition). -/
theorem shift_add (j l : M) : shift (p := p) hC (j + l) = shift hC j * shift hC l :=
  ContinuousLinearMap.ext fun y => ext_coeff <| funext fun n => by
    rw [coeff_shift, mul_apply_eq_comp, coeff_shift, coeff_shift, sub_add_eq_sub_sub]

end ShiftAdd

section ShiftNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {M : Type*} [AddGroup M] {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {v : M → ℝ} {C : ℝ}

variable (hC : Moderate (FiberTrivialization.weight (E := E)) v C)

/-- `‖S_l‖ ≤ C v_l`. -/
theorem norm_shift_le (l : M) : ‖shift (p := p) hC l‖ ≤ C * v l :=
  LinearMap.mkContinuous_norm_le _ (hC.mul_pos FiberTrivialization.weight_pos l).le _


section PositiveSymbolWeight

variable [PosWeight v]

/-- The shifts are dominated by the weight of the symbol frame: `‖S_l‖ ≤ C ω^{sym}_l`. -/
theorem norm_shift_le_weight (l : M) :
    ‖shift (p := p) hC l‖ ≤ C * FiberTrivialization.weight (E := WeightedScalar 𝕜 v) l := by
  rw [WeightedScalar.fiberTrivialization_weight]
  exact norm_shift_le hC l

end PositiveSymbolWeight

end ShiftNorm

section SeriesBounds

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {M : Type*} [AddCommGroup M] {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {v : M → ℝ} {C : ℝ} {a : M → 𝕜}

theorem summable_norm_smul_shift (ha : MemL1v v a)
    (hC : Moderate (FiberTrivialization.weight (E := E)) v C) :
    Summable fun l => ‖a l • shift (p := p) hC l‖ :=
  (ha.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) fun l =>
    (norm_smul_le (a l) (shift (p := p) hC l)).trans
      ((mul_le_mul_of_nonneg_left (norm_shift_le hC l) (norm_nonneg (a l))).trans_eq (by ring))

/-- The symbol operator `∑' l, a l • S_l` (a tsum in `WeightedLp M E p →L[𝕜] WeightedLp M E p`;
absolutely convergent by `summable_norm_smul_shift`). -/
def symbolSeries (a : M → 𝕜) (_ha : MemL1v v a)
    (hC : Moderate (FiberTrivialization.weight (E := E)) v C) :
    WeightedLp M E p →L[𝕜] WeightedLp M E p :=
  ∑' l, a l • shift hC l

variable (ha : MemL1v v a) (hC : Moderate (FiberTrivialization.weight (E := E)) v C)

/-- `‖∑' l, a l • S_l‖ ≤ C ‖a‖_{1,v}`. -/
theorem norm_symbolSeries_le : ‖symbolSeries (p := p) a ha hC‖ ≤ C * normL1v v a :=
  tsum_of_norm_bounded (ha.hasSum.mul_left C) fun l =>
    (norm_smul_le (a l) (shift (p := p) hC l)).trans
      ((mul_le_mul_of_nonneg_left (norm_shift_le hC l) (norm_nonneg (a l))).trans_eq (by ring))


end SeriesBounds

section SeriesComplete

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {M : Type*} [AddCommGroup M] {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {v : M → ℝ} {C : ℝ} {a : M → 𝕜}

variable [CompleteSpace 𝕜]

/-- The operator series `∑' l, a l • S_l` converges in `WeightedLp M E p →L[𝕜] WeightedLp M E p`. -/
theorem summable_smul_shift (ha : MemL1v v a)
    (hC : Moderate (FiberTrivialization.weight (E := E)) v C) :
    Summable fun l => a l • shift (p := p) hC l :=
  haveI := completeSpace_carrier (𝕜 := 𝕜) (E := E) (p := p)
  (summable_norm_smul_shift ha hC).of_norm

variable (ha : MemL1v v a) (hC : Moderate (FiberTrivialization.weight (E := E)) v C)

/-- The symbol operator in coordinates: `coeff (M_a y) n = ∑' l, a l * coeff y (n - l)`. -/
theorem coeff_symbolSeries (y : WeightedLp M E p) (n : M) :
    coeff (symbolSeries a ha hC y) n = ∑' l, a l * coeff y (n - l) := by
  refine (((coeffCLM n).comp (ContinuousLinearMap.apply 𝕜 (WeightedLp M E p) y)).map_tsum
    (summable_smul_shift ha hC)).trans (tsum_congr fun l => ?_)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, coeffCLM_apply,
    smul_apply, coeff_smul, Pi.smul_apply, coeff_shift, smul_eq_mul]

end SeriesComplete

section SymbolCarrier

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {v : M → ℝ} [PosWeight v]

/-- The raw scalar coefficients of a symbol: `rawSymbol a l = WeightedScalar.toReal (a l)`. -/
def rawSymbol (a : lpOneAlg M (WeightedScalar 𝕜 v)) : M → 𝕜 :=
  fun l => WeightedScalar.toReal (a l)

/-- A symbol has raw coefficients in `ℓ¹_v`. -/
theorem memL1v_rawSymbol (a : lpOneAlg M (WeightedScalar 𝕜 v)) : MemL1v v (rawSymbol a) :=
  (lpOneAlg.summable_norm a).congr fun l => WeightedScalar.norm_def (a l)

/-- The norm of a symbol is the `ℓ¹_v` norm of its raw coefficients:
`‖a‖ = ∑' l, ‖rawSymbol a l‖ * v l` (the fibre norm `‖a l‖` already carries the weight). -/
theorem norm_symbol_eq (a : lpOneAlg M (WeightedScalar 𝕜 v)) :
    ‖a‖ = ∑' l, ‖rawSymbol a l‖ * v l :=
  (lpOneAlg.norm_eq_tsum a).trans (tsum_congr fun l => WeightedScalar.norm_def (a l))

theorem norm_symbol_eq_normL1v (a : lpOneAlg M (WeightedScalar 𝕜 v)) :
    ‖a‖ = normL1v v (rawSymbol a) :=
  norm_symbol_eq a

/-- The symbol with raw coefficients `a ∈ ℓ¹_v`. -/
def ofRaw (a : M → 𝕜) (ha : MemL1v v a) : lpOneAlg M (WeightedScalar 𝕜 v) :=
  ⟨⟨fun l => WeightedScalar.ofReal (a l),
    (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).2 <| by
      simpa only [ENNReal.toReal_one, Real.rpow_one, WeightedScalar.norm_ofReal, MemL1v] using ha⟩⟩

@[simp] theorem rawSymbol_ofRaw (a : M → 𝕜) (ha : MemL1v v a) :
    rawSymbol (ofRaw a ha) = a := rfl

@[simp] theorem ofRaw_rawSymbol (a : lpOneAlg M (WeightedScalar 𝕜 v)) :
    ofRaw (rawSymbol a) (memL1v_rawSymbol a) = a := rfl

theorem rawSymbol_add (a b : lpOneAlg M (WeightedScalar 𝕜 v)) :
    rawSymbol (a + b) = rawSymbol a + rawSymbol b :=
  lpOneAlg.toRealSeq_add a b

theorem rawSymbol_smul (c : 𝕜) (a : lpOneAlg M (WeightedScalar 𝕜 v)) :
    rawSymbol (c • a) = c • rawSymbol a :=
  lpOneAlg.toRealSeq_smul c a



end SymbolCarrier

section Action

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {M : Type*} [AddCommGroup M] {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {v : M → ℝ} {C : ℝ}

variable [CompleteSpace 𝕜] [PosWeight v]

/-- The symbol action as a linear map, `a ↦ ∑' l, rawSymbol a l • S_l`. -/
def symbolActionLM (hC : Moderate (FiberTrivialization.weight (E := E)) v C) :
    lpOneAlg M (WeightedScalar 𝕜 v) →ₗ[𝕜] (WeightedLp M E p →L[𝕜] WeightedLp M E p) where
  toFun a := symbolSeries (rawSymbol a) (memL1v_rawSymbol a) hC
  map_add' a b := by
    show ∑' l, rawSymbol (a + b) l • shift (p := p) hC l =
      ∑' l, rawSymbol a l • shift hC l + ∑' l, rawSymbol b l • shift hC l
    rw [← (summable_smul_shift (p := p) (memL1v_rawSymbol a) hC).tsum_add
      (summable_smul_shift (memL1v_rawSymbol b) hC)]
    exact tsum_congr fun l => by
      rw [rawSymbol_add, Pi.add_apply]
      exact add_smul (rawSymbol a l) (rawSymbol b l) (shift hC l)
  map_smul' c a := by
    show ∑' l, rawSymbol (c • a) l • shift (p := p) hC l = c • ∑' l, rawSymbol a l • shift hC l
    rw [← (summable_smul_shift (p := p) (memL1v_rawSymbol a) hC).tsum_const_smul c]
    exact tsum_congr fun l => by
      rw [rawSymbol_smul, Pi.smul_apply, smul_eq_mul]
      exact mul_smul c (rawSymbol a l) (shift hC l)

/-- **The symbol action, bundled independently of the lift**:
`lpOneAlg M (WeightedScalar 𝕜 v) →L[𝕜] (WeightedLp M E p →L[𝕜] WeightedLp M E p)`,
`a ↦ ∑' l, rawSymbol a l • S_l`, with constant `C` (`norm_symbol_eq`). -/
def symbolAction₀ (hC : Moderate (FiberTrivialization.weight (E := E)) v C) :
    lpOneAlg M (WeightedScalar 𝕜 v) →L[𝕜] (WeightedLp M E p →L[𝕜] WeightedLp M E p) :=
  (symbolActionLM hC).mkContinuous C fun a =>
    (norm_symbolSeries_le (memL1v_rawSymbol a) hC).trans_eq
      (congrArg (C * ·) (norm_symbol_eq_normL1v a)).symm

variable (hC : Moderate (FiberTrivialization.weight (E := E)) v C)

theorem symbolAction₀_apply (a : lpOneAlg M (WeightedScalar 𝕜 v)) :
    symbolAction₀ (p := p) hC a = symbolSeries (rawSymbol a) (memL1v_rawSymbol a) hC := rfl


/-- The symbol action on an atom: `symbolAction₀ (single l r) = r • S_l`. -/
theorem symbolAction₀_single [DecidableEq M] (l : M) (r : 𝕜) :
    symbolAction₀ (p := p) hC (lpOneAlg.single l r) = r • shift hC l := by
  change ∑' k, lpOneAlg.toRealSeq (lpOneAlg.single (E := WeightedScalar 𝕜 v) l r) k •
    shift (p := p) hC k = r • shift hC l
  rw [lpOneAlg.toRealSeq_single_eq_piSingle, tsum_eq_single l fun k hk => by
    rw [Pi.single_eq_of_ne hk]; exact zero_smul 𝕜 (shift hC k), Pi.single_eq_same]

/-- `‖symbolAction₀‖ ≤ C`. -/
theorem norm_symbolAction₀_le : ‖symbolAction₀ (p := p) hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _
    (hC.const_pos FiberTrivialization.weight_pos PosWeight.weight_pos).le _


end Action

section Lift

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {M : Type*} [AddCommGroup M] {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {v : M → ℝ} {C : ℝ}

variable [CompleteSpace 𝕜] [DecidableEq M] [SubMulWeightBase v]

variable (hC : Moderate (FiberTrivialization.weight (E := E)) v C)

/-- **The symbol action through the universal property of `ℓ¹_v`**: the library's
`lpOneAlg.liftAlgHom` applied to the shift family (`S_0 = 1`, `S_{j+l} = S_j S_l`,
`‖S_l‖ ≤ C v_l`; the target `WeightedLp M E p →L[𝕜] WeightedLp M E p` is a complete normed
algebra). -/
def symbolAction :
    lpOneAlg M (WeightedScalar 𝕜 v) →A[𝕜] (WeightedLp M E p →L[𝕜] WeightedLp M E p) :=
  haveI := completeSpace_carrier (𝕜 := 𝕜) (E := E) (p := p)
  lpOneAlg.liftAlgHom (shift (p := p) hC) C (norm_shift_le_weight hC) (shift_zero hC)
    (shift_add hC)

/-- The algebra lift sends the unit atom at `l` to the shift `S_l`. -/
@[simp] theorem symbolAction_single (l : M) :
    symbolAction (p := p) hC (lpOneAlg.single l 1) = shift hC l :=
  haveI := completeSpace_carrier (𝕜 := 𝕜) (E := E) (p := p)
  lpOneAlg.liftAlgHom_single _ _ _ _ _ l

/-- **The operator series is the algebra lift**: `symbolAction₀ = symbolAction` as continuous
linear maps, by determination on the symbol atoms (valid for every carrier exponent, `∞`
included). -/
theorem symbolAction₀_eq :
    symbolAction₀ (p := p) hC = (symbolAction hC).toContinuousLinearMap :=
  lpOneAlg.continuousLinearMap_ext fun l => by
    rw [symbolAction₀_single, one_smul]
    exact (symbolAction_single hC l).symm

theorem symbolAction₀_apply_eq (a : lpOneAlg M (WeightedScalar 𝕜 v)) :
    symbolAction₀ (p := p) hC a = symbolAction hC a := by
  rw [symbolAction₀_eq]
  rfl

/-- Multiplicativity of the operator series, inherited from the lift:
`M_{a * b} = M_a ∘ M_b`. -/
theorem symbolAction₀_mul (a b : lpOneAlg M (WeightedScalar 𝕜 v)) :
    symbolAction₀ (p := p) hC (a * b) = (symbolAction₀ hC a).comp (symbolAction₀ hC b) := by
  rw [symbolAction₀_apply_eq, symbolAction₀_apply_eq, symbolAction₀_apply_eq, map_mul]
  rfl

/-- Unitality of the operator series, inherited from the lift: `M_1 = 1`. -/
theorem symbolAction₀_one : symbolAction₀ (p := p) hC 1 = 1 := by
  rw [symbolAction₀_apply_eq, map_one]

/-- `‖symbolAction‖ ≤ C` (as a continuous linear map). -/
theorem norm_symbolAction_le : ‖(symbolAction (p := p) hC).toContinuousLinearMap‖ ≤ C := by
  rw [← symbolAction₀_eq]
  exact norm_symbolAction₀_le hC


end Lift

section Summability

/-- If `∑ (w n)⁻¹ ^ 2 < ∞`, then every `x : WeightedLp M (WeightedScalar 𝕜 w) 2` has
`Summable fun n => ‖WeightedLp.coeff x n‖`. -/
theorem summable_norm_coeff_weightedScalar {𝕜 : Type*} [NormedField 𝕜] {M : Type*}
    {w : M → ℝ} [PosWeight w] (hw : Summable fun n => (w n)⁻¹ ^ 2)
    (x : WeightedLp M (WeightedScalar 𝕜 w) 2) : Summable fun n => ‖WeightedLp.coeff x n‖ :=
  summable_norm_coeff_of_summable_inv_sq
    (by simpa only [WeightedScalar.fiberTrivialization_weight] using hw) x

end Summability

end WeightedLp
end RadiiPolynomial
