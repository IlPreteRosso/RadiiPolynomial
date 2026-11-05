import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.TailDiagonal

/-! Finite-head coordinate projections and their complement over arbitrary framed NormedField carriers. -/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp

section OneSymbol

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*}

/-- The tail symbol of `1` has modulus at most `1` on every head. -/
theorem norm_tailSymbol_one_le (S : Set M) [DecidablePred (· ∈ S)] (k : M) :
    ‖tailSymbol S (fun _ => (1 : 𝕜)) k‖ ≤ 1 := by
  rw [norm_tailSymbol]
  split_ifs
  · exact zero_le_one
  · rw [norm_one, inv_one]

/-- The named boundedness proof of the tail symbol of `1` (every head). -/
theorem bddAbove_tailSymbol_one (S : Set M) [DecidablePred (· ∈ S)] :
    BddAbove (Set.range fun k => ‖tailSymbol S (fun _ => (1 : 𝕜)) k‖) :=
  ⟨1, by rintro _ ⟨k, rfl⟩; exact norm_tailSymbol_one_le S k⟩

end OneSymbol

section OneCoefficients

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [DecidableEq M] (F : Finset M)

/-- On the complement head `(↑F)ᶜ` the tail symbol of `1` is the indicator of `F`. -/
theorem tailSymbol_compl_one (k : M) :
    tailSymbol ((F : Set M)ᶜ) (fun _ => (1 : 𝕜)) k = if k ∈ F then 1 else 0 := by
  by_cases hk : k ∈ F
  · rw [tailSymbol_of_notMem (show k ∉ (F : Set M)ᶜ from fun h => h (Finset.mem_coe.2 hk)),
      inv_one, ite_eq_left hk]
  · rw [tailSymbol_of_mem (show k ∈ (F : Set M)ᶜ from fun h => hk (Finset.mem_coe.1 h)),
      ite_eq_right hk]

/-- On the head `↑F` the tail symbol of `1` is the indicator of the complement of `F`. -/
theorem tailSymbol_coe_one (k : M) :
    tailSymbol (F : Set M) (fun _ => (1 : 𝕜)) k = if k ∈ F then 0 else 1 := by
  by_cases hk : k ∈ F
  · rw [tailSymbol_of_mem (Finset.mem_coe.2 hk), ite_eq_left hk]
  · rw [tailSymbol_of_notMem (fun h => hk (Finset.mem_coe.1 h)), inv_one, ite_eq_right hk]

end OneCoefficients

section Projections

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (F : Finset M)

/-- **The head projection** `P_F = tailDiag (↑F)ᶜ 1`: the tail diagonal with the complement
head `(↑F)ᶜ` and the constant symbol `1`. -/
def headProj : WeightedLp M E p →L[𝕜] WeightedLp M E p :=
  tailDiag ((F : Set M)ᶜ) (fun _ => (1 : 𝕜)) (bddAbove_tailSymbol_one _)

/-- **The tail projection** `Q_F = tailDiag ↑F 1`: the tail diagonal with the head `↑F`
and the constant symbol `1`. -/
def tailProj : WeightedLp M E p →L[𝕜] WeightedLp M E p :=
  tailDiag (F : Set M) (fun _ => (1 : 𝕜)) (bddAbove_tailSymbol_one _)

/-- The head projection in coordinates: `coeff (P_F x) k = 1_{k ∈ F} coeff x k`. -/
@[simp] theorem coeff_headProj (x : WeightedLp M E p) (k : M) :
    coeff (headProj (𝕜 := 𝕜) F x) k = if k ∈ F then coeff x k else 0 := by
  rw [headProj, coeff_tailDiag, tailSymbol_compl_one, ite_mul, one_mul, zero_mul]

/-- The tail projection in coordinates: `coeff (Q_F x) k = 1_{k ∉ F} coeff x k`. -/
@[simp] theorem coeff_tailProj (x : WeightedLp M E p) (k : M) :
    coeff (tailProj (𝕜 := 𝕜) F x) k = if k ∈ F then 0 else coeff x k := by
  rw [tailProj, coeff_tailDiag, tailSymbol_coe_one, ite_mul, one_mul, zero_mul]

/-- `Q_F = id - P_F`. -/
theorem tailProj_eq_id_sub_headProj :
    tailProj (𝕜 := 𝕜) (E := E) (p := p) F = ContinuousLinearMap.id 𝕜 _ - headProj (𝕜 := 𝕜) F :=
  ContinuousLinearMap.ext fun x => ext_coeff <| funext fun k => by
    rw [coeff_tailProj, sub_apply, ContinuousLinearMap.id_apply, coeff_sub,
      Pi.sub_apply, coeff_headProj]
    split_ifs <;> simp

/-- **The identity-tail defect law**: for every operator `T`, `I − (T + Q_F) = P_F − T`. The
identity tail `Q_F = I − P_F` cancels against `I`, so the defect of `T + Q_F` is the head
defect `P_F − T` (no hypothesis on `T`). -/
theorem id_sub_add_tailProj (T : WeightedLp M E p →L[𝕜] WeightedLp M E p) :
    ContinuousLinearMap.id 𝕜 _ - (T + tailProj (𝕜 := 𝕜) F) = headProj (𝕜 := 𝕜) F - T := by
  rw [tailProj_eq_id_sub_headProj]
  abel

/-- `P_F ∘ P_F = P_F`. -/
theorem headProj_comp_headProj :
    (headProj (𝕜 := 𝕜) (E := E) (p := p) F).comp (headProj (𝕜 := 𝕜) F) = headProj (𝕜 := 𝕜) F :=
  ContinuousLinearMap.ext fun x => ext_coeff <| funext fun k => by
    rw [ContinuousLinearMap.comp_apply, coeff_headProj, coeff_headProj]
    split_ifs <;> rfl

/-- `P_F ∘ Q_F = 0`. -/
theorem headProj_comp_tailProj :
    (headProj (𝕜 := 𝕜) (E := E) (p := p) F).comp (tailProj (𝕜 := 𝕜) F) = 0 :=
  ContinuousLinearMap.ext fun x => ext_coeff <| funext fun k => by
    rw [ContinuousLinearMap.comp_apply, coeff_headProj, coeff_tailProj,
      zero_apply, coeff_zero]
    split_ifs <;> rfl

end Projections

section ProjectionApplyNorm

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- `‖P_S x‖ ≤ ‖x‖`. -/
theorem norm_headProj_apply_le (S : Finset M) (x : WeightedLp M E p) :
    ‖headProj (𝕜 := 𝕜) S x‖ ≤ ‖x‖ := by
  have hp : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  refine lp.norm_mono hp fun n => ?_
  rw [norm_apply_eq, norm_apply_eq, coeff_headProj]
  by_cases hn : n ∈ S
  · rw [ite_eq_left hn]
  · rw [ite_eq_right hn, norm_zero, zero_mul, ← norm_apply_eq]
    exact norm_nonneg _

end ProjectionApplyNorm

end RadiiPolynomial.WeightedLp

end
