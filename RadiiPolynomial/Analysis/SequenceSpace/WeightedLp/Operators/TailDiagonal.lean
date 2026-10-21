import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.Schur
import Mathlib.Analysis.PSeries

/-!
Same-exponent tail inverse and cross-exponent ℓ∞→ℓ² smoothing with the square-sum upper bound.
The exact-attainment cluster is proved in the frozen records and parked from this API. The
shared p2 disjoint-output law and real psi1 tail are geometry-neutral services; no Chebyshev
carrier is imported.
-/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp

section TailSymbol

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} (S : Set M) [DecidablePred (· ∈ S)] (μ : M → 𝕜)

/-- The tail symbol `d k = 1_{k ∉ S} (μ k)⁻¹` (field inverse; no hypothesis on `μ`). -/
def tailSymbol : M → 𝕜 := fun k => if k ∈ S then 0 else (μ k)⁻¹

variable {S μ} in
/-- On the head the tail symbol vanishes. -/
theorem tailSymbol_of_mem {k : M} (hk : k ∈ S) : tailSymbol S μ k = 0 := ite_eq_left hk

variable {S μ} in
/-- Off the head the tail symbol is the inverse symbol. -/
theorem tailSymbol_of_notMem {k : M} (hk : k ∉ S) : tailSymbol S μ k = (μ k)⁻¹ := ite_eq_right hk

/-- The modulus of the tail symbol: `‖d k‖ = 1_{k ∉ S} ‖μ k‖⁻¹`. -/
theorem norm_tailSymbol (k : M) : ‖tailSymbol S μ k‖ = if k ∈ S then 0 else ‖μ k‖⁻¹ := by
  unfold tailSymbol
  split_ifs
  · exact norm_zero
  · exact norm_inv _

/-- Under a designated minimum witness every tail entry is at most `‖μ k₀‖⁻¹`. -/
theorem norm_tailSymbol_le_of_witness {k₀ : M} (hμ : μ k₀ ≠ 0)
    (hmin : ∀ k ∉ S, ‖μ k₀‖ ≤ ‖μ k‖) (k : M) : ‖tailSymbol S μ k‖ ≤ ‖μ k₀‖⁻¹ := by
  rw [norm_tailSymbol]
  split_ifs with hk
  · exact inv_nonneg.2 (norm_nonneg _)
  · exact inv_anti₀ (norm_pos_iff.2 hμ) (hmin k hk)

end TailSymbol

section SameExponent

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} [DecidableEq M] {E : M → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (S : Set M) [DecidablePred (· ∈ S)] (μ : M → 𝕜)
  (hd : BddAbove (Set.range fun k => ‖tailSymbol S μ k‖))

/-- The tail-inverse diagonal `T_S(μ) = diag(tailSymbol S μ)` on `WeightedLp M E p`. -/
def tailDiag : WeightedLp M E p →L[𝕜] WeightedLp M E p := diagCLM (tailSymbol S μ) hd

omit [DecidableEq M] in
/-- `T_S(μ)` in coordinates: `coeff (T x) k = d k * coeff x k`. -/
@[simp] theorem coeff_tailDiag (x : WeightedLp M E p) (k : M) :
    coeff (tailDiag S μ hd x) k = tailSymbol S μ k * coeff x k :=
  coeff_diagCLM _ hd x k

/-- `T_S(μ)` on an atom: `T (single m r) = single m (d m * r)`. -/
theorem tailDiag_single (m : M) (r : 𝕜) :
    tailDiag (E := E) (p := p) S μ hd (single m r) = single m (tailSymbol S μ m * r) :=
  ext_coeff <| funext fun k => by
    rw [coeff_tailDiag, coeff_single, coeff_single]
    by_cases h : k = m
    · subst h; rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, mul_zero]

end SameExponent



section L2Norm

variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)]

/-- The `ℓ²` norm square is the sum of the fibre norm squares (`rpow` at `p = 2` read as `npow`). -/
theorem norm_sq_eq_tsum (x : WeightedLp M E 2) : ‖x‖ ^ 2 = ∑' k, ‖x k‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h


end L2Norm

section DisjointOutputs

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]

/-- **`ℓ²` aggregation over disjoint supports**: if at every index one of the two coordinates
vanishes, `‖x + y‖² = ‖x‖² + ‖y‖²` (the norm squares add; this is not a max law). -/
theorem norm_add_sq_of_disjoint {x y : WeightedLp M E 2}
    (h : ∀ k, coeff x k = 0 ∨ coeff y k = 0) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hpt : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hpw : ∀ k, ‖(x + y) k‖ ^ (2 : ℝ≥0∞).toReal =
      ‖x k‖ ^ (2 : ℝ≥0∞).toReal + ‖y k‖ ^ (2 : ℝ≥0∞).toReal := fun k => by
    rw [lp.coeFn_add, Pi.add_apply, hpt]
    rcases h k with hk | hk
    · rw [show x k = 0 by rw [← equiv_coeff x k, hk, map_zero], zero_add, norm_zero,
        Real.zero_rpow two_ne_zero, zero_add]
    · rw [show y k = 0 by rw [← equiv_coeff y k, hk, map_zero], add_zero, norm_zero,
        Real.zero_rpow two_ne_zero, add_zero]
  have hxy := lp.hasSum_norm hp (x + y)
  rw [funext hpw] at hxy
  have e := hxy.unique ((lp.hasSum_norm hp x).add (lp.hasSum_norm hp y))
  rwa [hpt, Real.rpow_two, Real.rpow_two, Real.rpow_two] at e

end DisjointOutputs

section CrossGeometry

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {w : M → ℝ} [PosWeight w]
  {S : Set M} [DecidablePred (· ∈ S)] {μ : M → 𝕜}

/-- The pointwise bound behind face (b): `‖d k • y k‖² ≤ ‖d k‖² ‖y‖²_∞`. -/
theorem norm_sq_smul_apply_le (y : WeightedLp M (WeightedScalar 𝕜 w) ∞) (k : M) :
    ‖tailSymbol S μ k • y k‖ ^ 2 ≤ ‖tailSymbol S μ k‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_smul, mul_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_apply_le_norm y k) 2) (by positivity)

/-- Under `Summable ‖d‖²` the coordinatewise image of an `ℓ^∞` element lies in `ℓ²`. -/
theorem memℓp_tailSymbol_smul (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2)
    (y : WeightedLp M (WeightedScalar 𝕜 w) ∞) :
    Memℓp (fun k => tailSymbol S μ k • y k) 2 := by
  refine memℓp_gen ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  exact Summable.of_nonneg_of_le (fun k => by positivity) (norm_sq_smul_apply_le y)
    (hs.mul_right _)

end CrossGeometry

section CrossLinear

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {w : M → ℝ} [PosWeight w]
  {S : Set M} [DecidablePred (· ∈ S)] {μ : M → 𝕜}
variable (w S μ)

/-- The cross-exponent tail diagonal as a linear map `ℓ^∞ → ℓ²`. -/
def tailDiagInfₗ (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2) :
    WeightedLp M (WeightedScalar 𝕜 w) ∞ →ₗ[𝕜] WeightedLp M (WeightedScalar 𝕜 w) 2 where
  toFun y := ⟨fun k => tailSymbol S μ k • y k, memℓp_tailSymbol_smul hs y⟩
  map_add' x y := lp.ext <| funext fun k => by
    show tailSymbol S μ k • (x + y) k = tailSymbol S μ k • x k + tailSymbol S μ k • y k
    rw [lp.coeFn_add, Pi.add_apply, smul_add]
  map_smul' c x := lp.ext <| funext fun k => by
    show tailSymbol S μ k • (c • x) k = c • (tailSymbol S μ k • x k)
    rw [lp.coeFn_smul, Pi.smul_apply, smul_comm]

end CrossLinear

section CrossLinearLaws

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {w : M → ℝ} [PosWeight w]
  {S : Set M} [DecidablePred (· ∈ S)] {μ : M → 𝕜}

/-- The bound `‖T y‖ ≤ √(∑' ‖d‖²) ‖y‖`. -/
theorem norm_tailDiagInfₗ_apply_le (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2)
    (y : WeightedLp M (WeightedScalar 𝕜 w) ∞) :
    ‖tailDiagInfₗ w S μ hs y‖ ≤ √(∑' k, ‖tailSymbol S μ k‖ ^ 2) * ‖y‖ := by
  have hsq : ‖tailDiagInfₗ w S μ hs y‖ ^ 2 ≤ (√(∑' k, ‖tailSymbol S μ k‖ ^ 2) * ‖y‖) ^ 2 := by
    rw [norm_sq_eq_tsum, mul_pow, Real.sq_sqrt (tsum_nonneg fun _ => by positivity),
      ← tsum_mul_right]
    exact Summable.tsum_le_tsum (fun k => norm_sq_smul_apply_le y k)
      ((lp.memℓp (tailDiagInfₗ w S μ hs y)).summable (by norm_num) |>.congr fun k => by
        simp only [ENNReal.toReal_ofNat, Real.rpow_two])
      (hs.mul_right _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

end CrossLinearLaws

section CrossContinuous

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {w : M → ℝ} [PosWeight w]
  {S : Set M} [DecidablePred (· ∈ S)] {μ : M → 𝕜}
variable (w S μ)

/-- **The cross-exponent tail diagonal** `T∞ : ℓ^∞_w → ℓ²_w` on the scalar fibre, under
`Summable ‖d‖²`, with the bound `√(∑' ‖d‖²)`. -/
def tailDiagInf (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2) :
    WeightedLp M (WeightedScalar 𝕜 w) ∞ →L[𝕜] WeightedLp M (WeightedScalar 𝕜 w) 2 :=
  (tailDiagInfₗ w S μ hs).mkContinuous (√(∑' k, ‖tailSymbol S μ k‖ ^ 2))
    (norm_tailDiagInfₗ_apply_le hs)

end CrossContinuous

section CrossContinuousLaws

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {w : M → ℝ} [PosWeight w]
  {S : Set M} [DecidablePred (· ∈ S)] {μ : M → 𝕜}

theorem tailDiagInf_apply (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2)
    (y : WeightedLp M (WeightedScalar 𝕜 w) ∞) (k : M) :
    tailDiagInf w S μ hs y k = tailSymbol S μ k • y k := rfl

/-- `T∞` in coordinates: `coeff (T∞ y) k = d k * coeff y k`. -/
@[simp] theorem coeff_tailDiagInf (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2)
    (y : WeightedLp M (WeightedScalar 𝕜 w) ∞) (k : M) :
    coeff (tailDiagInf w S μ hs y) k = tailSymbol S μ k * coeff y k := by
  rw [coeff_apply, tailDiagInf_apply, map_smul, smul_eq_mul, ← coeff_apply]

end CrossContinuousLaws

section CrossNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {M : Type*} {w : M → ℝ} [PosWeight w]
  {S : Set M} [DecidablePred (· ∈ S)] {μ : M → 𝕜}

variable (w) in
/-- `‖T∞‖ ≤ √(∑' ‖d‖²)`. -/
theorem norm_tailDiagInf_le (hs : Summable fun k => ‖tailSymbol S μ k‖ ^ 2) :
    ‖tailDiagInf w S μ hs‖ ≤ √(∑' k, ‖tailSymbol S μ k‖ ^ 2) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

end CrossNorm

section ScalarTail



/-- The scalar tail constant `ψ₁(N) = ∑_{k > N} k⁻²`, written over `ℕ` by the shift
`k ↦ k + N + 1`. -/
def psi1 (N : ℕ) : ℝ := ∑' k : ℕ, (1 : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 2

/-- The terms of `ψ₁(N)` are summable (the `p`-series with `p = 2`, shifted). -/
theorem summable_psi1_term (N : ℕ) :
    Summable fun k : ℕ => (1 : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 2 :=
  ((summable_nat_add_iff (N + 1)).2 (Real.summable_one_div_nat_pow.2 one_lt_two)).congr
    fun k => by rw [← add_assoc]


/-- The telescoping comparison `1 / (n + 1) ^ 2 ≤ 2 / (2n + 1) - 2 / (2(n + 1) + 1)`. -/
private theorem one_div_sq_le_telescope (n : ℕ) :
    (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 ≤
      2 / (2 * (n : ℝ) + 1) - 2 / (2 * ((n + 1 : ℕ) : ℝ) + 1) := by
  push_cast
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith

/-- **The rational majorant** `ψ₁(N) ≤ 2 / (2N + 1)` (telescoping). -/
theorem psi1_le (N : ℕ) : psi1 N ≤ 2 / (2 * N + 1) := by
  have key : ∀ k : ℕ, (1 : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 2 ≤
      2 / (2 * ((k + N : ℕ) : ℝ) + 1) - 2 / (2 * ((k + 1 + N : ℕ) : ℝ) + 1) := fun k => by
    rw [show k + 1 + N = k + N + 1 by omega]
    exact one_div_sq_le_telescope (k + N)
  refine Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun n => ?_
  refine ((Finset.sum_le_sum fun k _ => key k).trans_eq
    (Finset.sum_range_sub' (fun k => 2 / (2 * ((k + N : ℕ) : ℝ) + 1)) n)).trans ?_
  have h0 : (0 : ℝ) ≤ 2 / (2 * ((n + N : ℕ) : ℝ) + 1) := by positivity
  show 2 / (2 * ((0 + N : ℕ) : ℝ) + 1) - 2 / (2 * ((n + N : ℕ) : ℝ) + 1) ≤ 2 / (2 * (N : ℝ) + 1)
  rw [zero_add]
  linarith

end ScalarTail

end RadiiPolynomial.WeightedLp

end
