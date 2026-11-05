import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.Reality
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The unweighted real pairing on a weighted ℓ² carrier

For a weight with `h1 : ∀ n, 1 ≤ w n`, the coefficient inclusion
`embedL2 h1 : WeightedLp M (WeightedScalar ℂ w) 2 →L[ℂ] lp (fun _ => ℂ) 2` is bounded by `1`, and
`pairing h1 x y = Re ⟪embedL2 x, embedL2 y⟫ = ∑ Re (conj xₙ yₙ)` (`pairing_eq_tsum`) is a bounded
symmetric real bilinear form with the Cauchy–Schwarz bound `abs_pairing_le`. The head forms
(`pairing_headProj_comm`, `pairing_eq_headProj_left`, `abs_pairing_le_headProj`), the finite adjoint
`pairing_finMatrixCLM`, the restriction `pairingR` to the real subspace and the reality of head
sums on it (`ofReal_pairing_headProj_eq_sum`) complete the service.
-/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp

section Inclusion

/-! ### The inclusion `ι : X → ℓ²(M; ℂ)` (no index class) -/

variable {M : Type*} {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- The coefficient family of `x` is square summable, with norm at most `1 * ‖x‖`: the pointwise
bound `‖coeff x n‖ ≤ ‖coeff x n‖ * w n = ‖x n‖` is the only use of `h1`. -/
private theorem embed_mem_bound (h1 : ∀ n, 1 ≤ w n) (x : X) :
    ∃ h : Memℓp (coeff x) 2, ‖(⟨coeff x, h⟩ : lp (fun _ : M => ℂ) 2)‖ ≤ 1 * ‖x‖ :=
  memℓp_norm_le_of_le_comp (F := fun _ : M => ℂ) Function.injective_id x (coeff x) zero_le_one
    fun n => by
      rw [id, norm_apply_eq, WeightedScalar.fiberTrivialization_weight, one_mul]
      exact le_mul_of_one_le_right (norm_nonneg _) (h1 n)

/-- **The inclusion** `ι : X →L[ℂ] ℓ²(M; ℂ)`, `ι x = coeff x`, with constant `1`. -/
def embedL2 (h1 : ∀ n, 1 ≤ w n) : X →L[ℂ] lp (fun _ : M => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨coeff x, (embed_mem_bound h1 x).choose⟩
      map_add' := fun x y => lp.ext (coeff_add x y)
      map_smul' := fun c x => lp.ext (coeff_smul c x) }
    1 fun x => (embed_mem_bound h1 x).choose_spec

variable (h1 : ∀ n, 1 ≤ w n)

/-- `ι x` has the coefficients of `x`: `embedL2 h1 x n = coeff x n`. -/
theorem embedL2_apply (x : X) (n : M) : embedL2 h1 x n = coeff x n := rfl

/-- `ι` does not increase norms: `‖embedL2 h1 x‖ ≤ ‖x‖`. -/
theorem norm_embedL2_apply_le (x : X) : ‖embedL2 h1 x‖ ≤ ‖x‖ :=
  (embed_mem_bound h1 x).choose_spec.trans_eq (one_mul _)

end Inclusion

section Pairing

/-! ### The pairing, its bound and symmetry (no index class) -/

variable {M : Type*} {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- The `ℂ`-linear `ι` commutes with real scalars. -/
private theorem embedL2_real_smul (h1 : ∀ n, 1 ≤ w n) (r : ℝ) (x : X) :
    embedL2 h1 (r • x) = r • embedL2 h1 x :=
  ContinuousLinearMap.map_smul_of_tower (embedL2 h1) r x

/-- **The unweighted real pairing** `b(x, y) = ⟪ι x, ι y⟫_ℝ`, with constant `1`. -/
def pairing (h1 : ∀ n, 1 ≤ w n) : X →L[ℝ] X →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ (fun x y : X => inner ℝ (embedL2 h1 x) (embedL2 h1 y))
    (fun x₁ x₂ y => by rw [map_add, inner_add_left])
    (fun c x y => by rw [embedL2_real_smul, real_inner_smul_left, smul_eq_mul])
    (fun x y₁ y₂ => by rw [map_add, inner_add_right])
    (fun c x y => by rw [embedL2_real_smul, real_inner_smul_right, smul_eq_mul])).mkContinuous₂ 1
    fun x y => (abs_real_inner_le_norm (embedL2 h1 x) (embedL2 h1 y)).trans <|
      (mul_le_mul (norm_embedL2_apply_le h1 x) (norm_embedL2_apply_le h1 y) (norm_nonneg _)
        (norm_nonneg _)).trans_eq (by rw [one_mul])

variable (h1 : ∀ n, 1 ≤ w n)

/-- The pairing is the real inner product of the inclusions: `b(x, y) = ⟪ι x, ι y⟫_ℝ`. -/
theorem pairing_apply (x y : X) :
    pairing h1 x y = inner ℝ (embedL2 h1 x) (embedL2 h1 y) := rfl

/-- The pairing in coordinates: `b(x, y) = ∑' n, Re (conj x_n * y_n)`. -/
theorem pairing_eq_tsum (x y : X) :
    pairing h1 x y = ∑' n, (starRingEnd ℂ (coeff x n) * coeff y n).re := by
  rw [pairing_apply, lp.inner_eq_tsum]
  exact tsum_congr fun n => by rw [Complex.inner, mul_comm, embedL2_apply, embedL2_apply]

/-- Cauchy–Schwarz for the pairing: `|b(x, y)| ≤ ‖x‖ ‖y‖`. -/
theorem abs_pairing_le (x y : X) : |pairing h1 x y| ≤ ‖x‖ * ‖y‖ :=
  (abs_real_inner_le_norm _ _).trans
    (mul_le_mul (norm_embedL2_apply_le h1 x) (norm_embedL2_apply_le h1 y) (norm_nonneg _)
      (norm_nonneg _))

/-- The pairing is symmetric: `b(x, y) = b(y, x)`. -/
theorem pairing_comm (x y : X) : pairing h1 x y = pairing h1 y x :=
  (pairing_apply h1 x y).trans (real_inner_comm _ _)

end Pairing

section Invariance

/-! ### `K`-invariance and the restriction to `XR` (`[InvolutiveNeg M]`) -/

variable {M : Type*} [InvolutiveNeg M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (hw : ∀ n, w (-n) = w n) (h1 : ∀ n, 1 ≤ w n)

/-- **The restricted pairing** on `XR`, at the type `bilinearComp` produces. -/
def pairingR :=
  (pairing h1).bilinearComp (realSub hw).subtypeL (realSub hw).subtypeL

end Invariance

section Rows

/-! ### Row restriction (`[DecidableEq M]`) -/

variable {M : Type*} [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (h1 : ∀ n, 1 ≤ w n) (T : Finset M)

/-- `P_T` is symmetric for the pairing. No summability is used. -/
theorem pairing_headProj_comm (x y : X) :
    pairing h1 (headProj (𝕜 := ℂ) T x) y = pairing h1 x (headProj (𝕜 := ℂ) T y) := by
  rw [pairing_eq_tsum, pairing_eq_tsum]
  exact tsum_congr fun n => by
    rw [coeff_headProj, coeff_headProj]
    by_cases h : n ∈ T
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, map_zero, zero_mul, mul_zero]

/-- **Row restriction**: for `x` supported on `T`,
`b(ψ, x) = b(P_T ψ, x)`. -/
theorem pairing_eq_headProj_left (ψ x : X) (hx : ∀ n ∉ T, coeff x n = 0) :
    pairing h1 ψ x = pairing h1 (headProj (𝕜 := ℂ) T ψ) x := by
  have hPx : headProj (𝕜 := ℂ) T x = x := ext_coeff <| funext fun n => by
    rw [coeff_headProj]
    by_cases h : n ∈ T
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, hx n h]
  rw [pairing_headProj_comm, hPx]

/-- The leakage bound `|b(ψ, x)| ≤ ‖P_T ψ‖ ‖x‖` for `x` supported on `T`. -/
theorem abs_pairing_le_headProj (ψ x : X) (hx : ∀ n ∉ T, coeff x n = 0) :
    |pairing h1 ψ x| ≤ ‖headProj (𝕜 := ℂ) T ψ‖ * ‖x‖ :=
  (congrArg abs (pairing_eq_headProj_left h1 T ψ x hx)).trans_le (abs_pairing_le h1 _ _)

end Rows

section PairingMatrix

variable {M : Type*} [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- The finite adjoint under the unweighted pairing: `b(ψ, A x) = b(Aᴴ ψ, x)`. -/
theorem pairing_finMatrixCLM (h1 : ∀ n, 1 ≤ w n) (F : Finset M) (A : M → M → ℂ) (ψ x : X) :
    pairing h1 ψ (finMatrixCLM F A x) =
      pairing h1 (finMatrixCLM F (fun i j => starRingEnd ℂ (A j i)) ψ) x := by
  rw [pairing_eq_tsum, pairing_eq_tsum,
    tsum_eq_sum (s := F) fun n hn => by
      rw [coeff_finMatrixCLM, ite_eq_right hn, mul_zero, Complex.zero_re],
    tsum_eq_sum (s := F) fun n hn => by
      rw [coeff_finMatrixCLM, ite_eq_right hn, map_zero, zero_mul, Complex.zero_re],
    ← Complex.re_sum, ← Complex.re_sum]
  have hL : ∀ n ∈ F, starRingEnd ℂ (coeff ψ n) * coeff (finMatrixCLM F A x) n =
      ∑ j ∈ F, starRingEnd ℂ (coeff ψ n) * (A n j * coeff x j) := fun n hn => by
    rw [coeff_finMatrixCLM, ite_eq_left hn, Finset.mul_sum]
  have hR : ∀ j ∈ F, starRingEnd ℂ (coeff (finMatrixCLM F (fun i j => starRingEnd ℂ (A j i)) ψ) j) *
      coeff x j = ∑ n ∈ F, starRingEnd ℂ (coeff ψ n) * (A n j * coeff x j) := fun j hj => by
    rw [coeff_finMatrixCLM, ite_eq_left hj, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by rw [map_mul, Complex.conj_conj]; ring
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_comm]

end PairingMatrix

section PairingReal

variable {M : Type*} [InvolutiveNeg M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- On `XR`, the complex head sum `∑_{j ∈ F} conj y_j x_j` over a symmetric head is real, and it is
the head pairing `b(y, P_F x)`. -/
theorem ofReal_pairing_headProj_eq_sum (hw : ∀ n, w (-n) = w n) (h1 : ∀ n, 1 ≤ w n)
    {F : Finset M} (hF : ∀ n, -n ∈ F ↔ n ∈ F) {y x : X} (hy : y ∈ realSub hw)
    (hx : x ∈ realSub hw) :
    ((pairing h1 y (headProj (𝕜 := ℂ) F x) : ℝ) : ℂ) =
      ∑ j ∈ F, starRingEnd ℂ (coeff y j) * coeff x j := by
  have hsum : pairing h1 y (headProj (𝕜 := ℂ) F x) =
      (∑ j ∈ F, starRingEnd ℂ (coeff y j) * coeff x j).re := by
    rw [pairing_eq_tsum, tsum_eq_sum (s := F) fun n hn => by
      rw [coeff_headProj, ite_eq_right hn, mul_zero, Complex.zero_re], Complex.re_sum]
    exact Finset.sum_congr rfl fun j hj => by rw [coeff_headProj, ite_eq_left hj]
  have hreal : starRingEnd ℂ (∑ j ∈ F, starRingEnd ℂ (coeff y j) * coeff x j) =
      ∑ j ∈ F, starRingEnd ℂ (coeff y j) * coeff x j := by
    rw [map_sum]
    refine Finset.sum_nbij' Neg.neg Neg.neg (fun j hj => (hF j).2 hj) (fun j hj => (hF j).2 hj)
      (fun j _ => neg_neg j) (fun j _ => neg_neg j) fun j _ => ?_
    rw [map_mul, (mem_realSub_iff_coeff hw).1 hy j, (mem_realSub_iff_coeff hw).1 hx j]
  rw [hsum]
  exact Complex.conj_eq_iff_re.1 hreal

end PairingReal

end RadiiPolynomial.WeightedLp

end
