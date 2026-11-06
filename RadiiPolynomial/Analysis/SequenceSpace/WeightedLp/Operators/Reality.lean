import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.FiniteBlock

/-!
# Conjugate reflection and the real subspace of a weighted ℓ² carrier

On `X = WeightedLp M (WeightedScalar ℂ w) 2` with a negation-invariant weight
`hw : ∀ n, w (-n) = w n`, the conjugate reflection `conjReflL hw : X →L[ℝ] X`,
`(K x)ₙ = conj x₋ₙ`, is ℝ-linear and conjugate-linear over `ℂ` (`conjReflL_smul`), an involution
(`conjReflL_conjReflL`) and an isometry (`norm_conjReflL`, `isometry_conjReflL`); its fixed points
are the conjugate-symmetric families (`conjReflL_eq_self_iff_coeff`). Its fixed ℝ-subspace
`realSub hw = {x : x₋ₙ = conj xₙ}` (`mem_realSub_iff_coeff`) is complete, and a `K`-commuting
operator restricts to it (`restrictReal`). The commutation faces with `K`: diagonal multipliers
with conjugate-symmetric symbols, `tailDiag` and the finite-head diagonal `headDiag`, the head and
tail projections of a symmetric head, and finite matrices with `A (-i) (-j) = conj (A i j)`.

These are carrier faces: none needs a product on `X`. The commutation of `K` with the
row-bounded product `convCLM` is in `Operators/RealityConvolution.lean`, the only face that
imports `WeightedLp/Convolution`.
-/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp

section Reflection

variable {M : Type*} [InvolutiveNeg M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- The reflected family `n ↦ θ_n (conj (coeff x (-n)))` lies in `X`, with norm at most
`1 * ‖x‖`. This is where the negation invariance `hw` of the weight is used. -/
private theorem conjRefl_memℓp (hw : ∀ n, w (-n) = w n) (x : X) :
    ∃ h : Memℓp (fun n => FiberTrivialization.equiv (E := WeightedScalar ℂ w) n
        (starRingEnd ℂ (coeff x (-n)))) 2,
      ‖(⟨_, h⟩ : X)‖ ≤ 1 * ‖x‖ :=
  memℓp_norm_le_of_le_comp neg_injective x _ zero_le_one fun n => by
    rw [FiberTrivialization.norm_equiv_apply, norm_apply_eq, Complex.norm_conj,
      WeightedScalar.fiberTrivialization_weight, WeightedScalar.fiberTrivialization_weight, hw,
      one_mul]

/-- The conjugate reflection as a real-linear map. -/
private def conjReflLM (hw : ∀ n, w (-n) = w n) : X →ₗ[ℝ] X where
  toFun x := ⟨_, (conjRefl_memℓp hw x).choose⟩
  map_add' x y := ext_coeff <| funext fun n => (coeff_mk_equiv _ _ n).trans <| by
    simp only [coeff_add, Pi.add_apply, coeff_mk_equiv, map_add]
  map_smul' r x := ext_coeff <| funext fun n => (coeff_mk_equiv _ _ n).trans <| by
    simp only [RingHom.id_apply, RCLike.real_smul_eq_coe_smul (K := ℂ), coeff_smul,
      Pi.smul_apply, smul_eq_mul, coeff_mk_equiv, map_mul, RCLike.conj_ofReal]

/-- **The conjugate reflection** `K : X →L[ℝ] X`, `(K x)_n = conj x_{-n}`, with constant `1`. -/
def conjReflL (hw : ∀ n, w (-n) = w n) : X →L[ℝ] X :=
  (conjReflLM hw).mkContinuous 1 fun x => (conjRefl_memℓp hw x).choose_spec

variable (hw : ∀ n, w (-n) = w n)

/-- The conjugate reflection in coordinates. -/
@[simp] theorem coeff_conjReflL (x : X) (n : M) :
    coeff (conjReflL hw x) n = starRingEnd ℂ (coeff x (-n)) :=
  coeff_mk_equiv _ _ n

/-- `K` is conjugate-linear over `ℂ`. -/
theorem conjReflL_smul (c : ℂ) (x : X) :
    conjReflL hw (c • x) = starRingEnd ℂ c • conjReflL hw x :=
  ext_coeff <| funext fun n => by
    rw [coeff_conjReflL, coeff_smul, coeff_smul, Pi.smul_apply, Pi.smul_apply, coeff_conjReflL,
      smul_eq_mul, smul_eq_mul, map_mul]

/-- `K` is an involution: `K (K x) = x`. -/
theorem conjReflL_conjReflL (x : X) : conjReflL hw (conjReflL hw x) = x :=
  ext_coeff <| funext fun n => by
    rw [coeff_conjReflL, coeff_conjReflL, neg_neg, Complex.conj_conj]

/-- `K` preserves the norm: the bound `‖K x‖ ≤ ‖x‖` of the construction, applied to `x` and to
`K x` (`conjReflL_conjReflL`). -/
theorem norm_conjReflL (x : X) : ‖conjReflL hw x‖ = ‖x‖ := by
  have h (y : X) : ‖conjReflL hw y‖ ≤ ‖y‖ := by
    simpa only [one_mul] using
      (conjReflL hw).le_of_opNorm_le (LinearMap.mkContinuous_norm_le _ zero_le_one _) y
  exact le_antisymm (h x) ((congrArg norm (conjReflL_conjReflL hw x)).symm.trans_le (h _))

/-- **`K` is an isometry** of `X`. -/
theorem isometry_conjReflL : Isometry (conjReflL hw) :=
  AddMonoidHomClass.isometry_of_norm (conjReflL hw) (norm_conjReflL hw)

/-- **The fixed points of `K`** in coordinates: `K x = x` iff `x₋ₙ = conj xₙ` for every `n`. -/
theorem conjReflL_eq_self_iff_coeff (x : X) :
    conjReflL hw x = x ↔ ∀ n, coeff x (-n) = starRingEnd ℂ (coeff x n) := by
  refine ⟨fun h n => ?_, fun h => ext_coeff <| funext fun n => ?_⟩
  · rw [← congrFun (congrArg coeff h) (-n), coeff_conjReflL, neg_neg]
  · rw [coeff_conjReflL, h, Complex.conj_conj]

/-! Two real structures on `X`. Instance search gives `lp.instNormedSpace` (module
`lp.instModuleSubtypePreLpMemAddSubgroup`) over the fibre `NormedSpace.complexToReal`. The global
carrier-level `NormedSpace.complexToReal` / `Module.complexToReal` (priority 900) gives a second
one. They agree by `rfl` at default transparency, not at instance transparency: `rw`/`simp` with
a lemma stated through `complexToReal` (`Complex.coe_smul`) does not fire on `X`, while its term
application does. Rewrite with the generic `IsScalarTower` lemma `RCLike.real_smul_eq_coe_smul`,
then `RCLike.ofReal_eq_complex_ofReal` for the coercion. -/
end Reflection

section RealSubspace

variable {M : Type*} [InvolutiveNeg M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- **The real subspace** `XR = Fix(K)`, the kernel of `K - id`. -/
def realSub (hw : ∀ n, w (-n) = w n) : Submodule ℝ X :=
  (conjReflL hw - ContinuousLinearMap.id ℝ X).ker

variable (hw : ∀ n, w (-n) = w n)

/-- `x ∈ XR` iff `K x = x`. -/
theorem mem_realSub {x : X} : x ∈ realSub hw ↔ conjReflL hw x = x := by
  rw [realSub, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply,
    ContinuousLinearMap.id_apply, sub_eq_zero]

/-- Membership in coordinates: `x_{-n} = conj x_n`. -/
theorem mem_realSub_iff_coeff {x : X} :
    x ∈ realSub hw ↔ ∀ n, coeff x (-n) = starRingEnd ℂ (coeff x n) :=
  (mem_realSub hw).trans (conjReflL_eq_self_iff_coeff hw x)

/-- `XR` is complete: it is the kernel of the continuous `K - id`. -/
instance completeSpace_realSub : CompleteSpace (realSub hw) :=
  ContinuousLinearMap.completeSpace_ker _

end RealSubspace

section Restriction

variable {M : Type*} [InvolutiveNeg M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (hw : ∀ n, w (-n) = w n)

/-- **Restriction to `XR`** of a real continuous linear map commuting with `K`. -/
def restrictReal (T : X →L[ℝ] X) (hT : ∀ x, conjReflL hw (T x) = T (conjReflL hw x)) :
    realSub hw →L[ℝ] realSub hw :=
  (T.comp (realSub hw).subtypeL).codRestrict (realSub hw) fun y =>
    (mem_realSub hw).2 ((hT y).trans (congrArg T ((mem_realSub hw).1 y.2)))

end Restriction

/-! ## The commutations with `K` -/

section TailSymbol

/-! ### The tail symbol (index class `Neg`) -/

variable {M : Type*} [Neg M]

/-- A symmetric head and a conjugate-symmetric symbol give a conjugate-symmetric tail
symbol. -/
theorem tailSymbol_neg {S : Set M} [DecidablePred (· ∈ S)] (hS : ∀ n, -n ∈ S ↔ n ∈ S)
    {μ : M → ℂ} (hμ : ∀ n, μ (-n) = starRingEnd ℂ (μ n)) (n : M) :
    tailSymbol S μ (-n) = starRingEnd ℂ (tailSymbol S μ n) := by
  by_cases h : n ∈ S
  · rw [tailSymbol_of_mem ((hS n).2 h), tailSymbol_of_mem h, map_zero]
  · rw [tailSymbol_of_notMem (mt (hS n).1 h), tailSymbol_of_notMem h, map_inv₀, hμ]

end TailSymbol

section Diagonal

/-! ### Diagonal multipliers and `tailDiag` -/

variable {M : Type*} [InvolutiveNeg M] {w : M → ℝ} [PosWeight w] (hw : ∀ n, w (-n) = w n)

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- A diagonal multiplier with a conjugate-symmetric symbol commutes with `K`. -/
theorem conjReflL_diagCLM {d : M → ℂ} (hd : BddAbove (Set.range fun n => ‖d n‖))
    (hsym : ∀ n, d (-n) = starRingEnd ℂ (d n)) (x : X) :
    conjReflL hw (diagCLM d hd x) = diagCLM d hd (conjReflL hw x) :=
  ext_coeff <| funext fun n => by
    rw [coeff_conjReflL, coeff_diagCLM, coeff_diagCLM, coeff_conjReflL, map_mul, hsym,
      Complex.conj_conj]

/-- `tailDiag S μ` is `diagCLM (tailSymbol S μ)`, so it commutes with `K`. -/
theorem conjReflL_tailDiag {S : Set M} [DecidablePred (· ∈ S)] (hS : ∀ n, -n ∈ S ↔ n ∈ S)
    {μ : M → ℂ} (hμ : ∀ n, μ (-n) = starRingEnd ℂ (μ n))
    (hd : BddAbove (Set.range fun k => ‖tailSymbol S μ k‖)) (x : X) :
    conjReflL hw (tailDiag S μ hd x) = tailDiag S μ hd (conjReflL hw x) :=
  conjReflL_diagCLM hw hd (tailSymbol_neg hS hμ) x

/-- `headDiag S μ` is `diagCLM (1_S μ)`: on a head closed under negation, with `μ` conjugate
symmetric on the head, it commutes with `K`. The symbol off the head is never read. -/
theorem conjReflL_headDiag (S : Finset M) (hS : ∀ n ∈ S, -n ∈ S) {μ : M → ℂ}
    (hμ : ∀ n ∈ S, μ (-n) = starRingEnd ℂ (μ n)) (x : X) :
    conjReflL hw (headDiag S μ x) = headDiag S μ (conjReflL hw x) :=
  conjReflL_diagCLM hw _ (fun n => by
    by_cases hn : n ∈ S
    · rw [Set.indicator_of_mem (Finset.mem_coe.2 (hS n hn)),
        Set.indicator_of_mem (Finset.mem_coe.2 hn), hμ n hn]
    · rw [Set.indicator_of_notMem (fun h => hn (neg_neg n ▸ hS (-n) (Finset.mem_coe.1 h))),
        Set.indicator_of_notMem (mt Finset.mem_coe.1 hn), map_zero]) x

end Diagonal

section Projection

/-! ### Projections and finite matrices on a symmetric head -/

variable {M : Type*} [InvolutiveNeg M] [DecidableEq M] {w : M → ℝ} [PosWeight w]
  (hw : ∀ n, w (-n) = w n)

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

/-- The head projection on a symmetric head commutes with `K`. -/
theorem conjReflL_headProj (F : Finset M) (hF : ∀ n, -n ∈ F ↔ n ∈ F) (x : X) :
    conjReflL hw (headProj (𝕜 := ℂ) F x) = headProj (𝕜 := ℂ) F (conjReflL hw x) :=
  ext_coeff <| funext fun n => by
    rw [coeff_conjReflL, coeff_headProj, coeff_headProj, coeff_conjReflL]
    by_cases h : n ∈ F
    · rw [ite_eq_left ((hF n).2 h), ite_eq_left h]
    · rw [ite_eq_right (mt (hF n).1 h), ite_eq_right h, map_zero]

/-- The tail projection on a symmetric head commutes with `K`. -/
theorem conjReflL_tailProj (F : Finset M) (hF : ∀ n, -n ∈ F ↔ n ∈ F) (x : X) :
    conjReflL hw (tailProj (𝕜 := ℂ) F x) = tailProj (𝕜 := ℂ) F (conjReflL hw x) :=
  ext_coeff <| funext fun n => by
    rw [coeff_conjReflL, coeff_tailProj, coeff_tailProj, coeff_conjReflL]
    by_cases h : n ∈ F
    · rw [ite_eq_left ((hF n).2 h), ite_eq_left h, map_zero]
    · rw [ite_eq_right (mt (hF n).1 h), ite_eq_right h]

/-- A finite matrix that is `K`-symmetric on `F × F` commutes with `K`. The `F`-sum
is reindexed by `j ↦ -j`. -/
theorem conjReflL_finMatrixCLM (F : Finset M) (hF : ∀ n, -n ∈ F ↔ n ∈ F) (A : M → M → ℂ)
    (hA : ∀ i ∈ F, ∀ j ∈ F, A (-i) (-j) = starRingEnd ℂ (A i j)) (x : X) :
    conjReflL hw (finMatrixCLM F A x) = finMatrixCLM F A (conjReflL hw x) :=
  ext_coeff <| funext fun n => by
    rw [coeff_conjReflL, coeff_finMatrixCLM, coeff_finMatrixCLM]
    by_cases h : n ∈ F
    · rw [ite_eq_left ((hF n).2 h), ite_eq_left h, map_sum]
      refine Finset.sum_nbij' Neg.neg Neg.neg (fun j hj => (hF j).2 hj) (fun j hj => (hF j).2 hj)
        (fun j _ => neg_neg j) (fun j _ => neg_neg j) fun j hj => ?_
      rw [map_mul, coeff_conjReflL, neg_neg, ← Complex.conj_conj (A n (-j)),
        ← hA n h (-j) ((hF j).2 hj), neg_neg]
    · rw [ite_eq_right (mt (hF n).1 h), ite_eq_right h, map_zero]

end Projection

section ZeroAtom

variable {M : Type*} [AddGroup M] [DecidableEq M] {w : M → ℝ} [PosWeight w]

local notation "X" => WeightedLp M (WeightedScalar ℂ w) 2

variable (hw : ∀ n, w (-n) = w n)

/-- A real atom at `0` lies in `XR`: `single 0 (r : ℂ) ∈ XR`. -/
theorem single_zero_mem_realSub (r : ℝ) : (single 0 (r : ℂ) : X) ∈ realSub hw := by
  refine (mem_realSub_iff_coeff hw).2 fun n => ?_
  simp only [coeff_single, Pi.single_apply, neg_eq_zero]
  split_ifs
  · exact (Complex.conj_ofReal r).symm
  · exact (map_zero _).symm

end ZeroAtom

end RadiiPolynomial.WeightedLp

end
