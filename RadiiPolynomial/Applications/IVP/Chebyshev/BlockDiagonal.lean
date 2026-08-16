import RadiiPolynomial.Applications.IVP.Chebyshev.Operator
import RadiiPolynomial.Operators.BlockDiagonal.Lift

/-!
# Block-Diagonal Defect CLM on XCheb (ℤ-Indexed Chebyshev Space)

Lifts the defect of a `SystemBlockDiagData` (with tailDiag = 0) to a continuous linear map
on `XCheb ν L` (ℤ-indexed Chebyshev space).

The composed approximate derivative is `composedApproxCheb D = id - defectChebCLM D`.
Norm bound: `‖defectChebCLM D‖ ≤ finiteBlockMatrixNorm(D.finBlock)`.
-/

open scoped BigOperators Topology NNReal ENNReal
open RadiiPolynomial ChebyshevIVP

noncomputable section

namespace ChebyshevIVP

variable {ν : PosReal} {L N : ℕ} [NeZero L] [Fact (1 ≤ (ν : ℝ))]

/-! ## Coefficient extraction from XCheb -/

/-- Extract ℕ-indexed coefficients from XCheb as SystemCoeff. -/
def toCoeffCheb (h : XCheb ν L) : SystemCoeff L :=
  fun l n => l1Chebyshev.toSeq (h l) (↑n : ℤ)

/-! ## General lpOneAlg helpers for finitely-supported ℤ-indexed elements -/

/-- Norm of a finitely-supported lpOneAlg element equals the ℕ-finite sum.
If `f(k) = 0` for `k < 0` and `‖f(↑n)‖ = 0` for `n > N`, then
`‖f‖ = ∑ n : Fin(N+1), ‖f(↑n)‖`. Uses ℤ = ℕ+ ⊔ ℕ- decomposition. -/
lemma lpOneAlg.norm_eq_natFinSum_of_finSupp (f : lpOneAlg ℤ (ScaledRealZ ν)) (N : ℕ)
    (h_neg : ∀ m : ℕ, (f : ∀ k : ℤ, ScaledRealZ ν k) (Int.negSucc m) = 0)
    (h_tail : ∀ n : ℕ, N < n → ‖(f : ∀ k : ℤ, ScaledRealZ ν k) (↑n : ℤ)‖ = 0) :
    ‖f‖ = ∑ n : Fin (N + 1), ‖(f : ∀ k : ℤ, ScaledRealZ ν k) (↑(n : ℕ) : ℤ)‖ := by
  set g : ℤ → ℝ := fun k => ‖(f : ∀ k : ℤ, ScaledRealZ ν k) k‖ with hg_def
  have hg_summ : Summable g := lpOneAlg.summable_norm f
  rw [lpOneAlg.norm_eq_tsum f,
    tsum_of_nat_of_neg_add_one
      (hg_summ.comp_injective (fun _ _ h => by omega))
      (hg_summ.comp_injective (fun _ _ h => by omega))]
  -- Negative part = 0
  rw [show ∑' n : ℕ, g (-(↑n + 1)) = 0 from by
    have : (fun n : ℕ => g (-(↑n + 1))) = fun _ => 0 := by
      ext n; show ‖(f : ∀ k, ScaledRealZ ν k) (-(↑n + 1 : ℤ))‖ = 0
      have : -(↑n + 1 : ℤ) = Int.negSucc n := by omega
      rw [this, h_neg]; simp
    rw [this]; exact tsum_zero]
  -- ℕ-tsum → finite sum
  rw [add_zero, tsum_eq_sum (s := Finset.range (N + 1))
    (fun n hn => h_tail n (by simp [Finset.mem_range] at hn; omega))]
  rw [← Fin.sum_univ_eq_sum_range]

/-- Chebyshev coefficient subseries bound: `∑_{k≤N} |toSeq(f)(↑k)| * ν^k ≤ ‖f‖`. -/
lemma l1Chebyshev_finSum_le_norm (f : l1Chebyshev ν) :
    ∑ k : Fin (N + 1), |l1Chebyshev.toSeq f (↑(k : ℕ) : ℤ)| * (ν : ℝ) ^ (k : ℕ) ≤ ‖f‖ := by
  have heq : ∀ k : Fin (N + 1),
      |l1Chebyshev.toSeq f (↑(k : ℕ) : ℤ)| * (ν : ℝ) ^ (k : ℕ) = ‖f (↑(k : ℕ) : ℤ)‖ := fun k => by
    rw [lpOneAlg.norm_eq_abs_toReal_mul_weight f (↑(k:ℕ) : ℤ)]
    congr 1; simp [ScaledRealZ.norm_lpAlgRingData_ofReal, Int.natAbs_natCast]
  simp_rw [heq]
  calc ∑ k : Fin (N + 1), ‖f (↑(k : ℕ) : ℤ)‖
      = ∑' k : Fin (N + 1), ‖f (↑(k : ℕ) : ℤ)‖ := (tsum_fintype _).symm
    _ ≤ ∑' m : ℤ, ‖f m‖ := tsum_comp_le_tsum_of_inj
          (lpOneAlg.summable_norm f) (fun _ => norm_nonneg _)
          (fun a b h => by ext; omega)
    _ = ‖f‖ := (lpOneAlg.norm_eq_tsum _).symm

/-! ## Defect on XCheb: function + Memℓp -/

/-- Raw ℤ-indexed sequence for the defect action: `D.actionFinite` on k ≥ 0, zero on k < 0. -/
private def defectCheb_seq (D : SystemBlockDiagData L N)
    (c : SystemCoeff L) (l : Fin L) : ∀ k : ℤ, ScaledRealZ ν k :=
  fun k => match k with
  | (n : ℕ) => lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑n) (D.actionFinite c l n)
  | Int.negSucc _ => 0

section defectMemlp
omit [NeZero L] [Fact (1 ≤ (ν : ℝ))]

/-- The defect sequence is in ℓ¹ (finitely supported on modes 0..N). -/
private lemma defectCheb_memℓp (D : SystemBlockDiagData L N)
    (c : SystemCoeff L) (l : Fin L) :
    Memℓp (defectCheb_seq (ν := ν) D c l) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  apply Summable.of_nat_of_neg_add_one
  · -- Positive: finitely supported (actionFinite = 0 for n > N)
    refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => ?_
    have hlt : N < n := by simp [Finset.mem_range] at hn; omega
    show ‖defectCheb_seq D c l (↑n : ℤ)‖ = 0
    simp only [defectCheb_seq, SystemBlockDiagData.actionFinite_tail _ _ _ _ hlt,
      lpAlgRingData.ofReal_zero, norm_zero]
  · -- Negative: all zeros
    have : (fun n : ℕ => ‖defectCheb_seq (ν := ν) D c l (-(↑n + 1 : ℤ))‖) =
        fun _ => (0 : ℝ) := by
      ext n; have h : -(↑n + 1 : ℤ) = Int.negSucc n := by omega
      rw [h]; simp [defectCheb_seq]
    rw [this]; exact summable_zero

end defectMemlp

/-- The defect applied to XCheb, returning a well-typed XCheb element. -/
def defectCheb_apply (D : SystemBlockDiagData L N) (h : XCheb ν L) : XCheb ν L := fun l =>
  ⟨⟨defectCheb_seq D (toCoeffCheb h) l, defectCheb_memℓp D (toCoeffCheb h) l⟩⟩

/-! ### Linearity -/

omit [NeZero L] in
lemma defectCheb_apply_add (D : SystemBlockDiagData L N) (h₁ h₂ : XCheb ν L) :
    defectCheb_apply D (h₁ + h₂) = defectCheb_apply D h₁ + defectCheb_apply D h₂ := by
  funext l; apply lpOneAlg.ext_toRealSeq; funext k
  show lpAlgRingData.toReal k (defectCheb_seq D (toCoeffCheb (h₁ + h₂)) l k) =
    lpAlgRingData.toReal k (defectCheb_seq D (toCoeffCheb h₁) l k) +
    lpAlgRingData.toReal k (defectCheb_seq D (toCoeffCheb h₂) l k)
  cases k with
  | ofNat n =>
    simp only [defectCheb_seq]
    rw [show toCoeffCheb (h₁ + h₂) = fun l n => toCoeffCheb h₁ l n + toCoeffCheb h₂ l n from by
      ext l n; simp [toCoeffCheb, l1Chebyshev.toSeq, lpOneAlg.toRealSeq_add]]
    exact (SystemBlockDiagData.actionFinite_add D _ _).symm ▸ rfl
  | negSucc _ => simp [defectCheb_seq, lpAlgRingData.toReal_zero]

omit [NeZero L] in
lemma defectCheb_apply_smul (D : SystemBlockDiagData L N) (r : ℝ) (h : XCheb ν L) :
    defectCheb_apply D (r • h) = r • defectCheb_apply D h := by
  funext l; apply lpOneAlg.ext_toRealSeq; funext k
  show lpAlgRingData.toReal k (defectCheb_seq D (toCoeffCheb (r • h)) l k) =
    r * lpAlgRingData.toReal k (defectCheb_seq D (toCoeffCheb h) l k)
  cases k with
  | ofNat n =>
    simp only [defectCheb_seq]
    rw [show toCoeffCheb (r • h) = fun l n => r * toCoeffCheb h l n from by
      ext l n; simp [toCoeffCheb, l1Chebyshev.toSeq, lpOneAlg.toRealSeq_smul]]
    exact (SystemBlockDiagData.actionFinite_smul D r _).symm ▸ rfl
  | negSucc _ => simp [defectCheb_seq, lpAlgRingData.toReal_zero]

/-! ### Norm bound -/

/-- Norm bound: `‖defectCheb(D, h)‖ ≤ finiteBlockMatrixNorm(D.finBlock) * ‖h‖`.

Proof outline: the defect is finitely supported (modes 0..N), so its ℤ-norm equals
the weighted finite sum of `|actionFinite(c)(l)(n)| * ν^n`. This is bounded by
`blockRowNorm * ‖h‖` per component (same bound as the ℕ-indexed case via
`finWeightedMatrixNorm_mulVec_le`), then aggregated to `finiteBlockMatrixNorm * ‖h‖`. -/
lemma defectCheb_norm_le (D : SystemBlockDiagData L N) (h : XCheb ν L) :
    ‖defectCheb_apply D h‖ ≤ finiteBlockMatrixNorm ν D.finBlock * ‖h‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (finiteBlockMatrixNorm_nonneg (ν := ν) _)
    (norm_nonneg _))).2 fun l => ?_
  set c := toCoeffCheb h
  -- ℤ-norm → finite sum (defect is finitely supported)
  have h_norm : ‖defectCheb_apply D h l‖ =
      ∑ n : Fin (N + 1), |D.actionFinite c l (n : ℕ)| * (ν : ℝ) ^ (n : ℕ) := by
    conv_lhs => rw [lpOneAlg.norm_eq_natFinSum_of_finSupp (defectCheb_apply D h l) N
      (fun m => rfl)
      (fun n hn => by
        show ‖(defectCheb_seq D c l (↑n : ℤ) : ScaledRealZ ν _)‖ = 0
        simp [defectCheb_seq, SystemBlockDiagData.actionFinite_tail _ _ _ _ hn,
          lpAlgRingData.ofReal_zero])]
    exact Finset.sum_congr rfl fun ⟨n, _⟩ _ => rfl
  -- Unfold actionFinite + apply general weighted norm bound + aggregate
  rw [h_norm]
  have h_unfold : ∀ n : Fin (N + 1), D.actionFinite c l (↑n : ℕ) =
      ∑ j : Fin L, ∑ k : Fin (N + 1), D.finBlock l j n k * c j ↑k := fun n =>
    SystemBlockDiagData.actionFinite_finite D c l ↑n (by omega)
  simp_rw [h_unfold]
  exact (D.actionFinite_weighted_norm_le (ν := ν) c l fun j =>
    (l1Chebyshev_finSum_le_norm (h j)).trans (norm_le_pi_norm h j)).trans
    (mul_le_mul_of_nonneg_right (Finset.le_sup' _ (Finset.mem_univ l)) (norm_nonneg h))

/-! ### CLM construction -/

/-- The defect as a CLM on XCheb. -/
def defectChebCLM (D : SystemBlockDiagData L N) : XCheb ν L →L[ℝ] XCheb ν L :=
  LinearMap.mkContinuous
    { toFun := defectCheb_apply D
      map_add' := defectCheb_apply_add D
      map_smul' := defectCheb_apply_smul D }
    (finiteBlockMatrixNorm ν D.finBlock)
    (defectCheb_norm_le D)

/-- Linear map underlying the composed approximate derivative on XCheb. -/
private def composedApprox_lm (D : SystemBlockDiagData L N) :
    XCheb ν L →ₗ[ℝ] XCheb ν L where
  toFun h := h - defectCheb_apply D h
  map_add' h₁ h₂ := by rw [defectCheb_apply_add]; abel
  map_smul' r h := by rw [defectCheb_apply_smul]; simp [smul_sub]

private lemma composedApprox_bound (D : SystemBlockDiagData L N) (h : XCheb ν L) :
    ‖composedApprox_lm D h‖ ≤ (1 + finiteBlockMatrixNorm ν D.finBlock) * ‖h‖ :=
  calc ‖h - defectCheb_apply D h‖
      ≤ ‖h‖ + ‖defectCheb_apply D h‖ := norm_sub_le h _
    _ ≤ ‖h‖ + finiteBlockMatrixNorm ν D.finBlock * ‖h‖ :=
        add_le_add le_rfl (defectCheb_norm_le D h)
    _ = (1 + finiteBlockMatrixNorm ν D.finBlock) * ‖h‖ := by ring

/-- The composed approximate derivative on XCheb: `h ↦ h - defect(h)`. -/
def composedApproxCheb (D : SystemBlockDiagData L N) : XCheb ν L →L[ℝ] XCheb ν L :=
  LinearMap.mkContinuous (composedApprox_lm D)
    (1 + finiteBlockMatrixNorm ν D.finBlock) (composedApprox_bound D)

@[simp] lemma composedApproxCheb_apply (D : SystemBlockDiagData L N) (h : XCheb ν L) :
    composedApproxCheb D h = h - defectCheb_apply D h := rfl

/-! ### Key properties -/

/-- Z₀ bound: `‖id - composedApproxCheb D‖ ≤ Z₀`. -/
lemma composedApproxCheb_Z₀ (D : SystemBlockDiagData L N) {Z₀ : ℝ}
    (hZ₀ : finiteBlockMatrixNorm ν D.finBlock ≤ Z₀) :
    ‖ContinuousLinearMap.id ℝ (XCheb ν L) - composedApproxCheb (ν := ν) D‖ ≤ Z₀ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (le_trans
    (finiteBlockMatrixNorm_nonneg (ν := ν) _) hZ₀) fun x => ?_
  -- Use sub_apply to evaluate: (id - composedApprox)(x) = x - (x - defect(x)) = defect(x)
  rw [sub_apply, ContinuousLinearMap.id_apply, composedApproxCheb_apply,
    sub_sub_cancel]
  exact (defectCheb_norm_le D x).trans (mul_le_mul_of_nonneg_right hZ₀ (norm_nonneg x))

/-- Tail identity: composedApproxCheb acts as identity on real values at modes n > N. -/
lemma composedApproxCheb_tail_toReal (D : SystemBlockDiagData L N)
    (h : XCheb ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    lpOneAlg.toRealSeq (composedApproxCheb (ν := ν) D h l) (↑n : ℤ) =
      lpOneAlg.toRealSeq (h l) (↑n : ℤ) := by
  -- composedApproxCheb D h = h - defectCheb_apply D h (by rfl)
  -- composedApproxCheb D h l = (h - defect(h)) l = h l - defect(h) l
  show lpOneAlg.toRealSeq ((h l - defectCheb_apply D h l : l1Chebyshev ν)) (↑n : ℤ) = _
  -- toRealSeq(a - b) = toRealSeq(a) - toRealSeq(b)
  have hsub : lpOneAlg.toRealSeq (h l - defectCheb_apply D h l : l1Chebyshev ν) (↑n : ℤ) =
      lpOneAlg.toRealSeq (h l) (↑n : ℤ) - lpOneAlg.toRealSeq (defectCheb_apply D h l) (↑n : ℤ) :=
    congr_fun (lpOneAlg.toRealSeq_add (h l) (-defectCheb_apply D h l)) (↑n : ℤ) ▸ by
      simp [sub_eq_add_neg, lpOneAlg.toRealSeq]; rfl
  rw [hsub]
  -- defect on tail = 0
  have h_zero : lpOneAlg.toRealSeq (defectCheb_apply D h l) (↑n : ℤ) = 0 := by
    show lpAlgRingData.toReal (↑n : ℤ) (defectCheb_seq D (toCoeffCheb h) l (↑n : ℤ)) = 0
    simp [defectCheb_seq, SystemBlockDiagData.actionFinite_tail _ _ _ _ hn,
      lpAlgRingData.toReal_ofReal]
  rw [h_zero, sub_zero]

/-! ## BlockDiagLift Instance for XCheb -/

/-- The Chebyshev system space `XCheb ν L = (l1Chebyshev ν)^L` supports block-diagonal
defect lifting via ℕ-coefficient extraction (`toCoeffCheb`) and ℤ-embedding
(`defectCheb_apply`). -/
instance instBlockDiagLiftXCheb : BlockDiagLift (XCheb ν L) L ν where
  extractCoeff := toCoeffCheb
  liftDefect D h := defectCheb_apply D h
  liftDefect_add D h₁ h₂ := defectCheb_apply_add D h₁ h₂
  liftDefect_smul D r h := defectCheb_apply_smul D r h
  liftDefect_norm_le D h := defectCheb_norm_le D h

end ChebyshevIVP

end
