import RadiiPolynomial.Applications.IVP.Chebyshev.Operator
import RadiiPolynomial.Operators.BlockDiagonal.Lift
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided

/-!
# Block-Diagonal Defect CLM on XCheb (ℤ-Indexed Chebyshev Space)

Lifts the finite-block action `actionFinite` of a `SystemBlockDiagData` to a continuous
linear map on `XCheb ν L` (ℤ-indexed Chebyshev space). The tail part of the data is not
used; the intended input is a defect, whose tail model is `0`.

The lift is the Taylor lift on `XL1 ν L` (`instBlockDiagLiftXL1`) transported along the bundled
maps `l1Chebyshev.OneSided.restr : ℓ¹_ν(ℤ) →L ℓ¹_ν(ℕ)` (‖restr x‖ ≤ ‖x‖) and
`l1Chebyshev.natEmbed : ℓ¹_ν(ℕ) →L ℓ¹_ν(ℤ)` (an isometry): restrict each component to its
nonnegative modes, apply `D.actionFinite`, re-embed with zero negative modes.

The composed approximate derivative `composedApproxCheb D` is the generic
`BlockDiagLift.composedApproxCLM`; it equals `id − defectChebCLM D`
(`composedApproxCheb_eq_id_sub`).
Norm bound, pointwise form: `‖defectCheb_apply D h‖ ≤ finiteBlockMatrixNorm(D.finBlock) * ‖h‖`
(`defectCheb_norm_le`), from which `defectChebCLM` is built; the operator-norm form is not
stated separately.
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

/-! ## Defect on XCheb -/

/-- The defect applied to XCheb: the XL1 lift (`D.actionFinite` on `toCoeff`, rebuilt by `ofCoeff`)
of the restricted components `l1Chebyshev.OneSided.restr (h j)`, re-embedded by
`l1Chebyshev.natEmbed`. Under `[NeZero L]` this is `BlockDiagLift.liftDefect` at
`instBlockDiagLiftXL1`, transported (`instBlockDiagLiftXCheb`). -/
def defectCheb_apply (D : SystemBlockDiagData L N) (h : XCheb ν L) : XCheb ν L := fun l =>
  l1Chebyshev.natEmbed
    (ofCoeff (ν := ν) (D.actionFinite (toCoeff fun j => l1Chebyshev.OneSided.restr (h j)))
      (fun l => D.actionFinite_mem (toCoeff fun j => l1Chebyshev.OneSided.restr (h j)) l) l)

omit [NeZero L] in
/-- The restricted components have the ℕ-coefficients of `h`. -/
private lemma toCoeff_restr (h : XCheb ν L) :
    toCoeff (ν := ν) (fun j => l1Chebyshev.OneSided.restr (h j)) = toCoeffCheb h :=
  funext₂ fun j k => l1Chebyshev.OneSided.restr_toSeq (h j) k

/-! ### Coefficient faces of the defect -/

omit [NeZero L] in
/-- The defect on the nonnegative modes: the finite block action on the ℕ-coefficients. -/
theorem defectCheb_apply_toSeq_natCast (D : SystemBlockDiagData L N) (h : XCheb ν L)
    (l : Fin L) (n : ℕ) :
    l1Chebyshev.toSeq (defectCheb_apply D h l) (n : ℤ) = D.actionFinite (toCoeffCheb h) l n := by
  rw [defectCheb_apply, l1Chebyshev.natEmbed_toSeq_natCast]
  change toCoeff (ofCoeff (ν := ν) _ _) l n = _
  rw [toCoeff_ofCoeff, toCoeff_restr]

omit [NeZero L] in
/-- The defect vanishes on the negative modes. -/
theorem defectCheb_apply_toSeq_negSucc (D : SystemBlockDiagData L N) (h : XCheb ν L)
    (l : Fin L) (m : ℕ) :
    l1Chebyshev.toSeq (defectCheb_apply D h l) (Int.negSucc m) = 0 := by
  rw [defectCheb_apply, l1Chebyshev.natEmbed_toSeq_negSucc]

/-! ### Linearity -/

omit [NeZero L] in
lemma defectCheb_apply_add (D : SystemBlockDiagData L N) (h₁ h₂ : XCheb ν L) :
    defectCheb_apply D (h₁ + h₂) = defectCheb_apply D h₁ + defectCheb_apply D h₂ := by
  have hc : toCoeffCheb (h₁ + h₂) = fun l n => toCoeffCheb h₁ l n + toCoeffCheb h₂ l n :=
    funext₂ fun l n => l1Chebyshev.toSeq_add (h₁ l) (h₂ l) n
  refine funext fun l => l1Chebyshev.ext_natCast_negSucc (fun n => ?_) (fun m => ?_)
  · rw [Pi.add_apply, l1Chebyshev.toSeq_add, defectCheb_apply_toSeq_natCast,
      defectCheb_apply_toSeq_natCast, defectCheb_apply_toSeq_natCast, hc]
    exact congr_fun (congr_fun (SystemBlockDiagData.actionFinite_add D _ _) l) n
  · rw [Pi.add_apply, l1Chebyshev.toSeq_add, defectCheb_apply_toSeq_negSucc,
      defectCheb_apply_toSeq_negSucc, defectCheb_apply_toSeq_negSucc, add_zero]

omit [NeZero L] in
lemma defectCheb_apply_smul (D : SystemBlockDiagData L N) (r : ℝ) (h : XCheb ν L) :
    defectCheb_apply D (r • h) = r • defectCheb_apply D h := by
  have hc : toCoeffCheb (r • h) = fun l n => r * toCoeffCheb h l n :=
    funext₂ fun l n => l1Chebyshev.toSeq_smul r (h l) n
  refine funext fun l => l1Chebyshev.ext_natCast_negSucc (fun n => ?_) (fun m => ?_)
  · rw [Pi.smul_apply, l1Chebyshev.toSeq_smul, defectCheb_apply_toSeq_natCast,
      defectCheb_apply_toSeq_natCast, hc]
    exact congr_fun (congr_fun (SystemBlockDiagData.actionFinite_smul D r _) l) n
  · rw [Pi.smul_apply, l1Chebyshev.toSeq_smul, defectCheb_apply_toSeq_negSucc,
      defectCheb_apply_toSeq_negSucc, mul_zero]

/-! ### Norm bound -/

/-- Norm bound: `‖defectCheb(D, h)‖ ≤ finiteBlockMatrixNorm(D.finBlock) * ‖h‖`, inherited from
the XL1 lift (`liftDefect_norm_le` at `instBlockDiagLiftXL1`) through `‖restr x‖ ≤ ‖x‖` and the
isometry `natEmbed`. -/
lemma defectCheb_norm_le (D : SystemBlockDiagData L N) (h : XCheb ν L) :
    ‖defectCheb_apply D h‖ ≤ finiteBlockMatrixNorm ν D.finBlock * ‖h‖ := by
  have hr : ‖(fun j => l1Chebyshev.OneSided.restr (h j) : XL1 ν L)‖ ≤ ‖h‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg h)).2 fun j =>
      (l1Chebyshev.OneSided.norm_restr_le (h j)).trans (norm_le_pi_norm h j)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (finiteBlockMatrixNorm_nonneg (ν := ν) _)
    (norm_nonneg _))).2 fun l => ?_
  rw [defectCheb_apply, l1Chebyshev.norm_natEmbed]
  exact (norm_le_pi_norm _ l).trans ((@BlockDiagLift.liftDefect_norm_le (XL1 ν L) _ _ L _ ν
    instBlockDiagLiftXL1 N D _).trans
      (mul_le_mul_of_nonneg_left hr (finiteBlockMatrixNorm_nonneg (ν := ν) _)))

/-! ## BlockDiagLift Instance for XCheb -/

/-- The Chebyshev system space `XCheb ν L = (l1Chebyshev ν)^L` supports block-diagonal
defect lifting: the XL1 lift `instBlockDiagLiftXL1` of the restricted components
(`l1Chebyshev.OneSided.restr`), re-embedded by `l1Chebyshev.natEmbed` (= `defectCheb_apply`). -/
instance instBlockDiagLiftXCheb : BlockDiagLift (XCheb ν L) L ν where
  liftDefect D h := fun l => l1Chebyshev.natEmbed
    (@BlockDiagLift.liftDefect (XL1 ν L) _ _ L _ ν instBlockDiagLiftXL1 _ D
      (fun j => l1Chebyshev.OneSided.restr (h j)) l)
  liftDefect_add D h₁ h₂ := defectCheb_apply_add D h₁ h₂
  liftDefect_smul D r h := defectCheb_apply_smul D r h
  liftDefect_norm_le D h := defectCheb_norm_le D h

/-- The XCheb instance's defect action is `defectCheb_apply`, so `simp` normalizes
`composedApproxCheb D h` to `h - defectCheb_apply D h` through the generic
`composedApproxCLM_apply`. -/
@[simp] lemma liftDefect_eq_defectCheb_apply (D : SystemBlockDiagData L N) (h : XCheb ν L) :
    @BlockDiagLift.liftDefect (XCheb ν L) _ _ L _ ν instBlockDiagLiftXCheb N D h =
      defectCheb_apply D h := rfl

/-! ### CLM construction -/

/-- The defect as a CLM on XCheb. -/
def defectChebCLM (D : SystemBlockDiagData L N) : XCheb ν L →L[ℝ] XCheb ν L :=
  LinearMap.mkContinuous
    { toFun := defectCheb_apply D
      map_add' := defectCheb_apply_add D
      map_smul' := defectCheb_apply_smul D }
    (finiteBlockMatrixNorm ν D.finBlock)
    (defectCheb_norm_le D)

/-- The composed approximate derivative on XCheb, `h ↦ h - defect(h)`: the generic
`BlockDiagLift.composedApproxCLM` at the XCheb instance. -/
abbrev composedApproxCheb (D : SystemBlockDiagData L N) : XCheb ν L →L[ℝ] XCheb ν L :=
  BlockDiagLift.composedApproxCLM (X := XCheb ν L) (ν := ν) D

@[simp] lemma composedApproxCheb_apply (D : SystemBlockDiagData L N) (h : XCheb ν L) :
    composedApproxCheb D h = h - defectCheb_apply D h := rfl

/-- `composedApproxCheb D = id − defectChebCLM D`. -/
theorem composedApproxCheb_eq_id_sub (D : SystemBlockDiagData L N) :
    composedApproxCheb (ν := ν) D = ContinuousLinearMap.id ℝ _ - defectChebCLM D := by
  ext1 h; rfl

/-! ### Key properties -/

/-- Z₀ bound: `‖id - composedApproxCheb D‖ ≤ Z₀`. -/
lemma composedApproxCheb_Z₀ (D : SystemBlockDiagData L N) {Z₀ : ℝ}
    (hZ₀ : finiteBlockMatrixNorm ν D.finBlock ≤ Z₀) :
    ‖ContinuousLinearMap.id ℝ (XCheb ν L) - composedApproxCheb (ν := ν) D‖ ≤ Z₀ := by
  rw [composedApproxCheb]
  exact BlockDiagLift.composedApprox_Z₀ (X := XCheb ν L) D hZ₀

/-- The composed approximate derivative on the nonnegative modes. -/
theorem composedApproxCheb_toSeq_natCast (D : SystemBlockDiagData L N) (h : XCheb ν L)
    (l : Fin L) (n : ℕ) :
    l1Chebyshev.toSeq (composedApproxCheb (ν := ν) D h l) (n : ℤ) =
      l1Chebyshev.toSeq (h l) n - D.actionFinite (toCoeffCheb h) l n := by
  rw [composedApproxCheb_apply, Pi.sub_apply, l1Chebyshev.toSeq_sub,
    defectCheb_apply_toSeq_natCast]

/-- The composed approximate derivative is the identity on the negative modes. -/
theorem composedApproxCheb_toSeq_negSucc (D : SystemBlockDiagData L N) (h : XCheb ν L)
    (l : Fin L) (m : ℕ) :
    l1Chebyshev.toSeq (composedApproxCheb (ν := ν) D h l) (Int.negSucc m) =
      l1Chebyshev.toSeq (h l) (Int.negSucc m) := by
  rw [composedApproxCheb_apply, Pi.sub_apply, l1Chebyshev.toSeq_sub,
    defectCheb_apply_toSeq_negSucc, sub_zero]

/-- Tail identity: composedApproxCheb acts as identity on real values at modes n > N. -/
lemma composedApproxCheb_tail_toReal (D : SystemBlockDiagData L N)
    (h : XCheb ν L) (l : Fin L) (n : ℕ) (hn : N < n) :
    lpOneAlg.toRealSeq (composedApproxCheb (ν := ν) D h l) (↑n : ℤ) =
      lpOneAlg.toRealSeq (h l) (↑n : ℤ) := by
  rw [← l1Chebyshev.toSeq, composedApproxCheb_toSeq_natCast,
    SystemBlockDiagData.actionFinite_tail _ _ _ _ hn, sub_zero]; rfl

end ChebyshevIVP

end
