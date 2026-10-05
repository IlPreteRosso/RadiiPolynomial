import RadiiPolynomial.Applications.Galerkin.Face
import RadiiPolynomial.Core.Transport

/-!
# The diblock-copolymer carrier as an instance of the polynomial Galerkin face

Book Exercise 2.7.13 (a): the diblock-copolymer projection keeps the positive Chebyshev modes
`1, …, N` of an even sequence whose zero mode vanishes. This file provides the carrier side of that
exercise: the lift and projection, the centred constants of the cubic and the exercise's weighted norm.

* `J : (Fin N → ℝ) → FνN ν N` puts `x_k` at mode `k + 1` and `0` at mode `0`; it is the kept-mode
  embedding `Jσ (Fin.succEmb N)` (`J_eq_Jσ`), with left inverse `Tl`.
* `ιD = ιN ∘ J` and `πD = Tl ∘ πN` lift into and project out of the flip-fixed algebra; the product of
  three padded elements is the full triple sum over `k₁ + k₂ + k₃ = k` with `kᵢ ∈ [-N, N]`
  (`toSeq_mul_mul_ιN`), and the even padding of `J x` is the even extension with zero mode `0`
  (`evenLift_J`).
* The centred majorant of `x³` is `3 (2β + δ) δ` (`derivativeCentredBound_cube`); the exact rational
  instances `cube_centred_Q` and `cube_centred_lt_lipschitz_Q` (the centred constant is strictly below
  the uncentred Lipschitz route) are checked by `decide +kernel`.
* At `ν = 1` the exercise's weighted norm `2 Σ_k |x_k|` is `‖J x‖` (`diblockNorm_eq`), `‖ιD x‖`
  (`norm_ιD_eq`) and the norm of the positive-mode carrier `FνP N` read through `FνP.amb`
  (`FνP.diblockNorm_eq_amb`).
* The projection (2.52) `diblockF` is the polynomial face `polyFace` on `ιD1` (`diblockF_eq`); its
  `Z₂` bound in the weighted norm is `3 |λ| AΛnorm (2 normXBar + r) r`, where `AΛnorm` bounds
  `A ∘ Λ` and `normXBar` bounds `x̄` in that norm (`norm_fderiv_diblockF_sub_le`); the
  radii-polynomial theorem on `FνP` then gives the unique zero in the closed `r`-ball about `x̄`
  (`existsUnique_diblockF_zero`). These are the end theorems of the exercise, book-free.
-/

noncomputable section

open scoped BigOperators

namespace ExampleDiblock

open RadiiPolynomial RadiiPolynomial.Galerkin MvPolyBridge

/-- The weight `ν = 1`. -/
def ν₁ : PosReal := ⟨1, one_pos⟩

@[simp] theorem ν₁_coe : (ν₁ : ℝ) = 1 := rfl

instance : Fact (1 ≤ (ν₁ : ℝ)) := ⟨le_of_eq ν₁_coe.symm⟩

/-! ### The diblock inclusion `J = Jσ (Fin.succEmb N)` -/

section Diblock

variable {ν : PosReal} {N : ℕ}

/-- The positive-mode inclusion `J(x)₀ = 0`, `J(x)_{k+1} = x_k`. -/
def J : (Fin N → ℝ) →ₗ[ℝ] FνN ν N where
  toFun x := FνN.mk (Fin.cons 0 x)
  map_add' x y := FνN.ext fun k => by
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  map_smul' c x := FνN.ext fun k => by
    refine Fin.cases ?_ (fun i => ?_) k <;> simp

@[simp] theorem J_zero (x : Fin N → ℝ) : (J (ν := ν) x : FνN ν N) 0 = 0 := rfl
@[simp] theorem J_succ (x : Fin N → ℝ) (k : Fin N) :
    (J (ν := ν) x : FνN ν N) k.succ = x k := rfl

/-- `‖J x‖ = 2 Σ_k |x_k| ν^{k+1}`. -/
theorem norm_J (x : Fin N → ℝ) :
    ‖(J (ν := ν) x : FνN ν N)‖ = 2 * ∑ k : Fin N, |x k| * (ν : ℝ) ^ ((k : ℕ) + 1) := by
  rw [FνN.norm_eq, J_zero, abs_zero, zero_add]
  simp only [J_succ]

/-- The diblock inclusion is the kept-mode embedding along `Fin.succEmb N`. -/
theorem J_eq_Jσ (x : Fin N → ℝ) : (J (ν := ν) x : FνN ν N) = Jσ (Fin.succEmb N) x := by
  refine FνN.ext fun k => Fin.cases ?_ (fun i => ?_) k
  · exact (Function.extend_apply' x (0 : Fin (N + 1) → ℝ) 0 fun ⟨a, ha⟩ => Fin.succ_ne_zero a ha).symm
  · exact (Jσ_apply_emb (Fin.succEmb N) x i).symm

end Diblock

/-! ### The cubic nonlinearity and its centred constants (with `ℚ` mirrors) -/

section Constants

/-- The cubic nonlinearity `x ↦ x³` as computable syntax (`L = 1`). -/
def cubeQ : CompPoly 1 := .mul (.mul (.X 0) (.X 0)) (.X 0)

/-- `x³`: the centred majorant is `3 (2β + δ) δ`. -/
theorem derivativeCentredBound_cube {K : Type*} [Field K] (β δ : Fin 1 → K) :
    CompPoly.derivativeCentredBound cubeQ β δ = 3 * (2 * β 0 + δ 0) * δ 0 := by
  simp [CompPoly.derivativeCentredBound, cubeQ]
  ring

/-- The exact rational instance of `derivativeCentredBound_cube`, kernel-checked. -/
theorem cube_centred_Q :
    CompPoly.derivativeCentredBound cubeQ (fun _ => (3 / 2 : ℚ)) (fun _ => 1 / 10) =
      3 * (2 * (3 / 2) + 1 / 10) * (1 / 10) := by
  decide +kernel

/-- At `β = 3/2`, `δ = 1/10` the centred majorant of `x³` (`0.93`) is strictly below the uncentred
syntactic Lipschitz route `derivativeLipschitzBound x³ (β + δ) · δ` (`0.96`). -/
theorem cube_centred_lt_lipschitz_Q :
    CompPoly.derivativeCentredBound cubeQ (fun _ => (3 / 2 : ℚ)) (fun _ => 1 / 10) <
      CompPoly.derivativeLipschitzBound cubeQ (fun _ => (3 / 2 + 1 / 10 : ℚ)) * (1 / 10) := by
  decide +kernel

end Constants

/-! ### The diblock lift and projection -/

section DiblockCarrier

open l1Chebyshev

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] {N : ℕ}

/-- The positive-mode restriction `T y = (y_{k+1})_k`, a left inverse of `J`. -/
def Tl : FνN ν N →ₗ[ℝ] (Fin N → ℝ) where
  toFun y k := y k.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fact (1 ≤ (ν : ℝ))] in
theorem norm_J_Tl_le (y : FνN ν N) : ‖(J (ν := ν) (Tl y) : FνN ν N)‖ ≤ ‖y‖ := by
  rw [norm_J, FνN.norm_eq]
  exact le_add_of_nonneg_left (abs_nonneg _)

/-- `J` on the ambient sup-norm space (continuous by finite dimensionality). -/
def Jc : (Fin N → ℝ) →L[ℝ] FνN ν N := LinearMap.toContinuousLinearMap J

/-- `T` as a continuous linear map. -/
def Tc : FνN ν N →L[ℝ] (Fin N → ℝ) := LinearMap.toContinuousLinearMap Tl

/-- The diblock lift `(Fin N → ℝ) → symmetricSubalgebra`: zero mode `0`, positive modes `x`, even
padding. -/
def ιD : (Fin N → ℝ) →L[ℝ] symmetricSubalgebra ν := (ιN (ν := ν) (N := N)).toContinuousLinearMap.comp Jc

/-- The diblock projection `symmetricSubalgebra → (Fin N → ℝ)`: modes `1..N`. -/
def πD : symmetricSubalgebra ν →L[ℝ] (Fin N → ℝ) := Tc.comp πN

theorem ιD_apply (x : Fin N → ℝ) : (ιD (ν := ν) x : symmetricSubalgebra ν) = ιN (J x) := rfl

theorem πD_apply (a : symmetricSubalgebra ν) (k : Fin N) :
    (πD (N := N) a) k = toSeq (a : l1Chebyshev ν) (((k : ℕ) : ℤ) + 1) := by
  change toSeq (a : l1Chebyshev ν) (((k.succ : ℕ)) : ℤ) = _
  rw [Fin.val_succ, Nat.cast_succ]

/-- The full product of three padded elements, before any projection, is the triple sum over
`k₁ + k₂ + k₃ = k` with `kᵢ ∈ [-N, N]` (no intermediate truncation): the library lemma
`Galerkin.toSeq_mul_mul_ιN` under the example's name. -/
theorem toSeq_mul_mul_ιN (x y z : FνN ν N) (k : ℤ) :
    toSeq (((ιN x * ιN y * ιN z : symmetricSubalgebra ν)) : l1Chebyshev ν) k =
      ∑ k₁ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∑ k₂ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ∑ k₃ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          if k₁ + k₂ + k₃ = k then evenLift x k₁ * evenLift y k₂ * evenLift z k₃ else 0 :=
  RadiiPolynomial.Galerkin.toSeq_mul_mul_ιN x y z k

omit [Fact (1 ≤ (ν : ℝ))] in
/-- The even padding of `J x` is the even extension `x̂` with `x̂_0 = 0` and `x̂_{±(k+1)} = x_k`. -/
theorem evenLift_J (x : Fin N → ℝ) (m : ℤ) :
    evenLift (J (ν := ν) x) m =
      if h : 1 ≤ m.natAbs ∧ m.natAbs ≤ N then x ⟨m.natAbs - 1, by omega⟩ else 0 := by
  unfold evenLift
  by_cases hN : m.natAbs ≤ N
  · rw [dite_eq_left hN]
    rcases Nat.eq_zero_or_pos m.natAbs with h0 | hpos
    · rw [dite_eq_right (by omega),
        show (⟨m.natAbs, Nat.lt_succ_of_le hN⟩ : Fin (N + 1)) = 0 from Fin.ext h0]
      rfl
    · rw [dite_eq_left ⟨hpos, hN⟩,
        show (⟨m.natAbs, Nat.lt_succ_of_le hN⟩ : Fin (N + 1)) =
          Fin.succ ⟨m.natAbs - 1, by omega⟩ from Fin.ext (by simp; omega)]
      rfl
  · rw [dite_eq_right hN, dite_eq_right (by omega)]

/-- The diblock lift into the one-component algebra space `(symmetricSubalgebra ν)^1`. -/
def ιD1 : (Fin N → ℝ) →L[ℝ] (Fin 1 → symmetricSubalgebra ν) := ContinuousLinearMap.pi fun _ => ιD

/-- A diagonal operator on the ambient space. -/
def diagC (d : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun k => d k • ContinuousLinearMap.proj k

end DiblockCarrier

/-! ### The exercise's weighted norm `2 Σ_k |x_k|` at `ν = 1` -/

section DiblockNorm

variable {N : ℕ}

/-- The exercise's weighted norm `2 Σ_k |x_k|` is the carrier norm of `J x` at `ν = 1`. -/
theorem diblockNorm_eq (x : Fin N → ℝ) :
    2 * ∑ k, |x k| = ‖(J (ν := ν₁) x : FνN ν₁ N)‖ := by
  rw [norm_J, ν₁_coe]
  simp

theorem norm_ιD_eq (x : Fin N → ℝ) :
    ‖(ιD (ν := ν₁) x : l1Chebyshev.symmetricSubalgebra ν₁)‖ = 2 * ∑ k, |x k| := by
  rw [ιD_apply, norm_ιN, diblockNorm_eq]

/-- Projection side: `2 Σ_k |(a • πD w)_k| ≤ |a| ‖w‖` (`‖T‖ ≤ 1` on `J`-norms, `‖πN‖ ≤ 1`). -/
theorem diblockNorm_smul_πD_le (a : ℝ) (w : l1Chebyshev.symmetricSubalgebra ν₁) :
    2 * ∑ k, |(a • πD (N := N) w) k| ≤ |a| * ‖w‖ := by
  rw [diblockNorm_eq, map_smul, norm_smul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ((norm_J_Tl_le (πN w)).trans ?_) (abs_nonneg a)
  exact (ContinuousLinearMap.le_of_opNorm_le _ norm_πN_le w).trans_eq (one_mul _)

theorem norm_ιD1 (x : Fin N → ℝ) :
    ‖(ιD1 (ν := ν₁) x : Fin 1 → l1Chebyshev.symmetricSubalgebra ν₁)‖ = 2 * ∑ k, |x k| := by
  rw [show (ιD1 (ν := ν₁) x : Fin 1 → l1Chebyshev.symmetricSubalgebra ν₁) = fun _ => ιD x from rfl,
    pi_norm_const, norm_ιD_eq]

end DiblockNorm

/-! ### The positive-mode carrier `FνP N` (`Fin N → ℝ` normed by `‖J x‖` at `ν = 1`) -/

set_option linter.unusedVariables false in
/-- The positive-mode carrier: `Fin N → ℝ` normed by `‖J x‖` (at `ν = 1`, the exercise's weighted
norm `2 Σ_k |x_k|`). -/
def FνP (N : ℕ) : Type := Fin N → ℝ

namespace FνP

variable {N : ℕ}

instance : AddCommGroup (FνP N) := inferInstanceAs (AddCommGroup (Fin N → ℝ))
instance : Module ℝ (FνP N) := inferInstanceAs (Module ℝ (Fin N → ℝ))

/-- `J` on the synonym. -/
def Jp : FνP N →ₗ[ℝ] FνN ν₁ N := J

theorem Jp_injective : Function.Injective (Jp (N := N)) := fun _ _ h => congrArg Tl h

instance : NormedAddCommGroup (FνP N) :=
  NormedAddCommGroup.induced (FνP N) (FνN ν₁ N) (Jp (N := N)) Jp_injective
instance : NormedSpace ℝ (FνP N) := NormedSpace.induced ℝ (FνP N) (FνN ν₁ N) (Jp (N := N))
instance : FiniteDimensional ℝ (FνP N) := inferInstanceAs (FiniteDimensional ℝ (Fin N → ℝ))

/-- The identity `FνP N ≃L (Fin N → ℝ)` (two norms on one vector space). -/
def amb : FνP N ≃L[ℝ] (Fin N → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun x := x
      invFun x := x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv _ := rfl
      right_inv _ := rfl }

theorem diblockNorm_eq_amb (y : Fin N → ℝ) : 2 * ∑ k, |y k| = ‖amb.symm y‖ :=
  diblockNorm_eq y

end FνP

section DiblockMap

variable {N : ℕ}

/-- The even extension `x̂` (`x̂_0 = 0`, `x̂_{±(k+1)} = x_k`). -/
def diblockExt (x : Fin N → ℝ) : ℤ → ℝ := fun j =>
  if h : 1 ≤ j.natAbs ∧ j.natAbs ≤ N then x ⟨j.natAbs - 1, by omega⟩ else 0

/-- The full triple convolution over `k₁ + k₂ + k₃ = k`, `kᵢ ∈ [-N, N]`. -/
def diblockConv (x : Fin N → ℝ) (k : ℤ) : ℝ :=
  ∑ k₁ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∑ k₂ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    ∑ k₃ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      if k₁ + k₂ + k₃ = k then diblockExt x k₁ * diblockExt x k₂ * diblockExt x k₃ else 0

/-- The diblock-copolymer projection (2.52). -/
def diblockF (lam sig : ℝ) (x : Fin N → ℝ) : Fin N → ℝ := fun k =>
  (-(((k : ℕ) : ℝ) + 1) ^ 4 + lam * (((k : ℕ) : ℝ) + 1) ^ 2 - lam * sig) * x k -
    lam * (((k : ℕ) : ℝ) + 1) ^ 2 * diblockConv x (((k : ℕ) : ℤ) + 1)

theorem diblockExt_eq_evenLift_J {ν : PosReal} (x : Fin N → ℝ) (m : ℤ) :
    diblockExt x m = evenLift (J (ν := ν) x) m := by
  rw [evenLift_J]
  rfl

theorem diblockConv_eq_πD {ν : PosReal} [Fact (1 ≤ (ν : ℝ))] (x : Fin N → ℝ) (k : Fin N) :
    diblockConv x (((k : ℕ) : ℤ) + 1) =
      πD ((fun u (l : Fin 1) => ((fun _ : Fin 1 => cubeQ) l).evalBanach u) (ιD1 (ν := ν) x) 0) k := by
  rw [πD_apply, show ((fun u (l : Fin 1) => ((fun _ : Fin 1 => cubeQ) l).evalBanach u)
      (ιD1 (ν := ν) x) 0 : l1Chebyshev.symmetricSubalgebra ν) = ιD x * ιD x * ιD x from rfl,
    ιD_apply, toSeq_mul_mul_ιN]
  simp only [diblockConv, diblockExt_eq_evenLift_J (ν := ν)]

theorem diblockF_eq (lam sig : ℝ) (Λ : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))
    (hΛ : ∀ x k, Λ x k = (((k : ℕ) : ℝ) + 1) ^ 2 * x k) :
    diblockF lam sig = polyFace
      (diagC fun k : Fin N => -(((k : ℕ) : ℝ) + 1) ^ 4 + lam * (((k : ℕ) : ℝ) + 1) ^ 2 - lam * sig)
      (LinearMap.toContinuousLinearMap Λ) ((-lam) • ((πD (ν := ν₁)).comp (ContinuousLinearMap.proj 0)))
      (ιD1 (ν := ν₁)) (fun _ => cubeQ) := by
  funext x k
  change _ - lam * (((k : ℕ) : ℝ) + 1) ^ 2 * diblockConv x (((k : ℕ) : ℤ) + 1) = _
  rw [diblockConv_eq_πD (ν := ν₁)]
  simp only [polyFace, Pi.add_apply, LinearMap.coe_toContinuousLinearMap', hΛ, diagC,
    ContinuousLinearMap.pi_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem differentiable_diblockF (lam sig : ℝ) :
    Differentiable ℝ (diblockF (N := N) lam sig) := by
  rw [diblockF_eq lam sig (diagC fun k : Fin N => (((k : ℕ) : ℝ) + 1) ^ 2).toLinearMap
    (fun x k => by simp [diagC])]
  exact fun x => (hasFDerivAt_polyFace _ _ _ _ _ x).differentiableAt

/-- `Z₂` of Exercise 2.7.13 (a), in the weighted norm `2 Σ_k |x_k|`. -/
theorem norm_fderiv_diblockF_sub_le {lam sig : ℝ} {xBar : Fin N → ℝ}
    (A Λ : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))
    (hΛ : ∀ x k, Λ x k = (((k : ℕ) : ℝ) + 1) ^ 2 * x k)
    {AΛnorm normXBar r : ℝ} (hAΛnn : 0 ≤ AΛnorm)
    (hAΛ : ∀ h, 2 * ∑ k, |A (Λ h) k| ≤ AΛnorm * (2 * ∑ k, |h k|))
    (hxBar : 2 * ∑ k, |xBar k| ≤ normXBar) :
    ∀ c, 2 * ∑ k, |(c - xBar) k| ≤ r → ∀ h,
      2 * ∑ k, |A (fderiv ℝ (diblockF lam sig) c h - fderiv ℝ (diblockF lam sig) xBar h) k| ≤
        3 * |lam| * AΛnorm * (2 * normXBar + r) * r * (2 * ∑ k, |h k|) := by
  intro c hc h
  rw [diblockF_eq lam sig Λ hΛ, fderiv_polyFace_sub_apply, LinearMap.coe_toContinuousLinearMap',
    smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  have hD := norm_jacCLM_sub_le_centred (fun _ => cubeQ) (ιD1 (ν := ν₁) c) (ιD1 xBar)
    (fun _ => normXBar) (fun _ => r) (M := 3 * (2 * normXBar + r) * r)
    (fun _ => (derivativeCentredBound_cube _ _).le) (fun _ => (norm_ιD_eq xBar).trans_le hxBar)
    (fun _ => by
      show ‖(ιD c : l1Chebyshev.symmetricSubalgebra ν₁) - ιD xBar‖ ≤ r
      rw [← map_sub, norm_ιD_eq]; exact hc)
  refine (hAΛ _).trans ((mul_le_mul_of_nonneg_left ((diblockNorm_smul_πD_le _ _).trans
    (mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ 0).trans ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hD (norm_nonneg _)))) (abs_nonneg _))) hAΛnn).trans_eq ?_)
  rw [abs_neg, norm_ιD1]
  ring

/-- Exercise 2.7.13 (a): the diblock projection has a unique zero in the closed `r`-ball about `x̄`
(uniqueness is relative to that ball). -/
theorem existsUnique_diblockF_zero {lam sig : ℝ} {xBar : Fin N → ℝ}
    (A Λ : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))
    (hΛ : ∀ x k, Λ x k = (((k : ℕ) : ℝ) + 1) ^ 2 * x k)
    {Y₀ Z₀ AΛnorm normXBar r : ℝ} (hr : 0 < r) (hAΛnn : 0 ≤ AΛnorm)
    (hY₀ : 2 * ∑ k, |A (diblockF lam sig xBar) k| ≤ Y₀)
    (hZ₀ : ∀ h, 2 * ∑ k, |(h - A (fderiv ℝ (diblockF lam sig) xBar h)) k| ≤
      Z₀ * (2 * ∑ k, |h k|))
    (hAΛ : ∀ h, 2 * ∑ k, |A (Λ h) k| ≤ AΛnorm * (2 * ∑ k, |h k|))
    (hxBar : 2 * ∑ k, |xBar k| ≤ normXBar)
    (hp : 3 * |lam| * AΛnorm * r ^ 3 + 6 * |lam| * normXBar * AΛnorm * r ^ 2 -
      (1 - Z₀) * r + Y₀ < 0) :
    ∃! xTilde, 2 * ∑ k, |(xTilde - xBar) k| ≤ r ∧ diblockF lam sig xTilde = 0 :=
  rp_transport_local FνP.amb (W := fun y => 2 * ∑ k, |y k|) FνP.diblockNorm_eq_amb
    (DF := fderiv ℝ (diblockF lam sig)) A (fderiv ℝ (diblockF lam sig) xBar).toLinearMap
    (Z₁ := 0) (Z₂ := fun ρ => 3 * |lam| * AΛnorm * (2 * normXBar + ρ)) hr
    (fun x _ => (differentiable_diblockF lam sig x).hasFDerivAt.hasFDerivWithinAt) hY₀ hZ₀
    (fun h => by simp)
    (norm_fderiv_diblockF_sub_le A Λ hΛ hAΛnn hAΛ hxBar)
    (by simp only [generalRadiiPolynomial]; linarith)

end DiblockMap

end ExampleDiblock

end
