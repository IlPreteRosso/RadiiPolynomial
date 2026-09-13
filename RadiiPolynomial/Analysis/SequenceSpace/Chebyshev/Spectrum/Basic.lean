import RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Joukowski
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The physical Chebyshev algebra and its complex characters — basic layer

Root of the Chebyshev spectrum branch. The carrier is the *production* symmetric
subalgebra `l1Chebyshev.symmetricSubalgebra ν` (`Physical ν`); no shadow carrier is
introduced. `Character ν` is the type of continuous `ℂ`-valued characters of it,
`restriction` produces one from an annulus point by Laurent evaluation, `mode`
supplies the symmetric Laurent modes `eₙ + e₋ₙ`, and `retract` exposes the existing
symmetrization with its symmetric codomain. The two extensionality theorems —
`linear_ext` (modes determine continuous linear maps) and `character_ext` (the
Joukowski generator determines a character) — are what the classification rests on.

Closes the first layer of the "spectrum as a space" gap: production bundles no
character object for the Chebyshev geometry at all.
-/

noncomputable section

namespace RadiiPolynomial.PhysicalSpectrum

open lpOneAlg CrossGeometry

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]

abbrev Physical := l1Chebyshev.symmetricSubalgebra ν
abbrev Character := Physical ν →A[ℝ] ℂ

def restriction (z : ℂ) (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)) : Character ν :=
  (l1Chebyshev.evalLaurentC ν z hz).comp (l1Chebyshev.symmetricSubalgebra ν).valA

@[simp] theorem restriction_gen (z : ℂ)
    (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)) :
    restriction ν z hz (joukowskiGenSymm ν) = joukowski z := by
  change l1Chebyshev.evalLaurentC ν z hz (joukowskiGen ν) = _
  simp only [joukowskiGen, map_smul, map_add, l1Chebyshev.evalLaurentC_single,
    zpow_neg_one, zpow_one, joukowski, Complex.real_smul]
  norm_num
  ring

/-- Restriction identifies exactly inversion pairs, including the branch
points ±1, where the pair consists of a single point. -/
theorem restriction_eq_iff (z w : ℂ)
    (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ))
    (hw : (ν : ℝ)⁻¹ ≤ ‖w‖ ∧ ‖w‖ ≤ (ν : ℝ)) :
    restriction ν z hz = restriction ν w hw ↔ w = z ∨ w = z⁻¹ := by
  constructor
  · intro h
    have hg := DFunLike.congr_fun h (joukowskiGenSymm ν)
    rw [restriction_gen, restriction_gen, joukowski, joukowski] at hg
    have hz0 := lpOneAlg.ne_zero_of_annulus ν hz
    have hw0 := lpOneAlg.ne_zero_of_annulus ν hw
    have hf : (w - z) * (w - z⁻¹) = 0 := by
      field_simp at hg ⊢
      linear_combination -hg
    exact (mul_eq_zero.mp hf).imp sub_eq_zero.mp sub_eq_zero.mp
  · rintro (rfl | rfl)
    · rfl
    · ext a
      exact (l1Chebyshev.evalLaurentC_inv_of_isSymmetric ν z hz hw a.val a.property).symm

/-- Symmetric Laurent modes in the physical carrier; mode zero is `2`. -/
def mode (n : ℕ) : Physical ν :=
  ⟨single (n : ℤ) 1 + single (-(n : ℤ)) 1, by
    intro k
    simp only [toRealSeq_add, Pi.add_apply, toRealSeq_single,
      neg_eq_iff_eq_neg, neg_neg]
    ring⟩

@[simp] theorem mode_zero : mode ν 0 = (1 : Physical ν) + 1 := by
  apply Subtype.ext
  change single (0 : ℤ) 1 + single (-(0 : ℤ)) 1 = (1 : l1Chebyshev ν) + 1
  rw [neg_zero, ← one_eq_single_zero]

theorem mode_one : mode ν 1 = (2 : ℝ) • joukowskiGenSymm ν := by
  apply Subtype.ext
  change single 1 1 + single (-1) 1 =
    (2 : ℝ) • ((2 : ℝ)⁻¹ • (single 1 1 + single (-1) 1) : l1Chebyshev ν)
  simp [smul_smul]

theorem mode_recurrence (n : ℕ) :
    mode ν 1 * mode ν (n + 1) = mode ν (n + 2) + mode ν n := by
  apply Subtype.ext
  change (single (1 : ℤ) 1 + single (-1) 1) *
      (single ((n + 1 : ℕ) : ℤ) 1 + single (-((n + 1 : ℕ) : ℤ)) 1) =
    (single ((n + 2 : ℕ) : ℤ) 1 + single (-((n + 2 : ℕ) : ℤ)) 1) +
      (single (n : ℤ) 1 + single (-(n : ℤ)) 1)
  rw [add_mul, mul_add, mul_add, single_mul_single, single_mul_single,
    single_mul_single, single_mul_single]
  simp only [one_mul]
  rw [show (1 : ℤ) + (n + 1 : ℕ) = (n + 2 : ℕ) by omega,
    show (1 : ℤ) + -(n + 1 : ℕ) = -(n : ℤ) by omega,
    show (-1 : ℤ) + (n + 1 : ℕ) = (n : ℤ) by omega,
    show (-1 : ℤ) + -(n + 1 : ℕ) = -(n + 2 : ℕ) by omega]
  abel

theorem norm_mode_le (n : ℕ) : ‖mode ν n‖ ≤ 2 * (ν : ℝ) ^ n := by
  change ‖(mode ν n).val‖ ≤ _
  dsimp only [mode]
  refine (norm_add_le _ _).trans ?_
  rw [l1Chebyshev.norm_single, l1Chebyshev.norm_single]
  simp [Int.natAbs_natCast, Int.natAbs_neg, two_mul]

/-- Existing symmetrization, with its physical codomain exposed. -/
def retract : l1Chebyshev ν →L[ℝ] Physical ν :=
  (l1Chebyshev.symmetrize_CLM (ν := ν)).codRestrict
    (l1Chebyshev.symmetricSubalgebra ν).toSubmodule
    fun a => l1Chebyshev.symmetrize_isSymmetric a

@[simp] theorem retract_coe (a : l1Chebyshev ν) :
    (retract ν a : l1Chebyshev ν) = l1Chebyshev.symmetrize a := rfl

@[simp] theorem retract_val (a : Physical ν) : retract ν a.val = a :=
  Subtype.ext (l1Chebyshev.symmetrize_eq_self_of_isSymmetric a.val a.property)

@[simp] theorem retract_single_zero : retract ν (single 0 1) = 1 := by
  rw [← one_eq_single_zero]
  exact retract_val ν 1

@[simp] theorem retract_single_neg (n : ℕ) :
    retract ν (single (Int.negSucc n) 1) = 0 :=
  Subtype.ext (l1Chebyshev.symmetrize_single_negSucc n 1)

@[simp] theorem retract_single_pos (n : ℕ) :
    retract ν (single ((n + 1 : ℕ) : ℤ) 1) = mode ν (n + 1) := by
  apply Subtype.ext
  apply lpOneAlg.ext_toRealSeq
  funext k
  change l1Chebyshev.toSeq (l1Chebyshev.symmetrize _) k = _
  rw [l1Chebyshev.symmetrize_toSeq, l1Chebyshev.toSeq_single]
  simp only [mode, toRealSeq_add, Pi.add_apply, toRealSeq_single]
  change (if (k.natAbs : ℤ) = (n + 1 : ℕ) then (1 : ℝ) else 0) =
    (if k = (n + 1 : ℕ) then 1 else 0) + (if k = -(n + 1 : ℕ) then 1 else 0)
  rcases Int.natAbs_eq k with hk | hk <;>
    split_ifs <;> first | omega | norm_num

/-- Continuous linear maps on the physical carrier are determined by modes. -/
theorem linear_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ ψ : Physical ν →L[ℝ] E} (h0 : φ 1 = ψ 1)
    (h : ∀ n : ℕ, φ (mode ν (n + 1)) = ψ (mode ν (n + 1))) : φ = ψ := by
  have heq : φ.comp (retract ν) = ψ.comp (retract ν) := by
    apply lpOneAlg.continuousLinearMap_ext
    intro k
    simp only [ContinuousLinearMap.comp_apply]
    cases k with
    | ofNat n =>
      cases n with
      | zero =>
        change φ (retract ν (single 0 1)) = ψ (retract ν (single 0 1))
        simpa only [retract_single_zero] using h0
      | succ n =>
        change φ (retract ν (single ((n + 1 : ℕ) : ℤ) 1)) =
          ψ (retract ν (single ((n + 1 : ℕ) : ℤ) 1))
        simpa only [retract_single_pos] using h n
    | negSucc n => simp
  ext a
  simpa only [ContinuousLinearMap.comp_apply, retract_val] using
    DFunLike.congr_fun heq a.val

/-- Every complex character is determined by the normalized physical
coordinate `g = (e₁ + e₋₁)/2`. -/
theorem character_ext {φ ψ : Character ν}
    (h : φ (joukowskiGenSymm ν) = ψ (joukowskiGenSymm ν)) : φ = ψ := by
  have hm : ∀ n : ℕ, φ (mode ν n) = ψ (mode ν n) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp
    | one => simp only [mode_one, map_smul, h]
    | more n h0 h1 =>
      have hp := congrArg φ (mode_recurrence ν n)
      have hq := congrArg ψ (mode_recurrence ν n)
      simp only [map_mul, map_add] at hp hq
      have hg : φ (mode ν 1) = ψ (mode ν 1) := by
        simp only [mode_one, map_smul, h]
      rw [hg, h0, h1] at hp
      exact add_right_cancel (hp.symm.trans hq)
  have heq : φ.toContinuousLinearMap = ψ.toContinuousLinearMap :=
    linear_ext ν (by simp) (fun n => hm (n + 1))
  exact ContinuousAlgHom.ext (fun a => DFunLike.congr_fun heq a)

end RadiiPolynomial.PhysicalSpectrum
