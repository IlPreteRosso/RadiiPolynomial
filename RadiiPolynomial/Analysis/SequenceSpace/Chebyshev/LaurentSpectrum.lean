import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UnitLift
import RadiiPolynomial.Analysis.SequenceSpace.CharacterTopology
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# The Laurent character space as a topological space

Sequence-space layer, bilateral (Laurent) Chebyshev carrier. The complex
characters `l1Chebyshev ν →A[ℝ] ℂ` of the *real* production algebra are bundled
here as a topological space: `pointwiseTopology` is the carrier-independent
topology of pointwise convergence from
`Analysis/SequenceSpace/CharacterTopology.lean`, installed as a `local instance`
only (no global instance), and
`characterHomeomorphAnnulus : Character ν ≃ₜ Annulus ν` identifies them with the
closed annulus `ν⁻¹ ≤ ‖z‖ ≤ ν`, including its circle degeneration at `ν = 1`.
Parameter continuity comes from the uniform weighted lift
`synthesis : l1Chebyshev ν →L[ℝ] (Annulus ν →ᵇ ℂ)` built on `powerColumn`.

Before this module production had the annulus characters `evalLaurentC` and
`algHom_ext` but no packaged classification or topology; the module is independent
of `Geometric/Spectrum.lean`.
-/

noncomputable section
open scoped BoundedContinuousFunction

namespace RadiiPolynomial.LaurentSpectrum
open lpOneAlg

abbrev Character (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] := l1Chebyshev ν →A[ℝ] ℂ
abbrev Annulus (ν : PosReal) := {z : ℂ // (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)}

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]

def annulusCharacter (z : Annulus ν) : Character ν :=
  l1Chebyshev.evalLaurentC ν z.val z.property

@[simp] theorem annulusCharacter_gen (z : Annulus ν) :
    annulusCharacter ν z (single 1 1) = z.val :=
  l1Chebyshev.evalLaurentC_gen ν z.val z.property

@[simp] theorem annulusCharacter_single (z : Annulus ν) (k : ℤ) :
    annulusCharacter ν z (single k 1) = z.val^k :=
  l1Chebyshev.evalLaurentC_single ν z.val z.property k

def characterEquivAnnulus : Character ν ≃ Annulus ν where
  toFun χ := ⟨χ (single 1 1),
    l1Chebyshev.inv_le_norm_genUnit ν χ, l1Chebyshev.norm_genUnit_le ν χ⟩
  invFun := annulusCharacter ν
  left_inv _χ := l1Chebyshev.algHom_ext ν (annulusCharacter_gen ν _)
  right_inv z := Subtype.ext (annulusCharacter_gen ν z)

omit [Fact (1 ≤ (ν : ℝ))] in
theorem annulus_norm_zpow_le (z : Annulus ν) (k : ℤ) : ‖z.val^k‖ ≤ (ν : ℝ)^k.natAbs := by
  have h := lpOneAlg.norm_annulus_zpow_le ν z.property k
  simpa only [Units.val_zpow_eq_zpow_val, Units.val_mk0, one_mul] using h

def powerColumn (k : ℤ) : Annulus ν →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun z => z.val^k)
    (continuous_subtype_val.zpow₀ k (fun z => Or.inl (lpOneAlg.ne_zero_of_annulus ν z.property)))
    ((ν : ℝ)^k.natAbs) (fun z => annulus_norm_zpow_le ν z k)

omit [Fact (1 ≤ (ν : ℝ))] in
@[simp] theorem powerColumn_apply (k : ℤ) (z : Annulus ν) : powerColumn ν k z = z.val^k := rfl

omit [Fact (1 ≤ (ν : ℝ))] in
theorem norm_powerColumn_le (k : ℤ) : ‖powerColumn ν k‖ ≤ (ν : ℝ)^k.natAbs :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (pow_nonneg ν.coe_nonneg k.natAbs) _

def synthesis : l1Chebyshev ν →L[ℝ] (Annulus ν →ᵇ ℂ) :=
  liftCLM (powerColumn ν) 1 (fun k => by
    rw [ScaledRealZ.norm_lpAlgRingData_ofReal]
    simpa using norm_powerColumn_le ν k)

theorem synthesis_eq_character (z : Annulus ν) (a : l1Chebyshev ν) :
    synthesis ν a z = annulusCharacter ν z a := by
  let S : l1Chebyshev ν →L[ℝ] ℂ := (BoundedContinuousFunction.evalCLM ℝ z).comp (synthesis ν)
  have hS : S = (annulusCharacter ν z).toContinuousLinearMap := by
    apply lpOneAlg.continuousLinearMap_ext
    intro k
    change synthesis ν (single k 1) z = annulusCharacter ν z (single k 1)
    rw [synthesis, liftCLM_single, annulusCharacter_single]
    simp [powerColumn_apply]
  exact DFunLike.congr_fun hS a

theorem continuous_annulusCharacter_apply (a : l1Chebyshev ν) :
    Continuous (fun z : Annulus ν => annulusCharacter ν z a) := by
  have he : (fun z : Annulus ν => annulusCharacter ν z a) = synthesis ν a := by
    funext z
    exact (synthesis_eq_character ν z a).symm
  rw [he]
  exact (synthesis ν a).continuous

@[instance_reducible]
def pointwiseTopology : TopologicalSpace (Character ν) :=
  Gelfand.pointwiseTopology ℝ (l1Chebyshev ν) ℂ

local instance : TopologicalSpace (Character ν) := pointwiseTopology ν

theorem continuous_character_apply (a : l1Chebyshev ν) :
    Continuous (fun χ : Character ν => χ a) :=
  Gelfand.continuous_character_apply (R := ℝ) (l1Chebyshev ν) ℂ a

theorem continuous_annulusCharacter : Continuous (annulusCharacter ν) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi (fun a => continuous_annulusCharacter_apply ν a)

/-- Complex characters of the actual real bilateral coefficient algebra form
the closed annulus, including its circle degeneration at ν=1. -/
def characterHomeomorphAnnulus : Character ν ≃ₜ Annulus ν where
  toEquiv := characterEquivAnnulus ν
  continuous_toFun := (continuous_character_apply ν (single 1 1)).subtype_mk _
  continuous_invFun := continuous_annulusCharacter ν

@[simp] theorem characterHomeomorphAnnulus_apply (χ : Character ν) :
    (characterHomeomorphAnnulus ν χ).val = χ (single 1 1) := rfl

end RadiiPolynomial.LaurentSpectrum
