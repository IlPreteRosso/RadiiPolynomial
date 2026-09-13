import RadiiPolynomial.Analysis.SequenceSpace.Geometric.EvalC
import RadiiPolynomial.Analysis.SequenceSpace.CharacterTopology
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# The Taylor character space as a topological space

Sequence-space layer, Taylor (geometric) carrier. The complex characters
`l1Weighted ν →A[ℝ] ℂ` of the *real* production algebra are bundled here as a
topological space: `pointwiseTopology` is the carrier-independent topology of
pointwise convergence from `Analysis/SequenceSpace/CharacterTopology.lean`,
installed as a `local instance` only (no global instance), and
`characterHomeomorphDisc : Character ν ≃ₜ Disc ν` identifies them with the closed
complex disc of radius `ν`. Continuity in the parameter comes from the uniform
weighted lift `synthesis : l1Weighted ν →L[ℝ] (Disc ν →ᵇ ℂ)` built on `powerColumn`.

Before this module production identified the characters pointwise
(`character_classification_evalC`) but bundled no topological spectrum object.

Main declarations: `TaylorSpectrum.Character`, `Disc`, `discCharacter`,
`powerColumn`, `synthesis`, `characterEquivDisc`, `pointwiseTopology`,
`characterHomeomorphDisc`.
-/

noncomputable section
open scoped BoundedContinuousFunction

namespace RadiiPolynomial.TaylorSpectrum
open lpOneAlg

abbrev Character (ν : PosReal) := l1Weighted ν →A[ℝ] ℂ
abbrev Disc (ν : PosReal) := {z : ℂ // ‖z‖ ≤ (ν : ℝ)}

variable (ν : PosReal)

def discCharacter (z : Disc ν) : Character ν := l1Weighted.evalC ν z.val z.property

@[simp] theorem discCharacter_gen (z : Disc ν) :
    discCharacter ν z (single 1 1) = z.val := l1Weighted.evalC_gen ν z.val z.property

theorem discCharacter_single (z : Disc ν) (n : ℕ) :
    discCharacter ν z (single n 1) = z.val^n := by
  rw [← lpOneAlg.gen_pow_eq_single (𝕜 := ℝ) ν n, map_pow, discCharacter_gen]

def characterEquivDisc : Character ν ≃ Disc ν where
  toFun χ := ⟨χ (single 1 1), l1Weighted.norm_gen_le ν χ⟩
  invFun := discCharacter ν
  left_inv _χ := l1Weighted.algHom_ext ν (discCharacter_gen ν _)
  right_inv z := Subtype.ext (discCharacter_gen ν z)

def powerColumn (n : ℕ) : Disc ν →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun z => z.val^n)
    (continuous_subtype_val.pow n) ((ν : ℝ)^n) (fun z => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg z.val) z.property n)

@[simp] theorem powerColumn_apply (n : ℕ) (z : Disc ν) : powerColumn ν n z = z.val^n := rfl

theorem norm_powerColumn_le (n : ℕ) : ‖powerColumn ν n‖ ≤ (ν : ℝ)^n :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (pow_nonneg ν.coe_nonneg n) _

def synthesis : l1Weighted ν →L[ℝ] (Disc ν →ᵇ ℂ) :=
  liftCLM (powerColumn ν) 1 (fun n => by
    change ‖powerColumn ν n‖ ≤ 1 * (|1| * (ν : ℝ)^n)
    simpa using norm_powerColumn_le ν n)

theorem synthesis_eq_character (z : Disc ν) (a : l1Weighted ν) :
    synthesis ν a z = discCharacter ν z a := by
  let S : l1Weighted ν →L[ℝ] ℂ := (BoundedContinuousFunction.evalCLM ℝ z).comp (synthesis ν)
  have hS : S = (discCharacter ν z).toContinuousLinearMap := by
    apply lpOneAlg.continuousLinearMap_ext
    intro n
    change synthesis ν (single n 1) z = discCharacter ν z (single n 1)
    rw [synthesis, liftCLM_single, discCharacter_single]
    simp [powerColumn_apply]
  exact DFunLike.congr_fun hS a

theorem continuous_discCharacter_apply (a : l1Weighted ν) :
    Continuous (fun z : Disc ν => discCharacter ν z a) := by
  have he : (fun z : Disc ν => discCharacter ν z a) = synthesis ν a := by
    funext z
    exact (synthesis_eq_character ν z a).symm
  rw [he]
  exact (synthesis ν a).continuous

@[instance_reducible]
def pointwiseTopology : TopologicalSpace (Character ν) :=
  Gelfand.pointwiseTopology ℝ (l1Weighted ν) ℂ

local instance : TopologicalSpace (Character ν) := pointwiseTopology ν

theorem continuous_character_apply (a : l1Weighted ν) :
    Continuous (fun χ : Character ν => χ a) :=
  Gelfand.continuous_character_apply (R := ℝ) (l1Weighted ν) ℂ a

theorem continuous_discCharacter : Continuous (discCharacter ν) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi (fun a => continuous_discCharacter_apply ν a)

/-- Complex characters of the real Taylor coefficient algebra form its closed
disc, for every positive weight radius, with pointwise character topology. -/
def characterHomeomorphDisc : Character ν ≃ₜ Disc ν where
  toEquiv := characterEquivDisc ν
  continuous_toFun := (continuous_character_apply ν (single 1 1)).subtype_mk _
  continuous_invFun := continuous_discCharacter ν

@[simp] theorem characterHomeomorphDisc_apply (χ : Character ν) :
    (characterHomeomorphDisc ν χ).val = χ (single 1 1) := rfl

end RadiiPolynomial.TaylorSpectrum
