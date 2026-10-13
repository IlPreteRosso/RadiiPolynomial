import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# FIBER-TRIVIALIZATION-U1 probes (G2 / G3), frame-only edition

Compile probes for the `FiberTrivialization` refactor (consensus
`CONSENSUS_fiber_trivialization.md` §1–§5, gates G2/G3), migrated by unit E1
(`CONSENSUS_ft_reindex.md`): the legacy ten-field data class and its scalar-compatibility class
are deleted with their compatibility layer, so the old-view, round-trip and coexistence probes
are retired; the frame-selection probes (two frames on one family, the `−1` frame) are in
`FT/FrameReindexProbes.lean`. NOT imported by the root facade; build with
`lake build RadiiPolynomial.Examples.tests.FT.FiberTrivializationProbes`.
-/

noncomputable section

namespace RadiiPolynomial.Tests.FT

open RadiiPolynomial

/-! ## G2.1 Real and complex standard fibers: instance selection -/

section Instances

variable {M : Type*} (w : M → ℝ) [PosWeight w]

example : FiberTrivialization ℝ M (WeightedScalar ℝ w) := inferInstance
example : FiberTrivialization ℂ M (WeightedScalar ℂ w) := inferInstance
-- The frame found on the standard model IS the standard frame (single instance path).
example : (inferInstance : FiberTrivialization ℝ M (WeightedScalar ℝ w)) =
    WeightedScalar.instFiberTrivialization := rfl
example : (inferInstance : FiberTrivialization ℂ M (WeightedScalar ℂ w)) =
    WeightedScalar.instFiberTrivialization := rfl

-- The norm instance on a fiber is the weighted one (definitional check).
example (m : M) (x : WeightedScalar ℂ w m) : ‖x‖ = ‖WeightedScalar.toReal x‖ * w m := rfl

-- The outParam `𝕜` is inferred from the fiber family alone.
example (m : M) (x : WeightedScalar ℂ w m) :
    (FiberTrivialization.equiv (E := WeightedScalar ℂ w) m).symm x = WeightedScalar.toReal x :=
  rfl

end Instances

/-! ## G2.2 A non-unit weight (2): an accidentally unweighted norm would give 1 -/

section WeightTwo

def two : ℕ → ℝ := fun _ => 2

instance : PosWeight two := ⟨fun _ => by norm_num [two]⟩

example : ‖FiberTrivialization.equiv (E := WeightedScalar ℝ two) 0 (1 : ℝ)‖ = 2 := by
  simp [two]

example : ‖FiberTrivialization.equiv (E := WeightedScalar ℂ two) 0 (1 : ℂ)‖ = 2 := by
  simp [two]

example : FiberTrivialization.weight (E := WeightedScalar ℝ two) 0 = 2 := by
  simp [two]

example : ‖FiberTrivialization.atom (E := WeightedScalar ℝ two) 0‖ = 2 := by
  rw [← FiberTrivialization.weight, WeightedScalar.fiberTrivialization_weight]; rfl

-- Generic derived scaling identity at weight 2.
example (r : ℝ) : ‖FiberTrivialization.equiv (E := WeightedScalar ℝ two) 3 r‖ = |r| * 2 := by
  rw [FiberTrivialization.norm_equiv_apply, WeightedScalar.fiberTrivialization_weight,
    Real.norm_eq_abs]; rfl

end WeightTwo

/-! ## G2.3 Old views at their old types; rfl bridges -/

section OldViews

variable {M : Type*} (w : M → ℝ) [PosWeight w] (m : M) (r : ℝ) (x : WeightedScalar ℝ w m)

example : (FiberTrivialization.equiv m r : WeightedScalar ℝ w m) = WeightedScalar.ofReal r := rfl
example : (WeightedScalar.equiv r : WeightedScalar ℝ w m) = WeightedScalar.ofReal r := rfl
example : (FiberTrivialization.equiv (E := WeightedScalar ℝ w) m).symm x =
    WeightedScalar.toReal x := rfl

-- Old AddEquiv view (`ofReal : 𝕜 ≃+ _`) and function views compile at their old types.
example : ℝ ≃+ WeightedScalar ℝ w m := WeightedScalar.ofReal
example : WeightedScalar ℝ w m → ℝ := WeightedScalar.toReal
example : (WeightedScalar.equiv : ℝ ≃ₗ[ℝ] WeightedScalar ℝ w m).toAddEquiv =
    WeightedScalar.ofReal := rfl
example : (WeightedScalar.ofReal r : WeightedScalar ℝ w m) = r := rfl

-- Book-style rfl / `show` patterns (ReferenceBook Spine/A2 `normW`, Ch10 `norm_ofReal_one_geomW`),
-- now through the frame.
example : ‖FiberTrivialization.equiv (E := WeightedScalar ℝ w) m r‖ = ‖r‖ * w m := rfl
example : FiberTrivialization.weight (E := WeightedScalar ℂ w) m = w m := by
  show ‖(WeightedScalar.ofReal (1 : ℂ) : WeightedScalar ℂ w m)‖ = _
  rw [WeightedScalar.norm_ofReal, norm_one, one_mul]

-- The frame round trip (replaces the legacy `toReal_ofReal` field).
example : (FiberTrivialization.equiv (E := WeightedScalar ℝ w) m).symm
    (FiberTrivialization.equiv m r) = r :=
  FiberTrivialization.equiv_symm_apply_equiv m r

end OldViews

/-! ## G2.4 Generic θ: derived laws, round trips, scalar compatibility -/

section Generic

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]

example (m : M) : 0 < FiberTrivialization.weight (E := E) m := FiberTrivialization.weight_pos m

example (m : M) (r : 𝕜) :
    ‖FiberTrivialization.equiv (E := E) m r‖ = ‖r‖ * FiberTrivialization.weight (E := E) m :=
  FiberTrivialization.norm_equiv_apply m r

-- Scalar action on coordinates: `map_smul` of `θ_m⁻¹` (no compatibility class).
example (m : M) (r : 𝕜) (x : E m) :
    (FiberTrivialization.equiv (E := E) m).symm (r • x) =
      r * (FiberTrivialization.equiv (E := E) m).symm x :=
  map_smul _ r x
example (f : lpOneAlg M E) (r : 𝕜) : lpOneAlg.toRealSeq (r • f) = r • lpOneAlg.toRealSeq f :=
  lpOneAlg.toRealSeq_smul r f

end Generic

/-! ## G2.5 Monoid generality and to_additive translations (weights of the chosen frame) -/

section Monoids

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]

-- Multiplicative (possibly noncommutative) index monoid.
example [Monoid M] [lpOneMulAlgWeightMul 𝕜 M E] (j l : M) :
    FiberTrivialization.weight (E := E) (j * l) ≤
      FiberTrivialization.weight (E := E) j * FiberTrivialization.weight (E := E) l :=
  lpOneMulAlgWeightMul.weight_mul_le j l
example [Monoid M] [lpOneMulAlgWeightMul 𝕜 M E] :
    FiberTrivialization.weight (E := E) (1 : M) = 1 :=
  lpOneMulAlgWeightMul.weight_one

-- Additive index monoid (translated names).
example [AddMonoid M] [lpOneAlgWeightMul 𝕜 M E] (j l : M) :
    FiberTrivialization.weight (E := E) (j + l) ≤
      FiberTrivialization.weight (E := E) j * FiberTrivialization.weight (E := E) l :=
  lpOneAlgWeightMul.weight_add_le j l
example [AddMonoid M] [lpOneAlgWeightMul 𝕜 M E] :
    FiberTrivialization.weight (E := E) (0 : M) = 1 :=
  lpOneAlgWeightMul.weight_zero
example [AddMonoid M] [lpOneAlgWeightSubMul 𝕜 M E] (m : M) :
    1 ≤ FiberTrivialization.weight (E := E) m :=
  lpOneAlgWeightSubMul.one_le_weight m

-- Ring structure still found generically (multiplicative and additive).
example [Monoid M] [DecidableEq M] [CompleteSpace 𝕜] [lpOneMulAlgWeightMul 𝕜 M E] :
    NormedRing (lpOneAlg M E) := inferInstance
example [AddMonoid M] [DecidableEq M] [CompleteSpace 𝕜] [lpOneAlgWeightMul 𝕜 M E] :
    NormedRing (lpOneAlg M E) := inferInstance

-- Standard model with an additive weight class.
example {w : ℕ → ℝ} [SubMulWeightBase w] : lpOneAlgWeightMul ℝ ℕ (WeightedScalar ℝ w) :=
  inferInstance
example {w : ℕ → ℝ} [SubMulWeight w] : lpOneAlgWeightSubMul ℝ ℕ (WeightedScalar ℝ w) :=
  inferInstance
example {w : ℕ → ℝ} [SubMulWeightBase w] : NormOneClass (lpOneAlg ℕ (WeightedScalar ℝ w)) :=
  inferInstance

end Monoids

/-! ## G3 Standard-model identities: `single`, convolution, scalar action -/

section StandardModel

variable {ν : PosReal}

-- Geometric `single` unfolds to the same coefficient function.
example (n k : ℕ) (x : ℝ) :
    l1Weighted.toSeq (l1Weighted.single (ν := ν) n x) k = if k = n then x else 0 :=
  l1Weighted.single_toSeq n k x

-- Generic `lpOneAlg.single` on the standard fiber: `fiberSingle j (θ_j x)`, `θ_j x = ofReal x`.
example (j : ℕ) (x : ℝ) :
    lpOneAlg.single (E := ScaledReal ν) j x = ⟨lp.single 1 j (WeightedScalar.ofReal x)⟩ := rfl

-- The convolution product unfolds to the same term (coefficient = Cauchy/additive convolution).
example (f g : l1Weighted ν) (k : ℕ) :
    (f * g) k = WeightedScalar.ofReal
      (_root_.DiscreteConvolution.addRingConvolution (lpOneAlg.toRealSeq f)
        (lpOneAlg.toRealSeq g) k) :=
  rfl
example (f : l1Weighted ν) (k : ℕ) : lpOneAlg.toRealSeq f k = WeightedScalar.toReal (f k) := rfl

-- `single_mul` (the monoid-algebra identity) is unchanged.
example (m n : ℕ) (r s : ℝ) :
    l1Weighted.single (ν := ν) m r * l1Weighted.single n s = l1Weighted.single (m + n) (r * s) :=
  l1Weighted.single_mul m n r s

-- Scalar action on coefficients.
example (r : ℝ) (f : l1Weighted ν) :
    lpOneAlg.toRealSeq (r • f) = r • lpOneAlg.toRealSeq f := lpOneAlg.toRealSeq_smul r f
example (r : ℝ) (f : l1Weighted ν) (k : ℕ) : (r • f) k = WeightedScalar.ofReal (r * WeightedScalar.toReal (f k)) := rfl

end StandardModel

end RadiiPolynomial.Tests.FT

end
