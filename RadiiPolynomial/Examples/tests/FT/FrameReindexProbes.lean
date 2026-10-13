import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1
import Mathlib.Analysis.Complex.Basic

/-!
# Frame re-index probes (unit E1, consensus `CONSENSUS_ft_reindex.md` R1–R5)

The weighted ℓ¹ API is indexed by the chosen frame `FiberTrivialization 𝕜 M E` alone. These
probes check, against the station only (no consumer imports):

1. instance selection for real and complex scalars and the θ/θ⁻¹ coordinate and atom formulas;
2. a non-unit weight (`2`, and the Beurling weight `2ⁿ`);
3. the frame-free primitives `fiberSingle` and its expansion (no frame in scope);
4. the ring from the index monoid, `DecidableEq` and convolution compatibility alone, and the
   θ-transported product and unit;
5. both convolution summability routes (finite antidiagonal, also over the non-complete `ℚ`;
   complete scalar field over `ℤ`), with the selected instance identified;
6. two distinct frames on the same fiber family, selected explicitly: the `−1` frame has the same
   weights, the negated product and the unit `-1` (the sign countermodel of R2).

NOT imported by the root facade; build with
`lake build RadiiPolynomial.Examples.tests.FT.FrameReindexProbes`.
-/

noncomputable section

namespace RadiiPolynomial.Tests.FTReindex

open RadiiPolynomial
open _root_.DiscreteConvolution

/-! ## 1. Instance selection; θ/θ⁻¹ formulas; real and complex scalars -/

section Instances

variable {M : Type*} (w : M → ℝ) [PosWeight w]

example : FiberTrivialization ℝ M (WeightedScalar ℝ w) := inferInstance
example : FiberTrivialization ℂ M (WeightedScalar ℂ w) := inferInstance
example : (inferInstance : FiberTrivialization ℂ M (WeightedScalar ℂ w)) =
    WeightedScalar.instFiberTrivialization := rfl

-- Coordinates are θ⁻¹ (here the identity of `ℂ`), the outParam `𝕜` read off the fibers.
example (f : lpOneAlg M (WeightedScalar ℂ w)) (m : M) :
    lpOneAlg.toRealSeq f m = WeightedScalar.toReal (f m) := rfl
example (f : lpOneAlg M (WeightedScalar ℂ w)) (m : M) :
    lpOneAlg.toRealSeq f m = (FiberTrivialization.equiv (E := WeightedScalar ℂ w) m).symm (f m) :=
  lpOneAlg.toRealSeq_apply f m
-- Scalar single = frame-free insertion of `θ_j x`.
example [DecidableEq M] (j : M) (x : ℂ) :
    lpOneAlg.single (E := WeightedScalar ℂ w) j x =
      lpOneAlg.fiberSingle j (WeightedScalar.ofReal x) := rfl
-- Linearity of the coordinates over `ℂ` (no separate compatibility class).
example (f : lpOneAlg M (WeightedScalar ℂ w)) (r : ℂ) :
    lpOneAlg.toRealSeq (r • f) = r • lpOneAlg.toRealSeq f := lpOneAlg.toRealSeq_smul r f

-- Complex convolution algebra on the standard frame.
example {w : ℕ → ℝ} [SubMulWeightBase w] : NormedRing (lpOneAlg ℕ (WeightedScalar ℂ w)) :=
  inferInstance
example {w : ℕ → ℝ} [SubMulWeightBase w] : NormedCommRing (lpOneAlg ℕ (WeightedScalar ℂ w)) :=
  inferInstance
example {w : ℕ → ℝ} [SubMulWeightBase w] : NormedAlgebra ℂ (lpOneAlg ℕ (WeightedScalar ℂ w)) :=
  inferInstance
example {w : ℕ → ℝ} [SubMulWeightBase w] : NormOneClass (lpOneAlg ℕ (WeightedScalar ℂ w)) :=
  inferInstance
example {w : ℕ → ℝ} [SubMulWeightBase w] : NormedAlgebra ℝ (lpOneAlg ℕ (WeightedScalar ℝ w)) :=
  inferInstance

end Instances

/-! ## 2. Non-unit weights: an accidentally unweighted norm would give 1 -/

section WeightTwo

/-- The constant weight `2`. -/
def two : ℕ → ℝ := fun _ => 2

instance : PosWeight two := ⟨fun _ => by norm_num [two]⟩

example : FiberTrivialization.weight (E := WeightedScalar ℝ two) 3 = 2 := by simp [two]
example : FiberTrivialization.weight (E := WeightedScalar ℂ two) 3 = 2 := by simp [two]
example : ‖(lpOneAlg.single (E := WeightedScalar ℝ two) 0 (1 : ℝ))‖ = 2 := by
  rw [lpOneAlg.norm_single]; simp [two]
example : ‖(lpOneAlg.single (E := WeightedScalar ℂ two) 5 (3 : ℂ))‖ = 6 := by
  rw [lpOneAlg.norm_single]; norm_num [two]
example (f : lpOneAlg ℕ (WeightedScalar ℝ two)) (m : ℕ) :
    ‖f m‖ = ‖lpOneAlg.toRealSeq f m‖ * 2 := by
  rw [lpOneAlg.norm_eq_abs_toReal_mul_weight]; simp [two]
-- The frame-free insertion carries no weight factor of its own.
example (x : WeightedScalar ℝ two 4) :
    ‖(lpOneAlg.fiberSingle 4 x : lpOneAlg ℕ (WeightedScalar ℝ two))‖ = ‖x‖ :=
  lpOneAlg.norm_fiberSingle 4 x

/-- The Beurling weight `2ⁿ`. -/
def pow2 : ℕ → ℝ := fun n => 2 ^ n

instance : SubMulWeightBase pow2 where
  weight_pos _ := by unfold pow2; positivity
  submul m n := by unfold pow2; rw [pow_add]
  weight_zero := by simp [pow2]

example : ‖(lpOneAlg.single (E := WeightedScalar ℝ pow2) 1 (1 : ℝ) *
    lpOneAlg.single (E := WeightedScalar ℝ pow2) 1 (1 : ℝ))‖ = 4 := by
  rw [lpOneAlg.single_mul_single, lpOneAlg.norm_single]; norm_num [pow2]
example : ‖(1 : lpOneAlg ℕ (WeightedScalar ℂ pow2))‖ = 1 := norm_one

end WeightTwo

/-! ## 3. Frame-free primitives (no frame, no scalar field in scope) -/

section FrameFree

variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [DecidableEq M]

example (h : lpOneAlg M E) : HasSum (fun m => lpOneAlg.fiberSingle m (h m)) h :=
  lpOneAlg.hasSum_fiberSingle h
example (m : M) (x : E m) : ‖lpOneAlg.fiberSingle m x‖ = ‖x‖ := lpOneAlg.norm_fiberSingle m x
example (m : M) (x y : E m) :
    lpOneAlg.fiberSingle m (x + y) = lpOneAlg.fiberSingle m x + lpOneAlg.fiberSingle m y :=
  lpOneAlg.fiberSingle_add m x y
-- The expansion pushed through a continuous linear map for the inherited action.
example {𝕜 : Type*} [NormedField 𝕜] [∀ m, NormedSpace 𝕜 (E m)] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (W : lpOneAlg M E →L[𝕜] F) (h : lpOneAlg M E) :
    HasSum (fun m => W (lpOneAlg.fiberSingle m (h m))) (W h) :=
  lpOneAlg.hasSum_fiberSingle_mapCLM W h

end FrameFree

/-! ## 4. Ring from monoid + `DecidableEq` + convolution compatibility; θ-transported product -/

section Generic

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]

example [AddMonoid M] [DecidableEq M] [lpOneAlgConvCompat 𝕜 M E] :
    NormedRing (lpOneAlg M E) := inferInstance
example [Monoid M] [DecidableEq M] [lpOneMulAlgConvCompat 𝕜 M E] :
    NormedRing (lpOneAlg M E) := inferInstance
example [AddMonoid M] [DecidableEq M] [lpOneAlgConvCompat 𝕜 M E] :
    NormedAlgebra 𝕜 (lpOneAlg M E) := inferInstance
-- No weight ≥ 1 anywhere on the ring path; NormOne keeps its own weight hypothesis.
example [AddMonoid M] [DecidableEq M] [lpOneAlgConvCompat 𝕜 M E] [lpOneAlgWeightMul 𝕜 M E] :
    NormOneClass (lpOneAlg M E) := inferInstance
example [AddMonoid M] [DecidableEq M] [CompleteSpace 𝕜] [lpOneAlgWeightMul 𝕜 M E] :
    NormedRing (lpOneAlg M E) := inferInstance

-- θ / θ⁻¹ formulas of the product and the unit.
example [AddMonoid M] [DecidableEq M] [lpOneAlgConvCompat 𝕜 M E] (f g : lpOneAlg M E) (k : M) :
    (f * g) k = FiberTrivialization.equiv (E := E) k
      (addRingConvolution (lpOneAlg.toRealSeq f) (lpOneAlg.toRealSeq g) k) :=
  lpOneAlg.mul_apply f g k
example [AddMonoid M] [DecidableEq M] [lpOneAlgConvCompat 𝕜 M E] (f g : lpOneAlg M E) :
    lpOneAlg.toRealSeq (f * g) =
      addRingConvolution (lpOneAlg.toRealSeq f) (lpOneAlg.toRealSeq g) :=
  lpOneAlg.toRealSeq_mul_fun f g
example [AddMonoid M] [DecidableEq M] [lpOneAlgConvCompat 𝕜 M E] :
    (1 : lpOneAlg M E) = lpOneAlg.single 0 (1 : 𝕜) := lpOneAlg.one_eq_single_zero
-- Weight classes read the frame's weight `‖θ_m 1‖`.
example [AddMonoid M] [lpOneAlgWeightMul 𝕜 M E] (j l : M) :
    FiberTrivialization.weight (E := E) (j + l) ≤
      FiberTrivialization.weight (E := E) j * FiberTrivialization.weight (E := E) l :=
  lpOneAlgWeightMul.weight_add_le j l
example [Monoid M] [lpOneMulAlgWeightMul 𝕜 M E] :
    FiberTrivialization.weight (E := E) (1 : M) = 1 := lpOneMulAlgWeightMul.weight_one
-- Atom and weight of the frame.
example (m : M) : FiberTrivialization.atom (E := E) m = FiberTrivialization.equiv m 1 := rfl
example (m : M) :
    FiberTrivialization.weight (E := E) m = ‖FiberTrivialization.equiv (E := E) m 1‖ := rfl

end Generic

/-! ## 5. Both convolution summability routes -/

section Routes

-- Finite antidiagonal route, over the non-complete field `ℚ`.
example : lpOneAlgConvCompat ℚ ℕ (WeightedScalar ℚ pow2) := inferInstance
example : (inferInstance : lpOneAlgConvCompat ℚ ℕ (WeightedScalar ℚ pow2)) =
    lpOneAlg.instConvCompatOfAntidiag := rfl
example : NormedRing (lpOneAlg ℕ (WeightedScalar ℚ pow2)) := inferInstance
-- Over `ℝ` and `ℕ` the antidiagonal route is selected (priority 1100).
example : (inferInstance : lpOneAlgConvCompat ℝ ℕ (WeightedScalar ℝ pow2)) =
    lpOneAlg.instConvCompatOfAntidiag := rfl

/-- The Beurling weight `2^|k|` on `ℤ` (infinite addition fibers). -/
def pow2Z : ℤ → ℝ := fun k => 2 ^ k.natAbs

instance : SubMulWeightBase pow2Z where
  weight_pos _ := by unfold pow2Z; positivity
  submul m n := by
    unfold pow2Z
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (Int.natAbs_add_le m n)
  weight_zero := by simp [pow2Z]

-- Complete scalar field route over `ℤ`.
example : (inferInstance : lpOneAlgConvCompat ℝ ℤ (WeightedScalar ℝ pow2Z)) =
    lpOneAlg.instConvCompatOfWeightMul := rfl
example : NormedRing (lpOneAlg ℤ (WeightedScalar ℂ pow2Z)) := inferInstance
-- Neither route over `ℚ` and `ℤ`.
example : True := by
  fail_if_success (have : lpOneAlgConvCompat ℚ ℤ (WeightedScalar ℚ pow2Z) := inferInstance)
  trivial

end Routes

/-! ## 6. Two distinct frames on the same fiber family: the `−1` frame

On `U = WeightedScalar ℝ unitW` (unit weights) the standard frame `θ_m = id` and the frame
`θ'_m r = θ_m (−r)` have the same weights; transported through `θ'`, the product is minus the
standard one and the unit is `-1 = -δ₀`. Equal weights therefore do not determine the product:
every weight and convolution witness is indexed by the selected frame. `θ'` is selected
explicitly (`letI`), never by instance search. -/

section NegFrame

/-- Unit weights. -/
def unitW : ℕ → ℝ := fun _ => 1

instance : SubMulWeightBase unitW where
  weight_pos _ := one_pos
  submul _ _ := by simp [unitW]
  weight_zero := rfl

/-- The fiber family of the probe. -/
abbrev U : ℕ → Type := WeightedScalar ℝ unitW

/-- The `−1` frame on `U`: `θ'_m r = θ_m (−r)`. A `def`, not an instance: it is selected
explicitly (`letI`). -/
@[instance_reducible]
def negFrame : FiberTrivialization ℝ ℕ U where
  equiv _ := (LinearEquiv.neg ℝ).trans WeightedScalar.equiv

/-- The weights of the `−1` frame are the standard ones. -/
theorem negFrame_weight (m : ℕ) :
    (letI := negFrame; FiberTrivialization.weight (E := U) m) =
      FiberTrivialization.weight (E := U) m := by
  show ‖(WeightedScalar.ofReal (-(1 : ℝ)) : U m)‖ = ‖(WeightedScalar.ofReal (1 : ℝ) : U m)‖
  rw [WeightedScalar.norm_ofReal, WeightedScalar.norm_ofReal, norm_neg]

/-- The atoms differ: `θ'_0 1 = θ_0 (−1)`. -/
theorem negFrame_atom (m : ℕ) :
    (letI := negFrame; FiberTrivialization.atom (E := U) m) =
      -FiberTrivialization.atom (E := U) m := rfl

/-- The two frames are distinct. -/
theorem negFrame_ne : negFrame ≠ WeightedScalar.instFiberTrivialization := by
  intro h
  have h1 := congrArg (fun θ : FiberTrivialization ℝ ℕ U =>
    WeightedScalar.toReal (@FiberTrivialization.equiv ℝ _ ℕ U _ _ θ 0 1)) h
  change (-1 : ℝ) = 1 at h1
  norm_num at h1

/-- The Beurling witness of the `−1` frame (its weights are `1`; the class is a `Prop`). -/
theorem negFrameWeightMul : letI := negFrame; lpOneAlgWeightMul ℝ ℕ U :=
  letI := negFrame
  { weight_add_le := fun j l => by
      rw [negFrame_weight, negFrame_weight, negFrame_weight]
      exact lpOneAlgWeightMul.weight_add_le j l
    weight_zero := by
      rw [negFrame_weight]
      exact lpOneAlgWeightMul.weight_zero }

/-- The product of `lpOneAlg ℕ U` in the `−1` frame (explicit selection). -/
def mulNeg (f g : lpOneAlg ℕ U) : lpOneAlg ℕ U :=
  letI := negFrame; letI := negFrameWeightMul; f * g

/-- The unit of `lpOneAlg ℕ U` in the `−1` frame. -/
def oneNeg : lpOneAlg ℕ U :=
  letI := negFrame; letI := negFrameWeightMul; 1

/-- **The `−1`-frame theorem.** Same family, same weights, negated product. -/
theorem mulNeg_eq_neg_mul (f g : lpOneAlg ℕ U) : mulNeg f g = -(f * g) := by
  refine lpOneAlg.ext fun k => ?_
  show (-(addRingConvolution (fun m => -WeightedScalar.toReal (f m))
      (fun m => -WeightedScalar.toReal (g m)) k) : ℝ) =
    -(addRingConvolution (fun m => WeightedScalar.toReal (f m))
      (fun m => WeightedScalar.toReal (g m)) k)
  rw [addRingConvolution_apply, addRingConvolution_apply]
  simp only [neg_mul_neg]

/-- **The `−1`-frame theorem, unit.** The unit is `-1 = -δ₀`. -/
theorem oneNeg_eq_neg_one : oneNeg = -1 := by
  refine lpOneAlg.ext fun k => ?_
  rfl

theorem oneNeg_eq_neg_single : oneNeg = -lpOneAlg.single (E := U) 0 1 := by
  rw [oneNeg_eq_neg_one, lpOneAlg.one_eq_single_zero]

/-- The instance search never selects the `−1` frame. -/
example : (inferInstance : FiberTrivialization ℝ ℕ U) = WeightedScalar.instFiberTrivialization :=
  rfl

/-- The standard weight witness is not a witness for the `−1` frame by inference. -/
example : True := by
  fail_if_success
    (have : (letI := negFrame; lpOneAlgWeightMul ℝ ℕ U) := inferInstance)
  trivial

end NegFrame

end RadiiPolynomial.Tests.FTReindex

end
