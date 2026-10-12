import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# FIBER-TRIVIALIZATION-U1 probes (G2 / G3)

Compile probes for the `FiberTrivialization` refactor (consensus
`CONSENSUS_fiber_trivialization.md` §1–§5, gates G2/G3). NOT imported by the root facade;
build with `lake build RadiiPolynomial.Examples.tests.FT.FiberTrivializationProbes`.
-/

noncomputable section

namespace RadiiPolynomial.Tests.FT

open RadiiPolynomial

/-! ## G2.1 Real and complex standard fibers: instance selection -/

section Instances

variable {M : Type*} (w : M → ℝ) [PosWeight w]

example : FiberTrivialization ℝ M (WeightedScalar ℝ w) := inferInstance
example : FiberTrivialization ℂ M (WeightedScalar ℂ w) := inferInstance
example : lpAlgRingData ℝ M (WeightedScalar ℝ w) := inferInstance
example : lpAlgRingData ℂ M (WeightedScalar ℂ w) := inferInstance
example : lpAlgSmulCompat ℝ M (WeightedScalar ℝ w) := inferInstance
example : lpAlgSmulCompat ℂ M (WeightedScalar ℂ w) := inferInstance

-- The legacy instance on the standard model IS the derived one (single instance path).
example : (inferInstance : lpAlgRingData ℝ M (WeightedScalar ℝ w)) =
    FiberTrivialization.toLpAlgRingData := rfl
example : (inferInstance : lpAlgRingData ℂ M (WeightedScalar ℂ w)) =
    FiberTrivialization.toLpAlgRingData := rfl

-- The norm instance on a fiber is the weighted one (definitional check).
example (m : M) (x : WeightedScalar ℂ w m) : ‖x‖ = ‖WeightedScalar.toReal x‖ * w m := rfl

-- The outParam `𝕜` is inferred from the fiber family alone.
example (m : M) (x : WeightedScalar ℂ w m) : lpAlgRingData.toReal m x = WeightedScalar.toReal x :=
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

example : ‖lpAlgRingData.ofReal (E := WeightedScalar ℝ two) 0 (1 : ℝ)‖ = 2 := by
  rw [lpAlgRingData.norm_ofReal_eq, norm_one, one_mul,
    ← lpAlgRingData.weight_def, WeightedScalar.lpAlgRingData_weight]; rfl

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
example : ∀ m, ℝ → WeightedScalar ℝ w m := lpAlgRingData.ofReal
example : ∀ m, WeightedScalar ℝ w m → ℝ := lpAlgRingData.toReal
example : (WeightedScalar.equiv : ℝ ≃ₗ[ℝ] WeightedScalar ℝ w m).toAddEquiv =
    WeightedScalar.ofReal := rfl
example : lpAlgRingData.ofReal (E := WeightedScalar ℝ w) m r = WeightedScalar.ofReal r := rfl
example : lpAlgRingData.toReal m x = WeightedScalar.toReal x := rfl
example : (WeightedScalar.ofReal r : WeightedScalar ℝ w m) = r := rfl

-- Book-style rfl / `show` patterns (ReferenceBook Spine/A2 `normW`, Ch10 `norm_ofReal_one_geomW`).
example : ‖lpAlgRingData.ofReal (E := WeightedScalar ℝ w) m r‖ = ‖r‖ * w m := rfl
example : ‖lpAlgRingData.ofReal (E := WeightedScalar ℂ w) m (1 : ℂ)‖ = w m := by
  show ‖(WeightedScalar.ofReal (1 : ℂ) : WeightedScalar ℂ w m)‖ = _
  rw [WeightedScalar.norm_ofReal, norm_one, one_mul]

-- Representative simp: the legacy round trip still closes by simp.
example : lpAlgRingData.toReal m (lpAlgRingData.ofReal (E := WeightedScalar ℝ w) m r) = r := by
  simp [lpAlgRingData.toReal_ofReal]

end OldViews

/-! ## G2.4 Generic θ: derived laws, round trips, scalar compatibility -/

section Generic

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]

example (m : M) : 0 < FiberTrivialization.weight (E := E) m := FiberTrivialization.weight_pos m

example (m : M) (r : 𝕜) :
    ‖lpAlgRingData.ofReal (E := E) m r‖ = ‖r‖ * FiberTrivialization.weight (E := E) m :=
  FiberTrivialization.norm_equiv_apply m r

-- old → new → old and new → old → new round trips (definitional).
example (m : M) (r : 𝕜) :
    (FiberTrivialization.ofLpAlgRingData (FiberTrivialization.toLpAlgRingData (𝕜 := 𝕜) (E := E))).equiv
      m r = FiberTrivialization.equiv (E := E) m r := rfl
example (m : M) (x : E m) :
    ((FiberTrivialization.ofLpAlgRingData
        (FiberTrivialization.toLpAlgRingData (𝕜 := 𝕜) (E := E))).equiv m).symm x =
      (FiberTrivialization.equiv (E := E) m).symm x := rfl

-- Scalar-action compatibility of the derived witness.
example (m : M) (r : 𝕜) (x : E m) :
    lpAlgRingData.toReal m (r • x) = r * lpAlgRingData.toReal m x :=
  lpAlgSmulCompat.toReal_smul m r x

-- Weight agreement between the two interfaces.
example (m : M) : lpAlgRingData.weight (E := E) m = FiberTrivialization.weight (E := E) m := rfl

end Generic

section LegacyRoundTrip

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
  (d : lpAlgRingData 𝕜 M E) [@lpAlgSmulCompat 𝕜 _ M E _ _ d]

-- legacy → θ → legacy: the projections come back definitionally.
example (m : M) (r : 𝕜) :
    @lpAlgRingData.ofReal 𝕜 _ M E _
      (@FiberTrivialization.toLpAlgRingData 𝕜 _ M E _ _ (FiberTrivialization.ofLpAlgRingData d))
      m r = d.ofReal m r := rfl
example (m : M) (x : E m) :
    @lpAlgRingData.toReal 𝕜 _ M E _
      (@FiberTrivialization.toLpAlgRingData 𝕜 _ M E _ _ (FiberTrivialization.ofLpAlgRingData d))
      m x = d.toReal m x := rfl

end LegacyRoundTrip

/-! ## G2.5 Monoid generality and to_additive translations -/

section Monoids

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [lpAlgRingData 𝕜 M E]

-- Multiplicative (possibly noncommutative) index monoid: the old two-scalar form is derived.
example [Monoid M] [lpOneMulAlgWeightMul 𝕜 M E] (j l : M) (a b : 𝕜) :
    ‖lpAlgRingData.ofReal (E := E) (j * l) (a * b)‖ ≤
      ‖lpAlgRingData.ofReal (E := E) j a‖ * ‖lpAlgRingData.ofReal (E := E) l b‖ :=
  lpOneMulAlgWeightMul.norm_ofReal_mul_le j l a b

example [Monoid M] [lpOneMulAlgWeightMul 𝕜 M E] :
    ‖lpAlgRingData.ofReal (E := E) (1 : M) (1 : 𝕜)‖ = 1 :=
  lpOneMulAlgWeightMul.norm_ofReal_one_one

-- Additive index monoid (translated names).
example [AddMonoid M] [lpOneAlgWeightMul 𝕜 M E] (j l : M) (a b : 𝕜) :
    ‖lpAlgRingData.ofReal (E := E) (j + l) (a * b)‖ ≤
      ‖lpAlgRingData.ofReal (E := E) j a‖ * ‖lpAlgRingData.ofReal (E := E) l b‖ :=
  lpOneAlgWeightMul.norm_ofReal_mul_le j l a b

example [AddMonoid M] [lpOneAlgWeightMul 𝕜 M E] :
    ‖lpAlgRingData.ofReal (E := E) (0 : M) (1 : 𝕜)‖ = 1 :=
  lpOneAlgWeightMul.norm_ofReal_one_zero

example [AddMonoid M] [lpOneAlgWeightSubMul 𝕜 M E] (m : M) :
    1 ≤ ‖lpAlgRingData.ofReal (E := E) m (1 : 𝕜)‖ :=
  lpOneAlgWeightSubMul.norm_ofReal_one_ge m

-- The new primary fields, both notations.
example [Monoid M] [lpOneMulAlgWeightMul 𝕜 M E] (j l : M) :
    lpAlgRingData.weight (E := E) (j * l) ≤
      lpAlgRingData.weight (E := E) j * lpAlgRingData.weight (E := E) l :=
  lpOneMulAlgWeightMul.weight_mul_le j l
example [AddMonoid M] [lpOneAlgWeightMul 𝕜 M E] (j l : M) :
    lpAlgRingData.weight (E := E) (j + l) ≤
      lpAlgRingData.weight (E := E) j * lpAlgRingData.weight (E := E) l :=
  lpOneAlgWeightMul.weight_add_le j l

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

/-! ## G2.6 Coexistence: an independently supplied legacy instance (conjugation on ℂ)

`ConjFiber` carries legacy data `toReal = ofReal = conj`: all ten old fields hold, but it is not
`ℂ`-linear. A θ-instance lives on `WeightedScalar ℂ w` in the same file.

What this section shows: on a family WITHOUT θ, no scalar-compatibility witness and no θ are
synthesized from legacy data, and old-only consumers still elaborate. What it does NOT show:
the R2-A hazard (θ and independent legacy data on the SAME family); the `fail_if_success`
below passes trivially, since `toLpAlgSmulCompat` never applies to `ConjFiber`. The
same-family case is §G2.6b. -/

section Coexistence

/-- A local fiber family: `ℂ` at every index, unit weight. -/
def ConjFiber (_ : ℕ) : Type := ℂ

instance (n : ℕ) : NormedAddCommGroup (ConjFiber n) := inferInstanceAs (NormedAddCommGroup ℂ)
instance (n : ℕ) : NormedSpace ℂ (ConjFiber n) := inferInstanceAs (NormedSpace ℂ ℂ)

/-- Independently supplied legacy data: conjugation. -/
instance conjData : lpAlgRingData ℂ ℕ ConjFiber where
  toReal _ x := (starRingEnd ℂ) (show ℂ from x)
  ofReal _ r := ((starRingEnd ℂ) r : ℂ)
  toReal_ofReal _ r := Complex.conj_conj r
  ofReal_toReal _ x := Complex.conj_conj (show ℂ from x)
  ofReal_add _ a b := map_add (starRingEnd ℂ) a b
  ofReal_zero _ := map_zero (starRingEnd ℂ)
  toReal_add _ x y := map_add (starRingEnd ℂ) (show ℂ from x) (show ℂ from y)
  toReal_zero _ := map_zero (starRingEnd ℂ)
  toReal_neg _ x := map_neg (starRingEnd ℂ) (show ℂ from x)
  norm_ofReal_eq _ r := by
    show ‖(starRingEnd ℂ) r‖ = ‖r‖ * ‖(starRingEnd ℂ) (1 : ℂ)‖
    rw [Complex.norm_conj, map_one, norm_one, mul_one]

-- No witness on a family without θ (vacuous for the same-family hazard; see §G2.6b).
example : True := by
  fail_if_success (have : lpAlgSmulCompat ℂ ℕ ConjFiber := inferInstance)
  trivial

-- Nor is a θ (no reverse instance).
example : True := by
  fail_if_success (have : FiberTrivialization ℂ ℕ ConjFiber := inferInstance)
  trivial

-- The old scalar-compatibility conclusion is FALSE for this data (r = I, x = 1).
example : ¬ ∀ (m : ℕ) (r : ℂ) (x : ConjFiber m),
    lpAlgRingData.toReal m (r • x) = r * lpAlgRingData.toReal m x := by
  intro h
  have h1 := h 0 Complex.I (show ℂ from 1)
  change (starRingEnd ℂ) (Complex.I * 1) = Complex.I * (starRingEnd ℂ) 1 at h1
  rw [mul_one, map_one, mul_one, Complex.conj_I] at h1
  have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination -h1
  simp [Complex.I_ne_zero] at h2

-- The θ-instance on a different family coexists in the same file.
example {w : ℕ → ℝ} [PosWeight w] : lpAlgSmulCompat ℂ ℕ (WeightedScalar ℂ w) := inferInstance

-- Old-only generic consumers still elaborate on the legacy data.
example (j : ℕ) (x : ℂ) :
    ‖(lpOneAlg.single (E := ConjFiber) j x : lpOneAlg ℕ ConjFiber)‖ =
      ‖x‖ * ‖lpAlgRingData.ofReal (E := ConjFiber) j (1 : ℂ)‖ :=
  lpOneAlg.norm_single j x
example (j k : ℕ) (x : ℂ) :
    lpOneAlg.toRealSeq (lpOneAlg.single (E := ConjFiber) j x) k = if k = j then x else 0 :=
  lpOneAlg.toRealSeq_single j x k
example (f : lpOneAlg ℕ ConjFiber) (m : ℕ) :
    ‖f m‖ = ‖lpOneAlg.toRealSeq f m‖ * ‖lpAlgRingData.ofReal (E := ConjFiber) m (1 : ℂ)‖ :=
  lpOneAlg.norm_eq_abs_toReal_mul_weight f m

end Coexistence

/-! ## G2.6b Same-family coexistence (R2-A hazard)

θ = `LinearEquiv.refl` and independently supplied conjugation data on ONE family `CF`. The
default `lpAlgRingData` is the conjugation data; no scalar-compatibility witness is synthesized
for it; the derived witness exists exactly for the θ-derived data; old-only consumers elaborate
on the conjugation data. (Critic probe `CriticCoexist.lean`, copied verbatim.) -/

section SameFamilyCoexistence

def CF (_ : ℕ) : Type := ℂ
instance (n : ℕ) : NormedAddCommGroup (CF n) := inferInstanceAs (NormedAddCommGroup ℂ)
instance (n : ℕ) : NormedSpace ℂ (CF n) := inferInstanceAs (NormedSpace ℂ ℂ)
-- θ = id on the SAME family
instance thetaCF : FiberTrivialization ℂ ℕ CF := ⟨fun _ => LinearEquiv.refl ℂ ℂ⟩
-- independently supplied conjugation data on the SAME family
instance conjCF : lpAlgRingData ℂ ℕ CF where
  toReal _ x := (starRingEnd ℂ) (show ℂ from x)
  ofReal _ r := ((starRingEnd ℂ) r : ℂ)
  toReal_ofReal _ r := Complex.conj_conj r
  ofReal_toReal _ x := Complex.conj_conj (show ℂ from x)
  ofReal_add _ a b := map_add (starRingEnd ℂ) a b
  ofReal_zero _ := map_zero (starRingEnd ℂ)
  toReal_add _ x y := map_add (starRingEnd ℂ) (show ℂ from x) (show ℂ from y)
  toReal_zero _ := map_zero (starRingEnd ℂ)
  toReal_neg _ x := map_neg (starRingEnd ℂ) (show ℂ from x)
  norm_ofReal_eq _ r := by
    show ‖(starRingEnd ℂ) r‖ = ‖r‖ * ‖(starRingEnd ℂ) (1 : ℂ)‖
    rw [Complex.norm_conj, map_one, norm_one, mul_one]
-- which lpAlgRingData wins by default?
example : (inferInstance : lpAlgRingData ℂ ℕ CF) = conjCF := rfl
-- smul witness for the conj data must NOT be synthesized
example : True := by
  fail_if_success (have : @lpAlgSmulCompat ℂ _ ℕ CF _ _ conjCF := inferInstance)
  trivial
example : True := by
  fail_if_success (have : lpAlgSmulCompat ℂ ℕ CF := inferInstance)
  trivial
-- the derived witness IS available for the derived data
example : @lpAlgSmulCompat ℂ _ ℕ CF _ _ FiberTrivialization.toLpAlgRingData := inferInstance
-- old-only consumer elaborates on the conj data
example (j : ℕ) (x : ℂ) :
    ‖(lpOneAlg.single (E := CF) j x : lpOneAlg ℕ CF)‖ =
      ‖x‖ * ‖lpAlgRingData.ofReal (E := CF) j (1 : ℂ)‖ := lpOneAlg.norm_single j x

end SameFamilyCoexistence

/-! ## G3 Standard-model identities: `single`, convolution, scalar action -/

section StandardModel

variable {ν : PosReal}

-- Geometric `single` unfolds to the same coefficient function.
example (n k : ℕ) (x : ℝ) :
    l1Weighted.toSeq (l1Weighted.single (ν := ν) n x) k = if k = n then x else 0 :=
  l1Weighted.single_toSeq n k x

-- Generic `lpOneAlg.single` on the standard fiber: the legacy `ofReal` is `WeightedScalar.ofReal`.
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
