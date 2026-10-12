import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Diagonal
import RadiiPolynomial.Algebra.Ring.HeadTailIdentities

/-!
# Head/tail identities for bounded operators

The ring identities of `Algebra/Ring/HeadTailIdentities.lean` read in the ring of bounded
operators `E →L[𝕜] E`, where multiplication is composition (`ContinuousLinearMap.mul_def`).
For an idempotent head `P` and `R P = 0`,
`(M P + R)(P L (1 - P) + (1 - P) L) = M P L (1 - P) + R L`; a norm-one scalar multiple of
the left side has the norm of the right side. The finite-head projection `lpOneAlg.headProj`
of `WeightedL1/Diagonal.lean` is one such idempotent.

This module is imported only by higher consumers; no `Analysis` or `Algebra` module imports it.

Main declarations:
* `HeadTail.composition_identity` — the operator form of `composition_identity_ring`.
* `HeadTail.composition_identity_headProj` — the same at `P = headProj H`.
* `HeadTail.norm_smul_composition_identity` — the norm-one scalar face.
* `HeadTail.signed_transfer` — the S027 statement shape, as an explicit specialization.
-/

namespace RadiiPolynomial

namespace HeadTail

/-- Composition identity for bounded operators: for an idempotent `P` and
`R ∘ P = 0`, `(M P + R)(P L (1 - P) + (1 - P) L) = M P L (1 - P) + R L`. -/
theorem composition_identity {𝕜 : Type*} [NormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (P M R L : E →L[𝕜] E) (hP : IsIdempotentElem P) (hRP : R ∘L P = 0) :
    (M ∘L P + R) ∘L (P ∘L L ∘L (1 - P) + (1 - P) ∘L L) =
      M ∘L P ∘L L ∘L (1 - P) + R ∘L L := by
  simp only [← ContinuousLinearMap.mul_def] at hRP ⊢
  simpa only [mul_assoc] using composition_identity_ring P M R L hP hRP

/-- The composition identity at the finite-head projection
`P = headProj H` of `lpOneAlg J G`. -/
theorem composition_identity_headProj {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {G : J → Type*}
    [∀ j, NormedAddCommGroup (G j)] [∀ j, NormedSpace 𝕜 (G j)] [DecidableEq J]
    (H : Finset J) (M R L : lpOneAlg J G →L[𝕜] lpOneAlg J G)
    (hRP : R ∘L lpOneAlg.headProj H = 0) :
    (M ∘L lpOneAlg.headProj H + R) ∘L
        (lpOneAlg.headProj H ∘L L ∘L (1 - lpOneAlg.headProj H) +
          (1 - lpOneAlg.headProj H) ∘L L) =
      M ∘L lpOneAlg.headProj H ∘L L ∘L (1 - lpOneAlg.headProj H) + R ∘L L :=
  composition_identity _ M R L (lpOneAlg.isIdempotentElem_headProj H) hRP

/-- Norm-one scalar face of the composition identity:
`‖σ • ((M P + R)(P L (1 - P) + (1 - P) L))‖ = ‖M P L (1 - P) + R L‖` for `‖σ‖ = 1`. -/
theorem norm_smul_composition_identity {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (P M R L : E →L[𝕜] E) (σ : 𝕜)
    (hP : IsIdempotentElem P) (hRP : R ∘L P = 0) (hσ : ‖σ‖ = 1) :
    ‖σ • ((M ∘L P + R) ∘L (P ∘L L ∘L (1 - P) + (1 - P) ∘L L))‖ =
      ‖M ∘L P ∘L L ∘L (1 - P) + R ∘L L‖ := by
  rw [norm_smul, hσ, one_mul, composition_identity P M R L hP hRP]

/-- `hZ` is a model-discrepancy hypothesis. It stays conditional until the book's
E → Y → E maps discharge it; no unbounded book operator is identified with a CLM on E. -/
theorem signed_transfer {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (P M R L Z : E →L[𝕜] E) (σ : 𝕜)
    (hP : P ∘L P = P) (hRP : R ∘L P = 0) (hσ : ‖σ‖ = 1)
    (hZ : Z = σ • ((M ∘L P + R) ∘L (P ∘L L ∘L (1 - P) + (1 - P) ∘L L))) :
    ‖Z‖ = ‖M ∘L P ∘L L ∘L (1 - P) + R ∘L L‖ := by
  rw [hZ]
  exact norm_smul_composition_identity P M R L σ ((ContinuousLinearMap.mul_def P P).trans hP)
    hRP hσ

end HeadTail

end RadiiPolynomial
