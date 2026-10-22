import RadiiPolynomial.Certification.IVP.Chebyshev.TC
import RadiiPolynomial.Certification.IVP.Chebyshev.Z1
import RadiiPolynomial.Certification.RadiiPolynomialQ

/-!
# Chebyshev certification adapter: the family face

`ChebCertQ` (the certificate numbers and override slots), `ChebCertQ.Checks` (all obligations
as one ℚ-decidable conjunction), `d.certified_of_Y₀Z₀` and `d.certified_of_checks`.
-/

open scoped BigOperators Topology
open RadiiPolynomial MvPolyBridge RadiiPolynomial.Certification.Rational

namespace ChebyshevIVP

/-! ### The family face -/

section Face

/-- The numbers a certificate supplies beyond its bundle: the five radii-polynomial
numbers plus the five override slots (each `≥` its generated majorant, `_of_le` pattern). -/
structure ChebCertQ (L : ℕ) where
  Y₀ : ℚ
  Z₀ : ℚ
  Z₁ : ℚ
  Z₂ : ℚ
  r₀ : ℚ
  /-- override: radii `R i ≥ ‖S(ā_i)‖` (exact `SnormQ`). -/
  R : Fin L → ℚ
  /-- override: `K ≥ max_l derivativeBound (f l) R`. -/
  K : ℚ
  /-- override: `ε ≥ epsGen` (generated ε-leakage). -/
  ε : ℚ
  /-- override: `C ≥ TCnormGen` (generated `‖TC‖` constant). -/
  C : ℚ
  /-- override: `B ≥ 2 · max_l derivativeLipschitzBound (f l) (R + 2 r₀)`. -/
  B : ℚ

variable {L : ℕ} [NeZero L]

/-- All ℚ-decidable obligations, on the raw `StdChebIVPData` fields (ν-free: one
`decide +kernel`). The first conjunct is the exact family-neutral defect clause
(`DefectExact`). The literals are recipe constants of the library lemmas the conjuncts feed:
* `ν_q / (N + 1)` is the tail factor of `chebyshev_Z₁_le_relaxed` (the `Z₁` total);
* the `2` in `2 * derivativeLipschitzBound` is the symmetrization of the raw displacement
  (`norm_compPolyDerivative_sub_le`);
* the radii `C.R i + 2 * C.r₀` bound `‖S(cᵢ)‖` on the ball from `‖S(āᵢ)‖ ≤ C.R i` and
  `‖S(cᵢ − āᵢ)‖ ≤ 2 ‖cᵢ − āᵢ‖ ≤ 2 r₀` (`l1Chebyshev.symmetrize_norm_le`);
* the last conjunct is the radii polynomial `Z₂ r₀² − (1 − Z₀ − Z₁) r₀ + Y₀ < 0`
  (`generalRadiiPolynomial_ratCast`). -/
abbrev ChebCertQ.Checks (C : ChebCertQ L) (N : ℕ)
    (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ)
    (f : Fin L → CompPoly L) (p_q : Fin L → ℚ) : Prop :=
  finiteBlockMatrixNormQ L N (defectCols A_col DF_col) ν_q ≤ C.Z₀ ∧
    (∀ l, Y₀Q N A_col abar_Q ν_q f p_q l ≤ C.Y₀) ∧
    (∀ i, SnormQ N abar_Q ν_q i ≤ C.R i) ∧
    (∀ l, CompPoly.Chebyshev.derivativeBound (f l) C.R ≤ C.K) ∧
    epsGen N A_col DF_col abar_Q ν_q f ≤ C.ε ∧
    C.ε + ν_q / ((N : ℚ) + 1) * C.K ≤ C.Z₁ ∧
    TCnormGen N A_col ν_q ≤ C.C ∧
    (∀ l, 2 * CompPoly.Chebyshev.derivativeLipschitzBound (f l)
      (fun i => C.R i + 2 * C.r₀) ≤ C.B) ∧
    C.C * C.B ≤ C.Z₂ ∧
    0 < C.r₀ ∧
    C.Z₂ * C.r₀ ^ 2 - (1 - C.Z₀ - C.Z₁) * C.r₀ + C.Y₀ < 0

namespace StdChebIVPData

section FaceBundle

variable {ν : PosReal} {N : ℕ} [Fact (1 ≤ (ν : ℝ))]

/-- Face with `Y₀`, `Z₀` from ℚ checks and `Z₁`, `Z₂` as explicit operator bounds; `hradii` is
the radii polynomial `Z₂ r₀² − (1 − Z₀ − Z₁) r₀ + Y₀ < 0` in exact arithmetic
(`generalRadiiPolynomial_ratCast`). -/
theorem certified_of_Y₀Z₀ (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    (p : Fin L → ℝ) (p_q : Fin L → ℚ) (hp : ∀ l, p l = (p_q l : ℝ)) {Y₀ Z₀ Z₁ Z₂ r₀ : ℚ}
    (hZ₀ : finiteBlockMatrixNormQ L N (defectCols d.A_col d.DF_col) d.ν_q ≤ Z₀)
    (hY₀ : ∀ l, Y₀Q N d.A_col d.abar_Q d.ν_q f p_q l ≤ Y₀)
    (hZ₁ : ‖d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar‖ ≤ (Z₁ : ℝ))
    (hZ₂ : ∀ c ∈ Metric.closedBall d.abar (r₀ : ℝ),
      ‖fderiv ℝ (d.G (banachField f) p) c - fderiv ℝ (d.G (banachField f) p) d.abar‖
        ≤ (Z₂ : ℝ) * (r₀ : ℝ))
    (hr₀ : 0 < r₀) (hradii : Z₂ * r₀ ^ 2 - (1 - Z₀ - Z₁) * r₀ + Y₀ < 0) :
    ∃! xTilde ∈ Metric.closedBall d.abar (r₀ : ℝ), d.G (banachField f) p xTilde = 0 :=
  d.existsUnique_of_compPoly f p (Z₂_val := (Z₂ : ℝ)) (by exact_mod_cast hr₀)
    (Y₀_le_of_Q d f p p_q hp hY₀) (defect_finBlockNorm_le_of_Q d hZ₀) hZ₁ hZ₂
    (generalRadiiPolynomial_neg_of_Q_const _ _ _ _ _ hradii)

/-- **Family face.** Existence and uniqueness of the zero of the preconditioned
Chebyshev IVP map for any `StdChebIVPData` bundle and `CompPoly` system, from ONE
ℚ-decidable conjunction (`decide +kernel`) plus the rational boundary-value bridge `hp`. -/
theorem certified_of_checks (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    (p : Fin L → ℝ) (p_q : Fin L → ℚ) (hp : ∀ l, p l = (p_q l : ℝ)) (C : ChebCertQ L)
    (h : C.Checks N d.A_col d.DF_col d.abar_Q d.ν_q f p_q) :
    ∃! xTilde ∈ Metric.closedBall d.abar (C.r₀ : ℝ), d.G (banachField f) p xTilde = 0 := by
  obtain ⟨hZ₀, hY₀, hR, hK, hε, hZ₁, hC, hB, hZ₂, hr₀, hrad⟩ := h
  exact certified_of_Y₀Z₀ d f p p_q hp hZ₀ hY₀ (Z₁_le_of_Q d f p hR hK hε hZ₁)
    (Z₂_le_of_Q d f p hR hr₀.le hC hB hZ₂) hr₀ hrad

end FaceBundle

end StdChebIVPData

end Face

end ChebyshevIVP
