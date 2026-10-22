import RadiiPolynomial.Certification.IVP.Chebyshev.Face
import RadiiPolynomial.Certification.IVP.Chebyshev.Kernel.QLayer

/-!
# Chebyshev certification adapter: kernel-scale face

The obligations `ChebCertQ.ChecksK` (with a `DefectBy` slot for `Z₀` and per-block leakage
data `E`), `checks_of_checksK`, `d.Z₁_le_of_checksK` and the family face
`d.certified_of_checksK`.
-/

open scoped BigOperators Topology
open RadiiPolynomial MvPolyBridge RadiiPolynomial.Certification.Rational

namespace ChebyshevIVP

section KernelFace

variable {L : ℕ} [NeZero L]

/-- Kernel-scale obligations: `Checks` with the `Z₀` conjunct at a `DefectBy` slot `s` with grid
denominator `S` (sound for the exact clause by `defectBy_sound`) and the `ε` conjunct replaced by
per-block certificate data `E` (column checks through `colNormS`, far envelope, row sums). Every
conjunct is ν-free and ℚ-decidable; a certificate may close each by its own `decide +kernel`.
The literals are those of `Checks`: `ν_q / (N + 1)` is the tail factor of
`chebyshev_Z₁_le_relaxed`; the `2` in `2 * derivativeLipschitzBound` is the symmetrization of the
raw displacement (`norm_compPolyDerivative_sub_le`); the radii `C.R i + 2 * C.r₀` bound `‖S(cᵢ)‖`
on the ball (`l1Chebyshev.symmetrize_norm_le`); the last conjunct is the radii polynomial
(`generalRadiiPolynomial_ratCast`); `Mfar N f abar_Q + 1` is the number of columns checked
individually (`chebColNormQ_far` beyond it). -/
abbrev ChebCertQ.ChecksK (C : ChebCertQ L) (s : Z₀Slot) (S : ℕ) (E : Fin L → Fin L → ℚ) (N : ℕ)
    (A_col DF_col : Fin L → Fin L → ℕ → Array ℚ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ)
    (f : Fin L → CompPoly L) (p_q : Fin L → ℚ) : Prop :=
  DefectBy L N A_col DF_col ν_q s S C.Z₀ ∧
    (∀ l, Y₀Q N A_col abar_Q ν_q f p_q l ≤ C.Y₀) ∧
    (∀ i, SnormQ N abar_Q ν_q i ≤ C.R i) ∧
    (∀ l, CompPoly.Chebyshev.derivativeBound (f l) C.R ≤ C.K) ∧
    (∀ l j, ∀ mn < Mfar N f abar_Q + 1,
      colNormS N A_col DF_col abar_Q ν_q f l j mn ≤ E l j * ν_q ^ mn) ∧
    (∀ l j, rowA0Q N A_col ν_q l j ≤ E l j * ν_q ^ (Mfar N f abar_Q + 1)) ∧
    (∀ l, ∑ j, E l j ≤ C.ε) ∧
    C.ε + ν_q / ((N : ℚ) + 1) * C.K ≤ C.Z₁ ∧
    TCnormF N A_col ν_q ≤ C.C ∧
    (∀ l, 2 * CompPoly.Chebyshev.derivativeLipschitzBound (f l)
      (fun i => C.R i + 2 * C.r₀) ≤ C.B) ∧
    C.C * C.B ≤ C.Z₂ ∧
    0 < C.r₀ ∧
    C.Z₂ * C.r₀ ^ 2 - (1 - C.Z₀ - C.Z₁) * C.r₀ + C.Y₀ < 0

/-- **Soundness of the kernel-scale checker**: `ChecksK → Checks`. -/
theorem checks_of_checksK (C : ChebCertQ L) (E : Fin L → Fin L → ℚ) {N : ℕ}
    {A_col DF_col : Fin L → Fin L → ℕ → Array ℚ} {abar_Q : Fin L → Array ℚ} {ν_q : ℚ}
    (hν : 0 < ν_q) {f : Fin L → CompPoly L} {p_q : Fin L → ℚ} (s : Z₀Slot) (S : ℕ)
    (h : C.ChecksK s S E N A_col DF_col abar_Q ν_q f p_q) :
    C.Checks N A_col DF_col abar_Q ν_q f p_q := by
  obtain ⟨hZ₀, hY₀, hR, hK, hcol, hfar, hE, hZ₁, hC, hB, hZ₂, hr₀, hrad⟩ := h
  refine ⟨defectBy_sound s S hZ₀, hY₀, hR, hK, epsGen_le_of_cols N A_col DF_col abar_Q hν f E
    (fun l j mn hmn => ?_) hfar hE, hZ₁, TCnormF_eq N A_col ν_q ▸ hC, hB, hZ₂, hr₀, hrad⟩
  rw [← colNormS_eq]
  exact hcol l j mn hmn

namespace StdChebIVPData

section KernelFaceBundle

variable {ν : PosReal} {N : ℕ} [Fact (1 ≤ (ν : ℝ))]

/-- The `Z₁` operator bound from the kernel-scale checks (the bound `Z₁_le_of_Q` produces). -/
theorem Z₁_le_of_checksK (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    (p : Fin L → ℝ) (p_q : Fin L → ℚ) (C : ChebCertQ L) (E : Fin L → Fin L → ℚ)
    (s : Z₀Slot) (S : ℕ) (h : C.ChecksK s S E N d.A_col d.DF_col d.abar_Q d.ν_q f p_q) :
    ‖d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar‖ ≤ (C.Z₁ : ℝ) := by
  obtain ⟨-, -, hR, hK, hε, hZ₁, -⟩ := checks_of_checksK C E (ν_q_pos d) s S h
  exact Z₁_le_of_Q d f p hR hK hε hZ₁


/-- **Family face, kernel scale.** Existence and uniqueness from the kernel-scale obligations. -/
theorem certified_of_checksK (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L)
    (p : Fin L → ℝ) (p_q : Fin L → ℚ) (hp : ∀ l, p l = (p_q l : ℝ)) (C : ChebCertQ L)
    (E : Fin L → Fin L → ℚ) (s : Z₀Slot) (S : ℕ)
    (h : C.ChecksK s S E N d.A_col d.DF_col d.abar_Q d.ν_q f p_q) :
    ∃! xTilde ∈ Metric.closedBall d.abar (C.r₀ : ℝ), d.G (banachField f) p xTilde = 0 :=
  certified_of_checks d f p p_q hp C (checks_of_checksK C E (ν_q_pos d) s S h)

end KernelFaceBundle

end StdChebIVPData

end KernelFace

end ChebyshevIVP
