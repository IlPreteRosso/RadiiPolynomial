import RadiiPolynomial.Applications.IVP.Chebyshev.Analyticity
import RadiiPolynomial.Applications.IVP.Chebyshev.Polynomial
import RadiiPolynomial.Applications.IVP.VectorField

/-!
# Chebyshev solution faces for a polynomial system

Application layer, one step above `Chebyshev/Analytic.lean` and `Chebyshev/Analyticity.lean`.
Those two modules are deliberately free of any polynomial syntax: they take an arbitrary
coefficient nonlinearity `φ` together with the five structural facts that relate it to the
real vector field. This module supplies all five from one `CompPoly` system `f`:

* the evaluation identity `hφ` — `CompPoly.Chebyshev.eval_eval`;
* differentiability of the preconditioned map — `differentiable_G_of_compPoly`;
* the operator form of `Z₀` — `StdChebIVPData.Z₀_le`;
* strict contractivity of the finite defect — `defect_finBlockNorm_lt_one_of_radii`, read
  off the same four bounds;
* the Lipschitz constant of the vector field — `IVP.vectorField_lipschitzOnWith`, the
  syntactic constant at the trajectory radius, chosen internally.

A certificate therefore supplies the numbers, the four bounds, the radii-polynomial
inequality and a trajectory radius, and nothing structural. The conclusions are stated
for `IVP.vectorField f`, the geometry-free real right-hand side of the same syntax.

The analyticity face strengthens only the *produced* solution: the competitor class stays
`ChebyshevIVP.IsSolution` (continuous with a one-sided derivative), which is weaker than
analyticity, so uniqueness is not silently narrowed.
-/

open RadiiPolynomial MvPolyBridge Set Metric

noncomputable section

namespace ChebyshevIVP

namespace StdChebIVPData

variable {ν : PosReal} {L N : ℕ} [NeZero L] [Fact (1 ≤ (ν : ℝ))]
  (d : StdChebIVPData ν L N) (f : Fin L → CompPoly L) (p : Fin L → ℝ)

/-- **Existence and uniqueness on `[-1, 1]` from one polynomial system.** The
`CompPoly`-driven face of `StdChebIVPData.solution_existsUnique`: the evaluation identity,
the differentiability witness, the operator form of `Z₀` and the strict contractivity of
the finite defect are all derived from `f` and from the four bounds themselves. -/
theorem solution_existsUnique_of_compPoly
    {Y₀ Z₀ Z₁ Z₂_val r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : ‖d.G (banachField f) p d.abar‖ ≤ Y₀)
    (hZ₀fin : finiteBlockMatrixNorm ν d.defect.finBlock ≤ Z₀)
    (hZ₁ : ‖d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar‖ ≤ Z₁)
    (hZ₂ : ∀ c ∈ closedBall d.abar r₀,
      ‖fderiv ℝ (d.G (banachField f) p) c - fderiv ℝ (d.G (banachField f) p) d.abar‖
        ≤ Z₂_val * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂_val) r₀ < 0)
    {R : ℝ} (hR : 2 * (‖d.abar‖ + r₀) ≤ R) :
    ∃ g : ℝ → Fin L → ℝ, IsSolution (IVP.vectorField f) p R g ∧
      ∀ g' : ℝ → Fin L → ℝ, IsSolution (IVP.vectorField f) p R g' →
        EqOn g' g (Icc (-1 : ℝ) 1) :=
  d.solution_existsUnique (banachField f) p (IVP.vectorField f)
    (fun a l _t ht => CompPoly.Chebyshev.eval_eval (f l) a (abs_le.mpr ht))
    (d.defect_finBlockNorm_lt_one_of_radii (banachField f) p hr₀ hY₀ hZ₀fin hZ₁ hZ₂ h_radii)
    (d.differentiable_G_of_compPoly f p) hr₀ hY₀ (d.Z₀_le hZ₀fin) hZ₁ hZ₂ h_radii
    (IVP.vectorField_lipschitzOnWith f (by linarith [norm_nonneg d.abar])) hR

/-- **Sharper existence and uniqueness at weights `ν ≥ 2`**: the contractive trajectory
radius `‖ā‖ + r₀` replaces `2(‖ā‖ + r₀)`. Same derived structural facts as
`solution_existsUnique_of_compPoly`. -/
theorem solution_existsUnique_of_two_le_of_compPoly
    (hν : (2 : ℝ) ≤ (ν : ℝ))
    {Y₀ Z₀ Z₁ Z₂_val r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : ‖d.G (banachField f) p d.abar‖ ≤ Y₀)
    (hZ₀fin : finiteBlockMatrixNorm ν d.defect.finBlock ≤ Z₀)
    (hZ₁ : ‖d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar‖ ≤ Z₁)
    (hZ₂ : ∀ c ∈ closedBall d.abar r₀,
      ‖fderiv ℝ (d.G (banachField f) p) c - fderiv ℝ (d.G (banachField f) p) d.abar‖
        ≤ Z₂_val * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂_val) r₀ < 0)
    {R : ℝ} (hR : ‖d.abar‖ + r₀ ≤ R) :
    ∃ g : ℝ → Fin L → ℝ, IsSolution (IVP.vectorField f) p R g ∧
      ∀ g' : ℝ → Fin L → ℝ, IsSolution (IVP.vectorField f) p R g' →
        EqOn g' g (Icc (-1 : ℝ) 1) :=
  d.solution_existsUnique_of_two_le (banachField f) p (IVP.vectorField f) hν
    (fun a l _t ht => CompPoly.Chebyshev.eval_eval (f l) a (abs_le.mpr ht))
    (d.defect_finBlockNorm_lt_one_of_radii (banachField f) p hr₀ hY₀ hZ₀fin hZ₁ hZ₂ h_radii)
    (d.differentiable_G_of_compPoly f p) hr₀ hY₀ (d.Z₀_le hZ₀fin) hZ₁ hZ₂ h_radii
    (IVP.vectorField_lipschitzOnWith f (by linarith [norm_nonneg d.abar])) hR

/-- **The produced solution is real analytic across the endpoints.** Same hypotheses as
`solution_existsUnique_of_two_le_of_compPoly`; `2 ≤ ν` already gives the `1 < ν` that
`analyticOnNhd_x_sol` needs. Uniqueness is still stated against the weaker `IsSolution`
competitor class, so the statement strengthens the witness and not the uniqueness claim. -/
theorem analytic_solution_existsUnique_of_two_le_of_compPoly
    (hν : (2 : ℝ) ≤ (ν : ℝ))
    {Y₀ Z₀ Z₁ Z₂_val r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : ‖d.G (banachField f) p d.abar‖ ≤ Y₀)
    (hZ₀fin : finiteBlockMatrixNorm ν d.defect.finBlock ≤ Z₀)
    (hZ₁ : ‖d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar‖ ≤ Z₁)
    (hZ₂ : ∀ c ∈ closedBall d.abar r₀,
      ‖fderiv ℝ (d.G (banachField f) p) c - fderiv ℝ (d.G (banachField f) p) d.abar‖
        ≤ Z₂_val * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂_val) r₀ < 0)
    {R : ℝ} (hR : ‖d.abar‖ + r₀ ≤ R) :
    ∃ g : ℝ → Fin L → ℝ, AnalyticOnNhd ℝ g (Icc (-1 : ℝ) 1) ∧
      IsSolution (IVP.vectorField f) p R g ∧
      ∀ g' : ℝ → Fin L → ℝ, IsSolution (IVP.vectorField f) p R g' →
        EqOn g' g (Icc (-1 : ℝ) 1) := by
  obtain ⟨xTilde, hball, hG⟩ :=
    (d.existsUnique_of_compPoly f p hr₀ hY₀ hZ₀fin hZ₁ hZ₂ h_radii).exists
  have hφ : ∀ (a : XCheb ν L) (l : Fin L) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 →
      l1Chebyshev.eval (banachField f a l) t =
        IVP.vectorField f (fun i => l1Chebyshev.eval (a i) t) l :=
    fun a l _t ht => CompPoly.Chebyshev.eval_eval (f l) a (abs_le.mpr ht)
  have hZ₀_lt_one :=
    d.defect_finBlockNorm_lt_one_of_radii (banachField f) p hr₀ hY₀ hZ₀fin hZ₁ hZ₂ h_radii
  refine ⟨x_sol xTilde,
    analyticOnNhd_x_sol (lt_of_lt_of_le one_lt_two hν) xTilde,
    d.x_sol_isSolution_of_two_le (banachField f) p (IVP.vectorField f) xTilde hν hφ
      hZ₀_lt_one hball hG hR,
    fun g' hg' => d.solution_eq_canonical_of_two_le (banachField f) p (IVP.vectorField f)
      xTilde hν hφ hZ₀_lt_one
      (IVP.vectorField_lipschitzOnWith f (by linarith [norm_nonneg d.abar]))
      hball hG hR g' hg'⟩

end StdChebIVPData

end ChebyshevIVP

end
