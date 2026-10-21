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

/-- Polynomial structural obligations for a proved uniform evaluator bound, exposing
one canonical coefficient witness. The default, contractive and analytic sockets all
consume this face; only the evaluator bound and trajectory radius vary. -/
theorem exists_canonical_solution_of_compPoly_of_evalBound
    (C : NNReal)
    (h_eval : ∀ (t : ℝ) (ht : |t| ≤ 1),
      ‖(l1Chebyshev.evalAtCLM t ht : l1Chebyshev ν →L[ℝ] ℝ)‖ ≤ (C : ℝ))
    {Y₀ Z₀ Z₁ Z₂_val r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hY₀ : ‖d.G (banachField f) p d.abar‖ ≤ Y₀)
    (hZ₀fin : finiteBlockMatrixNorm ν d.defect.finBlock ≤ Z₀)
    (hZ₁ : ‖d.composedApproxCLM - fderiv ℝ (d.G (banachField f) p) d.abar‖ ≤ Z₁)
    (hZ₂ : ∀ c ∈ closedBall d.abar r₀,
      ‖fderiv ℝ (d.G (banachField f) p) c - fderiv ℝ (d.G (banachField f) p) d.abar‖
        ≤ Z₂_val * r₀)
    (h_radii : generalRadiiPolynomial Y₀ Z₀ Z₁ (fun _ => Z₂_val) r₀ < 0)
    {R : ℝ} (hR : (C : ℝ) * (‖d.abar‖ + r₀) ≤ R) :
    ∃ xTilde : XCheb ν L, IsSolution (IVP.vectorField f) p R (x_sol xTilde) ∧
      ∀ g' : ℝ → Fin L → ℝ, IsSolution (IVP.vectorField f) p R g' →
        EqOn g' (x_sol xTilde) (Icc (-1 : ℝ) 1) :=
  d.solution_existsUnique_of_evalBound (banachField f) p (IVP.vectorField f) C h_eval
    (fun a l _t ht => CompPoly.Chebyshev.eval_eval (f l) a (abs_le.mpr ht))
    (d.defect_finBlockNorm_lt_one_of_radii (banachField f) p hr₀ hY₀ hZ₀fin hZ₁ hZ₂ h_radii)
    (d.differentiable_G_of_compPoly f p) hr₀ hY₀ (d.Z₀_le hZ₀fin) hZ₁ hZ₂ h_radii
    (IVP.vectorField_lipschitzOnWith f
      ((mul_nonneg C.coe_nonneg (add_nonneg (norm_nonneg _) hr₀.le)).trans hR)) hR

/-- Existence and uniqueness with the default storage evaluation bound `2`.
The socket chooses its evaluator witness internally. -/
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
        EqOn g' g (Icc (-1 : ℝ) 1) := by
  obtain ⟨xTilde, hsol, huniq⟩ :=
    d.exists_canonical_solution_of_compPoly_of_evalBound f p 2
      (fun t ht => l1Chebyshev.norm_evalAtCLM_le t ht)
      hr₀ hY₀ hZ₀fin hZ₁ hZ₂ h_radii (by simpa using hR)
  exact ⟨x_sol xTilde, hsol, huniq⟩

/-- Existence and uniqueness with the contractive storage evaluation bound at `2 ≤ ν`.
The socket chooses bound `1` and its proved evaluator witness internally. -/
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
        EqOn g' g (Icc (-1 : ℝ) 1) := by
  obtain ⟨xTilde, hsol, huniq⟩ :=
    d.exists_canonical_solution_of_compPoly_of_evalBound f p 1
      (fun t ht => l1Chebyshev.norm_evalAtCLM_le_of_two_le hν t ht)
      hr₀ hY₀ hZ₀fin hZ₁ hZ₂ h_radii (by simpa using hR)
  exact ⟨x_sol xTilde, hsol, huniq⟩

/-- At `2 ≤ ν`, the canonical solution is analytic across the endpoints.
Uniqueness retains the weaker `IsSolution` competitor class. -/
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
  obtain ⟨xTilde, hsol, huniq⟩ :=
    d.exists_canonical_solution_of_compPoly_of_evalBound f p 1
      (fun t ht => l1Chebyshev.norm_evalAtCLM_le_of_two_le hν t ht)
      hr₀ hY₀ hZ₀fin hZ₁ hZ₂ h_radii (by simpa using hR)
  exact ⟨x_sol xTilde, analyticOnNhd_x_sol (lt_of_lt_of_le one_lt_two hν) xTilde,
    hsol, huniq⟩

end StdChebIVPData

end ChebyshevIVP

end
