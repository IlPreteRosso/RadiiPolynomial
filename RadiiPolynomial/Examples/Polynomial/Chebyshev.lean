import RadiiPolynomial.Algebra.Polynomial
import RadiiPolynomial.Tactic.MakeCompPoly

/-!
# Independent finite Chebyshev polynomial consumers

The main example is `p(x,y) = 3 + (3/2)xy - x² - y` at `x = 1 + T₁` and
`y = 2 + T₂/2`. Its coefficient table and two symbolic partials are computed
independently of the implementation. A separate `T₅²` example detects the
high-to-low interaction that a Taylor Cauchy product would miss.

The exact rational identities use `native_decide`. The propagated support bound
extends the main coefficient table to every mode; completed-algebra bridges
connect it to actual Banach inputs.

The last section reifies the logistic nonlinearity with `compPolyOf%` directly over
the Chebyshev carrier and reads its certificate constants off the syntax
(`derivativeBound`, `derivativeLipschitzBound`, `lipschitzBound`): the reifier and
the bounds are geometry-free, only the adapter's `eval` is Chebyshev-specific.
-/

open MvPolyBridge RadiiPolynomial

namespace ChebyshevPolynomialExample

/-- A polynomial with a genuine cross term and every arithmetic AST constructor. -/
def mixedPolynomial : CompPoly 2 :=
  .sub (.add (.add (.C 3) (.smul (3 / 2) (.mul (.X 0) (.X 1))))
    (.neg (.mul (.X 0) (.X 0)))) (.X 1)

/-- Stored coefficients: the physical interpretation doubles positive Chebyshev modes. -/
def inputArrays : Fin 2 → Array ℚ := ![#[1, 1 / 2], #[2, 0, 1 / 4]]

/-- Laurent coefficients of `p(1+T₁, 2+T₂/2)`. -/
def expectedCoefficient (k : ℤ) : ℚ :=
  match k.natAbs with
  | 0 => 5 / 2
  | 1 => 11 / 16
  | 2 => -(1 / 8)
  | 3 => 3 / 16
  | _ => 0

/-- Both signs, the constant term, and the first zero modes match the hand calculation. -/
theorem mixed_coefficients :
    ∀ i : Fin 11, mixedPolynomial.evalChebCoeff inputArrays ((i : ℤ) - 5) =
      expectedCoefficient ((i : ℤ) - 5) := by
  native_decide

/-- The finite table and the propagated support bound determine every output mode. -/
theorem mixed_coefficients_all (k : ℤ) :
    mixedPolynomial.evalChebCoeff inputArrays k = expectedCoefficient k := by
  by_cases hk : k.natAbs ≤ 5
  · have hi : (k + 5).toNat < 11 := by omega
    have he : (((k + 5).toNat : ℕ) : ℤ) - 5 = k := by omega
    simpa only [he] using mixed_coefficients ⟨(k + 5).toNat, hi⟩
  · rw [mixedPolynomial.evalChebCoeff_eq_zero_of_radius_lt inputArrays k (by
      simpa [mixedPolynomial, CompPoly.laurentRadius, inputArrays] using Nat.lt_of_not_ge hk)]
    unfold expectedCoefficient
    split <;> norm_num <;> omega

/-- The first partial is `(3/2)y - 2x`, including its negative modes. -/
theorem first_partial_coefficients :
    ∀ i : Fin 7, (mixedPolynomial.pderiv 0).evalChebCoeff inputArrays ((i : ℤ) - 3) =
      (match (((i : ℤ) - 3).natAbs) with
        | 0 => 1
        | 1 => -1
        | 2 => 3 / 8
        | _ => 0) := by
  native_decide

/-- The second partial is `(3/2)x - 1`; this also checks variable separation. -/
theorem second_partial_coefficients :
    ∀ i : Fin 7, (mixedPolynomial.pderiv 1).evalChebCoeff inputArrays ((i : ℤ) - 3) =
      (match (((i : ℤ) - 3).natAbs) with
        | 0 => 1 / 2
        | 1 => 3 / 4
        | _ => 0) := by
  native_decide

/-- Symmetric rational input sequences, independent of an evaluation bound. -/
def symmetricInputs (i : Fin 2) (k : ℤ) : ℚ := (inputArrays i).getD k.natAbs 0

/-- The sharp support radii are one and two, rather than the array sizes two and three. -/
def minimalRadii (i : Fin 2) : ℕ := (inputArrays i).size - 1

/-- The chosen radii really bound the supplied data. -/
theorem inputs_supported :
    ∀ (i : Fin 2) (k : ℤ), minimalRadii i < k.natAbs → symmetricInputs i k = 0 := by
  intro i k hk
  have hout : ¬k.natAbs < (inputArrays i).size := by
    simp only [minimalRadii] at hk
    omega
  simp [symmetricInputs, Array.getD, hout]

/-- Padding every input radius by seven remains valid. -/
theorem inputs_supported_padded :
    ∀ (i : Fin 2) (k : ℤ), minimalRadii i + 7 < k.natAbs → symmetricInputs i k = 0 := by
  intro i k hk
  exact inputs_supported i k (by omega)

/-- The same mixed polynomial is unchanged at every mode by valid support overestimates. -/
theorem support_bound_independent (k : ℤ) :
    mixedPolynomial.evalLaurentCoeffSeq minimalRadii symmetricInputs k =
      mixedPolynomial.evalLaurentCoeffSeq (fun i => minimalRadii i + 7) symmetricInputs k :=
  mixedPolynomial.evalLaurentCoeffSeq_eq_of_support _ _ _
    inputs_supported inputs_supported_padded k

/-- A single high Chebyshev mode, stored with the usual half coefficient. -/
def highMode : Fin 1 → Array ℚ := fun _ => #[0, 0, 0, 0, 0, 1 / 2]

/-- Squaring the single input is independent of the multivariate consumer. -/
def squarePolynomial : CompPoly 1 := .mul (.X 0) (.X 0)

/-- `T₅² = (1 + T₁₀)/2`, including the constant contribution from opposite modes. -/
theorem high_mode_square :
    squarePolynomial.evalChebCoeff highMode 0 = 1 / 2 ∧
    squarePolynomial.evalChebCoeff highMode 10 = 1 / 4 ∧
    squarePolynomial.evalChebCoeff highMode (-10) = 1 / 4 ∧
    squarePolynomial.evalChebCoeff highMode 5 = 0 := by
  native_decide

/-- Applying the Taylor interpreter to the same storage loses the constant term. -/
theorem taylor_interpreter_misses_constant :
    squarePolynomial.evalCoeff highMode 0 = 0 ∧
    squarePolynomial.evalCoeff highMode 0 ≠ squarePolynomial.evalChebCoeff highMode 0 := by
  native_decide

section Semantic

variable {ν : PosReal} [Fact (1 ≤ (ν : ℝ))]

/-- Actual finite stored Banach-algebra elements realizing the two arrays. -/
noncomputable def storedInputs : Fin 2 → l1Chebyshev ν :=
  ![l1Chebyshev.single 0 1 + l1Chebyshev.single 1 (1 / 2),
    l1Chebyshev.single 0 2 + l1Chebyshev.single 2 (1 / 4)]

/-- The finite Banach elements agree with the rational storage at every nonnegative mode. -/
theorem stored_inputs_coefficients (i : Fin 2) (k : ℕ) :
    l1Chebyshev.toSeq (storedInputs (ν := ν) i) (k : ℤ) =
      ((inputArrays i).getD k 0 : ℝ) := by
  by_cases hk : k < 3
  · interval_cases k <;> fin_cases i <;>
      norm_num [storedInputs, inputArrays, l1Chebyshev.toSeq_single]
  · fin_cases i <;>
      simp [storedInputs, inputArrays, l1Chebyshev.toSeq_single, Array.getD, hk,
        show ¬k < 2 by omega, show k ≠ 0 by omega,
        show k ≠ 1 by omega, show (k : ℤ) ≠ 2 by omega]

/-- The generic bridge specializes to the actual finite-single inputs. -/
theorem semantic_coefficients (k : ℤ) :
    l1Chebyshev.toSeq (CompPoly.Chebyshev.eval mixedPolynomial (storedInputs (ν := ν))) k =
      (mixedPolynomial.evalChebCoeff inputArrays k : ℝ) :=
  mixedPolynomial.toSeq_evalBanach_cheb_of_coeffs _ _ stored_inputs_coefficients k

/-- The computed nonzero constant is consequently a coefficient of the completed object. -/
theorem semantic_constant :
    l1Chebyshev.toSeq (CompPoly.Chebyshev.eval mixedPolynomial (storedInputs (ν := ν))) 0 =
      (5 / 2 : ℝ) := by
  rw [semantic_coefficients]
  have h := mixed_coefficients (5 : Fin 11)
  norm_num [expectedCoefficient] at h
  rw [h]
  norm_num

/-- Negative storage directions are annihilated by the symmetrization in the derivative. -/
theorem derivative_ignores_negative_storage (m : ℕ) :
    fderiv ℝ (CompPoly.Chebyshev.eval mixedPolynomial) (storedInputs (ν := ν))
      ![l1Chebyshev.single (Int.negSucc m) 1, 0] = 0 := by
  rw [CompPoly.Chebyshev.fderiv_eval_apply]
  simp [Fin.sum_univ_two, l1Chebyshev.symmetrize_single_negSucc,
    show l1Chebyshev.symmetrize (0 : l1Chebyshev ν) = 0 from
      (l1Chebyshev.symmetrize_CLM (ν := ν)).map_zero]

end Semantic


/-! ## Reification parity: `compPolyOf%` over the Chebyshev carrier -/

/-! The two production certificates check the same parity on their own nonlinearity:
`Example81.f_cpoly_reified` and `Example1421.f_cpoly_reified` state that the literal
`f_cpoly` each example ships is definitionally what `compPolyOf%` produces from the
nonlinearity's own lambda, so the elaborator has certificate-level consumers in both
geometries. -/

/-- Weight for the reified example (any `ν ≥ 1` works; `2` matches Example 14.2.1). -/
def νr : PosReal := ⟨2, by norm_num⟩

instance : Fact ((1 : ℝ) ≤ (νr : ℝ)) := ⟨by rw [show ((νr : ℝ)) = 2 from rfl]; norm_num⟩

/-- The logistic nonlinearity `u ↦ u² − u`, reified from a lambda over the Chebyshev
carrier rather than written as a literal AST. -/
def logisticReified : CompPoly 1 :=
  compPolyOf% (fun u : Fin 1 → l1Chebyshev νr => u 0 * u 0 - u 0)

/-- The same lambda over `ℝ` reifies to the same syntax: the reifier is geometry-free. -/
def logisticReal : CompPoly 1 :=
  compPolyOf% (fun u : Fin 1 → ℝ => u 0 * u 0 - u 0)

theorem logisticReified_eq_literal : logisticReified = .X 0 * .X 0 - .X 0 := rfl

theorem logisticReal_eq_logisticReified : logisticReal = logisticReified := rfl

/-- Inline rational literals are constants after elaboration resolves their instances. -/
theorem rationalConstant_reified :
    (compPolyOf% (fun _ : Fin 1 → ℝ => ((3 / 2 : ℚ) : ℝ)) : CompPoly 1) =
      .C (3 / 2) := rfl

/-- Explicit scalar embeddings reify to the same rational constant in any real algebra. -/
theorem algebraMapConstant_reified {R : Type*} [CommRing R] [Algebra ℝ R] :
    (compPolyOf% (fun _ : Fin 1 → R => algebraMap ℝ R ((3 / 2 : ℚ) : ℝ)) : CompPoly 1) =
      .C (3 / 2) := rfl

/-- A rational constant remains recognizable inside a polynomial with a variable. -/
theorem affineConstant_reified :
    (compPolyOf% (fun u : Fin 1 → l1Chebyshev νr =>
      u 0 + algebraMap ℝ (l1Chebyshev νr) ((3 / 2 : ℚ) : ℝ)) : CompPoly 1) =
      .X 0 + .C (3 / 2) := rfl

/-- A constant, a rational scalar and a cross term reify over the Chebyshev carrier as well;
this is `mixedPolynomial` up to the associativity of the literal AST. -/
def mixedReified : CompPoly 2 :=
  compPolyOf% (fun u : Fin 2 → l1Chebyshev νr =>
    (3 : l1Chebyshev νr) + ((3 / 2 : ℚ) : ℝ) • (u 0 * u 1) - u 0 * u 0 - u 1)

theorem mixedReified_eq_literal :
    mixedReified = .C 3 + .smul (3 / 2) (.X 0 * .X 1) - .X 0 * .X 0 - .X 1 := rfl

/-- The adapter interprets the reified syntax on symmetrized inputs, definitionally. -/
theorem logisticReified_eval (a : Fin 1 → l1Chebyshev νr) :
    CompPoly.Chebyshev.eval logisticReified a =
      l1Chebyshev.symmetrize (a 0) * l1Chebyshev.symmetrize (a 0)
        - l1Chebyshev.symmetrize (a 0) := rfl

/-- The Z₁ operator constant of Example 14.2.1 (`K = 512/100`) is the syntactic constant
of the reified polynomial at the certified radius `39/50`, in exact rational arithmetic. -/
theorem logisticReified_derivativeBound :
    CompPoly.Chebyshev.derivativeBound logisticReified (fun _ : Fin 1 => (39 / 50 : ℚ)) =
      512 / 100 := by
  simp [CompPoly.Chebyshev.derivativeBound, logisticReified]
  norm_num

/-- The Z₂ Lipschitz constant of the derivative is `4` on every ball (the derivative of
`u² − u` is affine), giving `8‖c − ā‖` after symmetrizing the displacement. -/
theorem logisticReified_derivativeLipschitzBound (R : Fin 1 → ℚ) :
    CompPoly.Chebyshev.derivativeLipschitzBound logisticReified R = 4 := by
  simp [CompPoly.Chebyshev.derivativeLipschitzBound, logisticReified]
  norm_num

/-- The real vector field's Lipschitz constant on `closedBall 0 R` is `2R + 1`. -/
theorem logisticReal_lipschitzBound (R : ℝ) :
    logisticReal.lipschitzBound (fun _ : Fin 1 => R) = 2 * R + 1 := by
  simp [logisticReal]
  ring

end ChebyshevPolynomialExample
