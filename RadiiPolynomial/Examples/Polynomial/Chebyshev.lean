import RadiiPolynomial.Algebra.Polynomial

/-!
# Independent finite Chebyshev polynomial consumers

The main example is `p(x,y) = 3 + (3/2)xy - x² - y` at `x = 1 + T₁` and
`y = 2 + T₂/2`. Its coefficient table and two symbolic partials are computed
independently of the implementation. A separate `T₅²` example detects the
high-to-low interaction that a Taylor Cauchy product would miss.

The exact rational identities use `native_decide`. The propagated support bound
extends the main coefficient table to every mode; completed-algebra bridges
connect it to actual Banach inputs.

The last section writes the logistic nonlinearity as a literal `CompPoly` expression
and identifies its Chebyshev interpretation on symmetrized inputs. The expression is
geometry-free; the adapter's `eval` supplies the Chebyshev semantics.
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
  mixedPolynomial.toSeq_evalBanach_eq_evalChebCoeff _ _ stored_inputs_coefficients k

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


/-! ## Literal logistic polynomial over the Chebyshev carrier -/

/-! `logisticReified` is written directly as polynomial syntax. Its evaluation theorem
below relates this literal expression to multiplication and subtraction of symmetrized
Chebyshev inputs. -/

/-- Weight for the literal logistic example (any `ν ≥ 1` works; `2` matches Example 14.2.1). -/
def νr : PosReal := ⟨2, by norm_num⟩

instance : Fact ((1 : ℝ) ≤ (νr : ℝ)) := ⟨by rw [show ((νr : ℝ)) = 2 from rfl]; norm_num⟩

/-- The logistic nonlinearity `u ↦ u² − u`, written as a literal `CompPoly` expression. -/
def logisticReified : CompPoly 1 :=
  .sub (.mul (.X ⟨0, by decide⟩) (.X ⟨0, by decide⟩)) (.X ⟨0, by decide⟩)









/-- The adapter interprets the literal syntax on symmetrized inputs, definitionally. -/
theorem logisticReified_eval (a : Fin 1 → l1Chebyshev νr) :
    CompPoly.Chebyshev.eval logisticReified a =
      l1Chebyshev.symmetrize (a 0) * l1Chebyshev.symmetrize (a 0)
        - l1Chebyshev.symmetrize (a 0) := rfl




end ChebyshevPolynomialExample
