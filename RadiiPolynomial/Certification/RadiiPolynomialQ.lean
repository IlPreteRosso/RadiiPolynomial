import RadiiPolynomial.Core.Theorem

/-!
# `ℚ` margin tools for the radii polynomial

Kernel-decidable `ℚ` mirrors of the radii polynomial and their casts to `ℝ`:
* `radiiPolyQ Y₀ Z₀ cs r` — the `ℚ` mirror of `radiiPolynomial` with `Z₂ = hornerEval cs`
  (a coefficient list of any length), with the cast identity `radiiPolyQ_cast` and the soundness
  lemma `radiiPolynomial_neg_of_Q` (one `decide +kernel` check on `radiiPolyQ … < 0` discharges
  `radiiPolynomial … r < 0` at the cast data);
* `generalRadiiPolynomial_neg_of_Q` — the same check for `generalRadiiPolynomial`, reusing
  `radiiPolyQ` at `Z₀ + Z₁` (no separate evaluator; `Z₂` enters only through its value at `r`);
* `generalRadiiPolynomial_ratCast` — `generalRadiiPolynomial` with a constant `Z₂` at rational
  data is the cast of a rational value, and `generalRadiiPolynomial_neg_of_Q_const` reduces its
  negativity to one rational inequality.
-/

namespace RadiiPolynomial





/-- The general radii polynomial with a constant `Z₂` at rational data is the cast of a rational
value. -/
theorem generalRadiiPolynomial_ratCast (Y₀ Z₀ Z₁ Z₂ r : ℚ) :
    generalRadiiPolynomial (Y₀ : ℝ) (Z₀ : ℝ) (Z₁ : ℝ) (fun _ => (Z₂ : ℝ)) (r : ℝ) =
      ((Z₂ * r ^ 2 - (1 - Z₀ - Z₁) * r + Y₀ : ℚ) : ℝ) := by
  unfold generalRadiiPolynomial; push_cast; ring

/-- Negativity of the general radii polynomial with a constant `Z₂` at rational data reduces to
one rational inequality. -/
theorem generalRadiiPolynomial_neg_of_Q_const (Y₀ Z₀ Z₁ Z₂ q : ℚ)
    (hQ : Z₂ * q ^ 2 - (1 - Z₀ - Z₁) * q + Y₀ < 0) :
    generalRadiiPolynomial (Y₀ : ℝ) (Z₀ : ℝ) (Z₁ : ℝ) (fun _ => (Z₂ : ℝ)) (q : ℝ) < 0 := by
  rw [generalRadiiPolynomial_ratCast]
  exact_mod_cast hQ

end RadiiPolynomial
