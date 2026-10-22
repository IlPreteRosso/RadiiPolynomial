import RadiiPolynomial.Core.Theorem

/-!
# `ℚ` margin tools for the radii polynomial

Kernel-decidable `ℚ` mirrors of the general radii polynomial with a constant `Z₂` and their
casts to `ℝ`:
* `generalRadiiPolynomial_ratCast` — `generalRadiiPolynomial` with a constant `Z₂` at rational
  data is the cast of the rational value `Z₂ r² - (1 - Z₀ - Z₁) r + Y₀`;
* `generalRadiiPolynomial_neg_of_Q_const` — its negativity reduces to one rational inequality
  (one decidable check on `ℚ` discharges `generalRadiiPolynomial … r < 0` at the cast data).
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
