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

/-- `ℚ` mirror of `radiiPolynomial` with `Z₂ = hornerEval cs` (a coefficient list of any
length). -/
def radiiPolyQ (Y₀ Z₀ : ℚ) (cs : List ℚ) (r : ℚ) : ℚ :=
  hornerEval cs r * r ^ 2 - (1 - Z₀) * r + Y₀

/-- The cast identity of `radiiPolyQ` (no sign condition). -/
theorem radiiPolyQ_cast (Y₀ Z₀ : ℚ) (cs : List ℚ) (r : ℚ) :
    ((radiiPolyQ Y₀ Z₀ cs r : ℚ) : ℝ) =
      radiiPolynomial Y₀ Z₀ (hornerEval (cs.map (Rat.cast : ℚ → ℝ))) r := by
  have h := map_hornerEval (Rat.castHom ℝ) cs r
  simp only [Rat.coe_castHom] at h
  simp only [radiiPolyQ, radiiPolynomial, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_one, h]

/-- Soundness of the `ℚ` endpoint check (one `decide +kernel` on `radiiPolyQ … < 0`); general in
`cs`, with `Z₂` identified with the cast Horner polynomial at the one radius `r` only. -/
theorem radiiPolynomial_neg_of_Q {Y₀ Z₀ r : ℝ} {Z₂ : ℝ → ℝ} {y z q : ℚ} {cs : List ℚ}
    (hY : Y₀ = y) (hZ : Z₀ = z) (hZ₂ : Z₂ r = hornerEval (cs.map (Rat.cast : ℚ → ℝ)) r)
    (hr : r = q) (hQ : radiiPolyQ y z cs q < 0) : radiiPolynomial Y₀ Z₀ Z₂ r < 0 := by
  have hc : ((radiiPolyQ y z cs q : ℚ) : ℝ) < 0 := by exact_mod_cast hQ
  rw [radiiPolyQ_cast, ← hY, ← hZ, ← hr] at hc
  simpa only [radiiPolynomial, hZ₂] using hc

/-- Soundness of the `ℚ` endpoint check for the general radii polynomial: `radiiPolyQ` at
`Z₀ + Z₁` discharges `generalRadiiPolynomial … r < 0`, with `Z₂` identified with the cast Horner
polynomial at the one radius `r` only. -/
theorem generalRadiiPolynomial_neg_of_Q {Y₀ Z₀ Z₁ r : ℝ} {Z₂ : ℝ → ℝ} {y z₀ z₁ q : ℚ}
    {cs : List ℚ} (hY : Y₀ = y) (hZ₀ : Z₀ = z₀) (hZ₁ : Z₁ = z₁)
    (hZ₂ : Z₂ r = hornerEval (cs.map (Rat.cast : ℚ → ℝ)) r) (hr : r = q)
    (hQ : radiiPolyQ y (z₀ + z₁) cs q < 0) : generalRadiiPolynomial Y₀ Z₀ Z₁ Z₂ r < 0 := by
  have h := radiiPolynomial_neg_of_Q (Z₀ := Z₀ + Z₁) hY (by rw [hZ₀, hZ₁, Rat.cast_add]) hZ₂ hr hQ
  simpa only [radiiPolynomial, generalRadiiPolynomial, sub_add_eq_sub_sub] using h

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
