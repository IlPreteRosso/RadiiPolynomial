import RadiiPolynomial.Core.Theorem

/-!
# `ℚ` margin tools for the radii polynomial

Kernel-decidable `ℚ` mirrors of the radii polynomial and their casts to `ℝ`:
* `radiiPolyQ Y₀ Z₀ cs r` — the `ℚ` mirror of `radiiPolynomial` with `Z₂ = hornerEval cs`
  (a coefficient list of any length), with the cast identity `radiiPolyQ_cast` and the soundness
  lemma `radiiPolynomial_neg_of_Q` (one `decide +kernel` check on `radiiPolyQ … < 0` discharges
  `radiiPolynomial … r < 0` at the cast data);
* `generalRadiiPolynomial_ratCast` — `generalRadiiPolynomial` with a constant `Z₂` at rational
  data is the cast of a rational value.
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

/-- The general radii polynomial with a constant `Z₂` at rational data is the cast of a rational
value. -/
theorem generalRadiiPolynomial_ratCast (Y₀ Z₀ Z₁ Z₂ r : ℚ) :
    generalRadiiPolynomial (Y₀ : ℝ) (Z₀ : ℝ) (Z₁ : ℝ) (fun _ => (Z₂ : ℝ)) (r : ℝ) =
      ((Z₂ * r ^ 2 - (1 - Z₀ - Z₁) * r + Y₀ : ℚ) : ℝ) := by
  unfold generalRadiiPolynomial; push_cast; ring

end RadiiPolynomial
