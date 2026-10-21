import RadiiPolynomial.Certification.PowerSeries.PolynomialZero

/-!
# Test (family PS): generality witness for the polynomial-zero face, degree 3

Not part of the default build (imported by no module); build it with
`lake build RadiiPolynomial.Examples.tests.PS.Cubic`.

`x·x·x - x = 6 + t` on `ℓ¹_ν`, `ν = 1`, `N = 10`: the exact root of `a₀³ - a₀ = 6` is `a₀ = 2`
with `P′(a₀) = 11`. The approximate zero `x̄`, the lower-triangular approximate inverse (the
Cauchy matrix of the rationalised Taylor coefficients `bQ` of `1/P′(x̄)`) and the bounds are exact
rationals; one `decide +kernel` checks them, and `PolyZeroData.existsUnique` gives a unique
power-series zero within `10⁻⁶` of `x̄`.
-/

open RadiiPolynomial MvPolyBridge

namespace Tests.PS

/-- Rationalised Taylor coefficients of `1/P′(x̄)`: the columns of the approximate inverse. -/
def bQ : Array ℚ := #[909090909090909/10000000000000000, -90157776108189/10000000000000000,
  11362860211983/10000000000000000, -384868588673/2500000000000000,
  108049470721/5000000000000000, -484128461/156250000000000, 2252942923/5000000000000000,
  -330980211/5000000000000000, 9799619/1000000000000000, -7297193/5000000000000000,
  2183999/10000000000000000]

/-- The cubic's certificate data. -/
def cub : PolyZeroData where
  P := .sub (.mul (.mul (.X 0) (.X 0)) (.X 0)) (.X 0)
  N := 10
  νq := 1
  aQ := #[2, 909090909090909/10000000000000000, -9015777610819/2000000000000000,
    3787620070661/10000000000000000, -384868588673/10000000000000000,
    84413649/19531250000000, -5164036917/10000000000000000, 321848989/5000000000000000,
    -82745053/10000000000000000, 5444233/5000000000000000, -1459439/10000000000000000]
  cQ := #[6, 1]
  Acols := fun j => Array.ofFn fun i : Fin 11 => if (j : ℕ) ≤ i then bQ.getD ((i : ℕ) - j) 0 else 0
  r₀ := 1/1000000
  Y₀ := 2069/100000000000000
  Z₀ := 3083/1000000000000000000
  Z₁ := 1021/10000
  Z₂ := 637/500

theorem cub_checks : cub.Checks := by decide +kernel

noncomputable def ν₁ : PosReal := ⟨1, one_pos⟩

/-- The same stored candidate, constructed directly from its finite coefficients. -/
noncomputable def candidate : l1Weighted ν₁ :=
  l1Weighted.mk (fun n => ((cub.aQ.getD n 0 : ℚ) : ℝ)) (by
    rw [l1Weighted.mem_iff]
    refine summable_of_ne_finset_zero (s := Finset.range cub.aQ.size) fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hn]
    simp)

/-- The same forcing coefficients `[6,1]`, with zero padding. -/
noncomputable def forcing : l1Weighted ν₁ :=
  l1Weighted.mk (fun n => (((#[6, 1] : Array ℚ).getD n 0 : ℚ) : ℝ)) (by
    rw [l1Weighted.mem_iff]
    refine summable_of_ne_finset_zero (s := Finset.range (#[6, 1] : Array ℚ).size) fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hn]
    simp)

theorem candidate_coeff (n : ℕ) : l1Weighted.toSeq candidate n = (cub.a n : ℝ) := rfl
theorem forcing_coeff (n : ℕ) : l1Weighted.toSeq forcing n = (cub.cq n : ℝ) := rfl


/-- A unique power-series zero of `x³ - x - (6 + t)` within `10⁻⁶` of `x̄` in `ℓ¹_1`. -/
theorem cub_existsUnique :
    ∃! x ∈ Metric.closedBall candidate ((1/1000000 : ℚ) : ℝ),
      x * x * x - x - forcing = 0 := by
  have h := cub.existsUnique (ν := ν₁)
    (by show (1 : ℝ) = ((1 : ℚ) : ℝ); norm_num) candidate forcing
    candidate_coeff forcing_coeff cub_checks
  simpa only [CompPoly.polyMap, cub, CompPoly.evalBanach] using h

end Tests.PS
