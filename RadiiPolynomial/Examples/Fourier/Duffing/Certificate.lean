import RadiiPolynomial.Applications.Fourier.Duffing
import RadiiPolynomial.Certification.RadiiPolynomialQ
import RadiiPolynomial.Examples.Fourier.Duffing.Numbers

/-!
# Book §10.1 Helmholtz–Duffing on `ℓ²_{6/5}`: the numerical closure

The concrete certificate at our own rational centre for the data `c = (1/10, 4, 1)`, `N = 10`,
`ν = 6/5` of book §10.1 (`ch10.tex:155–158`), and the endpoint: the raw Fourier map
`F_n(a) = (−n² + i n/10 + 4) aₙ − (a ⋆ a)ₙ − bₙ`, `b_{±1} = 1/2`, has a unique zero in the closed
ball of radius `1/200000` around the candidate `ā` in `ℓ²_{6/5}`; the zero is unique in the ball of
radius `1/25` and conjugate-symmetric (`conj ã₋ₙ = ãₙ`).

The candidate, the head matrix and the constants are the consumer-owned rational leaf `leaf` of
`Examples/Fourier/Duffing/Numbers.lean` (generated). The rational-leaf adapter
`Certification/Fourier/Quadratic.lean` turns it into the head certificate `cert` of the Duffing
family `Applications/Fourier/Duffing.lean` and its bounds (`QuadFourierLeafQ.cert_spec`). This
file supplies the bridges of the instance (`ν = 6/5`, the symbol and forcing mirrors), the
discharges of the family's forcing, tail-factor and tail-sum hypotheses, the radii inequality at
`r₀ = 1/200000` and `r₁ = 1/25`, and the endpoints, the concrete instances of
`duffing_existsUnique` and `duffing_existsUnique_real`.
-/

open scoped ENNReal NNReal

noncomputable section

namespace FourierDuffing.Certificate

open RadiiPolynomial RadiiPolynomial.WeightedLp RadiiPolynomial.WeightedLp.Bilateral
  RadiiPolynomial.Fourier.Quadratic RadiiPolynomial.Fourier.IkData RadiiPolynomial.Fourier.Duffing
  RadiiPolynomial.Certification.Fourier.Quadratic FourierDuffing.Numbers

/-! ### A. The instance data -/

section Objects

/-- The weight parameter `ν = 6/5`. -/
def ν₆₅ : PosReal := ⟨6 / 5, by norm_num⟩

/-- `ν = 6/5` satisfies `1 ≤ ν`. -/
instance fact_one_le_ν₆₅ : Fact (1 ≤ (ν₆₅ : ℝ)) := ⟨by show (1 : ℝ) ≤ 6 / 5; norm_num⟩

theorem coe_ν₆₅ : (ν₆₅ : ℝ) = 6 / 5 := rfl

/-- The control hypothesis `(10 + 1)² > 4`. -/
theorem control_hN : (4 : ℝ) < (((10 : ℕ) : ℝ) + 1) ^ 2 := by norm_num

/-- **The exact rational control** at `c₁ = 1/10`, `c₂ = 4`, `N = 10`:
`|μ₁₁|² = 117² + (11/10)² = 13689 + 121/100`. -/
theorem sq_norm_duffing_control : ‖duffing (1 / 10) 4 11‖ ^ 2 = 13689 + 121 / 100 := by
  rw [sq_norm_duffing]; norm_num

/-- The weight bridge `ν = nuQ`. -/
theorem hν : (ν₆₅ : ℝ) = (leaf.nuQ : ℝ) := by
  rw [coe_ν₆₅]
  norm_num [leaf, nuQ]

/-- **The candidate** `ā = J_F (ā_n)` on the head `|n| ≤ 10`. -/
def abar : X₂ ℂ ν₆₅ := leaf.abar ν₆₅

/-- The candidate's coefficients are the leaf's centre. -/
theorem coeff_abar (n : ℤ) : coeff abar n = toC (leaf.abarQ n) := leaf.coeff_abar n

/-- The symbol bridge: the Duffing symbol at `(1/10, 4)` is the mirror `muQ`. -/
theorem duffing_eq_toC (n : ℤ) : duffing (1 / 10) 4 n = toC (leaf.muQ n) := by
  apply Complex.ext
  · simp [duffing, muQ, c₂Q, sq]
    ring
  · simp [duffing, muQ, c₁Q, sq]

/-- The forcing bridge: the forcing at `c₃ = 1` is the mirror `forcQ`. -/
theorem coeff_forcing_eq (n : ℤ) : coeff (forcing (ν := ν₆₅) 1) n = toC (leaf.forcQ n) := by
  rw [coeff_forcing]
  simp only [forcQ]
  split_ifs
  · exact Complex.ext (by simp [c₃Q]) (by simp)
  · exact toC_zero.symm

end Objects

/-! ### B. The certificate, the producer discharges and the radii -/

section Bounds

/-- **The certificate** of book §10.1 at `c = (1/10, 4, 1)`, `N = 10`, `ν = 6/5` (the adapter's
certificate of the leaf). -/
def cert : Cert (headF 10) (duffing (1 / 10) 4) ν₆₅ :=
  leaf.cert checks chunk_checks hν duffing_eq_toC

/-- **The forcing hypothesis** `supp (c₃ b) ⊆ headF 10` (`forcing_supp`, `1 ≤ 10`). -/
theorem hg_data : ∀ k ∉ headF 10, coeff (forcing (ν := ν₆₅) 1) k = 0 := forcing_supp (by norm_num)

/-- **The bounds of the certificate** (the adapter's soundness theorem at the leaf): the `Y₀`
bound, the squared `Z₁` inequality at every tail factor `x` with `(x²)⁻¹ ≤ 100/1369021`, and the
squared `Z₂` inequality at `T2 = t2Q`. -/
theorem bounds :
    ‖G (headF 10) (duffing (1 / 10) 4) (summable_sq_tailSymbol_duffing_headF control_hN) cert.M
      (forcing 1) cert.abar‖ ≤ ((Y0c : ℚ) : ℝ) ∧
    (∀ x : ℝ, (x ^ 2)⁻¹ ≤ ((tailInvSqQ : ℚ) : ℝ) →
      cert.H ^ 2 + (‖betaOf (headF 10) cert.abar cert.abar_supp‖ / x) ^ 2 ≤ ((Z1c : ℚ) : ℝ) ^ 2) ∧
    4 * (cert.U ^ 2 + ((t2Q : ℚ) : ℝ)) ≤ ((Z2c : ℚ) : ℝ) ^ 2 ∧
    (0 : ℝ) ≤ ((Z1c : ℚ) : ℝ) ∧ (0 : ℝ) ≤ ((Z2c : ℚ) : ℝ) :=
  leaf.cert_spec checks chunk_checks hν duffing_eq_toC coeff_forcing_eq hg_data
    (duffing_ne_zero control_hN) _

/-- **The tail-sum hypothesis** `∑' ‖d‖² ≤ T2 = 484/287469` (the T2 producer at
`−132 ≤ 4 < 121`). -/
theorem T2_le : ∑' k, ‖tailSymbol ((headF 10 : Finset ℤ) : Set ℤ) (duffing (1 / 10) 4) k‖ ^ 2 ≤
    ((t2Q : ℚ) : ℝ) :=
  (tsum_sq_tailSymbol_duffing_le (c₁ := 1 / 10) control_hN (by norm_num)).trans
    (by rw [t2Q]; norm_num)

/-- **The `Z₁` hypothesis** in the endpoint's squared form (the tail factor `|μ₁₁|`,
`|μ₁₁|² = 1369021/100`). -/
theorem Z1_ok : cert.H ^ 2 + (‖betaOf (headF 10) cert.abar cert.abar_supp‖ /
    ‖duffing (1 / 10) 4 (((10 : ℕ) : ℤ) + 1)‖) ^ 2 ≤ ((Z1c : ℚ) : ℝ) ^ 2 :=
  bounds.2.1 _ (by
    rw [show (((10 : ℕ) : ℤ) + 1) = 11 by norm_num, sq_norm_duffing_control, tailInvSqQ]
    norm_num)

/-- **The radii inequality at `r₀ = 1/200000`**. -/
theorem radii_r0 :
    generalRadiiPolynomial ((Y0c : ℚ) : ℝ) cert.Z₀ ((Z1c : ℚ) : ℝ) (fun _ => ((Z2c : ℚ) : ℝ))
      (1 / 200000) < 0 := by
  have h := generalRadiiPolynomial_neg_of_Q_const Y0c Z0c Z1c Z2c r0 check_radii_r0
  rwa [show ((r0 : ℚ) : ℝ) = 1 / 200000 by rw [r0]; norm_num] at h

/-- **The radii inequality at `r₁ = 1/25`**. -/
theorem radii_r1 :
    generalRadiiPolynomial ((Y0c : ℚ) : ℝ) cert.Z₀ ((Z1c : ℚ) : ℝ) (fun _ => ((Z2c : ℚ) : ℝ))
      (1 / 25) < 0 := by
  have h := generalRadiiPolynomial_neg_of_Q_const Y0c Z0c Z1c Z2c r1 check_radii_r1
  rwa [show ((r1 : ℚ) : ℝ) = 1 / 25 by rw [r1]; norm_num] at h

end Bounds

/-! ### C. The endpoints -/

section Endpoints

/-- **THE ENDPOINT** (book §10.1 at its data, on `ℓ²_{6/5}` at our centre): the raw Fourier map
`F_n(a) = (−n² + i n/10 + 4) aₙ − (a ⋆ a)ₙ − bₙ` has a unique zero in the closed ball of radius
`1/200000` around `ā`. -/
theorem duffing_l2_existsUnique :
    ∃! a, a ∈ Metric.closedBall abar (1 / 200000) ∧
      ∀ n : ℤ, rawF (duffing (1 / 10) 4) (forcing 1) a n = 0 :=
  duffing_existsUnique control_hN cert hg_data bounds.1 Z1_ok bounds.2.2.2.1 T2_le bounds.2.2.1
    bounds.2.2.2.2 (by norm_num) radii_r0

/-- The same at the uniqueness radius `1/25`. -/
theorem duffing_l2_existsUnique_r1 :
    ∃! a, a ∈ Metric.closedBall abar (1 / 25) ∧
      ∀ n : ℤ, rawF (duffing (1 / 10) 4) (forcing 1) a n = 0 :=
  duffing_existsUnique control_hN cert hg_data bounds.1 Z1_ok bounds.2.2.2.1 T2_le bounds.2.2.1
    bounds.2.2.2.2 (by norm_num) radii_r1

/-- **The enclosure**: the zero in the small ball is the only zero in the ball of radius `1/25`. -/
theorem duffing_l2_enclosure :
    ∃ a ∈ Metric.closedBall abar (1 / 200000),
      (∀ n, rawF (duffing (1 / 10) 4) (forcing 1) a n = 0) ∧
        ∀ z ∈ Metric.closedBall abar (1 / 25),
          (∀ n, rawF (duffing (1 / 10) 4) (forcing 1) z n = 0) → z = a :=
  duffing_enclosure control_hN cert hg_data bounds.1 Z1_ok bounds.2.2.2.1 T2_le bounds.2.2.1
    bounds.2.2.2.2 (by norm_num) (by norm_num) radii_r0 radii_r1

/-- **The conjugate-symmetric endpoint**: the zero satisfies `conj ã₋ₙ = ãₙ`
(`duffing_existsUnique_real`). -/
theorem duffing_l2_real :
    ∃ a ∈ Metric.closedBall abar (1 / 200000),
      (∀ n, rawF (duffing (1 / 10) 4) (forcing 1) a n = 0) ∧ conjRefl a = a ∧
        ∀ z ∈ Metric.closedBall abar (1 / 200000),
          (∀ n, rawF (duffing (1 / 10) 4) (forcing 1) z n = 0) → z = a :=
  duffing_existsUnique_real control_hN cert hg_data bounds.1 Z1_ok bounds.2.2.2.1 T2_le bounds.2.2.1
    bounds.2.2.2.2 (by norm_num) radii_r0 (leaf.conjRefl_abar checks)

end Endpoints

end FourierDuffing.Certificate

end
