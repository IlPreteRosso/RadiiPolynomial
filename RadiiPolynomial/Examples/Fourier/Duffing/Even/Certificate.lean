import RadiiPolynomial.Applications.Fourier.Duffing
import RadiiPolynomial.Certification.RadiiPolynomialQ
import RadiiPolynomial.Examples.Fourier.Duffing.Even.Numbers

/-!
# The even Duffing instance on `ℓ²_{6/5}`: the numerical closure

PlasmaLean's periodic quadratic problem `u'' − u + u² = (4/5) cos x`
(`exterior/tmp/external_repos/PlasmaLean/PlasmaLean/Design/ValidatedBVP.lean`, Apache-2.0) read
in the Duffing convention `v = −u`: `v'' + 0 · v' + (−1) v − v² = (−4/5) cos t`, the Duffing family
of `Applications/Fourier/Duffing.lean` at `(c₁, c₂, c₃) = (0, −1, −4/5)`, `N = 10`, `ν = 6/5`. The
concrete certificate at our own rational centre (Newton started from PlasmaLean's candidate,
negated), and the endpoints: the raw Fourier map `F_n(a) = (−n² − 1) aₙ − (a ⋆ a)ₙ + (4/5) bₙ`,
`b_{±1} = 1/2`, has a unique zero in the closed ball of radius `1/500000` around the candidate `ā`
in `ℓ²_{6/5}`; the zero is unique in the ball of radius `1/10`, conjugate-symmetric
(`conj ã₋ₙ = ãₙ`) and even (`ã₋ₙ = ãₙ`).

The candidate, the head matrix and the constants are the consumer-owned rational leaf `leaf` of
`Examples/Fourier/Duffing/Even/Numbers.lean` (generated). The rational-leaf adapter
`Certification/Fourier/Quadratic.lean` turns it into the head certificate `cert` and its bounds.
The tail-sum hypothesis is the Duffing family's `T2` producer at `c₂ = −1` (inside its domain
`−(N+1)(N+2) ≤ c₂`), compared with the bound of record `4/2541`. Evenness is the even subfamily's
`duffing_existsUnique_even` (`Applications/Fourier/Duffing.lean`) at the even candidate (`check_even`).
-/

open scoped ENNReal NNReal

noncomputable section

namespace FourierDuffing.Even

open RadiiPolynomial RadiiPolynomial.WeightedLp RadiiPolynomial.WeightedLp.Bilateral
  RadiiPolynomial.Fourier.Quadratic RadiiPolynomial.Fourier.IkData RadiiPolynomial.Fourier.Duffing
  RadiiPolynomial.Certification.Fourier.Quadratic FourierDuffing.Even.Numbers

/-! ### A. The instance data -/

section Objects

/-- The weight parameter `ν = 6/5`. -/
def ν₆₅ : PosReal := ⟨6 / 5, by norm_num⟩

/-- `ν = 6/5` satisfies `1 ≤ ν`. -/
instance fact_one_le_ν₆₅ : Fact (1 ≤ (ν₆₅ : ℝ)) := ⟨by show (1 : ℝ) ≤ 6 / 5; norm_num⟩

theorem coe_ν₆₅ : (ν₆₅ : ℝ) = 6 / 5 := rfl

/-- The control hypothesis `(10 + 1)² > c₂ = −1`. -/
theorem control_hN : (-1 : ℝ) < (((10 : ℕ) : ℝ) + 1) ^ 2 := by norm_num

/-- **The exact rational control** at `c₁ = 0`, `c₂ = −1`, `N = 10`: `|μ₁₁|² = 122²`. -/
theorem sq_norm_duffing_control : ‖duffing 0 (-1) 11‖ ^ 2 = 14884 := by
  rw [sq_norm_duffing]; norm_num

/-- The weight bridge `ν = nuQ`. -/
theorem hν : (ν₆₅ : ℝ) = (leaf.nuQ : ℝ) := by
  rw [coe_ν₆₅]
  norm_num [leaf, nuQ]

/-- **The candidate** `ā = J_F (ā_n)` on the head `|n| ≤ 10`. -/
def abar : X₂ ℂ ν₆₅ := leaf.abar ν₆₅

/-- The symbol bridge: the Duffing symbol at `(0, −1)` is the mirror `muQ`. -/
theorem duffing_eq_toC (n : ℤ) : duffing 0 (-1) n = toC (leaf.muQ n) := by
  apply Complex.ext
  · simp [duffing, muQ, c₂Q, sq]
    ring
  · simp [duffing, muQ, c₁Q, sq]

/-- The forcing bridge: the forcing at `c₃ = −4/5` is the mirror `forcQ`. -/
theorem coeff_forcing_eq (n : ℤ) : coeff (forcing (ν := ν₆₅) (-4 / 5)) n = toC (leaf.forcQ n) := by
  rw [coeff_forcing]
  simp only [forcQ]
  split_ifs
  · exact Complex.ext (by simp [c₃Q]) (by simp)
  · exact toC_zero.symm

/-- **Evenness of the candidate** `refl ā = ā` (`check_even`). -/
theorem refl_abar : refl abar = abar :=
  ext_coeff <| funext fun n => by
    rw [coeff_refl, abar, leaf.coeff_abar, leaf.coeff_abar]
    by_cases h : n ∈ idx 10
    · rw [check_even n h]
    · have hn : -n ∉ headF 10 := fun h' => h (mem_idx.2 (by have := Finset.mem_Icc.1 h'; omega))
      rw [leaf.abarQ_eq_zero hn, leaf.abarQ_eq_zero fun h' => h (mem_idx.2 (Finset.mem_Icc.1 h'))]

end Objects

/-! ### B. The certificate, the producer discharges and the radii -/

section Bounds

/-- **The certificate** at `c = (0, −1, −4/5)`, `N = 10`, `ν = 6/5` (the adapter's certificate of
the leaf). -/
def cert : Cert (headF 10) (duffing 0 (-1)) ν₆₅ :=
  leaf.cert checks chunk_checks hν duffing_eq_toC

/-- **The forcing hypothesis** `supp (c₃ b) ⊆ headF 10` (`forcing_supp`, `1 ≤ 10`). -/
theorem hg_data : ∀ k ∉ headF 10, coeff (forcing (ν := ν₆₅) (-4 / 5)) k = 0 :=
  forcing_supp (by norm_num)

/-- **The bounds of the certificate** (the adapter's soundness theorem at the leaf). -/
theorem bounds :
    ‖G (headF 10) (duffing 0 (-1)) (summable_sq_tailSymbol_duffing_headF control_hN) cert.M
      (forcing (-4 / 5)) cert.abar‖ ≤ ((Y0c : ℚ) : ℝ) ∧
    (∀ x : ℝ, (x ^ 2)⁻¹ ≤ ((tailInvSqQ : ℚ) : ℝ) →
      cert.H ^ 2 + (‖betaOf (headF 10) cert.abar cert.abar_supp‖ / x) ^ 2 ≤ ((Z1c : ℚ) : ℝ) ^ 2) ∧
    4 * (cert.U ^ 2 + ((t2Q : ℚ) : ℝ)) ≤ ((Z2c : ℚ) : ℝ) ^ 2 ∧
    (0 : ℝ) ≤ ((Z1c : ℚ) : ℝ) ∧ (0 : ℝ) ≤ ((Z2c : ℚ) : ℝ) :=
  leaf.cert_spec checks chunk_checks hν duffing_eq_toC coeff_forcing_eq hg_data
    (duffing_ne_zero control_hN) _

/-- **The tail-sum hypothesis** `∑' ‖d‖² ≤ T2 = 4/2541`: the family's `T2` producer at `c₂ = −1`
(`−132 ≤ −1 < 121`) gives `121/78141 ≤ 4/2541`. -/
theorem T2_le : ∑' k, ‖tailSymbol ((headF 10 : Finset ℤ) : Set ℤ) (duffing 0 (-1)) k‖ ^ 2 ≤
    ((t2Q : ℚ) : ℝ) :=
  (tsum_sq_tailSymbol_duffing_le (c₁ := 0) control_hN (by norm_num)).trans
    (by rw [t2Q]; norm_num)

/-- **The `Z₁` hypothesis** in the endpoint's squared form (the tail factor `|μ₁₁| = 122`). -/
theorem Z1_ok : cert.H ^ 2 + (‖betaOf (headF 10) cert.abar cert.abar_supp‖ /
    ‖duffing 0 (-1) (((10 : ℕ) : ℤ) + 1)‖) ^ 2 ≤ ((Z1c : ℚ) : ℝ) ^ 2 :=
  bounds.2.1 _ (by
    rw [show (((10 : ℕ) : ℤ) + 1) = 11 by norm_num, sq_norm_duffing_control, tailInvSqQ]
    norm_num)

/-- **The radii inequality at `r₀ = 1/500000`**. -/
theorem radii_r0 :
    generalRadiiPolynomial ((Y0c : ℚ) : ℝ) cert.Z₀ ((Z1c : ℚ) : ℝ) (fun _ => ((Z2c : ℚ) : ℝ))
      (1 / 500000) < 0 := by
  have h := generalRadiiPolynomial_neg_of_Q_const Y0c Z0c Z1c Z2c r0 check_radii_r0
  rwa [show ((r0 : ℚ) : ℝ) = 1 / 500000 by rw [r0]; norm_num] at h

/-- **The radii inequality at `r₁ = 1/10`**. -/
theorem radii_r1 :
    generalRadiiPolynomial ((Y0c : ℚ) : ℝ) cert.Z₀ ((Z1c : ℚ) : ℝ) (fun _ => ((Z2c : ℚ) : ℝ))
      (1 / 10) < 0 := by
  have h := generalRadiiPolynomial_neg_of_Q_const Y0c Z0c Z1c Z2c r1 check_radii_r1
  rwa [show ((r1 : ℚ) : ℝ) = 1 / 10 by rw [r1]; norm_num] at h

end Bounds

/-! ### C. The endpoints -/

section Endpoints

/-- **THE ENDPOINT** (on `ℓ²_{6/5}` at our centre): the raw Fourier map
`F_n(a) = (−n² − 1) aₙ − (a ⋆ a)ₙ + (4/5) bₙ` has a unique zero in the closed ball of radius
`1/500000` around `ā`. -/
theorem even_l2_existsUnique :
    ∃! a, a ∈ Metric.closedBall abar (1 / 500000) ∧
      ∀ n : ℤ, rawF (duffing 0 (-1)) (forcing (-4 / 5)) a n = 0 :=
  duffing_existsUnique control_hN cert hg_data bounds.1 Z1_ok bounds.2.2.2.1 T2_le bounds.2.2.1
    bounds.2.2.2.2 (by norm_num) radii_r0

/-- The same at the uniqueness radius `1/10`. -/
theorem even_l2_existsUnique_r1 :
    ∃! a, a ∈ Metric.closedBall abar (1 / 10) ∧
      ∀ n : ℤ, rawF (duffing 0 (-1)) (forcing (-4 / 5)) a n = 0 :=
  duffing_existsUnique control_hN cert hg_data bounds.1 Z1_ok bounds.2.2.2.1 T2_le bounds.2.2.1
    bounds.2.2.2.2 (by norm_num) radii_r1

/-- **The enclosure**: the zero in the small ball is the only zero in the ball of radius `1/10`. -/
theorem even_l2_enclosure :
    ∃ a ∈ Metric.closedBall abar (1 / 500000),
      (∀ n, rawF (duffing 0 (-1)) (forcing (-4 / 5)) a n = 0) ∧
        ∀ z ∈ Metric.closedBall abar (1 / 10),
          (∀ n, rawF (duffing 0 (-1)) (forcing (-4 / 5)) z n = 0) → z = a :=
  duffing_enclosure control_hN cert hg_data bounds.1 Z1_ok bounds.2.2.2.1 T2_le bounds.2.2.1
    bounds.2.2.2.2 (by norm_num) (by norm_num) radii_r0 radii_r1

/-- **The conjugate-symmetric endpoint**: the zero satisfies `conj ã₋ₙ = ãₙ`
(`duffing_existsUnique_real`). -/
theorem even_l2_real :
    ∃ a ∈ Metric.closedBall abar (1 / 500000),
      (∀ n, rawF (duffing 0 (-1)) (forcing (-4 / 5)) a n = 0) ∧ conjRefl a = a ∧
        ∀ z ∈ Metric.closedBall abar (1 / 500000),
          (∀ n, rawF (duffing 0 (-1)) (forcing (-4 / 5)) z n = 0) → z = a :=
  duffing_existsUnique_real control_hN cert hg_data bounds.1 Z1_ok bounds.2.2.2.1 T2_le bounds.2.2.1
    bounds.2.2.2.2 (by norm_num) radii_r0 (leaf.conjRefl_abar checks)

/-- **The even endpoint**: the zero is conjugate-symmetric and even, `conj ã₋ₙ = ãₙ = ã₋ₙ`
(`duffing_existsUnique_even` at the even candidate). -/
theorem even_l2_even :
    ∃ a ∈ Metric.closedBall abar (1 / 500000),
      (∀ n, rawF (duffing 0 (-1)) (forcing (-4 / 5)) a n = 0) ∧ conjRefl a = a ∧ refl a = a ∧
        ∀ z ∈ Metric.closedBall abar (1 / 500000),
          (∀ n, rawF (duffing 0 (-1)) (forcing (-4 / 5)) z n = 0) → z = a :=
  duffing_existsUnique_even control_hN cert hg_data bounds.1 Z1_ok bounds.2.2.2.1 T2_le bounds.2.2.1
    bounds.2.2.2.2 (by norm_num) radii_r0 (leaf.conjRefl_abar checks)
    refl_abar

end Endpoints

end FourierDuffing.Even

end
