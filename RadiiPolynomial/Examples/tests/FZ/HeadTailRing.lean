import RadiiPolynomial.Algebra.Ring.HeadTailIdentities
import RadiiPolynomial.Operators.HeadTail
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basis

/-!
# L001 tests (T44): finite ring countermodels for the head/tail identities

TARGET_SHEET §7 ring countermodels for T34–T36 (in `ℚ`, and in `Matrix (Fin 2) (Fin 2) ℚ`
where a commutative witness cannot exist), the S027 checker tests `drop_hP` (:522),
`drop_hRP` (:525) and `drop_hsigma` (:528) for T37/T38a/T38b on `ℝ →L[ℝ] ℝ`, and the
positive sides of the mathematical-negative controls CTL-R1 and CTL-O1.

Each countermodel states the retained hypotheses, the failure of the dropped hypothesis and
the failure of the identity. The `hP` countermodel of T36 is infinite-dimensional and is a
critic check (TARGET_SHEET §7), not part of this module. Kernel-only; imported by nothing.
-/

noncomputable section

namespace RadiiPolynomial.Tests.FZ.HeadTail

open RadiiPolynomial HeadTail

/-! ### T34 `composition_identity_ring` -/

/-- Dropping `hP` (`ℚ`: `P = 2`, `M = L = 1`, `R = 0`): `-6` against `-2`. -/
theorem ring_T34_drop_hP :
    ¬ IsIdempotentElem (2 : ℚ) ∧ (0 : ℚ) * 2 = 0 ∧
      ((1 : ℚ) * 2 + 0) * (2 * 1 * (1 - 2) + (1 - 2) * 1) = -6 ∧
      (1 : ℚ) * 2 * 1 * (1 - 2) + 0 * 1 = -2 := by
  refine ⟨fun h => by norm_num [IsIdempotentElem] at h, by norm_num, by norm_num, by norm_num⟩

/-- Dropping `hRP` (`ℚ`: `P = M = L = R = 1`): `0` against `1`. -/
theorem ring_T34_drop_hRP :
    IsIdempotentElem (1 : ℚ) ∧ (1 : ℚ) * 1 ≠ 0 ∧
      ((1 : ℚ) * 1 + 1) * (1 * 1 * (1 - 1) + (1 - 1) * 1) = 0 ∧
      (1 : ℚ) * 1 * 1 * (1 - 1) + 1 * 1 = 1 :=
  ⟨IsIdempotentElem.one, by norm_num, by norm_num, by norm_num⟩

/-! ### T35 `defect_identity_ring` -/

/-- Dropping `hP` (`ℚ`: `P = 2`, `M = 1`, `G = Λ = 0`, `L = 1`): `6` against `2`. -/
theorem ring_T35_drop_hP :
    ¬ IsIdempotentElem (2 : ℚ) ∧ Commute (0 : ℚ) 2 ∧ (0 : ℚ) * 2 = 0 ∧
      ((1 : ℚ) * 2 + 0) * ((2 * (0 + 1) * 2 + (1 - 2) * 0 * (1 - 2)) - (0 + 1)) = 6 ∧
      -((1 : ℚ) * 2 * 1 * (1 - 2) + 0 * (1 - 2) * 1) = 2 :=
  ⟨fun h => by norm_num [IsIdempotentElem] at h, Commute.zero_left 2, by norm_num, by norm_num,
    by norm_num⟩

/-- The 2×2 matrix units over `ℚ`. -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℚ

/-- `E₁₁`. -/
def e11 : Mat2 := Matrix.single 0 0 1

/-- `E₁₂`. -/
def e12 : Mat2 := Matrix.single 0 1 1

/-- `E₂₂`. -/
def e22 : Mat2 := Matrix.single 1 1 1

theorem e11_mul_e11 : e11 * e11 = e11 := by
  rw [e11, Matrix.single_mul_single_same, mul_one]

theorem e11_mul_e12 : e11 * e12 = e12 := by
  rw [e11, e12, Matrix.single_mul_single_same, mul_one]

theorem e12_mul_e11 : e12 * e11 = 0 := by
  simp [e12, e11]

theorem e22_mul_e11 : e22 * e11 = 0 := by
  simp [e22, e11]

theorem e22_mul_e12 : e22 * e12 = 0 := by
  simp [e22, e12]

theorem e11_mul_e22 : e11 * e22 = 0 := by
  simp [e11, e22]

theorem e12_mul_e22 : e12 * e22 = e12 := by
  rw [e12, e22, Matrix.single_mul_single_same, mul_one]

theorem one_sub_e11 : (1 : Mat2) - e11 = e22 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e11, e22]

theorem e12_ne_zero : e12 ≠ 0 := fun h => by
  simpa [e12] using congrFun (congrFun h 0) 1

theorem e11_ne_zero : e11 ≠ 0 := fun h => by
  simpa [e11] using congrFun (congrFun h 0) 0

/-- Dropping `hΛ` (`P = E₁₁`, `Λ = E₁₂`, `G = 0`, `M = 1`, `L = 0`): `-E₁₂` against `0`. -/
theorem ring_T35_drop_hLambda :
    IsIdempotentElem e11 ∧ ¬ Commute e12 e11 ∧ (0 : Mat2) * e11 = 0 ∧
      (1 * e11 + 0) * ((e11 * (e12 + 0) * e11 + (1 - e11) * e12 * (1 - e11)) - (e12 + 0)) = -e12 ∧
      -(1 * e11 * 0 * (1 - e11) + 0 * (1 - e11) * 0) = (0 : Mat2) := by
  refine ⟨e11_mul_e11, fun h => ?_, zero_mul _, ?_, by simp⟩
  · have h' : e12 * e11 = e11 * e12 := h.eq
    rw [e12_mul_e11, e11_mul_e12] at h'
    exact e12_ne_zero h'.symm
  · rw [one_sub_e11, add_zero, add_zero, one_mul, mul_assoc e11 e12 e11, e12_mul_e11, mul_zero,
      e22_mul_e12, zero_mul, add_zero, zero_sub, mul_neg, e11_mul_e12]

/-- Dropping `hG` (`P = E₁₁`, `L = E₁₂`, `G = E₁₁`, `Λ = 0`, `M = 0`): `-E₁₂` against `0`. -/
theorem ring_T35_drop_hG :
    IsIdempotentElem e11 ∧ Commute (0 : Mat2) e11 ∧ e11 * e11 ≠ 0 ∧
      (0 * e11 + e11) * ((e11 * (0 + e12) * e11 + (1 - e11) * 0 * (1 - e11)) - (0 + e12)) = -e12 ∧
      -(0 * e11 * e12 * (1 - e11) + e11 * (1 - e11) * e12) = (0 : Mat2) := by
  refine ⟨e11_mul_e11, Commute.zero_left _, by rw [e11_mul_e11]; exact e11_ne_zero, ?_, ?_⟩
  · rw [zero_mul, zero_add, zero_add, mul_assoc e11 e12 e11, e12_mul_e11, mul_zero, mul_zero,
      zero_mul, add_zero, zero_sub, mul_neg, e11_mul_e12]
  · rw [one_sub_e11, zero_mul, zero_mul, zero_mul, zero_add, e11_mul_e22, zero_mul, neg_zero]

/-! ### T36 `inverse_defect_ring` -/

/-- Dropping `hGΛ` (`ℚ`: `P = G = M = 0`, `Λ = L = 0`): `1` against `0`. -/
theorem ring_T36_drop_hGLambda :
    IsIdempotentElem (0 : ℚ) ∧ (0 : ℚ) * 0 = 0 ∧ (0 : ℚ) * 0 * (1 - 0) ≠ 1 - 0 ∧
      1 - ((0 : ℚ) * 0 + 0) * (0 * (0 + 0) * 0 + (1 - 0) * 0 * (1 - 0)) = 1 ∧
      (0 : ℚ) - 0 * 0 * (0 + 0) * 0 = 0 :=
  ⟨IsIdempotentElem.zero, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Dropping `hG` (`ℚ`: `P = G = L = 1`, `M = Λ = 0`): `0` against `1`. -/
theorem ring_T36_drop_hG :
    IsIdempotentElem (1 : ℚ) ∧ (1 : ℚ) * 1 ≠ 0 ∧ (1 : ℚ) * 0 * (1 - 1) = 1 - 1 ∧
      1 - ((0 : ℚ) * 1 + 1) * (1 * (0 + 1) * 1 + (1 - 1) * 0 * (1 - 1)) = 0 ∧
      (1 : ℚ) - 0 * 1 * (0 + 1) * 1 = 1 :=
  ⟨IsIdempotentElem.one, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- CTL-R1 positive side: T36 with right side `P + M P (Λ + L) P` is false
(`ℚ`: `P = 1`, `G = 0`, `M = 1`, `Λ = 0`, `L = 1`; the hypotheses hold): `0` against `2`. -/
theorem ctl_R1_witness :
    IsIdempotentElem (1 : ℚ) ∧ (0 : ℚ) * 1 = 0 ∧ (0 : ℚ) * 0 * (1 - 1) = 1 - 1 ∧
      1 - ((1 : ℚ) * 1 + 0) * (1 * (0 + 1) * 1 + (1 - 1) * 0 * (1 - 1)) ≠
        1 + 1 * 1 * (0 + 1) * 1 :=
  ⟨IsIdempotentElem.one, by norm_num, by norm_num, by norm_num⟩


/-! ### The dropped hypotheses as universally quantified failures -/

/-- T34 without `hP` fails. -/
theorem ring_T34_hP_needed : ¬ ∀ P M R L : ℚ, R * P = 0 →
    (M * P + R) * (P * L * (1 - P) + (1 - P) * L) = M * P * L * (1 - P) + R * L :=
  fun h => by have := h 2 1 0 1 (by norm_num); norm_num at this

/-- T34 without `hRP` fails. -/
theorem ring_T34_hRP_needed : ¬ ∀ P M R L : ℚ, IsIdempotentElem P →
    (M * P + R) * (P * L * (1 - P) + (1 - P) * L) = M * P * L * (1 - P) + R * L :=
  fun h => by have := h 1 1 1 1 IsIdempotentElem.one; norm_num at this

/-- T35 without `hP` fails. -/
theorem ring_T35_hP_needed : ¬ ∀ P M G Λ L : ℚ, Commute Λ P → G * P = 0 →
    (M * P + G) * ((P * (Λ + L) * P + (1 - P) * Λ * (1 - P)) - (Λ + L)) =
      -(M * P * L * (1 - P) + G * (1 - P) * L) :=
  fun h => by have := h 2 1 0 0 1 (Commute.zero_left _) (by norm_num); norm_num at this

/-- T35 without `hΛ` fails (no commutative witness exists: in a commutative ring T35 holds
under `hP` alone). -/
theorem ring_T35_hLambda_needed : ¬ ∀ P M G Λ L : Mat2, IsIdempotentElem P → G * P = 0 →
    (M * P + G) * ((P * (Λ + L) * P + (1 - P) * Λ * (1 - P)) - (Λ + L)) =
      -(M * P * L * (1 - P) + G * (1 - P) * L) := fun h => by
  have e := h e11 1 0 e12 0 e11_mul_e11 (zero_mul _)
  rw [ring_T35_drop_hLambda.2.2.2.1, ring_T35_drop_hLambda.2.2.2.2, neg_eq_zero] at e
  exact e12_ne_zero e

/-- T35 without `hG` fails. -/
theorem ring_T35_hG_needed : ¬ ∀ P M G Λ L : Mat2, IsIdempotentElem P → Commute Λ P →
    (M * P + G) * ((P * (Λ + L) * P + (1 - P) * Λ * (1 - P)) - (Λ + L)) =
      -(M * P * L * (1 - P) + G * (1 - P) * L) := fun h => by
  have e := h e11 0 e11 0 e12 e11_mul_e11 (Commute.zero_left _)
  rw [ring_T35_drop_hG.2.2.2.1, ring_T35_drop_hG.2.2.2.2, neg_eq_zero] at e
  exact e12_ne_zero e

/-- T36 without `hGΛ` fails. -/
theorem ring_T36_hGLambda_needed : ¬ ∀ P M G Λ L : ℚ, IsIdempotentElem P → G * P = 0 →
    1 - (M * P + G) * (P * (Λ + L) * P + (1 - P) * Λ * (1 - P)) = P - M * P * (Λ + L) * P :=
  fun h => by have := h 0 0 0 0 0 IsIdempotentElem.zero (by norm_num); norm_num at this

/-- T36 without `hG` fails. -/
theorem ring_T36_hG_needed : ¬ ∀ P M G Λ L : ℚ, IsIdempotentElem P →
    G * Λ * (1 - P) = 1 - P →
    1 - (M * P + G) * (P * (Λ + L) * P + (1 - P) * Λ * (1 - P)) = P - M * P * (Λ + L) * P :=
  fun h => by have := h 1 0 1 0 1 IsIdempotentElem.one (by norm_num); norm_num at this

/-! ### T37/T38a/T38b on `ℝ →L[ℝ] ℝ` (S027T :517–:531) -/

/-- The identity of `ℝ` as a bounded operator. -/
abbrev IdR : ℝ →L[ℝ] ℝ := 1

/-- The composite `(M P + R)(P L (1 - P) + (1 - P) L)`. -/
def composite (P M R L : ℝ →L[ℝ] ℝ) : ℝ →L[ℝ] ℝ :=
  (M ∘L P + R) ∘L (P ∘L L ∘L (1 - P) + (1 - P) ∘L L)

/-- The reduced side `M P L (1 - P) + R L`. -/
def reduced (P M R L : ℝ →L[ℝ] ℝ) : ℝ →L[ℝ] ℝ := M ∘L P ∘L L ∘L (1 - P) + R ∘L L

/-- Dropping `hP` (S027T `drop_hP`): `P = 2`, `M = L = 1`, `R = 0`; at `1`: `-6` against `-2`. -/
theorem drop_hP : composite (2 • IdR) IdR 0 IdR 1 = -6 ∧ reduced (2 • IdR) IdR 0 IdR 1 = -2 := by
  norm_num [composite, reduced, IdR, ContinuousLinearMap.comp_apply, add_apply, sub_apply,
    smul_apply, one_apply_eq_self]

/-- `hRP` is retained by the `drop_hP` data. -/
theorem drop_hP_retained : (0 : ℝ →L[ℝ] ℝ) ∘L (2 • IdR) = 0 := ContinuousLinearMap.zero_comp _

/-- Dropping `hRP` (S027T `drop_hRP`): `P = M = R = L = 1`; at `1`: `0` against `1`. -/
theorem drop_hRP : composite IdR IdR IdR IdR 1 = 0 ∧ reduced IdR IdR IdR IdR 1 = 1 := by
  norm_num [composite, reduced, IdR, ContinuousLinearMap.comp_apply, add_apply, sub_apply,
    one_apply_eq_self]

/-- `hP` is retained by the `drop_hRP` data. -/
theorem drop_hRP_retained : IsIdempotentElem IdR := IsIdempotentElem.one

/-- Dropping `hσ` (S027T `drop_hsigma`): `σ = 2`, `P = M = 0`, `R = L = 1`: `2` against `1`. -/
theorem drop_hsigma : ‖(2 : ℝ) • composite 0 0 IdR IdR‖ = 2 ∧ ‖reduced 0 0 IdR IdR‖ = 1 := by
  have hc : composite 0 0 IdR IdR = IdR := by
    ext; simp [composite, IdR]
  have hr : reduced 0 0 IdR IdR = IdR := by
    ext; simp [reduced, IdR]
  rw [hc, hr, norm_smul]
  norm_num [IdR, norm_one]

/-- `hP` and `hRP` are retained by the `drop_hsigma` data. -/
theorem drop_hsigma_retained :
    IsIdempotentElem (0 : ℝ →L[ℝ] ℝ) ∧ IdR ∘L (0 : ℝ →L[ℝ] ℝ) = 0 :=
  ⟨IsIdempotentElem.zero, ContinuousLinearMap.comp_zero _⟩

/-- CTL-O1 positive side: T38a with `2 •` for `σ •` is false (`E = ℝ`, `P = M = 0`,
`R = L = 1`, hypotheses hold with `σ = 1`): `2` against `1`. -/
theorem ctl_O1_witness :
    IsIdempotentElem (0 : ℝ →L[ℝ] ℝ) ∧ IdR ∘L (0 : ℝ →L[ℝ] ℝ) = 0 ∧ ‖(1 : ℝ)‖ = 1 ∧
      ‖(2 : ℝ) • composite 0 0 IdR IdR‖ ≠ ‖reduced 0 0 IdR IdR‖ := by
  refine ⟨IsIdempotentElem.zero, ContinuousLinearMap.comp_zero _, norm_one, ?_⟩
  rw [drop_hsigma.1, drop_hsigma.2]; norm_num

/-- T37 without `hP` fails. -/
theorem T37_hP_needed : ¬ ∀ P M R L : ℝ →L[ℝ] ℝ, R ∘L P = 0 →
    composite P M R L = reduced P M R L := fun h => by
  have e := congrArg (fun f : ℝ →L[ℝ] ℝ => f 1) (h (2 • IdR) IdR 0 IdR drop_hP_retained)
  simp only [drop_hP.1, drop_hP.2] at e; norm_num at e

/-- T37 without `hRP` fails. -/
theorem T37_hRP_needed : ¬ ∀ P M R L : ℝ →L[ℝ] ℝ, IsIdempotentElem P →
    composite P M R L = reduced P M R L := fun h => by
  have e := congrArg (fun f : ℝ →L[ℝ] ℝ => f 1) (h IdR IdR IdR IdR drop_hRP_retained)
  simp only [drop_hRP.1, drop_hRP.2] at e; norm_num at e

/-- T38a without `hσ` fails. -/
theorem T38a_hsigma_needed : ¬ ∀ (P M R L : ℝ →L[ℝ] ℝ) (σ : ℝ), IsIdempotentElem P →
    R ∘L P = 0 → ‖σ • composite P M R L‖ = ‖reduced P M R L‖ := fun h => by
  have e := h 0 0 IdR IdR 2 drop_hsigma_retained.1 drop_hsigma_retained.2
  rw [drop_hsigma.1, drop_hsigma.2] at e; norm_num at e

/-- T38b without `hσ` fails (with `Z` the signed composite). -/
theorem T38b_hsigma_needed : ¬ ∀ (P M R L Z : ℝ →L[ℝ] ℝ) (σ : ℝ), P ∘L P = P →
    R ∘L P = 0 → Z = σ • composite P M R L → ‖Z‖ = ‖reduced P M R L‖ := fun h => by
  have e := h 0 0 IdR IdR _ 2 (ContinuousLinearMap.zero_comp _) drop_hsigma_retained.2 rfl
  rw [drop_hsigma.1, drop_hsigma.2] at e; norm_num at e

end RadiiPolynomial.Tests.FZ.HeadTail
