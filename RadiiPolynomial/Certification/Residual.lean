import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.NhdsWithin

/-!
# Residual certificates in normed rings

A candidate and a residual bound below one determine an exact one-sided inverse or
finite right Bézout identity, with solution and displacement bounds. This is the
same Neumann correction used for an approximate inverse in a normed operator algebra.

The estimates require neither commutativity nor `NormOneClass`: each term is
bounded after multiplication by the candidate, including power zero. The only
convergence assumption is `HasSummableGeomSeries`, which holds in every complete
normed ring. Dense candidate families also give the converse certificate criterion.
No spectral or coefficient-algebra hypotheses enter these results.
-/

noncomputable section

namespace RadiiPolynomial.Residual

variable {A ι : Type*} [NormedRing A] [HasSummableGeomSeries A] [Fintype ι]

/-- The error in a proposed right Bézout identity. -/
def residual (f b₀ : ι → A) : A := 1 - ∑ i, f i * b₀ i

/-- Correct every candidate coefficient on the right by the same geometric series. -/
def correction (f b₀ : ι → A) (i : ι) : A :=
  b₀ i * ∑' n : ℕ, (residual f b₀) ^ n

omit [HasSummableGeomSeries A] in
private theorem norm_mul_pow_le (b e : A) {ε : ℝ} (he : ‖e‖ ≤ ε) (n : ℕ) :
    ‖b * e ^ n‖ ≤ ‖b‖ * ε ^ n := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans he
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc]
    refine (norm_mul_le _ _).trans ?_
    simpa only [pow_succ, mul_assoc] using
      mul_le_mul ih he (norm_nonneg _) (mul_nonneg (norm_nonneg _) (pow_nonneg hε n))

/-- Multiplication by a convergent geometric series, without a unit-norm axiom. -/
theorem norm_mul_geomSeries_le (b e : A) {ε : ℝ} (he : ‖e‖ ≤ ε) (hε : ε < 1) :
    ‖b * ∑' n : ℕ, e ^ n‖ ≤ ‖b‖ / (1 - ε) := by
  rw [← (summable_geometric_of_norm_lt_one (he.trans_lt hε)).tsum_mul_left b]
  simpa only [div_eq_mul_inv] using
    tsum_of_norm_bounded
      ((hasSum_geometric_of_lt_one ((norm_nonneg _).trans he) hε).mul_left ‖b‖)
      (norm_mul_pow_le b e he)

/-- The displacement bound also avoids a unit-norm axiom. -/
theorem norm_mul_geomSeries_sub_le (b e : A) {ε : ℝ} (he : ‖e‖ ≤ ε) (hε : ε < 1) :
    ‖b * (∑' n : ℕ, e ^ n) - b‖ ≤ ε * ‖b‖ / (1 - ε) := by
  have hs := (summable_geometric_of_norm_lt_one (he.trans_lt hε)).mul_left b
  have ht : b * (∑' n : ℕ, e ^ n) - b = ∑' n : ℕ, b * e ^ (n + 1) := by
    rw [← (summable_geometric_of_norm_lt_one (he.trans_lt hε)).tsum_mul_left b,
      hs.tsum_eq_zero_add]
    simp
  rw [ht]
  rw [div_eq_mul_inv]
  refine tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one ((norm_nonneg _).trans he) hε).mul_left (ε * ‖b‖)) ?_
  intro n
  simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using norm_mul_pow_le b e he (n + 1)

/-- Right Neumann correction of an approximate right inverse. -/
def rightInverseCorrection (a b₀ : A) : A :=
  b₀ * ∑' n : ℕ, (1 - a * b₀) ^ n

/-- A small right residual produces a right inverse; commutativity is not needed. -/
theorem mul_rightInverseCorrection (a b₀ : A) (h : ‖1 - a * b₀‖ < 1) :
    a * rightInverseCorrection a b₀ = 1 := by
  unfold rightInverseCorrection
  rw [← mul_assoc]
  convert mul_neg_geom_series (1 - a * b₀) h using 2
  simp

/-- The corrected right inverse has the candidate norm divided by the residual gap. -/
theorem norm_rightInverseCorrection_le (a b₀ : A) {ε : ℝ}
    (h : ‖1 - a * b₀‖ ≤ ε) (hε : ε < 1) :
    ‖rightInverseCorrection a b₀‖ ≤ ‖b₀‖ / (1 - ε) :=
  norm_mul_geomSeries_le b₀ (1 - a * b₀) h hε

/-- Distance from the approximate right inverse to its correction. -/
theorem norm_rightInverseCorrection_sub_le (a b₀ : A) {ε : ℝ}
    (h : ‖1 - a * b₀‖ ≤ ε) (hε : ε < 1) :
    ‖rightInverseCorrection a b₀ - b₀‖ ≤ ε * ‖b₀‖ / (1 - ε) :=
  norm_mul_geomSeries_sub_le b₀ (1 - a * b₀) h hε

/-- A residual certificate supplies an exact right inverse and both quantitative bounds. -/
theorem exists_right_inverse_of_residual_le (a b₀ : A) {ε : ℝ}
    (h : ‖1 - a * b₀‖ ≤ ε) (hε : ε < 1) :
    ∃ b : A, a * b = 1 ∧ ‖b‖ ≤ ‖b₀‖ / (1 - ε) ∧
      ‖b - b₀‖ ≤ ε * ‖b₀‖ / (1 - ε) :=
  ⟨rightInverseCorrection a b₀, mul_rightInverseCorrection a b₀ (h.trans_lt hε),
    norm_rightInverseCorrection_le a b₀ h hε,
    norm_rightInverseCorrection_sub_le a b₀ h hε⟩

/-- Left Neumann correction, matching the residual `1 - b₀ * a` of an approximate
left inverse, including the `Z₀` convention for approximate inverse operators. -/
def leftInverseCorrection (a b₀ : A) : A :=
  (∑' n : ℕ, (1 - b₀ * a) ^ n) * b₀

omit [HasSummableGeomSeries A] in
private theorem op_leftInverseCorrection (a b₀ : A) :
    MulOpposite.op (leftInverseCorrection a b₀) =
      rightInverseCorrection (MulOpposite.op a) (MulOpposite.op b₀) := by
  simp only [leftInverseCorrection, rightInverseCorrection, MulOpposite.op_mul,
    ← tsum_op, MulOpposite.op_pow, MulOpposite.op_sub, MulOpposite.op_one]

private theorem hasSummableGeomSeries_opposite : HasSummableGeomSeries Aᵐᵒᵖ where
  summable_geometric_of_norm_lt_one x hx := by
    refine (summable_op.mpr
      (summable_geometric_of_norm_lt_one (show ‖x.unop‖ < 1 from hx))).congr ?_
    intro n
    simp only [MulOpposite.op_pow, MulOpposite.op_unop]

/-- A small left residual produces a left inverse, with the multiplication order preserved. -/
theorem leftInverseCorrection_mul (a b₀ : A) (h : ‖1 - b₀ * a‖ < 1) :
    leftInverseCorrection a b₀ * a = 1 := by
  let := hasSummableGeomSeries_opposite (A := A)
  apply MulOpposite.op_injective
  simpa only [MulOpposite.op_mul, op_leftInverseCorrection, MulOpposite.op_one] using
    mul_rightInverseCorrection (MulOpposite.op a) (MulOpposite.op b₀) h

/-- Norm bound for the corrected left inverse. -/
theorem norm_leftInverseCorrection_le (a b₀ : A) {ε : ℝ}
    (h : ‖1 - b₀ * a‖ ≤ ε) (hε : ε < 1) :
    ‖leftInverseCorrection a b₀‖ ≤ ‖b₀‖ / (1 - ε) := by
  let := hasSummableGeomSeries_opposite (A := A)
  have hb := norm_rightInverseCorrection_le (MulOpposite.op a) (MulOpposite.op b₀) h hε
  simpa only [← op_leftInverseCorrection, MulOpposite.norm_op] using hb

/-- Displacement bound for the corrected left inverse. -/
theorem norm_leftInverseCorrection_sub_le (a b₀ : A) {ε : ℝ}
    (h : ‖1 - b₀ * a‖ ≤ ε) (hε : ε < 1) :
    ‖leftInverseCorrection a b₀ - b₀‖ ≤ ε * ‖b₀‖ / (1 - ε) := by
  let := hasSummableGeomSeries_opposite (A := A)
  have hb := norm_rightInverseCorrection_sub_le (MulOpposite.op a) (MulOpposite.op b₀) h hε
  simpa only [← op_leftInverseCorrection, ← MulOpposite.op_sub, MulOpposite.norm_op] using hb

/-- The left residual certificate supplies an exact left inverse and both quantitative bounds. -/
theorem exists_left_inverse_of_residual_le (a b₀ : A) {ε : ℝ}
    (h : ‖1 - b₀ * a‖ ≤ ε) (hε : ε < 1) :
    ∃ b : A, b * a = 1 ∧ ‖b‖ ≤ ‖b₀‖ / (1 - ε) ∧
      ‖b - b₀‖ ≤ ε * ‖b₀‖ / (1 - ε) :=
  ⟨leftInverseCorrection a b₀, leftInverseCorrection_mul a b₀ (h.trans_lt hε),
    norm_leftInverseCorrection_le a b₀ h hε,
    norm_leftInverseCorrection_sub_le a b₀ h hε⟩

/-- A small residual gives an exact right Bézout identity, also in a noncommutative ring. -/
theorem correction_identity (f b₀ : ι → A) (h : ‖residual f b₀‖ < 1) :
    ∑ i, f i * correction f b₀ i = 1 := by
  simp only [correction, ← mul_assoc, ← Finset.sum_mul]
  convert mul_neg_geom_series (residual f b₀) h using 2
  simp [residual]

theorem norm_correction_le (f b₀ : ι → A) {ε : ℝ}
    (h : ‖residual f b₀‖ ≤ ε) (hε : ε < 1) (i : ι) :
    ‖correction f b₀ i‖ ≤ ‖b₀ i‖ / (1 - ε) :=
  norm_mul_geomSeries_le (b₀ i) (residual f b₀) h hε

theorem norm_correction_sub_le (f b₀ : ι → A) {ε : ℝ}
    (h : ‖residual f b₀‖ ≤ ε) (hε : ε < 1) (i : ι) :
    ‖correction f b₀ i - b₀ i‖ ≤ ε * ‖b₀ i‖ / (1 - ε) :=
  norm_mul_geomSeries_sub_le (b₀ i) (residual f b₀) h hε

theorem sum_norm_correction_le (f b₀ : ι → A) {ε : ℝ}
    (h : ‖residual f b₀‖ ≤ ε) (hε : ε < 1) :
    ∑ i, ‖correction f b₀ i‖ ≤ (∑ i, ‖b₀ i‖) / (1 - ε) := by
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => norm_correction_le f b₀ h hε i)

theorem sum_norm_correction_sub_le (f b₀ : ι → A) {ε : ℝ}
    (h : ‖residual f b₀‖ ≤ ε) (hε : ε < 1) :
    ∑ i, ‖correction f b₀ i - b₀ i‖ ≤ ε * (∑ i, ‖b₀ i‖) / (1 - ε) := by
  rw [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => norm_correction_sub_le f b₀ h hε i)

/-- The certificate supplies both a solution bound and a distance from the proposed tuple. -/
theorem exists_bezout_of_residual_le (f b₀ : ι → A) {ε : ℝ}
    (h : ‖residual f b₀‖ ≤ ε) (hε : ε < 1) :
    ∃ b : ι → A, (∑ i, f i * b i = 1) ∧
      (∑ i, ‖b i‖ ≤ (∑ i, ‖b₀ i‖) / (1 - ε)) ∧
      (∑ i, ‖b i - b₀ i‖ ≤ ε * (∑ i, ‖b₀ i‖) / (1 - ε)) :=
  ⟨correction f b₀, correction_identity f b₀ (h.trans_lt hε),
    sum_norm_correction_le f b₀ h hε, sum_norm_correction_sub_le f b₀ h hε⟩

omit [HasSummableGeomSeries A] in
theorem residual_add (f Δf b₀ : ι → A) :
    residual (f + Δf) b₀ = residual f b₀ - ∑ i, Δf i * b₀ i := by
  simp only [residual, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  abel

omit [HasSummableGeomSeries A] in
/-- Weighted coefficient perturbations add directly to the residual budget. -/
theorem norm_residual_add_le (f Δf b₀ : ι → A) {ε : ℝ}
    (h : ‖residual f b₀‖ ≤ ε) :
    ‖residual (f + Δf) b₀‖ ≤ ε + ∑ i, ‖Δf i‖ * ‖b₀ i‖ := by
  rw [residual_add]
  refine (norm_sub_le _ _).trans (add_le_add h ?_)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_mul_le _ _))

/-- Robust Bézout solvability with the same candidate tuple and an enlarged residual budget. -/
theorem exists_bezout_of_perturbation (f Δf b₀ : ι → A) {ε : ℝ}
    (h : ‖residual f b₀‖ ≤ ε)
    (hε : ε + ∑ i, ‖Δf i‖ * ‖b₀ i‖ < 1) :
    ∃ b : ι → A, (∑ i, (f i + Δf i) * b i = 1) ∧
      (∑ i, ‖b i‖ ≤ (∑ i, ‖b₀ i‖) / (1 - (ε + ∑ i, ‖Δf i‖ * ‖b₀ i‖))) ∧
      (∑ i, ‖b i - b₀ i‖ ≤
        (ε + ∑ i, ‖Δf i‖ * ‖b₀ i‖) * (∑ i, ‖b₀ i‖) /
          (1 - (ε + ∑ i, ‖Δf i‖ * ‖b₀ i‖))) :=
  exists_bezout_of_residual_le (f + Δf) b₀ (norm_residual_add_le f Δf b₀ h) hε


omit [HasSummableGeomSeries A] in
/-- The residual varies continuously with a finite candidate family. -/
theorem continuous_residual (f : ι → A) : Continuous (residual f) := by
  unfold residual
  fun_prop

omit [HasSummableGeomSeries A] in
/-- Any dense coefficient family contains candidates with arbitrarily small residual. -/
theorem exists_dense_candidate_of_bezout {D : Set A} (hD : Dense D)
    (f b : ι → A) (hb : ∑ i, f i * b i = 1) {η : ℝ} (hη : 0 < η) :
    ∃ b₀ : ι → A, (∀ i, b₀ i ∈ D) ∧ ‖residual f b₀‖ < η := by
  have hd : Dense (Set.pi Set.univ (fun _ : ι => D)) :=
    dense_pi Set.univ (fun _ _ => hD)
  obtain ⟨b₀, hb₀, hr⟩ := hd.exists_mem_open
    (isOpen_lt (continuous_residual f).norm continuous_const)
    ⟨b, by simpa only [Set.mem_ofPred_eq, residual, hb, sub_self, norm_zero] using hη⟩
  exact ⟨b₀, fun i => hb₀ i (Set.mem_univ i), hr⟩

/-- Solvability is equivalent to a residual certificate using any prescribed dense family. -/
theorem exists_bezout_iff_dense_certificate {D : Set A} (hD : Dense D) (f : ι → A) :
    (∃ b : ι → A, ∑ i, f i * b i = 1) ↔
      ∃ b₀ : ι → A, (∀ i, b₀ i ∈ D) ∧ ‖residual f b₀‖ < 1 := by
  constructor
  · rintro ⟨b, hb⟩
    exact exists_dense_candidate_of_bezout hD f b hb zero_lt_one
  · rintro ⟨b₀, _, hr⟩
    exact ⟨correction f b₀, correction_identity f b₀ hr⟩


end RadiiPolynomial.Residual
