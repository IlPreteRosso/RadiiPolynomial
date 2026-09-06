import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Aeval
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.EvalC
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.AnalyticExt
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UnitLift
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.SymmetricSubalgebra

/-!
# The forward Joukowski map between coefficient algebras

The symmetric Laurent generator

`g = (e₁ + e₋₁) / 2`

has power growth `‖gⁿ‖ ≤ 2 a(ν)ⁿ`, where
`a(ν) = (ν + ν⁻¹) / 2` is the semi-major axis of the Bernstein ellipse.
Consequently, whenever `a(ν) ≤ r`, the universal property of the Taylor
algebra produces a continuous algebra homomorphism into the physical,
flip-fixed Chebyshev algebra.  Its composite with the inclusion into the
bilateral carrier is

`joukowskiAeval : l1Weighted r →A[ℝ] l1Chebyshev ν`.

On characters this map is contravariantly the classical Joukowski map
`z ↦ (z + z⁻¹) / 2`: Laurent evaluation at an annulus point after
`joukowskiAeval` is Taylor evaluation at its Joukowski image.  The final
theorem states the same naturality for an arbitrary complex-valued character.

This module is independent of the concrete Taylor/Chebyshev IVP applications
and is exposed by the `CrossGeometry` sequence-space facade.
-/

noncomputable section

namespace RadiiPolynomial

namespace CrossGeometry

open lpOneAlg

/-- The semi-major axis of the Bernstein ellipse associated to the bilateral
weight `ν^|k|`. -/
def semiMajor (ν : PosReal) : ℝ := ((ν : ℝ) + (ν : ℝ)⁻¹) / 2

/-- The signed semi-minor expression `(ν - ν⁻¹)/2`.  It is the semi-minor
axis of the Bernstein ellipse when `ν ≥ 1`; for `ν < 1` it is negative. -/
def semiMinor (ν : PosReal) : ℝ := ((ν : ℝ) - (ν : ℝ)⁻¹) / 2

/-- The signed inverse expression `s + √(1+s²)`.  For `s ≥ 0` this is the
Bernstein-ellipse parameter whose semi-minor axis is `s`. -/
def bernsteinParameter (s : ℝ) : ℝ := s + Real.sqrt (1 + s ^ 2)

theorem semiMajor_pos (ν : PosReal) : 0 < semiMajor ν := by
  unfold semiMajor
  exact div_pos (add_pos ν.coe_pos (inv_pos.mpr ν.coe_pos)) (by norm_num)

/-- Every Bernstein ellipse contains its focal interval, so its semi-major
axis is at least one. -/
theorem one_le_semiMajor (ν : PosReal) : (1 : ℝ) ≤ semiMajor ν := by
  have hν : (0 : ℝ) < (ν : ℝ) := ν.2
  have hid : ((ν : ℝ) + (ν : ℝ)⁻¹ - 2) * (ν : ℝ) = ((ν : ℝ) - 1) ^ 2 := by
    field_simp
    ring
  have hs : 0 ≤ ((ν : ℝ) - 1) ^ 2 := sq_nonneg _
  have hadd : 0 ≤ (ν : ℝ) + (ν : ℝ)⁻¹ - 2 := by
    by_contra h
    have hneg : ((ν : ℝ) + (ν : ℝ)⁻¹ - 2) * (ν : ℝ) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge h) hν
    linarith
  unfold semiMajor
  linarith

/-- In the Bernstein regime `ν ≥ 1`, the signed semi-minor expression is
nonnegative. -/
theorem semiMinor_nonneg {ν : PosReal} (hν : (1 : ℝ) ≤ (ν : ℝ)) :
    0 ≤ semiMinor ν := by
  unfold semiMinor
  exact div_nonneg
    (sub_nonneg.mpr ((inv_le_one_of_one_le₀ hν).trans hν)) (by norm_num)

/-- A positive Taylor radius can fit below the semi-minor axis only in the
strict Bernstein regime `ν > 1`. -/
theorem one_lt_of_pos_le_semiMinor {ν σ : PosReal}
    (hreverse : (σ : ℝ) ≤ semiMinor ν) : (1 : ℝ) < (ν : ℝ) := by
  have hbpos : 0 < semiMinor ν := σ.coe_pos.trans_le hreverse
  by_contra hν
  have hνle : (ν : ℝ) ≤ 1 := le_of_not_gt hν
  have hinv : (1 : ℝ) ≤ (ν : ℝ)⁻¹ := (one_le_inv₀ ν.coe_pos).2 hνle
  unfold semiMinor at hbpos
  linarith

/-- The two semi-axes belong to the confocal family with foci `±1`. -/
theorem semiMajor_sq_sub_semiMinor_sq (ν : PosReal) :
    semiMajor ν ^ 2 - semiMinor ν ^ 2 = 1 := by
  have hν : (ν : ℝ) ≠ 0 := ν.coe_ne_zero
  unfold semiMajor semiMinor
  field_simp
  ring

/-- A Taylor disc of radius `s ≥ 0` fits inside the Bernstein ellipse exactly
when the corresponding ellipse parameter is at most `ν`. -/
theorem bernsteinParameter_le_iff_le_semiMinor {ν : PosReal} {s : ℝ} :
    bernsteinParameter s ≤ (ν : ℝ) ↔ s ≤ semiMinor ν := by
  have hν0 : (0 : ℝ) < (ν : ℝ) := ν.2
  have hmul : (ν : ℝ) * (ν : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hν0.ne'
  have hinv0 : (0 : ℝ) < (ν : ℝ)⁻¹ := inv_pos.mpr hν0
  have hsq : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
  have hsqrt0 : 0 ≤ Real.sqrt (1 + s ^ 2) := Real.sqrt_nonneg _
  unfold bernsteinParameter semiMinor
  constructor
  · intro h
    have h1 : Real.sqrt (1 + s ^ 2) ≤ (ν : ℝ) - s := by linarith
    have h2 : 1 + s ^ 2 ≤ ((ν : ℝ) - s) ^ 2 := by nlinarith [h1, hsqrt0]
    nlinarith [h2, hν0, hmul]
  · intro h
    have h2 : 1 + s ^ 2 ≤ ((ν : ℝ) - s) ^ 2 := by nlinarith [hν0, hmul, h]
    have hνs : 0 ≤ (ν : ℝ) - s := by nlinarith [hinv0]
    have h3 := Real.sqrt_le_sqrt h2
    rw [Real.sqrt_sq hνs] at h3
    linarith

/-- Combining the forward and reverse inclusion gates necessarily loses
Taylor radius: `σ² + 1 ≤ r²`. -/
theorem roundtrip_radius_sq_le {ν r σ : PosReal}
    (hforward : semiMajor ν ≤ (r : ℝ))
    (hreverse : (σ : ℝ) ≤ semiMinor ν) :
    (σ : ℝ) ^ 2 + 1 ≤ (r : ℝ) ^ 2 := by
  have hb : semiMinor ν ^ 2 = semiMajor ν ^ 2 - 1 := by
    linarith [semiMajor_sq_sub_semiMinor_sq ν]
  have hσ : (σ : ℝ) ^ 2 ≤ semiMinor ν ^ 2 :=
    pow_le_pow_left₀ σ.coe_nonneg hreverse 2
  have hr : semiMajor ν ^ 2 ≤ (r : ℝ) ^ 2 :=
    pow_le_pow_left₀ (semiMajor_pos ν).le hforward 2
  linarith

/-- Any Taylor→Chebyshev→Taylor round trip satisfying these two inclusion
gates strictly decreases the Taylor radius. -/
theorem roundtrip_radius_lt {ν r σ : PosReal}
    (hforward : semiMajor ν ≤ (r : ℝ))
    (hreverse : (σ : ℝ) ≤ semiMinor ν) :
    (σ : ℝ) < (r : ℝ) := by
  have h := roundtrip_radius_sq_le hforward hreverse
  nlinarith [r.coe_pos, σ.coe_pos]

/-- The Joukowski map `z ↦ (z + z⁻¹) / 2`. -/
def joukowski (z : ℂ) : ℂ := (z + z⁻¹) / 2

/-- The symmetric Laurent generator `(e₁ + e₋₁) / 2`. -/
def joukowskiGen (ν : PosReal) : l1Chebyshev ν :=
  (2 : ℝ)⁻¹ • (single 1 1 + single (-1) 1)

/-- The Joukowski generator is fixed by reflection of the bilateral modes. -/
theorem joukowskiGen_isSymmetric (ν : PosReal) : (joukowskiGen ν).IsSymmetric := by
  apply l1Chebyshev.IsSymmetric.smul
  intro k
  show l1Chebyshev.toSeq (single 1 1 + single (-1) 1 : l1Chebyshev ν) (-k) =
    l1Chebyshev.toSeq (single 1 1 + single (-1) 1 : l1Chebyshev ν) k
  simp only [l1Chebyshev.toSeq_add, l1Chebyshev.toSeq_single, neg_eq_iff_eq_neg]
  ring_nf

/-- The Joukowski generator as an element of the physical Chebyshev algebra. -/
def joukowskiGenSymm (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] :
    l1Chebyshev.symmetricSubalgebra ν :=
  ⟨joukowskiGen ν, joukowskiGen_isSymmetric ν⟩

private lemma pow_natAbs_diff_le (ν : PosReal) {n m : ℕ} (hmn : m ≤ n) :
    (ν : ℝ) ^ Int.natAbs ((m : ℤ) - ((n - m : ℕ) : ℤ)) ≤
      (ν : ℝ) ^ m * (ν : ℝ)⁻¹ ^ (n - m) +
        (ν : ℝ)⁻¹ ^ m * (ν : ℝ) ^ (n - m) := by
  by_cases h : n - m ≤ m
  · rw [show Int.natAbs ((m : ℤ) - ((n - m : ℕ) : ℤ)) = m - (n - m) by omega,
      pow_sub₀ (ν : ℝ) ν.coe_ne_zero h, ← inv_pow]
    exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg (inv_nonneg.mpr ν.coe_nonneg) m)
      (pow_nonneg ν.coe_nonneg (n - m)))
  · have h' : m ≤ n - m := by omega
    rw [show Int.natAbs ((m : ℤ) - ((n - m : ℕ) : ℤ)) = (n - m) - m by omega,
      pow_sub₀ (ν : ℝ) ν.coe_ne_zero h', ← inv_pow]
    rw [mul_comm ((ν : ℝ) ^ (n - m))]
    exact le_add_of_nonneg_left (mul_nonneg (pow_nonneg ν.coe_nonneg m)
      (pow_nonneg (inv_nonneg.mpr ν.coe_nonneg) (n - m)))

private lemma joukowskiGen_binomial_term (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]
    (n m : ℕ) :
    (single (E := ScaledRealZ ν) 1 (1 : ℝ)) ^ m * single (-1) 1 ^ (n - m) *
        (n.choose m : l1Chebyshev ν)
      = single ((m : ℤ) - ((n - m : ℕ) : ℤ)) (n.choose m : ℝ) := by
  rw [single_pow, single_pow, single_mul_single, one_mul]
  simp only [nsmul_eq_mul, mul_one]
  rw [show (n.choose m : l1Chebyshev ν) = (n.choose m : ℝ) • (1 : l1Chebyshev ν) by
    rw [Algebra.smul_def, mul_one, map_natCast]]
  rw [mul_smul_comm, mul_one, ← single_smul]
  congr 1
  ring

/-- The symmetric Laurent generator has power growth governed by the
semi-major axis: `‖gⁿ‖ ≤ 2 a(ν)ⁿ`. -/
theorem norm_joukowskiGen_pow_le (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] (n : ℕ) :
    ‖joukowskiGen ν ^ n‖ ≤ 2 * semiMajor ν ^ n := by
  rw [joukowskiGen, smul_pow, norm_smul, norm_pow]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [add_pow]
  have hs : ‖∑ m ∈ Finset.range (n + 1),
      (single (E := ScaledRealZ ν) 1 (1 : ℝ)) ^ m * single (-1) 1 ^ (n - m) *
        (n.choose m : l1Chebyshev ν)‖
      ≤ ∑ m ∈ Finset.range (n + 1),
        (n.choose m : ℝ) * (ν : ℝ) ^ Int.natAbs ((m : ℤ) - (n - m : ℕ)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [joukowskiGen_binomial_term, l1Chebyshev.norm_single,
      abs_of_nonneg (Nat.cast_nonneg _)]
  have hsum : ∑ m ∈ Finset.range (n + 1),
      (n.choose m : ℝ) * (ν : ℝ) ^ Int.natAbs ((m : ℤ) - (n - m : ℕ))
      ≤ 2 * ((ν : ℝ) + (ν : ℝ)⁻¹) ^ n := by
    calc
      _ ≤ ∑ m ∈ Finset.range (n + 1), (n.choose m : ℝ) *
          ((ν : ℝ) ^ m * (ν : ℝ)⁻¹ ^ (n - m) +
            (ν : ℝ)⁻¹ ^ m * (ν : ℝ) ^ (n - m)) := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.mem_range] at hm
        exact mul_le_mul_of_nonneg_left (pow_natAbs_diff_le ν (by omega))
          (Nat.cast_nonneg _)
      _ = (∑ m ∈ Finset.range (n + 1),
            (ν : ℝ) ^ m * (ν : ℝ)⁻¹ ^ (n - m) * (n.choose m : ℝ)) +
          ∑ m ∈ Finset.range (n + 1),
            (ν : ℝ)⁻¹ ^ m * (ν : ℝ) ^ (n - m) * (n.choose m : ℝ) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro m _
        ring
      _ = ((ν : ℝ) + (ν : ℝ)⁻¹) ^ n + ((ν : ℝ)⁻¹ + (ν : ℝ)) ^ n := by
        rw [add_pow, add_pow]
      _ = 2 * ((ν : ℝ) + (ν : ℝ)⁻¹) ^ n := by
        rw [add_comm ((ν : ℝ)⁻¹)]
        ring
  calc
    (2 : ℝ)⁻¹ ^ n * ‖∑ m ∈ Finset.range (n + 1),
        (single (E := ScaledRealZ ν) 1 (1 : ℝ)) ^ m * single (-1) 1 ^ (n - m) *
          (n.choose m : l1Chebyshev ν)‖
      ≤ (2 : ℝ)⁻¹ ^ n * ∑ m ∈ Finset.range (n + 1),
          (n.choose m : ℝ) * (ν : ℝ) ^ Int.natAbs ((m : ℤ) - (n - m : ℕ)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (2 : ℝ)⁻¹ ^ n * (2 * ((ν : ℝ) + (ν : ℝ)⁻¹) ^ n) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * semiMajor ν ^ n := by
      unfold semiMajor
      rw [div_eq_mul_inv, mul_pow]
      ring

/-- Under the inclusion gate `a(ν) ≤ r`, the symmetric Laurent generator is
dominated by `2 rⁿ`, exactly the hypothesis required by `l1Weighted.aeval`. -/
theorem norm_joukowskiGen_pow_le_of_gate {ν r : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : semiMajor ν ≤ (r : ℝ)) (n : ℕ) :
    ‖joukowskiGen ν ^ n‖ ≤ 2 * (r : ℝ) ^ n :=
  (norm_joukowskiGen_pow_le ν n).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (semiMajor_pos ν).le hgate n) (by norm_num))

/-- The forward map with its physical codomain exposed: the universal
Taylor evaluation at the symmetric Joukowski generator. -/
def joukowskiAevalSymm {ν r : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : semiMajor ν ≤ (r : ℝ)) :
    l1Weighted r →A[ℝ] l1Chebyshev.symmetricSubalgebra ν :=
  l1Weighted.aeval r (joukowskiGenSymm ν) 2 fun n => by
    change ‖joukowskiGen ν ^ n‖ ≤ 2 * (r : ℝ) ^ n
    exact norm_joukowskiGen_pow_le_of_gate hgate n

@[simp] theorem joukowskiAevalSymm_gen {ν r : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : semiMajor ν ≤ (r : ℝ)) :
    joukowskiAevalSymm hgate (single 1 1) = joukowskiGenSymm ν :=
  l1Weighted.aeval_gen r (joukowskiGenSymm ν) 2 _

/-- The forward map viewed in the ambient bilateral carrier. -/
def joukowskiAeval {ν r : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : semiMajor ν ≤ (r : ℝ)) : l1Weighted r →A[ℝ] l1Chebyshev ν :=
  (l1Chebyshev.symmetricSubalgebra ν).valA.comp (joukowskiAevalSymm hgate)

@[simp] theorem joukowskiAeval_gen {ν r : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : semiMajor ν ≤ (r : ℝ)) :
    joukowskiAeval hgate (single 1 1) = joukowskiGen ν := by
  rw [joukowskiAeval, ContinuousAlgHom.comp_apply, joukowskiAevalSymm_gen]
  rfl

theorem valA_comp_joukowskiAevalSymm {ν r : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : semiMajor ν ≤ (r : ℝ)) :
    (l1Chebyshev.symmetricSubalgebra ν).valA.comp (joukowskiAevalSymm hgate) =
      joukowskiAeval hgate :=
  rfl

@[simp] theorem coe_joukowskiAevalSymm {ν r : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : semiMajor ν ≤ (r : ℝ)) (a : l1Weighted r) :
    ((joukowskiAevalSymm hgate a : l1Chebyshev.symmetricSubalgebra ν) : l1Chebyshev ν) =
      joukowskiAeval hgate a :=
  rfl

private lemma add_inv_le_of_inv_le_le {t ν : ℝ} (ht : 0 < t) (hν : 0 < ν)
    (hlo : ν⁻¹ ≤ t) (hhi : t ≤ ν) : t + t⁻¹ ≤ ν + ν⁻¹ := by
  have hleft : 0 ≤ ν - t := sub_nonneg.mpr hhi
  have hright : 0 ≤ ν * t - 1 := by
    have h := mul_le_mul_of_nonneg_left hlo hν.le
    rw [mul_inv_cancel₀ hν.ne'] at h
    exact sub_nonneg.mpr h
  have hmul : (t + t⁻¹) * (ν * t) ≤ (ν + ν⁻¹) * (ν * t) := by
    calc
      (t + t⁻¹) * (ν * t) = ν * t ^ 2 + ν := by field_simp
      _ ≤ ν ^ 2 * t + t := by nlinarith [mul_nonneg hleft hright]
      _ = (ν + ν⁻¹) * (ν * t) := by field_simp
  nlinarith [mul_pos hν ht]

/-- The Joukowski image of the closed annulus lies in the closed disc of
radius `a(ν)`. -/
theorem norm_joukowski_le_semiMajor (ν : PosReal) {z : ℂ}
    (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)) :
    ‖joukowski z‖ ≤ semiMajor ν := by
  have hz0 : z ≠ 0 := lpOneAlg.ne_zero_of_annulus ν hz
  have hsum : ‖z‖ + ‖z‖⁻¹ ≤ (ν : ℝ) + (ν : ℝ)⁻¹ :=
    add_inv_le_of_inv_le_le (norm_pos_iff.mpr hz0) ν.coe_pos hz.1 hz.2
  rw [joukowski, norm_div]
  norm_num
  calc
    ‖z + z⁻¹‖ / 2 ≤ (‖z‖ + ‖z⁻¹‖) / 2 := by
      exact div_le_div_of_nonneg_right (norm_add_le z z⁻¹) (by norm_num)
    _ = (‖z‖ + ‖z‖⁻¹) / 2 := by rw [norm_inv]
    _ ≤ ((ν : ℝ) + (ν : ℝ)⁻¹) / 2 := by
      exact div_le_div_of_nonneg_right hsum (by norm_num)
    _ = semiMajor ν := rfl

/-- Annulus-to-disc containment at the cross-geometry gate `a(ν) ≤ r`. -/
theorem norm_joukowski_le {ν r : PosReal} (hgate : semiMajor ν ≤ (r : ℝ)) {z : ℂ}
    (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)) : ‖joukowski z‖ ≤ (r : ℝ) :=
  (norm_joukowski_le_semiMajor ν hz).trans hgate

/-- The Joukowski gate contains the physical interval, so in particular
`1 ≤ r`. -/
theorem one_le_of_semiMajor_le {ν r : PosReal}
    (hgate : semiMajor ν ≤ (r : ℝ)) : (1 : ℝ) ≤ (r : ℝ) :=
  (one_le_semiMajor ν).trans hgate

/-- Physical Chebyshev evaluation sends the symmetric Laurent generator to
the coordinate itself. -/
theorem eval_joukowskiGen (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]
    (t : ℝ) (ht : |t| ≤ 1) : l1Chebyshev.eval (joukowskiGen ν) t = t := by
  rw [joukowskiGen, l1Chebyshev.eval_smul,
    l1Chebyshev.eval_add (single 1 1) (single (-1) 1) ht]
  have hpos : l1Chebyshev.eval (single 1 1 : l1Chebyshev ν) t = 2 * t := by
    unfold l1Chebyshev.eval
    rw [l1Chebyshev.toSeq_single, if_neg (by norm_num : (0 : ℤ) ≠ 1)]
    simp only [zero_add]
    rw [tsum_eq_single 0]
    · norm_num [Polynomial.Chebyshev.T_one]
      rw [l1Chebyshev.toSeq_single, if_pos rfl]
      ring
    · intro k hk
      rw [l1Chebyshev.toSeq_single, if_neg (by omega), zero_mul]
  have hneg : l1Chebyshev.eval (single (-1) 1 : l1Chebyshev ν) t = 0 := by
    unfold l1Chebyshev.eval
    rw [l1Chebyshev.toSeq_single, if_neg (by norm_num : (0 : ℤ) ≠ -1)]
    simp only [zero_add]
    rw [tsum_congr (fun k => by
      rw [l1Chebyshev.toSeq_single, if_neg (by omega), zero_mul]), tsum_zero, mul_zero]
  rw [hpos, hneg]
  norm_num
  ring

/-- Real evaluation is natural across the physical Joukowski map: evaluation
of the Chebyshev realization at `t ∈ [-1,1]` pulls back to Taylor evaluation
at the same physical point. -/
theorem symmetricEvalCharacter_comp_joukowskiAevalSymm
    {ν r : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : semiMajor ν ≤ (r : ℝ)) (t : ℝ) (ht : |t| ≤ 1) :
    (l1Chebyshev.symmetricEvalCharacter ν t ht).comp (joukowskiAevalSymm hgate) =
      l1Weighted.evalContinuousAlgHom t (ht.trans (one_le_of_semiMajor_le hgate)) := by
  apply l1Weighted.algHom_ext r
  rw [ContinuousAlgHom.comp_apply, joukowskiAevalSymm_gen,
    l1Weighted.evalContinuousAlgHom_gen]
  rw [l1Chebyshev.symmetricEvalCharacter_apply]
  exact eval_joukowskiGen ν t ht

/-- The physical Joukowski map is injective.  Equality after the map gives
equality of Taylor realizations near `0`, hence equality of their coefficients
by analytic extensionality. -/
theorem joukowskiAevalSymm_injective {ν r : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : semiMajor ν ≤ (r : ℝ)) : Function.Injective (joukowskiAevalSymm hgate) := by
  intro a b hab
  apply l1Weighted.ext_of_eventuallyEq_eval
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t htball
  have ht : |t| ≤ 1 := by
    exact (by simpa [Real.dist_eq] using (Metric.mem_ball.mp htball).le)
  have hsquare := symmetricEvalCharacter_comp_joukowskiAevalSymm hgate t ht
  have ha := DFunLike.congr_fun hsquare a
  have hb := DFunLike.congr_fun hsquare b
  rw [ContinuousAlgHom.comp_apply, l1Weighted.evalContinuousAlgHom_apply] at ha hb
  rw [← ha, ← hb, hab]

/-- The forward Joukowski map remains injective after inclusion into the
ambient bilateral coefficient algebra. -/
theorem joukowskiAeval_injective {ν r : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : semiMajor ν ≤ (r : ℝ)) : Function.Injective (joukowskiAeval hgate) := by
  intro a b hab
  apply joukowskiAevalSymm_injective hgate
  apply Subtype.ext
  simpa only [coe_joukowskiAevalSymm] using hab

/-- **Joukowski naturality.** Pulling Laurent evaluation back along the forward
cross-geometry map is Taylor evaluation at the Joukowski image. -/
theorem evalLaurentC_comp_joukowskiAeval {ν r : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : semiMajor ν ≤ (r : ℝ)) (z : ℂ)
    (hz : (ν : ℝ)⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ (ν : ℝ)) :
    (l1Chebyshev.evalLaurentC ν z hz).comp (joukowskiAeval hgate) =
      l1Weighted.evalC r (joukowski z) (norm_joukowski_le hgate hz) := by
  apply l1Weighted.algHom_ext r
  rw [ContinuousAlgHom.comp_apply, joukowskiAeval_gen, l1Weighted.evalC_gen]
  simp only [joukowskiGen, map_smul, map_add, l1Chebyshev.evalLaurentC_single,
    zpow_neg_one, joukowski, Complex.real_smul]
  norm_num
  ring

/-- Arbitrary-character form of Joukowski naturality: the pullback of a
complex-valued character is evaluation at the Joukowski image of its generator
value. -/
theorem comp_joukowskiAeval_eq_evalC {ν r : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : semiMajor ν ≤ (r : ℝ)) (χ : l1Chebyshev ν →A[ℝ] ℂ) :
    χ.comp (joukowskiAeval hgate) =
      l1Weighted.evalC r (joukowski (χ (single 1 1)))
        (norm_joukowski_le hgate
          ⟨l1Chebyshev.inv_le_norm_genUnit ν χ, l1Chebyshev.norm_genUnit_le ν χ⟩) := by
  apply l1Weighted.algHom_ext r
  rw [ContinuousAlgHom.comp_apply, joukowskiAeval_gen, l1Weighted.evalC_gen]
  have hinv : χ (single (-1) 1) = (χ (single 1 1))⁻¹ := by
    rw [← lpOneAlg.genUnit_inv_val ν χ, Units.val_inv_eq_inv_val,
      lpOneAlg.genUnit_val]
  simp only [joukowskiGen, map_smul, map_add, hinv, joukowski, Complex.real_smul]
  norm_num
  ring

/-- At the left endpoint, the forward change of basis preserves evaluation
at that same physical point.  In particular, it pulls the Chebyshev endpoint
character back to Taylor evaluation at `-1`, not to the Taylor centre `0`. -/
theorem evalLaurentC_neg_one_comp_joukowskiAeval {ν r : PosReal}
    [Fact (1 ≤ (ν : ℝ))] (hgate : semiMajor ν ≤ (r : ℝ)) :
    let hz : (ν : ℝ)⁻¹ ≤ ‖(-1 : ℂ)‖ ∧ ‖(-1 : ℂ)‖ ≤ (ν : ℝ) := by
      simpa using (show (ν : ℝ)⁻¹ ≤ 1 ∧ 1 ≤ (ν : ℝ) from
        ⟨inv_le_one_of_one_le₀ Fact.out, Fact.out⟩)
    (l1Chebyshev.evalLaurentC ν (-1) hz).comp (joukowskiAeval hgate) =
      l1Weighted.evalC r (-1) (by
        simpa [joukowski] using norm_joukowski_le hgate hz) := by
  dsimp only
  simpa [joukowski] using
    evalLaurentC_comp_joukowskiAeval hgate (-1 : ℂ)
      (by simpa using (show (ν : ℝ)⁻¹ ≤ 1 ∧ 1 ≤ (ν : ℝ) from
        ⟨inv_le_one_of_one_le₀ Fact.out, Fact.out⟩))

/-! ### Boundary-aligned substitution -/

/-- The shifted physical coordinate `1 + t`, represented in the bilateral
carrier.  Unlike `joukowskiGen`, it vanishes at the left endpoint. -/
def endpointJoukowskiGen (ν : PosReal) : l1Chebyshev ν :=
  1 + joukowskiGen ν

theorem endpointJoukowskiGen_isSymmetric (ν : PosReal) :
    (endpointJoukowskiGen ν).IsSymmetric :=
  l1Chebyshev.isSymmetric_one.add (joukowskiGen_isSymmetric ν)

/-- The boundary-aligned generator as an element of the physical Chebyshev
algebra. -/
def endpointJoukowskiGenSymm (ν : PosReal) [Fact (1 ≤ (ν : ℝ))] :
    l1Chebyshev.symmetricSubalgebra ν :=
  ⟨endpointJoukowskiGen ν, endpointJoukowskiGen_isSymmetric ν⟩

/-- The shifted generator has power growth controlled by the translated
Bernstein ellipse: `‖(1 + g)ⁿ‖ ≤ 2(1 + a(ν))ⁿ`. -/
theorem norm_endpointJoukowskiGen_pow_le (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]
    (n : ℕ) :
    ‖endpointJoukowskiGen ν ^ n‖ ≤ 2 * (1 + semiMajor ν) ^ n := by
  rw [endpointJoukowskiGen, add_pow]
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ m ∈ Finset.range (n + 1),
        ‖(1 : l1Chebyshev ν) ^ m * joukowskiGen ν ^ (n - m) *
          (n.choose m : l1Chebyshev ν)‖
      ≤ ∑ m ∈ Finset.range (n + 1),
          2 * semiMajor ν ^ (n - m) * (n.choose m : ℝ) := by
        refine Finset.sum_le_sum fun m _ => ?_
        calc
          ‖(1 : l1Chebyshev ν) ^ m * joukowskiGen ν ^ (n - m) *
              (n.choose m : l1Chebyshev ν)‖
            ≤ ‖(1 : l1Chebyshev ν) ^ m * joukowskiGen ν ^ (n - m)‖ *
                ‖(n.choose m : l1Chebyshev ν)‖ := norm_mul_le _ _
          _ ≤ ‖joukowskiGen ν ^ (n - m)‖ * (n.choose m : ℝ) := by
            rw [one_pow, one_mul]
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            rw [← nsmul_one (n.choose m)]
            simpa using (norm_nsmul_le :
              ‖n.choose m • (1 : l1Chebyshev ν)‖ ≤
                (n.choose m : ℝ) * ‖(1 : l1Chebyshev ν)‖)
          _ ≤ 2 * semiMajor ν ^ (n - m) * (n.choose m : ℝ) :=
            mul_le_mul_of_nonneg_right (norm_joukowskiGen_pow_le ν (n - m))
              (Nat.cast_nonneg _)
    _ = 2 * (1 + semiMajor ν) ^ n := by
      rw [add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [one_pow, one_mul]
      ring

theorem norm_endpointJoukowskiGen_pow_le_of_gate {ν r : PosReal}
    [Fact (1 ≤ (ν : ℝ))] (hgate : 1 + semiMajor ν ≤ (r : ℝ)) (n : ℕ) :
    ‖endpointJoukowskiGen ν ^ n‖ ≤ 2 * (r : ℝ) ^ n :=
  (norm_endpointJoukowskiGen_pow_le ν n).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (add_nonneg zero_le_one (semiMajor_pos ν).le) hgate n) (by norm_num))

/-- Taylor substitution by the shifted coordinate `1 + t`.  The stronger gate
`1 + a(ν) ≤ r` prices the translation and aligns the Taylor centre with the
Chebyshev left endpoint. -/
def endpointJoukowskiAevalSymm {ν r : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : 1 + semiMajor ν ≤ (r : ℝ)) :
    l1Weighted r →A[ℝ] l1Chebyshev.symmetricSubalgebra ν :=
  l1Weighted.aeval r (endpointJoukowskiGenSymm ν) 2 fun n => by
    change ‖endpointJoukowskiGen ν ^ n‖ ≤ 2 * (r : ℝ) ^ n
    exact norm_endpointJoukowskiGen_pow_le_of_gate hgate n

@[simp]
theorem endpointJoukowskiAevalSymm_gen {ν r : PosReal}
    [Fact (1 ≤ (ν : ℝ))] (hgate : 1 + semiMajor ν ≤ (r : ℝ)) :
    endpointJoukowskiAevalSymm hgate (single 1 1) = endpointJoukowskiGenSymm ν :=
  l1Weighted.aeval_gen r (endpointJoukowskiGenSymm ν) 2 _

private lemma abs_one_add_le_two {t : ℝ} (ht : |t| ≤ 1) : |1 + t| ≤ 2 := by
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- Evaluation naturality for the boundary-aligned coordinate: physical
evaluation at `t` pulls back to Taylor evaluation at `1 + t`. -/
theorem symmetricEvalCharacter_comp_endpointJoukowskiAevalSymm
    {ν r : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : 1 + semiMajor ν ≤ (r : ℝ)) (t : ℝ) (ht : |t| ≤ 1) :
    (l1Chebyshev.symmetricEvalCharacter ν t ht).comp
        (endpointJoukowskiAevalSymm hgate) =
      l1Weighted.evalContinuousAlgHom (1 + t)
        ((abs_one_add_le_two ht).trans (by linarith [one_le_semiMajor ν])) := by
  apply l1Weighted.algHom_ext r
  rw [ContinuousAlgHom.comp_apply, endpointJoukowskiAevalSymm_gen,
    l1Weighted.evalContinuousAlgHom_gen,
    l1Chebyshev.symmetricEvalCharacter_apply t ht]
  change l1Chebyshev.eval (1 + joukowskiGen ν) t = 1 + t
  rw [l1Chebyshev.eval_add 1 (joukowskiGen ν) ht,
    l1Chebyshev.eval_one, eval_joukowskiGen ν t ht]

private lemma abs_neg_one_le_one : |(-1 : ℝ)| ≤ 1 := by norm_num

/-- At the left endpoint, the boundary-aligned substitution pulls back to
Taylor evaluation at the expansion centre. -/
theorem symmetricEndpointCharacter_comp_endpointJoukowskiAevalSymm
    {ν r : PosReal} [Fact (1 ≤ (ν : ℝ))]
    (hgate : 1 + semiMajor ν ≤ (r : ℝ)) :
    (l1Chebyshev.symmetricEvalCharacter ν (-1) abs_neg_one_le_one).comp
        (endpointJoukowskiAevalSymm hgate) =
      l1Weighted.evalContinuousAlgHom 0 (by simp) := by
  simpa using symmetricEvalCharacter_comp_endpointJoukowskiAevalSymm
    hgate (-1) abs_neg_one_le_one

end CrossGeometry

end RadiiPolynomial

end
