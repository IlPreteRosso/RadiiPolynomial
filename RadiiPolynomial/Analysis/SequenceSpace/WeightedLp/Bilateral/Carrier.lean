import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Carrier
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Scalar

/-! Bilateral geometric state X₂ and bounded coefficient codomain Y, with coefficient reconstruction. No multiplication instance is added. -/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp.Bilateral

section Carriers



/-- The bilateral geometric ℓ² carrier `WeightedLp ℤ (geomFiberZ 𝕜 ν) 2`. -/
abbrev X₂ (𝕜 : Type*) [NormedField 𝕜] (ν : PosReal) := WeightedLp ℤ (geomFiberZ 𝕜 ν) 2

/-- The bilateral geometric bounded-coefficient carrier `WeightedLp ℤ (geomFiberZ 𝕜 ν) ∞`, normed
by the supremum of the normalized magnitudes. -/
abbrev Y (𝕜 : Type*) [NormedField 𝕜] (ν : PosReal) := WeightedLp ℤ (geomFiberZ 𝕜 ν) ∞

end Carriers

section Geometry

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}

variable (ν) in
/-- The fibre norm of the standard frame of `geomFiberZ 𝕜 ν`: `‖θ_k z‖ = ‖z‖ * ν ^ |k|` (the
`𝕜`-form of `ScaledRealZ.norm_equiv_apply`). -/
theorem norm_equiv_geomFiberZ (k : ℤ) (z : 𝕜) :
    ‖FiberTrivialization.equiv (E := geomFiberZ 𝕜 ν) k z‖ = ‖z‖ * (ν : ℝ) ^ k.natAbs := by
  rw [FiberTrivialization.norm_equiv_apply, geomFiberZ_weight]

/-- The normalized magnitude of `x ∈ X₂ 𝕜 ν` at `k`: `‖x k‖ = ‖coeff x k‖ * ν ^ |k|`. -/
theorem norm_apply_X₂ (x : X₂ 𝕜 ν) (k : ℤ) : ‖x k‖ = ‖coeff x k‖ * (ν : ℝ) ^ k.natAbs := by
  rw [norm_apply_eq, geomFiberZ_weight]

/-- The normalized magnitude of `c ∈ Y 𝕜 ν` at `k`: `‖c k‖ = ‖coeff c k‖ * ν ^ |k|`. -/
theorem norm_apply_Y (c : Y 𝕜 ν) (k : ℤ) : ‖c k‖ = ‖coeff c k‖ * (ν : ℝ) ^ k.natAbs := by
  rw [norm_apply_eq, geomFiberZ_weight]

/-- The squared normalized magnitudes of `x ∈ X₂ 𝕜 ν` are summable. -/
theorem summable_sq_X₂ (x : X₂ 𝕜 ν) :
    Summable fun k : ℤ => ‖coeff x k‖ ^ 2 * (ν : ℝ) ^ (2 * k.natAbs) := by
  have h := (lp.memℓp x).summable (by norm_num)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  refine h.congr fun k => ?_
  rw [norm_apply_X₂, mul_pow, ← pow_mul']

/-- **The ℓ² norm in raw coefficients**: `‖x‖ ^ 2 = ∑' k, ‖coeff x k‖ ^ 2 * ν ^ (2 |k|)`. -/
theorem norm_sq_X₂ (x : X₂ 𝕜 ν) :
    ‖x‖ ^ 2 = ∑' k : ℤ, ‖coeff x k‖ ^ 2 * (ν : ℝ) ^ (2 * k.natAbs) := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  refine h.trans (tsum_congr fun k => ?_)
  rw [norm_apply_X₂, mul_pow, ← pow_mul']

/-- Every normalized magnitude of `c ∈ Y 𝕜 ν` is at most the norm. -/
theorem normMag_le_norm_Y (c : Y 𝕜 ν) (k : ℤ) : ‖coeff c k‖ * (ν : ℝ) ^ k.natAbs ≤ ‖c‖ :=
  (norm_apply_Y c k).symm.trans_le (norm_apply_le_norm c k)

variable (𝕜 ν) in
/-- The raw unit atom `e_k ∈ X₂ 𝕜 ν`: raw coefficient `1` at `k`, `0` elsewhere. -/
def atom (k : ℤ) : X₂ 𝕜 ν := single k 1

/-- The raw coefficients of a raw unit atom of `X₂ 𝕜 ν`: `coeff e_k = Pi.single k 1`. -/
theorem coeff_atom (k : ℤ) : coeff (atom 𝕜 ν k) = Pi.single k 1 := coeff_single k 1

/-- A raw coefficient family `f` with summable `‖f k‖ ^ 2 * ν ^ (2 |k|)` defines an element of
`X₂ 𝕜 ν`. -/
theorem memℓp_two_of_summable (f : ℤ → 𝕜)
    (h : Summable fun k => ‖f k‖ ^ 2 * (ν : ℝ) ^ (2 * k.natAbs)) :
    Memℓp (fun k => FiberTrivialization.equiv (E := geomFiberZ 𝕜 ν) k (f k)) 2 :=
  memℓp_gen <| h.congr fun k => by
    rw [norm_equiv_geomFiberZ, ENNReal.toReal_ofNat, Real.rpow_two, mul_pow, ← pow_mul']

/-- A raw coefficient family `f` with `‖f k‖ * ν ^ |k| ≤ D` for all `k` defines an element of
`Y 𝕜 ν`. -/
theorem memℓp_top_of_bdd (f : ℤ → 𝕜) {D : ℝ} (h : ∀ k, ‖f k‖ * (ν : ℝ) ^ k.natAbs ≤ D) :
    Memℓp (fun k => FiberTrivialization.equiv (E := geomFiberZ 𝕜 ν) k (f k)) ∞ :=
  memℓp_infty ⟨D, by
    rintro _ ⟨k, rfl⟩
    exact (norm_equiv_geomFiberZ ν k (f k)).trans_le (h k)⟩

end Geometry

section OfCoeff

variable {𝕜 : Type*} [NormedField 𝕜] {ν : PosReal}
variable {p : ℝ≥0∞}

/-- The element of the bilateral geometric carrier at exponent `p` with raw coefficient family
`f`: the family `k ↦ θ_k (f k)`, given its membership `hf`. The exponent is the one of `hf`:
`ofCoeff f (memℓp_two_of_summable f h) : X₂ 𝕜 ν` and
`ofCoeff f (memℓp_top_of_bdd f h) : Y 𝕜 ν`. -/
def ofCoeff (f : ℤ → 𝕜)
    (hf : Memℓp (fun k => FiberTrivialization.equiv (E := geomFiberZ 𝕜 ν) k (f k)) p) :
    WeightedLp ℤ (geomFiberZ 𝕜 ν) p :=
  ⟨_, hf⟩

/-- **The raw coefficients of `ofCoeff f _` are `f`.** -/
@[simp] theorem coeff_ofCoeff (f : ℤ → 𝕜)
    (hf : Memℓp (fun k => FiberTrivialization.equiv (E := geomFiberZ 𝕜 ν) k (f k)) p) (k : ℤ) :
    coeff (ofCoeff f hf) k = f k :=
  FiberTrivialization.equiv_symm_apply_equiv _ _

/-- The round trip: an element is the `ofCoeff` of its own raw coefficients. -/
theorem ofCoeff_coeff (x : WeightedLp ℤ (geomFiberZ 𝕜 ν) p)
    (hx : Memℓp (fun k => FiberTrivialization.equiv (E := geomFiberZ 𝕜 ν) k (coeff x k)) p) :
    ofCoeff (coeff x) hx = x :=
  ext_coeff <| funext <| coeff_ofCoeff _ hx

end OfCoeff

end RadiiPolynomial.WeightedLp.Bilateral

end
