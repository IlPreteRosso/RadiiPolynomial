import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.FiberTrivialization
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.MeanInequalities

/-!
# The weighted ℓᵖ carrier `WeightedLp M E p`

`WeightedLp M E p` is Mathlib's `lp E p`: the families `x m ∈ E m` with
`(∑' m, ‖x m‖ ^ p)^(1/p) < ∞` (`sup` for `p = ∞`), normed by that quantity. It is an `abbrev`,
not a wrapper: every frame-free face (normed group for `1 ≤ p`, completeness, the `𝕜`-module and
normed-space structure, `lp.single`, `lp.norm_apply_le_norm`) is Mathlib's, reached through small
bridge lemmas. No multiplication is selected by this carrier module.

## Design of record: the physical weight is a parameter

The weight is not a field of the carrier. It is the derived weight `ω_m = ‖θ_m 1‖` of a chosen
frame `[FiberTrivialization 𝕜 M E]` (`WeightedL1/FiberTrivialization.lean`); the standard model
`WeightedScalar 𝕜 w` has `ω = w`. The carrier itself is frame-free; the frame enters only through
the scalar coordinates and the scalar atoms of this file:

* `coeff x m = θ_m⁻¹ (x m)`, with the norm law `norm_apply_eq : ‖x m‖ = ‖coeff x m‖ * ω_m`, its
  additive and scalar faces, and extensionality `ext_coeff`;
* `coeffCLM m : WeightedLp M E p →L[𝕜] 𝕜`, with the pointwise estimate `norm_coeff_le` over any
  normed field and the operator-norm face `norm_coeffCLM_le : ‖coeffCLM m‖ ≤ ω_m⁻¹` over a
  nontrivially normed field;
* the scalar atom `single m r = lp.single p m (θ_m r)`, with `coeff_single` and
  `norm_single : ‖single m r‖ = ‖r‖ * ω_m`.

## Finite synthesis

Finite-p atom-span density (`dense_span_single`) and the bounded extension of finite atom sums
(`liftCLM`, `liftBound_iff`) are in `Operators/LiftBound.lean`.
-/

open scoped ENNReal NNReal Topology
open Filter

noncomputable section

namespace RadiiPolynomial

/-- The weighted ℓᵖ carrier: (the type of) Mathlib's `lp E p` on the fibre family
`E : M → Type*`. The weight is the derived weight of a chosen `FiberTrivialization` of `E`, never
a field of the carrier. The `abbrev` is type-valued, so every `lp` instance applies and dot
notation `x.coeff` resolves in this namespace. -/
abbrev WeightedLp (M : Type*) (E : M → Type*) [∀ m, NormedAddCommGroup (E m)] (p : ℝ≥0∞) :
    Type _ :=
  lp E p

namespace WeightedLp

/-! ### Frame-free faces -/

section FrameFree

variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exponent of a normed carrier is nonzero. -/
theorem exponent_ne_zero : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'

/-- A finite exponent of a normed carrier has positive real value. -/
theorem exponent_toReal_pos {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ∞) : 0 < q.toReal :=
  ENNReal.toReal_pos exponent_ne_zero hq

/-- Every fibre value is bounded by the norm: `‖x m‖ ≤ ‖x‖`. -/
theorem norm_apply_le_norm (x : WeightedLp M E p) (m : M) : ‖x m‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm exponent_ne_zero x m

end FrameFree

/-! ### Scalar coordinates through the chosen frame -/

section Coordinates

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞}

/-- The scalar coordinates in the chosen frame: `coeff x m = θ_m⁻¹ (x m)`. -/
def coeff (x : WeightedLp M E p) (m : M) : 𝕜 := (FiberTrivialization.equiv (E := E) m).symm (x m)

theorem coeff_apply (x : WeightedLp M E p) (m : M) :
    coeff x m = (FiberTrivialization.equiv (E := E) m).symm (x m) := rfl

/-- The frame recovers the fibre value from its coordinate: `θ_m (coeff x m) = x m`. -/
@[simp] theorem equiv_coeff (x : WeightedLp M E p) (m : M) :
    FiberTrivialization.equiv (E := E) m (coeff x m) = x m :=
  LinearEquiv.apply_symm_apply _ _

/-- The norm law `‖x m‖ = ‖θ_m⁻¹ x_m‖ ω_m`. -/
theorem norm_apply_eq (x : WeightedLp M E p) (m : M) :
    ‖x m‖ = ‖coeff x m‖ * FiberTrivialization.weight (E := E) m := by
  rw [← FiberTrivialization.norm_equiv_apply, equiv_coeff]

/-- `‖coeff x m‖ = ‖x m‖ / ω_m`. -/
theorem norm_coeff (x : WeightedLp M E p) (m : M) :
    ‖coeff x m‖ = ‖x m‖ / FiberTrivialization.weight (E := E) m :=
  FiberTrivialization.norm_equiv_symm_apply m (x m)

@[simp] theorem coeff_zero : coeff (0 : WeightedLp M E p) = 0 :=
  funext fun m => map_zero (FiberTrivialization.equiv (E := E) m).symm

@[simp] theorem coeff_add (x y : WeightedLp M E p) : coeff (x + y) = coeff x + coeff y :=
  funext fun m => map_add (FiberTrivialization.equiv (E := E) m).symm (x m) (y m)


@[simp] theorem coeff_sub (x y : WeightedLp M E p) : coeff (x - y) = coeff x - coeff y :=
  funext fun m => map_sub (FiberTrivialization.equiv (E := E) m).symm (x m) (y m)

/-- The coordinates are `𝕜`-linear for Mathlib's fibrewise action (`map_smul` of `θ_m⁻¹`). -/
@[simp] theorem coeff_smul (c : 𝕜) (x : WeightedLp M E p) : coeff (c • x) = c • coeff x :=
  funext fun m => map_smul (FiberTrivialization.equiv (E := E) m).symm c (x m)

/-- Extensionality through the coordinates of the chosen frame. -/
theorem ext_coeff {x y : WeightedLp M E p} (h : coeff x = coeff y) : x = y :=
  lp.ext <| funext fun m => by rw [← equiv_coeff x m, ← equiv_coeff y m, congr_fun h m]


/-! ### Scalar atoms -/

section Single

variable [DecidableEq M]

/-- The scalar atom with coordinate `r` at `m` and `0` elsewhere: `single m r = lp.single p m (θ_m r)`. -/
def single (m : M) (r : 𝕜) : WeightedLp M E p :=
  lp.single p m (FiberTrivialization.equiv (E := E) m r)

theorem coeFn_single (m : M) (r : 𝕜) :
    ⇑(single (E := E) (p := p) m r) = Pi.single m (FiberTrivialization.equiv (E := E) m r) := rfl

/-- The coordinates of a scalar atom: `coeff (single m r) = Pi.single m r`. -/
theorem coeff_single (m : M) (r : 𝕜) :
    coeff (single (E := E) (p := p) m r) = Pi.single m r := by
  funext k
  rw [coeff_apply, coeFn_single,
    Pi.apply_single (fun k => (FiberTrivialization.equiv (E := E) k).symm) (fun _ => map_zero _),
    LinearEquiv.symm_apply_apply]

@[simp] theorem coeff_single_self (m : M) (r : 𝕜) :
    coeff (single (E := E) (p := p) m r) m = r := by
  rw [coeff_single, Pi.single_eq_same]

/-- A scalar atom with a nonzero coordinate is nonzero: `r ≠ 0 → single m r ≠ 0`. -/
theorem single_ne_zero {m : M} {r : 𝕜} (hr : r ≠ 0) : (single m r : WeightedLp M E p) ≠ 0 :=
  fun h => hr <| by rw [← coeff_single_self (E := E) (p := p) m r, h, coeff_zero, Pi.zero_apply]


/-- `single m r = r • single m 1`. -/
theorem single_eq_smul (m : M) (r : 𝕜) :
    single (E := E) (p := p) m r = r • single m 1 := by
  rw [single, single, ← lp.single_smul, ← map_smul, smul_eq_mul, mul_one]

end Single

end Coordinates

/-! ### Real multiples on a complex carrier -/

section RealScalar

variable {M : Type*} {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace ℂ (E m)]
  [FiberTrivialization ℂ M E] {p : ℝ≥0∞}

/-- Coordinates of a real multiple on a complex carrier: `(r • x)ₙ = r xₙ`. -/
theorem coeff_real_smul (r : ℝ) (x : WeightedLp M E p) (n : M) :
    coeff (r • x) n = (r : ℂ) * coeff x n := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal, coeff_smul,
    Pi.smul_apply, smul_eq_mul]

end RealScalar

/-! ### Coordinates of finite sums (at arbitrary exponents) -/

section FiniteSums

variable {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {E : J → Type*}
  [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)] [FiberTrivialization 𝕜 J E]
  {p : ℝ≥0∞}

/-- The coordinates of a finite sum are the finite sums of the coordinates. -/
theorem coeff_sum {ι : Type*} (s : Finset ι) (f : ι → WeightedLp J E p) (j : J) :
    coeff (∑ k ∈ s, f k) j = ∑ k ∈ s, coeff (f k) j := by
  rw [coeff_apply, lp.coeFn_sum, Finset.sum_apply, map_sum]
  rfl

variable [DecidableEq J]

/-- The coordinates of a finite sum of scalar atoms. -/
theorem coeff_sum_single (s : Finset J) (c : J → 𝕜) (i : J) :
    coeff (∑ j ∈ s, single (E := E) (p := p) j (c j)) i = if i ∈ s then c i else 0 := by
  simp only [coeff_sum, coeff_single, Finset.sum_pi_single]

end FiniteSums

/-! ### The coordinate functionals and the norm of an atom (`1 ≤ p`) -/

section Normed

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The pointwise coordinate estimate `‖coeff x m‖ ≤ ω_m⁻¹ ‖x‖`. -/
theorem norm_coeff_le (x : WeightedLp M E p) (m : M) :
    ‖coeff x m‖ ≤ (FiberTrivialization.weight (E := E) m)⁻¹ * ‖x‖ := by
  rw [norm_coeff, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_apply_le_norm x m)
    (inv_nonneg.2 (FiberTrivialization.weight_nonneg m))

/-- The coordinate at `m` as a continuous `𝕜`-linear functional, with constant `ω_m⁻¹`. -/
def coeffCLM (m : M) : WeightedLp M E p →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun x => coeff x m
      map_add' := fun x y => congr_fun (coeff_add x y) m
      map_smul' := fun c x => congr_fun (coeff_smul c x) m }
    (FiberTrivialization.weight (E := E) m)⁻¹ fun x => norm_coeff_le x m

@[simp] theorem coeffCLM_apply (m : M) (x : WeightedLp M E p) :
    coeffCLM (E := E) (p := p) m x = coeff x m := rfl

/-- The norm of a scalar atom: `‖single m r‖ = ‖r‖ * ω_m`. -/
theorem norm_single [DecidableEq M] (m : M) (r : 𝕜) :
    ‖single (E := E) (p := p) m r‖ = ‖r‖ * FiberTrivialization.weight (E := E) m := by
  rw [single, lp.norm_single (zero_lt_one.trans_le Fact.out),
    FiberTrivialization.norm_equiv_apply]

end Normed

section OpNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The operator-norm face of the coordinate functional: `‖coeffCLM m‖ ≤ ω_m⁻¹`. -/
theorem norm_coeffCLM_le (m : M) :
    ‖coeffCLM (E := E) (p := p) m‖ ≤ (FiberTrivialization.weight (E := E) m)⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (inv_nonneg.2 (FiberTrivialization.weight_nonneg m)) _

end OpNorm

section Summability

/-- The quantitative coordinate estimate at exponent `2`: for a real majorant `v` with
`∑ (v m / ω_m) ^ 2 < ∞`, every `x : WeightedLp M E 2` has `Summable fun m => ‖coeff x m‖ * v m`
and `∑' m, ‖coeff x m‖ * v m ≤ √(∑' m, (v m / ω_m) ^ 2) * ‖x‖`. The proof applies Mathlib's Hölder
inequality `Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg` in frame coordinates to the
absolute majorant `|v|`, which has the same squared ratios, and compares termwise. No sign
condition on `v` is needed; only the frame weight `ω` enters. -/
theorem summable_norm_coeff_mul_and_tsum_le {𝕜 : Type*} [NormedField 𝕜] {M : Type*}
    {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [FiberTrivialization 𝕜 M E] (v : M → ℝ)
    (hvw : Summable fun m => (v m / FiberTrivialization.weight (E := E) m) ^ 2)
    (x : WeightedLp M E 2) :
    Summable (fun m => ‖coeff x m‖ * v m) ∧
    (∑' m, ‖coeff x m‖ * v m) ≤
      Real.sqrt (∑' m, (v m / FiberTrivialization.weight (E := E) m) ^ 2) * ‖x‖ := by
  have hsq : ∀ m, (|v m| / FiberTrivialization.weight (E := E) m) ^ 2 =
      (v m / FiberTrivialization.weight (E := E) m) ^ 2 := fun m => by
    rw [div_pow, div_pow, sq_abs]
  have habs : Summable (fun m => ‖coeff x m‖ * |v m|) ∧
      (∑' m, ‖coeff x m‖ * |v m|) ≤
        Real.sqrt (∑' m, (|v m| / FiberTrivialization.weight (E := E) m) ^ 2) * ‖x‖ := by
    have hg : ∀ m, 0 ≤ |v m| / FiberTrivialization.weight (E := E) m :=
      fun m => div_nonneg (abs_nonneg _) (FiberTrivialization.weight_nonneg m)
    have hf2 : Summable fun m => ‖x m‖ ^ (2 : ℝ) := by
      simpa only [ENNReal.toReal_ofNat] using
        (lp.memℓp x).summable (p := 2) (by norm_num)
    have hg2 : Summable fun m =>
        (|v m| / FiberTrivialization.weight (E := E) m) ^ (2 : ℝ) :=
      (hvw.congr fun m => (hsq m).symm).congr fun m => (Real.rpow_two _).symm
    obtain ⟨hs, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
      Real.HolderConjugate.two_two (fun m => norm_nonneg (x m)) hg hf2 hg2
    have hx : ‖x‖ = (∑' m, ‖x m‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
      simpa only [ENNReal.toReal_ofNat] using
        lp.norm_eq_tsum_rpow (p := 2) (by norm_num) x
    have hc : Real.sqrt (∑' m,
        (|v m| / FiberTrivialization.weight (E := E) m) ^ 2) =
        (∑' m, (|v m| / FiberTrivialization.weight (E := E) m) ^ (2 : ℝ)) ^
          (1 / (2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      exact congrArg (· ^ (1 / (2 : ℝ)))
        (tsum_congr fun m => (Real.rpow_two _).symm)
    have he : (fun m => ‖coeff x m‖ * |v m|) =
        fun m => ‖x m‖ * (|v m| / FiberTrivialization.weight (E := E) m) := by
      funext m
      rw [norm_coeff]
      ring
    refine ⟨he ▸ hs, ?_⟩
    rw [he, hx, hc, mul_comm]
    exact hle
  simp only [hsq] at habs
  have hs : Summable (fun m => ‖coeff x m‖ * v m) :=
    Summable.of_norm (habs.1.congr fun m => by
      rw [Real.norm_eq_abs, abs_mul, abs_norm])
  refine ⟨hs, (Summable.tsum_le_tsum (fun m => ?_) hs habs.1).trans habs.2⟩
  exact mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _)

/-- If `∑ (weight n)⁻¹ ^ 2 < ∞`, then every `x : WeightedLp M E 2` has
`Summable fun n => ‖WeightedLp.coeff x n‖`. -/
theorem summable_norm_coeff_of_summable_inv_sq {𝕜 : Type*} [NormedField 𝕜] {M : Type*}
    {E : M → Type*} [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)]
    [FiberTrivialization 𝕜 M E]
    (hw : Summable fun n => (FiberTrivialization.weight (E := E) n)⁻¹ ^ 2)
    (x : WeightedLp M E 2) : Summable fun n => ‖WeightedLp.coeff x n‖ := by
  have h := (summable_norm_coeff_mul_and_tsum_le (fun _ => 1)
    (by simpa only [one_div] using hw) x).1
  simpa only [mul_one] using h

end Summability

end WeightedLp

end RadiiPolynomial

