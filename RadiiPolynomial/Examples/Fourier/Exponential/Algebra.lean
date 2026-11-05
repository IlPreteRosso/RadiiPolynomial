import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.UniversalProperty
import RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Diagonal
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Scalar
import RadiiPolynomial.Analysis.Norm.Exponential

/-!
# The exponential Fourier family on `ℓ¹_ν`: PlasmaLean's slab equation

The equation `ψ'' + a (e^ψ − 1) = 0` (PlasmaLean's slab equation,
`exterior/tmp/external_repos/PlasmaLean/PlasmaLean/Design/ValidatedSlabEquilibrium.lean`,
Apache-2.0) with the `2π`-periodic ansatz `ψ = ∑ uₙ e^{int}` becomes the coefficient equation
`−n² uₙ + a ((e^u)ₙ − δₙ₀) = 0` on the registered algebra `X ν = lpOneAlg ℤ (geomFiberZ ℂ ν)`
(`ν ≥ 1`; the exponential is the Banach-algebra `NormedSpace.exp`). This file states the family,
parametric in `ν` and `a : ℂ`:

* the symbol `λ_k = 1/(1 + k²)` and the bounded diagonal `Λ = diagCLM λ 1`;
* the reflection `R ν = lpOneAlg.refl` (`(R x)_k = x_(−k)`; the weight `ν^|k|` is symmetric) and
  the even part `P_e = (1 + R)/2`;
* the symmetrized map `F̃(u) = −u + Λ(P_e u + a (e^(P_e u) − 1))` (PlasmaLean's `F(P_e u) − P_o u`)
  with its derivative `DF̃(u) = −1 + Λ (P_e + a e^(P_e u) P_e)` (Mathlib's `hasFDerivAt_exp`);
* the symmetries: a zero of `F̃` is even (`refl_of_Ftil_eq_zero`), and for real `a` the
  coefficient conjugation commutes with `F̃` (`Ftil_coeffConj`);
* the raw coefficient equation of an even zero (`coeff_equation_of_zero`).
-/

open scoped ComplexConjugate

noncomputable section

namespace FourierExponential.Family

open RadiiPolynomial lpOneAlg

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]

/-- The state space `ℓ¹_ν(ℤ; ℂ)`, the registered algebra. -/
abbrev X := lpOneAlg ℤ (geomFiberZ ℂ ν)

/-! ### A. The symbol and the diagonal `Λ` -/

/-- The symbol `λ_k = 1/(1 + k²)`. -/
def lam (k : ℤ) : ℂ := 1 / (1 + (k : ℂ) ^ 2)

theorem lam_eq_ofReal (k : ℤ) : lam k = ((1 / (1 + (k : ℝ) ^ 2) : ℝ) : ℂ) := by
  rw [lam]; push_cast; rfl

theorem norm_lam_le (k : ℤ) : ‖lam k‖ ≤ 1 := by
  rw [lam_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity), div_le_one (by positivity)]
  nlinarith [sq_nonneg (k : ℝ)]

theorem lam_neg (k : ℤ) : lam (-k) = lam k := by simp [lam]

theorem conj_lam (k : ℤ) : conj (lam k) = lam k := by
  rw [lam_eq_ofReal, Complex.conj_ofReal]

/-- `λ_n (1 + n²) = 1`. -/
theorem lam_mul (n : ℤ) : lam n * (1 + (n : ℂ) ^ 2) = 1 := by
  have h : (1 + (n : ℂ) ^ 2) ≠ 0 := by
    rw [show (1 + (n : ℂ) ^ 2) = ((1 + (n : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.ofReal_ne_zero.2 (by positivity)
  rw [lam]; field_simp

/-- **`Λ = diag(1/(1+k²))`**, the library bounded diagonal. -/
def Lam : X ν →L[ℂ] X ν := diagCLM lam 1 norm_lam_le

theorem toRealSeq_Lam (x : X ν) (k : ℤ) : toRealSeq (Lam ν x) k = lam k * toRealSeq x k :=
  toRealSeq_diagCLM lam 1 norm_lam_le x k

theorem Lam_single (j : ℤ) (c : ℂ) : Lam ν (single j c) = single j (lam j * c) :=
  diagCLM_single lam 1 norm_lam_le j c

/-! ### B. The reflection and the even part -/

omit [Fact (1 ≤ (ν : ℝ))] in
/-- The weight `ν^|k|` is symmetric. -/
theorem weight_neg_le (m : ℤ) :
    FiberTrivialization.weight (E := geomFiberZ ℂ ν) (-m) ≤
      FiberTrivialization.weight (E := geomFiberZ ℂ ν) m := by
  rw [geomFiberZ_weight, geomFiberZ_weight]
  exact (geomFiberZ_weight_neg ν m).le

/-- The reflection `(R x)_k = x_(−k)` of `ℓ¹_ν`. -/
abbrev R : X ν →A[ℂ] X ν := lpOneAlg.refl (weight_neg_le ν)

/-- The even part `P_e = (1 + R)/2`. -/
def Pe : X ν →L[ℂ] X ν := (1 / 2 : ℂ) • (1 + (R ν).toContinuousLinearMap)

theorem Pe_apply (x : X ν) : Pe ν x = (1 / 2 : ℂ) • (x + R ν x) := rfl

theorem norm_Pe_le (x : X ν) : ‖Pe ν x‖ ≤ ‖x‖ := by
  rw [Pe_apply, norm_smul]
  have h : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h]
  have := (norm_add_le x (R ν x)).trans (add_le_add le_rfl (norm_refl_le _ x))
  linarith

theorem refl_Pe (x : X ν) : R ν (Pe ν x) = Pe ν x := by
  rw [Pe_apply, map_smul, map_add, refl_refl, add_comm]

theorem Pe_single (m : ℤ) :
    Pe ν (single m 1) = (1 / 2 : ℂ) • (single m 1 + single (-m) 1 : X ν) := by
  rw [Pe_apply, refl_single]

theorem Pe_of_refl {u : X ν} (h : R ν u = u) : Pe ν u = u := by
  rw [Pe_apply, h, ← two_smul ℂ u, smul_smul]; norm_num

theorem refl_Lam (x : X ν) : R ν (Lam ν x) = Lam ν (R ν x) :=
  ext_toRealSeq (funext fun k => by
    rw [toRealSeq_refl, toRealSeq_Lam, toRealSeq_Lam, toRealSeq_refl, lam_neg])

/-! ### C. The conjugation commutes with `Λ` and `P_e` -/

theorem coeffConj_Lam (x : X ν) : coeffConj (Lam ν x) = Lam ν (coeffConj x) :=
  ext_toRealSeq (funext fun k => by
    rw [toRealSeq_coeffConj, toRealSeq_Lam, toRealSeq_Lam, map_mul, toRealSeq_coeffConj,
      conj_lam])

theorem coeffConj_Pe (x : X ν) : coeffConj (Pe ν x) = Pe ν (coeffConj x) := by
  rw [Pe_apply, Pe_apply, map_smulₛₗ, map_add, coeffConj_refl]
  congr 1
  rw [map_div₀, map_one, map_ofNat]

/-! ### D. The map `F̃`, its derivative, its symmetries -/

variable (a : ℂ)

/-- **The symmetrized zero-finding map** `F̃(u) = −u + Λ(P_e u + a (e^(P_e u) − 1))`. -/
def Ftil (u : X ν) : X ν := -u + Lam ν (Pe ν u + a • (NormedSpace.exp (Pe ν u) - 1))

/-- The derivative `DF̃(u) = −1 + Λ (P_e + a e^(P_e u) P_e)`. -/
def DFtil (u : X ν) : X ν →L[ℂ] X ν :=
  -1 + Lam ν ∘L (Pe ν + a • (mulLeftCLM (𝕜 := ℂ) (NormedSpace.exp (Pe ν u)) ∘L Pe ν))

theorem DFtil_apply (u h : X ν) :
    DFtil ν a u h = -h + Lam ν (Pe ν h + a • (NormedSpace.exp (Pe ν u) * Pe ν h)) := rfl

/-- **The derivative of `F̃`** from Mathlib's `hasFDerivAt_exp` on the registered algebra. -/
theorem hasFDerivAt_Ftil (u : X ν) : HasFDerivAt (Ftil ν a) (DFtil ν a u) u := by
  have hexp : HasFDerivAt (fun v : X ν => NormedSpace.exp (Pe ν v))
      ((NormedSpace.exp (Pe ν u) • (1 : X ν →L[ℂ] X ν)).comp (Pe ν)) u :=
    (hasFDerivAt_exp (𝕂 := ℂ)).comp u (Pe ν).hasFDerivAt
  have h1 := (Pe ν).hasFDerivAt.add ((hexp.sub_const 1).const_smul a)
  have h2 := ((Lam ν).hasFDerivAt (x := Pe ν u + a • (NormedSpace.exp (Pe ν u) - 1))).comp u h1
  have h3 := (hasFDerivAt_id u).neg.add h2
  refine h3.congr_fderiv ?_
  ext1 h
  simp only [DFtil, add_apply, neg_apply, ContinuousLinearMap.id_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply, smul_apply, mulLeftCLM_apply]
  rfl

/-- **A zero of `F̃` is even** (PlasmaLean's `Ftil_zero`): `u = Λ(P_e u + a (e^(P_e u) − 1))`,
and the right side is fixed by the reflection. -/
theorem refl_of_Ftil_eq_zero {u : X ν} (h : Ftil ν a u = 0) : R ν u = u := by
  have hu : u = Lam ν (Pe ν u + a • (NormedSpace.exp (Pe ν u) - 1)) := by
    rw [Ftil, neg_add_eq_zero] at h; exact h
  rw [hu, refl_Lam, map_add, map_smul, map_sub, map_one,
    NormHelpers.map_exp_of_continuous (R ν) (R ν).continuous, refl_Pe]

/-- **For real `a` the conjugation commutes with `F̃`.** -/
theorem Ftil_coeffConj (ha : conj a = a) (u : X ν) :
    Ftil ν a (coeffConj u) = coeffConj (Ftil ν a u) := by
  have h1 : coeffConj (1 : X ν) = 1 := map_one (coeffConjRingHom (𝕜 := ℂ) (E := geomFiberZ ℂ ν))
  have hexp : ∀ x : X ν, coeffConj (NormedSpace.exp x) = NormedSpace.exp (coeffConj x) :=
    NormHelpers.map_exp_of_continuous (coeffConjRingHom (𝕜 := ℂ) (E := geomFiberZ ℂ ν))
      coeffConj.continuous
  simp only [Ftil, map_add, map_neg, map_sub, map_smulₛₗ, RingHom.id_apply, coeffConj_Lam,
    hexp, h1, coeffConj_Pe, ha]

/-- **The raw coefficient equation** of an even zero: `F̃(u) = 0` and `R u = u` give
`−n² uₙ + a ((e^u)ₙ − δₙ₀) = 0`. -/
theorem coeff_equation_of_zero {u : X ν} (hF : Ftil ν a u = 0) (hR : R ν u = u) (n : ℤ) :
    -(n : ℂ) ^ 2 * toRealSeq u n +
      a * (toRealSeq (NormedSpace.exp u) n - if n = 0 then 1 else 0) = 0 := by
  rw [Ftil, Pe_of_refl ν hR] at hF
  have hk := congrArg (fun x : X ν => toRealSeq x n) hF
  simp only [toRealSeq_add, toRealSeq_neg, toRealSeq_Lam, toRealSeq_smul, toRealSeq_sub,
    Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    toRealSeq_zero, Pi.zero_apply, one_eq_single_zero, toRealSeq_single] at hk
  have hl := lam_mul n
  linear_combination (1 + (n : ℂ) ^ 2) * hk -
    (toRealSeq u n + a * (toRealSeq (NormedSpace.exp u) n - if n = 0 then 1 else 0)) * hl

end FourierExponential.Family

end
