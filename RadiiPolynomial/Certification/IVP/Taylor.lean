import RadiiPolynomial.Applications.IVP.Taylor
import RadiiPolynomial.Certification.Rational.Matrix
import RadiiPolynomial.Certification.Rational.Grid
import RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega
import RadiiPolynomial.Certification.Witness
import RadiiPolynomial.Certification.RadiiPolynomialQ
import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Compatibility.TaylorTailL1

/-!
# Taylor certification adapter

Exact rational clauses for `IVP.StdIVPData` and a `CompPoly` vector field, with soundness
at each real realization. This module imports the Taylor discretization and certification
evaluators; no reusable module below `Certification` imports it.

Retained computations include `abarNormQ`, `DLipBoundQ`, `activeQ`, `evalArr`,
`kerColMaxQ` and `supportM`. The kernel-column bound is assembled by
`StdIVPData.Z₁_le_of_pairBound` and `Z₁_le_ker_of_Q`; `Z₂_le_of_Q` uses
`activeBlockNormQ` at scale `ν_q · DLipBoundQ`.

`IVP.StdIVPDataQ` packages the stored rational data, `ofStd` extracts those rational data
from a realized bundle, and `toStdIVPData` realizes them at a specified weight. `ChecksZ₀`,
`ChecksZ₀By`, `ChecksZ₁ker`, `ChecksDF` and `ChecksZ₂` have their soundness bridges here.
The shared rational block action and cast bridge are owned by `Rational.Matrix`.
The older exact-derivative and alternate column wrappers are not this shipped surface.
-/

open scoped BigOperators Topology
open RadiiPolynomial MvPolyBridge RadiiPolynomial.Certification.Rational
open RadiiPolynomial.WeightedLp
open Finset

namespace IVP

/-! ## Computable ℚ quantities of the stored data and the syntax -/

section TaylorQ

variable {ν : PosReal} {L N : ℕ} [NeZero L]

/-- Exact ℚ weighted norm of the stored approximate solution, per component. -/
def abarNormQ (N : ℕ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ) (i : Fin L) : ℚ :=
  ∑ k ∈ Finset.Icc 0 N, |(abar_Q i).getD k 0| * ν_q ^ k



/-- Syntactic derivative-Lipschitz constant `max_l derivativeLipschitzBound (f_l) S` at the
radii `S`. -/
def DLipBoundQ (f_cpoly : Fin L → CompPoly L) (S : Fin L → ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun l => (f_cpoly l).derivativeLipschitzBound S

/-- Components with a nonzero syntactic derivative-Lipschitz constant at the radii `S`
(computed from the syntax). A component outside the set has syntactic constant `0` at every
nonnegative radii below `S` (monotonicity; used in `StdIVPData.Z₂_le_of_Q`); a component inside
it need not have a moving derivative, since the syntax can contain cancelling terms. -/
def activeQ (f_cpoly : Fin L → CompPoly L) (S : Fin L → ℚ) : Finset (Fin L) :=
  Finset.univ.filter fun l => (f_cpoly l).derivativeLipschitzBound S ≠ 0

/-- Coefficient array of `p` evaluated at `ā` over its syntactic support window. -/
def evalArr (N : ℕ) (abar_Q : Fin L → Array ℚ) (p : CompPoly L) : Array ℚ :=
  Array.mk ((List.range (CompPoly.supportBound N p + 1)).map fun k => p.evalCoeff abar_Q k)

/-- The rational head-column maximum of the tail kernel of `p(ā)`: `colMax q N d` with
`q k = |p(ā)_k| ν_q^(k+1)` and `d = CompPoly.supportBound N p`. -/
def kerColMaxQ (N : ℕ) (abar_Q : Fin L → Array ℚ) (ν_q : ℚ) (p : CompPoly L) : ℚ :=
  colMax (fun k => |(evalArr N abar_Q p).getD k 0| * ν_q ^ (k + 1)) N (CompPoly.supportBound N p)


/-- Support index of `F(ā)`: past `N` and past the syntactic support of every component. -/
def supportM (f_cpoly : Fin L → CompPoly L) (N : ℕ) : ℕ :=
  max N (Finset.univ.sup fun l => CompPoly.supportBound N (f_cpoly l)) + 1



/-! ### Column `Z₁` helpers

The tail operator of `Z₁` at component `l` is `h ↦ π_{>N} shiftDivN (Σ_m b_{lm} · h_m)` with
`b_{lm} = ∂_m f_l(ā)`. Per pair `(l, m)` the exact weighted column sup of
`π_{>N} ∘ shiftDivN ∘ leftMul b_{lm}` is the finite ℚ maximum `colSupQ` over `M ≤ N`
(columns above `N` are antitone, `shiftDivN_leftMul_tail_cols_le_of_Q`). Since `‖h‖` is the
sup over components, the operator bound is `Σ_m colSupQ_{lm}`; the per-`M` sum
`sup_M Σ_m` would NOT be sound for `L > 1` (different components can peak at different `M`).
For `L = 1` the two coincide. -/

omit [NeZero L] in
/-- `evalArr N abar_Q p` vanishes past the syntactic support window `CompPoly.supportBound N p`. -/
theorem evalArr_getD_eq_zero (p : CompPoly L) (abar_Q : Fin L → Array ℚ) (k : ℕ)
    (hk : CompPoly.supportBound N p < k) : (evalArr N abar_Q p).getD k 0 = 0 := by
  simp [evalArr, Array.getD, show ¬ k < CompPoly.supportBound N p + 1 by omega]

end TaylorQ

/-! ## Bound faces on a bundle -/

namespace StdIVPData

variable {ν : PosReal} {L N : ℕ} [NeZero L]

/-- The stored rational weight of a bundle is positive (it casts to `ν > 0`). -/
theorem ν_q_pos (d : IVP.StdIVPData ν L N) : 0 < d.ν_q := by
  have h : (0 : ℝ) < (d.ν_q : ℝ) := d.hν ▸ ν.2
  exact_mod_cast h

/-- The stored approximate solution has no coefficients past `N`: `(abar_Q i)[k] = 0` for
`N < k` (from the array size `N + 1`). -/
theorem abar_Q_getD_eq_zero (d : IVP.StdIVPData ν L N) (i : Fin L) (k : ℕ) (hk : N < k) :
    (d.abar_Q i).getD k 0 = 0 := by
  simp [Array.getD, show ¬ k < (d.abar_Q i).size by rw [d.habar_size i]; omega]

/-- The rational weighted norm `abarNormQ` of each stored component is nonnegative. -/
theorem abarNormQ_nonneg (d : IVP.StdIVPData ν L N) (i : Fin L) :
    0 ≤ abarNormQ N d.abar_Q d.ν_q i :=
  Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (pow_nonneg (ν_q_pos d).le k)

/-- The weighted ℓ¹ norm of the realized component `ā_i` equals the cast of its exact
rational norm `abarNormQ`. -/
theorem norm_abar_eq (d : IVP.StdIVPData ν L N) (i : Fin L) :
    ‖d.abar i‖ = (abarNormQ N d.abar_Q d.ν_q i : ℝ) :=
  l1Weighted.norm_eq_ratCast_sum_of_support _ _ _ (d.abar_toSeq_eq i) d.hν N
    (abar_Q_getD_eq_zero d i)

/-- `Z₂` from one exact-ℚ check of `activeBlockNormQ` at the computed scale
`C_q = ν_q · DLipBoundQ`: the derivative-Lipschitz constant of the polynomial field and its
active components are computed from the syntax at the radii `‖ā_i‖ + r₀`, so every degree is
covered and no constant is supplied by the caller. -/
theorem Z₂_le_of_Q (d : IVP.StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L)
    (x₀ : Fin L → ℝ) {r₀ : ℚ} (hr₀ : 0 ≤ r₀) {Z₂ : ℚ}
    (hle : activeBlockNormQ L N (fun l j k => d.A_col l j (k : ℕ)) d.ν_q
      (IVP.StdIVPData.approxInverse_tailBound_q (N := N))
      (d.ν_q * DLipBoundQ f_cpoly (fun i => abarNormQ N d.abar_Q d.ν_q i + r₀))
      (activeQ f_cpoly (fun i => abarNormQ N d.abar_Q d.ν_q i + r₀)) ≤ Z₂) :
    ∀ c ∈ Metric.closedBall (d.abar : XL1 ν L) (r₀ : ℝ),
      Z₂_norm (d.G (IVP.banachField f_cpoly) x₀) d.abar
        (ContinuousLinearMap.id ℝ (XL1 ν L)) c ≤ (Z₂ : ℝ) * (r₀ : ℝ) := by
  set S : Fin L → ℚ := fun i => abarNormQ N d.abar_Q d.ν_q i + r₀
  have hS0 : ∀ i, (0 : ℚ) ≤ S i := fun i => add_nonneg (abarNormQ_nonneg d i) hr₀
  have hmax : ∀ c ∈ Metric.closedBall (d.abar : XL1 ν L) (r₀ : ℝ), ∀ i,
      max ‖c i‖ ‖d.abar i‖ ≤ ((S i : ℚ) : ℝ) := fun c hc i => by
    have hd : ‖c - d.abar‖ ≤ (r₀ : ℝ) := by rw [← dist_eq_norm]; exact hc
    have hci : ‖c i - d.abar i‖ ≤ ‖c - d.abar‖ := norm_le_pi_norm (c - d.abar) i
    have hr : (0 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
    have ha := norm_abar_eq d i
    simp only [S]; push_cast
    refine max_le ?_ (by linarith)
    have := norm_le_insert' (c i) (d.abar i)
    linarith [norm_sub_norm_le (c i) (d.abar i)]
  have hmono : ∀ c ∈ Metric.closedBall (d.abar : XL1 ν L) (r₀ : ℝ), ∀ l,
      (f_cpoly l).derivativeLipschitzBound (fun i => max ‖c i‖ ‖d.abar i‖) ≤
        (((f_cpoly l).derivativeLipschitzBound S : ℚ) : ℝ) := fun c hc l => by
    rw [CompPoly.derivativeLipschitzBound_ratCast]
    exact CompPoly.derivativeLipschitzBound_mono _ (fun i => le_max_of_le_left (norm_nonneg _))
      (hmax c hc)
  have hBnn : 0 ≤ DLipBoundQ f_cpoly S :=
    (CompPoly.derivativeLipschitzBound_nonneg (f_cpoly 0) S hS0).trans
      (Finset.le_sup' (fun l => (f_cpoly l).derivativeLipschitzBound S) (Finset.mem_univ 0))
  refine d.Z₂_le_of_compPoly f_cpoly x₀ (activeQ f_cpoly S)
    (B := (DLipBoundQ f_cpoly S : ℝ))
    (fun l => ?_) (by exact_mod_cast hr₀) ?_ ?_
  · have h := activeBlockNorm_component_le d.approxInverse
      (fun l j k => d.A_col l j (k : ℕ)) d.ν_q _ _ (activeQ f_cpoly S)
      (fun l j k i => d.A_finBlock_eq l j i k) d.hν d.approxInverse_tailBound_eq
      (mul_nonneg (ν_q_pos d).le hBnn) hle l
    have e : ((DLipBoundQ f_cpoly S : ℚ) : ℝ) * (ν : ℝ) =
        ((d.ν_q * DLipBoundQ f_cpoly S : ℚ) : ℝ) := by
      rw [d.hν]; push_cast; ring
    rw [e]; exact h
  · intro j hj c hc
    have h0 : (f_cpoly j).derivativeLipschitzBound S = 0 := by
      simpa [activeQ] using hj
    refine le_antisymm ?_ (CompPoly.derivativeLipschitzBound_nonneg _ _
      (fun i => le_max_of_le_left (norm_nonneg _)))
    have := hmono c hc j
    rw [h0, Rat.cast_zero] at this
    exact this
  · intro c hc l
    refine (hmono c hc l).trans ?_
    exact_mod_cast Finset.le_sup' (fun l => (f_cpoly l).derivativeLipschitzBound S)
      (Finset.mem_univ l)

/-- The rational IVP coefficients at `ā` vanish past `supportM f_cpoly N`, the support index
read off the syntax. -/
theorem ivpCoeffsQ_support (d : IVP.StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L)
    (x₀_q : Fin L → ℚ) (l : Fin L) (n : ℕ) (hn : supportM f_cpoly N < n) :
    IVP.ivpCoeffsQ f_cpoly d.abar_Q x₀_q l n = 0 := by
  have hsb : CompPoly.supportBound N (f_cpoly l) ≤
      Finset.univ.sup fun l => CompPoly.supportBound N (f_cpoly l) :=
    Finset.le_sup (f := fun l => CompPoly.supportBound N (f_cpoly l)) (Finset.mem_univ l)
  unfold supportM at hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [IVP.ivpCoeffsQ]
  rw [abar_Q_getD_eq_zero d l (m + 1) (by omega), CompPoly.evalCoeff,
    CompPoly.evalCoeffSeq_eq_zero_of_support N (f_cpoly l) _
      (fun i k hk => abar_Q_getD_eq_zero d i k hk) m (by omega)]
  ring

/-- The real IVP coefficients `F(ā)` of a `CompPoly` field vanish past `supportM f_cpoly N`, for
every real initial value `x₀` (`x₀` enters `ivpCoeffs` only at `n = 0`, and `n > 0` here): the
rational bridge at zero initial data and `ivpCoeffsQ_support`. -/
theorem ivpCoeffs_abar_eq_zero_of_compPoly (d : IVP.StdIVPData ν L N)
    (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ) (l : Fin L) (n : ℕ)
    (hn : supportM f_cpoly N < n) :
    IVP.ivpCoeffs (fun a j => (f_cpoly j).evalBanach a) x₀ d.abar l n = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by unfold supportM at hn; omega⟩
  have h := d.ivpCoeffs_abar_eq_cast_of_compPoly f_cpoly 0 0 (fun _ => by simp) l (m + 1)
  rw [ivpCoeffsQ_support d f_cpoly 0 l (m + 1) hn, Rat.cast_zero] at h
  exact h





/-- Every entry of `evalArr N d.abar_Q p` (in or past the support window) is the exact
coefficient `p.evalCoeff d.abar_Q k`. -/
theorem evalArr_getD (d : IVP.StdIVPData ν L N) (p : CompPoly L) (k : ℕ) :
    (evalArr N d.abar_Q p).getD k 0 = p.evalCoeff d.abar_Q k := by
  by_cases hk : k < CompPoly.supportBound N p + 1
  · simp [evalArr, Array.getD, hk]
  · rw [CompPoly.evalCoeff, CompPoly.evalCoeffSeq_eq_zero_of_support N p _
      (fun i n hn => abar_Q_getD_eq_zero d i n hn) k (by omega)]
    simp [evalArr, Array.getD, hk]


/-- **Per-pair soundness through the kernel test**: the tail of `shiftDivN (p(ā) · x)` is at most
`kerColMaxQ p · ‖x‖`. -/
theorem tail_evalBanach_mul_le_ker (d : IVP.StdIVPData ν L N) (p : CompPoly L)
    (x : l1Weighted ν) :
    ∑' n, |l1Weighted.toSeq (shiftDivN (p.evalBanach d.abar * x)) (n + (N + 1))| *
        (ν : ℝ) ^ (n + (N + 1)) ≤ (kerColMaxQ N d.abar_Q d.ν_q p : ℝ) * ‖x‖ := by
  have hb : ∀ k, l1Weighted.toSeq (p.evalBanach d.abar) k =
      ((evalArr N d.abar_Q p).getD k 0 : ℝ) := fun k => by
    rw [p.toSeq_evalBanach d.abar d.abar_Q d.abar_toSeq_eq k, evalArr_getD d]
  refine tailTsum_shiftDivN_mul_le_of_check (d := CompPoly.supportBound N p) _
    (fun k hk => by rw [hb, evalArr_getD_eq_zero p d.abar_Q k hk, Rat.cast_zero])
    (fun k => |(evalArr N d.abar_Q p).getD k 0| * d.ν_q ^ (k + 1))
    (fun k _ => le_of_eq ?_) (fun j hj => le_sup' _ (mem_range.2 (Nat.lt_succ_of_le hj))) x
  rw [symbolMass, hb, Real.norm_eq_abs, d.hν]
  push_cast
  rfl

/-- The derivative of a `CompPoly` component at `ā`, as a sum of left multiplications. -/
theorem fderiv_banachField_apply (d : IVP.StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L)
    (h : XL1 ν L) (l : Fin L) :
    (fderiv ℝ (fun a => IVP.banachField f_cpoly a l) d.abar) h =
      ∑ m : Fin L, ((f_cpoly l).pderiv m).evalBanach d.abar * h m :=
  fderiv_banachField_apply' f_cpoly d.abar h l

omit [NeZero L] in
/-- A tail bound `tail (shiftDivN (b · x)) ≤ c · ‖x‖` for every `x` forces `0 ≤ c`: test it at
the atom `δ₀`, whose norm is its weight `ν⁰ > 0`. -/
private theorem pairBound_nonneg (b : l1Weighted ν) {c : ℝ}
    (hc : ∀ x : l1Weighted ν,
      ∑' n, |l1Weighted.toSeq (shiftDivN (b * x)) (n + (N + 1))| * (ν : ℝ) ^ (n + (N + 1)) ≤
        c * ‖x‖) : 0 ≤ c := by
  have hx : 0 < ‖(l1Weighted.single 0 1 : l1Weighted ν)‖ := by
    rw [l1Weighted.norm_single, abs_one, pow_zero, one_mul]
    exact one_pos
  exact nonneg_of_mul_nonneg_left
    ((tsum_nonneg fun n => mul_nonneg (abs_nonneg _) (pow_nonneg ν.2.le _)).trans (hc _)) hx

/-- **Generic-`L` `Z₁` face from per-pair tail bounds**: the finite Jacobian check `hDF`, per-pair
constants `c l m` with `tail (shiftDivN ((∂_m f_l)(ā) · x)) ≤ c l m · ‖x‖`, and one ℚ inequality
`Σ_m c l m ≤ Z₁` per component give the `Z₁` operator bound, through
`StdIVPData.Z₁_le_exact_of_compPoly`. The per-pair producers are `colSupQ`
(`tail_evalBanach_mul_le`) and `kerColMaxQ` (`tail_evalBanach_mul_le_ker`); the constants carry
no sign hypothesis. -/
theorem Z₁_le_of_pairBound (d : IVP.StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L)
    (x₀ : Fin L → ℝ)
    (hDF : ∀ (j m : Fin L) (row col : Fin (N + 1)),
      (d.DF_col j m (col : ℕ)).getD (row : ℕ) 0 =
        IVP.ivp_DF_of_Dφ_nat
          (fun j m k => ((f_cpoly j).pderiv m).evalCoeff d.abar_Q k)
          j m (row : ℕ) (col : ℕ))
    (c : Fin L → Fin L → ℚ)
    (hc : ∀ (l m : Fin L) (x : l1Weighted ν),
      ∑' n, |l1Weighted.toSeq (shiftDivN (((f_cpoly l).pderiv m).evalBanach d.abar * x))
          (n + (N + 1))| * (ν : ℝ) ^ (n + (N + 1)) ≤ (c l m : ℝ) * ‖x‖)
    {Z₁ : ℚ} (hle : ∀ l, ∑ m : Fin L, c l m ≤ Z₁) :
    Z₁_norm (d.G (IVP.banachField f_cpoly) x₀) d.abar (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((IVP.StdIVPData.composedApprox d).toCLM (ν := ν)) ≤ (Z₁ : ℝ) := by
  have hc0 : ∀ l m, (0 : ℝ) ≤ c l m := fun l m => pairBound_nonneg _ (hc l m)
  have hC : (0 : ℝ) ≤ (Z₁ : ℝ) :=
    (Finset.sum_nonneg fun m _ => hc0 0 m).trans (by exact_mod_cast hle 0)
  refine d.Z₁_le_exact_of_compPoly f_cpoly x₀
    (d.composedApprox_eq_fderiv_G_fin_of_compPoly f_cpoly x₀ hDF)
    (fun h l => (fderiv ℝ (fun a => IVP.banachField f_cpoly a l) d.abar) h)
    (fun _ _ => rfl) hC (fun h l => ?_) le_rfl
  rw [fderiv_banachField_apply d f_cpoly h l]
  refine (RadiiPolynomial.tail_shiftDivN_sum_le Finset.univ _).trans ?_
  refine (Finset.sum_le_sum fun m _ =>
    (hc l m (h m)).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm h m) (hc0 l m))).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact_mod_cast hle l


/-- **Column `Z₁` face through the kernel test (generic in `L`)**: the finite Jacobian check
`hDF` and one ℚ inequality `Σ_m kerColMaxQ (∂_m f_l) ≤ Z₁` per component. -/
theorem Z₁_le_ker_of_Q (d : IVP.StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L)
    (x₀ : Fin L → ℝ)
    (hDF : ∀ (j m : Fin L) (row col : Fin (N + 1)),
      (d.DF_col j m (col : ℕ)).getD (row : ℕ) 0 =
        IVP.ivp_DF_of_Dφ_nat
          (fun j m k => ((f_cpoly j).pderiv m).evalCoeff d.abar_Q k)
          j m (row : ℕ) (col : ℕ))
    {Z₁ : ℚ} (hle : ∀ l, ∑ m : Fin L, kerColMaxQ N d.abar_Q d.ν_q ((f_cpoly l).pderiv m) ≤ Z₁) :
    Z₁_norm (d.G (IVP.banachField f_cpoly) x₀) d.abar (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((IVP.StdIVPData.composedApprox d).toCLM (ν := ν)) ≤ (Z₁ : ℝ) :=
  d.Z₁_le_of_pairBound f_cpoly x₀ hDF
    (fun l m => kerColMaxQ N d.abar_Q d.ν_q ((f_cpoly l).pderiv m))
    (fun _ _ => tail_evalBanach_mul_le_ker d _) hle

end StdIVPData

/-! ## The ν-free record and its per-bound clauses -/

/-- **ν-free rational Taylor-IVP record**: the ℚ fields of `IVP.StdIVPData` and its stored
shape invariant, without the real weight.

Usage sketch (symbolic): a certificate supplies
`q : StdIVPDataQ L N := ⟨A_col, DF_col, abar_Q, ν_q, habar_size⟩` with
`habar_size : ∀ l, (abar_Q l).size = N + 1`, and realizes it at a real weight `ν` with a
bridge `hν : (ν : ℝ) = (ν_q : ℝ)` as `q.toStdIVPData ν hν : IVP.StdIVPData ν L N`; every
clause below is a decidable proposition on `q` alone. -/
structure StdIVPDataQ (L N : ℕ) [NeZero L] where
  A_col : Fin L → Fin L → ℕ → Array ℚ
  DF_col : Fin L → Fin L → ℕ → Array ℚ
  abar_Q : Fin L → Array ℚ
  ν_q : ℚ
  habar_size : ∀ l, (abar_Q l).size = N + 1

namespace StdIVPDataQ

variable {L N : ℕ} [NeZero L]

/-- Realization at a real weight with its rational bridge. -/
def toStdIVPData (q : StdIVPDataQ L N) (ν : PosReal) (hν : (ν : ℝ) = ((q.ν_q : ℚ) : ℝ)) :
    IVP.StdIVPData ν L N where
  A_col := q.A_col
  DF_col := q.DF_col
  abar_Q := q.abar_Q
  ν_q := q.ν_q
  hν := hν
  habar_size := q.habar_size

/-- `Z₀` exact clause of the record (one-line specialisation of `DefectExact`). -/
abbrev ChecksZ₀ (q : StdIVPDataQ L N) (Z₀ : ℚ) : Prop :=
  DefectExact L N q.A_col q.DF_col q.ν_q Z₀

/-- `Z₀` clause at a slot and grid denominator (one-line specialisation of `DefectBy`). -/
abbrev ChecksZ₀By (q : StdIVPDataQ L N) (s : Z₀Slot) (S : ℕ) (Z₀ : ℚ) : Prop :=
  DefectBy L N q.A_col q.DF_col q.ν_q s S Z₀

/-- `Z₂` clause: `activeBlockNormQ` at the computed scale `ν_q · DLipBoundQ` and the computed
active set, both at the radii `‖āᵢ‖ + r₀`. -/
abbrev ChecksZ₂ (q : StdIVPDataQ L N) (f_cpoly : Fin L → CompPoly L) (r₀ Z₂ : ℚ) : Prop :=
  activeBlockNormQ L N (fun l j k => q.A_col l j (k : ℕ)) q.ν_q
    (IVP.StdIVPData.approxInverse_tailBound_q (N := N))
    (q.ν_q * DLipBoundQ f_cpoly (fun i => abarNormQ N q.abar_Q q.ν_q i + r₀))
    (activeQ f_cpoly (fun i => abarNormQ N q.abar_Q q.ν_q i + r₀)) ≤ Z₂

/-- Forgetful map from an existing bundle: its ℚ fields and size invariant, forgetting `hν`
(`toStdIVPData_ofStd` is the definitional round trip). -/
def ofStd {ν : PosReal} (d : IVP.StdIVPData ν L N) : StdIVPDataQ L N :=
  ⟨d.A_col, d.DF_col, d.abar_Q, d.ν_q, d.habar_size⟩


/-! #### Soundness bridges for the exact stored data -/

section Bridges

variable (q : StdIVPDataQ L N) {ν : PosReal} (hν : (ν : ℝ) = ((q.ν_q : ℚ) : ℝ))





end Bridges

/-- Kernel `Z₁` clause: `Σ_m kerColMaxQ (∂_m f_l) ≤ Z₁` for every component (decidable). -/
abbrev ChecksZ₁ker (q : StdIVPDataQ L N) (f_cpoly : Fin L → CompPoly L) (Z₁ : ℚ) : Prop :=
  ∀ l, ∑ m : Fin L, kerColMaxQ N q.abar_Q q.ν_q ((f_cpoly l).pderiv m) ≤ Z₁

/-! #### ν-free slot checks (each decidable, no `ν`) -/

section Checks

variable (q : StdIVPDataQ L N) (f_cpoly : Fin L → CompPoly L)

/-- Jacobian clause: the stored `DF` is the exact finite Jacobian of `f_cpoly` at `ā`. -/
abbrev ChecksDF : Prop :=
  ∀ (j m : Fin L) (row col : Fin (N + 1)),
    (q.DF_col j m (col : ℕ)).getD (row : ℕ) 0 =
      IVP.ivp_DF_of_Dφ_nat (fun j m k => ((f_cpoly j).pderiv m).evalCoeff q.abar_Q k)
        j m (row : ℕ) (col : ℕ)




end Checks

/-- The kernel `Z₁` clause, with the Jacobian clause `ChecksDF`, bounds the `Z₁` operator norm of
the realization. -/
theorem Z₁ker_sound (q : StdIVPDataQ L N) {ν : PosReal} (hν : (ν : ℝ) = ((q.ν_q : ℚ) : ℝ))
    (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ) {Z₁ : ℚ} (hDF : q.ChecksDF f_cpoly)
    (h : q.ChecksZ₁ker f_cpoly Z₁) :
    Z₁_norm ((q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀) (q.toStdIVPData ν hν).abar
      (ContinuousLinearMap.id ℝ (XL1 ν L))
      ((IVP.StdIVPData.composedApprox (q.toStdIVPData ν hν)).toCLM (ν := ν)) ≤ (Z₁ : ℝ) :=
  StdIVPData.Z₁_le_ker_of_Q (q.toStdIVPData ν hν) f_cpoly x₀ hDF h

section Sound

variable (q : StdIVPDataQ L N) {ν : PosReal} (hν : (ν : ℝ) = ((q.ν_q : ℚ) : ℝ))

/-- The exact `Z₀` clause bounds the finite block norm of the realized defect `I - A·A†`. -/
theorem Z₀_sound {Z₀ : ℚ} (h : q.ChecksZ₀ Z₀) :
    finiteBlockMatrixNorm ν (q.toStdIVPData ν hν).defect.finBlock ≤ (Z₀ : ℝ) :=
  finiteBlockMatrixNorm_defect_le_of_Q _ _ q.A_col q.DF_col q.ν_q
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) hν h

/-- The slot/grid `Z₀` clause (at slot `s`, grid denominator `S`) implies the exact `Z₀`
clause. -/
theorem ChecksZ₀By_sound (s : Z₀Slot) (S : ℕ) {Z₀ : ℚ} (h : q.ChecksZ₀By s S Z₀) :
    q.ChecksZ₀ Z₀ :=
  defectBy_sound s S h

/-- The slot/grid `Z₀` clause bounds the finite block norm of the realized defect. -/
theorem defectZBy_sound (s : Z₀Slot) (S : ℕ) {Z₀ : ℚ} (h : q.ChecksZ₀By s S Z₀) :
    finiteBlockMatrixNorm ν (q.toStdIVPData ν hν).defect.finBlock ≤ (Z₀ : ℝ) :=
  q.Z₀_sound hν (q.ChecksZ₀By_sound s S h)

/-- The `Z₂` clause, at a nonnegative radius `r₀`, gives the `Z₂` bound `Z₂ · r₀` on the
closed ball of radius `r₀` around the realized `ā`. -/
theorem Z₂_sound (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ) {r₀ Z₂ : ℚ} (hr₀ : 0 ≤ r₀)
    (h : q.ChecksZ₂ f_cpoly r₀ Z₂) :
    ∀ c ∈ Metric.closedBall ((q.toStdIVPData ν hν).abar : XL1 ν L) (r₀ : ℝ),
      Z₂_norm ((q.toStdIVPData ν hν).G (IVP.banachField f_cpoly) x₀) (q.toStdIVPData ν hν).abar
        (ContinuousLinearMap.id ℝ (XL1 ν L)) c ≤ (Z₂ : ℝ) * (r₀ : ℝ) :=
  StdIVPData.Z₂_le_of_Q (q.toStdIVPData ν hν) f_cpoly x₀ hr₀ h

end Sound

/-! #### Soundness of the remaining per-bound clauses -/

section Faces

variable (q : StdIVPDataQ L N) {ν : PosReal} (hν : (ν : ℝ) = ((q.ν_q : ℚ) : ℝ))
  (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ)




/-! #### Soundness of the column clause -/


end Faces

end StdIVPDataQ

end IVP
