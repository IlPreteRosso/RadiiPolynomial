import RadiiPolynomial.Examples.IVP.Chebyshev.Example1421.Algebra
import RadiiPolynomial.Certification
import RadiiPolynomial.Certification.IVP.Chebyshev

/-!
# Example 14.2.1 — Certificate (complete)

Full machine-checked verification of the Chebyshev logistic twin at ν = 2,
N = 40 (`main_theorem`), through the family face `StdChebIVPData.certified_of_checksK` of
the Chebyshev certification adapter (`Certification/IVP/Chebyshev/Kernel/Face.lean`, through
the facade `Certification/IVP/Chebyshev.lean`). Every
obligation is an exact-ℚ conjunct of `ChebCertQ.ChecksK`, closed by its own
`decide +kernel` lemma on the stored data (`A_col`, `DF_col`, `abar_0`, `ν_q`); the
certificate uses no compiled-code evaluation. The four bounds:

- `Y₀_le` — ‖G(ā)‖ ≤ 10⁻²¹ from the exact ℚ value of the residual after the stored
  preconditioner (`Y₀_le_of_Q`);
- `Z₀_finBlockNorm_le` — the 41×41 block defect ‖I − A·DF‖ ≤ 10⁻¹⁶ from the grid clause
  of `DefectBy` at denominator `10 ^ 60` (`StdChebIVPData.Z₀_sound`); the function-space
  endpoints consume this finite-block bound. `main_theorem` supplies the same grid
  check through `StdChebIVPData.certified_of_checksK`;
- `Z₁_le` — ε + ν/(N+1)·K ≤ 0.2533 via `chebyshev_Z₁_le_relaxed` (`Z₁_le_of_checksK`):
  negatives pass through, the tail is −shiftDiv(Dφ h), and the ε-leakage (7/2000) is
  certified column by column in exact ℚ — columns ≤ N cancel exactly against the stored
  Jacobian, the leaked Dφ couplings N < m ≤ 2N+2 peak at ≈ 0.0034, and beyond 2N+2 only
  row 0's alternating functional survives; K = 5.12 is the syntactic derivative constant
  at the certified radius `‖S(ā)‖ ≤ 39/50` (the kernel checks `k_R`, `k_K`; the same radius
  is the public `Sabar_norm_le`);
- `Z₂_le` — 14·r₀ through `Z₂_le_of_Q`: the derivative's Lipschitz constant
  `8 = 2·derivativeLipschitzBound (X² − X)` read off the syntax, and the sharp full-column
  bound ‖TC‖ ≤ 7/4 (closed-form `TC` rows, tail ν/(N+1) = 2/41);

plus `radii_neg` (the radii polynomial at r = 10⁻⁶).
-/

open scoped BigOperators Topology NNReal ENNReal
open Metric Set Filter ContinuousLinearMap RadiiPolynomial ChebyshevIVP Example1421

noncomputable section

namespace Example1421.Cert

/-! ## The certificate and its kernel checks

The numbers are those of `Numbers.lean` (`Y₀, Z₀, Z₁, Z₂, r₋`) plus the overrides
`‖S(ā)‖ ≤ 39/50`, `K = K_bound`, `ε = eps_bound`, `‖TC‖ ≤ 7/4`, `B = 8`. Each conjunct of
`ChebCertQ.ChecksK` is its own `decide +kernel` lemma, stated on the stored data (`data`'s
fields by `rfl`). The `ε` columns are split at the stored block edge (`mn < 41`: the residual
columns vanish, `DF` being the exact Jacobian; `41 ≤ mn ≤ 82`: the Jacobian's high-mode tail).
`Z₀` uses the grid slot of `DefectBy` at denominator `10 ^ 60`. -/

section Kernel

open RadiiPolynomial.Certification.Rational

/-- The rational boundary value. -/
private def p_q : Fin L → ℚ := fun _ => 1 / 2

private theorem hp : ∀ l, p₀ l = (p_q l : ℝ) := fun l => by norm_num [p₀, p_q]

/-- The certificate numbers. -/
private def cert : ChebCertQ L where
  Y₀ := Y₀_bound
  Z₀ := Z₀_bound
  Z₁ := Z₁_bound
  Z₂ := Z₂_bound
  r₀ := r_minus
  R := fun _ => 39 / 50
  K := K_bound
  ε := eps_bound
  C := 7 / 4
  B := 8

/-- Per-block leakage datum (one block, `E = eps_bound`). -/
private def E : Fin L → Fin L → ℚ := fun _ _ => eps_bound

/-- The stored candidate as a component family (`data.abar_Q` by `rfl`). -/
private abbrev abarQ : Fin L → Array ℚ := fun _ => abar_0

private theorem k_Z₀ : DefectBy L N A_col DF_col ν_q .grid (10 ^ 60) cert.Z₀ := by
  decide +kernel

private theorem k_Y₀ : ∀ l, Y₀Q N A_col abarQ ν_q f_cpoly p_q l ≤ cert.Y₀ := by
  decide +kernel

private theorem k_R : ∀ i, SnormQ N abarQ ν_q i ≤ cert.R i := by
  decide +kernel

private theorem k_K : ∀ l, MvPolyBridge.CompPoly.Chebyshev.derivativeBound (f_cpoly l) cert.R ≤ cert.K := by
  decide +kernel

private theorem k_Mfar : Mfar N f_cpoly abarQ + 1 = 41 + 42 := by
  decide +kernel

/-- `ε` columns inside the stored block (`mn ≤ 40`). -/
private theorem k_eps_lo : ∀ l j, ∀ mn < 41,
    colNormS N A_col DF_col abarQ ν_q f_cpoly l j mn ≤ E l j * ν_q ^ mn := by
  decide +kernel

/-- `ε` columns beyond the stored block (`41 ≤ mn ≤ 82 = Mfar`). -/
private theorem k_eps_hi : ∀ l j, ∀ t < 42,
    colNormS N A_col DF_col abarQ ν_q f_cpoly l j (41 + t) ≤ E l j * ν_q ^ (41 + t) := by
  decide +kernel

private theorem k_far : ∀ l j, rowA0Q N A_col ν_q l j ≤ E l j * ν_q ^ (Mfar N f_cpoly abarQ + 1) := by
  decide +kernel

private theorem k_E : ∀ l, ∑ j, E l j ≤ cert.ε := by
  decide +kernel

private theorem k_Z₁ : cert.ε + ν_q / ((N : ℚ) + 1) * cert.K ≤ cert.Z₁ := by
  decide +kernel

private theorem k_TC : TCnormF N A_col ν_q ≤ cert.C := by
  decide +kernel

private theorem k_B : ∀ l, 2 * MvPolyBridge.CompPoly.Chebyshev.derivativeLipschitzBound (f_cpoly l)
    (fun i => cert.R i + 2 * cert.r₀) ≤ cert.B := by
  decide +kernel

private theorem k_Z₂ : cert.C * cert.B ≤ cert.Z₂ := by
  decide +kernel

private theorem k_r₀ : 0 < cert.r₀ := by
  decide +kernel

private theorem k_rad : cert.Z₂ * cert.r₀ ^ 2 - (1 - cert.Z₀ - cert.Z₁) * cert.r₀ + cert.Y₀ < 0 := by
  decide +kernel

/-- The kernel-scale obligations, assembled from the per-conjunct lemmas (stored data). -/
private theorem checksK : cert.ChecksK .grid (10 ^ 60) E N A_col DF_col abarQ ν_q f_cpoly p_q :=
  ⟨k_Z₀, k_Y₀, k_R, k_K,
    fun l j mn hmn => by
      have hmn' : mn < 41 + 42 := k_Mfar ▸ hmn
      exact (lt_or_ge mn 41).elim (k_eps_lo l j mn) fun hm => by
        simpa [Nat.add_sub_of_le hm] using k_eps_hi l j (mn - 41) (by omega),
    k_far, k_E, k_Z₁, k_TC, k_B, k_Z₂, k_r₀, k_rad⟩

/-- The same obligations on the bundle's fields (definitional). -/
private theorem checksK_data :
    cert.ChecksK .grid (10 ^ 60) E N data.A_col data.DF_col data.abar_Q data.ν_q f_cpoly p_q :=
  checksK

end Kernel

local notation "ābar" => ChebyshevIVP.StdChebIVPData.abar data

/-! ## The four bounds -/

/-- Y₀ obligation: `‖G(ā)‖ ≤ 10⁻²¹`, from the exact ℚ value of the preconditioned residual. -/
lemma Y₀_le :
    ‖data.G (banachField f_cpoly) p₀ (ChebyshevIVP.StdChebIVPData.abar data)‖ ≤ (Y₀_bound : ℝ) :=
  data.Y₀_le_of_Q f_cpoly p₀ p_q hp k_Y₀

/-- Z₀ obligation in finite-block form, from the grid clause. -/
lemma Z₀_finBlockNorm_le :
    finiteBlockMatrixNorm ν_val data.defect.finBlock ≤ (Z₀_bound : ℝ) :=
  data.Z₀_sound .grid (10 ^ 60) k_Z₀

/-- The certified radius of the symmetrized candidate: `‖S(ā)‖ ≤ 39/50`. -/
lemma Sabar_norm_le (l : Fin L) : ‖l1Chebyshev.symmetrize_CLM (ābar l)‖ ≤ ((39/50 : ℚ) : ℝ) := by
  rw [l1Chebyshev.symmetrize_CLM_apply, data.norm_symmetrize_abar_eq l]
  exact Rat.cast_le.mpr (k_R l)

/-- **Z₁ obligation**: `‖composedApprox − DG(ā)‖ ≤ Z₁ = ε + ν/(N+1)·K`. -/
lemma Z₁_le :
    ‖data.composedApproxCLM - fderiv ℝ (data.G (banachField f_cpoly) p₀) ābar‖ ≤ ((Z₁_bound : ℚ) : ℝ) :=
  data.Z₁_le_of_checksK f_cpoly p₀ p_q cert E .grid (10 ^ 60) checksK_data


/-- **Z₂ obligation**: the Lipschitz bound on DG over the certificate ball, from
`Z₂_le_of_Q`: `‖TC‖ ≤ 7/4` (closed-form rows, `TCnormF_eq`) times the syntactic derivative
Lipschitz constant `8 = 2 · derivativeLipschitzBound (X² − X)` at the radii `39/50 + 2 r₀`. -/
lemma Z₂_le : ∀ c ∈ Metric.closedBall ābar ((r_minus : ℚ) : ℝ),
    ‖fderiv ℝ (data.G (banachField f_cpoly) p₀) c
        - fderiv ℝ (data.G (banachField f_cpoly) p₀) ābar‖
      ≤ ((Z₂_bound : ℚ) : ℝ) * ((r_minus : ℚ) : ℝ) :=
  data.Z₂_le_of_Q f_cpoly p₀ (r₀ := cert.r₀) (C := cert.C) (B := cert.B) (Z₂ := cert.Z₂) k_R
    k_r₀.le (by rw [← TCnormF_eq]; exact k_TC) k_B k_Z₂

/-- The radii polynomial is negative at the certified radius r = 10⁻⁶. -/
lemma radii_neg :
    generalRadiiPolynomial (Y₀_bound : ℝ) (Z₀_bound : ℝ) (Z₁_bound : ℝ)
      (fun _ => (Z₂_bound : ℝ)) (r_minus : ℝ) < 0 := by
  norm_num [generalRadiiPolynomial, Y₀_bound, Z₀_bound, Z₁_bound, Z₂_bound, r_minus]

/-! ## The main theorem -/

/-- **Example 14.2.1**: the composed Chebyshev map for `u̇ = u(u−1)`, `u(−1) = ½`
has a unique zero within `10⁻⁶` of the numerical Chebyshev candidate, at
`ν = 2`, `N = 40`. The book's own twin of Example 8.1, machine-checked. -/
theorem main_theorem :
    ∃! xTilde ∈ Metric.closedBall (ChebyshevIVP.StdChebIVPData.abar data)
        ((r_minus : ℚ) : ℝ),
      data.G (banachField f_cpoly) p₀ xTilde = 0 :=
  data.certified_of_checksK f_cpoly p₀ p_q hp cert E .grid (10 ^ 60) checksK_data

end Example1421.Cert
