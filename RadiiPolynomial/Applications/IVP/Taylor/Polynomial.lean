import RadiiPolynomial.Applications.IVP.Taylor.Standard
import RadiiPolynomial.Algebra.Polynomial.CompPoly.WeightedL1

/-!
# CompPoly Adapter for Standard IVPs

Derives the symbolic specification, differentiability, and rational Jacobian bridge needed by
`StdIVPData.composedApprox_eq_fderiv_G_fin` from one computable polynomial system.
-/

open RadiiPolynomial MvPolyBridge

namespace IVP

variable {L : ℕ}

/-- Exact rational IVP residual of the stored approximate solution for a `CompPoly`
vector field and rational initial condition. -/
def ivpCoeffsQ
    (f_cpoly : Fin L → CompPoly L) (abar_Q : Fin L → Array ℚ) (x₀_q : Fin L → ℚ)
    (l : Fin L) (n : ℕ) : ℚ :=
  match n with
  | 0 => (abar_Q l).getD 0 0 - x₀_q l
  | n + 1 => ((n : ℚ) + 1) * (abar_Q l).getD (n + 1) 0 -
      (f_cpoly l).evalCoeff abar_Q n

end IVP

noncomputable section

namespace IVP

variable {ν : PosReal} {L N : ℕ} [NeZero L]

/-- The real IVP residual at `d.abar` is the cast of `ivpCoeffsQ` when the vector
field comes from `CompPoly` and the initial condition is rational. -/
lemma StdIVPData.ivpCoeffs_abar_eq_cast_of_compPoly
    (d : StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L)
    (x₀ : Fin L → ℝ) (x₀_q : Fin L → ℚ)
    (hx₀ : ∀ l, x₀ l = (x₀_q l : ℝ)) (l : Fin L) (n : ℕ) :
    ivpCoeffs (fun a j => (f_cpoly j).evalBanach a) x₀ d.abar l n =
      (ivpCoeffsQ f_cpoly d.abar_Q x₀_q l n : ℝ) := by
  cases n with
  | zero =>
      simp only [ivpCoeffs, ivpCoeffsQ]
      rw [d.abar_toSeq_eq, hx₀ l]
      push_cast
      rfl
  | succ n =>
      simp only [ivpCoeffs, ivpCoeffsQ]
      rw [d.abar_toSeq_eq,
        (f_cpoly l).toSeq_evalBanach d.abar d.abar_Q d.abar_toSeq_eq n]
      push_cast
      rfl

/-- `StdIVPData.composedApprox` agrees with the derivative of the IVP map on finite modes
when the vector field comes from a `CompPoly` system.

All structural witnesses are derived from `f_cpoly`; the caller supplies only the exact
finite Jacobian check against the stored numerical matrix. -/
lemma StdIVPData.composedApprox_eq_fderiv_G_fin_of_compPoly
    (d : StdIVPData ν L N) (f_cpoly : Fin L → CompPoly L) (x₀ : Fin L → ℝ)
    (hDF_nat : ∀ (j m : Fin L) (row col : Fin (N + 1)),
      (d.DF_col j m (col : ℕ)).getD (row : ℕ) 0 =
        ivp_DF_of_Dφ_nat
          (fun j m k => ((f_cpoly j).pderiv m).evalCoeff d.abar_Q k)
          j m (row : ℕ) (col : ℕ))
    (h : XL1 ν L) (l : Fin L) (n : ℕ) (hn : n ≤ N) :
    toCoeff (ν := ν) ((StdIVPData.composedApprox d).toCLM (ν := ν) h) l n =
      toCoeff (ν := ν) ((fderiv ℝ
        (d.G (fun a l => (f_cpoly l).evalBanach a) x₀) d.abar) h) l n :=
  d.composedApprox_eq_fderiv_G_fin
    (fun a l => (f_cpoly l).evalBanach a)
    (fun l => (f_cpoly l).toMvPoly) x₀
    (fun a l => compPoly_evalBanach_eq_evalInBanach (f_cpoly l) a)
    (fun l => differentiable_evalBanach_l1Weighted (f_cpoly l))
    (fun j m k => ((f_cpoly j).pderiv m).evalCoeff d.abar_Q k)
    (fun j m k => compPoly_Dφ_bridge f_cpoly
      (fun l => (f_cpoly l).toMvPoly) (fun _ => rfl)
      d.abar_Q d.abar d.abar_toSeq_eq j m k)
    hDF_nat h l n hn

end IVP
