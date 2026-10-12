import RadiiPolynomial.Examples.IVP.Taylor.Example81.Certificate

/-!
# Test (family TY): the all-generated Taylor certificate face on Example 8.1

Not part of the default build (imported by no module); build it with
`lake build RadiiPolynomial.Examples.tests.TY.AllGenerated`.

The ν-free record of Example 8.1's bundle (`IVP.StdIVPDataQ.ofStd data`) and the five numbers of
its production certificate pass every generated clause of `IVP.TaylorCertQ.ChecksBy` (exact-columns
`Z₀` at grid denominator `10⁶⁰`, column `Z₁`) in one `decide +kernel`; the all-generated face
`IVP.StdIVPDataQ.certified_of_checksBy` then gives the unique zero, with standard axioms only.
This exercises the faces `TaylorCertQ`, `ChecksRadii`, `ChecksBy`, `Y₀_sound`, `Z₁By_sound`,
`radii_sound`, `certified_of_bounds` and `certified_of_checksBy`.
-/

open RadiiPolynomial Example81

namespace Tests.TY

/-- The ν-free record of Example 8.1's bundle. -/
def dataQ : IVP.StdIVPDataQ L N := IVP.StdIVPDataQ.ofStd data

/-- The certificate numbers of Example 8.1 (exact column `Z₁`). -/
def C81 : IVP.TaylorCertQ := ⟨Y₀_bound, Z₀_bound, Cert.Z₁_exact_bound, Z₂_bound, r_minus⟩

set_option maxHeartbeats 0 in
theorem all81 : C81.ChecksBy .exactCols (10 ^ 60) .column dataQ f_cpoly x₀_q := by
  decide +kernel

theorem main81 :
    ∃! xTilde ∈ Metric.closedBall ((dataQ.toStdIVPData ν_val ν_val_eq_q).abar : XL1 ν_val L)
        (C81.r₀ : ℝ),
      (dataQ.toStdIVPData ν_val ν_val_eq_q).G (IVP.banachField f_cpoly) x₀ xTilde = 0 :=
  dataQ.certified_of_checksBy ν_val_eq_q f_cpoly x₀ .exactCols (10 ^ 60) .column x₀_q
    (fun l => by fin_cases l; norm_num [x₀, x₀_q]) C81 all81

end Tests.TY

#print axioms Tests.TY.all81
#print axioms Tests.TY.main81
