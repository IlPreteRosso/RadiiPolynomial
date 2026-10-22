import RadiiPolynomial.Certification.IVP.Chebyshev.QLayer
import RadiiPolynomial.Certification.IVP.Chebyshev.Common
import RadiiPolynomial.Certification.IVP.Chebyshev.Y0Z0
import RadiiPolynomial.Certification.IVP.Chebyshev.TC
import RadiiPolynomial.Certification.IVP.Chebyshev.Z1
import RadiiPolynomial.Certification.IVP.Chebyshev.Face
import RadiiPolynomial.Certification.IVP.Chebyshev.Kernel.QLayer
import RadiiPolynomial.Certification.IVP.Chebyshev.Kernel.Face

/-!
# Chebyshev certification adapter

Exact-ℚ clauses for the standard Chebyshev IVP bundle `ChebyshevIVP.StdChebIVPData` and a
`CompPoly` system, with their soundness at every real realization. This facade imports the
eight modules of `Certification/IVP/Chebyshev/`; they import the Chebyshev discretization
through its narrow owner `Applications/IVP/Chebyshev/Polynomial` and the exact-rational
certification layer; no reusable module below `Certification` imports them.

## Modules

1. `QLayer`: `radiusF`, `MY`, `Y₀Q`, `SnormQ` — the computable ℚ quantities of the residual and
   of the symmetrized candidate.
2. `Common`: `FCe` and the basis-direction row facts (`FCseq_single_nat`, …) shared by `TC`
   and `Z1`.
3. `Y0Z0`: bridges on a bundle `d : StdChebIVPData ν L N`: `d.defect_finBlockNorm_le_of_Q`
   (exact block norm of the family-neutral `defectCols`), `d.Z₀_sound` (any `DefectBy` slot),
   `d.Y₀_le_of_Q`, and the exact `‖S(āᵢ)‖` (`d.norm_symmetrize_abar_eq`).
4. `TC` (`Z₂`): the `TC` column norms `TCcolQ`, `TCcolNormQ`, `TCblockGen`, `TCnormGen`; the
   operator bound `d.TC_norm_le_gen` and `d.Z₂_le_of_Q`.
5. `Z1` (`Z₁`): the leakage columns `jacColQ`, `DcolAux`, `colNormAux`, `chebColNormQ`,
   `Mfar`, `rowA0Q`, `epsBlockGen`, `epsGen`; the hypotheses `d.Z₁_hneg`, `d.Z₁_htail`,
   `d.Z₁_hDφ`, `d.Z₁_hfin` of `chebyshev_Z₁_le_relaxed`, and `d.Z₁_le_of_Q`.
6. `Face`: the family face: `ChebCertQ` (the certificate numbers and override slots),
   `ChebCertQ.Checks` (all obligations as one ℚ-decidable conjunction), `d.certified_of_Y₀Z₀`
   and `d.certified_of_checks`.
7. `Kernel/QLayer`: the clipped Laurent interpreter `evalFast` (`evalFast_eq`), the sparse
   leakage columns `colNormS` (`colNormS_eq`), the closed-form `TC` rows `TCnormF`
   (`TCnormF_eq`).
8. `Kernel/Face`: the kernel-scale obligations `ChebCertQ.ChecksK` (with a `DefectBy` slot for
   `Z₀` and per-block leakage data `E`), `checks_of_checksK`, `d.Z₁_le_of_checksK` and the
   family face `d.certified_of_checksK`.

Imports: `QLayer → Y0Z0 → {TC, Z1} → Face → Kernel/Face`, `Common → {TC, Z1}`,
`{TC, Z1} → Kernel/QLayer → Kernel/Face`; `TC` and `Z1` are independent.
-/
