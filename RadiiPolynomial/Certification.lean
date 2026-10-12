import RadiiPolynomial.Certification.Witness
import RadiiPolynomial.Certification.LeanCertAdapter
import RadiiPolynomial.Certification.Rational.Matrix
import RadiiPolynomial.Certification.ColumnTailBound
import RadiiPolynomial.Certification.Residual
import RadiiPolynomial.Certification.Residual.FiniteSupport
import RadiiPolynomial.Certification.RadiiPolynomialQ
import RadiiPolynomial.Certification.Rational.Frac
import RadiiPolynomial.Certification.Rational.Grid

/-!
Certification layer below the family faces: witness reductions (`Witness`), the exact-rational
finite-matrix layer and its real bridges (`Rational.Matrix`), the rational grid checkers
(`Rational.Frac`, `Rational.Grid`), exact-ℚ radii-polynomial evaluation (`RadiiPolynomialQ`),
residual inverse certificates (`Residual`, `Residual.FiniteSupport`), the exact column tail bounds
used by the Taylor `Z₁` (`ColumnTailBound`) and the dyadic LeanCert evaluators
(`LeanCertAdapter`). The family certificate faces `Certification.IVP.Taylor`,
`Certification.IVP.Chebyshev` and `Certification.PowerSeries.PolynomialZero` import their
application discretizations and are not part of this facade; certificates import them directly,
so a Taylor certificate does not load the Chebyshev discretization.
-/
