import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Derivatives of algebra-valued multivariate polynomials

`polynomialDerivative` packages the formal partial derivatives as a continuous
linear map. `hasFDerivAt_aeval` identifies it with the Fréchet derivative of
polynomial evaluation in a normed commutative algebra. The proof uses
`MvPolynomial.induction_on`, independently of any coefficient representation.
-/

noncomputable section

open scoped BigOperators

namespace MvPolynomial

section Differential

variable {ι C 𝕜 R : Type*} [Fintype ι] [CommSemiring C]
  [NormedField 𝕜] [NormedCommRing R] [NormedAlgebra 𝕜 R] [Algebra C R]

/-- The polynomial derivative in a normed commutative algebra. -/
def polynomialDerivative (p : MvPolynomial ι C) (a : ι → R) : (ι → R) →L[𝕜] R :=
  ∑ i : ι, (aeval a (pderiv i p)) • ContinuousLinearMap.proj i

@[simp] theorem polynomialDerivative_apply (p : MvPolynomial ι C) (a h : ι → R) :
    polynomialDerivative (𝕜 := 𝕜) p a h = ∑ i : ι, aeval a (pderiv i p) * h i := by
  simp [polynomialDerivative]

end Differential

variable {ι C 𝕜 R : Type*} [Fintype ι] [CommSemiring C]
  [NontriviallyNormedField 𝕜] [NormedCommRing R] [NormedAlgebra 𝕜 R] [Algebra C R]

/-- Algebra-valued multivariate polynomial evaluation has the formal partial derivatives.
No completeness or scalar-tower hypothesis is needed. -/
theorem hasFDerivAt_aeval (p : MvPolynomial ι C) (a : ι → R) :
    HasFDerivAt (fun x : ι → R => aeval x p) (polynomialDerivative (𝕜 := 𝕜) p a) a := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r =>
      have hd : polynomialDerivative (𝕜 := 𝕜) (MvPolynomial.C r) a = 0 := by
        ext h
        simp
      rw [hd]
      simpa only [MvPolynomial.aeval_C] using
        hasFDerivAt_const (𝕜 := 𝕜) (algebraMap C R r) a
  | add p q hp hq =>
      have hd : polynomialDerivative (𝕜 := 𝕜) (p + q) a =
          polynomialDerivative p a + polynomialDerivative q a := by
        ext h
        simp [polynomialDerivative_apply, add_mul, Finset.sum_add_distrib]
      rw [hd]
      simp only [map_add]
      exact hp.add hq
  | mul_X p i hp =>
      have hi := (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι => R)
        i).hasFDerivAt (x := a)
      have hd : polynomialDerivative (𝕜 := 𝕜) (p * MvPolynomial.X i) a =
          (aeval a p) • ContinuousLinearMap.proj i + (a i) • polynomialDerivative p a := by
        ext h
        simp only [polynomialDerivative_apply, MvPolynomial.pderiv_mul,
          map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.pderiv_X,
          Pi.single_apply, apply_ite (aeval a), map_one, map_zero,
          add_apply, smul_apply,
          ContinuousLinearMap.proj_apply, smul_eq_mul, add_mul,
          Finset.sum_add_distrib, Finset.mul_sum]
        have hdelta : (∑ j : ι, (aeval a p * if i = j then (1 : R) else 0) * h j)
            = aeval a p * h i := by
          simp [mul_ite]
        rw [hdelta]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hd]
      simp only [map_mul, MvPolynomial.aeval_X]
      exact hp.mul hi

end MvPolynomial
