import RadiiPolynomial.Algebra.Rees.Laurent.Euler
import RadiiPolynomial.Algebra.Rees.Laurent.Gamma
import Mathlib.Data.Int.Interval

/-!
# The head cutoff of an `eps`-product

`PH_z_mul_z_head`: for any finite head `H` containing `k`, the head projection of the product
`z (k - j) * z j` is `X ^ eps k j • z k`. This is the one Γ-layer lemma that needs both the cutoff
API `PH` of `Euler` and the cancellation length `eps` of `Gamma`.
-/

noncomputable section

namespace RadiiPolynomial.Rees.Laurent

open Polynomial LaurentPolynomial

variable {R : Type*} [CommRing R]

theorem PH_z_mul_z_head {H : Finset ℤ} {k j : ℤ} (hk : k ∈ H) :
    PH H ((z (k - j) : U R) * z j) = (X : R[X]) ^ eps k j • (z k : U R) := by
  rw [z_sub_mul_z, map_smul, PH_z, ite_eq_left hk]

end RadiiPolynomial.Rees.Laurent
