import RadiiPolynomial.Applications.IVP.Boundary
import RadiiPolynomial.Applications.IVP.Chebyshev.Trajectory
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.SymmetricSubalgebra
import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.EvaluationBounds
import RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Joukowski

/-!
# The Chebyshev IVP boundary functional

The production Chebyshev carrier stores a one-sided coefficient vector inside
the bilateral sequence space.  Evaluation at the left endpoint is therefore a
split continuous linear functional on storage.  It becomes an algebra
character only after passing to the flip-fixed physical subalgebra.

The coefficient antiderivative is normalized at the left endpoint by the
generic boundary-kernel projection.
-/

open scoped BigOperators

noncomputable section

namespace RadiiPolynomial

namespace IVP

open Polynomial.Chebyshev
open ChebyshevIVP

variable (ν : PosReal) [Fact (1 ≤ (ν : ℝ))]

/-- Evaluation of the stored Chebyshev series at the left endpoint.  This is
linear and unital on the storage carrier, but not multiplicative there. -/
def chebyshevBoundary : l1Chebyshev ν →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun a => l1Chebyshev.eval a (-1)
      map_add' := fun a b => by
        simpa using l1Chebyshev.eval_add a b (t := (-1 : ℝ)) (by norm_num)
      map_smul' := fun r a => by
        simpa only [RingHom.id_apply, smul_eq_mul] using l1Chebyshev.eval_smul r a (-1) }
    2 (fun a => by
      change |l1Chebyshev.eval a (-1)| ≤ 2 * ‖a‖
      exact l1Chebyshev.abs_eval_le_two_mul_norm a (by norm_num))

@[simp]
theorem chebyshevBoundary_apply (a : l1Chebyshev ν) :
    chebyshevBoundary ν a = l1Chebyshev.eval a (-1) :=
  rfl

@[simp]
theorem chebyshevBoundary_one : chebyshevBoundary ν 1 = 1 := by
  rw [chebyshevBoundary_apply, l1Chebyshev.eval_one]

/-- The storage boundary is not multiplicative on the full bilateral
coefficient algebra: it ignores negative modes.  Multiplicativity is restored
only on the flip-fixed physical subalgebra below. -/
theorem chebyshevBoundary_not_multiplicative :
    chebyshevBoundary ν
        (l1Chebyshev.single (-1) 1 * l1Chebyshev.single 1 1) ≠
      chebyshevBoundary ν (l1Chebyshev.single (-1) 1) *
        chebyshevBoundary ν (l1Chebyshev.single 1 1) := by
  have hneg : l1Chebyshev.eval (l1Chebyshev.single (ν := ν) (-1) 1) (-1) = 0 := by
    unfold l1Chebyshev.eval
    rw [l1Chebyshev.toSeq_single]
    simp only [if_neg (by omega : (0 : ℤ) ≠ -1), zero_add]
    have hzero : ∀ k : ℕ,
        l1Chebyshev.toSeq (l1Chebyshev.single (ν := ν) (-1) 1)
          ((k + 1 : ℕ) : ℤ) = 0 := fun k => by
      rw [l1Chebyshev.toSeq_single, if_neg (by omega)]
    simp_rw [hzero, zero_mul]
    simp
  rw [lpOneAlg.single_mul_single]
  norm_num
  rw [← lpOneAlg.one_eq_single_zero]
  rw [hneg, zero_mul, l1Chebyshev.eval_one]
  norm_num

/-- The storage-level splitting into the endpoint value and zero-endpoint
coefficients. -/
def chebyshevSplitBoundary : SplitBoundary ℝ (l1Chebyshev ν) ℝ where
  trace := chebyshevBoundary ν
  extension := algebraMapCLM ℝ (l1Chebyshev ν)
  trace_extension r := by
    rw [coe_algebraMapCLM, Algebra.algebraMap_eq_smul_one,
      map_smul, chebyshevBoundary_one, smul_eq_mul, mul_one]

/-- On the flip-fixed physical algebra, endpoint evaluation is a genuine
continuous algebra character. -/
def symmetricEndpointCharacter :
    l1Chebyshev.symmetricSubalgebra ν →A[ℝ] ℝ :=
  l1Chebyshev.symmetricEvalCharacter ν (-1) (by norm_num)

/-- The storage boundary is the physical endpoint character after
symmetrization. -/
theorem chebyshevBoundary_factor_symmetric (a : l1Chebyshev ν) :
    chebyshevBoundary ν a = symmetricEndpointCharacter ν
      ⟨l1Chebyshev.symmetrize a, l1Chebyshev.symmetrize_isSymmetric a⟩ :=
  (l1Chebyshev.eval_symmetrize a (-1)).symm

/-- The physical endpoint character pulls the Joukowski map back to Taylor
evaluation at the same point `-1`.  It does not pull back to the Taylor centre
character at `0`. -/
theorem symmetricEndpointCharacter_comp_joukowskiAevalSymm {r : PosReal}
    (hgate : CrossGeometry.semiMajor ν ≤ (r : ℝ)) :
    (symmetricEndpointCharacter ν).comp (CrossGeometry.joukowskiAevalSymm hgate) =
      l1Weighted.evalContinuousAlgHom (-1)
        (by simpa using CrossGeometry.one_le_of_semiMajor_le hgate) := by
  simpa [symmetricEndpointCharacter] using
    CrossGeometry.symmetricEvalCharacter_comp_joukowskiAevalSymm
      hgate (-1) (by norm_num)

/-- At weights `ν ≥ 2`, the left-endpoint boundary functional is
contractive on the production storage carrier. -/
theorem abs_chebyshevBoundary_le_norm_of_two_le (hν : (2 : ℝ) ≤ (ν : ℝ))
    (a : l1Chebyshev ν) : |chebyshevBoundary ν a| ≤ ‖a‖ := by
  rw [chebyshevBoundary_apply]
  exact l1Chebyshev.abs_eval_le_norm_of_two_le hν a (by norm_num)

/-- The coefficient antiderivative as a continuous linear map. -/
def chebyshevIntegrateCLM : l1Chebyshev ν →L[ℝ] l1Chebyshev ν :=
  -(chebyshevShiftDiv_CLM (ν := ν))

@[simp]
theorem chebyshevIntegrateCLM_apply (c : l1Chebyshev ν) :
    chebyshevIntegrateCLM ν c = chebyshevIntegrate c :=
  rfl

/-- Chebyshev integration normalized to vanish at the left endpoint. -/
def chebyshevAnchoredPrimitive :
    l1Chebyshev ν →L[ℝ] (chebyshevSplitBoundary ν).trace.ker :=
  (chebyshevSplitBoundary ν).anchoredPrimitive (chebyshevIntegrateCLM ν)

@[simp]
theorem chebyshevAnchoredPrimitive_zero_boundary (c : l1Chebyshev ν) :
    chebyshevBoundary ν
      (chebyshevAnchoredPrimitive ν c : l1Chebyshev ν) = 0 :=
  (chebyshevAnchoredPrimitive ν c).2

/-- The normalized coefficient primitive realizes the definite integral from
the left endpoint. -/
theorem eval_chebyshevAnchoredPrimitive (c : l1Chebyshev ν) {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    l1Chebyshev.eval (chebyshevAnchoredPrimitive ν c : l1Chebyshev ν) t =
      ∫ s in (-1 : ℝ)..t, l1Chebyshev.eval c s := by
  rw [chebyshevAnchoredPrimitive, SplitBoundary.anchoredPrimitive,
    ContinuousLinearMap.comp_apply, SplitBoundary.zeroPart_coe,
    chebyshevIntegrateCLM_apply]
  change l1Chebyshev.eval
      (chebyshevIntegrate c - algebraMap ℝ (l1Chebyshev ν)
        (chebyshevBoundary ν (chebyshevIntegrate c))) t = _
  rw [Algebra.algebraMap_eq_smul_one, l1Chebyshev.eval_sub _ _ (by
      exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩),
    l1Chebyshev.eval_smul, l1Chebyshev.eval_one, mul_one,
    chebyshevBoundary_apply]
  rw [integral_eval c ht]

end IVP

end RadiiPolynomial
