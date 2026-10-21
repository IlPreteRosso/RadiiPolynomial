import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Fiber Trivializations

A *fiber trivialization* of a family of normed `𝕜`-modules `E : M → Type*` is a chosen
`𝕜`-linear equivalence `θ_m : 𝕜 ≃ₗ[𝕜] E m` for every index `m`: each fiber is a
one-dimensional normed `𝕜`-module with a chosen nonzero generator, the *atom*
`δ_m := θ_m 1`, which spans the fiber. The *weight* `ω_m := ‖δ_m‖` is derived, as are
the scaling identity `‖θ_m r‖ = ‖r‖ * ω_m`, positivity `0 < ω_m`, and every additive
identity of `θ_m` (they are `map_add`, `map_neg`, `map_zero` of a linear equivalence).

The frame `θ` is chosen structure, never canonical: replacing `θ_m r` by `θ_m (u_m r)` with
`‖u_m‖ = 1` keeps every weight but can change the atoms and the transported convolution
product. "Metric on a trivial line family" is the permitted reading; no topological-bundle
or base-continuity claim is made.

This file is independent of `lpOneAlg`. The frame is the primary datum of the weighted ℓ¹ API:
the scalar coordinates `toRealSeq f m = θ_m⁻¹ (f m)`, the scalar singles, the weight classes and
the convolution product of `lpOneAlg M E` are all indexed by the chosen `FiberTrivialization`
(`WeightedL1/Carrier.lean`, `WeightedL1/Algebra.lean`).
-/

noncomputable section

namespace RadiiPolynomial

/-- A chosen `𝕜`-linear frame `θ_m : 𝕜 ≃ₗ[𝕜] E m` of every fiber of a family of normed
`𝕜`-modules. Each fiber is a one-dimensional normed `𝕜`-module with the chosen nonzero
generator `atom m = θ_m 1`; the weight `‖atom m‖` and the norm law are derived. -/
class FiberTrivialization (𝕜 : outParam Type*) [NormedField 𝕜] (M : Type*) (E : M → Type*)
    [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] where
  /-- The chosen frame `θ_m` of the fiber `E m`. -/
  equiv : ∀ m, 𝕜 ≃ₗ[𝕜] E m

namespace FiberTrivialization

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]

/-- The atom `δ_m = θ_m 1`: the chosen generator of the fiber `E m`. -/
def atom (m : M) : E m := equiv m 1

/-- The weight `ω_m = ‖θ_m 1‖` of the fiber `E m` (derived, never a field). -/
def weight (m : M) : ℝ := ‖atom (E := E) m‖



/-- `θ_m r = r • δ_m`. -/
lemma equiv_apply_eq_smul_atom (m : M) (r : 𝕜) :
    equiv (E := E) m r = r • atom (E := E) m := by
  rw [atom, ← map_smul, smul_eq_mul, mul_one]

/-- The scaling identity `‖θ_m r‖ = ‖r‖ * ω_m`. -/
lemma norm_equiv_apply (m : M) (r : 𝕜) :
    ‖equiv (E := E) m r‖ = ‖r‖ * weight (E := E) m := by
  rw [equiv_apply_eq_smul_atom, norm_smul, weight]

lemma atom_ne_zero (m : M) : atom (E := E) m ≠ 0 := fun h =>
  one_ne_zero ((equiv (E := E) m).injective (h.trans (map_zero (equiv (E := E) m)).symm))

/-- Positivity of the weight, derived from injectivity of `θ_m` and `1 ≠ 0`. -/
lemma weight_pos (m : M) : 0 < weight (E := E) m := norm_pos_iff.mpr (atom_ne_zero m)

lemma weight_nonneg (m : M) : 0 ≤ weight (E := E) m := (weight_pos m).le

lemma weight_ne_zero (m : M) : weight (E := E) m ≠ 0 := (weight_pos m).ne'

/-- `‖θ_m⁻¹ x‖ = ‖x‖ / ω_m`. -/
lemma norm_equiv_symm_apply (m : M) (x : E m) :
    ‖(equiv (E := E) m).symm x‖ = ‖x‖ / weight (E := E) m := by
  rw [eq_div_iff (weight_ne_zero m), ← norm_equiv_apply, LinearEquiv.apply_symm_apply]

/-! ### Additive identities (all are `map_*` of a linear equivalence) -/

@[simp] lemma equiv_zero (m : M) : equiv (E := E) m 0 = 0 := map_zero _
@[simp] lemma equiv_add (m : M) (a b : 𝕜) :
    equiv (E := E) m (a + b) = equiv m a + equiv m b := map_add _ a b
@[simp] lemma equiv_neg (m : M) (a : 𝕜) : equiv (E := E) m (-a) = -equiv m a := map_neg _ a
@[simp] lemma equiv_symm_zero (m : M) : (equiv (E := E) m).symm 0 = 0 := map_zero _
lemma equiv_symm_apply_equiv (m : M) (r : 𝕜) :
    (equiv (E := E) m).symm (equiv m r) = r := LinearEquiv.symm_apply_apply _ r
lemma equiv_apply_equiv_symm (m : M) (x : E m) :
    equiv (E := E) m ((equiv m).symm x) = x := LinearEquiv.apply_symm_apply _ x

/-! ### Continuity with the scaling constants `ω_m` and `1 / ω_m` -/

lemma continuous_equiv (m : M) : Continuous (equiv (E := E) m) :=
  AddMonoidHomClass.continuous_of_bound (equiv (E := E) m) (weight (E := E) m)
    fun r => (norm_equiv_apply m r).trans_le (le_of_eq (mul_comm _ _))

lemma continuous_equiv_symm (m : M) : Continuous (equiv (E := E) m).symm :=
  AddMonoidHomClass.continuous_of_bound (equiv (E := E) m).symm (weight (E := E) m)⁻¹
    fun x => (norm_equiv_symm_apply m x).trans_le (le_of_eq (by rw [div_eq_inv_mul]))

/-- The frame `θ_m` as a continuous linear equivalence `𝕜 ≃L[𝕜] E m` (continuous both ways, with
the constants `ω_m` and `1 / ω_m`). -/
def equivL (m : M) : 𝕜 ≃L[𝕜] E m where
  toLinearEquiv := equiv m
  continuous_toFun := continuous_equiv m
  continuous_invFun := continuous_equiv_symm m


end FiberTrivialization

end RadiiPolynomial

end
