import RadiiPolynomial.Algebra.Rees.Laurent.Family
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Int.Interval

/-!
# The Euler derivation and the finite-core diagonal calculus on the Rees family

The signed Euler derivation `δ = T d/dT` (`δ Tʲ = j Tʲ`) of `S[T;T⁻¹]` (any commutative ring `S`)
restricts to the Rees family `U R` (`S = R[X]`). On `U R` it preserves the tail ideal `JN N`, the
coordinate pieces, the head/tail coordinate modules and the polynomial degree pieces. Coordinate
multipliers `diagU lam` form an algebra map `diagAlgHom`; the polynomial symbols
`qDelta sym = aeval δ sym` are diagonal with eigenvalues `sym k`, commute with the head projections
`PH H`, and `PH H ∘ₗ qDelta sym ∘ₗ (1 - PH H) = 0`. The tail-inverse criterion
`qDelta_bijOn_tail_iff` says `qDelta sym` is bijective on the coordinate tail iff its tail
eigenvalues are units; `deltaU_bijOn_tail` is the case `sym = X` over a `ℚ`-algebra.
Boundaries (under `[Nontrivial R]`): `X_pow_smul_one_ne_zero`, `X_pow_smul_one_not_mem_tailMod`,
`deltaU_not_injOn_JN`, `no_inv_X_pow`, `z_ne_zero`.

## Instance selection and usage for operator-level identities

Under the default instances, `(1 : U R →ₗ[R[X]] U R) - PH H` does not elaborate (the subtraction of
linear maps on the subalgebra `U R` fails to find its additive group). The section `Selection` of
this file therefore declares two `local instance`s, `instUAddCommGroup` (the additive group
inherited through the induced ring structure `(U R).toRing`) and `instUZero` (its zero), which select
the EXISTING operations and introduce no independent structure (`zero_selection_eq_existing` is the
`rfl` witness). They are local to that section; the operator-level identities `PH_comp_one_sub`,
`one_sub_comp_PH`, `PH_qDelta_tail` and `PH_add_qDelta_tail` are stated there.

REQUIRED USAGE for operator-level identities: a consumer that states or rewrites with them opts into
the selection with
`attribute [local instance] Rees.Laurent.instUAddCommGroup Rees.Laurent.instUZero`
(inside the `RadiiPolynomial` namespace; with fully qualified names:
`attribute [local instance] RadiiPolynomial.Rees.Laurent.instUAddCommGroup RadiiPolynomial.Rees.Laurent.instUZero`).
Consumers that keep the default instances use the applied corollaries `PH_apply_sub_PH_apply`,
`PH_sub_apply` and `PH_qDelta_tail_apply`, stated after the section under default instances.

Promoted from the S028a `ReesEuler` freeze by unit L003-ReesLaurent (see `RENAMES.md`).
-/

noncomputable section

namespace RadiiPolynomial.Rees.Laurent

open Polynomial LaurentPolynomial

section Generic

/-- Coordinate multiplication on the ambient Laurent algebra. -/
def diagL {S : Type*} [CommSemiring S] (lam : ℤ → S) : S[T;T⁻¹] →ₗ[S] S[T;T⁻¹] where
  toFun f := AddMonoidAlgebra.ofCoeff (Finsupp.onFinset f.coeff.support
    (fun j => lam j * f.coeff j) (by
      intro j hj
      exact Finsupp.mem_support_iff.mpr (fun hf => hj (by rw [hf, mul_zero]))))
  map_add' f g := by
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro j
    simp only [Finsupp.onFinset_apply,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]
  map_smul' p f := by
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro j
    simp only [Finsupp.onFinset_apply,
      AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem coeff_diagL {S : Type*} [CommSemiring S] (lam : ℤ → S) (f : S[T;T⁻¹]) (j : ℤ) :
    (diagL lam f).coeff j = lam j * f.coeff j := rfl

theorem diagL_single {S : Type*} [CommSemiring S] (lam : ℤ → S) (j : ℤ) (p : S) :
    diagL lam (AddMonoidAlgebra.single j p) = AddMonoidAlgebra.single j (lam j * p) := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro k
  by_cases h : j = k
  · subst k
    simp only [coeff_diagL, coeff_single_eq, ite_true]
  · simp only [coeff_diagL, coeff_single_eq, ite_eq_right h, mul_zero]

/-- The signed-index Euler derivation `T d/dT` of `S[T;T⁻¹]`. -/
def deltaL (S : Type*) [CommRing S] : Derivation S S[T;T⁻¹] S[T;T⁻¹] :=
  Derivation.mk' (diagL (fun j => (j : S))) (by
    intro f g
    change diagL (fun j => (j : S)) (f * g) =
      f * diagL (fun j => (j : S)) g + g * diagL (fun j => (j : S)) f
    induction f using AddMonoidAlgebra.induction_linear with
    | zero => simp only [zero_mul, map_zero, mul_zero, add_zero]
    | add f h hf hh =>
      simp only [add_mul, mul_add, map_add, hf, hh]
      abel
    | single i p =>
      induction g using AddMonoidAlgebra.induction_linear with
      | zero => simp only [mul_zero, map_zero, zero_mul, add_zero]
      | add g h hg hh =>
        simp only [mul_add, add_mul, map_add, hg, hh]
        abel
      | single j q =>
        simp only [AddMonoidAlgebra.single_mul_single, diagL_single,
          Int.cast_add]
        rw [add_comm j i, ← AddMonoidAlgebra.single_add]
        congr 1
        ring)

theorem coeff_deltaL {S : Type*} [CommRing S] (f : S[T;T⁻¹]) (j : ℤ) :
    (deltaL S f).coeff j = (j : S) * f.coeff j := rfl

end Generic

section Selection

variable {R : Type*} [CommRing R]

/-- Select the inherited group directly, without changing its operations. -/
local instance instUAddCommGroup : AddCommGroup (U R) := (U R).toRing.toAddCommGroup

/-- Select the zero of the inherited additive group in both assembly environments. -/
local instance instUZero : Zero (U R) := (instUAddCommGroup (R := R)).toZero

theorem zero_selection_eq_existing :
    (0 : U R) = @Zero.zero (U R) ((instUAddCommGroup (R := R)).toZero) := rfl

theorem deltaL_mem_U {f : (R[X])[T;T⁻¹]} (hf : f ∈ U R) : deltaL R[X] f ∈ U R := by
  apply (mem_U_iff _).mpr
  intro j
  rw [coeff_deltaL]
  exact dvd_mul_of_dvd_right ((mem_U_iff _).mp hf j) _

/-- Restriction of Euler differentiation to the Rees family. -/
def deltaU (R : Type*) [CommRing R] : Derivation R[X] (U R) (U R) where
  toFun f := ⟨deltaL R[X] f, deltaL_mem_U f.property⟩
  map_add' f g := Subtype.ext ((deltaL R[X]).map_add f g)
  map_smul' p f := Subtype.ext ((deltaL R[X]).map_smul p f)
  map_one_eq_zero' := Subtype.ext (deltaL R[X]).map_one_eq_zero
  leibniz' f g := Subtype.ext ((deltaL R[X]).leibniz f g)

theorem coe_deltaU (f : U R) :
    ((deltaU R f : U R) : (R[X])[T;T⁻¹]) = deltaL R[X] f := rfl

theorem coeff_deltaU (f : U R) (j : ℤ) :
    ((deltaU R f : U R) : (R[X])[T;T⁻¹]).coeff j =
      (j : R[X]) * (f : (R[X])[T;T⁻¹]).coeff j := rfl

theorem deltaU_z (j : ℤ) : deltaU R (z j) = (j : R[X]) • (z j : U R) := by
  apply Subtype.ext
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro k
  by_cases h : k = j
  · subst k
    simp only [coeff_deltaU, coe_z_apply, coe_smul_z_apply, ite_true]
  · simp only [coeff_deltaU, coe_z_apply, coe_smul_z_apply, ite_eq_right h, mul_zero]

theorem deltaU_mul (f g : U R) :
    deltaU R (f * g) = f * deltaU R g + g * deltaU R f := (deltaU R).leibniz f g

theorem deltaU_one : deltaU R 1 = 0 := (deltaU R).map_one_eq_zero

theorem U_ext {f g : U R}
    (h : ∀ j, (f : (R[X])[T;T⁻¹]).coeff j = (g : (R[X])[T;T⁻¹]).coeff j) : f = g :=
  Subtype.ext (AddMonoidAlgebra.ext (Finsupp.ext h))

theorem coeff_smul (p : R[X]) (f : U R) (j : ℤ) :
    ((p • f : U R) : (R[X])[T;T⁻¹]).coeff j = p * (f : (R[X])[T;T⁻¹]).coeff j := rfl

/-- A coordinate submodule cut out by vanishing on a predicate. -/
def coordMod (P : ℤ → Prop) : Submodule R[X] (U R) where
  carrier := {f | ∀ j, P j → (f : (R[X])[T;T⁻¹]).coeff j = 0}
  zero_mem' := by intro j _; rfl
  add_mem' := by
    intro f g hf hg j hj
    change (f : (R[X])[T;T⁻¹]).coeff j + (g : (R[X])[T;T⁻¹]).coeff j = 0
    rw [hf j hj, hg j hj, add_zero]
  smul_mem' := by
    intro p f hf j hj
    rw [coeff_smul, hf j hj, mul_zero]

/-- The coordinate piece of index `j`. -/
def idxPiece (j : ℤ) : Submodule R[X] (U R) := coordMod (fun i => i ≠ j)
/-- The head coordinate module of a finite index set. -/
def headMod (H : Finset ℤ) : Submodule R[X] (U R) := coordMod (fun j => j ∉ H)
/-- The coordinate tail module `{|j| > N}`. -/
def tailMod (N : ℕ) : Submodule R[X] (U R) := coordMod (fun j => j.natAbs ≤ N)

/-- Homogeneous polynomial degree pieces, as additive subgroups. -/
def reesPiece (n : ℕ) : AddSubgroup (U R) where
  carrier := {f | ∀ j, (f : (R[X])[T;T⁻¹]).coeff j =
    Polynomial.C (((f : (R[X])[T;T⁻¹]).coeff j).coeff n) * X ^ n}
  zero_mem' := by intro j; simp only [Subalgebra.coe_zero, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply, Polynomial.coeff_zero, Polynomial.C_0, zero_mul]
  add_mem' := by
    intro f g hf hg j
    change (f : (R[X])[T;T⁻¹]).coeff j + (g : (R[X])[T;T⁻¹]).coeff j = _
    simp only [Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      Polynomial.coeff_add, Polynomial.C_add, add_mul]
    rw [← hf j, ← hg j]
  neg_mem' := by
    intro f hf j
    change -(f : (R[X])[T;T⁻¹]).coeff j = _
    simp only [Subalgebra.coe_neg, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply,
      Polynomial.coeff_neg, Polynomial.C_neg, neg_mul]
    rw [← hf j]

theorem deltaU_mem_JN {N : ℕ} {f : U R} (hf : f ∈ JN N) : deltaU R f ∈ JN N := by
  apply (mem_JN_iff N _).mpr
  intro j
  rw [coeff_deltaU]
  exact dvd_mul_of_dvd_right ((mem_JN_iff N _).mp hf j) _

theorem deltaU_smul (p : R[X]) (f : U R) : deltaU R (p • f) = p • deltaU R f :=
  (deltaU R).map_smul p f

theorem deltaU_mem_idxPiece {j : ℤ} {f : U R} (hf : f ∈ idxPiece j) :
    deltaU R f = (j : R[X]) • f := by
  apply U_ext
  intro i
  rw [coeff_deltaU, coeff_smul]
  by_cases hi : i = j
  · rw [hi]
  · rw [hf i hi, mul_zero, mul_zero]

theorem deltaU_mem_reesPiece {n : ℕ} {f : U R} (hf : f ∈ reesPiece n) :
    deltaU R f ∈ reesPiece n := by
  intro j
  rw [coeff_deltaU, ← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, Polynomial.C_mul]
  rw [mul_assoc, ← hf j]

theorem deltaU_mem_headMod {H : Finset ℤ} {f : U R} (hf : f ∈ headMod H) :
    deltaU R f ∈ headMod H := by
  intro j hj
  rw [coeff_deltaU, hf j hj, mul_zero]

theorem deltaU_mem_tailMod {N : ℕ} {f : U R} (hf : f ∈ tailMod N) :
    deltaU R f ∈ tailMod N := by
  intro j hj
  rw [coeff_deltaU, hf j hj, mul_zero]

/-- Coordinate multipliers preserve the divisibility defining the Rees algebra. -/
def diagU (lam : ℤ → R[X]) : U R →ₗ[R[X]] U R where
  toFun f := ⟨diagL lam f, (mem_U_iff _).mpr (fun j =>
    dvd_mul_of_dvd_right ((mem_U_iff _).mp f.property j) (lam j))⟩
  map_add' f g := Subtype.ext ((diagL lam).map_add f g)
  map_smul' p f := Subtype.ext ((diagL lam).map_smul p f)

theorem coeff_diagU (lam : ℤ → R[X]) (f : U R) (j : ℤ) :
    ((diagU lam f : U R) : (R[X])[T;T⁻¹]).coeff j =
      lam j * (f : (R[X])[T;T⁻¹]).coeff j := rfl

/-- The head projection for a finite signed-index set. -/
def PH (H : Finset ℤ) : U R →ₗ[R[X]] U R := diagU (fun j => if j ∈ H then 1 else 0)

theorem coeff_PH (H : Finset ℤ) (f : U R) (j : ℤ) :
    ((PH (R := R) H f : U R) : (R[X])[T;T⁻¹]).coeff j =
      if j ∈ H then (f : (R[X])[T;T⁻¹]).coeff j else 0 := by
  change (if j ∈ H then (1 : R[X]) else 0) * _ = _
  split_ifs <;> simp only [one_mul, zero_mul]

theorem diagU_z (lam : ℤ → R[X]) (j : ℤ) :
    diagU lam (z j : U R) = lam j • (z j : U R) :=
  Subtype.ext ((diagL_single lam j (X ^ j.natAbs)).trans
    (AddMonoidAlgebra.smul_single' (lam j) j (X ^ j.natAbs)).symm)

theorem PH_z (H : Finset ℤ) (j : ℤ) :
    PH (R := R) H (z j : U R) = if j ∈ H then (z j : U R) else 0 := by
  rw [PH, diagU_z]
  split_ifs <;> simp only [one_smul, zero_smul]

theorem PH_comp_PH (H : Finset ℤ) : (PH (R := R) H : U R →ₗ[R[X]] U R) ∘ₗ PH (R := R) H = PH (R := R) H := by
  apply LinearMap.ext
  intro f
  apply U_ext
  intro j
  simp only [LinearMap.comp_apply, coeff_PH]
  split_ifs <;> rfl

theorem PH_comp_one_sub (H : Finset ℤ) :
    (PH (R := R) H : U R →ₗ[R[X]] U R) ∘ₗ ((1 : U R →ₗ[R[X]] U R) - PH (R := R) H : U R →ₗ[R[X]] U R) = 0 := by
  rw [LinearMap.comp_sub, show (1 : U R →ₗ[R[X]] U R) = LinearMap.id from rfl,
    LinearMap.comp_id, PH_comp_PH, sub_self]

theorem one_sub_comp_PH (H : Finset ℤ) :
    ((1 : U R →ₗ[R[X]] U R) - (PH (R := R) H : U R →ₗ[R[X]] U R) : U R →ₗ[R[X]] U R) ∘ₗ PH (R := R) H = 0 := by
  rw [LinearMap.sub_comp, show (1 : U R →ₗ[R[X]] U R) = LinearMap.id from rfl,
    LinearMap.id_comp, PH_comp_PH, sub_self]

theorem deltaU_eq_diagU : (deltaU R).toLinearMap = diagU (fun k => (k : R[X])) := by
  apply LinearMap.ext
  intro f
  apply U_ext
  intro j
  rfl

/-- The diagonal algebra representation on the finite Rees core. -/
def diagAlgHom : (ℤ → R[X]) →ₐ[R[X]] Module.End R[X] (U R) where
  toFun := diagU
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply U_ext
    intro j
    simp only [coeff_diagU, Pi.zero_apply, zero_mul, LinearMap.zero_apply,
      Subalgebra.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  map_one' := by
    apply LinearMap.ext
    intro f
    apply U_ext
    intro j
    simp only [coeff_diagU, Pi.one_apply, one_mul, Module.End.one_apply]
  map_add' lam mu := by
    apply LinearMap.ext
    intro f
    apply U_ext
    intro j
    simp only [coeff_diagU, Pi.add_apply, LinearMap.add_apply,
      Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul]
  map_mul' lam mu := by
    apply LinearMap.ext
    intro f
    apply U_ext
    intro j
    simp only [coeff_diagU, Pi.mul_apply, Module.End.mul_apply]
    ring
  commutes' p := by
    apply LinearMap.ext
    intro f
    apply U_ext
    intro j
    change p * (f : (R[X])[T;T⁻¹]).coeff j =
      ((p • f : U R) : (R[X])[T;T⁻¹]).coeff j
    rfl

/-- Polynomial symbols use signed integer eigenvalues. -/
def qDelta (sym : Polynomial R) : Module.End R[X] (U R) :=
  Polynomial.aeval (deltaU R).toLinearMap (sym.map (algebraMap R R[X]))

theorem qDelta_eq_diagU (sym : Polynomial R) :
    qDelta sym = diagU (fun k => Polynomial.C (sym.eval (k : R))) := by
  unfold qDelta
  rw [deltaU_eq_diagU]
  have h := Polynomial.aeval_algHom_apply (diagAlgHom (R := R))
    (fun j : ℤ => (j : R[X])) (sym.map (algebraMap R R[X]))
  refine h.trans ?_
  change diagU _ = diagU _
  congr 1
  funext k
  rw [Polynomial.aeval_pi_apply₂]
  change (sym.map Polynomial.C).eval (k : R[X]) = Polynomial.C (sym.eval (k : R))
  rw [← Polynomial.C_eq_intCast, Polynomial.eval_map_apply]

theorem qDelta_z (sym : Polynomial R) (j : ℤ) :
    qDelta sym (z j : U R) = Polynomial.C (sym.eval (j : R)) • (z j : U R) := by
  rw [qDelta_eq_diagU, diagU_z]

theorem diagU_comm_diagU (lam mu : ℤ → R[X]) :
    diagU lam ∘ₗ diagU mu = diagU mu ∘ₗ diagU lam := by
  apply LinearMap.ext
  intro f
  apply U_ext
  intro j
  simp only [LinearMap.comp_apply, coeff_diagU]
  ring

theorem PH_comm_diagU (H : Finset ℤ) (lam : ℤ → R[X]) :
    PH (R := R) H ∘ₗ diagU lam = diagU lam ∘ₗ PH (R := R) H := diagU_comm_diagU _ _

theorem PH_comm_deltaU (H : Finset ℤ) :
    PH (R := R) H ∘ₗ (deltaU R).toLinearMap = (deltaU R).toLinearMap ∘ₗ PH (R := R) H := by
  rw [deltaU_eq_diagU]
  exact PH_comm_diagU H _

theorem PH_comm_qDelta (H : Finset ℤ) (sym : Polynomial R) :
    PH (R := R) H ∘ₗ qDelta sym = qDelta sym ∘ₗ PH (R := R) H := by
  rw [qDelta_eq_diagU]
  exact PH_comm_diagU H _

theorem PH_qDelta_tail (H : Finset ℤ) (sym : Polynomial R) :
    PH (R := R) H ∘ₗ qDelta sym ∘ₗ ((1 : U R →ₗ[R[X]] U R) - PH (R := R) H : U R →ₗ[R[X]] U R) = 0 := by
  rw [← LinearMap.comp_assoc, PH_comm_qDelta, LinearMap.comp_assoc, PH_comp_one_sub, LinearMap.comp_zero]

theorem PH_add_qDelta_tail (H : Finset ℤ) (sym : Polynomial R)
    (L : Module.End R[X] (U R)) :
    PH (R := R) H ∘ₗ (qDelta sym + L) ∘ₗ ((1 : U R →ₗ[R[X]] U R) - PH (R := R) H : U R →ₗ[R[X]] U R) =
      PH (R := R) H ∘ₗ L ∘ₗ ((1 : U R →ₗ[R[X]] U R) - PH (R := R) H : U R →ₗ[R[X]] U R) := by
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
  have hz := DFunLike.congr_fun (PH_qDelta_tail H sym) f
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
  rw [hz, zero_add]

/-- Raw specialization of the coordinates at `t`. -/
def specCoeff (t : R) (f : U R) : ℤ → R :=
  fun k => ((f : (R[X])[T;T⁻¹]).coeff k).eval t

/-- Raw head projection of a coefficient sequence. -/
def rawHead (H : Finset ℤ) (a : ℤ → R) : ℤ → R := fun k => if k ∈ H then a k else 0

/-- Raw diagonal multiplier of a coefficient sequence. -/
def rawDiag (lam : ℤ → R) (a : ℤ → R) : ℤ → R := fun k => lam k * a k

theorem specCoeff_deltaU (t : R) (f : U R) :
    specCoeff t (deltaU R f) = rawDiag (fun k => (k : R)) (specCoeff t f) := by
  funext k
  simp only [specCoeff, rawDiag, coeff_deltaU, Polynomial.eval_mul,
    ← Polynomial.C_eq_intCast, Polynomial.eval_C]

theorem specCoeff_qDelta (t : R) (sym : Polynomial R) (f : U R) :
    specCoeff t (qDelta sym f) = rawDiag (fun k => sym.eval (k : R)) (specCoeff t f) := by
  funext k
  simp only [specCoeff, rawDiag, qDelta_eq_diagU, coeff_diagU,
    Polynomial.eval_mul, Polynomial.eval_C]

theorem specCoeff_PH (t : R) (H : Finset ℤ) (f : U R) :
    specCoeff t (PH (R := R) H f) = rawHead H (specCoeff t f) := by
  funext k
  simp only [specCoeff, rawHead, coeff_PH]
  split_ifs <;> simp only [Polynomial.eval_zero]

theorem specCoeff_z (t : R) (j k : ℤ) :
    specCoeff t (z j : U R) k = if k = j then t ^ j.natAbs else 0 := by
  simp only [specCoeff, coe_z_apply]
  split_ifs <;> simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]

theorem rawHead_rawDiag (H : Finset ℤ) (lam : ℤ → R) (a : ℤ → R) :
    rawHead H (rawDiag lam a) = rawDiag lam (rawHead H a) := by
  funext k
  simp only [rawHead, rawDiag]
  split_ifs <;> simp only [mul_zero]

theorem rawHead_rawDiag_tail (H : Finset ℤ) (lam : ℤ → R) (a : ℤ → R) :
    rawHead H (rawDiag lam (a - rawHead H a)) = 0 := by
  funext k
  simp only [rawHead, rawDiag, Pi.sub_apply, Pi.zero_apply]
  split_ifs <;> simp only [sub_self, mul_zero]

/-- `rawDiag` is the pointwise product. -/
theorem rawDiag_eq_mul (lam a : ℤ → R) : rawDiag lam a = lam * a := rfl

/-- `rawHead` is the indicator of the head set. -/
theorem rawHead_eq_indicator (H : Finset ℤ) (a : ℤ → R) :
    rawHead H a = Set.indicator (↑H : Set ℤ) a := by
  funext k
  rw [Set.indicator_apply]
  unfold rawHead
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (Finset.mem_coe.mpr h1) h2
  · exact absurd (Finset.mem_coe.mp h2) h1
  · rfl

theorem deltaU_X_pow_smul_one (N : ℕ) :
    deltaU R ((X : R[X]) ^ (2 * N + 2) • (1 : U R)) = 0 := by
  rw [deltaU_smul, deltaU_one, smul_zero]

theorem X_pow_smul_one_ne_zero [Nontrivial R] (N : ℕ) :
    (X : R[X]) ^ (2 * N + 2) • (1 : U R) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : U R => (f : (R[X])[T;T⁻¹]).coeff 0) h
  simp only [coe_smul_one_apply, ite_true, Subalgebra.coe_zero,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  exact (Polynomial.monic_X_pow _).ne_zero hc

theorem deltaU_not_injOn_JN [Nontrivial R] (N : ℕ) :
    ¬ Set.InjOn (deltaU R) (JN (R := R) N : Set (U R)) := by
  intro h
  exact X_pow_smul_one_ne_zero N (h (X_pow_smul_one_mem_JN N)
    (JN N).zero_mem (by rw [deltaU_X_pow_smul_one, map_zero]))

theorem tailMod_le_JN (N : ℕ) : (tailMod (R := R) N : Set (U R)) ⊆ (JN (R := R) N : Set (U R)) := by
  intro f hf
  apply (mem_JN_iff N f).mpr
  intro j
  by_cases hj : j.natAbs ≤ N
  · rw [hf j hj]
    exact dvd_zero _
  · rw [show max j.natAbs (2 * N + 2 - j.natAbs) = j.natAbs by omega]
    exact (mem_U_iff _).mp f.property j

theorem X_pow_smul_one_not_mem_tailMod [Nontrivial R] (N : ℕ) :
    (X : R[X]) ^ (2 * N + 2) • (1 : U R) ∉ tailMod N := by
  intro hf
  have hc := hf 0 (by simp only [Int.natAbs_zero, Nat.zero_le])
  rw [coe_smul_one_apply, ite_eq_left rfl] at hc
  exact (Polynomial.monic_X_pow _).ne_zero hc

/-- The head image of `J_N` under any head projection stays in `J_N`. -/
theorem PH_mem_JN (H : Finset ℤ) {N : ℕ} {f : U R} (hf : f ∈ JN N) : PH H f ∈ JN N := by
  apply (mem_JN_iff N _).mpr
  intro j
  rw [coeff_PH]
  split_ifs
  · exact (mem_JN_iff N _).mp hf j
  · exact dvd_zero _

/-- Every coefficient of an element of `J_N` is divisible by `X ^ (aN N k + |k|)`. -/
theorem head_coeff_dvd_of_mem_JN {N : ℕ} {f : U R}
    (hf : f ∈ JN N) (k : ℤ) :
    (X : R[X]) ^ (aN N k + k.natAbs) ∣
      ((f : U R) : (R[X])[T;T⁻¹]).coeff k := by
  convert (mem_JN_iff N _).mp hf k using 1
  congr 1
  unfold aN
  omega

/-- The divisible head image of a product with a tail-ideal factor. -/
theorem head_coeff_dvd_PH_mul_tail (H : Finset ℤ) {N : ℕ} (b : U R) {t : U R}
    (ht : t ∈ JN N) (k : ℤ) :
    (X : R[X]) ^ (aN N k + k.natAbs) ∣
      ((PH H (b * t) : U R) : (R[X])[T;T⁻¹]).coeff k :=
  head_coeff_dvd_of_mem_JN (PH_mem_JN H ((JN N).mul_mem_left b ht)) k

theorem no_inv_X_pow [Nontrivial R] {a : ℕ} (ha : 1 ≤ a) :
    ¬ ∃ f : U R, (X : R[X]) ^ a • f = 1 := by
  rintro ⟨f, hf⟩
  have hc := congrArg (fun g : U R => ((g : (R[X])[T;T⁻¹]).coeff 0).eval 0) hf
  rw [coeff_smul, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    zero_pow (by omega : a ≠ 0), zero_mul] at hc
  have h1 := coe_smul_one_apply (R := R) (1 : R[X]) 0
  rw [one_smul, ite_eq_left rfl] at h1
  rw [h1, Polynomial.eval_one] at hc
  exact zero_ne_one hc

theorem no_inv_X_pow_aN [Nontrivial R] (N : ℕ) {k : ℤ} (hk : k.natAbs ≤ N) :
    ¬ ∃ f : U R, (X : R[X]) ^ aN N k • f = 1 := by
  apply no_inv_X_pow
  unfold aN
  omega

theorem qDelta_bijOn_tail (sym : Polynomial R) {N : ℕ}
    (hunit : ∀ k : ℤ, N < k.natAbs → IsUnit (sym.eval (k : R))) :
    Set.BijOn (qDelta sym) (tailMod (R := R) N : Set (U R)) (tailMod (R := R) N : Set (U R)) := by
  refine Set.BijOn.mk ?_ ?_ ?_
  · intro f hf j hj
    rw [qDelta_eq_diagU, coeff_diagU, hf j hj, mul_zero]
  · intro f hf g hg hfg
    apply U_ext
    intro j
    by_cases hj : N < j.natAbs
    · have hc := congrArg (fun v : U R => (v : (R[X])[T;T⁻¹]).coeff j) hfg
      rw [qDelta_eq_diagU, coeff_diagU, coeff_diagU] at hc
      exact ((hunit j hj).map Polynomial.C).mul_left_cancel hc
    · rw [hf j (by omega), hg j (by omega)]
  · intro f hf
    classical
    let lam : ℤ → R[X] := fun k => if hk : N < k.natAbs then
      Polynomial.C (Classical.choose ((hunit k hk).exists_right_inv)) else 0
    refine ⟨diagU lam f, ?_, ?_⟩
    · intro j hj
      rw [coeff_diagU, hf j hj, mul_zero]
    · apply U_ext
      intro j
      rw [qDelta_eq_diagU, coeff_diagU, coeff_diagU]
      by_cases hj : N < j.natAbs
      · dsimp only [lam]
        rw [dite_eq_left hj, ← mul_assoc, ← Polynomial.C_mul,
          Classical.choose_spec ((hunit j hj).exists_right_inv), Polynomial.C_1, one_mul]
      · rw [hf j (by omega), mul_zero, mul_zero]

theorem isUnit_of_surjOn_tail (sym : Polynomial R) {N : ℕ} :
    Set.SurjOn (qDelta sym) (tailMod (R := R) N : Set (U R)) (tailMod (R := R) N : Set (U R)) →
      ∀ k : ℤ, N < k.natAbs → IsUnit (sym.eval (k : R)) := by
  intro h k hk
  have hz : (z k : U R) ∈ tailMod N := by
    intro j hj
    rw [coe_z_apply, ite_eq_right (show j ≠ k by intro he; subst j; omega)]
  obtain ⟨f, _, hf⟩ := h hz
  obtain ⟨p, hp⟩ := (mem_U_iff _).mp f.property k
  have hc := congrArg (fun v : U R => (v : (R[X])[T;T⁻¹]).coeff k) hf
  rw [qDelta_eq_diagU, coeff_diagU, coe_z_apply, ite_eq_left rfl, hp] at hc
  have hcoeff := congrArg (fun q : R[X] => q.coeff k.natAbs) hc
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', ite_eq_left le_rfl,
    Nat.sub_self, Polynomial.coeff_X_pow_self] at hcoeff
  exact IsUnit.of_mul_eq_one (p.coeff 0) hcoeff

/-- The tail-inverse criterion. -/
theorem qDelta_bijOn_tail_iff (sym : Polynomial R) {N : ℕ} :
    Set.BijOn (qDelta sym) (tailMod (R := R) N : Set (U R)) (tailMod (R := R) N : Set (U R)) ↔
      ∀ k : ℤ, N < k.natAbs → IsUnit (sym.eval (k : R)) :=
  ⟨fun h => isUnit_of_surjOn_tail sym h.surjOn, qDelta_bijOn_tail sym⟩

/-- Over a `ℚ`-algebra the Euler derivation is bijective on the coordinate tail. -/
theorem deltaU_bijOn_tail [Algebra ℚ R] (N : ℕ) :
    Set.BijOn (deltaU R) (tailMod (R := R) N : Set (U R)) (tailMod (R := R) N : Set (U R)) := by
  have hunit : ∀ k : ℤ, N < k.natAbs → IsUnit ((X : R[X]).eval (k : R)) := by
    intro k hk
    rw [Polynomial.eval_X]
    have hk0 : (k : ℚ) ≠ 0 := by
      exact_mod_cast (show k ≠ 0 by intro h; subst k; simp only [Int.natAbs_zero] at hk; omega)
    simpa only [map_intCast] using (IsUnit.mk0 (k : ℚ) hk0).map (algebraMap ℚ R)
  have h := qDelta_bijOn_tail (X : R[X]) hunit
  simpa only [qDelta, Polynomial.map_X, Polynomial.aeval_X, Derivation.coeFn_coe] using h

theorem z_ne_zero [Nontrivial R] (j : ℤ) : (z j : U R) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : U R => (f : (R[X])[T;T⁻¹]).coeff j) h
  simp only [coe_z_apply, ite_true, Subalgebra.coe_zero,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  exact (Polynomial.monic_X_pow _).ne_zero hc

end Selection

/-! ### Applied corollaries for default-instance consumers

Stated outside the scope of the local instance selection, under the default instances of `U R`. -/

section Applied

variable {R : Type*} [CommRing R]

theorem PH_apply_sub_PH_apply (H : Finset ℤ) (f : U R) : PH (R := R) H (f - PH (R := R) H f) = 0 :=
  LinearMap.congr_fun (PH_comp_one_sub H) f

theorem PH_sub_apply (H : Finset ℤ) (f : U R) : PH (R := R) H f - PH (R := R) H (PH (R := R) H f) = 0 :=
  LinearMap.congr_fun (one_sub_comp_PH H) f

theorem PH_qDelta_tail_apply (H : Finset ℤ) (sym : Polynomial R) (f : U R) : PH (R := R) H (qDelta sym (f - PH (R := R) H f)) = 0 :=
  LinearMap.congr_fun (PH_qDelta_tail H sym) f

end Applied

end RadiiPolynomial.Rees.Laurent
