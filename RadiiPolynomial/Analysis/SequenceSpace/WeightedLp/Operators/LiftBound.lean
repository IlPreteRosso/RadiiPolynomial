import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.Schur
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Finite synthesis and bounded extension on weighted ℓᵖ

`LiftBound` is the bound on finite atom sums. For `p ≠ ∞`, its extension into a complete
normed target is specified by `liftCLM`, computation on atoms, a norm bound, uniqueness and
`liftBound_iff`. Uniqueness and the converse do not assume target completeness. Atom-span
density for `p ≠ ∞` is `dense_span_single`.

The construction and uniqueness laws use a normed scalar field; operator-norm faces separately
require nontrivially normed scalars. The kernel construction uses complete scalars. Its coordinate series
converges unconditionally. Comparison with the Schur realization uses the same complete
normed-field frame; absolute row summability is a separate `RCLike` result. At `p = 1`, the exact criteria are the column bound and
`ColSum`. No specialized diagonal, top, Schur, Laurent or head/tail producer is exported here.
-/

open scoped ENNReal NNReal Topology
open Filter

noncomputable section

namespace RadiiPolynomial.WeightedLp

/-! ### Density for the finite-synthesis contract -/

section Density

variable {𝕜 : Type*} [NormedField 𝕜] {M : Type*} {E : M → Type*}
  [∀ m, NormedAddCommGroup (E m)] [∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Density of the span of the scalar atoms** for `p ≠ ∞`. -/
theorem dense_span_single [DecidableEq M] (hp : p ≠ ∞) :
    Dense (Submodule.span 𝕜 (Set.range fun m => single (E := E) (p := p) m (1 : 𝕜)) :
      Set (WeightedLp M E p)) := by
  refine fun x => mem_closure_of_tendsto (lp.hasSum_single hp x) (Eventually.of_forall fun s => ?_)
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [← equiv_coeff x m, ← single, single_eq_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

end Density

/-! ### Finite sums of scalar atoms and their norms -/

section AtomSums

variable {𝕜 : Type*} [NormedField 𝕜] {J : Type*} {E : J → Type*}
  [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)] [FiberTrivialization 𝕜 J E]
  {p : ℝ≥0∞}

variable [DecidableEq J]

/-- The atom with the coordinate `coeff x j` is Mathlib's `lp.single p j (x j)`. -/
theorem single_coeff (x : WeightedLp J E p) (j : J) :
    single (E := E) (p := p) j (coeff x j) = lp.single p j (x j) := by
  rw [single, equiv_coeff]

variable [Fact (1 ≤ p)]

/-- **The atom expansion** `x = ∑ j, single j (coeff x j)` for `p ≠ ∞`. -/
theorem hasSum_single_coeff (hp : p ≠ ∞) (x : WeightedLp J E p) :
    HasSum (fun j => single (E := E) (p := p) j (coeff x j)) x := by
  simpa only [single_coeff] using lp.hasSum_single hp x

/-- The `p`-th power of the norm of a finite sum of atoms (`p ≠ ∞`). -/
theorem norm_sum_single_rpow (hp : p ≠ ∞) (s : Finset J) (c : J → 𝕜) :
    ‖∑ j ∈ s, single (E := E) (p := p) j (c j)‖ ^ p.toReal =
      ∑ j ∈ s, (‖c j‖ * FiberTrivialization.weight (E := E) j) ^ p.toReal := by
  have hp0 := exponent_toReal_pos hp
  rw [lp.norm_rpow_eq_tsum hp0, tsum_eq_sum (s := s)]
  · exact Finset.sum_congr rfl fun j hj => by rw [norm_apply_eq, coeff_sum_single, ite_eq_left hj]
  · intro j hj
    rw [norm_apply_eq, coeff_sum_single, ite_eq_right hj, norm_zero, zero_mul,
      Real.zero_rpow hp0.ne']

omit [Fact (1 ≤ p)] in
/-- The `p = 1` face: `‖∑ j ∈ s, single j (c j)‖₁ = ∑ j ∈ s, ‖c j‖ ω_j`. -/
@[simp] theorem norm_sum_single_one (s : Finset J) (c : J → 𝕜) :
    ‖∑ j ∈ s, single (E := E) (p := 1) j (c j)‖ =
      ∑ j ∈ s, ‖c j‖ * FiberTrivialization.weight (E := E) j := by
  simpa using norm_sum_single_rpow (E := E) (p := 1) ENNReal.one_ne_top s c


end AtomSums

/-! ### The predicates -/

section Predicates

variable {𝕜 : Type*} [NormedField 𝕜] {I J : Type*} [DecidableEq J]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **The finite lift test** (layer 1): `0 ≤ C`, and for every finite `s` and scalars `c`,
`‖∑ j ∈ s, c j • y j‖ ≤ C ‖∑ j ∈ s, single j (c j)‖` with the carrier norm of
`WeightedLp J E p` on the right. Well-typed at every exponent; for `p ≠ ∞` it is exactly the
existence of a bounded extension (`liftBound_iff`). A structure, not a class: an operator is not
canonical per carrier. -/
structure LiftBound (E : J → Type*) [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
    [FiberTrivialization 𝕜 J E] (p : ℝ≥0∞) [Fact (1 ≤ p)] (y : J → Y) (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  le : ∀ (s : Finset J) (c : J → 𝕜),
    ‖∑ j ∈ s, c j • y j‖ ≤ C * ‖∑ j ∈ s, single (E := E) (p := p) j (c j)‖

/-- The columns of a kernel `K : I → J → 𝕜` as elements of the target carrier, given their
memberships: `kcol K hK j = (i ↦ θ_i (K i j))`. -/
def kcol {F : I → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
    [FiberTrivialization 𝕜 I F] {p : ℝ≥0∞} (K : I → J → 𝕜)
    (hK : ∀ j, Memℓp (fun i => FiberTrivialization.equiv (E := F) i (K i j)) p) (j : J) :
    WeightedLp I F p :=
  ⟨_, hK j⟩

/-- **The kernel lift test**: every column of `K` lies in the target carrier
(`memℓp_col`, bundled, so consumers never discharge it) and the columns pass the finite lift
test with constant `C`. -/
structure KernelLiftBound (E : J → Type*) [∀ j, NormedAddCommGroup (E j)]
    [∀ j, NormedSpace 𝕜 (E j)] [FiberTrivialization 𝕜 J E] (F : I → Type*)
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)] [FiberTrivialization 𝕜 I F]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : I → J → 𝕜) (C : ℝ) : Prop where
  memℓp_col : ∀ j, Memℓp (fun i => FiberTrivialization.equiv (E := F) i (K i j)) p
  toLiftBound : LiftBound E p (kcol K memℓp_col) C

end Predicates

/-! ### Layer 1: the converse, the extension and uniqueness -/

section Layer1

variable {𝕜 : Type*} [NormedField 𝕜] {J : Type*} [DecidableEq J]
  {E : J → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
  [FiberTrivialization 𝕜 J E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {y : J → Y} {C C' : ℝ}

/-- A larger constant passes the test. -/
theorem LiftBound.mono (h : LiftBound E p y C) (hC : C ≤ C') : LiftBound E p y C' :=
  ⟨h.nonneg.trans hC, fun s c =>
    (h.le s c).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))⟩


/-- Every bounded operator is the series of its atom images (`p ≠ ∞`). -/
theorem hasSum_apply_single (hp : p ≠ ∞) (T : WeightedLp J E p →L[𝕜] Y) (x : WeightedLp J E p) :
    HasSum (fun j => coeff x j • T (single j 1)) (T x) := by
  convert T.hasSum (hasSum_single_coeff hp x) using 2 with j
  rw [single_eq_smul j (coeff x j), map_smul]

/-- The bound carried by the test along any convergent atom series (`p ≠ ∞`). -/
theorem LiftBound.norm_le_of_hasSum (hp : p ≠ ∞) (h : LiftBound E p y C) (x : WeightedLp J E p)
    {z : Y} (hz : HasSum (fun j => coeff x j • y j) z) : ‖z‖ ≤ C * ‖x‖ :=
  le_of_tendsto_of_tendsto' (Filter.Tendsto.norm hz)
    ((Filter.Tendsto.norm (hasSum_single_coeff hp x)).const_mul C) fun s => h.le s (coeff x)

/-- **Uniqueness** (`p ≠ ∞`, no completeness): bounded operators agreeing on the atoms agree. -/
theorem ext_single (hp : p ≠ ∞) ⦃T S : WeightedLp J E p →L[𝕜] Y⦄
    (hTS : ∀ j, T (single j 1) = S (single j 1)) : T = S :=
  ContinuousLinearMap.ext_on (dense_span_single hp) (by rintro _ ⟨j, rfl⟩; exact hTS j)


section Extension

variable [CompleteSpace Y]

/-- The atom series `∑ j, coeff x j • y j` converges (`p ≠ ∞`, complete target): its partial
sums are Cauchy because those of the atom expansion of `x` are. -/
theorem LiftBound.summable (hp : p ≠ ∞) (h : LiftBound E p y C) (x : WeightedLp J E p) :
    Summable fun j => coeff x j • y j := by
  have hC1 : 0 < C + 1 := by linarith [h.nonneg]
  refine summable_iff_cauchySeq_finset.2 (cauchySeq_finset_iff_vanishing_norm.2 fun ε hε => ?_)
  have hx : Tendsto (fun s : Finset J => ∑ j ∈ s, single (E := E) (p := p) j (coeff x j)) atTop
      (𝓝 x) := hasSum_single_coeff hp x
  obtain ⟨s, hs⟩ := cauchySeq_finset_iff_vanishing_norm.1 hx.cauchySeq (ε / (C + 1))
    (div_pos hε hC1)
  exact ⟨s, fun t ht => (h.le t (coeff x)).trans_lt <|
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)).trans_lt
      ((lt_div_iff₀' hC1).1 (hs t ht))⟩

/-- The linear map underlying `liftCLM`. -/
def liftLM (hp : p ≠ ∞) (h : LiftBound E p y C) : WeightedLp J E p →ₗ[𝕜] Y where
  toFun x := ∑' j, coeff x j • y j
  map_add' x x' := by
    simp only [coeff_add, Pi.add_apply, add_smul]
    exact (h.summable hp x).tsum_add (h.summable hp x')
  map_smul' c x := by
    simp only [coeff_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
    exact (h.summable hp x).tsum_const_smul c

/-- **The extension** (`p ≠ ∞`, complete target): `x ↦ ∑' j, coeff x j • y j`, bounded by `C`. -/
def liftCLM (hp : p ≠ ∞) (h : LiftBound E p y C) : WeightedLp J E p →L[𝕜] Y :=
  (liftLM hp h).mkContinuous C fun x => h.norm_le_of_hasSum hp x (h.summable hp x).hasSum

theorem liftCLM_apply (hp : p ≠ ∞) (h : LiftBound E p y C) (x : WeightedLp J E p) :
    liftCLM hp h x = ∑' j, coeff x j • y j :=
  rfl

theorem hasSum_liftCLM (hp : p ≠ ∞) (h : LiftBound E p y C) (x : WeightedLp J E p) :
    HasSum (fun j => coeff x j • y j) (liftCLM hp h x) :=
  (h.summable hp x).hasSum

@[simp] theorem liftCLM_single (hp : p ≠ ∞) (h : LiftBound E p y C) (j : J) (r : 𝕜) :
    liftCLM hp h (single j r) = r • y j := by
  rw [liftCLM_apply, tsum_eq_single j fun k hk => by rw [coeff_single, Pi.single_eq_of_ne hk, zero_smul],
    coeff_single_self]



/-- Every bounded operator with the prescribed atom images is the extension. -/
theorem eq_liftCLM (hp : p ≠ ∞) (h : LiftBound E p y C) (T : WeightedLp J E p →L[𝕜] Y)
    (hT : ∀ j, T (single j 1) = y j) : T = liftCLM hp h :=
  ext_single hp fun j => by rw [hT, liftCLM_single, one_smul]


end Extension

end Layer1

/-! ### Operator-norm faces of the generic extension -/

section Layer1OpNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {J : Type*} [DecidableEq J]
  {E : J → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
  [FiberTrivialization 𝕜 J E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {y : J → Y} {C C' : ℝ}

/-- **The converse, at every exponent (`∞` included)**: the atom images of a bounded operator pass
the finite lift test with its operator norm. -/
theorem LiftBound.of_clm (T : WeightedLp J E p →L[𝕜] Y) :
    LiftBound E p (fun j => T (single j 1)) ‖T‖ where
  nonneg := norm_nonneg T
  le s c := by
    have hT : ∑ j ∈ s, c j • T (single j 1) = T (∑ j ∈ s, single (E := E) (p := p) j (c j)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [single_eq_smul j (c j), map_smul]
    rw [hT]
    exact T.le_opNorm _

/-- **The column principle at every finite exponent**: `‖T‖ ≤ C` iff the atom images of `T`
pass the finite lift test with `C` (no completeness of `Y`). -/
theorem opNorm_le_iff_liftBound (hp : p ≠ ∞) (T : WeightedLp J E p →L[𝕜] Y) (hC : 0 ≤ C) :
    ‖T‖ ≤ C ↔ LiftBound E p (fun j => T (single j 1)) C :=
  ⟨(LiftBound.of_clm T).mono, fun h =>
    T.opNorm_le_bound hC fun x => h.norm_le_of_hasSum hp x (hasSum_apply_single hp T x)⟩

section Complete

variable [CompleteSpace Y]

theorem norm_liftCLM_le (hp : p ≠ ∞) (h : LiftBound E p y C) : ‖liftCLM hp h‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ h.nonneg _

/-- **The universal property** (`p ≠ ∞`): the finite lift test holds iff a bounded operator with
the prescribed atom images and norm at most `C` exists. -/
theorem liftBound_iff (hp : p ≠ ∞) :
    LiftBound E p y C ↔
      0 ≤ C ∧ ∃ T : WeightedLp J E p →L[𝕜] Y, (∀ j, T (single j 1) = y j) ∧ ‖T‖ ≤ C := by
  refine ⟨fun h => ⟨h.nonneg, liftCLM hp h, fun j => by rw [liftCLM_single, one_smul],
    norm_liftCLM_le hp h⟩, ?_⟩
  rintro ⟨-, T, hT, hTC⟩
  rw [← funext hT]
  exact (LiftBound.of_clm T).mono hTC

end Complete

end Layer1OpNorm

/-! ### `p = 1`: the test is the column bound -/

section One

variable {𝕜 : Type*} [NormedField 𝕜] {J : Type*} [DecidableEq J]
  {E : J → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
  [FiberTrivialization 𝕜 J E] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {y : J → Y} {C : ℝ}

/-- **`p = 1`, any normed target: the finite lift test is the column bound** `‖y j‖ ≤ C ω_j`
(exact, one inequality per column). -/
theorem liftBound_one_iff :
    LiftBound E 1 y C ↔ 0 ≤ C ∧ ∀ j, ‖y j‖ ≤ C * FiberTrivialization.weight (E := E) j := by
  refine ⟨fun h => ⟨h.nonneg, fun j => ?_⟩, fun ⟨hC, hy⟩ => ⟨hC, fun s c => ?_⟩⟩
  · simpa [norm_single] using h.le {j} fun _ => 1
  · refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => (norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_left (hy j) (norm_nonneg _))).trans_eq ?_)
    rw [norm_sum_single_one, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

end One

/-! ### The kernel face -/

section KernelFace

variable {𝕜 : Type*} [NormedField 𝕜] {I J : Type*} [DecidableEq J]
  {E : J → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
  [FiberTrivialization 𝕜 J E]
  {F : I → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [FiberTrivialization 𝕜 I F] {p : ℝ≥0∞} [Fact (1 ≤ p)] {K : I → J → 𝕜} {C C' : ℝ}

omit [DecidableEq J] [Fact (1 ≤ p)] in
@[simp] theorem coeff_kcol
    (hK : ∀ j, Memℓp (fun i => FiberTrivialization.equiv (E := F) i (K i j)) p) (j : J) (i : I) :
    coeff (kcol K hK j) i = K i j :=
  FiberTrivialization.equiv_symm_apply_equiv i (K i j)

omit [DecidableEq J] [Fact (1 ≤ p)] in
theorem norm_kcol_apply
    (hK : ∀ j, Memℓp (fun i => FiberTrivialization.equiv (E := F) i (K i j)) p) (j : J) (i : I) :
    ‖kcol K hK j i‖ = ‖K i j‖ * FiberTrivialization.weight (E := F) i :=
  FiberTrivialization.norm_equiv_apply i (K i j)




variable (hp : p ≠ ∞)

section Complete

variable [CompleteSpace 𝕜]


end Complete

section RCLikeFaces

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : J → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
  [FiberTrivialization 𝕜 J E]
  {F : I → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [FiberTrivialization 𝕜 I F] {K : I → J → 𝕜}


end RCLikeFaces

end KernelFace

/-! ### `p = 1`: the exact kernel test -/

section KernelEndpoints

variable {𝕜 : Type*} [NormedField 𝕜] {I J : Type*} [DecidableEq J]
  {E : J → Type*} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
  [FiberTrivialization 𝕜 J E]
  {F : I → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [FiberTrivialization 𝕜 I F] {K : I → J → 𝕜} {C : ℝ}

omit [DecidableEq J] in
/-- At `p = 1` the normalized column sum of `K` at `j` is `‖kcol j‖₁ / ω_j`. -/
theorem hasSum_schurEntry_kcol
    (hK : ∀ j, Memℓp (fun i => FiberTrivialization.equiv (E := F) i (K i j)) 1) (j : J) :
    HasSum (fun i => schurEntry (FiberTrivialization.weight (E := F))
      (FiberTrivialization.weight (E := E)) K i j)
      (‖kcol K hK j‖ / FiberTrivialization.weight (E := E) j) := by
  have h := lp.hasSum_norm (p := 1) (by simp) (kcol K hK j)
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  simpa only [schurEntry, ← norm_kcol_apply hK] using h.div_const _

/-- **`p = 1`: the kernel test is the column Schur hypothesis** (exact). -/
theorem kernelLiftBound_one_iff :
    KernelLiftBound E F 1 K C ↔ 0 ≤ C ∧ ColSum (FiberTrivialization.weight (E := F))
      (FiberTrivialization.weight (E := E)) K C := by
  refine ⟨fun h => ?_, fun ⟨hC, hcol⟩ => ?_⟩
  · obtain ⟨hC, hy⟩ := liftBound_one_iff.1 h.toLiftBound
    refine ⟨hC, hC, fun j => (hasSum_schurEntry_kcol h.memℓp_col j).summable, fun j => ?_⟩
    rw [(hasSum_schurEntry_kcol h.memℓp_col j).tsum_eq]
    exact (div_le_iff₀ (FiberTrivialization.weight_pos j)).2 (hy j)
  · have hm : ∀ j, Memℓp (fun i => FiberTrivialization.equiv (E := F) i (K i j)) 1 := fun j =>
      memℓp_gen (((hcol.col_summable j).mul_right
        (FiberTrivialization.weight (E := E) j)).congr fun i => by
          rw [ENNReal.toReal_one, Real.rpow_one, FiberTrivialization.norm_equiv_apply, schurEntry,
            div_mul_cancel₀ _ (FiberTrivialization.weight_ne_zero j)])
    refine ⟨hm, liftBound_one_iff.2 ⟨hC, fun j => ?_⟩⟩
    have hj := hcol.col_le j
    rw [(hasSum_schurEntry_kcol hm j).tsum_eq] at hj
    exact (div_le_iff₀ (FiberTrivialization.weight_pos j)).1 hj

end KernelEndpoints

end RadiiPolynomial.WeightedLp
