import RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.LiftBound

/-!
# Checks for the two-layer membership API (`Operators/LiftBound.lean`)

One carrier, `WeightedLp ℕ (WeightedScalar ℝ w₂) p` with the weight `w₂ n = 2^n`.

* (i) `p = 1`: the two layers coincide. Two atom images `y₁ 0 = 1`, `y₁ 1 = -3`; the column test
  (`liftBound_one_iff`) gives the operator, the converse (`LiftBound.of_clm`) returns the column
  bound, and the operator norm is exactly `3/2`.
* (v) negative control at `p = ∞`: `LiftBound E ∞ y C` is well-typed, `liftCLM` is not available.
-/

open scoped ENNReal NNReal

noncomputable section

namespace RadiiPolynomial.WeightedLp.LiftBoundChecks

/-- The weight `2^n` on `ℕ`. -/
abbrev w₂ : ℕ → ℝ := fun n => 2 ^ n

local instance posWeight_w₂ : PosWeight w₂ := ⟨fun n => pow_pos two_pos n⟩

local notation "E₂" => WeightedScalar ℝ w₂

theorem weight_w₂ (n : ℕ) : FiberTrivialization.weight (E := E₂) n = 2 ^ n :=
  WeightedScalar.fiberTrivialization_weight n

theorem two_ne_top' : (2 : ℝ≥0∞) ≠ ∞ := by simp

/-! ### (i) `p = 1`: the two layers coincide -/

/-- Two atom images: `y₁ 0 = 1`, `y₁ 1 = -3`, zero elsewhere. -/
def y₁ : ℕ → ℝ := fun n => if n = 0 then 1 else if n = 1 then -3 else 0

/-- The column bound `‖y₁ n‖ ≤ (3/2) 2^n` (the whole layer-2 obligation at `p = 1`). -/
theorem y₁_col (n : ℕ) : ‖y₁ n‖ ≤ 3 / 2 * FiberTrivialization.weight (E := E₂) n := by
  rw [weight_w₂]
  rcases n with _ | _ | n
  · norm_num [y₁]
  · norm_num [y₁]
  · simp only [y₁, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_eq_right, norm_zero]
    positivity

theorem i_liftBound : LiftBound E₂ 1 y₁ (3 / 2) :=
  liftBound_one_iff.2 ⟨by norm_num, y₁_col⟩

/-- The operator of the column test has norm exactly `3/2`: the converse returns the column bound
at `n = 1`. -/
theorem i_norm_eq : ‖liftCLM ENNReal.one_ne_top i_liftBound‖ = 3 / 2 := by
  refine le_antisymm (norm_liftCLM_le _ _) ?_
  have h := (liftBound_one_iff.1 (LiftBound.of_clm (liftCLM ENNReal.one_ne_top i_liftBound))).2 1
  simp only [liftCLM_single, one_smul, weight_w₂] at h
  norm_num [y₁] at h
  linarith

/-- The round trip: the atom images of the operator are `y₁` again. -/
example (n : ℕ) : liftCLM ENNReal.one_ne_top i_liftBound (single n 1) = y₁ n := by
  rw [liftCLM_single, one_smul]


/-! ### (v) negative control at `p = ∞` -/

/-- The predicate is well-typed (and inhabited) at `p = ∞`. -/
example : LiftBound E₂ ∞ (fun _ : ℕ => (0 : ℝ)) 0 :=
  ⟨le_rfl, fun s c => by simp⟩

-- The finite-p constructor requires the impossible parameter `p ≠ ∞` at `p = ∞`.
/--
error: unsolved goals
h : LiftBound E₂ ∞ (fun x => 0) 0
⊢ False
-/
#guard_msgs in
example (h : LiftBound E₂ ∞ (fun _ : ℕ => (0 : ℝ)) 0) :
    WeightedLp ℕ E₂ ∞ →L[ℝ] ℝ :=
  liftCLM (by simp) h

end RadiiPolynomial.WeightedLp.LiftBoundChecks

end
