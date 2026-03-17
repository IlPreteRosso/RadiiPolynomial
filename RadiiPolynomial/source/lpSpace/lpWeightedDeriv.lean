import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Add
import RadiiPolynomial.source.lpSpace.lpWeighted

/-!
# Differentiability of `l1Weighted` constructions

This file contains differentiability and `fderiv` lemmas for `l1Weighted`:
- `differentiable_toSeq`: coordinate evaluation is differentiable (it's a CLM)
- `differentiable_mk_of_finSupp`: finitely-supported `lpWeighted.mk` is differentiable
- `fderiv_mk_of_finSupp_toSeq_tail`: fderiv vanishes on tail modes

These are separated from `lpWeighted.lean` because they are the only consumers
of `Mathlib.Analysis.Calculus.FDeriv.{Linear,Add}`.
-/

open scoped BigOperators Topology NNReal ENNReal Matrix

noncomputable section

namespace RadiiPolynomial

namespace l1Weighted

variable {ν : PosReal}

/-- `toSeq · n` is differentiable (it's a CLM). -/
@[fun_prop]
lemma differentiable_toSeq (n : ℕ) : Differentiable ℝ (fun a : l1Weighted ν => toSeq a n) :=
  (toSeq_CLM n).differentiable

/-- A finitely-supported function into `l1Weighted ν` is differentiable if each
coefficient function is differentiable. Decomposes as `Σ_k single_CLM k (f_k(a))`.
This is the key API for proving differentiability through `lpWeighted.mk`. -/
lemma differentiable_mk_of_finSupp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℕ → ℝ) (M : ℕ) (hsupp : ∀ a n, M < n → f a n = 0)
    (hf : ∀ a, lpWeighted.Mem ν 1 (f a))
    (hd : ∀ k : Fin (M + 1), Differentiable ℝ (fun a => f a k)) :
    Differentiable ℝ (fun a => lpWeighted.mk (f a) (hf a)) := by
  -- mk(f a) = Σ_k single_CLM k (f a k): both agree at each toSeq index.
  have hsum_eq : ∀ a, lpWeighted.mk (f a) (hf a) =
      ∑ k : Fin (M + 1), single_CLM (ν := ν) (k : ℕ) (f a k) := by
    intro a; apply lpWeighted.ext; intro n
    simp only [lpWeighted.mk_apply, toSeq_finset_sum, single_CLM_apply]
    simp only [single_toSeq]
    -- Goal: f a n = ∑ k : Fin (M+1), if n = ↑k then f a ↑k else 0
    by_cases hn : n ≤ M
    · -- Exactly one k has ↑k = n: the sum collapses to f a n
      rw [Finset.sum_eq_single ⟨n, by omega⟩
        (fun k _ hk => if_neg (by intro h; exact hk (Fin.ext h.symm)))
        (fun h => absurd (Finset.mem_univ _) h)]
      simp
    · -- n > M: no k has ↑k = n, so sum = 0 = f a n
      rw [hsupp a n (by omega)]
      exact (Finset.sum_eq_zero fun k _ => if_neg (by intro h; omega)).symm
  intro a; show DifferentiableAt ℝ (fun a => lpWeighted.mk (f a) (hf a)) a
  rw [show (fun a => lpWeighted.mk (f a) (hf a)) =
      fun a => ∑ k : Fin (M + 1), single_CLM (ν := ν) (↑k) (f a ↑k) from funext hsum_eq]
  exact DifferentiableAt.fun_sum fun (k : Fin (M + 1)) _ =>
    ((single_CLM (ν := ν) (↑k)).differentiable.comp (hd k)) a

/-- Fderiv of finitely-supported `lpWeighted.mk` vanishes on tail modes.
If `f a n = 0` for `n > M` and each `f · k` is differentiable, then
`toSeq((fderiv (mk ∘ f)) x h) n = 0` for `n > M`. -/
lemma fderiv_mk_of_finSupp_toSeq_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℕ → ℝ) (M : ℕ) (hsupp : ∀ a n, M < n → f a n = 0)
    (hf : ∀ a, lpWeighted.Mem ν 1 (f a))
    (hd : ∀ k : Fin (M + 1), Differentiable ℝ (fun a => f a k))
    (x h : E) (n : ℕ) (hn : M < n) :
    toSeq ((fderiv ℝ (fun a => lpWeighted.mk (f a) (hf a)) x) h) n = 0 := by
  -- The function is identically zero at mode n > M (since f a n = 0)
  -- So the coordinate function `a ↦ toSeq(mk(f a)) n` is constant 0
  have hzero_fn : (fun a => toSeq (lpWeighted.mk (f a) (hf a)) n) = fun _ => 0 :=
    funext fun a => by simp [hsupp a n hn]
  -- fderiv of constant = 0
  have hfderiv_zero : (fderiv ℝ (fun a => toSeq (lpWeighted.mk (f a) (hf a)) n) x) h = 0 := by
    rw [hzero_fn]; simp
  -- Connect: toSeq((fderiv (mk ∘ f) x) h) n = fderiv(a ↦ toSeq(mk(f a)) n) x h
  have hchain : toSeq ((fderiv ℝ (fun a => lpWeighted.mk (f a) (hf a)) x) h) n =
      (fderiv ℝ (fun a => toSeq (lpWeighted.mk (f a) (hf a)) n) x) h := by
    have : (fun a => toSeq (lpWeighted.mk (f a) (hf a)) n) =
        ⇑(toSeq_CLM (ν := ν) n) ∘ (fun a => lpWeighted.mk (f a) (hf a)) := rfl
    rw [this, fderiv_comp x (toSeq_CLM n).differentiableAt
      (differentiable_mk_of_finSupp f M hsupp hf hd x),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv]; rfl
  rw [hchain, hfderiv_zero]

end l1Weighted

end RadiiPolynomial

end
