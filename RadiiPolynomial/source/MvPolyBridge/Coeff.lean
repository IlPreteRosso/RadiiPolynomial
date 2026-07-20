import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.PowerSeries.Basic
import RadiiPolynomial.source.lpSpace.CauchyProduct

/-!
# Rational Coefficient Semantics for Multivariate Polynomials

Evaluates an `MvPolynomial` in rational formal power series and extracts coefficients.
Sequence inputs are the mathematical API; arrays are zero-padded certificate adapters.
-/

open RadiiPolynomial

noncomputable section

namespace MvPolyBridge

variable {L : ℕ}

/-- A rational sequence as a formal power series. -/
def seqToPowerSeries (a : ℕ → ℚ) : PowerSeries ℚ :=
  PowerSeries.mk a

/-- A rational array as a zero-padded formal power series. -/
def arrayToPowerSeries (arr : Array ℚ) : PowerSeries ℚ :=
  seqToPowerSeries fun n => arr.getD n 0

/-- Evaluate an `MvPolynomial` in rational formal power series. -/
def mvPolyToPowerSeries (p : MvPolynomial (Fin L) ℚ)
    (seqs : Fin L → PowerSeries ℚ) : PowerSeries ℚ :=
  MvPolynomial.eval₂ PowerSeries.C seqs p

/-- The `n`th coefficient after substituting rational sequences for the variables. -/
def mvPolyCoeff (p : MvPolynomial (Fin L) ℚ)
    (seqs : Fin L → ℕ → ℚ) (n : ℕ) : ℚ :=
  (PowerSeries.coeff (R := ℚ) n)
    (mvPolyToPowerSeries p fun i => seqToPowerSeries (seqs i))

/-- Array adapter for `mvPolyCoeff`. -/
def mvPolyCoeffQ (p : MvPolynomial (Fin L) ℚ)
    (arrs : Fin L → Array ℚ) (n : ℕ) : ℚ :=
  mvPolyCoeff p (fun i k => (arrs i).getD k 0) n

private lemma coeff_C_eq (r : ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.C (R := ℚ) r) = if n = 0 then r else 0 := by
  cases n with
  | zero => simp [PowerSeries.coeff_zero_C]
  | succ n => simp [PowerSeries.coeff_succ_C]

@[simp] lemma mvPolyCoeff_C (r : ℚ) (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff (MvPolynomial.C r) seqs n = if n = 0 then r else 0 := by
  simp only [mvPolyCoeff, mvPolyToPowerSeries, MvPolynomial.eval₂_C, coeff_C_eq]

@[simp] lemma mvPolyCoeff_zero (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff 0 seqs n = 0 := by
  rw [show (0 : MvPolynomial (Fin L) ℚ) = MvPolynomial.C 0 from by simp, mvPolyCoeff_C]
  simp

@[simp] lemma mvPolyCoeff_X (i : Fin L) (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff (MvPolynomial.X i) seqs n = seqs i n := by
  simp only [mvPolyCoeff, mvPolyToPowerSeries, seqToPowerSeries,
    MvPolynomial.eval₂_X, PowerSeries.coeff_mk]

@[simp] lemma mvPolyCoeff_add (p q : MvPolynomial (Fin L) ℚ)
    (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff (p + q) seqs n = mvPolyCoeff p seqs n + mvPolyCoeff q seqs n := by
  simp only [mvPolyCoeff, mvPolyToPowerSeries, MvPolynomial.eval₂_add, map_add]

@[simp] lemma mvPolyCoeff_neg (p : MvPolynomial (Fin L) ℚ)
    (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff (-p) seqs n = -mvPolyCoeff p seqs n := by
  simp only [mvPolyCoeff, mvPolyToPowerSeries, MvPolynomial.eval₂_neg, map_neg]

@[simp] lemma mvPolyCoeff_sub (p q : MvPolynomial (Fin L) ℚ)
    (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff (p - q) seqs n = mvPolyCoeff p seqs n - mvPolyCoeff q seqs n := by
  simp only [mvPolyCoeff, mvPolyToPowerSeries, MvPolynomial.eval₂_sub, map_sub]

@[simp] lemma mvPolyCoeff_mul (p q : MvPolynomial (Fin L) ℚ)
    (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff (p * q) seqs n =
      CauchyProduct (mvPolyCoeff p seqs) (mvPolyCoeff q seqs) n := by
  simp only [mvPolyCoeff, mvPolyToPowerSeries, MvPolynomial.eval₂_mul,
    CauchyProduct.apply, PowerSeries.coeff_mul]

@[simp] lemma mvPolyCoeff_one (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff 1 seqs n = if n = 0 then 1 else 0 := by
  rw [show (1 : MvPolynomial (Fin L) ℚ) = MvPolynomial.C 1 from by simp, mvPolyCoeff_C]

@[simp] lemma mvPolyCoeff_X_fun (i : Fin L) (seqs : Fin L → ℕ → ℚ) :
    mvPolyCoeff (MvPolynomial.X i) seqs = seqs i :=
  funext (mvPolyCoeff_X i seqs)

@[simp] lemma mvPolyCoeff_C_fun (r : ℚ) (seqs : Fin L → ℕ → ℚ) :
    mvPolyCoeff (MvPolynomial.C r) seqs = fun n => if n = 0 then r else 0 :=
  funext (mvPolyCoeff_C r seqs)

@[simp] lemma mvPolyCoeff_C_mul (r : ℚ) (p : MvPolynomial (Fin L) ℚ)
    (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff (MvPolynomial.C r * p) seqs n = r * mvPolyCoeff p seqs n := by
  simp only [mvPolyCoeff, mvPolyToPowerSeries, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
  rw [show PowerSeries.C (R := ℚ) r = algebraMap ℚ _ r from rfl,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]

@[simp] lemma mvPolyCoeffQ_C (r : ℚ) (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ (MvPolynomial.C r) arrs n = if n = 0 then r else 0 := by
  simp [mvPolyCoeffQ]

@[simp] lemma mvPolyCoeffQ_zero (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ 0 arrs n = 0 := by simp [mvPolyCoeffQ]

@[simp] lemma mvPolyCoeffQ_X (i : Fin L) (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ (MvPolynomial.X i) arrs n = (arrs i).getD n 0 := by
  simp [mvPolyCoeffQ]

@[simp] lemma mvPolyCoeffQ_add (p q : MvPolynomial (Fin L) ℚ)
    (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ (p + q) arrs n = mvPolyCoeffQ p arrs n + mvPolyCoeffQ q arrs n := by
  simp [mvPolyCoeffQ]

@[simp] lemma mvPolyCoeffQ_neg (p : MvPolynomial (Fin L) ℚ)
    (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ (-p) arrs n = -mvPolyCoeffQ p arrs n := by simp [mvPolyCoeffQ]

@[simp] lemma mvPolyCoeffQ_sub (p q : MvPolynomial (Fin L) ℚ)
    (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ (p - q) arrs n = mvPolyCoeffQ p arrs n - mvPolyCoeffQ q arrs n := by
  simp [mvPolyCoeffQ]

@[simp] lemma mvPolyCoeffQ_mul (p q : MvPolynomial (Fin L) ℚ)
    (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ (p * q) arrs n =
      CauchyProduct (mvPolyCoeffQ p arrs) (mvPolyCoeffQ q arrs) n := by
  simp only [mvPolyCoeffQ, mvPolyCoeff_mul]
  rfl

@[simp] lemma mvPolyCoeffQ_one (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ 1 arrs n = if n = 0 then 1 else 0 := by simp [mvPolyCoeffQ]

@[simp] lemma mvPolyCoeffQ_X_fun (i : Fin L) (arrs : Fin L → Array ℚ) :
    mvPolyCoeffQ (MvPolynomial.X i) arrs = fun n => (arrs i).getD n 0 :=
  funext (mvPolyCoeffQ_X i arrs)

@[simp] lemma mvPolyCoeffQ_C_fun (r : ℚ) (arrs : Fin L → Array ℚ) :
    mvPolyCoeffQ (MvPolynomial.C r) arrs = fun n => if n = 0 then r else 0 :=
  funext (mvPolyCoeffQ_C r arrs)

@[simp] lemma mvPolyCoeffQ_C_mul (r : ℚ) (p : MvPolynomial (Fin L) ℚ)
    (arrs : Fin L → Array ℚ) (n : ℕ) :
    mvPolyCoeffQ (MvPolynomial.C r * p) arrs n = r * mvPolyCoeffQ p arrs n := by
  simp [mvPolyCoeffQ]

end MvPolyBridge
