import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.PowerSeries.Basic
import RadiiPolynomial.Algebra.Convolution.CauchyProduct

/-!
# Rational Coefficient Semantics for Multivariate Polynomials

Evaluates an `MvPolynomial` in rational formal power series and extracts coefficients.
Sequence inputs are the mathematical API.
-/

open RadiiPolynomial

noncomputable section

namespace MvPolyBridge

variable {L : ℕ}

/-- The `n`th coefficient after substituting rational sequences for the variables: the coefficient
of the `aeval` image in `PowerSeries ℚ`, each sequence read as a power series through the bridge
`cauchyProduct.toPowerSeries`. -/
def mvPolyCoeff (p : MvPolynomial (Fin L) ℚ)
    (seqs : Fin L → ℕ → ℚ) (n : ℕ) : ℚ :=
  PowerSeries.coeff n (MvPolynomial.aeval (fun i => cauchyProduct.toPowerSeries (seqs i)) p)

@[simp] lemma mvPolyCoeff_C (r : ℚ) (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff (MvPolynomial.C r) seqs n = if n = 0 then r else 0 := by
  simp [mvPolyCoeff, PowerSeries.coeff_C]


@[simp] lemma mvPolyCoeff_X (i : Fin L) (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff (MvPolynomial.X i) seqs n = seqs i n := by
  simp [mvPolyCoeff]

@[simp] lemma mvPolyCoeff_add (p q : MvPolynomial (Fin L) ℚ)
    (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff (p + q) seqs n = mvPolyCoeff p seqs n + mvPolyCoeff q seqs n := by
  simp [mvPolyCoeff]

@[simp] lemma mvPolyCoeff_neg (p : MvPolynomial (Fin L) ℚ)
    (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff (-p) seqs n = -mvPolyCoeff p seqs n := by
  simp [mvPolyCoeff]

@[simp] lemma mvPolyCoeff_sub (p q : MvPolynomial (Fin L) ℚ)
    (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff (p - q) seqs n = mvPolyCoeff p seqs n - mvPolyCoeff q seqs n := by
  simp [mvPolyCoeff]

@[simp] lemma mvPolyCoeff_mul (p q : MvPolynomial (Fin L) ℚ)
    (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff (p * q) seqs n =
      cauchyProduct (mvPolyCoeff p seqs) (mvPolyCoeff q seqs) n := by
  simp only [mvPolyCoeff, map_mul, cauchyProduct.apply, PowerSeries.coeff_mul]


@[simp] lemma mvPolyCoeff_X_fun (i : Fin L) (seqs : Fin L → ℕ → ℚ) :
    mvPolyCoeff (MvPolynomial.X i) seqs = seqs i :=
  funext (mvPolyCoeff_X i seqs)


@[simp] lemma mvPolyCoeff_C_mul (r : ℚ) (p : MvPolynomial (Fin L) ℚ)
    (seqs : Fin L → ℕ → ℚ) (n : ℕ) :
    mvPolyCoeff (MvPolynomial.C r * p) seqs n = r * mvPolyCoeff p seqs n := by
  simp [mvPolyCoeff, PowerSeries.coeff_C_mul]

end MvPolyBridge
