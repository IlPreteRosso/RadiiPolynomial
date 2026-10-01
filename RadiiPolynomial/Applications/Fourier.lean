import RadiiPolynomial.Applications.Fourier.Semilinear
import RadiiPolynomial.Applications.Fourier.SemilinearFirstOrder

/-!
# Fourier applications (facade)

Re-exports the semilinear consumer on the bilateral geometric carrier
`lpOneAlg ℤ (geomFiberZ 𝕜 ν)`:

* `Applications/Fourier/Semilinear.lean` — the general-symbol semilinear consumer in six layers:
  (1) any symbol `lam` with the finite-head diagonal `headDiag`; (2) the preconditioned map
  `precondMap`, its model derivative `modelDeriv` and `DG(ā) − B₀ = −defect` for every bounded `M`
  and tail diagonal `r`; (3) the raw identification under `r = 0` on the head and `r_k λ_k = 1` off
  it (`tailInv` under tail nonvanishing); (4) the exact finite window
  `B + max (N + 1) K₀` with attainment; (5) the degree window `(d − 1) N + max (N + 1) K₀`
  (`= d N + 1` when `d ≥ 1` and `K₀ ≤ N + 1`); (6) the Γ majorant `(‖M P Γ‖ + C) ‖β‖`.
* `Applications/Fourier/SemilinearFirstOrder.lean` — the first-order family `λ_k = i k` as the
  specialization: first-tail bound `1/(N + 1)`, `K₀ = 1`, window `N + m + 1`.

The Γ majorant is a universal head bound, not the exact window norm.
-/
