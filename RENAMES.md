# RENAMES — end-consumer interface alignment (TASK 2, 2026-09-13)

Ledger of every renamed, moved, retired, or deleted Lean declaration of the alignment pass.
Convention: `| old | new | file | step | reason |`. "retired" = deleted with a library replacement
named in the reason; "moved" = same name, new file. Certificate axiom sets are frozen in
`tmp/autonomous_agenda_2026_09_13/TASK2_axioms_before.txt` and must reprint byte-identically
except for the label changes listed here. Design: `tmp/autonomous_agenda_2026_09_13/TASK2_design_synthesis.md`.

## Decisions on the design panel's open questions (mine, revertible by the user)
1. Naming: keep the skill's `f`/`F` convention; Ex 8.1/8.3 `f` (coefficient nonlinearity) untouched; Ex 14.2.1's real
   vector field is `IVP.vectorField f_cpoly`; `r_minus` (pipeline root, Numbers layer) and `r₀` (theorem radius) both kept.
2. `compPolyOf%`: literal `f_cpoly` stays the definition; a `rfl` reification witness is added (A4).
3. Ex 14.2.1 function-level theorems: retire only the self-labelled compatibility `main_solution_existsUnique_radius_two`
   (+ `R_traj_le_two`); keep `main_solution_existsUnique`, `_contractive`, `_radius_one`.

## RENAMED
| old | new | file | step | reason |
|---|---|---|---|---|
| `Example1421.Cert.main_existsUnique` | `Example1421.Cert.main_theorem` | `Examples/IVP/Chebyshev/Example1421/Certificate.lean` | E1 | the four-example headline name; now proved by `StdChebIVPData.existsUnique_of_compPoly f_cpoly p₀ … Y₀_le Z₀_finBlockNorm_le Z₁_le Z₂_le radii_neg` (finite-block `Z₀`, no differentiability witness). Paper main.tex:1414 cites the old name — RECORDED, not edited |
| `IVP.ivpComposedApprox_eq_fderiv_fin` | `IVP.composedApprox_eq_fderiv_fin` | `Applications/IVP/Taylor/Theorem.lean` | A1 | the `ivp` prefix only existed to pair with the retired `ivpComposedApprox` alias; sole consumer `Applications/IVP/Taylor/Standard.lean` updated |
| `smulCLM`, `smulCLM_apply`, `norm_smulCLM`, `id_eq_smulCLM_one`, `smulCLM_comp`, `smulCLM_sub`, `id_sub_smulCLM`, `smulCLM_injective`, `fderiv_sq_sub_const`, `differentiable_sq_sub_const`, `Z₂_bound_sq_sub_const` (root namespace) | `Example245.*` | `Examples/FiniteDimensional/Example245/Algebra.lean` | A2 | an example file was declaring eleven root-namespace symbols; one consumer (`Example245/Certificate.lean`), so namespaced rather than promoted. `#check smulCLM` now fails at the root |
| `Example245.Cert.ex_f` | `Example245.Cert.f` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | `ex_` prefix dropped; the namespace already says which example |
| `Example245.Cert.ex_xBar` | `Example245.Cert.xBar` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | idem |
| `Example245.Cert.ex_A` | `Example245.Cert.A` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | idem |
| `Example245.Cert.ex_A_dag` | `Example245.Cert.A_dag` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | idem |
| `Example245.Cert.ex_Y₀` | `Example245.Cert.Y₀_bound` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | `*_bound` is the spelling of the other four examples |
| `Example245.Cert.ex_Z₀` | `Example245.Cert.Z₀_bound` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | idem |
| `Example245.Cert.ex_Z₂` | `Example245.Cert.Z₂_bound` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | idem |
| `Example245.Cert.ex_r₀` | `Example245.Cert.r₀` | `Examples/FiniteDimensional/Example245/Certificate.lean` | A2 | idem |
| `Example77.Cert.ν` | `Example77.Cert.ν_q` | `Examples/PowerSeries/Example77/Certificate.lean` | A3 | a `def ν : ℚ` shadowed the project-wide weight symbol inside the namespace that also defines `ν_val`; the duplicate commented `-- def ν : ℚ := 1/4` of the alternative parameter set (same value) was deleted |
| `Example77.Cert.Y₀_bnd` | `Example77.Cert.Y₀_bound` | `Examples/PowerSeries/Example77/Certificate.lean` | A3 | `*_bound` is the spelling of the other four examples (commented alternative set renamed too) |
| `Example77.Cert.Z₀_bnd` | `Example77.Cert.Z₀_bound` | `Examples/PowerSeries/Example77/Certificate.lean` | A3 | idem |
| `Example77.Cert.Z₁_bnd` | `Example77.Cert.Z₁_bound` | `Examples/PowerSeries/Example77/Certificate.lean` | A3 | idem |
| `Example77.Cert.Z₂_bnd` | `Example77.Cert.Z₂_bound` | `Examples/PowerSeries/Example77/Certificate.lean` | A3 | idem |
| `RadiiPolynomial.IVP.SplitBoundary` (+ `.trace_extension_apply`, `.equiv`, `.equiv_fst`, `.equiv_snd_coe`, `.zeroPart`, `.zeroPart_coe`, `.trace_zeroPart`, `.extension_add_zeroPart`, `.anchoredPrimitive`, `.trace_anchoredPrimitive`, `.fiber_eq_translate_ker`) | `IVP.SplitBoundary` … | `Applications/IVP/Boundary.lean` | H1 | the outer `namespace RadiiPolynomial` wrapper dropped (this module imports only Mathlib, so no `open RadiiPolynomial` is added); zero external consumers, `command grep -rn '^namespace RadiiPolynomial$' Applications/` now empty |
| `RadiiPolynomial.IVP.{taylorBoundaryCharacter, taylorBoundaryCharacter_apply, taylorEndpointCharacter, taylorEndpointCharacter_apply, taylorReborderingDefect, taylorReborderingDefect_apply, norm_taylorReborderingDefect_apply_le, norm_taylorReborderingDefect_le, norm_taylorReborderingDefect, taylorSplitBoundary, taylorSplitBoundary_trace, taylorBoundary_shiftDivN, taylorAnchoredPrimitive, taylorAnchoredPrimitive_coe}` | `IVP.*` | `Applications/IVP/Taylor/Boundary.lean` | H1 | outer wrapper dropped, `open RadiiPolynomial` added |
| `RadiiPolynomial.IVP.{chebyshevBoundary, chebyshevBoundary_apply, chebyshevBoundary_one, chebyshevBoundary_not_multiplicative, chebyshevSplitBoundary, symmetricEndpointCharacter, chebyshevBoundary_factor_symmetric, symmetricEndpointCharacter_comp_joukowskiAevalSymm, abs_chebyshevBoundary_le_norm_of_two_le, chebyshevIntegrateCLM, chebyshevIntegrateCLM_apply, chebyshevAnchoredPrimitive, chebyshevAnchoredPrimitive_zero_boundary, eval_chebyshevAnchoredPrimitive}` | `IVP.*` | `Applications/IVP/Chebyshev/Boundary.lean` | H1 | outer wrapper dropped, `open RadiiPolynomial` added |

## MOVED
| name | from | to | step | reason |
|---|---|---|---|---|
| `IVP.vectorField` | `Applications/IVP/Taylor/Trajectory.lean` | `Applications/IVP/VectorField.lean` (new) | L4 | geometry-free right-hand side; both discretizations' function-space conclusions name it, so it sits below Taylor and Chebyshev. Name, namespace and docstring unchanged; `IVP.banachField` stays in `Trajectory.lean` (it mentions `XL1`) |
| `Example1421.G_diff` | `Examples/IVP/Chebyshev/Example1421/Lambda.lean` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E2 | restated on `ChebyshevIVP.banachField f_cpoly`, proof unchanged (`data.differentiable_G_of_compPoly f_cpoly p₀`); kept for `Examples/Transport/TwinTransport.lean` |
| `IVP.analyticOnNhd_x_analytic` | `Applications/IVP/Taylor/ComplexTime.lean` | `Applications/IVP/Taylor/Analyticity.lean` (new) | H3 | a purely real statement had forced `Example81/Analyticity.lean` to import the complex-time layer; name, namespace, statement and proof unchanged, `ComplexTime.lean` now imports the new module |
| `Example83.Cert.lorenz_analyticOnNhd` | `Examples/IVP/Taylor/Example83/ComplexTime.lean` | `Examples/IVP/Taylor/Example83/Analyticity.lean` (new) | H3 | layer parity with Ex 8.1; names and proofs unchanged |
| `Example83.Cert.lorenz_analytic_existsUnique` | `Examples/IVP/Taylor/Example83/ComplexTime.lean` | `Examples/IVP/Taylor/Example83/Analyticity.lean` (new) | H3 | idem |

## RETIRED (deleted; replacement named)
| old | replacement | file | step | reason |
|---|---|---|---|---|
| `Example1421.hasFDerivAt_sq_cheb` | `CompPoly.Chebyshev.hasFDerivAt_eval` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers; the adapter proves `HasFDerivAt` for any `CompPoly` |
| `Example1421.hasFDerivAt_q` | `CompPoly.Chebyshev.hasFDerivAt_eval` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers |
| `Example1421.differentiable_phi` | `ChebyshevIVP.StdChebIVPData.differentiable_G_of_compPoly` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers |
| `Example1421.fderiv_phi_apply` | `ChebyshevIVP.StdChebIVPData.fderiv_G_of_compPoly` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers |
| `Example1421.norm_Dphi_le` | `CompPoly.Chebyshev.norm_derivative_apply_le` / `ChebyshevIVP.norm_compPolyDerivative_le` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers |
| `Example1421.norm_S_le` | `l1Chebyshev.symmetrize_CLM_norm_le` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers; bare alias for the library bound |
| `Example1421.norm_Ssym_le` | `l1Chebyshev.symmetrize_norm_le` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers; bare alias for the library bound |
| `Example1421.SP_apply` | — | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | D1 | zero consumers; `SP` unfolds by `rfl` |
| `Example77.F_eq` | — | `Examples/PowerSeries/Example77/Algebra.lean` | D1 | zero consumers; `rfl` |
| `Example77.F_sub_const_eq_fun` | — | `Examples/PowerSeries/Example77/Algebra.lean` | D1 | zero consumers |
| `Example77.Z₀_structural` | `ScalarBlockDiagData.Z₀_le_finWeightedMatrixNorm_of_tailCancel` | `Examples/PowerSeries/Example77/Algebra.lean` | D1 | zero consumers; bare alias for the library reduction |
| `Example77.differentiable_sq` | `Example77.hasFDerivAt_sq` (`.differentiableAt`) | `Examples/PowerSeries/Example77/Algebra.lean` | D1 | zero consumers |
| `Example77.fderiv_sq` | `Example77.hasFDerivAt_sq` (`.fderiv`) | `Examples/PowerSeries/Example77/Algebra.lean` | D1 | zero consumers |
| `Example245.fderiv_sq` | `Example245.fderiv_sq_sub_const` | `Examples/FiniteDimensional/Example245/Algebra.lean` | D1 | zero consumers |
| `Example245.Cert.ex_A_dag_eq` | — | `Examples/FiniteDimensional/Example245/Certificate.lean` | D1 | zero consumers (`private`) |
| `Example81.f_bridge` | `CompPoly.toSeq_evalBanach` | `Examples/IVP/Taylor/Example81/Algebra.lean` | D1 | zero consumers; one-line application of the library bridge |
| `Example83.f_bridge` | `CompPoly.toSeq_evalBanach` | `Examples/IVP/Taylor/Example83/Algebra.lean` | D1 | zero consumers; one-line application of the library bridge |
| `Example83.G_ā_vec` | — | `Examples/IVP/Taylor/Example83/Numbers.lean` | D1 | zero consumers; the Y₀ fold is computed from `F_Q`, not from stored `G(ā)` literals |
| `Example83.G_ā_vec_0` | — | `Examples/IVP/Taylor/Example83/Numbers.lean` | D1 | zero consumers (`private`; ≈11.6 KB of literals) |
| `Example83.G_ā_vec_1` | — | `Examples/IVP/Taylor/Example83/Numbers.lean` | D1 | zero consumers (`private`) |
| `Example83.G_ā_vec_2` | — | `Examples/IVP/Taylor/Example83/Numbers.lean` | D1 | zero consumers (`private`) |
| `Example1421.phi` | `ChebyshevIVP.banachField f_cpoly` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E1/E2 | rfl-equal; every statement of `Certificate.lean`, `Analytic.lean`, `TwinTransport.lean` now reads `data.G (banachField f_cpoly) p₀` |
| `Example1421.Ssym` | `l1Chebyshev.symmetrize` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E1/E2 | bare alias |
| `Example1421.S` | `l1Chebyshev.symmetrize_CLM` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E1/E2 | bare alias; `Sabar_norm_le` keeps its name and proof shape, its statement now reads `‖l1Chebyshev.symmetrize_CLM (ābar l)‖` |
| `Example1421.Ssym_toSeq` | `l1Chebyshev.symmetrize_toSeq` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E1/E2 | bare alias |
| `Example1421.S_apply` | `l1Chebyshev.symmetrize_CLM_apply` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E1/E2 | bare alias |
| `Example1421.SP` | — | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E2 | intermediate of the retired CLM-level derivative formula |
| `Example1421.leftMul_apply'` | — | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E2 | intermediate of the retired CLM-level derivative formula |
| `Example1421.derivative_f_cpoly_eq` | `Example1421.Dphi_eq_derivative` (direct proof) | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E2 | the CLM-level identity `derivative (f_cpoly l) a = (2·leftMul(S aₗ) − id) ∘ S ∘ projₗ` is folded into the componentwise `Dphi_eq_derivative` |
| `Example1421.hasFDerivAt_phi` | `ChebyshevIVP.hasFDerivAt_compPoly` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E2 | adapter proves it for any `CompPoly` system |
| `Example1421.DPhiCLM` | `ChebyshevIVP.compPolyDerivative f_cpoly` | `Examples/IVP/Chebyshev/Example1421/Lambda.lean` (deleted) | E1/E2 | one derivative name at the CLM level; the example's explicit `Dphi` is reached by the new rfl-backed `compPolyDerivative_apply_eq_Dphi` |
| `Example1421.DPhiCLM_apply` | `Example1421.compPolyDerivative_apply_eq_Dphi` (new) | `Examples/IVP/Chebyshev/Example1421/Lambda.lean` (deleted) | E1/E2 | componentwise bridge `compPolyDerivative f_cpoly a h l = Dphi a h l := (Dphi_eq_derivative a h l).symm` |
| `Example1421.hasFDerivAt_Phi` | `ChebyshevIVP.hasFDerivAt_compPoly` | `Examples/IVP/Chebyshev/Example1421/Lambda.lean` (deleted) | E2 | — |
| `Example1421.compPolyDerivative_eq` | `Example1421.compPolyDerivative_apply_eq_Dphi` | `Examples/IVP/Chebyshev/Example1421/Lambda.lean` (deleted) | E1/E2 | CLM identity replaced by the componentwise one |
| `Example1421.fderiv_G` | `ChebyshevIVP.StdChebIVPData.fderiv_G_of_compPoly f_cpoly p₀` | `Examples/IVP/Chebyshev/Example1421/Lambda.lean` (deleted) | E1/E2 | `Certificate.lean`'s `fderiv_toSeq` rewrites with the library lemma directly |
| `Example1421.Cert.f` | `IVP.vectorField f_cpoly` | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | rfl-equal; the surviving theorem statements spell the vector field this way (see "Statement wording" below) |
| `Example1421.Cert.hφ_eval` | derived inside `StdChebIVPData.solution_existsUnique_of_compPoly` / `_of_two_le_of_compPoly` / `analytic_solution_existsUnique_of_two_le_of_compPoly` (`CompPoly.Chebyshev.eval_eval`) | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | structural obligation, no longer stated per example |
| `Example1421.Cert.f_lipschitzOnWith` | `CompPoly.lipschitzOnWith_evalBanach_pi` inside the faces; the syntactic input was briefly the example lemma `lipschitzBound_f_cpoly` (retired again in round 2: the faces build it internally) : lipschitzBound (X² − X) (fun _ => R) = 2R + 1` | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | the faces take `hK` on the syntax |
| `Example1421.Cert.defect_norm_lt_one` | `ChebyshevIVP.StdChebIVPData.defect_finBlockNorm_lt_one_of_radii` (derived inside the faces) | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | derived from the four bounds |
| `Example1421.Cert.two_le_ν_val` | inline `by rw [show ((ν_val : ℝ)) = 2 from rfl]` | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | private one-liner |
| `Example1421.Cert.main_solution_existsUnique_radius_two` | — (headline is `main_solution_existsUnique_radius_one`) | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | self-labelled compatibility statement; companion l.2608 ripple for the docs pass |
| `Example1421.Cert.R_traj_le_two` | — | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | only consumer was `_radius_two` |
| `Example81.Cert.banachField_eq_f` | `IVP.StdIVPData.x_analytic_isAnalyticSolution_of_compPoly` &co. (the `_of_compPoly` faces supply `rfl` internally) | `Examples/IVP/Taylor/Example81/Analytic.lean` | T1 | private `rfl` bridge; the four function-space theorems now call the L6 faces, which take `f_cpoly` and no `h_phi_eq` |
| `Example83.Cert.banachField_eq_f` | `IVP.StdIVPData.x_analytic_isAnalyticSolution_of_compPoly` &co. | `Examples/IVP/Taylor/Example83/Analytic.lean` | T1 | idem |
| `IVP.ivpComposedApprox` | `SystemBlockDiagData.composedApprox` | `Operators/BlockDiagonal/Composition.lean` | A1 | compatibility `abbrev` for the pre-refactor Taylor API; all 11 use sites rewritten (`Applications/IVP/Taylor/{Theorem,Standard}.lean`) |
| `IVP.ivpComposedApprox_defect_eq` | `SystemBlockDiagData.composedApprox_defect_eq` | `Operators/BlockDiagonal/Composition.lean` | A1 | wrapper delegating to the `SystemBlockDiagData` lemma |
| `IVP.ivpComposedApprox_toCLM_tail` | `SystemBlockDiagData.composedApprox_toCLM_tail` | `Operators/BlockDiagonal/Composition.lean` | A1 | wrapper delegating to the `SystemBlockDiagData` lemma |
| `Example245.existsUnique` | `general_radii_polynomial_theorem` | `Examples/FiniteDimensional/Example245/Algebra.lean` | A2 | verbatim argument permutation of Thm 7.6.2; `Cert.main_theorem` now calls the abstract theorem directly |
| `KappaToy.f := Example77.F_sub_const c` (and its `Example77.{sq, fderiv_F_sub_const, fderiv_F_sub_const_affine, differentiable_F_sub_const}` uses) | local `KappaToy.{f, hasFDerivAt_f, fderiv_f, fderiv_f_affine}` | `Examples/Transport/KappaToy.lean` | H4 | removes the last Examples→Examples import outside `TwinTransport`; `f` is now `fun a => a * a - c` with its own `auto_hasFDerivAt` derivative (import `Examples.PowerSeries.Example77.Algebra` replaced by `Tactic.AutoPolyFDeriv`) |

## DELETED FILES
| file | step | reason |
|---|---|---|
| `RadiiPolynomial/Examples/IVP/Chebyshev/Example1421/Lambda.lean` (+ its import line in `RadiiPolynomial/Examples.lean`; `Certificate.lean` now imports `…Example1421.Algebra`) | E2 | every declaration retired or moved (see RETIRED/MOVED); Ex 14.2.1 now has exactly Numbers → Algebra → Certificate → Analytic → Analyticity |

## ADDED (library faces, step 2-4)

New declarations, all sorry-free, all printing exactly `propext, Classical.choice, Quot.sound`.
No global instance, no `native_decide`, no new axiom.

| declaration | file | step | role |
|---|---|---|---|
| `ChebyshevIVP.banachField` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 | Chebyshev coefficient nonlinearity of a `CompPoly` system; mirror of `IVP.banachField` |
| `ChebyshevIVP.banachField_apply` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 | `@[simp]` component form (`rfl`) |
| `ChebyshevIVP.StdChebIVPData.defect_finBlockNorm_lt_one_of_radii` | `Applications/IVP/Chebyshev/Standard.lean` | L2 | Chebyshev mirror of the Taylor lemma; derives `‖defect‖ < 1` from the four bounds |
| `ChebyshevIVP.StdChebIVPData.Z₂_le_of_compPoly_max` | `Applications/IVP/Chebyshev/Polynomial.lean` | L3 | `Z₂` socket: syntactic derivative Lipschitz constant plus a `TC` bound gives the ball statement |
| `ChebyshevIVP.StdChebIVPData.existsUnique_of_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L3 | coefficient-zero face, `Z₀` in finite-block form |
| `ChebyshevIVP.StdChebIVPData.solution_existsUnique_of_compPoly` | `Applications/IVP/Chebyshev/AnalyticPolynomial.lean` (new) | L5 | function-space face, trajectory radius `2(‖ā‖ + r₀)` |
| `ChebyshevIVP.StdChebIVPData.solution_existsUnique_of_two_le_of_compPoly` | `Applications/IVP/Chebyshev/AnalyticPolynomial.lean` (new) | L5 | contractive face at `2 ≤ ν`, radius `‖ā‖ + r₀` |
| `ChebyshevIVP.StdChebIVPData.analytic_solution_existsUnique_of_two_le_of_compPoly` | `Applications/IVP/Chebyshev/AnalyticPolynomial.lean` (new) | L5 | same, with `AnalyticOnNhd` for the produced solution only |
| `IVP.StdIVPData.existsUnique_of_compPoly` | `Applications/IVP/Taylor/Polynomial.lean` | L6 | Taylor coefficient-zero face |
| `IVP.StdIVPData.existsUnique_ivpCoeffs_of_compPoly` | `Applications/IVP/Taylor/Polynomial.lean` | L6 | same at the source residual, `Z₀` in finite-block form |
| `IVP.StdIVPData.x_analytic_isAnalyticSolution_of_compPoly` | `Applications/IVP/Taylor/Analytic.lean` | L6 | `φ := banachField φ_cpoly`, `h_phi_eq := rfl` |
| `IVP.StdIVPData.analytic_eq_canonical_of_compPoly` | `Applications/IVP/Taylor/Analytic.lean` | L6 | idem |
| `IVP.StdIVPData.analytic_unique_of_compPoly` | `Applications/IVP/Taylor/Analytic.lean` | L6 | idem |
| `IVP.StdIVPData.analytic_existsUnique_of_compPoly` | `Applications/IVP/Taylor/Analytic.lean` | L6 | idem |
| `Example1421.compPolyDerivative_apply_eq_Dphi` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | E1 | rfl-backed bridge from the adapter's system derivative to the example's explicit `Dphi` |
| `Example1421.Cert.lipschitzBound_f_cpoly` | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | E3 | `lipschitzBound (X² − X) (fun _ => R) = 2R + 1`; the one syntactic input of the three function-space theorems and of `Analyticity.lean` |
| `Example81.f_cpoly_reified` | `Examples/IVP/Taylor/Example81/Algebra.lean` | A4 | `f_cpoly 0 = compPolyOf% (fun u : Fin L → ℝ => u 0 * u 0 - u 0) := rfl` — certificate-level consumer of the elaborator (needs `import RadiiPolynomial.Tactic.MakeCompPoly`) |
| `Example1421.f_cpoly_reified` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | A4 | idem, Chebyshev geometry (the reifier is geometry-free, so the same `Fin L → ℝ` lambda is used) |
| `RadiiPolynomial.Gelfand.pointwiseTopology` | `Analysis/SequenceSpace/CharacterTopology.lean` (new) | H2 | carrier-independent topology of pointwise convergence on `A →A[R] B`; the three per-carrier `pointwiseTopology` defs (`TaylorSpectrum`, `LaurentSpectrum`, `PhysicalSpectrum`) are now one-line specializations, each module keeping its own `local instance` |
| `RadiiPolynomial.Gelfand.continuous_character_apply` | `Analysis/SequenceSpace/CharacterTopology.lean` (new) | H2 | the single continuity fact the three modules needed; the three same-named per-carrier theorems keep their names and delegate |
| `KappaToy.hasFDerivAt_f`, `KappaToy.fderiv_f`, `KappaToy.fderiv_f_affine` | `Examples/Transport/KappaToy.lean` | H4 | the toy's own calculus for `a ↦ a·a − c`, replacing the imported Ex 7.7 lemmas |

## RESTATED (same name, statement rewritten through `ChebyshevIVP.banachField`)

`rw` matches syntactically, so the adapter lemmas that inlined
`fun x l => CompPoly.Chebyshev.eval (f l) x` had to be restated for the new faces to
compose. All proofs are unchanged except `ivpCoeffs_abar_eq_cast_of_compPoly`, whose
`simp only` set gained `banachField, CompPoly.Chebyshev.eval` as unfold rules. All six
keep their axiom sets, and Example 14.2.1's `exact`/`have` call sites were accepted
unchanged (defeq).

| declaration | file | step |
|---|---|---|
| `ChebyshevIVP.StdChebIVPData.ivpCoeffs_abar_eq_cast_of_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 |
| `ChebyshevIVP.hasFDerivAt_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 |
| `ChebyshevIVP.StdChebIVPData.hasFDerivAt_G_of_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 |
| `ChebyshevIVP.StdChebIVPData.differentiable_G_of_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 |
| `ChebyshevIVP.StdChebIVPData.fderiv_G_of_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 |
| `ChebyshevIVP.StdChebIVPData.fderiv_G_fin_toSeq_of_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 |
| `ChebyshevIVP.StdChebIVPData.fderiv_G_single_fin_eq_cast_of_compPoly` | `Applications/IVP/Chebyshev/Polynomial.lean` | L1 |

## NEW MODULES

| module | imports | wired into |
|---|---|---|
| `Applications/IVP/VectorField.lean` | `Algebra.Polynomial.CompPoly.Core` only | `Taylor/Trajectory.lean`, and both facades `Applications/IVP/Taylor.lean` and `Applications/IVP/Chebyshev.lean` |
| `Applications/IVP/Chebyshev/AnalyticPolynomial.lean` | `Chebyshev.Analyticity`, `Chebyshev.Polynomial`, `IVP.VectorField` | facade `Applications/IVP/Chebyshev.lean` (already imported by the root) |

Import added as a consequence: `Applications/IVP/Taylor/Polynomial.lean` now imports
`Applications/IVP/Taylor/Trajectory.lean`, because `IVP.banachField` lives there and the
Taylor faces state their hypotheses through it. No cycle; the `Applications.IVP.Taylor`
facade consequently also exposes `Trajectory`.

### NEW MODULES (steps 10, H2/H3)

| file | step | role |
|---|---|---|
| `RadiiPolynomial/Applications/IVP/Taylor/Analyticity.lean` | H3 | hosts the moved `IVP.analyticOnNhd_x_analytic`; imported by `Taylor/ComplexTime.lean`, `Example81/Analyticity.lean`, `Example83/Analyticity.lean` and the root import |
| `RadiiPolynomial/Examples/IVP/Taylor/Example83/Analyticity.lean` | H3 | Ex 8.3's real-analyticity theorems, mirroring `Example81/Analyticity.lean`; wired into `Examples.lean` and the `TaylorCertifiedExamples.lean` shim |
| `RadiiPolynomial/Analysis/SequenceSpace/CharacterTopology.lean` | H2 | `Gelfand.pointwiseTopology` / `Gelfand.continuous_character_apply`, imported by `Geometric/Spectrum.lean`, `Chebyshev/LaurentSpectrum.lean`, `Chebyshev/Spectrum/Topology.lean` |

## RESTATED (Example 14.2.1, steps E1–E3; same names, `phi`/`S`/`f` spelled through library names)

Statements are unchanged up to `rfl`-unfolding of the retired aliases; proofs of the
native_decide-bearing declarations are byte-identical in structure (names and native call
counts unchanged: `data`, `Sabar_norm_le`, `Y₀_le`, `Z₀_finBlockNorm_le`, `abar_0_size`,
`TCcolNormQ_le_small`, `colNormQ_le_small`, `rowA0Q_le`).

| declaration | file | change |
|---|---|---|
| `Example1421.Dphi` | `Algebra.lean` | body `(2:ℝ) • (l1Chebyshev.symmetrize_CLM (a l) * l1Chebyshev.symmetrize_CLM (h l)) - l1Chebyshev.symmetrize_CLM (h l)` (was the same through the alias `S`) |
| `Example1421.Dphi_eq_derivative` | `Algebra.lean` | direct proof (`derivative_apply` + `Fin.sum_univ_one` + the two `change`s), no CLM-level intermediate |
| `Example1421.Cert.{Y₀_le, Z₁_le, Z₁_le_semiMajor, Z₂_le}` | `Certificate.lean` | `data.G phi p₀` → `data.G (banachField f_cpoly) p₀`; `Z₂_le` proved by `data.Z₂_le_of_compPoly_max f_cpoly p₀ … TC_norm_le …` with `Z₂_bound = (7/4)·8` |
| `Example1421.Cert.Sabar_norm_le` | `Certificate.lean` | `‖S (ābar l)‖` → `‖l1Chebyshev.symmetrize_CLM (ābar l)‖`; proof shape unchanged (`native_decide` witness `ax_1_3` unchanged) |
| private `Sabar_toSeq`, `S_single_toSeq`, `conv_single_toSeq`, `Dphi_single_toSeq`, `Trow_negSucc_toSeq`, `fderiv_toSeq`, `compPolyDphiQ_eq`, `Trow`, `Trow_eq`, `Z₁_hneg`, `Z₁_htail`, `Z₁_hfin`, `Trow_single_toSeq`, `F_abar_eq`, `Y₀_eval_correct` | `Certificate.lean` | same spelling changes; `fderiv_toSeq` rewrites with `data.fderiv_G_of_compPoly f_cpoly p₀` and `compPolyDerivative_apply_eq_Dphi`; `S_single_toSeq` pins `(ν := ν_val)` on the `single` (the alias used to pin it) |
| `TwinTransport.{twin_transports, twin_scalar_certificate}` | `Examples/Transport/TwinTransport.lean` | `data.G phi p₀` → `data.G (banachField f_cpoly) p₀` (4 sites) |

### Statement wording (the paper and the ground note cite these; statements literally unchanged except for the spelling of the vector field)

| theorem | old spelling | new spelling |
|---|---|---|
| `Example1421.Cert.main_solution_existsUnique` | `ChebyshevIVP.IsSolution f p₀ R_traj g` | `ChebyshevIVP.IsSolution (IVP.vectorField f_cpoly) p₀ R_traj g` |
| `Example1421.Cert.main_solution_existsUnique_contractive` | `… IsSolution f p₀ R_traj_contractive …` | `… IsSolution (IVP.vectorField f_cpoly) p₀ R_traj_contractive …` |
| `Example1421.Cert.main_solution_existsUnique_radius_one` | `… IsSolution f p₀ 1 …` | `… IsSolution (IVP.vectorField f_cpoly) p₀ 1 …` |
| `Example1421.Cert.analytic_solution_existsUnique_radius_one` | `… IsSolution Example1421.Cert.f Example1421.p₀ 1 …` | `… IsSolution (IVP.vectorField Example1421.f_cpoly) Example1421.p₀ 1 …` |
| `Example1421.Cert.main_theorem` (ex `main_existsUnique`) | `data.G phi p₀ xTilde = 0` | `data.G (banachField f_cpoly) p₀ xTilde = 0` |

`Cert.f u l` was by definition `(f_cpoly l).evalBanach u`, which is `IVP.vectorField f_cpoly u l` by `rfl`.

## Audit files synced (E4)

| file | change |
|---|---|
| `tmp/proposal_experiments_2026_09_06/ChebCompPolyExample1421.lean` | `phiPoly_eq_phi` → `phiPoly_eq_banachField` (`= ChebyshevIVP.banachField Example1421.f_cpoly`), `evalBanach_eq_f` → `evalBanach_eq_vectorField`, `fPoly_eq_f` → `fPoly_eq_vectorField`; local `defect_norm_lt_one` now derived by `data.defect_finBlockNorm_lt_one_of_radii`; the Lipschitz input is `CompPoly.lipschitzOnWith_evalBanach_pi f_cpoly 1 (K := 3) (fun l => by simp [CompPoly.lipschitzBound, f_cpoly]; norm_num)` passed directly (defeq to `fPoly` by one delta step) |
| `tmp/proposal_experiments_2026_09_06/checks/cheb_comppoly_promotion_2026_09_12/promoted_axioms.lean` | dropped `Example1421.hasFDerivAt_phi` and `Example1421.Cert.hφ_eval` (retired), `main_existsUnique` → `main_theorem`; `checks/…/before/` and `baseline_axioms.lean` untouched |

## Writeup ripple (filled by the docs pass)

Filled 2026-09-13 by the documentation pass. Every Lean name written into these files was
verified with `command grep -rn "<name>" RadiiPolynomial/` before it was written; no `.lean`
file was touched and no build was run.

| file | what changed |
|---|---|
| `ARCHITECTURE.md` | Directory table: new rows `Analysis/SequenceSpace/CharacterTopology` (`Gelfand.pointwiseTopology`, `Gelfand.continuous_character_apply`) and `Applications/IVP/VectorField.lean` (`IVP.vectorField`); Geometric and Chebyshev rows now say their spectrum modules install the *shared* topology as a `local instance`; the Taylor row gains `Analyticity` (`IVP.analyticOnNhd_x_analytic`, no longer attributed to `ComplexTime`) and the three `StdIVPData.*_of_compPoly` faces; the Chebyshev row gains `ChebyshevIVP.banachField`, `StdChebIVPData.{existsUnique_of_compPoly, Z₂_le_of_compPoly_max, defect_finBlockNorm_lt_one_of_radii}` and the three `AnalyticPolynomial` faces. Import rule 6 records the single surviving `Examples → Examples` edge (`TwinTransport → Example1421/Certificate`). Boundaries: the `IVP.ivpComposedApprox` alias bullet replaced by its dated retirement plus `IVP.composedApprox_eq_fderiv_fin`; example progression is now `Numbers → Algebra → Certificate → Analytic → Analyticity` with "Example 14.2.1 has exactly these five and no `Lambda.lean`" and the per-example strengthenings corrected (`Analyticity` for Ex 8.1/8.3/14.2.1, `ComplexTime` for Ex 8.3 only); the pointwise-topology bullet rewritten around the shared definition; the root-wiring sentence now names `Taylor/{Analytic,Analyticity,ComplexTime}.lean` and why `Analyticity` sits below `ComplexTime`. |
| `/Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/UBIQUITOUS_LANGUAGE.md` | Trust-surface row: `main_existsUnique` → `main_theorem` (with a dated "was its spelling before 2026-09-13"). Spectrum row and its 2026-09-13 status bullet: the three homeomorphisms now name the shared `Gelfand.pointwiseTopology` of `Analysis/SequenceSpace/CharacterTopology.lean`, and `IVP.analyticOnNhd_x_analytic` is located in `Taylor/Analyticity.lean`. Λ-decomposition row: the example's `DPhiCLM`, `compPolyDerivative_eq`, `fderiv_G` and `Example1421/Lambda.lean` recorded as retired, the library derivative named as `ChebyshevIVP.compPolyDerivative`, the bridge as `Example1421.compPolyDerivative_apply_eq_Dphi`, and the still-live library `Applications/IVP/Chebyshev/Lambda.lean` explicitly distinguished. Derivative-constants row: the "kept as a header" claim about the retired `norm_Dphi_le` corrected. Adapter row: the stale "`f_cpoly` supplies `phi`, `f`, `hφ_eval`, `G_diff`, `fderiv_G`" replaced by the post-alignment interface. New section "End-consumer interface" with six rows: coefficient nonlinearity φ = `banachField f_cpoly` (both geometries), vector field f = `IVP.vectorField f_cpoly`, `_of_compPoly` face, `r_minus` vs `r₀`, `x₀` vs `p₀`, `retract` vs `symmetrize`. |
| `/Users/ilpreterosso/.claude/skills/radii-poly-api-design/SKILL.md` | §9 rewritten: five layers, the explicit "what an example supplies" list, both geometries' `_of_compPoly` entry points, the two derived maps, the syntactic-constant sockets (`CompPoly.normBound`/`lipschitzBound`/`derivativeBound`, `ivp_Dφ_norm_le_of_compPoly`, `Z₂_le_of_compPoly_max`) with the cancellation caveat, and the `f_cpoly_reified` rfl-witness convention. Pattern list: `MvPolyBridge/CompPoly.lean` → `RadiiPolynomial/Algebra/Polynomial/CompPoly/Core.lean`, `source/Tactic/` → `RadiiPolynomial/Tactic/` (and `compPolyOf%` now reifies constants), `IVP/AnalyticGlue` → `Applications/IVP/Taylor/Analytic.lean` with the `banachField_eq_f` obligation recorded as gone. Build hygiene rewritten: the `examples/tests/{easy,hard}` skeleton tree no longer exists; today's layout is the `RadiiPolynomial/Examples.lean` import list. |
| `RadiiPolynomial/tmp/ground_floor/note_ground_floor.tex` | Status flips to production for the spectra/analyticity branch (ellipse contractivity ¶, the `rem:spectop` and physical-classification remarks, the fiber identity, the complex-disc ODE sentence, the cross-geometry verdict, the Taylor and Chebyshev read-back paragraphs). Status ¶ rewritten around three promotions (residual certificate Sept 7, Chebyshev adapter Sept 12, spectra/analyticity Sept 13) and names what is still an experiment. Trust ¶: build count 3,999 → 4,026 jobs, promotion list extended. Production table gains eight rows (shared character topology; disc spectrum + full-disc analyticity; annulus spectrum; physical spectrum, six modules; real-character obstructions; Taylor real analyticity + complex time; Chebyshev read-back analyticity; the four strengthened certificates) and `Example1421.compPolyDerivative_eq` → `compPolyDerivative_apply_eq_Dphi`. Experiment table loses the five promoted rows and gains three new ones (`CoronaDivisionCoproduct.lean`, `SpectralGap.lean`, `tmp/cross_geometry_arrow/FoldedProductRing.lean`). Experiment-checks ¶: 49 modules/6,022 lines → 51/5,239, with the twelve new re-exports explained. Limits ¶: "derives no norm bound from syntax" replaced by the syntactic-constant statement and the Ex 8.1 cancellation exception. |
| `/Users/ilpreterosso/VSCode/Lean/RadiiPolynomial/exterior/tmp/formalization_companion/formalization_companion.tex` | Packaged annulus/ellipse classifications now stated (`LaurentSpectrum.characterEquivAnnulus`, `PhysicalSpectrum.characterEquivEllipse`); "What Lean has" moved to production with the production file names and the shared topology; the `IsAnalyticSolution` paragraph points at the production analyticity theorems. Ex 8.1/8.3 per-example obligations reduced from two to one (`banachField_eq_f` recorded as deleted). Library `Lambda.lean` citation disambiguated by its full path. Ex 14.2.1: bounds sentence `main_existsUnique` → `main_theorem`; the "Example 14.2.1, migrated" paragraph rewritten to the new interface (one polynomial system in, `banachField f_cpoly`, `compPolyDerivative` + `compPolyDerivative_apply_eq_Dphi`, retirement of `DPhiCLM`/`hasFDerivAt_Phi`/`compPolyDerivative_eq`/`fderiv_G` and of `Example1421/Lambda.lean`, `existsUnique_of_compPoly`, `Z₂_le_of_compPoly_max`), and its closing "no norm bound is derived from syntax" replaced. Analytic strengthening paragraph moved to production. "The three per-example obligations" → "The one per-example obligation" (`hφ_eval` and `f_lipschitzOnWith` derived inside the faces; `lipschitzBound_f_cpoly` named). Trust-surface ¶: `main_existsUnique` → `main_theorem`, and the `_radius_two` compatibility sentence replaced by its dated retirement. Transform-map table: spectrum rows "checked experiment" → "production", with a new `characterEquiv*` row. Catalogue: new entries for `Applications/IVP/VectorField.lean`, `Chebyshev/AnalyticPolynomial.lean`, the two `Analyticity.lean` modules, the spectra modules and `CharacterTopology.lean`; the Taylor entry gains `Taylor/Polynomial.lean`'s faces; the example entry records the five layers and the retired radius-two statement. |
| `exterior/paper/v5/main.tex` | One citation token at line 1414: `Example1421.Cert.main_existsUnique` → `main_theorem`. No prose changed. Full audit, including eleven citations checked and left alone, in `tmp/autonomous_agenda_2026_09_13/TASK2_PAPER_CITATIONS.md`. |

Rebuilds (three consecutive `pdflatex -synctex=1 -interaction=nonstopmode` runs each, identical output):
ground note 45 pp / 0 errors / 0 overfull / 0 underfull (was 43 pp, 0 overfull);
companion 57 pp / 0 errors / 0 overfull / 25 underfull (was 56 pp, 0 overfull, 23 underfull);
paper v5 23 pp / 0 errors / 0 overfull / 0 underfull (unchanged).

Acceptance: every RETIRED/RENAMED old name above is absent from the two `.tex` files, the
glossary, `ARCHITECTURE.md`, `SKILL.md` and `main.tex`, except inside dated
"renamed/retired/formerly" notes — `main_existsUnique` (companion, glossary),
`ivpComposedApprox` (ARCHITECTURE), `norm_Dphi_le` (glossary, in the aliases-to-avoid column),
`DPhiCLM`, `hasFDerivAt_Phi`, `compPolyDerivative_eq`, `banachField_eq_f`, `f_lipschitzOnWith`
and `Example1421/Lambda.lean` (companion, glossary, SKILL) — and in this file.
`Applications/IVP/Chebyshev/Lambda.lean` is a live library module and its citations stand.

## Header-diff audit (completeness check, 2026-09-13)
`git diff -U0 -- '*.lean' | grep '^[-+](theorem|lemma|def|…)'`: 70 removed / 58 added declaration header lines. Every removed
header not matched by a RENAMES.md row falls in one of two classes:
- **Pre-TASK-2 removals (2026-09-12 Chebyshev-adapter migration of Example 14.2.1, other session; documented in
  `tmp/proposal_experiments_2026_09_06/CHEB_COMPPOLY_PROMOTION_RESULTS.md`, not in RENAMES.md by design):** `suppWindow`,
  `FCseq_Dphi_single`, `Sabar_support`, `phi_abar_toSeq_nat`, `FAseq_single` (Example1421/Certificate.lean). Uncommitted since, hence visible here.
  The private generic `FAseq_single` in `Applications/IVP/Chebyshev/Polynomial.lean` is a different declaration.
- **Restated / re-homed but still present (header line rewritten, declaration exists — verified `grep -rlw`):** `hasFPowerSeriesAt_eval`
  (Geometric/AnalyticExt.lean, now a corollary of `hasFPowerSeriesOnBall_eval`), `A_norm_le`, `hdiff`, `r₀_pos`, `ν_val_eq_q`, `A_inj`
  (Example245/Certificate.lean, Example77/Certificate.lean, KappaToy.lean — `ex_` prefix drops / H4 local calculus).
No other unaccounted header change. Verdict: RENAMES.md complete for TASK 2.

## Round 2 (R2, 2026-09-13) — review findings applied

Gates: every step built its targets green and reprinted its endpoints byte-identically against
`TASK2_axioms_after_T.txt`; the full 18-endpoint probe is saved as `TASK2_axioms_after_R2.txt`
(byte-identical). Three consecutive full `lake build`s: 4,026 jobs. Backups of every touched file:
`tmp/autonomous_agenda_2026_09_13/backup_task2_R2/`.

### RETIRED (R2; deleted, replacement named)
| old | replacement | file | step | reason |
|---|---|---|---|---|
| `Example1421.Cert.lipschitzBound_f_cpoly` | `IVP.vectorField_lipschitzOnWith` (internal to the faces) | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | R2-1 | the three Chebyshev solution faces no longer take `{K} (hK)`; the Lipschitz constant `∑ l, lipschitzBound (f l) R` is chosen inside the face (`R ≥ 0` from `hR`), so the example states no syntactic number. Statements of `main_solution_existsUnique*` and `analytic_solution_existsUnique_radius_one` literally unchanged |
| `Example81.Cert.Df_diff_norm_le` (private) | `IVP.StdIVPData.Z₂_le_of_compPoly` + `CompPoly.norm_fderiv_evalBanach_sub_le_max` | `Examples/IVP/Taylor/Example81/Certificate.lean` | R2-5 | the Lipschitz bound of the derivative is read off the syntax (`derivativeLipschitzBound (X² − X) = 2`, radius-free); `Z₂_le_cert` keeps its name, statement and its single `native_decide` (`…Z₂_le_cert._native.native_decide.ax_1_1`) |
| `Example83.Cert.D₂_lorenz`, `Example83.Cert.hD₂_lorenz`, `Example83.Cert.Df_diff_norm_le` (all private) | `IVP.StdIVPData.Z₂_le_of_compPoly` (`hinactive` for the linear first equation, `hB` with `B = 2`) | `Examples/IVP/Taylor/Example83/Certificate.lean` | R2-5 | idem; the Hessian table and its `pderiv` check are replaced by the syntactic constant, `{1, 2}` active set and the `native_decide` block-norm check unchanged (`…Z₂_le_cert._native.native_decide.ax_1_1`) |
| `Example81.fderiv_G_scalar_tail` | `IVP.StdIVPData.Z₁_le_of_compPoly` / `Z₁_le_exact_of_compPoly` (tail plumbing discharged inside `StdIVPData.Z₁_le`) | `Examples/IVP/Taylor/Example81/Algebra.lean` | R2-6 | zero consumers after `Z₁_le_cert`/`Z₁_le_exact` became one call each; `Df`, `Df_eq_fderiv`, `Df_norm_le` (native-bearing), `Df_eq_leftMul` untouched |
| `Example83.fderiv_G_lorenz_tail` | idem | `Examples/IVP/Taylor/Example83/Algebra.lean` | R2-6 | idem |
| `Example81.Cert.defect_norm_lt_one`, `Example83.Cert.defect_norm_lt_one` (private) | `IVP.StdIVPData.{x_analytic_isAnalyticSolution, analytic_eq_canonical, analytic_unique, analytic_existsUnique}_of_compPoly_of_radii`, `ivpCoeffs_zero_of_compPoly_of_radii` | `Examples/IVP/Taylor/Example8{1,3}/Analytic.lean` | R2-4 | `Z₀ < 1` is derived by the faces from the same five facts `main_theorem` consumes; `xTilde`/`xTilde_ball`/`xTilde_G_zero`/`x_analytic` stay (live consumers: `logistic_analyticOnNhd`, `lorenz_analyticOnNhd`, `lorenz_coefficients_zero`, `lorenz_complex_ivp`). `ComplexTime.lean`'s duplicated `hdefect` derivation resolved the same way (library face) |
| `Example1421.Cert.abar_toSeq_neg`, `Example1421.Cert.abar_norm_component_le` (private) | `ChebyshevIVP.StdChebIVPData.abar_toSeq_negSucc`, `StdChebIVPData.norm_abar_le_norm_symmetrize` | `Examples/IVP/Chebyshev/Example1421/Analytic.lean` | R2-7 | bundle-level facts (`ā` is one-sided); `abar_norm_le` is now a one-liner through the bundle lemma and `Sabar_norm_le` |

### ADDED (R2; library faces, all sorry-free, axioms exactly `propext, Classical.choice, Quot.sound`)
| declaration | file | step | role |
|---|---|---|---|
| `IVP.vectorField_lipschitzOnWith` | `Applications/IVP/VectorField.lean` (+ import `CompPoly/Bounds`) | R2-1 | `LipschitzOnWith (toNNReal (∑ l, lipschitzBound (f l) R)) (vectorField f) (closedBall 0 R)` for `R ≥ 0`; the internal Lipschitz witness of the Chebyshev solution faces |
| `IVP.StdIVPData.ivpCoeffs_zero_of_compPoly_of_radii` | `Applications/IVP/Taylor/Polynomial.lean` | R2-4 | `G xTilde = 0 → ivpCoeffs … xTilde = 0` with `Z₀ < 1` from the four bounds (consumer: `Example83.Cert.lorenz_coefficients_zero`) |
| `IVP.StdIVPData.x_analytic_isAnalyticSolution_of_compPoly_of_radii`, `analytic_eq_canonical_of_compPoly_of_radii`, `analytic_unique_of_compPoly_of_radii`, `analytic_existsUnique_of_compPoly_of_radii` | `Applications/IVP/Taylor/Analytic.lean` (+ import `Taylor/Polynomial`) | R2-4 | the Taylor analytic faces from the bounds; the last two choose the zero via `existsUnique_of_compPoly`; mirror of `Chebyshev/AnalyticPolynomial.lean` |
| `MvPolyBridge.CompPoly.norm_fderiv_evalBanach_sub_le`, `norm_fderiv_evalBanach_sub_le_max` | `Algebra/Polynomial/CompPoly/WeightedL1.lean` | R2-5 | Lipschitz bound of `fderiv (evalBanach p)` in `‖c − a‖` by `derivativeLipschitzBound` (Taylor face of `Chebyshev.norm_derivative_sub_le_of_norm_sub`, no factor 2) |
| `IVP.StdIVPData.Z₂_le_of_compPoly` | `Applications/IVP/Taylor/Polynomial.lean` | R2-5 | Taylor `Z₂` socket on `ivp_Z₂_le`: `(active) (hcomp_le : native block-norm check, first argument) (hr₀) (hinactive) (hB)`; derives differentiability, `0 ≤ B`, `0 ≤ Z₂` |
| `IVP.StdIVPData.Z₁_le`, `Z₁_le_exact` (+ private `composedApprox_sub_fderiv_G_toSeq`) | `Applications/IVP/Taylor/Standard.lean` | R2-6 | generic `Z₁` recipe / exact-column faces with the `hfin`/`htail` plumbing discharged (`composedApprox_toCLM_tail` + `fderiv_G_tail`) |
| `IVP.StdIVPData.Z₁_le_of_compPoly`, `Z₁_le_exact_of_compPoly` | `Applications/IVP/Taylor/Polynomial.lean` | R2-6 | the same at `φ := banachField f_cpoly`; consumers `Example8{1,3}.Cert.Z₁_le_cert`, `Example81.Cert.Z₁_le_exact` (one call each, the example's own `Df`, `Df_eq_fderiv`, `Df_norm_le`) |
| `ChebyshevIVP.StdChebIVPData.abar_toSeq_negSucc`, `norm_abar_le_norm_symmetrize` | `Applications/IVP/Chebyshev/Standard.lean` (+ import `Chebyshev/Evaluation`) | R2-7 | one-sided storage of `ā` and `‖ā l‖ ≤ ‖S(ā l)‖` |
| `Example1421.two_le_ν_val` | `Examples/IVP/Chebyshev/Example1421/Algebra.lean` | R2-8 | `(2 : ℝ) ≤ ν_val`, replaces three inlined `by rw [show (ν_val : ℝ) = 2 from rfl]` |

### RESTATED (R2; same name, signature changed)
| declaration | file | step | change |
|---|---|---|---|
| `ChebyshevIVP.StdChebIVPData.solution_existsUnique_of_compPoly`, `solution_existsUnique_of_two_le_of_compPoly`, `analytic_solution_existsUnique_of_two_le_of_compPoly` | `Applications/IVP/Chebyshev/AnalyticPolynomial.lean` | R2-1 | `{K : NNReal} (hK : …)` removed; conclusions unchanged |
| `ChebyshevIVP.StdChebIVPData.Z₂_le_of_compPoly_max` | `Applications/IVP/Chebyshev/Polynomial.lean` | R2-2 | `hB` quantified over `c ∈ closedBall ā r₀` instead of all `c`; docstring says which radii the constant is taken at (degree ≤ 2 ⇒ radius-free) |
| `IVP.StdIVPData.existsUnique_of_compPoly` | `Applications/IVP/Taylor/Polynomial.lean` | R2-3 | `hZ₀ : Z₀_norm … ≤ Z₀` → `hZ₀fin : finiteBlockMatrixNorm ν d.defect.finBlock ≤ Z₀` (matches its sibling and the Chebyshev face); Ex 8.1/8.3 `main_theorem` drop `data.Z₀_le` |
| `IVP.ivp_Z₂_le` | `Applications/IVP/Taylor/Operator.lean` | R2-5 | `c`, `hc` moved before `active`; `hzero` and `hDφ_diff` are stated at the point `c` only (strictly more general; sole other consumer `Theorem.lean` adapted with `fun h j hj => hzero c h j hj`) |
| `RadiiPolynomial.Gelfand.pointwiseTopology` | `Analysis/SequenceSpace/CharacterTopology.lean` | R2-8 | `R` explicit; the three consumers (`Geometric/Spectrum`, `Chebyshev/LaurentSpectrum`, `Chebyshev/Spectrum/Topology`) drop `(R := ℝ)` |
| `Example8{1,3}.Cert.main_theorem`, `ivp_main_theorem`, `Z₁_le_cert`, `Z₂_le_cert`, `Example81.Cert.Z₁_le_exact`, `Example8{1,3}.Cert.{x_analytic_isAnalyticSolution, analytic_eq_canonical, analytic_unique, analytic_existsUnique}`, `Example83.Cert.lorenz_coefficients_zero`, `Example1421.Cert.{main_solution_existsUnique, _contractive, _radius_one, analytic_solution_existsUnique_radius_one, Z₂_le, abar_norm_le}` | examples | R2 | bodies only (proof terms retargeted to the faces; the no-op cast adaptors `Y₀_le.trans (by … exact_mod_cast le_refl _)` and `fun c hc => Z₂_le_cert c hc` dropped); statements unchanged; axiom sets byte-identical |

Docstrings rewritten (R2-8): `Applications/IVP/Taylor/Analytic.lean` module header (three tiers of faces),
`Applications/IVP/Chebyshev/Standard.lean` "Deferred to Example Level" → "Certificate faces",
`Applications/IVP/Chebyshev/Polynomial.lean` "Certificate faces" paragraph + `norm_compPolyDerivative_le`
(system face kept for a future system-level `Z₁` theorem), `Example1421/Certificate.lean` header
(`Z₀_finBlockNorm_le` is the `Z₀` input), `Example1421/Algebra.lean` §4 audit witnesses
(`computed_DF_columns`/`computed_DF_entries`/`rawDerivative_single_eq_dataDF`). Dead imports removed
from `Example1421/Algebra.lean`: `Analysis/SequenceSpace/Chebyshev/Bordered`, `Certification/LeanCertAdapter`,
`Algebra/Polynomial` (build-verified).


## Independent-review fixes (Codex, 2026-09-13)

The four findings in `tmp/autonomous_agenda_2026_09_13/review_codex/REVIEW.md` are resolved.
`MakeCompPoly.lean` now synthesizes the input lambda before reification; the production
polynomial example adds `rationalConstant_reified`, `algebraMapConstant_reified`, and
`affineConstant_reified`. No existing declaration was renamed or removed.

Experimental `BorderedCheb` exports `instCompleteSpace` and `instNormOneClass`; downstream
residual and exact multiplier-norm checks use these instances directly. It remains in tmp.
The three quadratic-bound docstrings now qualify the syntactic AST presentation.
The header audit above corrects the old Example1421 `FAseq_single` removal's classification.

The canonical tracked `.claude/skills/radii-poly-api-design/SKILL.md` now incorporates the
current interface guidance while preserving its original core description and UMP doctrine.
Both `~/.agents/skills/radii-poly-api-design/SKILL.md` and
`~/.claude/skills/radii-poly-api-design/SKILL.md` are byte-identical mirrors of it; this
supersedes the earlier global-Claude-only skill update recorded in the writeup table.

Gates: full build 4,026 jobs; 51/51 experiment checks; frozen 18-endpoint axiom output
byte-identical after the existing label rename; folded consumer/bridge checks and skill
validation pass. No `.tex` or curated-memory edits, commits, or pushes in this correction.
Evidence and Claude handoff: `tmp/autonomous_agenda_2026_09_13/review_fixes_codex/`.

## L001-HeadTailGeneric promotion (G1, 2026-10-01)

Scratch declarations of the S027 unit (`tmp/units/S027-HeadTailColumns/freeze/v1/HeadTailColumns.lean`) and of filtration-probe slice 25 (`tmp/filtration_probe/freeze_slice25_v2/FourierZ1Window.lean`) promoted to the library by unit L001 (contract `tmp/units/L001-HeadTailGeneric/contract/v2/`). Every renamed, generalized or compatibility-specialization row of its MIGRATION_TABLE.md; the scratch files stay frozen and are not imported. Test-only rows live in `Examples/tests/FZ/HeadTail*.lean`.

| old | new | file | step | reason |
|---|---|---|---|---|
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.norm_ofReal_one_pos` | `RadiiPolynomial.lpOneAlg.norm_ofReal_one_pos` | `Analysis/SequenceSpace/WeightedL1/Columns.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.colRatio` | `RadiiPolynomial.lpOneAlg.colRatio` | `Analysis/SequenceSpace/WeightedL1/Columns.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.colRatio_nonneg` | `RadiiPolynomial.lpOneAlg.colRatio_nonneg` | `Analysis/SequenceSpace/WeightedL1/Columns.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.cols_le_opNorm` | `RadiiPolynomial.lpOneAlg.cols_le_opNorm` | `Analysis/SequenceSpace/WeightedL1/Columns.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.colRatio_le_opNorm` | `RadiiPolynomial.lpOneAlg.colRatio_le_opNorm` | `Analysis/SequenceSpace/WeightedL1/Columns.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.opNorm_le_iff_cols` | `RadiiPolynomial.lpOneAlg.opNorm_le_iff_cols` | `Analysis/SequenceSpace/WeightedL1/Columns.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.colRatio_bddAbove` | `RadiiPolynomial.lpOneAlg.colRatio_bddAbove` | `Analysis/SequenceSpace/WeightedL1/Columns.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.opNorm_eq_iSup_cols` | `RadiiPolynomial.lpOneAlg.opNorm_eq_iSup_cols` | `Analysis/SequenceSpace/WeightedL1/Columns.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.norm_diagRaw_le` | `RadiiPolynomial.lpOneAlg.norm_diagCLM_apply_le` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.D_r` | `RadiiPolynomial.lpOneAlg.diagCLM` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.toRealSeq_D_r` | `RadiiPolynomial.lpOneAlg.toRealSeq_diagCLM` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.D_r_single` | `RadiiPolynomial.lpOneAlg.diagCLM_single` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.headSymbol` | `RadiiPolynomial.lpOneAlg.headSymbol` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.norm_headSymbol_le` | `RadiiPolynomial.lpOneAlg.norm_headSymbol_le` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.P_H` | `RadiiPolynomial.lpOneAlg.headProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.Q_H` | `RadiiPolynomial.lpOneAlg.tailProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.Q_H_eq` | `RadiiPolynomial.lpOneAlg.tailProj_eq_one_sub` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.toRealSeq_P_H` | `RadiiPolynomial.lpOneAlg.toRealSeq_headProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.toRealSeq_Q_H` | `RadiiPolynomial.lpOneAlg.toRealSeq_tailProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.P_H_single` | `RadiiPolynomial.lpOneAlg.headProj_single` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.Q_H_single` | `RadiiPolynomial.lpOneAlg.tailProj_single` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.P_H_comp_P_H` | `RadiiPolynomial.lpOneAlg.headProj_comp_headProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.P_H_comp_Q_H` | `RadiiPolynomial.lpOneAlg.headProj_comp_tailProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.Q_H_comp_P_H` | `RadiiPolynomial.lpOneAlg.tailProj_comp_headProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.Q_H_comp_Q_H` | `RadiiPolynomial.lpOneAlg.tailProj_comp_tailProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.P_H_add_Q_H` | `RadiiPolynomial.lpOneAlg.headProj_add_tailProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.norm_add_of_head_tail` | `RadiiPolynomial.lpOneAlg.norm_add_of_head_tail` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.colRatio_add_of_head_tail` | `RadiiPolynomial.lpOneAlg.colRatio_add_of_head_tail` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.opNorm_add_eq_iSup` | `RadiiPolynomial.lpOneAlg.opNorm_add_eq_iSup` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.head_comp_eq_zero_iff_tail_comp_eq_self` | `RadiiPolynomial.lpOneAlg.head_comp_eq_zero_iff_tail_comp_eq_self` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.colRatio_add_of_head_zero` | `RadiiPolynomial.lpOneAlg.colRatio_add_of_head_zero` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.opNorm_add_eq_iSup_of_head_zero` | `RadiiPolynomial.lpOneAlg.opNorm_add_eq_iSup_of_head_zero` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.composition_identity` | `RadiiPolynomial.HeadTail.composition_identity` | `Operators/HeadTail.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.signed_transfer` | `RadiiPolynomial.HeadTail.signed_transfer` | `Operators/HeadTail.lean` | L001 | compatibility specialization (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.opNorm_le_iff_cols` | `RadiiPolynomial.lpOneAlg.opNorm_le_iff_cols` | `Analysis/SequenceSpace/WeightedL1/Columns.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio` | `RadiiPolynomial.lpOneAlg.colRatio` | `Analysis/SequenceSpace/WeightedL1/Columns.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_nonneg` | `RadiiPolynomial.lpOneAlg.colRatio_nonneg` | `Analysis/SequenceSpace/WeightedL1/Columns.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_le_opNorm` | `RadiiPolynomial.lpOneAlg.colRatio_le_opNorm` | `Analysis/SequenceSpace/WeightedL1/Columns.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_bddAbove` | `RadiiPolynomial.lpOneAlg.colRatio_bddAbove` | `Analysis/SequenceSpace/WeightedL1/Columns.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.opNorm_eq_iSup_cols` | `RadiiPolynomial.lpOneAlg.opNorm_eq_iSup_cols` | `Analysis/SequenceSpace/WeightedL1/Columns.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.toRealSeq_diagRaw` | `RadiiPolynomial.lpOneAlg.toRealSeq_diagCLM` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.norm_diagRaw_le` | `RadiiPolynomial.lpOneAlg.norm_diagCLM_apply_le` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.diagCLM` | `RadiiPolynomial.lpOneAlg.diagCLM` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.toRealSeq_diagCLM` | `RadiiPolynomial.lpOneAlg.toRealSeq_diagCLM` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.norm_diagCLM_apply_le` | `RadiiPolynomial.lpOneAlg.norm_diagCLM_apply_le` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.diagCLM_single` | `RadiiPolynomial.lpOneAlg.diagCLM_single` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.headSym` | `RadiiPolynomial.lpOneAlg.headSymbol` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.norm_headSym_le` | `RadiiPolynomial.lpOneAlg.norm_headSymbol_le` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.headP` | `RadiiPolynomial.lpOneAlg.headProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.tailQ` | `RadiiPolynomial.lpOneAlg.tailProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.toRealSeq_headP` | `RadiiPolynomial.lpOneAlg.toRealSeq_headProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.toRealSeq_tailQ` | `RadiiPolynomial.lpOneAlg.toRealSeq_tailProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.tailQ_apply` | `RadiiPolynomial.lpOneAlg.tailProj_eq_one_sub` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.headP_single` | `RadiiPolynomial.lpOneAlg.headProj_single` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.tailQ_single` | `RadiiPolynomial.lpOneAlg.tailProj_single` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.headP_comp_headP` | `RadiiPolynomial.lpOneAlg.headProj_comp_headProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.headP_comp_tailQ` | `RadiiPolynomial.lpOneAlg.headProj_comp_tailProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.tailQ_comp_headP` | `RadiiPolynomial.lpOneAlg.tailProj_comp_headProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.tailQ_comp_tailQ` | `RadiiPolynomial.lpOneAlg.tailProj_comp_tailProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.norm_headP_apply_le` | `RadiiPolynomial.lpOneAlg.norm_headProj_apply_le` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.norm_tailQ_apply_le` | `RadiiPolynomial.lpOneAlg.norm_tailProj_apply_le` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.headP_eq_self_iff` | `RadiiPolynomial.lpOneAlg.headProj_apply_eq_self_iff` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.tailQ_eq_self_iff` | `RadiiPolynomial.lpOneAlg.tailProj_apply_eq_self_iff` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.headP_comp_diagCLM` | `RadiiPolynomial.lpOneAlg.headProj_comp_diagCLM` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.tailQ_comp_diagCLM` | `RadiiPolynomial.lpOneAlg.tailProj_comp_diagCLM` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.norm_add_of_head_tail` | `RadiiPolynomial.lpOneAlg.norm_add_of_head_tail` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_add_of_head_tail` | `RadiiPolynomial.lpOneAlg.colRatio_add_of_head_tail` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.opNorm_add_eq_iSup` | `RadiiPolynomial.lpOneAlg.opNorm_add_eq_iSup` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_Z_tail` | `RadiiPolynomial.lpOneAlg.colRatio_eq_zero_of_comp_tailProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_S_head` | `RadiiPolynomial.lpOneAlg.colRatio_eq_zero_of_comp_headProj` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_Z_add_S` | `RadiiPolynomial.lpOneAlg.colRatio_add_of_comp_split` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.opNorm_joint_eq_iSup` | `RadiiPolynomial.lpOneAlg.opNorm_joint_eq_iSup` | `Analysis/SequenceSpace/WeightedL1/Diagonal.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.defect_identity_ring` | `RadiiPolynomial.HeadTail.defect_identity_ring` | `Algebra/Ring/HeadTailIdentities.lean` | L001 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.inverse_defect_ring_core` | `RadiiPolynomial.HeadTail.inverse_defect_ring` | `Algebra/Ring/HeadTailIdentities.lean` | L001 | renamed (MIGRATION_TABLE.md) |

## L003-ReesLaurent promotion (G2, 2026-10-01)

Scratch declarations of filtration-probe slices 20/23 (`tmp/filtration_probe/ReesFamily.lean`, `tmp/filtration_probe/ReesBridge.lean`) and of the S028a unit (`tmp/units/S028a-ReesEulerBridge/freeze/v2/ReesEuler.lean`, `ReesGamma.lean`) promoted to the library by unit L003 (contract `tmp/units/L003-ReesLaurent/contract/v6/`). Every renamed or generalized row of its MIGRATION_TABLE.md; the scratch files stay frozen and are not imported. Test-only rows live in `Examples/tests/RS/Rees*.lean`; deferred rows (the leakage layer, `gammaW_inv_le`, `rees_minimal_iff`, the window `winZ`) are not listed.

| old | new | file | step | reason |
|---|---|---|---|---|
| `RadiiPolynomial.FiltrationProbe.coeff_single_eq` | `RadiiPolynomial.Rees.Laurent.coeff_single_eq` | `Algebra/Rees/Laurent/Family.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.dvd_coeff_mul` | `RadiiPolynomial.Rees.Laurent.dvd_coeff_mul` | `Algebra/Rees/Laurent/Family.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.U` | `RadiiPolynomial.Rees.Laurent.U` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.mem_U_iff` | `RadiiPolynomial.Rees.Laurent.mem_U_iff` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.z` | `RadiiPolynomial.Rees.Laurent.z` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.coe_z` | `RadiiPolynomial.Rees.Laurent.coe_z` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.coe_z_apply` | `RadiiPolynomial.Rees.Laurent.coe_z_apply` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.JN` | `RadiiPolynomial.Rees.Laurent.JN` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.aN` | `RadiiPolynomial.Rees.Laurent.aN` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.u` | `RadiiPolynomial.Rees.Laurent.u` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.q` | `RadiiPolynomial.Rees.Laurent.q` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.coe_smul_U` | `RadiiPolynomial.Rees.Laurent.coe_smul_U` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.z_mul_z_eq` | `RadiiPolynomial.Rees.Laurent.z_mul_z_eq` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.z_mul_z` | `RadiiPolynomial.Rees.Laurent.z_mul_z` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.z_mul_z_of_nonneg` | `RadiiPolynomial.Rees.Laurent.z_mul_z_of_nonneg` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.z_mul_z_of_nonpos` | `RadiiPolynomial.Rees.Laurent.z_mul_z_of_nonpos` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.z_mul_z_opposite` | `RadiiPolynomial.Rees.Laurent.z_mul_z_opposite` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.z_zero` | `RadiiPolynomial.Rees.Laurent.z_zero` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.z_one_pow` | `RadiiPolynomial.Rees.Laurent.z_one_pow` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.SN` | `RadiiPolynomial.Rees.Laurent.SN` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.z_mem_SN` | `RadiiPolynomial.Rees.Laurent.z_mem_SN` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.JN_le_SN` | `RadiiPolynomial.Rees.Laurent.JN_le_SN` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.z_mem_JN_pos` | `RadiiPolynomial.Rees.Laurent.z_mem_JN_pos` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.z_mem_JN_neg` | `RadiiPolynomial.Rees.Laurent.z_mem_JN_neg` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.coe_smul_z_mul_z` | `RadiiPolynomial.Rees.Laurent.coe_smul_z_mul_z` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.exists_single_mem_JN` | `RadiiPolynomial.Rees.Laurent.exists_single_mem_JN` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.mem_JN_iff` | `RadiiPolynomial.Rees.Laurent.mem_JN_iff` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.coe_smul_z_apply` | `RadiiPolynomial.Rees.Laurent.coe_smul_z_apply` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.X_pow_add_dvd_mul_X_pow_iff` | `RadiiPolynomial.Rees.Laurent.X_pow_add_dvd_mul_X_pow_iff` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.z_mem_JN_of_tail` | `RadiiPolynomial.Rees.Laurent.z_mem_JN_of_tail` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.smul_z_mem_JN_iff` | `RadiiPolynomial.Rees.Laurent.smul_z_mem_JN_iff` | `Algebra/Rees/Laurent/Family.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.z_neg_mul_z` | `RadiiPolynomial.Rees.Laurent.z_neg_mul_z` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.coe_smul_one_apply` | `RadiiPolynomial.Rees.Laurent.coe_smul_one_apply` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.X_pow_smul_one_mem_JN` | `RadiiPolynomial.Rees.Laurent.X_pow_smul_one_mem_JN` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.contraction_fails` | `RadiiPolynomial.Rees.Laurent.contraction_fails` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.tail_span_not_ideal` | `RadiiPolynomial.Rees.Laurent.tail_span_not_ideal` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.q_of_ne_zero` | `RadiiPolynomial.Rees.Laurent.q_of_ne_zero` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.q_zero` | `RadiiPolynomial.Rees.Laurent.q_zero` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.smul_q_mem_JN_iff` | `RadiiPolynomial.Rees.Laurent.smul_q_mem_JN_iff` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.q_mul_q_sub` | `RadiiPolynomial.Rees.Laurent.q_mul_q_sub` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.q_sq_sub` | `RadiiPolynomial.Rees.Laurent.q_sq_sub` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.coe_u` | `RadiiPolynomial.Rees.Laurent.coe_u` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.u_pow_coeff` | `RadiiPolynomial.Rees.Laurent.u_pow_coeff` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.u_pow_odd_mem` | `RadiiPolynomial.Rees.Laurent.u_pow_odd_mem` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.u_pow_even_not_mem` | `RadiiPolynomial.Rees.Laurent.u_pow_even_not_mem` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.instUAddCommGroup` | `RadiiPolynomial.Rees.Laurent.instUAddCommGroup` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.instUZero` | `RadiiPolynomial.Rees.Laurent.instUZero` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.zero_selection_eq_existing` | `RadiiPolynomial.Rees.Laurent.zero_selection_eq_existing` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.diagL` | `RadiiPolynomial.Rees.Laurent.diagL` | `Algebra/Rees/Laurent/Euler.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.coeff_diagL` | `RadiiPolynomial.Rees.Laurent.coeff_diagL` | `Algebra/Rees/Laurent/Euler.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.diagL_single` | `RadiiPolynomial.Rees.Laurent.diagL_single` | `Algebra/Rees/Laurent/Euler.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaL` | `RadiiPolynomial.Rees.Laurent.deltaL` | `Algebra/Rees/Laurent/Euler.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.coeff_deltaL` | `RadiiPolynomial.Rees.Laurent.coeff_deltaL` | `Algebra/Rees/Laurent/Euler.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaL_mem_U` | `RadiiPolynomial.Rees.Laurent.deltaL_mem_U` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaU` | `RadiiPolynomial.Rees.Laurent.deltaU` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.coe_deltaU` | `RadiiPolynomial.Rees.Laurent.coe_deltaU` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.coeff_deltaU` | `RadiiPolynomial.Rees.Laurent.coeff_deltaU` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaU_z` | `RadiiPolynomial.Rees.Laurent.deltaU_z` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaU_mul` | `RadiiPolynomial.Rees.Laurent.deltaU_mul` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaU_one` | `RadiiPolynomial.Rees.Laurent.deltaU_one` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.U_ext` | `RadiiPolynomial.Rees.Laurent.U_ext` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.coeff_smul` | `RadiiPolynomial.Rees.Laurent.coeff_smul` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.coordMod` | `RadiiPolynomial.Rees.Laurent.coordMod` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.idxPiece` | `RadiiPolynomial.Rees.Laurent.idxPiece` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.headMod` | `RadiiPolynomial.Rees.Laurent.headMod` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.tailMod` | `RadiiPolynomial.Rees.Laurent.tailMod` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.reesPiece` | `RadiiPolynomial.Rees.Laurent.reesPiece` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaU_mem_JN` | `RadiiPolynomial.Rees.Laurent.deltaU_mem_JN` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaU_smul` | `RadiiPolynomial.Rees.Laurent.deltaU_smul` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaU_mem_idxPiece` | `RadiiPolynomial.Rees.Laurent.deltaU_mem_idxPiece` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaU_mem_reesPiece` | `RadiiPolynomial.Rees.Laurent.deltaU_mem_reesPiece` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaU_mem_headMod` | `RadiiPolynomial.Rees.Laurent.deltaU_mem_headMod` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaU_mem_tailMod` | `RadiiPolynomial.Rees.Laurent.deltaU_mem_tailMod` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.diagU` | `RadiiPolynomial.Rees.Laurent.diagU` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.coeff_diagU` | `RadiiPolynomial.Rees.Laurent.coeff_diagU` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.PH` | `RadiiPolynomial.Rees.Laurent.PH` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.coeff_PH` | `RadiiPolynomial.Rees.Laurent.coeff_PH` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.diagU_z` | `RadiiPolynomial.Rees.Laurent.diagU_z` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.PH_z` | `RadiiPolynomial.Rees.Laurent.PH_z` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.PH_comp_PH` | `RadiiPolynomial.Rees.Laurent.PH_comp_PH` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.PH_comp_one_sub` | `RadiiPolynomial.Rees.Laurent.PH_comp_one_sub` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.one_sub_comp_PH` | `RadiiPolynomial.Rees.Laurent.one_sub_comp_PH` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaU_eq_diagU` | `RadiiPolynomial.Rees.Laurent.deltaU_eq_diagU` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.diagAlgHom` | `RadiiPolynomial.Rees.Laurent.diagAlgHom` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.qDelta` | `RadiiPolynomial.Rees.Laurent.qDelta` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.qDelta_eq_diagU` | `RadiiPolynomial.Rees.Laurent.qDelta_eq_diagU` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.qDelta_z` | `RadiiPolynomial.Rees.Laurent.qDelta_z` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.diagU_comm_diagU` | `RadiiPolynomial.Rees.Laurent.diagU_comm_diagU` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.PH_comm_diagU` | `RadiiPolynomial.Rees.Laurent.PH_comm_diagU` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.PH_comm_deltaU` | `RadiiPolynomial.Rees.Laurent.PH_comm_deltaU` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.PH_comm_qDelta` | `RadiiPolynomial.Rees.Laurent.PH_comm_qDelta` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.PH_qDelta_tail` | `RadiiPolynomial.Rees.Laurent.PH_qDelta_tail` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.PH_add_qDelta_tail` | `RadiiPolynomial.Rees.Laurent.PH_add_qDelta_tail` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.specCoeff` | `RadiiPolynomial.Rees.Laurent.specCoeff` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.rawHead` | `RadiiPolynomial.Rees.Laurent.rawHead` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.rawDiag` | `RadiiPolynomial.Rees.Laurent.rawDiag` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.specCoeff_deltaU` | `RadiiPolynomial.Rees.Laurent.specCoeff_deltaU` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.specCoeff_qDelta` | `RadiiPolynomial.Rees.Laurent.specCoeff_qDelta` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.specCoeff_PH` | `RadiiPolynomial.Rees.Laurent.specCoeff_PH` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.specCoeff_z` | `RadiiPolynomial.Rees.Laurent.specCoeff_z` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.rawHead_rawDiag` | `RadiiPolynomial.Rees.Laurent.rawHead_rawDiag` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.rawHead_rawDiag_tail` | `RadiiPolynomial.Rees.Laurent.rawHead_rawDiag_tail` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaU_X_pow_smul_one` | `RadiiPolynomial.Rees.Laurent.deltaU_X_pow_smul_one` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.X_pow_smul_one_ne_zero` | `RadiiPolynomial.Rees.Laurent.X_pow_smul_one_ne_zero` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaU_not_injOn_JN` | `RadiiPolynomial.Rees.Laurent.deltaU_not_injOn_JN` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.tailMod_le_JN` | `RadiiPolynomial.Rees.Laurent.tailMod_le_JN` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.X_pow_smul_one_not_mem_tailMod` | `RadiiPolynomial.Rees.Laurent.X_pow_smul_one_not_mem_tailMod` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.PH_mem_JN` | `RadiiPolynomial.Rees.Laurent.PH_mem_JN` | `Algebra/Rees/Laurent/Euler.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.head_coeff_dvd_of_mem_JN` | `RadiiPolynomial.Rees.Laurent.head_coeff_dvd_of_mem_JN` | `Algebra/Rees/Laurent/Euler.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.head_coeff_dvd_PH_mul_tail` | `RadiiPolynomial.Rees.Laurent.head_coeff_dvd_PH_mul_tail` | `Algebra/Rees/Laurent/Euler.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.no_inv_X_pow` | `RadiiPolynomial.Rees.Laurent.no_inv_X_pow` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.no_inv_X_pow_aN` | `RadiiPolynomial.Rees.Laurent.no_inv_X_pow_aN` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.qDelta_bijOn_tail` | `RadiiPolynomial.Rees.Laurent.qDelta_bijOn_tail` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.deltaU_bijOn_tail` | `RadiiPolynomial.Rees.Laurent.deltaU_bijOn_tail` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.isUnit_of_surjOn_tail` | `RadiiPolynomial.Rees.Laurent.isUnit_of_surjOn_tail` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.qDelta_bijOn_tail_iff` | `RadiiPolynomial.Rees.Laurent.qDelta_bijOn_tail_iff` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesEuler.z_ne_zero` | `RadiiPolynomial.Rees.Laurent.z_ne_zero` | `Algebra/Rees/Laurent/Euler.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesGamma.z_sub_mul_z` | `RadiiPolynomial.Rees.Laurent.z_sub_mul_z` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesGamma.PH_z_mul_z_head` | `RadiiPolynomial.Rees.Laurent.PH_z_mul_z_head` | `Algebra/Rees/Laurent/GammaCutoff.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesGamma.X_pow_eps_split` | `RadiiPolynomial.Rees.Laurent.X_pow_eps_split` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesGamma.X_pow_eps_smul_z_mem_JN` | `RadiiPolynomial.Rees.Laurent.X_pow_eps_smul_z_mem_JN` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesGamma.gammaW_eq_eval_annihilator` | `RadiiPolynomial.Rees.Laurent.gammaW_eq_eval_annihilator` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesGamma.weight_eq_rees` | `RadiiPolynomial.Rees.Laurent.weight_eq_rees` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesGamma.eval_eps_div_eval_aN` | `RadiiPolynomial.Rees.Laurent.eval_eps_div_eval_aN` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesGamma.z_mul_z_jstar` | `RadiiPolynomial.Rees.Laurent.z_mul_z_jstar` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesBridge.gammaW` | `RadiiPolynomial.Rees.Laurent.gammaW` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesBridge.gammaW_pos` | `RadiiPolynomial.Rees.Laurent.gammaW_pos` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesBridge.eps` | `RadiiPolynomial.Rees.Laurent.eps` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesBridge.eps_spec` | `RadiiPolynomial.Rees.Laurent.eps_spec` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesBridge.aN` | `RadiiPolynomial.Rees.Laurent.aN` | `Algebra/Rees/Laurent/Family.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesBridge.sgn'` | `RadiiPolynomial.Rees.Laurent.sgn'` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesBridge.jstar` | `RadiiPolynomial.Rees.Laurent.jstar` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesBridge.aN_le_eps` | `RadiiPolynomial.Rees.Laurent.aN_le_eps` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesBridge.eps_sub_aN` | `RadiiPolynomial.Rees.Laurent.eps_sub_aN` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesBridge.eps_jstar` | `RadiiPolynomial.Rees.Laurent.eps_jstar` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesBridge.jstar_tail` | `RadiiPolynomial.Rees.Laurent.jstar_tail` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesBridge.aN_eq_min` | `RadiiPolynomial.Rees.Laurent.aN_eq_min` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesBridge.weight_eq` | `RadiiPolynomial.Rees.Laurent.weight_eq` | `Algebra/Rees/Laurent/Gamma.lean` | L003 | generalized (MIGRATION_TABLE.md) |

## L002-FourierTailWindow promotion (G2, 2026-10-01)

Scratch declarations of filtration-probe slice 25 (`tmp/filtration_probe/freeze_slice25_v2/FourierZ1Window.lean`), of the S027 unit (`tmp/units/S027-HeadTailColumns/freeze/v1/HeadTailColumns.lean`, Fourier section) and of the S028b unit (`tmp/units/S028b-FourierSemilinearZ1/freeze/v1/FourierSemilinear.lean`) promoted to the library by unit L002 (contract `tmp/units/L002-FourierTailWindow/contract/v2/`; every renamed/generalized row of its MIGRATION_TABLE.md; L001 rows are in the block above). Namespace `RadiiPolynomial.Fourier`; generalized rows are stated over `[NormedField 𝕜]` (`[CompleteSpace 𝕜]` where multiplication occurs, `[NontriviallyNormedField 𝕜]` for operator norms) instead of `RCLike`.

| old | new | file | step | reason |
|---|---|---|---|---|
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.norm_eq_tsum_coeff` | `RadiiPolynomial.Fourier.norm_eq_tsum_coeff` | `Analysis/SequenceSpace/Fourier/Support.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.summable_coeff` | `RadiiPolynomial.Fourier.summable_coeff` | `Analysis/SequenceSpace/Fourier/Support.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.winZ` | `RadiiPolynomial.Fourier.winZ` | `Analysis/SequenceSpace/Fourier/Support.lean` | L002 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.mem_winZ` | `RadiiPolynomial.Fourier.mem_winZ` | `Analysis/SequenceSpace/Fourier/Support.lean` | L002 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.winZ_nonempty` | `RadiiPolynomial.Fourier.winZ_nonempty` | `Analysis/SequenceSpace/Fourier/Support.lean` | L002 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.le_sup'_of_far_antitone` | `RadiiPolynomial.Fourier.le_sup'_of_far_antitone` | `Analysis/SequenceSpace/Fourier/Support.lean` | L002 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.iSup_eq_sup'_of_far_antitone` | `RadiiPolynomial.Fourier.iSup_eq_sup'_of_far_antitone` | `Analysis/SequenceSpace/Fourier/Support.lean` | L002 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.toRealSeq_mul_single` | `RadiiPolynomial.Fourier.toRealSeq_mul_single` | `Analysis/SequenceSpace/Fourier/Support.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.Hd` | `RadiiPolynomial.Fourier.defectHead` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.Tl` | `RadiiPolynomial.Fourier.defectTail` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.defect` | `RadiiPolynomial.Fourier.defect` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.defect_eq` | `RadiiPolynomial.Fourier.defect_eq` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.Hd_single` | `RadiiPolynomial.Fourier.defectHead_single` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.Tl_single` | `RadiiPolynomial.Fourier.defectTail_single` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_Hd_head` | `RadiiPolynomial.Fourier.colRatio_defectHead_head` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_Hd_eq` | `RadiiPolynomial.Fourier.colRatio_defectHead_eq` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_Hd_far` | `RadiiPolynomial.Fourier.colRatio_defectHead_far` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.aCol` | `RadiiPolynomial.Fourier.headCol` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_Hd_eq_aCol` | `RadiiPolynomial.Fourier.colRatio_defectHead_eq_headCol` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.sCol` | `RadiiPolynomial.Fourier.tailCol` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_Tl` | `RadiiPolynomial.Fourier.colRatio_defectTail` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_Tl_eq_sCol` | `RadiiPolynomial.Fourier.colRatio_defectTail` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_Tl_far_pos` | `RadiiPolynomial.Fourier.colRatio_defectTail_far_pos` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_Tl_far_neg` | `RadiiPolynomial.Fourier.colRatio_defectTail_far_neg` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.headP_comp_Hd` | `RadiiPolynomial.Fourier.headProj_comp_defectHead` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.Hd_comp_headP` | `RadiiPolynomial.Fourier.defectHead_comp_headProj` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.tailQ_comp_Tl` | `RadiiPolynomial.Fourier.tailProj_comp_defectTail` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_defect` | `RadiiPolynomial.Fourier.colRatio_defect` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.opNorm_defect_eq_iSup` | `RadiiPolynomial.Fourier.opNorm_defect_eq_iSup` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_defect_far_eq_Tl` | `RadiiPolynomial.Fourier.colRatio_defect_far_eq_defectTail` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_Tl_succ_le` | `RadiiPolynomial.Fourier.colRatio_defectTail_succ_le` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_Tl_pred_le` | `RadiiPolynomial.Fourier.colRatio_defectTail_pred_le` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_defect_succ_le_of` | `RadiiPolynomial.Fourier.colRatio_defect_succ_le_of` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_defect_pred_le_of` | `RadiiPolynomial.Fourier.colRatio_defect_pred_le_of` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.opNorm_defect_eq_sup'_of` | `RadiiPolynomial.Fourier.opNorm_defect_eq_sup'_of` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_defect_far_antitone` | `RadiiPolynomial.Fourier.colRatio_defect_far_antitone` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.opNorm_defect_eq_sup'` | `RadiiPolynomial.Fourier.opNorm_defect_eq_sup'` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.colRatio_defect_explicit` | `RadiiPolynomial.Fourier.colRatio_defect_explicit` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.opNorm_defect_eq_sup'_explicit` | `RadiiPolynomial.Fourier.opNorm_defect_eq_sup'_explicit` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.defect_attained` | `RadiiPolynomial.Fourier.defect_attained` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.window_eq_of_le` | `RadiiPolynomial.Fourier.window_eq_of_le` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.opNorm_defect_eq_sup'_first` | `RadiiPolynomial.Fourier.opNorm_defect_eq_sup'_first` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.opNorm_joint_defect_eq_sup'` | `RadiiPolynomial.Fourier.opNorm_joint_defect_eq_sup'` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.opNorm_joint_defect_sub_eq_sup'` | `RadiiPolynomial.Fourier.opNorm_joint_defect_sub_eq_sup'` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.toRealSeq_one` | `RadiiPolynomial.Fourier.toRealSeq_one` | `Analysis/SequenceSpace/Fourier/Support.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.band_one` | `RadiiPolynomial.Fourier.band_one` | `Analysis/SequenceSpace/Fourier/Support.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierZ1Window.band_single` | `RadiiPolynomial.Fourier.band_single` | `Analysis/SequenceSpace/Fourier/Support.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.H` | `RadiiPolynomial.Fourier.winZ` | `Analysis/SequenceSpace/Fourier/Support.lean` | L002 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.mem_H` | `RadiiPolynomial.Fourier.mem_winZ` | `Analysis/SequenceSpace/Fourier/Support.lean` | L002 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.HeadTailColumns.colRatio_geom` | `RadiiPolynomial.Fourier.colRatio_geom` | `Analysis/SequenceSpace/Fourier/TailWindow.lean` | L002 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.band_mul` | `RadiiPolynomial.Fourier.band_mul` | `Analysis/SequenceSpace/Fourier/Support.lean` | L002 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.band_pow` | `RadiiPolynomial.Fourier.band_pow` | `Analysis/SequenceSpace/Fourier/Support.lean` | L002 | generalized (MIGRATION_TABLE.md) |

## L004-FourierGammaLeakage promotion (G3, 2026-10-01)

Scratch declarations of the S028b unit (`tmp/units/S028b-FourierSemilinearZ1/freeze/v1/FourierSemilinearGamma.lean`) and of filtration-probe `ReesBridge` (`tmp/filtration_probe/ReesBridge.lean`, `gammaW_inv_le`) promoted to the library by unit L004 (contract `tmp/units/L004-FourierGammaLeakage/contract/v4/`; every renamed/generalized row of its MIGRATION_TABLE.md). Namespace `RadiiPolynomial.Fourier` (`gammaW_inv_le` in `RadiiPolynomial.Rees.Laurent`); the Γ faces are stated over a real-scalar field `[NormedAlgebra ℝ 𝕜]` instead of `ℂ`, the tail estimate over any bounded diagonal `diagCLM r C hr`.

| old | new | file | step | reason |
|---|---|---|---|---|
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.gammaC` | `RadiiPolynomial.Fourier.gammaScalar` | `Analysis/SequenceSpace/Fourier/GammaLeakage.lean` | L004 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.norm_gammaC` | `RadiiPolynomial.Fourier.norm_gammaScalar` | `Analysis/SequenceSpace/Fourier/GammaLeakage.lean` | L004 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.gammaC_ne_zero` | `RadiiPolynomial.Fourier.gammaScalar_ne_zero` | `Analysis/SequenceSpace/Fourier/GammaLeakage.lean` | L004 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.norm_gamma_head_le` | `RadiiPolynomial.Fourier.norm_gamma_head_le` | `Analysis/SequenceSpace/Fourier/GammaLeakage.lean` | L004 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.norm_gamma_inv_head_le` | `RadiiPolynomial.Fourier.norm_gamma_inv_head_le` | `Analysis/SequenceSpace/Fourier/GammaLeakage.lean` | L004 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.DΓ` | `RadiiPolynomial.Fourier.gammaDiag` | `Analysis/SequenceSpace/Fourier/GammaLeakage.lean` | L004 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.DΓplus` | `RadiiPolynomial.Fourier.gammaInvDiag` | `Analysis/SequenceSpace/Fourier/GammaLeakage.lean` | L004 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.DΓ_comp_DΓplus` | `RadiiPolynomial.Fourier.gammaDiag_comp_gammaInvDiag` | `Analysis/SequenceSpace/Fourier/GammaLeakage.lean` | L004 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.DΓ_entry_eq_rees` | `RadiiPolynomial.Fourier.gammaDiag_entry_eq_rees` | `Analysis/SequenceSpace/Fourier/GammaLeakage.lean` | L004 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.norm_DΓplus_leak_le` | `RadiiPolynomial.Fourier.norm_gammaInvDiag_leak_le` | `Analysis/SequenceSpace/Fourier/GammaLeakage.lean` | L004 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.norm_head_leak_le_coeff` | `RadiiPolynomial.Fourier.norm_head_leak_le_coeff` | `Analysis/SequenceSpace/Fourier/GammaLeakage.lean` | L004 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.norm_tail_leak_le_coeff` | `RadiiPolynomial.Fourier.norm_tail_leak_le_coeff` | `Analysis/SequenceSpace/Fourier/GammaLeakage.lean` | L004 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.ReesBridge.gammaW_inv_le` | `RadiiPolynomial.Rees.Laurent.gammaW_inv_le` | `Analysis/SequenceSpace/Fourier/GammaLeakage.lean` | L004 | generalized (MIGRATION_TABLE.md) |

## L005-FourierSemilinear promotion (G3, 2026-10-01)

Scratch declarations of the S028b unit (`tmp/units/S028b-FourierSemilinearZ1/freeze/v1/FourierSemilinear.lean` and `FourierSemilinearGamma.lean`:180) promoted to the library by unit L005 (contract `tmp/units/L005-FourierSemilinear/contract/v2/`; every renamed, generalized or compatibility-specialization row of its MIGRATION_TABLE.md whose new name is an L005 declaration; the FS:180/:195 rows landed by L002 are in its block above). Namespace `RadiiPolynomial.Fourier.Semilinear`; generalized rows are stated for a general symbol `lam : ℤ → 𝕜` over a scalar field `𝕜` instead of `ℂ` and the symbol `I * k`; the compatibility specializations keep the first-order family `ikSymbol` in `SemilinearFirstOrder.lean`.

| old | new | file | step | reason |
|---|---|---|---|---|
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.norm_fourier_symbol` | `RadiiPolynomial.Fourier.Semilinear.norm_ikSymbol` | `Applications/Fourier/SemilinearFirstOrder.lean` | L005 | renamed (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.lamH` | `RadiiPolynomial.Fourier.Semilinear.lamHead` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.norm_lamH_le` | `RadiiPolynomial.Fourier.Semilinear.norm_lamHead_le` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.rTail` | `RadiiPolynomial.Fourier.Semilinear.tailInv` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.rTail_head_zero` | `RadiiPolynomial.Fourier.Semilinear.tailInv_head_zero` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.norm_rTail` | `RadiiPolynomial.Fourier.Semilinear.norm_tailInv_ikSymbol` | `Applications/Fourier/SemilinearFirstOrder.lean` | L005 | compatibility specialization (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.norm_rTail_le` | `RadiiPolynomial.Fourier.Semilinear.norm_tailInv_ikSymbol_le` | `Applications/Fourier/SemilinearFirstOrder.lean` | L005 | compatibility specialization (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.tail_symbol_ne_zero` | `RadiiPolynomial.Fourier.Semilinear.ikSymbol_ne_zero` | `Applications/Fourier/SemilinearFirstOrder.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.rTail_hmono` | `RadiiPolynomial.Fourier.Semilinear.tailInv_ikSymbol_hmono` | `Applications/Fourier/SemilinearFirstOrder.lean` | L005 | compatibility specialization (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.LamH` | `RadiiPolynomial.Fourier.Semilinear.headDiag` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.toRealSeq_LamH` | `RadiiPolynomial.Fourier.Semilinear.toRealSeq_headDiag` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.LamH_single` | `RadiiPolynomial.Fourier.Semilinear.headDiag_single` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.P_comp_LamH` | `RadiiPolynomial.Fourier.Semilinear.headProj_comp_headDiag` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.LamH_comp_P` | `RadiiPolynomial.Fourier.Semilinear.headDiag_comp_headProj` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.R_comp_P` | `RadiiPolynomial.Fourier.Semilinear.diagCLM_comp_headProj_of_head_zero` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.Φhat` | `RadiiPolynomial.Fourier.Semilinear.phiHat` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.Φ'hat` | `RadiiPolynomial.Fourier.Semilinear.phiHatDeriv` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.hasFDerivAt_Φhat` | `RadiiPolynomial.Fourier.Semilinear.hasFDerivAt_phiHat` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.toRealSeq_finset_sum` | `RadiiPolynomial.Fourier.Semilinear.toRealSeq_finset_sum` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.band_aeval` | `RadiiPolynomial.Fourier.Semilinear.band_aeval` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.b` | `RadiiPolynomial.Fourier.Semilinear.beta` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.G` | `RadiiPolynomial.Fourier.Semilinear.precondMap` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.B₀` | `RadiiPolynomial.Fourier.Semilinear.modelDeriv` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.band_b` | `RadiiPolynomial.Fourier.Semilinear.band_beta` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.Fraw` | `RadiiPolynomial.Fourier.Semilinear.rawMap` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.headEmbed` | `RadiiPolynomial.Fourier.Semilinear.headEmbed` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.Araw` | `RadiiPolynomial.Fourier.Semilinear.rawPrecond` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.toRealSeq_headEmbed` | `RadiiPolynomial.Fourier.Semilinear.toRealSeq_headEmbed` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.headEmbed_Fraw` | `RadiiPolynomial.Fourier.Semilinear.headEmbed_rawMap` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.toRealSeq_G` | `RadiiPolynomial.Fourier.Semilinear.toRealSeq_precondMap` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.hasFDerivAt_G` | `RadiiPolynomial.Fourier.Semilinear.hasFDerivAt_precondMap` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.DG_sub_B0` | `RadiiPolynomial.Fourier.Semilinear.fderiv_sub_modelDeriv` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.DG_sub_B0_hZ` | `RadiiPolynomial.Fourier.Semilinear.fderiv_sub_modelDeriv_hZ` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.norm_DG_sub_B0_eq` | `RadiiPolynomial.Fourier.Semilinear.norm_fderiv_sub_modelDeriv` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.norm_DG_sub_B0_eq_sup'` | `RadiiPolynomial.Fourier.Semilinear.norm_fderiv_sub_modelDeriv_eq_sup'_first` | `Applications/Fourier/SemilinearFirstOrder.lean` | L005 | compatibility specialization (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.DG_sub_B0_attained` | `RadiiPolynomial.Fourier.Semilinear.fderiv_sub_modelDeriv_attained` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.sCol_rTail_coeff` | `RadiiPolynomial.Fourier.Semilinear.tailCol_tailInv_ikSymbol_coeff` | `Applications/Fourier/SemilinearFirstOrder.lean` | L005 | compatibility specialization (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.norm_DG_sub_B0_eq_sup'_dN` | `RadiiPolynomial.Fourier.Semilinear.norm_fderiv_sub_modelDeriv_eq_sup'_deg` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.window_dN_eq` | `RadiiPolynomial.Fourier.Semilinear.window_deg_eq` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.norm_DG_sub_B0_real` | `RadiiPolynomial.Fourier.Semilinear.norm_restrictScalars_fderiv_sub_modelDeriv` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `RadiiPolynomial.FiltrationProbe.FourierSemilinear.norm_DG_sub_B0_le_gamma` | `RadiiPolynomial.Fourier.Semilinear.norm_fderiv_sub_modelDeriv_le_gamma` | `Applications/Fourier/Semilinear.lean` | L005 | generalized (MIGRATION_TABLE.md) |
| `MvPolyBridge.CompPoly.Chebyshev.chebDerivativeLipschitzBound_mono` | `MvPolyBridge.CompPoly.Chebyshev.derivativeLipschitzBound_mono` | `Algebra/Polynomial/CompPoly/Chebyshev/Bounds.lean` | WB-1 | sibling naming (R-CHa-2); deprecated alias kept |
| `IVP.tail_shiftDivN_sum_le` | `RadiiPolynomial.tail_shiftDivN_sum_le` | `Analysis/SequenceSpace/Geometric/Omega.lean` (from `Certification/IVP/Taylor.lean`) | WB-1 | moved to the lower layer beside `l1Weighted.norm_tailProj_eq_tailTsum`; deprecated alias kept |

## Adoption of Mathlib's `DiscreteConvolution` module (2026-10-12)

The library's namespace `DiscreteConvolution` (`Algebra/Convolution/{Basic,Ring}.lean`) duplicated `Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution` (pinned Mathlib v4.34.1), so `import Mathlib` together with `import RadiiPolynomial` failed with "environment already contains 'DiscreteConvolution.addConvolution'". `Basic.lean` now imports the Mathlib module; the duplicates are deleted, and the library-owned remainder moves to the namespace `RadiiPolynomial.DiscreteConvolution` (no compatibility aliases into `DiscreteConvolution`). Consumers cite moved library names as `RadiiPolynomial.DiscreteConvolution.<name>` and Mathlib names as `_root_.DiscreteConvolution.<name>`. Design: `exterior/tmp/discrete_convolution_design_20261011/CONSENSUS_adopt_mathlib_dc.md` (A1–A9).

### (i) RENAMED (namespace move; additive twins and nested `HasSum` helpers included)

| old | new | file | note |
|---|---|---|---|
| `DiscreteConvolution.mulFiberEquiv` | `RadiiPolynomial.DiscreteConvolution.mulFiberEquiv` | `Algebra/Convolution/Basic.lean` | namespace move; statement against Mathlib's `DiscreteConvolution.mulFiber`/`addFiber` (same FQN and statement as the deleted library fiber) |
| `DiscreteConvolution.addFiberEquiv` | `RadiiPolynomial.DiscreteConvolution.addFiberEquiv` | `Algebra/Convolution/Basic.lean` | namespace move; statement against Mathlib's `DiscreteConvolution.mulFiber`/`addFiber` (same FQN and statement as the deleted library fiber) |
| `DiscreteConvolution.sigmaMulFiberEquiv` | `RadiiPolynomial.DiscreteConvolution.sigmaMulFiberEquiv` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.sigmaAddFiberEquiv` | `RadiiPolynomial.DiscreteConvolution.sigmaAddFiberEquiv` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.delta` | `RadiiPolynomial.DiscreteConvolution.delta` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.addDelta` | `RadiiPolynomial.DiscreteConvolution.addDelta` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.delta_one_eq` | `RadiiPolynomial.DiscreteConvolution.delta_one_eq` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.addDelta_zero_eq` | `RadiiPolynomial.DiscreteConvolution.addDelta_zero_eq` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.delta_ne` | `RadiiPolynomial.DiscreteConvolution.delta_ne` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.addDelta_ne` | `RadiiPolynomial.DiscreteConvolution.addDelta_ne` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.delta_ringConvolution'` | `RadiiPolynomial.DiscreteConvolution.delta_ringConvolution'` | `Algebra/Convolution/Ring.lean` | namespace move; the convolution in the statement is now Mathlib's `ringConvolution`/`addRingConvolution`, whose coefficient instance is `NonUnitalNonAssocSemiring R` (here the projection of the same `CommSemiring`/`NormedCommRing` instance); same function |
| `DiscreteConvolution.addDelta_addRingConvolution'` | `RadiiPolynomial.DiscreteConvolution.addDelta_addRingConvolution'` | `Algebra/Convolution/Ring.lean` | namespace move; the convolution in the statement is now Mathlib's `ringConvolution`/`addRingConvolution`, whose coefficient instance is `NonUnitalNonAssocSemiring R` (here the projection of the same `CommSemiring`/`NormedCommRing` instance); same function |
| `DiscreteConvolution.ringConvolution_delta'` | `RadiiPolynomial.DiscreteConvolution.ringConvolution_delta'` | `Algebra/Convolution/Ring.lean` | namespace move; the convolution in the statement is now Mathlib's `ringConvolution`/`addRingConvolution`, whose coefficient instance is `NonUnitalNonAssocSemiring R` (here the projection of the same `CommSemiring`/`NormedCommRing` instance); same function |
| `DiscreteConvolution.addRingConvolution_addDelta'` | `RadiiPolynomial.DiscreteConvolution.addRingConvolution_addDelta'` | `Algebra/Convolution/Ring.lean` | namespace move; the convolution in the statement is now Mathlib's `ringConvolution`/`addRingConvolution`, whose coefficient instance is `NonUnitalNonAssocSemiring R` (here the projection of the same `CommSemiring`/`NormedCommRing` instance); same function |
| `DiscreteConvolution.tripleMulMap` | `RadiiPolynomial.DiscreteConvolution.tripleMulMap` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.tripleAddMap` | `RadiiPolynomial.DiscreteConvolution.tripleAddMap` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.tripleMulFiber` | `RadiiPolynomial.DiscreteConvolution.tripleMulFiber` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.tripleAddFiber` | `RadiiPolynomial.DiscreteConvolution.tripleAddFiber` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.mem_tripleMulFiber` | `RadiiPolynomial.DiscreteConvolution.mem_tripleMulFiber` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.mem_tripleAddFiber` | `RadiiPolynomial.DiscreteConvolution.mem_tripleAddFiber` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.leftMulAssocEquiv` | `RadiiPolynomial.DiscreteConvolution.leftMulAssocEquiv` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.leftAddAssocEquiv` | `RadiiPolynomial.DiscreteConvolution.leftAddAssocEquiv` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.rightMulAssocEquiv` | `RadiiPolynomial.DiscreteConvolution.rightMulAssocEquiv` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.rightAddAssocEquiv` | `RadiiPolynomial.DiscreteConvolution.rightAddAssocEquiv` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.HasSum.leftMulAssocEquiv_sigma` | `RadiiPolynomial.DiscreteConvolution.HasSum.leftMulAssocEquiv_sigma` | `Algebra/Convolution/Ring.lean` | nested `HasSum` helper; namespace move, statement unchanged up to the moved names |
| `DiscreteConvolution.HasSum.leftAddAssocEquiv_sigma` | `RadiiPolynomial.DiscreteConvolution.HasSum.leftAddAssocEquiv_sigma` | `Algebra/Convolution/Ring.lean` | nested `HasSum` helper; namespace move, statement unchanged up to the moved names |
| `DiscreteConvolution.HasSum.rightMulAssocEquiv_sigma` | `RadiiPolynomial.DiscreteConvolution.HasSum.rightMulAssocEquiv_sigma` | `Algebra/Convolution/Ring.lean` | nested `HasSum` helper; namespace move, statement unchanged up to the moved names |
| `DiscreteConvolution.HasSum.rightAddAssocEquiv_sigma` | `RadiiPolynomial.DiscreteConvolution.HasSum.rightAddAssocEquiv_sigma` | `Algebra/Convolution/Ring.lean` | nested `HasSum` helper; namespace move, statement unchanged up to the moved names |
| `DiscreteConvolution.TripleConvolutionSummable` | `RadiiPolynomial.DiscreteConvolution.TripleConvolutionSummable` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.AddTripleConvolutionSummable` | `RadiiPolynomial.DiscreteConvolution.AddTripleConvolutionSummable` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.ringConvolution_assoc_left` | `RadiiPolynomial.DiscreteConvolution.ringConvolution_assoc_left` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.addRingConvolution_assoc_left` | `RadiiPolynomial.DiscreteConvolution.addRingConvolution_assoc_left` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.ringConvolution_assoc_right` | `RadiiPolynomial.DiscreteConvolution.ringConvolution_assoc_right` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.addRingConvolution_assoc_right` | `RadiiPolynomial.DiscreteConvolution.addRingConvolution_assoc_right` | `Algebra/Convolution/Ring.lean` | namespace move; statement unchanged up to the moved names |
| `DiscreteConvolution.ringConvolution_assoc` | `RadiiPolynomial.DiscreteConvolution.ringConvolution_assoc` | `Algebra/Convolution/Ring.lean` | namespace move; the convolution in the statement is now Mathlib's `ringConvolution`/`addRingConvolution`, whose coefficient instance is `NonUnitalNonAssocSemiring R` (here the projection of the same `CommSemiring`/`NormedCommRing` instance); same function |
| `DiscreteConvolution.addRingConvolution_assoc` | `RadiiPolynomial.DiscreteConvolution.addRingConvolution_assoc` | `Algebra/Convolution/Ring.lean` | namespace move; the convolution in the statement is now Mathlib's `ringConvolution`/`addRingConvolution`, whose coefficient instance is `NonUnitalNonAssocSemiring R` (here the projection of the same `CommSemiring`/`NormedCommRing` instance); same function |
| `RadiiPolynomial.CauchyProduct.eq_addRingConvolution` | unchanged FQN | `Algebra/Convolution/Ring.lean` | retyped: the right-hand side is Mathlib's `DiscreteConvolution.addRingConvolution` (coefficient instance `NonUnitalNonAssocSemiring R` projected from `[Semiring R]`); same function |

### (ii) DELETED duplicates (replacement = the Mathlib declaration)

| old | replacement | hypothesis note |
|---|---|---|
| `DiscreteConvolution.mulFiber` | `DiscreteConvolution.mulFiber` | same FQN and statement |
| `DiscreteConvolution.addFiber` | `DiscreteConvolution.addFiber` | same |
| `DiscreteConvolution.mem_mulFiber` | `DiscreteConvolution.mem_mulFiber` | attribute `[grind =]`, not `[simp]`: consumers cite it explicitly |
| `DiscreteConvolution.mem_addFiber` | `DiscreteConvolution.mem_addFiber` | idem |
| `DiscreteConvolution.convolution` | `DiscreteConvolution.convolution` | same definition |
| `DiscreteConvolution.addConvolution` | `DiscreteConvolution.addConvolution` | same definition |
| `DiscreteConvolution.ringConvolution` | `DiscreteConvolution.ringConvolution` | coefficient class `[NonUnitalNonAssocSemiring R]` (was `[Semiring R]`), taken before `[Monoid M]`; same function |
| `DiscreteConvolution.addRingConvolution` | `DiscreteConvolution.addRingConvolution` | idem |
| notations `⋆[L]`, `⋆₊[L]`, `⋆ᵣ`, `⋆ᵣ₊` | Mathlib's scoped notations (scope `DiscreteConvolution`) | same tokens and precedences |
| `DiscreteConvolution.ringConvolution_apply_eq` | `DiscreteConvolution.ringConvolution_apply` | `rfl`, `[simp]`; coefficient class `NonUnitalNonAssocSemiring` |
| `DiscreteConvolution.addRingConvolution_apply_eq` | `DiscreteConvolution.addRingConvolution_apply` | idem |
| `DiscreteConvolution.zero_ringConvolution` | `DiscreteConvolution.zero_ringConvolution` | `[NonUnitalNonAssocSemiring R]` (was `[CommSemiring R]`) |
| `DiscreteConvolution.zero_addRingConvolution` | `DiscreteConvolution.zero_addRingConvolution` | idem |
| `DiscreteConvolution.ringConvolution_zero` | `DiscreteConvolution.ringConvolution_zero` | idem |
| `DiscreteConvolution.addRingConvolution_zero` | `DiscreteConvolution.addRingConvolution_zero` | idem |
| `DiscreteConvolution.ringConvolution_add` | `DiscreteConvolution.ringConvolution_add` | witnesses `ConvolutionExists (.mul ℕ R) f g`, which unfold to the old `∀ x, Summable fun ab : mulFiber x => f ab.1.1 * g ab.1.2`; consumers pass the old witness unchanged (definitional) |
| `DiscreteConvolution.addRingConvolution_add` | `DiscreteConvolution.addRingConvolution_add` | `AddConvolutionExists` witnesses; idem |
| `DiscreteConvolution.add_ringConvolution` | `DiscreteConvolution.add_ringConvolution` | `ConvolutionExists` witnesses; idem |
| `DiscreteConvolution.add_addRingConvolution` | `DiscreteConvolution.add_addRingConvolution` | `AddConvolutionExists` witnesses; idem |
| `DiscreteConvolution.smul_ringConvolution` | `DiscreteConvolution.smul_ringConvolution` | external scalar `c : S` with `[DistribSMul S R] [IsScalarTower S R R] [ContinuousConstSMul S R]` and a `ConvolutionExists` witness; consumers use `S := R` |
| `DiscreteConvolution.smul_addRingConvolution` | `DiscreteConvolution.smul_addRingConvolution` | idem |
| `DiscreteConvolution.ringConvolution_smul` | `DiscreteConvolution.ringConvolution_smul` | external scalar with `[SMulCommClass S R R]`; consumers use `S := R` |
| `DiscreteConvolution.addRingConvolution_smul` | `DiscreteConvolution.addRingConvolution_smul` | idem |
| `DiscreteConvolution.ringConvolution_comm` | `DiscreteConvolution.ringConvolution_comm` | `[CommMonoid M] [NonUnitalNonAssocCommSemiring R]` |
| `DiscreteConvolution.addRingConvolution_comm` | `DiscreteConvolution.addRingConvolution_comm` | `[AddCommMonoid M]`; idem |
| private `DiscreteConvolution.mulFiber_eq_finset_mulAntidiagonal` / `addFiber_eq_finset_antidiagonal` | Mathlib's private `mulFiber_eq_mulAntidiagonal` (internal to the module) | none (was private) |

### (iii) Intentional deletions (no Mathlib replacement; no in-repository consumer)

Recorded as intentional deletions with no needed in-repository consumer migration, not as Mathlib replacements and not as proof that no external user exists: `DiscreteConvolution.mulMap`, `DiscreteConvolution.addMap`, `DiscreteConvolution.mulMap_apply`, `DiscreteConvolution.addMap_apply`, `DiscreteConvolution.mulFiber_eq_preimage`, `DiscreteConvolution.addFiber_eq_preimage`. (`tripleMulMap`/`tripleAddMap` are kept, see (i).)

### (iv) Finite-sum lemma replacements

| old | replacement |
|---|---|
| `DiscreteConvolution.convolution_eq_sum_finset_mulAntidiagonal` | `DiscreteConvolution.convolution_eq_sum_mulAntidiagonal` (Mathlib; same statement over `Finset.mulAntidiagonal`) |
| `DiscreteConvolution.addConvolution_eq_sum_finset_antidiagonal` | `DiscreteConvolution.addConvolution_eq_sum_antidiagonal` (Mathlib; same statement over `Finset.antidiagonal`) |

### ADDED

| name | statement | file | axioms |
|---|---|---|---|
| `RadiiPolynomial.DiscreteConvolution.delta_eq_single` | `delta e = Pi.single (1 : M) e` (`rfl`) | `Algebra/Convolution/Ring.lean` | none |
| `RadiiPolynomial.DiscreteConvolution.addDelta_eq_single` | `addDelta e = Pi.single (0 : M) e` (`to_additive` twin) | `Algebra/Convolution/Ring.lean` | none |

## Bundled power-series bridge `CauchyProduct.toPowerSeriesLinearEquiv` (2026-10-12)

Consensus `CONSENSUS_toPowerSeries_equiv.md` (E2). File `Algebra/Convolution/CauchyProduct.lean`. The raw map
`toPowerSeries` and `toPowerSeries_injective` are unchanged; the three map laws are deleted in favour of the
generic laws of the new `S`-linear equivalence `toPowerSeriesLinearEquiv S : (ℕ → R) ≃ₗ[S] PowerSeries R`
(`[Semiring S] [AddCommMonoid R] [Module S R]`), whose forward map is `toPowerSeries`
(`toPowerSeriesLinearEquiv_apply`, `rfl`). Type-checked replacements: `Examples/tests/CV/PowerSeriesBridge.lean` §3.

| deleted | replacement |
|---|---|
| `RadiiPolynomial.CauchyProduct.toPowerSeries_add` | `map_add (toPowerSeriesLinearEquiv S) a b`; the old raw statement is `by simpa only [toPowerSeriesLinearEquiv_apply] using map_add (toPowerSeriesLinearEquiv R) a b` |
| `RadiiPolynomial.CauchyProduct.toPowerSeries_zero` | `map_zero (toPowerSeriesLinearEquiv S)`; the old raw statement is `by simpa only [toPowerSeriesLinearEquiv_apply] using map_zero (toPowerSeriesLinearEquiv R)` |
| `RadiiPolynomial.CauchyProduct.toPowerSeries_smul` | `map_smul (toPowerSeriesLinearEquiv S) c a` (any scalar semiring `S`; the old `c : R` is `S := R`); the old raw statement is `by simpa only [toPowerSeriesLinearEquiv_apply] using map_smul (toPowerSeriesLinearEquiv R) c a` |

## API campaign 2026-10-12 — cohort A

Clusters C1, C2, C3-A, C5, C6 and C7-A of the 2026-10-12 API campaign, accepted by the Codex review for the
source generation bound by `p3/cohortA/COHORT_A_SOURCES_v2.SHA256SUMS` (`p3/cohortA/CODEX_AGREEMENT.md`).
Each cluster subsection opens with a ledger, one row per migration: old FQN | new FQN or replacement | kind |
evidence. Kinds: `moved`, `retired`, `weakened hypotheses`, `level-rename`, `de-simp`, `docstring`, and, where
a fragment records them, `renamed`, `statement changed`, `redefined`, `added`, `import change`, `proof only`,
`hygiene`. The detail under each ledger is the cluster's fragment. For C2 the final record
`p3/cohortA/CODEX_FINAL_C2_RECORD.md` replaces `RENAMES_C2.md` and `ARCHITECTURE_C2.md` where they differ; for
C7-A the final overlay of `p3/evidence_C7A/REPORT_C7A.md` replaces the six-de-simp inventory.

Evidence paths starting with `p3/` are relative to `exterior/tmp/api_campaign_20261012/`; paths starting with
`codex/` are relative to `tmp/agents_bus/checks/session_registration/codex/COHORT-A-20261012/` (Codex's
independent checks). Both lie in the outer repository, outside the Lake root.

ReferenceBook consumers: the cohort introduces no ReferenceBook migration. The four remaining ReferenceBook uses of
`DiscreteConvolution.addRingConvolution_apply_eq` (deleted by the Mathlib adoption above, table (ii); replacement
`DiscreteConvolution.addRingConvolution_apply`) in `Ch07/Sec4` (two), `Ch07/Sec8b` and `Spine/A2_MonoidAlgebra` are
a user-side migration (`p3/cohortA/CODEX_F4_AMENDMENT.md`).

### C1 — Convolution cleanup (`Algebra/Convolution`)

Triage rows P1-S00-1-1, -2, -3, -5, -6, -14, -24 (Codex AGREE, `CODEX_batch1.md` §C1). No declaration is
renamed, added or deleted. Statements change only by weaker instance hypotheses; every weakened statement
still instantiates at its old interface (evidence: `p3/evidence_C1/`).

#### Ledger (C1)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `RadiiPolynomial.DiscreteConvolution.delta_ringConvolution'`, `RadiiPolynomial.DiscreteConvolution.ringConvolution_delta'` (+ `addDelta_addRingConvolution'`, `addRingConvolution_addDelta'`) | unchanged FQN; `[CommSemiring R]` → `[NonUnitalNonAssocSemiring R]` | weakened hypotheses | `p3/evidence_C1/step2/MIGRATED_TYPES.md`; `p3/evidence_C1/probes/OldInterface.lean` |
| `RadiiPolynomial.DiscreteConvolution.TripleConvolutionSummable` (+ `AddTripleConvolutionSummable`, `.eq_1`) | unchanged FQN; `[CommSemiring R]` → `[Mul R] [AddCommMonoid R]` | weakened hypotheses | `p3/evidence_C1/step2/MIGRATED_TYPES.md`; `p3/evidence_C1/probes/DefeqWitness.lean` |
| `RadiiPolynomial.DiscreteConvolution.HasSum.leftMulAssocEquiv_sigma` (+ `HasSum.leftAddAssocEquiv_sigma`) | unchanged FQN; `[NormedCommRing R]` → `[AddCommMonoid R] [TopologicalSpace R] [Mul R]` | weakened hypotheses | `p3/evidence_C1/step2/MIGRATED_TYPES.md`; `p3/evidence_C1/probes/OldInterface.lean` |
| `RadiiPolynomial.DiscreteConvolution.HasSum.rightMulAssocEquiv_sigma` (+ `HasSum.rightAddAssocEquiv_sigma`) | unchanged FQN; `[NormedCommRing R]` → `[AddCommMonoid R] [TopologicalSpace R] [Semigroup R]` | weakened hypotheses | `p3/evidence_C1/step2/MIGRATED_TYPES.md`; `p3/evidence_C1/probes/NoncommLibrary.lean` |
| `RadiiPolynomial.DiscreteConvolution.ringConvolution_assoc_left`, `…_assoc_right`, `…ringConvolution_assoc` (+ `addRingConvolution_assoc_left`, `_right`, `addRingConvolution_assoc`) | unchanged FQN; `[NormedCommRing R]` → `[NonUnitalSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R] [T3Space R]` | weakened hypotheses | `p3/evidence_C1/step2/MIGRATED_TYPES.md`; `p3/evidence_C1/probes/NoncommLibrary.lean`; `codex/C1_Noncomm.out` |
| `RadiiPolynomial.lpOneMulAlgConvCompat.tripleMulConvSummable`, `RadiiPolynomial.lpOneAlgConvCompat.tripleConvSummable` (+ `mk`, `mk._flat_ctor`, `rec`, `recOn`, `casesOn` of both classes) | unchanged FQN and statement text; elaborated instance path `Semifield.toCommSemiring` → `Distrib.toMul`/`Semiring.toAddCommMonoid` | weakened hypotheses (induced) | `p3/evidence_C1/step2/MIGRATED_TYPES.md`; `p3/evidence_C1/probes/DefeqWitness.lean`; `codex/C1_Witness.out` |
| `Algebra/Convolution/Ring.lean`: `import Mathlib.Analysis.Normed.Ring.Lemmas` | dropped; importers that need `IsTopologicalSemiring` of a normed ring or `Module ℚ ℝ` import `Mathlib.Analysis.Normed.Ring.Lemmas` / `Mathlib.Algebra.Algebra.Rat` themselves | import change | `p3/evidence_C1/probes/ProbeRing_plusNormedImport.lean`; `p3/evidence_C1/probes/PowerSeriesBridge_repair.lean` |
| `RadiiPolynomial.CauchyProduct.eq_addRingConvolution` | statement unchanged; term proof (S00-5) | proof only | `p3/evidence_C1/step4/C1.diff` |
| `Algebra/Convolution/Ring.lean`: `noncomputable section` | removed; `Lean.isNoncomputable` flags and compiled code unchanged (S00-6) | hygiene | `p3/evidence_C1/REPORT_C1.md` (flags before = after) |
| ten `RadiiPolynomial.CauchyProduct` lemmas (S00-14); facade `Algebra/Convolution.lean` (S00-24) | docstrings added; seven `lemma` → `theorem`; one facade sentence | docstring | `p3/evidence_C1/step4/C1.diff` |
| module docstring of `Algebra/Convolution/Ring.lean` | per-section hypotheses paragraph; the associativity set is "the topological hypotheses of Mathlib's `tsum_mul_tsum` together with associativity of `R` (`NonUnitalSemiring`)" | docstring | `p3/evidence_C1/CRITIC_C1.md` (FIX-1) |

#### Hypothesis changes (`Algebra/Convolution/Ring.lean`, namespace `RadiiPolynomial.DiscreteConvolution`)

| declaration (+ `to_additive` twin) | old classes on `R` | new classes on `R` | row |
|---|---|---|---|
| `delta_ringConvolution'` (`addDelta_addRingConvolution'`), `ringConvolution_delta'` (`addRingConvolution_addDelta'`) | `[CommSemiring R] [TopologicalSpace R]` | `[NonUnitalNonAssocSemiring R] [TopologicalSpace R]` | S00-1 |
| `TripleConvolutionSummable` (`AddTripleConvolutionSummable`), incl. `.eq_1` | `[CommSemiring R] [TopologicalSpace R]` | `[Mul R] [AddCommMonoid R] [TopologicalSpace R]` | S00-2 |
| `HasSum.leftMulAssocEquiv_sigma` (`HasSum.leftAddAssocEquiv_sigma`) | `[NormedCommRing R]` | `[AddCommMonoid R] [TopologicalSpace R] [Mul R]` | S00-3 |
| `HasSum.rightMulAssocEquiv_sigma` (`HasSum.rightAddAssocEquiv_sigma`) | `[NormedCommRing R]` | `[AddCommMonoid R] [TopologicalSpace R] [Semigroup R]` | S00-3 |
| `ringConvolution_assoc_left`, `ringConvolution_assoc_right`, `ringConvolution_assoc` (`addRingConvolution_assoc_left`, `_right`, `addRingConvolution_assoc`) | `[NormedCommRing R]` | `[NonUnitalSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R] [T3Space R]` | S00-3 |

The index hypotheses (`[Monoid M]`, `[DecidableEq M]`) are unchanged. The summability meaning of
`TripleConvolutionSummable f g h x` is unchanged: `Summable` of `f a * g b * h c` over `tripleMulFiber x`.

Migrated types (elaborated type changes, statement text unchanged): the class fields
`RadiiPolynomial.lpOneMulAlgConvCompat.tripleMulConvSummable` and `RadiiPolynomial.lpOneAlgConvCompat.tripleConvSummable`
(`Analysis/SequenceSpace/WeightedL1/Algebra.lean`) now apply the predicate through the instances
`Distrib.toMul`/`Semiring.toAddCommMonoid` of the `NormedField 𝕜` instead of `Semifield.toCommSemiring`.
Their structure auxiliaries (`mk`, `mk._flat_ctor`, `rec`, `recOn`, `casesOn`) change with them. No source change
in that file; the old meaning is witnessed by unfolding plus `with_reducible_and_instances rfl`.

#### Import drop

`Algebra/Convolution/Ring.lean` no longer imports `Mathlib.Analysis.Normed.Ring.Lemmas`. Importers that used it
transitively must import it themselves. In particular, `IsTopologicalSemiring R` for a normed ring
(`NonUnitalSeminormedRing.toIsTopologicalRing`) and `Module ℚ ℝ` (`DivisionRing.toRatAlgebra`,
`Mathlib.Algebra.Algebra.Rat`) are no longer visible through `Ring.lean` or the facade `Algebra/Convolution.lean`.

#### Other changes

- `RadiiPolynomial.CauchyProduct.eq_addRingConvolution`: statement unchanged; the proof is now the term
  `funext fun n => (_root_.DiscreteConvolution.addRingConvolution_eq_sum_antidiagonal a b n).symm` (S00-5).
- `noncomputable section` removed from `Ring.lean` (S00-6). Executability is unchanged:
  `Lean.isNoncomputable` was already `false` and compiled code was already present for `delta`, `addDelta`,
  `sigmaMulFiberEquiv`, `tripleMulMap`, `leftMulAssocEquiv`, `rightMulAssocEquiv` and their twins, both before and after.
- Docstrings added to ten `CauchyProduct` lemmas, which are now declared with `theorem` (S00-14), and one
  sentence added to the facade docstring (S00-24).

### C2 — Core engine (`Core/Theorem.lean`, `Core/Bounds.lean`, `Core.lean`)

Triage rows S03-1 … S03-17. Authoritative record: `p3/cohortA/CODEX_FINAL_C2_RECORD.md` (final `Core/Bounds.lean`
sha256 `2640b50b…`). S03-15 (generic index for `X`/`Y`, dropping the `Geometric.Scalar` import of `Core/Bounds`) is
rolled back; the generic-index/arity rows and the axiom-contraction addendum of `RENAMES_C2.md` are withdrawn.
Final migrated set: three completeness drops and six level-rename-only rows. No public declaration is renamed,
moved to another file, retired or deleted.

#### Ledger (C2)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `RadiiPolynomial.injective_left_of_norm_id_sub_comp_lt_one` | unchanged FQN; drops `[CompleteSpace E]`, keeps `[NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]` | weakened hypotheses | `p3/evidence_C2/probes/OldInterfacePins.lean`; `codex/C2_FinalPins.out` |
| `RadiiPolynomial.isUnit_right_of_norm_id_sub_comp_lt_one` | idem | weakened hypotheses | idem |
| `RadiiPolynomial.isUnit_left_of_norm_id_sub_comp_lt_one` | idem | weakened hypotheses | idem |
| `RadiiPolynomial.X` | unchanged FQN and PosReal-specific interface (no extra implicit index, same arity); universe label `u_2` → `u_1` | level-rename | `codex/C2_LEVEL_CHECK.json`; `codex/C2_FinalPins.out` |
| `RadiiPolynomial.Y` | idem | level-rename | idem |
| `RadiiPolynomial.Y₀_norm` | unchanged FQN; universe labels `u_2, u_3` → `u_1, u_2` (same order) | level-rename | `codex/C2_LEVEL_CHECK.json`; `p3/evidence_C2/tools/level_rename_check.py` |
| `RadiiPolynomial.Z₀_norm` | idem | level-rename | idem |
| `RadiiPolynomial.Z₁_norm` | idem | level-rename | idem |
| `RadiiPolynomial.Z₂_norm` | idem | level-rename | idem |

#### Detail (C2)

| Declarations | Final migration | Verification |
|---|---|---|
| injective_left_of_norm_id_sub_comp_lt_one; isUnit_right_of_norm_id_sub_comp_lt_one; isUnit_left_of_norm_id_sub_comp_lt_one | Drop CompleteSpace E; retain NormedAddCommGroup E, NormedSpace ℝ E and FiniteDimensional ℝ E | Old-interface pins passed; completeness is inferred from finite dimensionality |
| RadiiPolynomial.X; RadiiPolynomial.Y | u_2 → u_1 only; same PosReal-specific interface, no extra implicit index type or arity | Types/values equal after positional level mapping; axioms unchanged |
| RadiiPolynomial.Y₀_norm; Z₀_norm; Z₁_norm; Z₂_norm | u_2,u_3 → u_1,u_2, same order | Types/values equal after positional level mapping and identified hygienic binder numbers; axioms unchanged |

- The level renames come from deleting the dead `variable {Seq : PosReal → Type*} …` block of `Core/Bounds.lean`
  (S03-14). An explicit universe instantiation such as `Y₀_norm.{u, v}` keeps its positional meaning.
- The three completeness drops (S03-3): `CompleteSpace E` is an instance from `FiniteDimensional ℝ E`, so every old
  call site elaborates unchanged (ReferenceBook `Ch02/Sec7.lean:3776` calls without `@`).
- In-file relocation, FQN and type unchanged: `RadiiPolynomial.norm_id_sub_comp_le_Z_bound` moves from section
  `LocalTheorems` to section `OperatorBounds` of `Core/Theorem.lean` (S03-2).
- Deleted non-declaration text: the 37-line commented-out `construct_derivative_inverse` (S03-4) and the dead `Seq`
  variable block (S03-14).
- Generated name: `RadiiPolynomial.Z_bound.eq_1` is now realized in `Core/Theorem.lean` by a `simpa [Z_bound]`
  (`p3/evidence_C2/REPORT_C2.md`).
- Imports: unchanged. `Core/Bounds` imports `Core/Theorem` and `Analysis/SequenceSpace/Geometric/Scalar`; the
  closure of `Core` and `Core/AlgebraZ2` is unchanged.

### C3-A — Polynomials (`Algebra/Polynomial/{CompPoly,MvPolynomial}`)

#### Ledger (C3-A)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `MvPolynomial.contDiff_aeval` | unchanged FQN; `Algebra/Polynomial/CompPoly/Core.lean` → `Algebra/Polynomial/MvPolynomial/Calculus.lean` | moved | `p3/evidence_C3A/step2/CROSS_MODULE_MOVES.txt` |
| `MvPolynomial.C_ofNat_eq` | unchanged FQN; `Algebra/Polynomial/CompPoly/Core.lean` → `Algebra/Polynomial/MvPolynomial/Core.lean`; numerals now `ofNat(n)` (`no_index`) | moved; statement changed | `p3/evidence_C3A/step2/CROSS_MODULE_MOVES.txt`; `p3/evidence_C3A/step2/probes/C3A_RwOfNat.lean` |
| `MvPolynomial.C_natCast_eq` | `MvPolynomial.C_eq_coe_nat` (same statement, rfl) / `map_natCast MvPolynomial.C` (`@[simp]`) | retired (simp cast normalizer) | `p3/evidence_C3A/step2/probes/C3A_Replacements.lean` |
| `MvPolynomial.C_intCast_eq` | `map_intCast MvPolynomial.C` (`@[simp]`) | retired (simp cast normalizer) | idem |
| `MvPolyBridge.seqToPowerSeries` | `RadiiPolynomial.CauchyProduct.toPowerSeries` (rfl) | retired (intermediate constructor) | idem |
| `MvPolyBridge.mvPolyToPowerSeries` | `MvPolynomial.aeval` (rfl) | retired (intermediate constructor) | idem |
| private `MvPolyBridge.coeff_C_eq` | `PowerSeries.coeff_C` | retired (private coefficient helper) | idem |
| `MvPolynomial.totalDegree_C_le` | `(MvPolynomial.totalDegree_C a).le` | retired (degree wrapper) | idem |
| `MvPolynomial.totalDegree_X_le` | `(MvPolynomial.totalDegree_X i).le` | retired (degree wrapper) | idem |
| `MvPolynomial.totalDegree_add_le` | `(totalDegree_add p q).trans (max_le_add_of_nonneg (Nat.zero_le _) (Nat.zero_le _))` | retired (degree wrapper) | idem |
| `MvPolynomial.totalDegree_sub_le` | `(totalDegree_sub p q).trans (max_le_add_of_nonneg (Nat.zero_le _) (Nat.zero_le _))` | retired (degree wrapper) | idem |
| `MvPolynomial.totalDegree_neg_le` | `(MvPolynomial.totalDegree_neg p).le` | retired (degree wrapper) | idem |
| `MvPolyBridge.mvPolyCoeff` | unchanged FQN and lemma statements; body `PowerSeries.coeff n (aeval (fun i => CauchyProduct.toPowerSeries (seqs i)) p)` (rfl-equal) | redefined | `p3/evidence_C3A/REPORT_C3A.md` |
| `MvPolyBridge.mvPolyCoeff.eq_1` | generated equation lemma; statement follows the new body (0 consumers) | statement changed | `p3/evidence_C3A/REPORT_C3A.md`; `p3/cohortA/CODEX_cohortA_review.md` |
| `MvPolyBridge.arrayToPowerSeries` | unchanged FQN; body `CauchyProduct.toPowerSeries fun n => arr.getD n 0` (rfl-equal) | redefined (superseded by cohort B (C3-B): retired) | `p3/evidence_C3A/REPORT_C3A.md` |
| `Algebra/Polynomial/CompPoly/{Core,WeightedL1}.lean` imports | `CompPoly/Core` imports `MvPolynomial.Core` and `Mathlib.Analysis.Normed.Module.Basic` instead of `Mathlib.Analysis.Calculus.ContDiff.Operations`; `CompPoly/WeightedL1` imports `MvPolynomial.Calculus` | import change | `p3/evidence_C3A/RENAMES_C3A.md` |

#### Detail (C3-A, fragment)

##### RENAMED
None.

##### MOVED (FQN unchanged; new home file)
| declaration | old file | new file | item | type |
|---|---|---|---|---|
| `MvPolynomial.contDiff_aeval` (paper main.tex:812, 1520) | `Algebra/Polynomial/CompPoly/Core.lean` | `Algebra/Polynomial/MvPolynomial/Calculus.lean` | S01-3 | unchanged (scope-erased type tree identical; raw differs only in hygienic binder names carrying the module name; levels/axioms same) |
| `MvPolynomial.C_ofNat_eq` | `Algebra/Polynomial/CompPoly/Core.lean` | `Algebra/Polynomial/MvPolynomial/Core.lean` | S01-3 (+S01-1) | CHANGED, see below |

CompPoly/Core now imports `MvPolynomial.Core` (C_ofNat_eq stays in simp scope of every CompPoly importer) and
`Mathlib.Analysis.Normed.Module.Basic` instead of `Mathlib.Analysis.Calculus.ContDiff.Operations`;
CompPoly/WeightedL1 imports `MvPolynomial.Calculus` (for `contDiff_aeval`).

##### SIGNATURE CHANGE (name kept)
| declaration | old | new | item |
|---|---|---|---|
| `MvPolynomial.C_ofNat_eq` | `C (OfNat.ofNat n : R) = (OfNat.ofNat n : MvPolynomial σ R)` | `C (ofNat(n) : R) = (ofNat(n) : MvPolynomial σ R)` (= `no_index (OfNat.ofNat n)`, Mathlib `Polynomial.C_ofNat` form) | S01-1 |

Same binders `{σ R : Type*} [CommSemiring R] (n : ℕ) [n.AtLeastTwo]`, same proof `map_ofNat C n`; the type trees differ only by two
`noindex` mdata wrappers. Effect: the simp lemma now fires on literal numerals (`C 2 * p` normalizes to `2 * p`).

##### RETIRED (no alias)
| declaration | replacement | item |
|---|---|---|
| `MvPolynomial.C_natCast_eq` | `MvPolynomial.C_eq_coe_nat` (same statement, rfl) / `map_natCast MvPolynomial.C` (`@[simp]`) | S01-2 |
| `MvPolynomial.C_intCast_eq` | `map_intCast MvPolynomial.C` (`@[simp]`) | S01-2 |
| `MvPolyBridge.seqToPowerSeries` | `RadiiPolynomial.CauchyProduct.toPowerSeries` (rfl) | S01-4 |
| `MvPolyBridge.mvPolyToPowerSeries` | `MvPolynomial.aeval` (rfl) | S01-4 |
| private `MvPolyBridge.coeff_C_eq` | `PowerSeries.coeff_C` | S01-4 |
| `MvPolynomial.totalDegree_C_le` | `(MvPolynomial.totalDegree_C a).le` | S01-6 |
| `MvPolynomial.totalDegree_X_le` | `(MvPolynomial.totalDegree_X i).le` | S01-6 |
| `MvPolynomial.totalDegree_add_le` | `(totalDegree_add p q).trans (max_le_add_of_nonneg (Nat.zero_le _) (Nat.zero_le _))` | S01-6 |
| `MvPolynomial.totalDegree_sub_le` | `(totalDegree_sub p q).trans (max_le_add_of_nonneg (Nat.zero_le _) (Nat.zero_le _))` | S01-6 |
| `MvPolynomial.totalDegree_neg_le` | `(MvPolynomial.totalDegree_neg p).le` | S01-6 |

Each replacement is checked at the ORIGINAL proposition in `step2/probes/C3A_Replacements.lean` (rc 0).
Roles of the retired declarations: `C_natCast_eq`, `C_intCast_eq`: simp cast normalizers (superseded by Mathlib
`map_natCast`/`map_intCast`/`C_eq_coe_nat`); `totalDegree_{C,X,add,sub,neg}_le`: weaker degree wrappers (sum/le forms
of Mathlib's max-bound facts); private `coeff_C_eq`: coefficient helper (= `PowerSeries.coeff_C`);
`seqToPowerSeries`, `mvPolyToPowerSeries`: intermediate constructors (rfl-equal to `CauchyProduct.toPowerSeries` and
`MvPolynomial.aeval`).

##### REDEFINED (name and every lemma statement kept)
- `MvPolyBridge.mvPolyCoeff p seqs n := PowerSeries.coeff n (aeval (fun i => CauchyProduct.toPowerSeries (seqs i)) p)`
  (S01-4; rfl-equal to the old body; still noncomputable). Its generated equation lemma `mvPolyCoeff.eq_1` changes
  statement accordingly (0 consumers anywhere).
- `MvPolyBridge.arrayToPowerSeries` body now `CauchyProduct.toPowerSeries fun n => arr.getD n 0` (rfl-equal; S01-5 cluster kept).
  Superseded by cohort B (C3-B): the S01-5 cluster is retired.

### C5 — Transport namespace (`Core/Transport.lean`)

No aliases. Module unchanged (`RadiiPolynomial.Core.Transport`); statements unchanged
(strict compare PASS: types `exact`, or `S1` = identical after this map; `gateQ` value `exact`).

#### Ledger (C5)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `transported_radii_identity` | `RadiiPolynomial.transported_radii_identity` | renamed (namespace) | `p3/evidence_C5/step2/STRICT_COMPARE.md` |
| `transport_radii_polynomial` | `RadiiPolynomial.transport_radii_polynomial` | renamed (namespace) | idem |
| `transport_radii_polynomial_of_margin` | `RadiiPolynomial.transport_radii_polynomial_of_margin` | renamed (namespace) | idem |
| `gateQ` | `RadiiPolynomial.gateQ` | renamed (namespace) | idem; `p3/evidence_C5/step2/OldNamesGone.lean` |
| `gateQ_sound` | `RadiiPolynomial.gateQ_sound` | renamed (namespace) | idem |
| `KappaToy.gateQ` (Examples) | deleted → `RadiiPolynomial.gateQ` (byte-identical copy) | retired (duplicate) | `p3/evidence_C5/step2/STRICT_COMPARE.md` |
| `KappaToy.gateQ_sound` (Examples) | deleted → `RadiiPolynomial.gateQ_sound` (byte-identical copy) | retired (duplicate) | idem |

Fragment table (items): the five renames are S03-11, the two `KappaToy` deletions S03-12.

Consumers: `open RadiiPolynomial` short names keep resolving (KappaToy, TwinTransport);
KappaToy:188 `_root_.gateQ_sound` → `gateQ_sound`. ReferenceBook source: 0 uses.
Companion `exterior/Unformalization/Core/Transport.tex` cites both halves of the module by short name
(`\lean{gateQ}`, `\lean{transported_radii_identity}`, `\lean{Z₂_transport}`, `\lean{rp_transport_local}`), so its
`.tex` text needs no change. The FQN-indexed sidecars `exterior/Unformalization/_sidecar/Core/Transport.sig.tsv`
(rows 1–5) and `_sidecar/ALL_FQNS.txt` still list the root names and need the P4 re-pin
(`p3/evidence_C5/CRITIC_C5.md`, item 6).

### C6 — Small files (`Certification/Residual.lean`, `Analysis/Calculus/Pi.lean`, `Analysis/SequenceSpace/CharacterTopology.lean`)

No public name changes. No declaration added, deleted, renamed or moved.

#### Ledger (C6)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `RadiiPolynomial.Residual.norm_correction_le` | unchanged; docstring "The corrected coefficient has norm at most `‖b₀ i‖ / (1 - ε)`." | docstring | `p3/cohortA/CORRECTION_PACKET_cohortA.md` (F2) |
| `RadiiPolynomial.Residual.norm_correction_sub_le`, `…sum_norm_correction_le`, `…sum_norm_correction_sub_le`, `…residual_add` | unchanged; docstrings added (S00-15) | docstring | `p3/evidence_C6/step2/STRICT_COMPARE.md`; `p3/evidence_C6/REPORT_C6.md` |
| `Certification/Residual.lean` (one `rw` merge, whitespace) | statements unchanged (S00-15) | proof only | `p3/evidence_C6/step3/C6.diff` |
| `fderiv_pi_apply` | statement and `@[simp]` unchanged; body `(hasFDerivAt_apply i x).fderiv` (S00-17) | proof only | `p3/evidence_C6/step2/STRICT_COMPARE.md` |
| `Analysis/SequenceSpace/CharacterTopology.lean`: `noncomputable section` | dropped; `Lean.isNoncomputable` flags unchanged (all `false`) (S00-20) | hygiene | `p3/evidence_C6/step2/FLAGS_C6_candidate.txt` |

- `differentiable_pi_apply` is KEPT (its retirement S00-16 is cohort B; its RENAMES row
  "retired → `differentiable_apply`" lands with that unit, not here).
  Superseded by cohorts B (round 2) and C (C6 tail): `differentiable_pi_apply` is retired → Mathlib `differentiable_apply`.
- Evidence: strict compare PASS, 45/45 rows `exact`, 0 new, 0 deleted, 0 axiom changes
  (`p3/evidence_C6/step2/STRICT_COMPARE.md`).

### C7-A — Geometric prefix (`Analysis/SequenceSpace/Geometric/{Scalar,Basic,Omega}.lean`, `Analysis/SequenceSpace/Chebyshev/UnitLift.lean`)

Consumer searches: `p3/evidence_C7A/step1/CONSUMER_SEARCH_retirements.txt` (Lake root incl. Examples and tests,
exterior/Unformalization companions, ReferenceBook).

#### Ledger (C7-A)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `RadiiPolynomial.l1Weighted.instFactLeENNRealOfNat` | Mathlib's global instance `fact_one_le_one_ennreal` | retired | `p3/evidence_C7A/step2/Witness_FactInst.lean`; `codex/C7_Witness.out` |
| `RadiiPolynomial.l1Weighted.toLpWeighted` | `RadiiPolynomial.lpOneAlg.toLp` (`a.toLp`) | retired | `p3/evidence_C7A/step2/STRICT_COMPARE.md` |
| `RadiiPolynomial.l1Weighted.toSeq_mul_single` | unchanged FQN; `Geometric/Omega.lean` → `Geometric/Basic.lean` | moved | `p3/evidence_C7A/step2/MOVED_CHECK.txt` |
| `RadiiPolynomial.l1Weighted.norm_tailProj_eq_tailTsum` | unchanged FQN; `Geometric/Omega.lean` → `Geometric/Basic.lean` | moved | idem |
| `RadiiPolynomial.lpWeighted.toSeq_apply` | lemma kept; `@[simp]` removed | de-simp | `codex/C7_Simp.out` |
| `RadiiPolynomial.l1Weighted.toSeq_apply` | lemma kept; `@[simp]` removed | de-simp | idem |
| `RadiiPolynomial.lpOneAlg.geomUnitLift_gen` | lemma kept; `@[simp]` removed | de-simp | idem |
| `RadiiPolynomial.lpOneAlg.evalLaurent_gen` | lemma kept; `@[simp]` removed | de-simp | idem |
| `RadiiPolynomial.l1Chebyshev.evalLaurentC_gen` | lemma kept; `@[simp]` removed | de-simp | idem |
| `RadiiPolynomial.l1Omega.toSeq_apply` | lemma and `@[simp]` kept; docstring "Coefficient evaluation agrees with the underlying coordinate." | docstring | `p3/evidence_C7A/REPORT_C7A.md` (final overlay); `codex/C7_Simp.out` |
| — | `RadiiPolynomial.l1Weighted.toSeq_eq_toRealSeq : toSeq a = lpOneAlg.toRealSeq a := rfl` (not simp) | added | `p3/evidence_C7A/step2/STRICT_COMPARE.md` |

#### Detail (C7-A, fragment with the final overlay)

##### Retirements (public removal with replacement)

| Old FQN | Replacement | Row | Consumers (Lake / companions / RB build sources) |
|---|---|---|---|
| `RadiiPolynomial.l1Weighted.instFactLeENNRealOfNat` (anonymous global `instance : Fact (1 ≤ (1 : ℝ≥0∞))`, Geometric/Basic.lean:88) | Mathlib's `fact_one_le_one_ennreal` (global instance; `#synth` now returns it). S2 pair witnessed (step2/Witness_FactInst.lean, `with_reducible_and_instances rfl`) | S04-4 (+ S04-10: commented copy Omega:78 deleted) | 0 / Basic.tex:134, :641 / 0 (RB hits only in ledger evidence copies) |
| `RadiiPolynomial.l1Weighted.toLpWeighted` | `RadiiPolynomial.lpOneAlg.toLp` (`a.toLp`; identical type `lp (ScaledReal ν) 1`) | S04-5 | 0 / Basic.tex:139, :642 / 0 (RB hits only in ledger evidence copies) |

The retired instance occurs in the types of `derivShift_CLM` and `derivShift_CLM_apply` (argument of
`lp.normedAddCommGroup`); there it is replaced by `fact_one_le_one_ennreal`, witnessed definitionally equal.

##### Module moves, FQN unchanged

| FQN | From | To | Row |
|---|---|---|---|
| `RadiiPolynomial.l1Weighted.toSeq_mul_single` | Analysis/SequenceSpace/Geometric/Omega.lean | Analysis/SequenceSpace/Geometric/Basic.lean | S04-7 |
| `RadiiPolynomial.l1Weighted.norm_tailProj_eq_tailTsum` | Analysis/SequenceSpace/Geometric/Omega.lean | Analysis/SequenceSpace/Geometric/Basic.lean | S04-7 |

Type, levels, axioms identical across the move (step2/MOVED_CHECK.txt). Every importer of Omega imports Basic.

##### Attribute changes (lemmas kept; `@[simp]` removed)

`RadiiPolynomial.lpWeighted.toSeq_apply`, `RadiiPolynomial.l1Weighted.toSeq_apply` (S04-3, partial);
`RadiiPolynomial.lpOneAlg.geomUnitLift_gen`, `RadiiPolynomial.lpOneAlg.evalLaurent_gen`, `RadiiPolynomial.l1Chebyshev.evalLaurentC_gen` (S04-17).
Five de-simps in all. `RadiiPolynomial.l1Omega.toSeq_apply` keeps `@[simp]`: the ReferenceBook proof
`Spine/A5_Differential.lean:208` relies on that simp normal form (campaign ruling). The archived C7-A report and
`step2/SIMP_INVENTORY_DIFF.txt`, which list six de-simps, predate this ruling.

##### New public declaration

`RadiiPolynomial.l1Weighted.toSeq_eq_toRealSeq : toSeq a = lpOneAlg.toRealSeq a := rfl` (S04-14, l1Weighted half; not simp).

##### Not public-API changes (recorded for completeness)

- Private Omega duplicates deleted (S04-8): `scaledReal_norm_ofReal` → `ScaledReal.norm_lpAlgRingData_ofReal`; `l1Weighted_single_eq` → `l1Weighted.single_eq_lpOneAlg_single`.
- Generated reserved names no longer realized inside Omega (realized on demand anywhere): `shift.eq_1`, `shiftDivN.eq_1`, `lambdaN.eq_1`, `l1Weighted.mk.eq_1`, `l1Weighted.toSeq.eq_1`, `lpWeighted.mk.congr_simp`.
- In-module relocation, statement identical: `l1Weighted.single_eq_lpOneAlg_single` (end of Basic → `section Single`, S04-11); `ScaledReal.norm_lpAlgRingData_ofReal` (reopened namespace folded, S04-19).

## API campaign 2026-10-12 — cohort B

Clusters C8, C10-A, C3-B, R10a, R10b, R10c, R10d, C9-A and C9-B of the 2026-10-12 API campaign. Each cluster was
accepted by its independent critic, with the critic's fixes applied, and stands pending the serialized cohort-B
library, test and ReferenceBook builds (`DECISIONS.md` of the campaign, entries 11:10Z to 14:55Z). The R10d rows are
recorded before its critic verdict and are marked "(critic ACCEPT ~15:10Z)". Coordinator rulings in `DECISIONS.md` override
fragment text where they differ.

Each cluster subsection opens with a ledger, one row per migration: old FQN | new FQN or replacement | kind |
evidence. Kinds: `retired`, `moved`, `renamed (no alias)`, `binder drop`, `binder drop (induced)`,
`class-field drop`, `level-rename`, `redefined`, `statement changed`, `consumer-compat face`, `added`,
`added (test)`, `proof only`, `import change`, `test import`, `docstring`. The detail under each ledger is the
cluster's fragment. For the Mathlib-bound R10 layer (`Algebra/Convolution`) the detail carries the full
new-declaration tables.

Evidence paths starting with `p3/` are relative to `exterior/tmp/api_campaign_20261012/`, in the outer repository,
outside the Lake root.

ReferenceBook consumers: no ReferenceBook source is edited by this cohort. The two `norm_sum_mul_pi_le` names keep
their ReferenceBook call sites (C3-B); the C9-A faces `toSeq_radiusRestrict`, `aeval_of_norm_le_comp_radiusRestrict`
and `exists_eval_eq_of_analyticAt` are optional ReferenceBook adoptions.

### C8 — Operators (`Operators/Matrix`, `Operators/BlockDiagonal`, `Operators/HeadTail.lean`)

Triage rows S05-1 … S05-25 (KEEP: S05-7, -10, -16, -17). All FQNs are under `RadiiPolynomial.` unless written
otherwise. S05-20 and the S05-21 design-note clause that cites it are conditional on C12's `ivp_Z₀_le` rewiring
(cohort C): if C12 declines it, the theorem and its three docstring citations (Lift.lean, Composition.lean, the
WeightedL1 design note) are dropped together.
Resolved by cohorts B (round 2) and C (C12, S09-1-10/-11): `IVP.ivp_Z₀_le` is rewired through `composedApprox_toCLM_eq_lift`; the
condition is met.

#### Ledger (C8)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `RadiiPolynomial.SystemBlockDiagData.norm_id_sub_comp_le_of_eq_defect` | `RadiiPolynomial.SystemBlockDiagData.Z₀_norm_le_of_eq_defect` (identical statement) (S05-5) | retired (duplicate) | `p3/evidence_C8/probes/OldInterfacePins.lean`; `p3/evidence_C8/step1/CONSUMER_SEARCH_baseline.txt` |
| `RadiiPolynomial.SystemBlockDiagData.norm_toCLM_apply_le_norm` | `(A.toCLM (ν := ν)).le_of_opNorm_le (A.norm_toCLM_le (ν := ν)) x` (S05-8) | retired (operator-norm wrapper) | idem |
| `RadiiPolynomial.norm_le_of_pi_component_bound` | `ContinuousLinearMap.opNorm_le_bound _ hC fun h => (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg h))).2 (hcomp h)` (S05-9) | retired (operator-norm wrapper) | idem |
| `RadiiPolynomial.norm_const_XL1_fin1` | Mathlib `pi_norm_const a` (S05-15) | retired (norm wrapper) | idem |
| `RadiiPolynomial.BlockDiagLift.extractCoeff` (class field) | none (the field had no reader; coefficient maps stay instance-side: `toCoeff`, `ChebyshevIVP.toCoeffCheb`); both constructor assignments (`instBlockDiagLiftXL1`, `ChebyshevIVP.instBlockDiagLiftXCheb`) removed in the same generation (S05-25) | class-field drop | `p3/evidence_C8/step2/INVENTORY_DIFF.txt`; `p3/evidence_C8/step2/MIGRATED_CHECK.txt` |
| `RadiiPolynomial.BlockDiagLift.mk`, `.rec`, `.casesOn`, `.recOn`, `.noConfusion*`, `.mk._flat_ctor`, `.liftDefect` | unchanged FQNs; `mk` takes one explicit argument fewer, the recursors' minor premise has no `extractCoeff`, the `liftDefect` projection index is 1 → 0 (S05-25) | class-field drop (induced) | idem |
| `RadiiPolynomial.l1Weighted.opNorm_le_of_fin_kill_tail_eq` | unchanged FQN; `Operators/BlockDiagonal/Scalar.lean` → `Analysis/SequenceSpace/Geometric/Basic.lean` (§NormSplitting, after `norm_le_of_fin_zero_tail_eq`) (S05-14 ≡ S04-6) | moved | `p3/evidence_C8/step2/MOVED_CHECK.txt`; `p3/evidence_C8/probes/OldInterfacePins.lean` |
| `RadiiPolynomial.defectOfBlockDiagOp` (+ `.eq_1`) | unchanged FQN; `[NeZero L]` dropped (S05-23) | binder drop | `p3/evidence_C8/step2/MIGRATED_CHECK.txt`; `p3/evidence_C8/probes/OldInterfacePins.lean` |
| `RadiiPolynomial.SystemBlockDiagData.defectOfTailCancel` | unchanged FQN; `[NeZero L]` dropped (S05-23) | binder drop | idem |
| `RadiiPolynomial.SystemBlockDiagData.seq_zero_of_action_zero` | unchanged FQN; `[NeZero L]` dropped (S05-23) | binder drop | idem |
| `RadiiPolynomial.toCLM_ext_of_toCoeff_eq` | unchanged FQN; `[NeZero L]` dropped (S05-23) | binder drop | idem |
| `RadiiPolynomial.XL1.opNorm_le_of_fin_kill_tail_eq` | unchanged FQN; `[NeZero L]` dropped (S05-23) | binder drop | idem |
| `RadiiPolynomial.composedApprox_defect_eq`, `…SystemBlockDiagData.Z₀_le_of_tailCancel`, `…SystemBlockDiagData.id_sub_comp_eq_defect_toCLM`, `…defectOfBlockDiagOp_toCLM_eq`, `…defect_of_composed_toCLM_eq`, `…finite_block_injective_of_defect_norm_lt_one` (+ 2 private lemmas) | unchanged FQN and printed statement; the instance argument disappears inside the `defectOfBlockDiagOp`/`defectOfTailCancel` subterms | binder drop (induced) | `p3/evidence_C8/step2/MIGRATED_CHECK.txt` |
| `IVP.ivp_Z₀_le`, `IVP.ivp_system_theorem`, `IVP.ivp_system_theorem_local`, `ChebyshevIVP.StdChebIVPData.Z₀_le`, `ChebyshevIVP.StdChebIVPData.composed_toSeq_nat`, `ChebyshevIVP.StdChebIVPData.defect_actionFinite_single`, `RadiiPolynomial.finiteBlockMatrixNorm_defect_le_of_Q` | unchanged FQN and printed statement; raw type loses the instance argument (no `@`-application or named instance argument in Lake or ReferenceBook) | binder drop (induced, downstream) | `p3/evidence_C8/step2/IMPLICIT_CONSUMERS.txt` |
| `RadiiPolynomial.SystemBlockDiagData.defectOfTailCancel` | body `defectOfBlockDiagOp A B` (the old structure literal is `rfl`-equal; pinned) (S05-6) | redefined | `p3/evidence_C8/probes/OldInterfacePins.lean` |
| `RadiiPolynomial.SystemBlockDiagData.differentiable_actionFinite` | unchanged FQN; universe label `u_2` → `u_1` (dead `Seq` variable removed) (S05-2) | level-rename | `p3/evidence_C8/step2/MIGRATED_CHECK.txt`; `p3/evidence_C8/REPORT_C8.md` |
| `RadiiPolynomial.SystemBlockDiagData.differentiable_action_fin` | idem | level-rename | idem |
| `RadiiPolynomial.SystemBlockDiagData.fderiv_action_fin` | idem | level-rename | idem |
| — | `RadiiPolynomial.FiniteBlockMatrix.toMatrix_eq_comp` (`rfl`) (S05-1) | added | `p3/evidence_C8/step2/STRICT_COMPARE.md` |
| — | `RadiiPolynomial.FinWeighted.vecEquiv`, `RadiiPolynomial.FinWeightedMatrix.toWeightedCLMAlgEquiv`, `…toWeightedCLMAlgEquiv_apply`, `…isUnit_toWeightedCLM_iff` (S05-19) | added | idem |
| — | `RadiiPolynomial.ScalarBlockDiagData.toScalarCLM_eq_conj`, `…id_sub_comp_toScalarCLM_eq_conj` (S05-18) | added | idem |
| — | `RadiiPolynomial.SystemBlockDiagData.composedApprox_toCLM_eq_lift` (S05-20; conditional on C12) | added (condition met: C12, cohorts B (round 2) and C) | idem |
| short names (FQNs in `REPORT_C8.md`): `matrix_isUnit_of_toWeightedCLM_isUnit` (now `(isUnit_toWeightedCLM_iff).mp`), `toWeightedCLM_one`/`_mul`/`_one_sub` (`map_*` corollaries), `injective_toCLM_of_finite_part_injective` (from `seq_zero_of_action_zero`), `applyX_add`/`applyX_smul`, `id_sub_comp_toScalarCLM_apply_eq` (via `…_eq_conj`), `isUnit_toMatrix_of_blockNorm_lt_one` (110 → 41 lines) | names and statements unchanged; re-proved (S05-11, -12, -18, -19, -24) | proof only | `p3/evidence_C8/REPORT_C8.md`; `p3/evidence_C8/step2/STRICT_COMPARE.md`; `p3/evidence_C8/probes/P24_golf.lean` |
| `Operators/BlockDiagonal/{Basic,WeightedL1,Scalar}.lean` imports | `Basic` imports `Geometric.Scalar`, `Norm.FiniteSum`, `Matrix.WeightedNorm`, `Mathlib.Analysis.Calculus.FDeriv.Add`/`.Mul` (no longer `Core.Bounds`, `Geometric.Basic`, `Matrix.OperatorNorm`); `WeightedL1` adds `Core.Bounds` and `Geometric.Basic`; `Scalar` adds `Matrix.OperatorNorm` (S05-3) | import change | `p3/evidence_C8/step3/C8_vs_baseline.diff`; `p3/evidence_C8/step1/DIRECT_IMPORTERS.txt` |
| `Operators/HeadTail.lean` run-ledger tags `(T37, L001.)`, `(T37b, L001; optional.)`, `(T38a, L001.)` and the `(T38b, L001.)` line comment | stripped (S05-22); provenance: ledger L001 / S027 `HeadTailColumns.lean:284–291`; no diary line added to the module | docstring | `p3/evidence_C8/step3/C8_vs_baseline.diff` |

#### Detail (C8, fragment)

- Retirements: consumer search over the Lake root (incl. Examples/tests), ReferenceBook (excl. ledger) and paper v6.3
  gives 0 uses of each retired name. Companions still cite them (WeightedL1.tex:306/325/511/645/647/661,
  Scalar.tex:180/350): P4 companion refresh.
- Move (S05-14): raw type and axioms identical (`MOVED_CHECK.txt`; `type_of%` gate in `probes/OldInterfacePins.lean`);
  now proved through `norm_le_of_fin_zero_tail_eq`.
- S05-25: the class `BlockDiagLift` is now a norm-bounded linear defect action with no coefficient law; the zero lift
  satisfies its axioms (pinned in Lift.lean). No replacement for `extractCoeff`.
- S05-23: the five `[NeZero L]` binders were measured unused; old interfaces (with the binder) are restated verbatim and
  discharged by the new declarations in `probes/OldInterfacePins.lean`. Full old and new types:
  `step2/INVENTORY_DIFF.txt`.
- S05-2: the three level-renames come from deleting the dead `variable {Seq …}` block of `BlockDiagonal/Basic.lean`; an
  explicit universe instantiation keeps its positional meaning.
- S05-19: `toWeightedCLMAlgEquiv : Matrix ≃ₐ[ℝ] (Space →L[ℝ] Space)` has the forward map `toWeightedCLM` (`rfl`) and
  sends multiplication to composition in the same order; `toWeightedCLM`'s `mkContinuous` body and bound are kept, and
  the norm statement stays `finWeightedMatrixNorm_eq_opNorm`.

### C10-A — Chebyshev side of Station 4 (`Analysis/SequenceSpace/Chebyshev/{Algebra,Scalar,UnitLift}.lean`, `Fourier/Support.lean`)

Triage rows S04-1, S04-2, S04-14 (l1Chebyshev half), S04-15, S04-18, S04-24. Final generation per the coordinator
overlay (S04-1 landed, ~11:00Z) and the critic's fresh final-state strict compare (PASS, 196 rows, 0 failures,
0 axiom changes).

#### Ledger (C10-A)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `RadiiPolynomial.l1Chebyshev.leftMul` (abbrev) | `RadiiPolynomial.lpOneAlg.mulLeftCLM (𝕜 := ℝ) a` (definitionally equal, `rfl`) (S04-15) | retired (duplicate abbrev) | `p3/evidence_C10A/step2/Witness_Retirements.lean`; `p3/evidence_C10A/step1/CONSUMER_SEARCH_retirements.txt` |
| `RadiiPolynomial.ScaledRealZ.toReal` (abbrev) | `RadiiPolynomial.WeightedScalar.toReal` (identical body) (S04-18) | retired (duplicate abbrev) | idem |
| `RadiiPolynomial.ScaledRealZ.norm_lpAlgRingData_ofReal` (`@[simp]` kept) | unchanged FQN; `Chebyshev/Algebra.lean` → `Chebyshev/Scalar.lean` (S04-2) | moved | `p3/evidence_C10A/step2/MOVED_CHECK.txt`; `p3/evidence_C10A/step2/SIMP_INVENTORY_DIFF.txt` |
| `RadiiPolynomial.geomFiberZ` (`abbrev`) | unchanged FQN; `Chebyshev/UnitLift.lean` → `Chebyshev/Scalar.lean`; `[NormedField 𝕜]` kept (the binder drop S04-24 is declined: KEEP) (S04-1) | moved | `p3/evidence_C10A/step1/full_S04-1_applied/MOVED_CHECK.txt`; `p3/evidence_C10A/CRITIC_C10A.md` |
| `RadiiPolynomial.geomFiberZ_weight` (not simp) | unchanged FQN; `Chebyshev/UnitLift.lean` → `Chebyshev/Scalar.lean`, with its `example … rfl`; `[NormedField 𝕜]` kept (S04-24 KEEP) (S04-1) | moved | idem |
| `Analysis/SequenceSpace/Fourier/Support.lean` imports | `Chebyshev.Scalar` + `WeightedL1.UniversalProperty` instead of `Chebyshev.UnitLift`; import closures Support 19 → 12, Fourier hub 26 → 19, `Applications/Fourier` 31 → 24 modules (S04-1) | import change | `p3/evidence_C10A/step1/full_S04-1_applied/CLOSURE_DIFF.txt` |
| `Examples/tests/FZ/TailWindowRegressions.lean` | `+import RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Algebra` (line 1; it reached `l1Chebyshev` only transitively before; coordinator-authorized) (S04-1) | test import | `p3/evidence_C10A/step1/Repair_TailWindowRegressions.lean` |
| — | `RadiiPolynomial.l1Chebyshev.toSeq_eq_toRealSeq (a : l1Chebyshev ν) : toSeq a = lpOneAlg.toRealSeq a := rfl` (not simp; twin of cohort A's `l1Weighted.toSeq_eq_toRealSeq`) (S04-14) | added | `p3/evidence_C10A/step2/NEW_DELETED.txt` |

#### Detail (C10-A, fragment with the final overlay)

- Consumers of the two retired abbrevs: Lake 0, ReferenceBook build sources 0, environment scan under
  `import RadiiPolynomial` 0 (`step1/USAGE_SCAN_env_root.txt`); companions Chebyshev/Algebra.tex:48, :113, :285 and
  Chebyshev/Scalar.tex:36, :106, :118 (+ the two `_sidecar` sig rows): P4 companion refresh.
- `l1Weighted.leftMul` (Geometric/Basic) is NOT retired (S04-15 KEEP; ReferenceBook Ch07/Sec4 docstrings refer to it).
- Moves: kind, levels, raw and scope-erased type, axioms identical; every consumer of
  `ScaledRealZ.norm_lpAlgRingData_ofReal` imports Chebyshev/Algebra, which imports Chebyshev/Scalar.
- Not public-API changes: generated auxiliaries `l1Chebyshev.leftMul._proof_1 … _proof_8` and compiler names
  `ScaledRealZ.toReal._boxed`, `._redArg`, `._redArg._boxed` are gone with their heads.

### C3-B — Polynomials tail (`Algebra/Polynomial/{CompPoly,MvPolynomial}`, `Analysis/Norm/FiniteSum.lean`)

Triage rows S01-5 + S06-8 (paired retirement of the array-adapter cluster), S01-10 + S06-12 (one proof home, ruled
wrapper form), S07-2-2 (generic faces). This supersedes the cohort-A C3-A rows that kept the S01-5 cluster
(`MvPolyBridge.arrayToPowerSeries`, "redefined"; both rows now carry a pointer here). The `Array` grep gate reads "no
`mvPolyCoeffQ`/`arrayToPowerSeries`": `CompPoly.evalCoeff` (and `CompPoly.toSeq_evalBanach`) is the live certificate
path and keeps `Array` (coordinator ruling, ~12:40Z).

#### Ledger (C3-B)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `MvPolyBridge.arrayToPowerSeries` | `RadiiPolynomial.CauchyProduct.toPowerSeries fun n => arr.getD n 0` (its body) (S01-5) | retired (array adapter) | `p3/evidence_C3B/step3/probes/C3B_Controls.lean`; `p3/evidence_C3B/step2/STRICT_COMPARE.md` |
| `MvPolyBridge.mvPolyCoeffQ` (+ `.eq_1`) | `MvPolyBridge.mvPolyCoeff p (fun i k => (arrs i).getD k 0) n` (its body) (S01-5) | retired (array adapter) | idem |
| `MvPolyBridge.mvPolyCoeffQ_{C,zero,X,add,neg,sub,mul,one,X_fun,C_fun,C_mul}` (11 `@[simp]` lemmas) | the same-suffix `MvPolyBridge.mvPolyCoeff_*` lemma at `seqs := fun i k => (arrs i).getD k 0` (S01-5) | retired (array adapter) | idem |
| `MvPolyBridge.CompPoly.evalCoeff_eq_mvPolyCoeffQ` | `MvPolyBridge.CompPoly.evalCoeffSeq_eq_mvPolyCoeff p (fun i k => (arrs i).getD k 0) n` (`evalCoeff` unfolds to `evalCoeffSeq` at those sequences); live path `CompPoly.evalCoeff` + `CompPoly.toSeq_evalBanach` (S01-5) | retired (array adapter) | idem |
| `MvPolyBridge.toSeq_evalInBanach` | `MvPolyBridge.toSeq_evalInBanach_of_coeffs p a (fun i n => (arrs i).getD n 0) ha` (its body); live path `CompPoly.toSeq_evalBanach` (S06-8) | retired (array adapter) | idem |
| — | `RadiiPolynomial.NormHelpers.norm_sum_mul_pi_le {A ι : Type*} [NonUnitalSeminormedRing A] [Fintype ι] (f h : ι → A) : ‖∑ i, f i * h i‖ ≤ (∑ i, ‖f i‖) * ‖h‖` in `Analysis/Norm/FiniteSum.lean` (the single proof) (S01-10) | added | `p3/evidence_C3B/step2/STRICT_COMPARE.md` |
| `MvPolyBridge.CompPoly.norm_sum_mul_pi_le` (CompPoly/Bounds) | unchanged name, statement, binders and attributes; body `RadiiPolynomial.NormHelpers.norm_sum_mul_pi_le f h` (`rfl`-equal); not deprecated (S01-10) | consumer-compat face | `p3/evidence_C3B/step2/STRICT_COMPARE.md`; `p3/evidence_C3B/step3/CONSUMERS_post.txt` |
| `MvPolyBridge.norm_sum_mul_pi_le` (MvPolynomial/WeightedL1) | unchanged name, statement, binders and attributes; body `NormHelpers.norm_sum_mul_pi_le f h` (`rfl`-equal); not deprecated (S06-12) | consumer-compat face | idem |
| — | `MvPolyBridge.CompPoly.norm_sum_pderiv_mul_le`, `MvPolyBridge.CompPoly.norm_sum_pderiv_sub_mul_le` (CompPoly/Bounds, section `Normed`; geometry-free) (S07-2-2) | added | `p3/evidence_C3B/step2/STRICT_COMPARE.md`; `p3/evidence_C3B/step3/probes/C3B_Controls.lean` |
| `Analysis/Norm/FiniteSum.lean`, `Algebra/Polynomial/CompPoly/Bounds.lean` imports | FiniteSum gains `Mathlib.Analysis.Normed.Ring.Basic` and `Mathlib.Analysis.Normed.Group.Constructions`; CompPoly/Bounds gains `RadiiPolynomial.Analysis.Norm.FiniteSum` (closure 3289 → 3290) | import change | `p3/evidence_C3B/step3/closure_Bounds_delta.txt`; `p3/evidence_C3B/step3/closure_FiniteSum_delta.txt` |

#### Detail (C3-B, fragment)

- Generated: `MvPolyBridge.mvPolyCoeffQ.eq_1` goes with its def. `MvPolyBridge.CompPoly.evalCoeff.eq_1` is no longer
  realized in `CompPoly/Core` (it was produced only by the retired theorem's `simpa`); it is the on-demand equation
  lemma of the kept `CompPoly.evalCoeff` and is regenerated by any `unfold`/`simp [evalCoeff]` (0 explicit uses, Lake
  and ReferenceBook). Its disappearance from the export is not a deletion of interface (coordinator ruling, ~12:40Z).
- Consumers of the retired cluster (word-boundary search; Lake incl. Examples/tests, ReferenceBook excl. ledger,
  companions, paper v6.3): Lean code 0 outside the cluster, before and after; ReferenceBook 0; paper 0.
- `NormHelpers.norm_sum_mul_pi_le` keeps the binder order of the live CompPoly copy and is `type_of%`-equal to it
  (definitionally equal at reducible transparency, not syntactically: in the generic face `‖h‖` goes through
  `Pi.seminormedAddCommGroup`, in the CompPoly copy through `Pi.nonUnitalSeminormedRing`).
- Wrapper call sites (7 in 5 files: Jacobian:223, Face:126, Chebyshev/Bounds:143, :170, CompPoly/WeightedL1:95,
  MvPolynomial/WeightedL1 ×2; ReferenceBook Ch10/Sec2BoundsZ2:309, :417 and Ch08/Sec2Theorem:516) are unchanged.
  Strict compare: both wrapper rows `exact` (type, levels, axioms).
- S07-2-2: statements as in REVIEW_P1-S07-2 item 2 / Probe1b, axioms standard; the Chebyshev corollaries (C10 phase C)
  are not edited here and are `type_of%`-equal to the Probe1b corollaries over these faces.

### R10a — finite-fiber convolution wrapper (`Algebra/Convolution/{Finite,FiniteFiber}.lean`)

Contract `r10/CONSENSUS_r10.FINAL_8c6d01a0.md` (D1–D3, S00-12, S00-21); brief `p3/BRIEF_R10a_finitefiber.md`. No
declaration is renamed, deleted or re-stated: `Finite.lean` gains six theorems (existing declarations byte-identical,
strict compare EXACT + `new_ok`), and the new module `FiniteFiber.lean` adds the wrapper. `CauchyProduct.lean` and
`Ring.lean` are unchanged by this unit (strict compare EXACT). Coordinator rulings (~11:10Z): the additive carrier is
generated by `@[to_additive FiniteFiberAddConvolution, to_additive_dont_translate]` on the def (identical body
`M → R`); explicit additive names are dropped where the linter says they are autogenerated; the pinned instance names
are `Semiring.toNatAlgebra`, `Ring.toIntAlgebra`, `NSMul.toSMul`, `ZSMul.toSMul`; `coeff_one` is simp in the
Kronecker form (as `MvPowerSeries.coeff_one`).

#### Ledger (R10a)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| — | `RadiiPolynomial.finiteMulConvolution.single_one_left_apply`, `…single_one_right_apply`, `RadiiPolynomial.map_finiteMulConvolution` (+ additive twins `finiteAddConvolution.single_zero_left_apply`, `…single_zero_right_apply`, `map_finiteAddConvolution`) (S00-12) | added | `p3/evidence_R10a/step2/compare_Finite.log`; `p3/evidence_R10a/step2/rules_Finite.json` |
| — | new module `RadiiPolynomial.Algebra.Convolution.FiniteFiber` (54 public declarations per twin, table below) | added | `p3/evidence_R10a/step2/strict_cand_FiniteFiber.json`; `p3/evidence_R10a/step2/selfcheck_FiniteFiber.log`; `p3/evidence_R10a/step2/frozen_types.txt`; `p3/evidence_R10a/step2/additive_generated.txt` |
| `Algebra/Convolution.lean` (facade) | `+import RadiiPolynomial.Algebra.Convolution.FiniteFiber` and one docstring sentence | import change | `p3/evidence_R10a/step2/compare_Facade.log` |
| — | test module `RadiiPolynomial.Examples.tests.CV.FiniteFiberConvolution` | added (test) | `p3/evidence_R10a/step1/targeted_build.log` |

#### New declarations (`Finite.lean`)

| FQN | kind | hypotheses | simp? | computable? |
|---|---|---|---|---|
| `RadiiPolynomial.finiteMulConvolution.single_one_left_apply` | theorem | `[MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M] [AddCommMonoid R] [Mul R]` + `(hzero_mul : ∀ r : R, 0 * r = 0)` | — | n/a (Prop) |
| `RadiiPolynomial.finiteAddConvolution.single_zero_left_apply` | theorem | `[AddZeroClass M] [HasAntidiagonal M] [DecidableEq M] [AddCommMonoid R] [Mul R]` + `(hzero_mul : ∀ r : R, 0 * r = 0)` | — | n/a (Prop) |
| `RadiiPolynomial.finiteMulConvolution.single_one_right_apply` | theorem | `[MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M] [AddCommMonoid R] [Mul R]` + `(hmul_zero : ∀ r : R, r * 0 = 0)` | — | n/a (Prop) |
| `RadiiPolynomial.finiteAddConvolution.single_zero_right_apply` | theorem | `[AddZeroClass M] [HasAntidiagonal M] [DecidableEq M] [AddCommMonoid R] [Mul R]` + `(hmul_zero : ∀ r : R, r * 0 = 0)` | — | n/a (Prop) |
| `RadiiPolynomial.map_finiteMulConvolution` | theorem | `[Mul M] [HasMulAntidiagonal M] [AddCommMonoid R] [Mul R] [AddCommMonoid R'] [Mul R']` + `(φ : R →+ R') (hφ : ∀ x y, φ (x * y) = φ x * φ y)` | — | n/a (Prop) |
| `RadiiPolynomial.map_finiteAddConvolution` | theorem | `[Add M] [HasAntidiagonal M] [AddCommMonoid R] [Mul R] [AddCommMonoid R'] [Mul R']` + `(φ : R →+ R') (hφ : …)` | — | n/a (Prop) |

#### New declarations (`FiniteFiber.lean`; both twins; auxiliaries `eq_1`, `_proof_n`, `single.congr_simp` omitted)

Universe variables: `M : Type u`, `R : Type v`, `S : Type w`. The additive twin translates only the index class.

| FQN | kind | hypotheses | simp? | computable? |
|---|---|---|---|---|
| `RadiiPolynomial.FiniteFiberConvolution` | def (type) | none (`M : Type u`, `R : Type v`) | — | computable (no IR: type) |
| `RadiiPolynomial.FiniteFiberAddConvolution` | def (type) | none (`M : Type u`, `R : Type v`) | — | computable (no IR: type) |
| `RadiiPolynomial.FiniteFiberConvolution.ofFun` | def (`Equiv`) | none | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.ofFun` | def (`Equiv`) | none | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.toFun` | def (`Equiv`) | none | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.toFun` | def (`Equiv`) | none | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.coeff` | def | none | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff` | def | none | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.ofFun_symm` | theorem | none | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.ofFun_symm` | theorem | none | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.toFun_symm` | theorem | none | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.toFun_symm` | theorem | none | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.toFun_ofFun` | theorem | none | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.toFun_ofFun` | theorem | none | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.ofFun_toFun` | theorem | none | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.ofFun_toFun` | theorem | none | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.coeff_ofFun` | theorem | none | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff_ofFun` | theorem | none | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.toFun_apply` | theorem | none | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.toFun_apply` | theorem | none | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.ext` | theorem (`@[ext]`) | none | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.ext` | theorem (`@[ext]`) | none | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.ext_iff` | theorem (generated by `@[ext]`) | none | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.ext_iff` | theorem (generated by `@[ext]`) | none | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.single` | def | `[DecidableEq M] [Zero R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.single` | def | `[DecidableEq M] [Zero R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.coeff_single` | theorem | `[DecidableEq M] [Zero R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff_single` | theorem | `[DecidableEq M] [Zero R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.instZero` | instance | `[Zero R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instZero` | instance | `[Zero R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instAdd` | instance | `[Add R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instAdd` | instance | `[Add R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instNeg` | instance | `[Neg R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instNeg` | instance | `[Neg R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instSub` | instance | `[Sub R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instSub` | instance | `[Sub R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instSMul` | instance | `[SMul S R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instSMul` | instance | `[SMul S R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instAddCommMonoid` | instance | `[AddCommMonoid R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instAddCommMonoid` | instance | `[AddCommMonoid R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instAddCommGroup` | instance | `[AddCommGroup R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instAddCommGroup` | instance | `[AddCommGroup R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instModule` | instance | `[Semiring S] [AddCommMonoid R] [Module S R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instModule` | instance | `[Semiring S] [AddCommMonoid R] [Module S R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.coeff_zero` | theorem | `[Zero R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff_zero` | theorem | `[Zero R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.coeff_add` | theorem | `[Add R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff_add` | theorem | `[Add R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.coeff_neg` | theorem | `[Neg R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff_neg` | theorem | `[Neg R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.coeff_sub` | theorem | `[Sub R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff_sub` | theorem | `[Sub R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.coeff_smul` | theorem | `[SMul S R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff_smul` | theorem | `[SMul S R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.instMul` | instance | `[Mul M] [HasMulAntidiagonal M] [AddCommMonoid R] [Mul R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instMul` | instance | `[Add M] [HasAntidiagonal M] [AddCommMonoid R] [Mul R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instOne` | instance | `[One M] [DecidableEq M] [Zero R] [One R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instOne` | instance | `[Zero M] [DecidableEq M] [Zero R] [One R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.toFun_mul` | theorem | `[Mul M] [HasMulAntidiagonal M] [AddCommMonoid R] [Mul R]` | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.toFun_mul` | theorem | `[Add M] [HasAntidiagonal M] [AddCommMonoid R] [Mul R]` | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.coeff_mul` | theorem | `[Mul M] [HasMulAntidiagonal M] [AddCommMonoid R] [Mul R]` | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff_mul` | theorem | `[Add M] [HasAntidiagonal M] [AddCommMonoid R] [Mul R]` | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.one_def` | theorem | `[One M] [DecidableEq M] [Zero R] [One R]` | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.one_def` | theorem | `[Zero M] [DecidableEq M] [Zero R] [One R]` | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.coeff_one` | theorem | `[One M] [DecidableEq M] [Zero R] [One R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff_one` | theorem | `[Zero M] [DecidableEq M] [Zero R] [One R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.single_mul_single` | theorem | `[Mul M] [HasMulAntidiagonal M] [DecidableEq M] [NonUnitalNonAssocSemiring R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.single_mul_single` | theorem | `[Add M] [HasAntidiagonal M] [DecidableEq M] [NonUnitalNonAssocSemiring R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.coeff_single_one_mul` | theorem | `[MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M] [NonUnitalNonAssocSemiring R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff_single_zero_mul` | theorem | `[AddZeroClass M] [HasAntidiagonal M] [DecidableEq M] [NonUnitalNonAssocSemiring R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.coeff_mul_single_one` | theorem | `[MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M] [NonUnitalNonAssocSemiring R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff_mul_single_zero` | theorem | `[AddZeroClass M] [HasAntidiagonal M] [DecidableEq M] [NonUnitalNonAssocSemiring R]` | simp | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.instNonUnitalNonAssocSemiring` | instance | `[Mul M] [HasMulAntidiagonal M] [NonUnitalNonAssocSemiring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instNonUnitalNonAssocSemiring` | instance | `[Add M] [HasAntidiagonal M] [NonUnitalNonAssocSemiring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instNonUnitalSemiring` | instance | `[Semigroup M] [HasMulAntidiagonal M] [NonUnitalSemiring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instNonUnitalSemiring` | instance | `[AddSemigroup M] [HasAntidiagonal M] [NonUnitalSemiring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instNonAssocSemiring` | instance | `[MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M] [NonAssocSemiring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instNonAssocSemiring` | instance | `[AddZeroClass M] [HasAntidiagonal M] [DecidableEq M] [NonAssocSemiring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instSemiring` | instance | `[Monoid M] [HasMulAntidiagonal M] [DecidableEq M] [Semiring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instSemiring` | instance | `[AddMonoid M] [HasAntidiagonal M] [DecidableEq M] [Semiring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instNonUnitalNonAssocCommSemiring` | instance | `[CommMagma M] [HasMulAntidiagonal M] [NonUnitalNonAssocCommSemiring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instNonUnitalNonAssocCommSemiring` | instance | `[AddCommMagma M] [HasAntidiagonal M] [NonUnitalNonAssocCommSemiring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instNonUnitalCommSemiring` | instance | `[CommSemigroup M] [HasMulAntidiagonal M] [NonUnitalCommSemiring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instNonUnitalCommSemiring` | instance | `[AddCommSemigroup M] [HasAntidiagonal M] [NonUnitalCommSemiring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instCommSemiring` | instance | `[CommMonoid M] [HasMulAntidiagonal M] [DecidableEq M] [CommSemiring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instCommSemiring` | instance | `[AddCommMonoid M] [HasAntidiagonal M] [DecidableEq M] [CommSemiring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.natCast_def` | theorem | `[MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M] [NonAssocSemiring R]` | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.natCast_def` | theorem | `[AddZeroClass M] [HasAntidiagonal M] [DecidableEq M] [NonAssocSemiring R]` | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.instNonUnitalNonAssocRing` | instance | `[Mul M] [HasMulAntidiagonal M] [NonUnitalNonAssocRing R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instNonUnitalNonAssocRing` | instance | `[Add M] [HasAntidiagonal M] [NonUnitalNonAssocRing R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instNonUnitalRing` | instance | `[Semigroup M] [HasMulAntidiagonal M] [NonUnitalRing R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instNonUnitalRing` | instance | `[AddSemigroup M] [HasAntidiagonal M] [NonUnitalRing R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instNonAssocRing` | instance | `[MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M] [NonAssocRing R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instNonAssocRing` | instance | `[AddZeroClass M] [HasAntidiagonal M] [DecidableEq M] [NonAssocRing R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instRing` | instance | `[Monoid M] [HasMulAntidiagonal M] [DecidableEq M] [Ring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instRing` | instance | `[AddMonoid M] [HasAntidiagonal M] [DecidableEq M] [Ring R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.instCommRing` | instance | `[CommMonoid M] [HasMulAntidiagonal M] [DecidableEq M] [CommRing R]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instCommRing` | instance | `[AddCommMonoid M] [HasAntidiagonal M] [DecidableEq M] [CommRing R]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.intCast_def` | theorem | `[MulOneClass M] [HasMulAntidiagonal M] [DecidableEq M] [NonAssocRing R]` | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.intCast_def` | theorem | `[AddZeroClass M] [HasAntidiagonal M] [DecidableEq M] [NonAssocRing R]` | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.instIsScalarTower` | instance (Prop) | `[Mul M] [HasMulAntidiagonal M] [AddCommMonoid R] [Mul R] [DistribSMul S R] [IsScalarTower S R R]` | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.instIsScalarTower` | instance (Prop) | `[Add M] [HasAntidiagonal M] [AddCommMonoid R] [Mul R] [DistribSMul S R] [IsScalarTower S R R]` | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.instSMulCommClass` | instance (Prop) | `[Mul M] [HasMulAntidiagonal M] [AddCommMonoid R] [Mul R] [DistribSMul S R] [SMulCommClass S R R]` | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.instSMulCommClass` | instance (Prop) | `[Add M] [HasAntidiagonal M] [AddCommMonoid R] [Mul R] [DistribSMul S R] [SMulCommClass S R R]` | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberConvolution.instAlgebra` | instance | `[CommSemiring S] [Semiring R] [Algebra S R] [Monoid M] [HasMulAntidiagonal M] [DecidableEq M]` | — | computable |
| `RadiiPolynomial.FiniteFiberAddConvolution.instAlgebra` | instance | `[CommSemiring S] [Semiring R] [Algebra S R] [AddMonoid M] [HasAntidiagonal M] [DecidableEq M]` | — | computable |
| `RadiiPolynomial.FiniteFiberConvolution.algebraMap_apply` | theorem | `[CommSemiring S] [Semiring R] [Algebra S R] [Monoid M] [HasMulAntidiagonal M] [DecidableEq M]` | — | n/a (Prop) |
| `RadiiPolynomial.FiniteFiberAddConvolution.algebraMap_apply` | theorem | `[CommSemiring S] [Semiring R] [Algebra S R] [AddMonoid M] [HasAntidiagonal M] [DecidableEq M]` | — | n/a (Prop) |

`Finite` and `FiniteFiber` import no topology, no `Ring`, no `Analysis`
(`p3/evidence_R10a/step3/import_closure_FiniteFiber.txt`: `Mathlib.Topology.*` = 0 modules, `Real` absent).

### R10b — power-series connections and the tsum/finite operation equality (`Algebra/Convolution/{Ring,FiniteFiber/PowerSeries}.lean`)

Contract `r10/CONSENSUS_r10.FINAL_8c6d01a0.md` (C1, C2, C4 first half; S00-4, S00-13, S02-9); brief
`p3/BRIEF_R10b_powerseries.md`. Coordinator rulings (~13:15Z): `single_ringConvolution_single` and its twin are
`@[simp]` (consistent with Mathlib's `single_ringConvolution`/`MonoidAlgebra.single_mul_single`; simp fires at the
function level only, since Mathlib's `ringConvolution_apply` pre-empts the applied form); `toMvPowerSeriesRingEquiv`
is computable; the `_smul` faces stay simp. Under `Classical.decEq` the wrapper and `MvPowerSeries` products are
plain-`rfl` definitional (critic, ~14:15Z).

#### Ledger (R10b)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `RadiiPolynomial.DiscreteConvolution.HasSum.leftMulAssocEquiv_sigma` | `RadiiPolynomial.DiscreteConvolution.hasSum_sigma_leftMulAssoc` (S00-4) | renamed (no alias) | `p3/evidence_R10b/step2/compare_Ring.log`; `p3/evidence_R10b/step2/rules_Ring.json`; `p3/evidence_R10b/step0/oldname_consumers.txt` |
| `RadiiPolynomial.DiscreteConvolution.HasSum.leftAddAssocEquiv_sigma` (generated) | `RadiiPolynomial.DiscreteConvolution.hasSum_sigma_leftAddAssoc` (generated by `to_additive`) (S00-4) | renamed (no alias) | idem |
| `RadiiPolynomial.DiscreteConvolution.HasSum.rightMulAssocEquiv_sigma` | `RadiiPolynomial.DiscreteConvolution.hasSum_sigma_rightMulAssoc` (S00-4) | renamed (no alias) | idem |
| `RadiiPolynomial.DiscreteConvolution.HasSum.rightAddAssocEquiv_sigma` (generated) | `RadiiPolynomial.DiscreteConvolution.hasSum_sigma_rightAddAssoc` (generated) (S00-4) | renamed (no alias) | idem |
| — | `RadiiPolynomial.DiscreteConvolution.ringConvolution_eq_finiteMulConvolution` (+ `addRingConvolution_eq_finiteAddConvolution`) (S00-13; T3) | added | `p3/evidence_R10b/step2/compare_Ring.log` |
| — | `RadiiPolynomial.DiscreteConvolution.single_ringConvolution_single` (+ `single_addRingConvolution_single`), `@[simp]` (S02-9; T4) | added | `p3/evidence_R10b/step2/compare_Ring.log`; `p3/evidence_R10b/step3/up_reproof.out` |
| — | new module `RadiiPolynomial.Algebra.Convolution.FiniteFiber.PowerSeries` (9 public declarations) (C1, C2) | added | `p3/evidence_R10b/step2/strict_cand_PowerSeries.json`; `p3/evidence_R10b/step2/selfcheck_PowerSeries.log`; `p3/evidence_R10b/step2/frozen_types.txt` |
| `Algebra/Convolution.lean` (facade) | `+import RadiiPolynomial.Algebra.Convolution.FiniteFiber.PowerSeries` and one docstring sentence | import change | `p3/evidence_R10b/HUB_R10b.md` |
| — | test modules `RadiiPolynomial.Examples.tests.CV.FiniteFiberPowerSeries`, `RadiiPolynomial.Examples.tests.CV.RingConvolutionFinite` | added (test) | `p3/evidence_R10b/step1/targeted_build.log` |

#### S00-4 renames (no deprecated alias; binder order unchanged)

| old FQN | new FQN | binder order (unchanged) | consumers |
|---|---|---|---|
| `RadiiPolynomial.DiscreteConvolution.HasSum.leftMulAssocEquiv_sigma` | `RadiiPolynomial.DiscreteConvolution.hasSum_sigma_leftMulAssoc` | `{M R} [Monoid M] [AddCommMonoid R] [TopologicalSpace R] [Mul R] {f g h : M → R} {x : M} {a : R} (hs : HasSum …)` | Ring.lean `ringConvolution_assoc_left` (call site updated); 0 elsewhere |
| `RadiiPolynomial.DiscreteConvolution.HasSum.leftAddAssocEquiv_sigma` (generated) | `RadiiPolynomial.DiscreteConvolution.hasSum_sigma_leftAddAssoc` (generated by `to_additive`) | same with `[AddMonoid M]` | Ring.lean `addRingConvolution_assoc_left` (generated); 0 elsewhere |
| `RadiiPolynomial.DiscreteConvolution.HasSum.rightMulAssocEquiv_sigma` | `RadiiPolynomial.DiscreteConvolution.hasSum_sigma_rightMulAssoc` | `{M R} [Monoid M] [AddCommMonoid R] [TopologicalSpace R] [Semigroup R] {f g h : M → R} {x : M} {a : R} (hs : HasSum …)` | Ring.lean `ringConvolution_assoc_right` (call site updated); 0 elsewhere |
| `RadiiPolynomial.DiscreteConvolution.HasSum.rightAddAssocEquiv_sigma` (generated) | `RadiiPolynomial.DiscreteConvolution.hasSum_sigma_rightAddAssoc` (generated) | same with `[AddMonoid M]` | Ring.lean `addRingConvolution_assoc_right` (generated); 0 elsewhere |
| auxiliaries `HasSum.right{Mul,Add}AssocEquiv_sigma.match_1_1` | `hasSum_sigma_right{Mul,Add}Assoc.match_1_1` | — | internal |

Hypotheses preserved exactly: left `[Mul R]`, right `[Semigroup R]` (asymmetric); bodies unchanged; strict compare
PASS with these four `renames` (types and values equal after erasing binder macro scopes); the control with empty
rules FAILS with exactly the 4 deletions + 8 additions (`p3/evidence_R10b/step2/compare_Ring_emptyrules_control.log`).
`ringConvolution_assoc_left`/`_right` change only by the renamed call site (types exact). Consumers: library, Examples
and tests only the two Ring.lean call sites; ReferenceBook 0; paper v6.3 0. The live companion
`Algebra/Convolution/Ring.tex` (lines 198, 211, 316–319) and the sidecars `_sidecar/ALL_FQNS.txt:1190–1193`,
`_sidecar/Algebra/Convolution/Ring.sig.tsv:25–28` carry the old names: P4 companion refresh. The history rows of this
file that name the old FQNs (Mathlib-adoption section, cohort-A C1 ledger) stay as history.

#### New declarations (`Ring.lean`, `FiniteFiber/PowerSeries.lean`)

| FQN | kind | hypotheses | simp? | computable? |
|---|---|---|---|---|
| `RadiiPolynomial.DiscreteConvolution.ringConvolution_eq_finiteMulConvolution` | theorem | `[Monoid M] [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [Finset.HasMulAntidiagonal M] (f g : M → R)` (= Mathlib's `ringConvolution_eq_sum_mulAntidiagonal`) | — | n/a |
| `RadiiPolynomial.DiscreteConvolution.addRingConvolution_eq_finiteAddConvolution` | theorem (generated) | `[AddMonoid M] … [Finset.HasAntidiagonal M]` | — | n/a |
| `RadiiPolynomial.DiscreteConvolution.single_ringConvolution_single` | theorem | `[Monoid M] [DecidableEq M] [NonUnitalNonAssocSemiring R] [TopologicalSpace R] (i j : M) (x y : R)` | simp (coordinator ruling ~13:15Z; `to_additive (attr := simp)`) | n/a |
| `RadiiPolynomial.DiscreteConvolution.single_addRingConvolution_single` | theorem (generated) | `[AddMonoid M] [DecidableEq M] …` | simp (coordinator ruling ~13:15Z; `to_additive (attr := simp)`) | n/a |
| `RadiiPolynomial.FiniteFiberAddConvolution.toPowerSeriesRingEquiv` | def (`R` explicit) | `[Semiring R]` | — | `noncomputable` (cause: `CauchyProduct.toPowerSeriesLinearEquiv` ← `Finsupp.uniqueEquiv`) |
| `RadiiPolynomial.FiniteFiberAddConvolution.toPowerSeriesRingEquiv_apply` | theorem (`rfl`) | `[Semiring R]` | — | n/a |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff_toPowerSeriesRingEquiv` | theorem | `[Semiring R]` | simp | n/a |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff_toPowerSeriesRingEquiv_symm` | theorem | `[Semiring R]` | simp | n/a |
| `RadiiPolynomial.FiniteFiberAddConvolution.toPowerSeriesRingEquiv_smul` | theorem | `[Semiring R] {S} [Semiring S] [Module S R]` | simp | n/a |
| `RadiiPolynomial.FiniteFiberAddConvolution.toMvPowerSeriesRingEquiv` | def (`σ R` explicit) | `[DecidableEq σ] [Semiring R]` | — | computable (compiled code present; stores only `toFun`/`invFun`) |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff_toMvPowerSeriesRingEquiv` | theorem (`rfl`) | `[DecidableEq σ] [Semiring R]` | simp | n/a |
| `RadiiPolynomial.FiniteFiberAddConvolution.coeff_toMvPowerSeriesRingEquiv_symm` | theorem (`rfl`) | `[DecidableEq σ] [Semiring R]` | simp | n/a |
| `RadiiPolynomial.FiniteFiberAddConvolution.toMvPowerSeriesRingEquiv_smul` | theorem (`rfl`) | `[DecidableEq σ] [Semiring R] {S} [Semiring S] [Module S R]` | simp | n/a |

`FiniteFiber/PowerSeries` imports no topology, no `Ring`, no `Analysis`
(`p3/evidence_R10b/step3/import_closure_PowerSeries.txt`: `Mathlib.Topology.*` = 0 modules); after R10d, `Real` is
absent from its closure as well. `Ring` gains no import.

### R10c — the MonoidAlgebra connection (`Algebra/Convolution/FiniteFiber/MonoidAlgebra.lean`)

Contract `r10/CONSENSUS_r10.FINAL_8c6d01a0.md` (C3, test requirements 3, 8, 9); brief
`p3/BRIEF_R10c_monoidalgebra.md`. No declaration is renamed, deleted or re-stated: one new module and one new test;
`Finite.lean` and `FiniteFiber.lean` are unchanged (strict compare EXACT). Coordinator rulings (~12:55Z): the explicit
twin name `ofAddMonoidAlgebra_smul` is accepted (`to_additive` would produce `…_vadd`); no `AlgHom` in this unit.

#### Ledger (R10c)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| — | new module `RadiiPolynomial.Algebra.Convolution.FiniteFiber.MonoidAlgebra` (14 public declarations per twin, table below) | added | `p3/evidence_R10c/step2/frozen_types.txt`; `p3/evidence_R10c/step2/additive_generated.txt`; `p3/evidence_R10c/step2/axioms_per_declaration.txt` |
| `Algebra/Convolution.lean` (facade) | `+import RadiiPolynomial.Algebra.Convolution.FiniteFiber.MonoidAlgebra` and one docstring sentence | import change | `p3/evidence_R10c/HUB_R10c.md` |
| — | test module `RadiiPolynomial.Examples.tests.CV.FiniteFiberMonoidAlgebra` | added (test) | `p3/evidence_R10c/step1/targeted_build_final.log`; `p3/evidence_R10c/step3/tests_outcome.txt` |

#### New declarations (14 per twin; generated twins in `RadiiPolynomial.FiniteFiberAddConvolution`)

| FQN (multiplicative; `RadiiPolynomial.FiniteFiberConvolution.`) | additive twin (`RadiiPolynomial.FiniteFiberAddConvolution.`) | kind | hypotheses | simp? | computable? |
|---|---|---|---|---|---|
| `toMonoidAlgebra` | `toAddMonoidAlgebra` | def | `[Semiring R]`, `hf : (support fun m => coeff m f).Finite` | — | noncomputable (`Finsupp.ofSupportFinite`) |
| `coeff_toMonoidAlgebra` | `coeff_toAddMonoidAlgebra` | theorem | `[Semiring R]` | simp | — |
| `ofMonoidAlgebra` (explicit `R M`) | `ofAddMonoidAlgebra` | def (`→+*`) | `[Semiring R] [Monoid M] [HasMulAntidiagonal M] [DecidableEq M]` / `[Semiring R] [AddMonoid M] [HasAntidiagonal M] [DecidableEq M]` | — | computable (IR present) |
| `ofMonoidAlgebra_apply` | `ofAddMonoidAlgebra_apply` | theorem (rfl) | as `ofMonoidAlgebra` | no | — |
| `coeff_ofMonoidAlgebra` | `coeff_ofAddMonoidAlgebra` | theorem (rfl) | as `ofMonoidAlgebra` | simp | — |
| `ofMonoidAlgebra_single` | `ofAddMonoidAlgebra_single` | theorem | as `ofMonoidAlgebra` | simp | — |
| `ofMonoidAlgebra_injective` | `ofAddMonoidAlgebra_injective` | theorem | as `ofMonoidAlgebra` | no | — |
| `ofMonoidAlgebra_smul` | `ofAddMonoidAlgebra_smul` (explicit name; the generated one would be `…_vadd`) | theorem (rfl) | as `ofMonoidAlgebra` + `{S : Type w} [SMulZeroClass S R]` | simp | — |
| `ofMonoidAlgebra_toMonoidAlgebra` | `ofAddMonoidAlgebra_toAddMonoidAlgebra` | theorem (rfl) | as `ofMonoidAlgebra` | simp | — |
| `toMonoidAlgebra_ofMonoidAlgebra` | `toAddMonoidAlgebra_ofAddMonoidAlgebra` | theorem | as `ofMonoidAlgebra` (any proof `hx`) | simp | — |
| `mem_rangeS_ofMonoidAlgebra` | `mem_rangeS_ofAddMonoidAlgebra` | theorem (iff) | as `ofMonoidAlgebra` | no | — |
| `ofMonoidAlgebraEquivRangeS` (explicit `R M`) | `ofAddMonoidAlgebraEquivRangeS` | def (`≃+*` onto `(ofMonoidAlgebra R M).rangeS`) | as `ofMonoidAlgebra` | — | noncomputable |
| `ofMonoidAlgebraEquivRangeS_apply` | `ofAddMonoidAlgebraEquivRangeS_apply` | theorem (rfl) | as `ofMonoidAlgebra` | simp | — |
| `ofMonoidAlgebraEquivRangeS_symm_apply` | `ofAddMonoidAlgebraEquivRangeS_symm_apply` | theorem (rfl) | as `ofMonoidAlgebra` | simp | — |

Exact types: `p3/evidence_R10c/step2/frozen_types.txt`; generated bodies: `step2/additive_generated.txt`; flags:
`step2/decls_flags.txt`; axioms (all 28: `propext, Classical.choice, Quot.sound`): `step2/axioms_per_declaration.txt`.
Name-clash check (0 hits in library, Mathlib pin, ReferenceBook, book/paper/companions; the one Mathlib hit
`DirectSum.toAddMonoidAlgebra` is in another namespace): `step0/newname_grep.txt`. `FiniteFiber/MonoidAlgebra`
imports no topology, no `Ring`, no `CauchyProduct`, no `Analysis` (`p3/evidence_R10c/step3/import_closure.txt`).

### R10d — the `CauchyProductReal` adapter (`Algebra/Convolution/{CauchyProduct,CauchyProductReal}.lean`) (critic ACCEPT ~15:10Z)

Contract `r10/CONSENSUS_r10.FINAL_8c6d01a0.md` routed item S00-11; brief `p3/BRIEF_R10d_cauchyproductreal.md`. The
unit's strict compares were taken with the frozen v2 tool copy; the cohort-B gate re-runs under the v3 driver
(coordinator, ~14:40Z). All rows of this subsection are recorded before the R10d critic verdict.

#### Ledger (R10d)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `RadiiPolynomial.CauchyProduct.ratCast` | unchanged FQN, type, body, docstring and axioms; module `RadiiPolynomial.Algebra.Convolution.CauchyProduct` → `RadiiPolynomial.Algebra.Convolution.CauchyProductReal` (S00-11) (critic ACCEPT ~15:10Z) | moved | `p3/evidence_R10d/step2/ratcast_row_identity.txt` |
| `Algebra/Convolution/CauchyProduct.lean`: `import Mathlib.Basic.Real.Basic` | dropped (closure 2893 → 2884 modules; `Real` absent); modules that obtained ℝ only through `CauchyProduct` import the adapter or another real-number source (S00-11) (critic ACCEPT ~15:10Z) | import change | `p3/evidence_R10d/step3/closure_compare.txt`; `p3/evidence_R10d/step3/ClosureCP_after.txt` |
| `Algebra/Polynomial/MvPolynomial/WeightedL1.lean` imports | `+import RadiiPolynomial.Algebra.Convolution.CauchyProductReal` (its `toSeq_evalInBanach_of_coeffs` rewrites with `ratCast`) (critic ACCEPT ~15:10Z) | import change | `p3/evidence_R10d/step2/consumer_resolve.txt` |
| `Algebra/Convolution.lean` (facade) | `+import RadiiPolynomial.Algebra.Convolution.CauchyProductReal` and one docstring sentence; repairs the hub-only consumer `Examples/tests/CV/PowerSeriesBridge.lean` (critic ACCEPT ~15:10Z) | import change | `p3/evidence_R10d/HUB_R10d.md`; `p3/evidence_R10d/step3/control_PowerSeriesBridge_current_hub.txt` |

#### Moved declaration (critic ACCEPT ~15:10Z)

| FQN | type | body | docstring | axioms |
|---|---|---|---|---|
| `RadiiPolynomial.CauchyProduct.ratCast` | `∀ (a b : ℕ → ℚ) (n : ℕ), CauchyProduct (fun k => ↑(a k)) (fun k => ↑(b k)) n = ↑(CauchyProduct a b n)` | `CauchyProduct.map_CauchyProduct (Rat.castHom ℝ) a b n` | "Cauchy product with `ℚ → ℝ` cast." | `[propext, Classical.choice, Quot.sound]` |

Row identity IDENTICAL (name tree, kind, levels, raw and normalized type tree, mdata, axioms, theorem value tree; no
auxiliary constants on either side). Consumers: `Algebra/Polynomial/MvPolynomial/WeightedL1.lean` (the only user,
`rw` at :112, now importing the owning adapter); facade access through `Algebra/Convolution.lean`; ReferenceBook live
sources 0; paper v6.3 0. Reusable modules that need `CauchyProduct.ratCast` import the adapter, not the hub.

### C9-A — Taylor analysis, Geometric side (`Analysis/SequenceSpace/Geometric/*`, `CharacterTopology.lean`)

Triage rows S06-1, S06-3, S06-6, S06-16, S06-17, S06-18 and the C6 addendum S07-2-9. Strict compare PASS (227
surviving rows exact; 12 retired incl. generated auxiliaries; 5 new). Coordinator ruling (~14:00Z): the simp-set
delta below is accepted. Every replacement is checked in `p3/evidence_C9A/step3/PositiveControls_C9A.lean`.

#### Ledger (C9-A)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `l1Weighted.toPowerSeries` (root namespace; def) | `RadiiPolynomial.CauchyProduct.toPowerSeries (l1Weighted.toSeq a)`, the computable raw constructor (`rfl`; the bundled `toPowerSeriesLinearEquiv ℝ` is also `rfl`-equal but is not the replacement) (S06-1) | retired | `p3/evidence_C9A/step3/PositiveControls_C9A.lean`; `p3/evidence_C9A/step1/CONSUMER_SEARCH_retirements_before.txt` |
| `l1Weighted.coeff_toPowerSeries` (root; `@[simp]`) | `RadiiPolynomial.CauchyProduct.coeff_toPowerSeries (l1Weighted.toSeq a) n` (also `@[simp]`) (S06-1) | retired | idem |
| `l1Weighted.coeff_mul_eq_cauchyProduct` (root) | `(RadiiPolynomial.CauchyProduct.eq_coeff_mul (toSeq a) (toSeq b) n).symm` (S06-1) | retired | idem |
| `l1Weighted.evalAlgHomQ` (root; def) | `(l1Weighted.evalAlgHom z hz).restrictScalars ℚ` (Mathlib `AlgHom.restrictScalars`; `rfl` to the retired body) (S06-3) | retired | idem |
| `l1Weighted.evalAlgHomQ_apply` (root; `@[simp]`) | `rfl` / `simp` on `((evalAlgHom z hz).restrictScalars ℚ) a = eval a z` (S06-3) | retired | idem |
| private `l1Weighted.summable_diff_bound` (EvaluationDerivative) | `RadiiPolynomial.l1Weighted.summable_abs_mul_pow_pred a hν'_pos.le hν'_lt_ν` (S06-6) | retired (private) | `p3/evidence_C9A/step2/NEW_DELETED.txt` |
| private `RadiiPolynomial.l1Weighted.summable_derivative_bound` (Analytic) | `RadiiPolynomial.l1Weighted.summable_abs_mul_pow_pred a hr.le hrν` (S06-6) | retired (private) | idem |
| — | `RadiiPolynomial.l1Weighted.summable_abs_mul_pow_pred (a) {r} (hr : 0 ≤ r) (hrν : r < ν)` (Geometric/Omega.lean, beside `l1Omega.summable_abs_eval`) (S06-6) | added | `p3/evidence_C9A/step2/STRICT_COMPARE.md` |
| — | `@[simp] RadiiPolynomial.l1Weighted.toSeq_radiusRestrict : toSeq (radiusRestrict hσr a) n = toSeq a n` (Geometric/RadiusRestriction.lean) (S06-16) | added | `p3/evidence_C9A/step2/STRICT_COMPARE.md`; `p3/evidence_C9A/step2/LINT_NEW.txt` |
| — | `RadiiPolynomial.l1Weighted.aeval_of_norm_le_comp_radiusRestrict` (every complete normed ℝ-algebra target with `NormOneClass`) (S06-17) | added | `p3/evidence_C9A/step2/STRICT_COMPARE.md` |
| `RadiiPolynomial.l1Weighted.evalContinuousAlgHom_comp_radiusRestrict` | statement unchanged; re-proved as a corollary of `aeval_of_norm_le_comp_radiusRestrict` via `aeval_eq_evalContinuousAlgHom` (ReferenceBook Spine/A10_Geometry:256 unchanged) (S06-17) | proof only | `p3/evidence_C9A/step2/STRICT_COMPARE.md` |
| — | `RadiiPolynomial.l1Weighted.exists_eval_eq_of_analyticAt` (Geometric/AnalyticExt.lean: local real scalar analyticity at `0` gives a positive radius and a coefficient sequence) (S06-18) | added | `p3/evidence_C9A/step2/STRICT_COMPARE.md` |
| — | `RadiiPolynomial.Gelfand.continuous_of_continuous_apply` (CharacterTopology.lean; introduction rule of the local pointwise topology; no global instance) (S07-2-9) | added | `p3/evidence_C9A/step2/STRICT_COMPARE.md`; `p3/evidence_C9A/step1/item9_CharacterTopology.txt` |
| `Analysis/SequenceSpace/Geometric/Evaluation.lean`: `import Mathlib.RingTheory.PowerSeries.Basic` | dropped (still in its closure through `Algebra/Convolution/CauchyProduct`) | import change | `p3/evidence_C9A/step3/C9A_vs_baseline.diff` |

#### Detail (C9-A, fragment)

- Consumers of the retired names before the unit (Lake / tests / ReferenceBook / paper): 0 each; the gitignored
  Lake-root `tmp/` holds archived snapshots that mention `l1Weighted.toPowerSeries` and `coeff_mul_eq_cauchyProduct`.
- Attribute delta of the nine modules (`step2/SIMP_INVENTORY_DIFF.txt`): `@[simp]` removed with the retired heads
  `l1Weighted.coeff_toPowerSeries` and `l1Weighted.evalAlgHomQ_apply`; `@[simp]` added on
  `l1Weighted.toSeq_radiusRestrict`. No instance or reducibility change.
- `TaylorSpectrum.continuous_discCharacter` is now one term through `Gelfand.continuous_of_continuous_apply` (statement
  unchanged); the LaurentSpectrum and Spectrum/Topology consumers are left to C10 phase C.
  Resolved by cohorts B (round 2) and C (C10-B/C, S07-2-9): both consumers are one term through that lemma.
- New faces answer ReferenceBook friction (optional adoption, not a campaign edit): `toSeq_radiusRestrict`
  (Ch08/Sec5Taylor:126–137), `aeval_of_norm_le_comp_radiusRestrict` (Spine/A10_Geometry:320–326, complex square =
  instance `B = ℂ`), `exists_eval_eq_of_analyticAt` (Ch08/Sec5Taylor:202).

### C9-B — Taylor analysis, polynomial-bridge side (`Algebra/Polynomial/MvPolynomial/WeightedL1.lean`, `CompPoly/WeightedL1.lean`)

Triage rows S06-7, S06-9, S06-10, S06-11, S06-15. Strict compare: exactly one changed row, the approved weakening
`norm_fderiv_diff_evalInBanach_bilinear`. The `Array` grep gate is read as for C3-B (`CompPoly.toSeq_evalBanach`,
`compPoly_Dφ_bridge` = live certificate path; coordinator ruling, ~13:45Z).

#### Ledger (C9-B)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `MvPolyBridge.evalInBanach_C_fun` | `funext fun x => MvPolyBridge.evalInBanach_C r x` (its body) (S06-7) | retired (induction plumbing) | `p3/evidence_C9B/step3/probes/C9B_Controls.lean`; `p3/evidence_C9B/step4/CONSUMERS_post.txt` |
| `MvPolyBridge.evalInBanach_add_fun` | `funext fun x => MvPolyBridge.evalInBanach_add p q x` (its body) (S06-7) | retired (induction plumbing) | idem |
| `MvPolyBridge.evalInBanach_mul_X_fun` | `funext fun x => by simp [MvPolyBridge.evalInBanach]` (its body; pointwise `evalInBanach_mul` + `evalInBanach_X`) (S06-7) | retired (induction plumbing) | idem |
| `MvPolyBridge.norm_fderiv_diff_system_of_const_second_pderiv` | `MvPolyBridge.norm_fderiv_diff_evalInBanach_of_const_second_pderiv (φ_spec l) c a h (D₂ l) (hD₂ l) (hC l)` (S06-11) | retired (per-component wrapper) | idem |
| — | `MvPolyBridge.hasFDerivAt_evalInBanach (p : MvPolynomial (Fin L) ℚ) (a : Fin L → l1Weighted ν) : HasFDerivAt (fun x => evalInBanach p x) (MvPolynomial.polynomialDerivative (𝕜 := ℝ) p a) a` (`:= MvPolynomial.hasFDerivAt_aeval p a`) (S06-7) | added | `p3/evidence_C9B/step2/STRICT_COMPARE.md` |
| `MvPolyBridge.norm_fderiv_diff_evalInBanach_bilinear` | unchanged FQN; hypothesis `hLip` global → pointwise at `(c, a)` (old and new types below); an old call `… p c a h hLip` becomes `… p c a h (hLip c a)` (S06-10) | statement changed (approved weakening) | `p3/evidence_C9B/step3/probes/C9B_Controls.lean`; `p3/evidence_C9B/step2/STRICT_COMPARE.md` |
| `MvPolyBridge.differentiable_evalInBanach`, `MvPolyBridge.fderiv_evalInBanach` (S06-7); `MvPolyBridge.norm_fderiv_diff_evalInBanach_of_const_second_pderiv`, `MvPolyBridge.CompPoly.norm_fderiv_evalBanach_sub_le` (S06-10) | statements byte-identical; re-proved through `hasFDerivAt_evalInBanach` and the pointwise `_bilinear` | proof only | `p3/evidence_C9B/step2/STRICT_COMPARE.md` |
| `Algebra/Polynomial/MvPolynomial/WeightedL1.lean` imports | `MvPolynomial.Calculus` instead of `MvPolynomial.Core` (closure 4025 → 4036; downstream closures unchanged) | import change | `p3/evidence_C9B/step2/closure_WL1_delta.txt` |

#### Changed statement (C9-B, the one approved row)

`MvPolyBridge.norm_fderiv_diff_evalInBanach_bilinear` (S06-10); conclusion, constant `C` and all other binders unchanged.

- OLD: `∀ {L : ℕ} {ν : PosReal} (p : MvPolynomial (Fin L) ℚ) (c a h : Fin L → l1Weighted ν) {C : ℝ}, (∀ (x y : Fin L → l1Weighted ν), ∑ i, ‖evalInBanach (pderiv i p) x - evalInBanach (pderiv i p) y‖ ≤ C * ‖x - y‖) → ‖(fderiv ℝ (fun x => evalInBanach p x) c - fderiv ℝ (fun x => evalInBanach p x) a) h‖ ≤ C * ‖c - a‖ * ‖h‖`
- NEW: `∀ {L : ℕ} {ν : PosReal} (p : MvPolynomial (Fin L) ℚ) (c a h : Fin L → l1Weighted ν) {C : ℝ}, ∑ i, ‖evalInBanach (pderiv i p) c - evalInBanach (pderiv i p) a‖ ≤ C * ‖c - a‖ → ‖(fderiv ℝ (fun x => evalInBanach p x) c - fderiv ℝ (fun x => evalInBanach p x) a) h‖ ≤ C * ‖c - a‖ * ‖h‖`
- Pin: `C9BControls.old_norm_fderiv_diff_evalInBanach_bilinear` and an anonymous `example` at the OLD type, both closed by
  the new lemma at `hLip c a` (`p3/evidence_C9B/step3/probes/C9B_Controls.lean`). Callers: before, in-file 1
  (`_of_const_second_pderiv`), external 0; after, in-file 1 + CompPoly/WeightedL1 1
  (`CompPoly.norm_fderiv_evalBanach_sub_le`); ReferenceBook 0.

#### Detail (C9-B, fragment)

- Generated: `MvPolyBridge.fderiv_evalInBanach._simp_1_2` (internal simp auxiliary of the old induction proof) is no
  longer produced.
- Consumers of the retired names (word-boundary; Lake incl. Examples/tests, ReferenceBook excl. ledger, companions,
  paper v6.3): Lean code in-file only before, 0 after; ReferenceBook 0; paper 0; companions 4 each
  (MvPolynomial/WeightedL1.tex + sidecar): P4 companion refresh.
- C6 tail precondition: `MvPolynomial/WeightedL1.lean` no longer uses root `differentiable_pi_apply`; Lake-wide `.lean`
  hits are its definition (`Analysis/Calculus/Pi.lean:20`) and a docstring mention (`Tactic/AutoPolyFDeriv.lean:22`);
  ReferenceBook 0. Its retirement (S00-16) is not part of this cohort's rows.
  Resolved by cohorts B (round 2) and C (C6 tail): `differentiable_pi_apply` is retired → Mathlib `differentiable_apply`.

## API campaign 2026-10-12 — cohorts B (round 2) and C

Clusters C4, C10-B/C (with the C10 addendum), C11, C12 (with the C3 addendum), C13, C14 and C14b, the C7 addendum
and the C6 tail of the 2026-10-12 API campaign. Each cluster was accepted by its independent critic, with the critic's
fixes applied, and stands pending the serialized round-2 library, test and ReferenceBook builds (`DECISIONS.md` of the
campaign, entries ~19:20Z on 10-12 to ~09:00Z on 10-13). Coordinator rulings in `DECISIONS.md` override fragment text
where they differ; the kinds follow the critics' REVIEWED TYPE CHANGES sections.

Each cluster subsection opens with a ledger, one row per migration: old FQN | new FQN or replacement | kind |
evidence. Kinds: `moved` (FQN unchanged, new module), `retired` (replacement named), `retired (private)`,
`privatized`, `renamed (no alias)`, `binder drop`, `statement changed`, `generalization`, `weakening`,
`migrated instance path`, `redefined` (body changed, type exact), `metadata`, `de-simp`, `added`, `added (private)`,
`added, then removed`, `proof only`, `syntax only`, `hygiene`, `docstring`, `import change`. Regenerated auxiliaries
(`_proof_*`, `.eq_1`, matchers, notation artifacts) are not public API; they are named only in one-sentence notes.

Evidence paths starting with `p3/` are relative to `exterior/tmp/api_campaign_20261012/`; `DECISIONS.md` is that
directory's decision log. Both lie in the outer repository, outside the Lake root.

ReferenceBook consumers: no ReferenceBook source is edited. Every retired, privatized or binder-dropped name below has
0 ReferenceBook uses (cluster critics).

### C4 — WeightedL1 carrier split (`Analysis/SequenceSpace/WeightedL1/*`, NEW `WeightedL1/Carrier.lean`)

Triage rows S02-1 … S02-15, S00-10 and the addenda S04-16, S07-1-2, S09-2-12, S08-1-5, S08-1-6. All FQNs are under
`RadiiPolynomial.`; no FQN is renamed and no deprecated alias is needed.

#### Ledger (C4)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| 130 constants of `WeightedL1/Algebra.lean` (the carrier half; list below) | unchanged FQNs; `WeightedL1/Algebra.lean` → `WeightedL1/Carrier.lean` (S02-1) | moved | `p3/evidence_C4/step1/S02_1_LINE_MAP.txt`; `p3/evidence_C4/step2/moved_rows_hygiene_check.txt` |
| `lpOneAlg.norm_ofReal_one_pos` | unchanged FQN, type and levels; `WeightedL1/Columns.lean` → `WeightedL1/Carrier.lean`, the one public copy (S02-2) | moved | `p3/evidence_C4/step3/old_interface_pins.out` |
| private `lpOneAlg.norm_mulOfReal_one_pos` (Algebra), private `lpOneAlg.norm_ofReal_one_pos` (Multilinear) | `lpOneAlg.norm_ofReal_one_pos` (S02-2) | retired (private) | `p3/evidence_C4/step2/RULES_C4.json` |
| private `lpOneAlg.mulFiber_finite`, private `lpOneAlg.addFiber_finite` (Algebra) | Mathlib `DiscreteConvolution.mulFiber_finite` / `DiscreteConvolution.addFiber_finite` (S00-10) | retired (private) | `p3/evidence_C4/step1/envlean_S00_10.txt` |
| `lpOneAlg.norm_eq_bilatFinSum` | unchanged FQN and statement (`Int.negSucc` hypotheses kept); `Chebyshev/Algebra.lean` → `WeightedL1/Carrier.lean`, re-proved through the sign split (S04-16) | moved | `p3/evidence_C4/step1/S04_16_deleted_hunk.txt`; `p3/evidence_C4/step3/old_interface_pins.out` |
| — | `lpOneAlg.norm_eq_tsum_natCast_add_tsum_neg`, `lpOneAlg.norm_eq_tsum_natCast_of_neg` (Carrier; sign split over `ℤ`, any fibers) (S07-1-2) | added | `p3/evidence_C4/step2/rowdiff.txt` |
| — | `lpOneAlg.norm_eq_natFinSum_of_finSupp` (Carrier; arbitrary fibers; replaces C13's `ChebyshevIVP.lpOneAlg.norm_eq_natFinSum_of_finSupp`) (S09-2-12) | added | `p3/evidence_C4/step3/fourier_rewire.out` |
| — | `lpOneAlg.toRealSeqAddHom : lpOneAlg M E →+ (M → 𝕜)`, `lpOneAlg.toRealSeqAddHom_apply` (`@[simp]`), `lpOneAlg.toRealSeq_injective`, `lpOneAlg.toRealSeq_finset_sum` (Carrier) (S02-8) | added | `p3/evidence_C4/step2/INVENTORY_diff.txt` |
| — | `lpOneAlg.toRealSeq_single_eq_piSingle` (Carrier) (S02-9) | added | `p3/evidence_C4/step2/rowdiff.txt` |
| — | `WeightedScalar.normedSpaceCore` (WeightedL1/Scalar) (S02-3) | added | idem |
| — | `lpOneAlg.norm_mulLeftCLM_le`, `lpOneAlg.norm_mulRightCLM_le` (UniversalProperty, section `MulCLMNorm`) (S08-1-5) | added | idem |
| — | `lpOneAlg.diagCLM_comp_headProj` (Diagonal) (S08-1-6) | added | idem |
| `lpOneAlg.colRatio_add_of_head_tail`, `lpOneAlg.colRatio_add_of_head_zero` | unchanged FQN; `[lpAlgSmulCompat 𝕜 I E] [lpAlgRingData 𝕜 J G] [lpAlgSmulCompat 𝕜 J G]` dropped (S02-4) | binder drop | `p3/evidence_C4/probes/OldInterfacePins.lean`; `p3/evidence_C4/CRITIC_C4.md` |
| `lpOneAlg.opNorm_add_eq_iSup`, `lpOneAlg.opNorm_add_eq_iSup_of_head_zero`, `lpOneAlg.opNorm_joint_eq_iSup` | unchanged FQN; `[lpAlgRingData 𝕜 J G] [lpAlgSmulCompat 𝕜 J G]` dropped (S02-4) | binder drop | idem |
| `lpOneAlg.instMulConvCompatOfAntidiag`, `lpOneAlg.instConvCompatOfAntidiag` (paper-cited; priority 1100) | unchanged FQN; `[DecidableEq M]` dropped (S02-5, Codex Q7); 0 `@`-uses in Lake root, ReferenceBook and paper | binder drop | `p3/evidence_C4/step3/Q7_RECORD_S02_5.md`; `p3/evidence_C4/probes/OldInterfacePins.lean` |
| `FiberTrivialization.equiv_symm_apply_equiv`, `FiberTrivialization.equiv_apply_equiv_symm` | unchanged; no longer `@[simp]` (Mathlib `LinearEquiv.symm_apply_apply` / `apply_symm_apply` are) (S02-7) | de-simp | `p3/evidence_C4/step1/S02_7_faces.out` |
| `WeightedScalar.instNormedAddCommGroup`, `WeightedScalar.instNormedSpace` | same names and types; built from `normedSpaceCore` with an explicit `edist`; `with_reducible_and_instances rfl` against the verbatim old body, `toEDist` included (S02-3) | redefined | `p3/evidence_C4/step1/defeq_gate_S02_3_after.out`; `p3/evidence_C4/probes/DefeqGate_S02_3.lean` |
| `lpOneAlg.single_mul_single` (paper-cited) | type Expr-equal; body through the two-atom rule `DiscreteConvolution.single_addRingConvolution_single` (S02-9) | proof only | `p3/evidence_C4/step3/old_interface_pins.out` |
| `WeightedL1/Algebra.lean`, `WeightedL1/UniversalProperty.lean` | `open DiscreteConvolution`; the `DiscreteConvolution.` qualifications dropped (Algebra 77 → 0, UniversalProperty 6 → 0); signatures identical (S02-10) | proof only | `p3/evidence_C4/step2/S02_10_signature_identity.txt` |
| `WeightedL1/{Carrier,Algebra,Columns,ScalarInstances}.lean` and the facade `WeightedL1.lean` | `Carrier` imports only `WeightedL1.FiberTrivialization`, `Mathlib.Analysis.Normed.Lp.lpSpace`, `Mathlib.Analysis.Normed.Module.TransferInstance`; `Algebra` imports `Carrier` and `Algebra.Convolution.Ring`; `Columns` and `ScalarInstances` import `Carrier`, not `Algebra`; the facade imports `Carrier` (S02-1) | import change | `p3/evidence_C4/step3/closure_measure.txt`; `p3/evidence_C4/step3/carrier_minus_lpSpace_closure.txt` |
| Columns (9) and Diagonal (40) run-ledger tags; `evalCLM` fields; module docs | 49/49 tags stripped (S02-15); `evalCLM` value identical (S02-11); module docs (S02-12/-13/-14) | docstring | `p3/evidence_C4/step4/C4_vs_baseline.diff` |

Moved public names (S02-1, S02-2, S04-16), extracted from the fragment `p3/evidence_C4/RENAMES_C4.md`; they are 132
constants including structure auxiliaries (`rec`, `casesOn`, `mk`, …), or 93 source-level names:

- `Chebyshev.Algebra` → `WeightedL1.Carrier` (1): `lpOneAlg.norm_eq_bilatFinSum`
- `WeightedL1.Algebra` → `WeightedL1.Carrier` (130): `FiberTrivialization.ofLpAlgRingData`, `FiberTrivialization.ofLpAlgRingData_equiv_apply`, `FiberTrivialization.ofLpAlgRingData_equiv_symm_apply`, `FiberTrivialization.toLpAlgRingData`, `FiberTrivialization.toLpAlgRingData_ofReal`, `FiberTrivialization.toLpAlgRingData_toReal`, `FiberTrivialization.toLpAlgRingData_weight`, `FiberTrivialization.toLpAlgSmulCompat`, `lpAlgRingData`, `lpAlgRingData.casesOn`, `lpAlgRingData.ctorIdx`, `lpAlgRingData.mk`, `lpAlgRingData.mk.noConfusion`, `lpAlgRingData.noConfusion`, `lpAlgRingData.noConfusionType`, `lpAlgRingData.norm_ofReal_eq`, `lpAlgRingData.ofReal`, `lpAlgRingData.ofReal_add`, `lpAlgRingData.ofReal_toReal`, `lpAlgRingData.ofReal_zero`, `lpAlgRingData.rec`, `lpAlgRingData.recOn`, `lpAlgRingData.toReal`, `lpAlgRingData.toReal_add`, `lpAlgRingData.toReal_neg`, `lpAlgRingData.toReal_ofReal`, `lpAlgRingData.toReal_zero`, `lpAlgRingData.weight`, `lpAlgRingData.weight_def`, `lpAlgSmulCompat`, `lpAlgSmulCompat.casesOn`, `lpAlgSmulCompat.mk`, `lpAlgSmulCompat.rec`, `lpAlgSmulCompat.recOn`, `lpAlgSmulCompat.toReal_smul`, `lpOneAlg`, `lpOneAlg.abs_mulToRealSeq_le`, `lpOneAlg.abs_toRealSeq_le`, `lpOneAlg.casesOn`, `lpOneAlg.ctorIdx`, `lpOneAlg.equiv`, `lpOneAlg.evalCLM`, `lpOneAlg.evalCLM_apply`, `lpOneAlg.ext`, `lpOneAlg.ext_mulToRealSeq`, `lpOneAlg.ext_toRealSeq`, `lpOneAlg.finsum_norm_le_of_cols`, `lpOneAlg.hasSum_single`, `lpOneAlg.hasSum_single_mapCLM`, `lpOneAlg.instCoeFunForall`, `lpOneAlg.instCompleteSpace`, `lpOneAlg.instNormedAddCommGroup`, `lpOneAlg.instNormedSpaceBase`, `lpOneAlg.isometry_mk`, `lpOneAlg.mk`, `lpOneAlg.mk.inj`, `lpOneAlg.mk.injEq`, `lpOneAlg.mk.noConfusion`, `lpOneAlg.mk.sizeOf_spec`, `lpOneAlg.mkAddHom`, `lpOneAlg.mulToRealSeq`, `lpOneAlg.mulToRealSeq_add`, `lpOneAlg.mulToRealSeq_neg`, `lpOneAlg.mulToRealSeq_sub`, `lpOneAlg.mulToRealSeq_zero`, `lpOneAlg.noConfusion`, `lpOneAlg.noConfusionType`, `lpOneAlg.norm_apply_le_norm`, `lpOneAlg.norm_def`, `lpOneAlg.norm_eq_abs_mulToReal_mul_weight`, `lpOneAlg.norm_eq_abs_toReal_mul_weight`, `lpOneAlg.norm_eq_tsum`, `lpOneAlg.norm_le_of_cols`, `lpOneAlg.norm_single`, `lpOneAlg.rec`, `lpOneAlg.recOn`, `lpOneAlg.single`, `lpOneAlg.single_smul`, `lpOneAlg.summable_abs_mulToRealSeq`, `lpOneAlg.summable_abs_toRealSeq`, `lpOneAlg.summable_norm`, `lpOneAlg.summable_norm_prod`, `lpOneAlg.summable_norm_shift`, `lpOneAlg.toLp`, `lpOneAlg.toLp_add`, `lpOneAlg.toLp_neg`, `lpOneAlg.toLp_smul`, `lpOneAlg.toLp_sub`, `lpOneAlg.toLp_zero`, `lpOneAlg.toRealSeq`, `lpOneAlg.toRealSeq_add`, `lpOneAlg.toRealSeq_neg`, `lpOneAlg.toRealSeq_single`, `lpOneAlg.toRealSeq_smul`, `lpOneAlg.toRealSeq_sub`, `lpOneAlg.toRealSeq_zero`, `lpOneAlgWeightMul`, `lpOneAlgWeightMul.casesOn`, `lpOneAlgWeightMul.mk`, `lpOneAlgWeightMul.norm_ofReal_mul_le`, `lpOneAlgWeightMul.norm_ofReal_one_zero`, `lpOneAlgWeightMul.rec`, `lpOneAlgWeightMul.recOn`, `lpOneAlgWeightMul.weight_add_le`, `lpOneAlgWeightMul.weight_zero`, `lpOneAlgWeightSubMul`, `lpOneAlgWeightSubMul.casesOn`, `lpOneAlgWeightSubMul.mk`, `lpOneAlgWeightSubMul.norm_ofReal_one_ge`, `lpOneAlgWeightSubMul.one_le_weight`, `lpOneAlgWeightSubMul.rec`, `lpOneAlgWeightSubMul.recOn`, `lpOneAlgWeightSubMul.tolpOneAlgWeightMul`, `lpOneMulAlgWeightMul`, `lpOneMulAlgWeightMul.casesOn`, `lpOneMulAlgWeightMul.mk`, `lpOneMulAlgWeightMul.norm_ofReal_mul_le`, `lpOneMulAlgWeightMul.norm_ofReal_one_one`, `lpOneMulAlgWeightMul.rec`, `lpOneMulAlgWeightMul.recOn`, `lpOneMulAlgWeightMul.weight_mul_le`, `lpOneMulAlgWeightMul.weight_one`, `lpOneMulAlgWeightSubMul`, `lpOneMulAlgWeightSubMul.casesOn`, `lpOneMulAlgWeightSubMul.mk`, `lpOneMulAlgWeightSubMul.norm_ofReal_one_ge`, `lpOneMulAlgWeightSubMul.one_le_weight`, `lpOneMulAlgWeightSubMul.rec`, `lpOneMulAlgWeightSubMul.recOn`, `lpOneMulAlgWeightSubMul.tolpOneMulAlgWeightMul`
- `WeightedL1.Columns` → `WeightedL1.Carrier` (1): `lpOneAlg.norm_ofReal_one_pos`

- Regenerated auxiliaries (`WeightedScalar.instNormedAddCommGroup._proof_{1,2,3,5,6,7,8}`, `lpOneAlg.evalCLM._proof_{1,2}`,
  `lpOneAlg.norm_eq_bilatFinSum._proof_1_1`) have exact parent types and are not public API.

### C10-B/C — Chebyshev phases B and C, phase-A tail and the C10 addendum (`Analysis/SequenceSpace/Chebyshev/*`, NEW `Chebyshev/Symmetrize.lean`)

Triage rows S07-1-1 … S07-1-11, S07-2-1/-2/-3/-5/-6/-7/-8/-9/-10/-11/-14, the phase-A tail S04-13/-17/-22 and the C10
addendum S09-2-13/-19/-21, CONS-T E2, S07-2-15. S04-17 and S04-22 were already landed by C7-A (verified, no edit).

#### Ledger (C10-B/C)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `RadiiPolynomial.summable_norm_natCast`, `RadiiPolynomial.norm_fiber_natCast` | unchanged FQN; `Chebyshev/UConversion.lean` → `Chebyshev/Algebra.lean`, after `l1Chebyshev.norm_fiber` (S07-1-1) | moved | `p3/evidence_C10BC/step2/compare.log` |
| `RadiiPolynomial.l1Chebyshev.IsSymmetric`, `.symmetrize`, `.symmetrize_toSeq`, `.symmetrize_add`, `.symmetrize_smul`, `.symmetrize_norm_le`, `.symmetrize_CLM`, `.symmetrize_CLM_apply`, `.symmetrize_CLM_norm_le`, `.symmetrize_isSymmetric`, `.symmetrize_eq_self_of_isSymmetric`, `.symmetrize_single_negSucc`, `.mul_symmetrize_single_toSeq`, `.natEmbed`, `.natEmbed_toSeq`, `.natEmbed_toSeq_natCast`, `.natEmbed_toSeq_negSucc`, `.norm_natEmbed`, `.natEmbed_single` (19 public; private helpers move with them) | unchanged FQN; `Chebyshev/Bordered.lean` → `Chebyshev/Symmetrize.lean` (S07-1-3, variant B); `l1Chebyshev.nonnegRestrict_symmetrize` stays in Bordered | moved | `p3/evidence_C10BC/step2/compare.log`; `p3/evidence_C10BC/step3/IMPORT_LISTS_final.txt` |
| `RadiiPolynomial.uIntegrate_toSeq` | private, same statement; public faces `uIntegrate_toSeq_zero` / `_negSucc` / `_succ` (S07-1-10) | privatized | `p3/evidence_C10BC/step1/S07_1_10_usage.txt` |
| `RadiiPolynomial.chebyshevFromU_toSeq` | private, same statement; public faces `chebyshevFromU_toSeq_natCast` / `_negSucc` (S07-1-10) | privatized | idem |
| private `MvPolyBridge.CompPoly.Chebyshev.physicalInput` (CompPoly/Chebyshev) | `RadiiPolynomial.l1Chebyshev.symmetricRetract ν` (definitionally equal) (S07-1-7) | retired (private) | `p3/evidence_C10BC/step2/compare.log` |
| private `CrossGeometry.add_inv_le_of_inv_le_le` (Joukowski), private `PhysicalSpectrum.focal_le_of_annulus` (Ellipse; identical statement) | `RadiiPolynomial.CrossGeometry.add_inv_le_add_inv_of_inv_le_of_le` (same statement) (S07-2-5) | retired (private) | idem |
| `RadiiPolynomial.borderedTU_equiv` | unchanged FQN; the unreferenced `[Fact (1 ≤ ν)]` dropped (`{ν} [Fact (1 < ν)]`); body built from `borderedToU_CLM`, `borderedFromU_CLM` (verbatim old body equal by `rfl`) (S07-1-5) | binder drop | `p3/evidence_C10BC/step3/old_interface_pins.out`; `p3/evidence_C10BC/CRITIC_C10BC.md` |
| `RadiiPolynomial.borderedToU_CLM_norm_mul_borderedFromU_CLM_norm_le` | unchanged FQN; `{ν} [Fact (1 < ν)]`; the `borderedToU_CLM` instance argument is now the section-local private `fact_one_le_of_one_lt` (Prop, proof-irrelevant; semantically a binder drop, pin A1) | statement changed | idem |
| private `MvPolyBridge.CompPoly.Chebyshev.coe_physical_eval` | `physicalInput (a i)` → `l1Chebyshev.symmetricRetract ν (a i)` in the statement (definitionally equal) | statement changed (private) | `p3/evidence_C10BC/CRITIC_C10BC.md` |
| `RadiiPolynomial.Galerkin.wt` | `def … if k = 0 then 1 else 2ν^k` → `abbrev … := borderedWeight ν k`; type exact; reducibility default → reducible (S07-1-6) | metadata | `p3/evidence_C10BC/step3/old_interface_pins.out`; `p3/evidence_C10BC/step2/INVENTORY_diff.txt` |
| `RadiiPolynomial.PhysicalSpectrum.retract` | body forwards to `l1Chebyshev.symmetricRetract ν`; type exact (S07-1-7) | redefined | `p3/evidence_C10BC/step3/old_interface_pins.out` |
| — | `l1Chebyshev.nonnegRestrict_norm_le`, `l1Chebyshev.nonnegRestrict_chebyshevFromU` (Bordered) (S07-1-4) | added | `p3/evidence_C10BC/step2/INVENTORY_diff.txt` |
| — | `borderedTU_equiv_apply` (`@[simp]`), `borderedTU_equiv_symm_apply` (`@[simp]`), `coe_borderedTU_equiv`, `coe_borderedTU_equiv_symm`, `norm_borderedTU_equiv_mul_norm_symm_le` (Bordered) (S07-1-5) | added | idem |
| — | `l1Chebyshev.symmetricRetract : l1Chebyshev ν →L[ℝ] symmetricSubalgebra ν` (a continuous linear retraction, not an algebra hom), `coe_symmetricRetract` (`@[simp]`), `symmetricRetract_coe` (`@[simp]`), `norm_symmetricRetract_le` (SymmetricSubalgebra) (S07-1-7) | added | idem |
| — | `l1Chebyshev.physicalBorderedEquiv : symmetricSubalgebra ν ≃ₗᵢ[ℝ] l1Bordered ν`, `physicalBorderedEquiv_apply` (`@[simp]`) (SymmetricSubalgebra) (S07-1-8) | added | idem |
| — | `l1Chebyshev.evalAtCLM`, `evalAtCLM_apply` (`@[simp]`), `norm_evalAtCLM_le` (Evaluation) (S07-1-9) | added | idem |
| — | `RadiiPolynomial.CrossGeometry.add_inv_le_add_inv_of_inv_le_of_le` (Joukowski) (S07-2-5) | added | idem |
| — | `l1Chebyshev.finSum_le_norm` (the C13-retired `ChebyshevIVP.l1Chebyshev_finSum_le_norm` without its unused `[Fact (1 ≤ ν)]`), `l1Chebyshev.ext_natCast_negSucc` (Algebra) (C10 addendum S09-2-13/-19) | added | `p3/evidence_C10BC/CRITIC_C10BC.md` |
| — | `l1Chebyshev.norm_toSeq_mul_le`, `l1Chebyshev.summable_toSeq_mul_of_abs_le_one` (Evaluation) (C10 addendum S09-2-21) | added | `p3/evidence_C10BC/step2/INVENTORY_diff.txt` |
| — | `lpOneAlg.norm_single_geomFiberZ` (Chebyshev/Scalar; `UnitLift` rewired to it) (C10 addendum CONS-T E2) | added | `p3/evidence_C10BC/step3/CLOSURE_ChebyshevScalar_final.txt` |
| — | `RadiiPolynomial.CrossGeometry.semiMajor_le_self` (Joukowski): added by C10-B/C, then REMOVED by the coordinator — no consumer after C13's inline fallback (S07-2-15 REJECTED) | added, then removed | `p3/evidence_C10BC/RENAMES_C10BC.md`; `DECISIONS.md` |
| `l1Chebyshev.toSeq_finset_sum` (S04-13); `nonnegRestrict_norm_of_isSymmetric`, `symmetrize_norm_le`, `norm_symmetrize_eq`, `norm_le_norm_symmetrize_of_neg_eq_zero` (S07-1-2); `borderedFromU_norm_le`, `borderedToU_borderedFromU`, `nonnegRestrictCLM` bound (S07-1-4); `derivativeBound_ratCast`, `derivativeLipschitzBound_ratCast`, `derivativeBound_nonneg`, `derivativeLipschitzBound_nonneg`, `derivativeLipschitzBound_mono` (S07-2-1); `norm_derivative_apply_le`, `norm_derivative_sub_apply_le` (S07-2-2, through `CompPoly.norm_sum_pderiv_(sub_)mul_le`); `norm_derivative_sub_le_of_norm_sub` (S07-2-3); `LaurentSpectrum.continuous_annulusCharacter`, `PhysicalSpectrum.continuous_ellipseCharacter` (S07-2-9, through `Gelfand.continuous_of_continuous_apply`); `summable_eval` (addendum) | statements unchanged (short names as in the fragment); re-proved | proof only | `p3/evidence_C10BC/step2/compare.log` |
| UConversion and Chebyshev module headers; S07-2-6/-7/-8/-14 interface docstrings | headers (a)–(d) rewritten (S07-1-11); UConversion header "sharp" → "(attainment is not proved)"; docstrings added | docstring | `p3/evidence_C10BC/step4/C10BC_vs_baseline.diff` |
| `Chebyshev/{Symmetrize,Bordered,UnitLift,Evaluation,SymmetricSubalgebra}.lean`, `CompPoly/Chebyshev/Coefficients.lean`, facade `Chebyshev.lean` | variant-B graph: Symmetrize → Chebyshev.Algebra + Geometric.Basic; Bordered → UConversion + Symmetrize; UnitLift → WeightedL1.UniversalProperty + Symmetrize; Coefficients → CompPoly.Laurent + Symmetrize; SymmetricSubalgebra → Evaluation + Bordered; no Bordered → SymmetricSubalgebra edge; the facade gains `Symmetrize` | import change | `p3/evidence_C10BC/step3/IMPORT_LISTS_final.txt`; `p3/evidence_C10BC/step3/CLOSURE_GAIN.tsv` |

- Nine regenerated or renumbered `_proof_` auxiliaries (parents `borderedTU_equiv`, `natEmbed`, `norm_symmetrize_eq`,
  `symmetrize_CLM`, `nonnegRestrict_norm_of_isSymmetric`) and the no-longer-pregenerated `derivativeBound.eq_1`,
  `derivativeLipschitzBound.eq_1`, `Galerkin.wt.eq_1`, `LinearMap.mkContinuous.congr_simp` are not public API.

### C11 — Fourier / Rees (`Algebra/Rees/Laurent/{Euler,Gamma}.lean`, `Analysis/SequenceSpace/Fourier/*`, `Applications/Fourier/*`)

Triage rows S08-1-1, -2, -4, -5, -6, -7, -8, -9, -10, -11. No FQN is renamed; no deprecated alias.

#### Ledger (C11)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `RadiiPolynomial.Rees.Laurent.gammaW_inv_le` | unchanged FQN and type; `Fourier/GammaLeakage.lean` → `Rees/Laurent/Gamma.lean` (section `Gamma`, after `gammaW_pos`) (S08-1-4) | moved | `p3/evidence_C11/step2/compare_lib.log` |
| `RadiiPolynomial.Rees.Laurent.deltaU_one`, `.deltaU_X_pow_smul_one`, `.X_pow_smul_one_ne_zero`, `.z_ne_zero`, `.PH_z` | unchanged FQN; the elaborated `0 : U R` is now the default `ZeroMemClass` zero (was the selected `instUZero`); binders, levels and axioms unchanged (S08-1-1) | statement changed | `p3/evidence_C11/step3/migrated_rows.out`; `p3/evidence_C11/probes/MigratedRows_S08_1_1.lean` |
| `RadiiPolynomial.Rees.Laurent.specCoeff t f` | `fun k => (specU t f).coeff k`, by `coeff_specU` (S08-1-2) | retired | `p3/evidence_C11/probes/RetiredRawBlock_Replacements.lean`; `p3/evidence_C11/step3/retired_replacements.out` |
| `RadiiPolynomial.Rees.Laurent.rawHead H a` | `Set.indicator (↑H : Set ℤ) a` (all `a : ℤ → R`) (S08-1-2) | retired | idem |
| `RadiiPolynomial.Rees.Laurent.rawDiag lam a` | `lam * a` (pointwise, all `a : ℤ → R`) (S08-1-2) | retired | idem |
| `RadiiPolynomial.Rees.Laurent.specCoeff_deltaU`, `.specCoeff_qDelta`, `.specCoeff_PH`, `.specCoeff_z` | `specU_deltaU`, `specU_qDelta`, `specU_PH`, `specU_z` (with `coeff_specU`, `coeff_deltaL` / `coeff_diagL`, `coeff_single_eq`); each old statement re-derived verbatim (S08-1-2) | retired | idem |
| `RadiiPolynomial.Rees.Laurent.rawHead_rawDiag` | `Set.indicator ↑H (lam * a) = lam * Set.indicator ↑H a` (`funext` + Mathlib `Set.indicator_mul_right`; Codex Q1) (S08-1-2) | retired | idem |
| `RadiiPolynomial.Rees.Laurent.rawHead_rawDiag_tail` | `Set.indicator ↑H (lam * (a - Set.indicator ↑H a)) = 0` (pointwise `indicator_of_mem` / `indicator_of_notMem`, `sub_self`; Codex Q1) (S08-1-2) | retired | idem |
| `RadiiPolynomial.Rees.Laurent.rawDiag_eq_mul`, `.rawHead_eq_indicator` | definitional records of the two replacements above (S08-1-2) | retired | idem |
| — | `RadiiPolynomial.Rees.Laurent.specU (t : R) : U R →+* R[T;T⁻¹]` (= `mapRingHom ℤ (evalRingHom t)` after `(U R).val`; noncomputable), `coeff_specU`, `specU_z`, `specU_deltaU`, `specU_qDelta`, `specU_PH` (Euler) (S08-1-2) | added | `p3/evidence_C11/step2/compare_lib.log` |
| `RadiiPolynomial.Fourier.norm_mulLeftCLM_le` | type identical; body `lpOneAlg.norm_mulLeftCLM_le c` (S08-1-5) | proof only | idem |
| `RadiiPolynomial.Fourier.Semilinear.diagCLM_comp_headProj_of_head_zero` | type identical; body `lpOneAlg.diagCLM_comp_headProj (winZ N) r C hr …` (S08-1-6) | proof only | idem |
| `RadiiPolynomial.Fourier.Semilinear.toRealSeq_finset_sum` | type identical; body `lpOneAlg.toRealSeq_finset_sum s a k` (S08-1-7) | proof only | idem |
| `RadiiPolynomial.Fourier.Semilinear.fderiv_sub_modelDeriv` | type identical; proof through `defect_eq` (Semilinear no longer realizes `Fourier.defect.eq_1`) (S08-1-9) | proof only | idem |
| GammaLeakage sections HeadDiagonals/Tail/Leak; Semilinear §§3–9, 11–13; SemilinearFirstOrder §§2–3 | local notations `𝓔`, `𝓟[N]`, `𝓠[N]`, `𝓛[b]`; types and def bodies Expr-identical (S08-1-10, -11) | syntax only | `p3/evidence_C11/step1/cmp_S08_1_11_Semilinear.out`; `p3/evidence_C11/step1/cmp_S08_1_10_GammaLeakage_negctl.out` |
| Support, TailWindow, GammaLeakage, Gamma, facade docs | run-ledger tags stripped, file pointers, facade blocks merged; the GammaLeakage/Semilinear "Promoted from … by unit L00x" paragraphs removed (Codex Q3/Q12) (S08-1-8) | docstring | `p3/evidence_C11/step4/C11_vs_baseline.diff` |

- L003 supersession: the L003 contract accepted the five S08-1-1 statements with Euler's selected zero; at the C11
  generation the `Selection` section holds only `instUAddCommGroup`, `instUZero`, `zero_selection_eq_existing` and the
  four operator identities, and under default instances `1 - PH H` still fails to elaborate (the L003 evidence is not
  rewritten).
- The new default-zero statements are syntactically equal to default-instance consumer statements only when
  `Rees.Laurent` is imported before `Applications.Fourier`; with the other order they stay instance-defeq and term, `rw`
  and `simp` uses succeed (critic F4).

### C12 — Taylor IVP, VectorField, Galerkin face, with the C3 addendum (`Applications/IVP/{VectorField,Taylor/*}`, `Algebra/Polynomial/CompPoly/{Derivative,WeightedL1}`, `Applications/Galerkin/Face.lean`)

No public rename and no public retirement. The C8 row S05-20 (`composedApprox_toCLM_eq_lift`) now has its consumer:
`IVP.ivp_Z₀_le` is rewired through it (S09-1-10/-11; Codex F2 pairing closed).

#### Ledger (C12)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `MvPolyBridge.contDiff_evalBanach` (paper-cited), `MvPolyBridge.differentiable_evalBanach` | unchanged FQN, type, levels and axioms; `CompPoly/WeightedL1.lean` → `CompPoly/Derivative.lean` (C3 addendum) | moved | `p3/evidence_C12/step2/MOVED_AND_CITED_CHECK.txt` |
| `IVP.differentiable_vectorField`, `IVP.differentiable_vectorField_pi`, `IVP.exists_lipschitz_vectorField_closedBall` | unchanged FQN and type; `Taylor/Trajectory.lean` → `VectorField.lean` (S09-1-1); `exists_lipschitz_vectorField_closedBall` is now proved with a syntactic constant, no compactness (S09-1-2) | moved | idem |
| `IVP.lipschitzOnWith_vectorField_closedBall` | unchanged FQN; same move; binder macro-scope module name only (S09-1-1) | moved | idem |
| `IVP.contDiff_vectorField`, `IVP.contDiff_vectorField_pi` | unchanged FQN; same move; in VectorField's import context `NormedSpace ℝ ℝ` elaborates through `NormedField.toNormedSpace` instead of the `InnerProductSpace`/`RCLike` path; equal to the old types by `with_reducible_and_instances rfl`; 0 consumers (S09-1-1; DECISIONS ~20:45Z ruling 1) | migrated instance path | `p3/evidence_C12/probes/MovedTypePins.lean`; `p3/evidence_C12/probes/MovedTypePins.out` |
| private `IVP.Z₁_component_le` (Taylor/Operator) | `IVP.ivp_Z₁_le_exact`; `IVP.ivp_Z₁_le` is its recipe instance (`C = ν/(N+1)·K` via `shiftDivN_tailTsum_le_div`) (S09-1-5) | retired (private) | `p3/evidence_C12/step2/STRICT_COMPARE.md` |
| private section `l1Weighted.norm_shiftDivN_CLM_le` (Taylor/Operator) | none (0 references) (S09-1-4) | retired (private) | idem |
| `RadiiPolynomial.Galerkin.I`, `RadiiPolynomial.Galerkin.Pi'` | type exact; bodies `ContinuousLinearMap.piMap fun _ => ιN.toContinuousLinearMap` / `ContinuousLinearMap.piMap fun _ => πN` (S09-1-13) | redefined | `p3/evidence_C12/probes/FaceReduction.out`; `p3/evidence_C12/probes/RB_Ch02Sec4_FisherGate.out` |
| `IVP.ivp_Z₁_le` (paper), `IVP.ivp_Y₀_le`, `IVP.StdIVPData.existsUnique_ivpCoeffs` (paper), `IVP.ivp_Z₀_le` (through `composedApprox_toCLM_eq_lift`), `IVP.analytic_solution_unique`, `IVP.StdIVPData.analytic_uniqueness_wrapper`, `IVP.StdIVPData.x_analytic_isAnalyticSolution` | types exact; re-proved (S09-1-5, S09-1-10/-11, S09-1-12, S09-2-23/-25/-26) | proof only | `p3/evidence_C12/step2/STRICT_COMPARE.md`; `p3/evidence_C12/probes/OldContextPins.out` |
| Taylor Operator (29) and Jacobian (12) non-internal rows | NeZero hygiene: every hand-written declaration exact; the matchers `IVP.ivpCoeffs.match_1`, `IVP.ivp_DF_of_Dφ_nat.match_1`, `IVP.ivp_hDF_block.match_1_1` differ by macro scope only (S09-1-7/-8) | hygiene | idem |
| `Applications/IVP/VectorField.lean`, `CompPoly/WeightedL1.lean`, `Taylor/Trajectory.lean`, `Taylor/ComplexTime.lean` imports | VectorField imports `CompPoly/{Core,Bounds,Derivative}` (closure +364 modules, still free of the ℓ¹ carriers); CompPoly/WeightedL1 imports `CompPoly/Derivative`; Trajectory drops `CompPoly.Bounds` and `Mathlib.Analysis.Calculus.ContDiff.RCLike`; ComplexTime drops its direct `Geometric.Analytic` | import change | `p3/evidence_C12/probes/CLOSURE_DELTAS.txt` |

- Measured and rejected: `import Mathlib.Analysis.InnerProductSpace.Basic` in VectorField restores the old instance path
  at +77 modules of closure (`p3/evidence_C12/probes/RemedyInnerProductImport.out`).

### C13 — Chebyshev IVP (`Applications/IVP/Chebyshev/*`)

Triage rows S09-2-2 … S09-2-21, S07-1-9 (boundary half), S09-3-1 … S09-3-7. The 13 public retirements match the
replacement table; every retired name has 0 ReferenceBook uses.

#### Ledger (C13)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `ChebyshevIVP.chebyshevShiftDiv_seq_zero` | `ChebyshevIVP.chebyshevShiftDiv_toSeq_zero` (S09-2-2) | retired | `p3/evidence_C13/step2/COMPARE_C13.md`; `p3/evidence_C13/probes/C13Pins.lean` |
| `ChebyshevIVP.chebyshevShiftDiv_seq_neg` | `ChebyshevIVP.chebyshevShiftDiv_toSeq_negSucc` (S09-2-2) | retired | idem |
| `ChebyshevIVP.chebyshevShiftDiv_seq_pos` | `ChebyshevIVP.chebyshevShiftDiv_toSeq_natCast` (S09-2-2) | retired | idem |
| `ChebyshevIVP.chebyshevShiftDiv_toSeq` (was `@[simp]`; RHS private) | the three `chebyshevShiftDiv_toSeq_*` faces (not simp) (S09-2-2) | retired | idem |
| `ChebyshevIVP.chebyshevIvpTail` | `StdChebIVPData.G_decomp` / `hasFDerivAt_G` / `fderiv_G` with `TCtail` (S09-2-3) | retired | idem |
| `ChebyshevIVP.differentiable_chebyshevIvpTail` | `StdChebIVPData.differentiable_G` (S09-2-3) | retired | idem |
| `ChebyshevIVP.fderiv_chebyshevIvpTail` | `StdChebIVPData.fderiv_G` (S09-2-3) | retired | idem |
| `ChebyshevIVP.summable_abs_toSeq` | `RadiiPolynomial.lpOneAlg.summable_abs_toRealSeq` (S09-2-5) | retired | idem |
| `ChebyshevIVP.summable_alternating_toSeq` | `l1Chebyshev.summable_eval (t := -1)` / `lpOneAlg.summable_abs_toRealSeq` (S09-2-5) | retired | idem |
| `ChebyshevIVP.tsum_abs_shift_le_norm` | `l1Chebyshev.abs_eval_le_two_mul_norm` (row 0 = evaluation) (S09-2-16) | retired | idem |
| `ChebyshevIVP.TCtailSeq` | `lpOneAlg.tailProj (Finset.Icc 0 N)` after `chebyshevShiftDiv` (= `TCtailElem`) (S09-2-17) | retired | idem |
| `ChebyshevIVP.lpOneAlg.norm_eq_natFinSum_of_finSupp` (BlockDiagonal copy) | `RadiiPolynomial.lpOneAlg.norm_eq_natFinSum_of_finSupp` (Carrier, generic fibers; added by C4) (S09-2-12) | retired | idem |
| `ChebyshevIVP.l1Chebyshev_finSum_le_norm` | `RadiiPolynomial.l1Chebyshev.finSum_le_norm` (added by C10-B/C) (S09-2-13) | retired | idem |
| `ChebyshevIVP.TCtailElem_norm_le_tail` | unchanged FQN, type and binder order; `Certification/IVP/Chebyshev.lean` → `Applications/IVP/Chebyshev/Lambda.lean` (S09-2-18, S10-2-2/-3) | moved | `p3/evidence_C13/step2/CERT_L2_vs_C14repair.md` |
| — | `ChebyshevIVP.chebyshevShiftDiv_toSeq_zero`, `…_toSeq_negSucc`, `…_toSeq_natCast` (S09-2-2) | added | `p3/evidence_C13/step2/COMPARE_C13.md` |
| — | `ChebyshevIVP.semiMajor_div_le_div` (inline proof; no `CrossGeometry.semiMajor_le_self`, no Joukowski import) (S09-2-4) | added | idem |
| — | `ChebyshevIVP.FAseq_zero_eq_eval` (no `Fact` binder), `ChebyshevIVP.chebyshevIvpCoeffs_zero_eq_eval` (S09-2-16) | added | idem |
| — | `ChebyshevIVP.defectCheb_apply_toSeq_natCast` / `_negSucc`, `ChebyshevIVP.composedApproxCheb_toSeq_natCast` / `_negSucc` (S09-2-10) | added | idem |
| — | `ChebyshevIVP.composedApproxCheb_eq_id_sub` (S09-2-11) | added | idem |
| — | `ChebyshevIVP.compPolyDerivative_apply` (not simp) (S09-3-6) | added | idem |
| — | `@[simp] ChebyshevIVP.liftDefect_eq_defectCheb_apply` (BlockDiagonal; the XCheb instance field is `defectCheb_apply`, so `simp` normalizes `composedApproxCheb D h` to `h - defectCheb_apply D h`) (critic F1, ruling 1a) | added | `p3/evidence_C13/CRITIC_C13.md`; `DECISIONS.md` |
| `ChebyshevIVP.chebyshevShiftDiv` | type exact; body `-(uIntegrate (chebyshevToU c))`; `chebyshevShiftDiv_eq_neg_uIntegrate_chebyshevToU` is now `rfl` (S09-2-2) | redefined | `p3/evidence_C13/probes/C13Pins.lean` |
| `ChebyshevIVP.chebyshevShiftDiv_CLM` | type exact; body `-(uIntegrate_CLM.comp chebyshevToU_CLM)` (S09-2-2) | redefined | idem |
| `ChebyshevIVP.composedApproxCheb` | `def` → `abbrev … := BlockDiagLift.composedApproxCLM (X := XCheb ν L) D`; reducibility default → reducible (S09-2-9) | metadata | idem |
| `ChebyshevIVP.defectCheb_apply`, `ChebyshevIVP.instBlockDiagLiftXCheb` | types exact; the XL1 lift (`ofCoeff ∘ actionFinite ∘ toCoeff`) of `OneSided.restr`, re-embedded by `natEmbed`; `defectCheb_apply` stays `NeZero`-free (S09-2-13; DECISIONS ~03:05Z ruling 2) | redefined | idem |
| `ChebyshevIVP.TCtailElem`, `ChebyshevIVP.TCtail` | types exact; `tailProj (Icc 0 N) ∘ chebyshevShiftDiv`; `TCtail = pi (tailProj ∘L chebyshevShiftDiv_CLM ∘L proj)` (S09-2-17) | redefined | idem |
| `IVP.chebyshevBoundary` | type exact; body `l1Chebyshev.evalAtCLM (-1) _`; `chebyshevBoundary_apply` still `rfl` (S07-1-9) | redefined | idem; `p3/evidence_C13/probes/RB_A6_copy_narrowImports.out` |
| `ChebyshevIVP.defectChebCLM`, `ChebyshevIVP.embedNatToInt`, `ChebyshevIVP.embedWithPassThrough`, `IVP.chebyshevIntegrateCLM`, `IVP.chebyshevSplitBoundary`, `IVP.symmetricEndpointCharacter` | types exact; values changed with the bodies above, each pinned (`rfl` or ext against the verbatim old body) | redefined | `p3/evidence_C13/CRITIC_C13.md` |
| private `chebyshevShiftDiv_seq`, `_fiber_le`, `_memℓp`, `_elem_le`; `l1Chebyshev_norm_eq_nat_tailTsum`; `summable_abs_shift`; `TCtailSeq_le`, `TCtail_memℓp`, `TCtailElem_add` / `_smul`, `TCtailFun_norm_le`; `defectCheb_seq`, `defectCheb_memℓp`; `composedApprox_lm`, `composedApprox_bound` (BlockDiagonal); Trajectory `norm_term_le`, `summable_of_bounded` | the faces above; the Carrier `ℤ`-split; `l1Chebyshev.norm_toSeq_mul_le` / `summable_toSeq_mul_of_abs_le_one` (S09-2-2/-4/-9/-13/-16/-17/-21) | retired (private) | `p3/evidence_C13/step2/COMPARE_C13.md` |
| private `ChebyshevIVP.action_chebyshev_tail_eq` (Operator) | RHS now `toSeq (chebyshevShiftDiv (φ a l)) n` (was the private sequence) (S09-2-2) | statement changed (private) | `p3/evidence_C13/CRITIC_C13.md` |
| — | private `toCoeff_restr` (BlockDiagonal) (S09-2-13) | added (private) | `p3/evidence_C13/step2/COMPARE_C13.md` |
| `Applications/IVP/Chebyshev/{BlockDiagonal,Lambda}.lean` imports | BlockDiagonal → `Chebyshev/OneSided`; Lambda → `WeightedL1/Diagonal`; Operator has no Joukowski edge (closure 23 → 23) | import change | `p3/evidence_C13/step3/CLOSURE_before_after.tsv` |

- `chebyshevShiftDiv_tailTsum_le_div` and `_le_half` keep their public faces with 0 consumers (DECISIONS ~03:05Z
  ruling 4); the S07-1-7 Boundary half is held (KEEP; ruling 7).
- Eighteen type-changed auxiliaries (`TCtail._proof_2`, `chebyshevShiftDiv.eq_1`, `defectCheb_apply._proof_1`,
  `IVP.chebyshevBoundary._proof_1`, …; list in the critic) follow their parents and are not public API.

### C14 — Certification and tactics (`Certification/*`, NEW `Certification/Rational/Matrix.lean`, `Tactic/*`)

Triage rows S10-1-1/-2/-3/-5/-6/-9/-11/-12/-13/-14/-15/-17 and S10-2-1/-4/-8/-10/-11/-12/-13/-16/-17, with the two C13
Certification repairs. Not executed: S10-1-4 (KEEP, Codex Q6), S10-1-8 and S10-2-18 (DEFER-USER).

#### Ledger (C14)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `RadiiPolynomial.Z₂_blockNormQ` | `activeBlockNormQ L N blockCols ν tailBound (ν * 2) active` (S10-1-1) | retired | `p3/evidence_C14/probes/C14Pins.lean`; `p3/evidence_C14/step2/cmpA/STRICT_COMPARE.md` |
| `RadiiPolynomial.Z₂_blockNorm_component_le` | `activeBlockNorm_component_le … (C_q := ν_q * 2)` (S10-1-1) | retired | idem |
| `RadiiPolynomial.Z₂_blockNormQ_eq` | definitional (`ring`); re-derived in the pins (S10-1-1) | retired | idem |
| `IVP.StdIVPDataQ.checksZ₂_iff_blockNormQ_gen` | none needed: `ChecksZ₂` is stated with `activeBlockNormQ` directly (S10-1-2) | retired | idem |
| `RadiiPolynomial.Z₂_blockNormQ_gen` | `activeBlockNormQ … (ν * C_q) active` (S10-1-3) | retired | idem |
| `RadiiPolynomial.Z₂_blockNormQ_gen_eq` | `ring` identity; re-derived in the pins (S10-1-3) | retired | idem |
| `RadiiPolynomial.Z₂_blockNorm_component_le_gen` | `activeBlockNorm_component_le … (C_q := ν_q * C_q)` (S10-1-3) | retired | idem |
| `RadiiPolynomial.Certification.Rational.foldlB_length` | `foldl_length (β := PM)` (S10-1-14) | retired | idem |
| `RadiiPolynomial.Certification.Rational.foldl_length` | unchanged FQN; generic in `{β ι : Type*}` (was `List QF`); the old statement is the instance `@foldl_length QF` (pin `pin_foldl_length_old`) (S10-1-14) | generalization | `p3/evidence_C14/probes/C14Pins.lean`; `p3/evidence_C14/CRITIC_C14.md` |
| `ChebyshevIVP.clm_apply_eq_sum` | unchanged FQN; any semiring, finite index, topological modules; `[Fact (1 ≤ ν)]` dropped; component form of Mathlib `ContinuousLinearMap.sum_comp_single` (pin `pin_clm_apply_eq_sum_old`) (S10-2-4) | weakening | `p3/evidence_C14/step2/cmpB/STRICT_COMPARE.md`; `p3/evidence_C14/probes/C14Pins.lean` |
| `RadiiPolynomial.matOfCols`, `.defectMatQ`, `.defectMatQ_correct`, `.blockDefectMatQ`, `.blockDefectMatQ_correct`, `.defectCols`, `.colNormQ`, `.finWeightedMatrixNormQ`, `.FiniteWeightedNorm.finWeightedMatrixNorm_le_of_Q_le`, `.finiteBlockMatrixNormQ`, `.activeBlockNormQ`, `.activeBlockNorm_component_le`, `.finiteBlockMatrixNorm_le_of_Q_le`, `.finiteBlockMatrixNorm_defect_le_of_Q`, `.norm_toCLM_le_of_Q`, `.norm_toScalarCLM_le_of_Q`, `.scalarBlockDiagAction`, `.ScalarBlockDiagData.toScalarCLM_toSeq_eq_action` (18 exact-ℚ declarations) | unchanged FQN; `Certification/LeanCertAdapter.lean` → `Certification/Rational/Matrix.lean`; 28 move rows exact or hygiene (S10-1-13) | moved | `p3/evidence_C14/step2/cmpA/STRICT_COMPARE.md`; `p3/evidence_C14/step3/LEANCERT_ENV_final.tsv` |
| `RadiiPolynomial.Certification.Rational.getD_ofFn_fin` | unchanged FQN; `Rational/Grid.lean` → `Rational/Matrix.lean` (S10-1-13) | moved | `p3/evidence_C14/step2/cmpA/STRICT_COMPARE.md` |
| — | `RadiiPolynomial.blockActionQ` (shared Taylor/Chebyshev action) and `RadiiPolynomial.SystemBlockDiagData.action_eq_blockActionQ` (Rational/Matrix); both `action_eq_actionQ` are corollaries, statements exact (S10-1-9) | added | idem |
| — | `RadiiPolynomial.l1Weighted.norm_eq_ratCast_sum_of_support` (Witness); `IVP.StdIVPData.norm_abar_eq`, `norm_evalBanach_abar_eq`, `PolyZeroData.norm_xbar` are corollaries (S10-1-11) | added | idem |
| syntax node kinds `LeanCert.Tactic.finMatrixBound`, `LeanCert.Tactic.finMatrixDyadic` | `RadiiPolynomial.Tactic.finMatrixBound`, `RadiiPolynomial.Tactic.finMatrixDyadic`; tokens `finmatrix_bound` / `finmatrix_dyadic` unchanged; elaborators registered only at the new kinds (S10-2-17) | renamed (no alias) | `p3/evidence_C14/probes/C14Pins.lean` |
| private `Example81.Cert.dataQ`, private `Example83.Cert.dataQ` | body `IVP.StdIVPDataQ.ofStd data`, equal to the old literal by `rfl`; Ex83 `dataQ` now noncomputable (section marker; `decide +kernel` re-checked) (S10-1-6) | redefined | `p3/evidence_C14/step2/INVENTORY_diff.txt` |
| Taylor `radii_sound`, PolynomialZero `certified`, Chebyshev `certified_of_Y₀Z₀`; `IVP.StdIVPData.norm_abar_eq`, `norm_evalBanach_abar_eq`, `PolyZeroData.norm_xbar`; both `action_eq_actionQ`; `ChebyshevIVP.StdChebIVPData.composed_toSeq_nat` / `_neg` (C13 repair) | statements exact; re-proved (S10-1-9/-11/-12; C13 repair 2) | proof only | `p3/evidence_C14/step2/cmpA/STRICT_COMPARE.md`; `p3/evidence_C14/step2/cmpB/STRICT_COMPARE.md` |
| `Certification/{Rational/Grid,LeanCertAdapter,IVP/Taylor,IVP/Chebyshev,PowerSeries/PolynomialZero}.lean`, facade `Certification.lean`; Ex83 Algebra | Grid, LeanCertAdapter, the three family faces and the facade import `Rational/Matrix`; `Certification/IVP/Chebyshev` imports `Applications.IVP.Chebyshev.Polynomial`, not the facade (closure 73 → 53) (S10-2-1); Ex83 drops its `PDerivSimp` import (S10-2-12) | import change | `p3/evidence_C14/step3/CLOSURE_final.tsv` |
| `Certification.lean`, `Rational/Matrix`, `LeanCertAdapter`, `Tactic/{PDerivSimp,MakeCompPoly,AutoPolyFDeriv}` docs | facade doc names `Rational.Matrix` and says the family faces are not in the facade (S10-2-8); native prose reworded (Codex Q7); `PDerivSimp` gains a `tests` section and role/side-effect docs (S10-2-10/-11); MakeCompPoly prose (S10-2-13); AutoPolyFDeriv doc points to Mathlib `differentiable_apply` (S10-2-16); S10-1-5/-15/-17 docstrings | docstring | `p3/evidence_C14/step4/C14_vs_baseline.diff` |

- `IVP.tail_shiftDivN_sum_le` (deprecated alias, `RENAMES.md`:676) is kept (S10-1-4, Codex Q6).
- C14 renamed no native auxiliary axiom: `#print axioms` of every endpoint is byte-identical before and after
  (`p3/evidence_C14/step2/endpoint_axioms_final.out`).
- Tests `TY/AllGenerated` and `TC/FinMatrixBound` are handed to C15 (`p3/evidence_C14/TESTS_HANDOFF_C14.md`).

### C14b — CONS-E extension of C14 (`Certification/IVP/{Taylor,Chebyshev}.lean`, Ex81/Ex83 Algebra and Certificate, Ex1421 Certificate)

Triage rows CONS-E-1, -2, -3, -11, -12 (:257), -13, -14 (Codex Q1 ownership).

#### Ledger (C14b)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| — | `ChebyshevIVP.StdChebIVPData.Z₁_le_semiMajor_of_Q` (Certification/IVP/Chebyshev, after `Z₁_le_of_Q`): total `ε + (ν_q⁻¹ + ν_q)/(2(N+1))·K ≤ Z₁` via `chebyshev_Z₁_le_semiMajor`; the relaxed sibling is kept (CONS-E-1) | added | `p3/evidence_C14b/step3/ctrl1421_semimajor.out`; `p3/evidence_C14b/CRITIC_C14b.md` |
| — | `ChebyshevIVP.StdChebIVPData.Z₁_le_semiMajor_of_checksK` (after `Z₁_le_of_checksK`): the `R`/`K`/`ε` conjuncts of `ChecksK` and a separate semi-major total `hZ₁`; no `p = p_q` hypothesis (CONS-E-1) | added | idem |
| — | `IVP.StdIVPData.ivpCoeffs_abar_eq_zero_of_compPoly` (Certification/IVP/Taylor, after `ivpCoeffsQ_support`): for any real `x₀`, `F(ā)_{l,n} = 0` when `supportM f_cpoly N < n` (CONS-E-2) | added | `p3/evidence_C14b/probes/CtrlTaylorSupport.lean`; `p3/evidence_C14b/step3/ctrl_taylor_support.out` |
| — | `IVP.StdIVPData.ivpCoeffs_abar_mem_of_compPoly`: `l1Weighted.Mem ν (F(ā)_l)` for every real `x₀` (CONS-E-2) | added | idem |
| `Example81.f_abar_support`, `Example81.F_abar_support`, `Example81.F_abar_mem`, `Example83.f_abar_support`, `Example83.F_abar_support`, `Example83.F_abar_mem` | statements, bounds and FQNs exact; one call of the Taylor faces each (CONS-E-2) | proof only | `p3/evidence_C14b/step4/C14b_vs_baseline.diff` |
| private `Example81.abar_toSeq_zero`, private `Example83.abar_toSeq_zero` | through `abar_Q_getD_eq_zero` (CONS-E-2) | proof only | idem |
| — | private `Example81.supportM_eq`, private `Example83.supportM_eq`: `IVP.supportM f_cpoly N = 2 * N + 1` by kernel `decide` (CONS-E-2) | added (private) | idem |
| private `Example81.Cert.F_abar`, `.G_eq_toCLM_F_abar`, `.F_abar_toCoeff_support`; private `Example83.Cert.F_abar`, `.G_eq_toCLM_F_abar`, `.F_abar_toCoeff_support` | none (0 consumers); `Y₀_le` goes through `IVP.ivp_Y₀_le`; statements re-derived from the faces (CONS-E-3) | retired (private) | `p3/evidence_C14b/probes/CtrlTaylorSupport.lean` |
| `Example81.Cert.Y₀_le`, `Example83.Cert.Y₀_le` (paper-cited) | statements exact; `finsum_bound` route kept; native auxiliary names shift (trust record below) (CONS-E-3) | proof only | `p3/evidence_C14b/step2/NATIVE_AXIOM_CORRESPONDENCE.md` |
| `Example1421.Cert.Z₁_le_semiMajor` (paper-cited, main.tex:1439) | statement exact, axioms the standard three; one call of `Z₁_le_semiMajor_of_checksK` (CONS-E-1) | proof only | `p3/evidence_C14b/step3/ctrl1421_semimajor.out` |
| Cert/IVP/Chebyshev and Ex81/Ex83/Ex1421 docs | "Audit cross-check (not consumed by the certificate)" (CONS-E-11); ":257 Additive" removed (CONS-E-12); `project_ivp_codomain_design` pointers removed (CONS-E-13); diary phrases removed (CONS-E-14) | docstring | `p3/evidence_C14b/step4/C14b_vs_baseline.diff` |

- `Example81.F.eq_1` and `Example83.F.eq_1` are no longer pregenerated in the Algebra modules; they are realized on first
  use with the baseline statement (`p3/evidence_C14b/probes/CtrlTaylorSupport.lean`).

#### Trust record — native auxiliary renames (C14b; not public API, Codex)

| old auxiliary | new auxiliary | kind | evidence |
|---|---|---|---|
| `Example81.Cert.Y₀_le._native.native_decide.ax_1_3` | `….ax_1_2` (identical proposition: `c = 0`, `R = 2*10+1`, `B = 3/1000000`) | native auxiliary rename | `p3/evidence_C14b/step2/NATIVE_AXIOM_CORRESPONDENCE.md` |
| `Example83.Cert.Y₀_le._native.native_decide.ax_1_3`, `ax_1_4`, `ax_1_5` | `ax_1_2`, `ax_1_3`, `ax_1_4` (identical propositions: components 0, 1, 2; `R = 2*30+1`, `B = 11/25000`) | native auxiliary rename | idem |

- Matching is by raw `Expr` (13 ↔ 13, nothing unmatched); endpoint native counts are unchanged (Ex81 1/1/1, Ex83 3/7/7,
  Ex1421 0) and agree with paper main.tex:1268–1270.

### C7 addendum (S10-2-14) — `Tactic/AutoPolyFDeriv.lean` → `Analysis/SequenceSpace/Geometric/Basic.lean`

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `RadiiPolynomial.l1Weighted.smul_proj_eq_leftMul_comp_proj` (`@[simp]`) | unchanged FQN and type; `Tactic/AutoPolyFDeriv.lean` → `Geometric/Basic.lean`, beside `smul_id_eq_leftMul` (section BanachAlgebra); `@[simp]` dropped; both tactic macros name it explicitly | moved; de-simp | `p3/evidence_C7addendum/REPORT_C7addendum.md`; `p3/evidence_C7addendum/Probe_simp.lean` |

### C6 tail (S00-16) — `Analysis/Calculus/Pi.lean`

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `differentiable_pi_apply` (root) | Mathlib `@[fun_prop] differentiable_apply` (dependent Pi, strictly more general); 0 consumers in the Lake root and ReferenceBook | retired | `p3/evidence_C6/RENAMES_C6.md`; `DECISIONS.md` |

### Supersessions of earlier rows (history kept)

- C6 (cohort A): the bullet "`differentiable_pi_apply` is KEPT" is superseded by the C6 tail above.
- C8 (cohort B): the S05-20 condition on C12 is met (C12 above); the row and the paragraph carry a pointer here.
- C9-A, C9-B (cohort B): the forward pointers to C10 phase C and to the S00-16 retirement are resolved (C10-B/C,
  C6 tail above).

### C15 (tests; CONS-T T-2/T-3/T-4, S10-1-7, S10-2-19)

| old | new | kind | evidence |
|---|---|---|---|
| `RadiiPolynomial/Examples/tests/FiberTrivializationProbes.lean` (module `RadiiPolynomial.Examples.tests.FiberTrivializationProbes`, namespace `RadiiPolynomial.FiberTrivializationProbes`) | `RadiiPolynomial/Examples/tests/FT/FiberTrivializationProbes.lean` (module `….tests.FT.FiberTrivializationProbes`, namespace `RadiiPolynomial.Tests.FT`) | test path move + re-namespace (T-4); 0 consumers; the accepted adoption bytes (sha 8c125247…) are preserved at `exterior/tmp/api_campaign_20261012/p3/evidence_C15/T4_snapshot/` | `p3/evidence_C15/RENAMES_C15.md` |
| — | `RadiiPolynomial/Examples/tests/TY/AllGenerated.lean`, `RadiiPolynomial/Examples/tests/TC/FinMatrixBound.lean` | new test modules (S10-1-7, S10-2-19) | `p3/evidence_C15/TESTS_REPORT_C15.md` |
| `tests/CV/PowerSeriesBridge` §5 `#print axioms` records | the same records under `#guard_msgs` (T-3) | test strengthening | `p3/evidence_C15/TESTS_REPORT_C15.md` |

## API campaign 2026-10-12 — DEFER round (user decisions 1–8; 2026-10-13/14)

The eight rows that the campaign deferred to the user (`DEFER_USER.md`) were decided on 2026-10-13 ("baaaaaba",
`DECISIONS.md` ~19:50Z) and executed as units D1, D2, E1, E2 and E1b, each accepted by its independent critic with
the critic's fixes applied (`DECISIONS.md`, entries ~22:25Z on 10-13 to ~04:55Z on 10-14). Coordinator rulings in
`DECISIONS.md` override fragment text where they differ.

| # | decision | executed by |
|---|---|---|
| 1 | (b) rename `CauchyProduct` → `cauchyProduct` with its derived names; no alias; paper erratum at the next paper pass | D1 item 1 |
| 2 | (a) re-index the weighted ℓ¹ API by the chosen frame `FiberTrivialization 𝕜 M E`; the legacy fiber classes are deleted | E1 (station), E2 (consumers), E1b (station API quality); design `ft_reindex/CONSENSUS_ft_reindex.md` v2 FINAL |
| 3 | (a) move the root declarations of `Core/Theorem.lean` under `RadiiPolynomial.` | D2 |
| 4 | (a) wrap `Geometric/Evaluation.lean` and `Geometric/EvaluationDerivative.lean` in `namespace RadiiPolynomial` | D1 item 4 |
| 5 | (a) rename `IVP.IsAnalyticSolution` → `IVP.IsBallSolution`; no alias | D1 item 5 |
| 6 | (a) keep the Ex81 production `Y₀` route | no change |
| 7 | (b) `Tactic/FinMatrixBound.lean` gets the project header | D1 item 7 (header comment only) |
| 8 | (a) Ex83 feeds `Z₁_le_of_compPoly` with the `fderiv` `Df`; the component-derivative lemmas are deleted | D1 item 8 |

Standing rules of the round (user, 2026-10-13): rapid development, no backward support ("Don't worry about
backwards support we are at rapid dev", ~20:58Z), and no mercy ("if the refactor deprecate some other older modules
have no mercy deleting em", ~21:40Z). No alias, no `deprecated` attribute and no compatibility shim was added; every
retired name has its replacement in the ledgers below.

Ledger columns: old FQN | new FQN or replacement | kind | evidence. Kinds as in the cohorts B (round 2) and C section,
plus `moved (namespace)` (same module; the FQN gains `RadiiPolynomial.`), `migrated (frame re-index)` (one row per
family; its printed statement changes follow as `↳` sub-rows), `restored` and `aux regenerated`. Regenerated
auxiliaries are named only in notes. Names in the E1, E1b and E2 ledgers are relative to `RadiiPolynomial.` unless they
start with `ChebyshevIVP.` or `RadiiPolynomial.`.

Evidence paths starting with `p3/`, `ft_reindex/` or `rb_round/` are relative to `exterior/tmp/api_campaign_20261012/`
in the outer repository, outside the Lake root; `DECISIONS.md` and `DEFER_USER.md` are that directory's logs.

ReferenceBook and paper: no ReferenceBook source or paper file is edited by the campaign. Unlike the earlier sections,
the ReferenceBook does use many of the names below; the cumulative migration recipe with its scratch replay is
`rb_round/RB_MIGRATION_ROUND.md` (the Paper session's round). Paper errata (decisions 1, 2, 5 and 8) are in
`p3/evidence_D1/PAPER_NOTES_D1.md` and `p3/evidence_E1/PAPER_NOTES_E1.md`; decision 3 needs none (printed short names).

### D1 — decisions 7, 4, 5, 8, 1 (`Tactic/FinMatrixBound.lean`, `Geometric/Evaluation*`, `Applications/IVP/Taylor/Analytic.lean`, Ex81/Ex83, `Algebra/Convolution/*`)

Unit D1 (`p3/evidence_D1/REPORT_D1_handback.md`, `p3/evidence_D1/CRITIC_D1.md`: own whole-library compare, 39 moves,
14 + 51 renames exact, Ex83 deletions with 0 consumers, endpoint axioms identical).

#### Ledger (D1)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `Tactic/FinMatrixBound.lean` header ("Copyright (c) 2026 LeanCert Contributors …") | the project header of `Tactic/MakeCompPoly.lean` (RadiiPolynomial contributors, Apache 2.0); no constant changes (decision 7) | header comment | `p3/evidence_D1/item7/cmp/STRICT_COMPARE.md` |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.l1Weighted.evalAlgHom'` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.evalAlgHom'` (private def) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.l1Weighted.evalAlgHom'._proof_1` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.evalAlgHom'._proof_1` (private theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.l1Weighted.evalAlgHom'._proof_2` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.evalAlgHom'._proof_2` (private theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.l1Weighted.evalAlgHom'._proof_3` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.evalAlgHom'._proof_3` (private theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.l1Weighted.evalAlgHom'._proof_4` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.evalAlgHom'._proof_4` (private theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.l1Weighted.evalCLM` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.evalCLM` (private def) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.l1Weighted.evalCLM._proof_1` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.evalCLM._proof_1` (private theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.l1Weighted.evalCLM._proof_2` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.evalCLM._proof_2` (private theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.l1Weighted.evalCLM_apply` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.evalCLM_apply` (private theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.l1Weighted.norm_term_le` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.norm_term_le` (private theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.l1Weighted.seq` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.seq` (private def) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.l1Weighted.summable_norm_eval` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.summable_norm_eval` (private theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.EvaluationDerivative.0.l1Weighted.seq` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.EvaluationDerivative.0.RadiiPolynomial.l1Weighted.seq` (private def) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.abs_eval_le` | `RadiiPolynomial.l1Weighted.abs_eval_le` (theorem; paper: printed spelling unchanged) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.continuous_eval` | `RadiiPolynomial.l1Weighted.continuous_eval` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval` | `RadiiPolynomial.l1Weighted.eval` (def; paper: printed `l1Weighted.eval` (resolves unchanged)) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.evalAlgHom` | `RadiiPolynomial.l1Weighted.evalAlgHom` (def) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.evalAlgHom_apply` | `RadiiPolynomial.l1Weighted.evalAlgHom_apply` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.evalContinuousAlgHom` | `RadiiPolynomial.l1Weighted.evalContinuousAlgHom` (def; paper: printed spelling unchanged) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.evalContinuousAlgHom.congr_simp` | `RadiiPolynomial.l1Weighted.evalContinuousAlgHom.congr_simp` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.evalContinuousAlgHom_apply` | `RadiiPolynomial.l1Weighted.evalContinuousAlgHom_apply` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval_CLM` | `RadiiPolynomial.l1Weighted.eval_CLM` (def) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval_CLM_apply` | `RadiiPolynomial.l1Weighted.eval_CLM_apply` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval_add` | `RadiiPolynomial.l1Weighted.eval_add` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval_at_zero` | `RadiiPolynomial.l1Weighted.eval_at_zero` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval_double_finset_sum` | `RadiiPolynomial.l1Weighted.eval_double_finset_sum` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval_finset_sum` | `RadiiPolynomial.l1Weighted.eval_finset_sum` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval_mul` | `RadiiPolynomial.l1Weighted.eval_mul` (theorem; paper: printed spelling unchanged) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval_mul_trunc` | `RadiiPolynomial.l1Weighted.eval_mul_trunc` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval_neg` | `RadiiPolynomial.l1Weighted.eval_neg` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval_one` | `RadiiPolynomial.l1Weighted.eval_one` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval_one._proof_1_1` | `RadiiPolynomial.l1Weighted.eval_one._proof_1_1` (internal theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval_single` | `RadiiPolynomial.l1Weighted.eval_single` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval_smul` | `RadiiPolynomial.l1Weighted.eval_smul` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval_sub` | `RadiiPolynomial.l1Weighted.eval_sub` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.eval_zero` | `RadiiPolynomial.l1Weighted.eval_zero` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.hasDerivAt_eval` | `RadiiPolynomial.l1Weighted.hasDerivAt_eval` (theorem; paper: printed spelling unchanged) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.hasDerivAt_eval_single` | `RadiiPolynomial.l1Weighted.hasDerivAt_eval_single` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `l1Weighted.summable_eval` | `RadiiPolynomial.l1Weighted.summable_eval` (theorem) | moved (namespace) | `p3/evidence_D1/item4/cmp/STRICT_COMPARE.md` |
| `Example81.Cert.x_analytic_isAnalyticSolution` | `Example81.Cert.x_analytic_isBallSolution` (theorem) | renamed (no alias) | `p3/evidence_D1/item5/cmp/STRICT_COMPARE.md` |
| `Example83.Cert.x_analytic_isAnalyticSolution` | `Example83.Cert.x_analytic_isBallSolution` (theorem) | renamed (no alias) | `p3/evidence_D1/item5/cmp/STRICT_COMPARE.md` |
| `IVP.IsAnalyticSolution` | `IVP.IsBallSolution` (inductive; paper main.tex:1354) | renamed (no alias) | `p3/evidence_D1/item5/cmp/STRICT_COMPARE.md` |
| `IVP.IsAnalyticSolution.casesOn` | `IVP.IsBallSolution.casesOn` (def) | renamed (no alias) | `p3/evidence_D1/item5/cmp/STRICT_COMPARE.md` |
| `IVP.IsAnalyticSolution.in_R` | `IVP.IsBallSolution.in_R` (theorem) | renamed (no alias) | `p3/evidence_D1/item5/cmp/STRICT_COMPARE.md` |
| `IVP.IsAnalyticSolution.init` | `IVP.IsBallSolution.init` (theorem) | renamed (no alias) | `p3/evidence_D1/item5/cmp/STRICT_COMPARE.md` |
| `IVP.IsAnalyticSolution.mk` | `IVP.IsBallSolution.mk` (ctor) | renamed (no alias) | `p3/evidence_D1/item5/cmp/STRICT_COMPARE.md` |
| `IVP.IsAnalyticSolution.mk._flat_ctor` | `IVP.IsBallSolution.mk._flat_ctor` (internal def) | renamed (no alias) | `p3/evidence_D1/item5/cmp/STRICT_COMPARE.md` |
| `IVP.IsAnalyticSolution.rec` | `IVP.IsBallSolution.rec` (rec) | renamed (no alias) | `p3/evidence_D1/item5/cmp/STRICT_COMPARE.md` |
| `IVP.IsAnalyticSolution.recOn` | `IVP.IsBallSolution.recOn` (def) | renamed (no alias) | `p3/evidence_D1/item5/cmp/STRICT_COMPARE.md` |
| `IVP.IsAnalyticSolution.solves` | `IVP.IsBallSolution.solves` (theorem) | renamed (no alias) | `p3/evidence_D1/item5/cmp/STRICT_COMPARE.md` |
| `IVP.StdIVPData.x_analytic_isAnalyticSolution` | `IVP.StdIVPData.x_analytic_isBallSolution` (theorem) | renamed (no alias) | `p3/evidence_D1/item5/cmp/STRICT_COMPARE.md` |
| `IVP.StdIVPData.x_analytic_isAnalyticSolution_of_compPoly` | `IVP.StdIVPData.x_analytic_isBallSolution_of_compPoly` (theorem) | renamed (no alias) | `p3/evidence_D1/item5/cmp/STRICT_COMPARE.md` |
| `IVP.StdIVPData.x_analytic_isAnalyticSolution_of_compPoly_of_radii` | `IVP.StdIVPData.x_analytic_isBallSolution_of_compPoly_of_radii` (theorem) | renamed (no alias) | `p3/evidence_D1/item5/cmp/STRICT_COMPARE.md` |
| `Example83.Df.eq_1` | the name is reused by the single equation lemma of the new `Df`, realized on first use | retired (aux) | `p3/evidence_D1/item8/cmp/STRICT_COMPARE.md` |
| `Example83.Df.eq_2` | `Example83.Df.eq_1` (the new `Df` has one equation) | retired (aux) | `p3/evidence_D1/item8/cmp/STRICT_COMPARE.md` |
| `Example83.Df.eq_3` | `Example83.Df.eq_1` (the new `Df` has one equation) | retired (aux) | `p3/evidence_D1/item8/cmp/STRICT_COMPARE.md` |
| `Example83.Df_eq_fderiv` | `rfl`: `Df h l` is by definition `fderiv ℝ (fun a => f a l) data.abar h` | retired | `p3/evidence_D1/item8/cmp/STRICT_COMPARE.md` |
| `Example83.fderiv_f_0` | none: `Df` is definitionally the `fderiv`, so the `Z₁` face hypothesis holds by `rfl` | retired | `p3/evidence_D1/item8/cmp/STRICT_COMPARE.md` |
| `Example83.fderiv_f_1` | none: `Df` is definitionally the `fderiv`, so the `Z₁` face hypothesis holds by `rfl` | retired | `p3/evidence_D1/item8/cmp/STRICT_COMPARE.md` |
| `Example83.fderiv_f_2` | none: `Df` is definitionally the `fderiv`, so the `Z₁` face hypothesis holds by `rfl` | retired | `p3/evidence_D1/item8/cmp/STRICT_COMPARE.md` |
| `_private.RadiiPolynomial.Examples.IVP.Taylor.Example83.Algebra.0.Example83.proj_L` | none (private abbrev used only by the deleted lemmas) | retired (private) | `p3/evidence_D1/item8/cmp/STRICT_COMPARE.md` |
| `Example83.Df` | type exact; value `fun h l => fderiv ℝ (fun a => f a l) data.abar h` (was the closed Lorenz-Jacobian formula); private `Example83.Cert.Df_norm_le` (paper-cited) keeps its statement, `main_theorem` and `ivp_main_theorem` are unchanged | redefined | `p3/evidence_D1/item8/cmp/STRICT_COMPARE.md`; `p3/evidence_D1/item8/ex83_axioms_after.out` |
| `Example83.σ_val` | none (definition with 0 uses; no-mercy rule) | retired | `p3/evidence_D1/CRITIC_D1.md` (F2); `DECISIONS.md` ~22:25Z ruling (c) |
| `Example83.ρ_val` | none (definition with 0 uses; no-mercy rule) | retired | `p3/evidence_D1/CRITIC_D1.md` (F2); `DECISIONS.md` ~22:25Z ruling (c) |
| `Example83.β_val` | none (definition with 0 uses; no-mercy rule) | retired | `p3/evidence_D1/CRITIC_D1.md` (F2); `DECISIONS.md` ~22:25Z ruling (c) |
| `import RadiiPolynomial.Tactic.AutoPolyFDeriv` in `Examples/IVP/Taylor/Example83/Algebra.lean` | dropped (unused after decision 8) | import change | `p3/evidence_D1/CRITIC_D1.md` (F2); `DECISIONS.md` ~22:25Z ruling (c) |
| `RadiiPolynomial.CauchyProduct` | `RadiiPolynomial.cauchyProduct` (def; paper main.tex:453, :469) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.apply` | `RadiiPolynomial.cauchyProduct.apply` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.apply_of_support_le_split` | `RadiiPolynomial.cauchyProduct.apply_of_support_le_split` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.apply_of_support_le_split._proof_1_1` | `RadiiPolynomial.cauchyProduct.apply_of_support_le_split._proof_1_1` (internal theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.apply_of_support_le_split._proof_1_4` | `RadiiPolynomial.cauchyProduct.apply_of_support_le_split._proof_1_4` (internal theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.apply_of_support_le_split._simp_1_2` | `RadiiPolynomial.cauchyProduct.apply_of_support_le_split._simp_1_2` (internal theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.apply_of_support_le_split._simp_1_3` | `RadiiPolynomial.cauchyProduct.apply_of_support_le_split._simp_1_3` (internal theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.apply_range` | `RadiiPolynomial.cauchyProduct.apply_range` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.assoc` | `RadiiPolynomial.cauchyProduct.assoc` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.coeff_toPowerSeries` | `RadiiPolynomial.cauchyProduct.coeff_toPowerSeries` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.coeff_toPowerSeriesLinearEquiv` | `RadiiPolynomial.cauchyProduct.coeff_toPowerSeriesLinearEquiv` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.comm` | `RadiiPolynomial.cauchyProduct.comm` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.delta_left` | `RadiiPolynomial.cauchyProduct.delta_left` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.delta_right` | `RadiiPolynomial.cauchyProduct.delta_right` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.eq_1` | `RadiiPolynomial.cauchyProduct.eq_1` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.eq_addRingConvolution` | `RadiiPolynomial.cauchyProduct.eq_addRingConvolution` (theorem; paper main.tex:469) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.eq_coeff_mul` | `RadiiPolynomial.cauchyProduct.eq_coeff_mul` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.eq_sum_fin` | `RadiiPolynomial.cauchyProduct.eq_sum_fin` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.eq_sum_fin._proof_1_3` | `RadiiPolynomial.cauchyProduct.eq_sum_fin._proof_1_3` (internal theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.eq_sum_fin._simp_1_1` | `RadiiPolynomial.cauchyProduct.eq_sum_fin._simp_1_1` (internal theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.eq_sum_fin._simp_1_2` | `RadiiPolynomial.cauchyProduct.eq_sum_fin._simp_1_2` (internal theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.left_distrib` | `RadiiPolynomial.cauchyProduct.left_distrib` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.map_CauchyProduct` | `RadiiPolynomial.cauchyProduct.map_cauchyProduct` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.mul_one` | `RadiiPolynomial.cauchyProduct.mul_one` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.mul_smul` | `RadiiPolynomial.cauchyProduct.mul_smul` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.mul_zero` | `RadiiPolynomial.cauchyProduct.mul_zero` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.one` | `RadiiPolynomial.cauchyProduct.one` (def; paper main.tex:657 (printed short name)) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.one_eq_single` | `RadiiPolynomial.cauchyProduct.one_eq_single` (theorem; paper main.tex:657 (printed short name, unchanged)) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.one_mul` | `RadiiPolynomial.cauchyProduct.one_mul` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.one_succ` | `RadiiPolynomial.cauchyProduct.one_succ` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.one_zero` | `RadiiPolynomial.cauchyProduct.one_zero` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.ratCast` | `RadiiPolynomial.cauchyProduct.ratCast` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.right_distrib` | `RadiiPolynomial.cauchyProduct.right_distrib` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.single_mul_single` | `RadiiPolynomial.cauchyProduct.single_mul_single` (theorem; paper main.tex:657 (printed short name, unchanged)) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.smul_mul` | `RadiiPolynomial.cauchyProduct.smul_mul` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.toPowerSeries` | `RadiiPolynomial.cauchyProduct.toPowerSeries` (def; paper main.tex:469, :834 (printed short name, unchanged)) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.toPowerSeries.eq_1` | `RadiiPolynomial.cauchyProduct.toPowerSeries.eq_1` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.toPowerSeriesLinearEquiv` | `RadiiPolynomial.cauchyProduct.toPowerSeriesLinearEquiv` (def) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.toPowerSeriesLinearEquiv_apply` | `RadiiPolynomial.cauchyProduct.toPowerSeriesLinearEquiv_apply` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.toPowerSeriesLinearEquiv_symm_apply` | `RadiiPolynomial.cauchyProduct.toPowerSeriesLinearEquiv_symm_apply` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.toPowerSeriesLinearEquiv_symm_apply_coeff` | `RadiiPolynomial.cauchyProduct.toPowerSeriesLinearEquiv_symm_apply_coeff` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.toPowerSeries_injective` | `RadiiPolynomial.cauchyProduct.toPowerSeries_injective` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.toPowerSeries_mul` | `RadiiPolynomial.cauchyProduct.toPowerSeries_mul` (theorem; paper main.tex:469, :834 (printed `toPowerSeries_mul`, unchanged)) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.toPowerSeries_one` | `RadiiPolynomial.cauchyProduct.toPowerSeries_one` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.toPowerSeries_single` | `RadiiPolynomial.cauchyProduct.toPowerSeries_single` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.zero_mul` | `RadiiPolynomial.cauchyProduct.zero_mul` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.zero_of_support` | `RadiiPolynomial.cauchyProduct.zero_of_support` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.zero_of_support._proof_1_3` | `RadiiPolynomial.cauchyProduct.zero_of_support._proof_1_3` (internal theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.zero_of_support.match_1_1` | `RadiiPolynomial.cauchyProduct.zero_of_support.match_1_1` (def) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct.«term_⋆_»` | `RadiiPolynomial.cauchyProduct.«term_⋆_»` (def) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |
| `RadiiPolynomial.CauchyProduct_eq_finiteAddConvolution` | `RadiiPolynomial.cauchyProduct_eq_finiteAddConvolution` (theorem) | renamed (no alias) | `p3/evidence_D1/item1/cmp/STRICT_COMPARE.md` |

- Decision 1: the module names `Algebra/Convolution/CauchyProduct` and `CauchyProductReal` are unchanged; the scoped
  notation `⋆` now lives in namespace `RadiiPolynomial.cauchyProduct`. The two notation auxiliaries (unexpander and
  macro rules, whose names embed the definition name) are regenerated under `RadiiPolynomial.cauchyProduct.` with
  values that differ only by the name literal (`p3/evidence_D1/CRITIC_D1.md` item 6). Mathlib and LeanCert declare no
  `cauchyProduct`.
- Decision 4: the printed spelling `l1Weighted.eval` and the paper text resolve unchanged inside `RadiiPolynomial`; the
  39th row (`evalContinuousAlgHom.congr_simp`) is generated in `Geometric/RadiusRestriction`.
- Decision 5: the derived conclusion names `x_analytic_isBallSolution*` were renamed with the predicate (ruling (a),
  `DECISIONS.md` ~22:25Z); eight docstrings say "ball solution" instead of "analytic solution" (critic F4).
- Decision 8: the reserved equation lemma `Example83.Df.eq_1` of the new one-equation `Df` is realized on first use.

### D2 — decision 3 (`Core/Theorem.lean`)

`Core/Theorem.lean` lies in one `namespace RadiiPolynomial`; statements, proofs, attributes and docstrings are
byte-identical, and all 228 Lake-root consumer hits already resolved through the namespace or an `open` (0 consumer
edits). Whole-library fingerprint (8756 constants) identical after mapping the moved names (`p3/evidence_D2/CRITIC_D2.md`).

#### Ledger (D2)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `I_E` | `RadiiPolynomial.I_E` (`abbrev`, section (file top, before NeumannSeries)) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `NewtonLikeMap` | `RadiiPolynomial.NewtonLikeMap` (`def`, section NewtonLikeOperator) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `NewtonLikeMap.differentiable` | `RadiiPolynomial.NewtonLikeMap.differentiable` (`lemma`, section NewtonLikeOperator) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `Z_bound` | `RadiiPolynomial.Z_bound` (`def`, section RadiiPolynomialDefinitions) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `Z_bound_general` | `RadiiPolynomial.Z_bound_general` (`def`, section RadiiPolynomialDefinitions) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `fixedPoint_injective_iff_zero` | `RadiiPolynomial.fixedPoint_injective_iff_zero` (`lemma`, section Proposition_2_3_1; paper main.tex:317 (printed short name, no erratum)) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `generalRadiiPolynomial` | `RadiiPolynomial.generalRadiiPolynomial` (`def`, section RadiiPolynomialDefinitions) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `generalRadiiPolynomial_alt_form` | `RadiiPolynomial.generalRadiiPolynomial_alt_form` (`lemma`, section RadiiPolynomialDefinitions) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `generalRadiiPolynomial_anti_bounds` | `RadiiPolynomial.generalRadiiPolynomial_anti_bounds` (`lemma`, section SplitMonotonicity) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `general_fixed_point_theorem` | `RadiiPolynomial.general_fixed_point_theorem` (`theorem`, section FixedPointTheorem) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `general_radii_poly_neg_implies_Z_lt_one` | `RadiiPolynomial.general_radii_poly_neg_implies_Z_lt_one` (`lemma`, section RadiiPolynomialImplications) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `general_radii_polynomial_theorem` | `RadiiPolynomial.general_radii_polynomial_theorem` (`theorem`, section GeneralRadiiPolynomialTheorem; paper main.tex:252 (printed short name, no erratum)) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `general_radii_polynomial_theorem_of_le` | `RadiiPolynomial.general_radii_polynomial_theorem_of_le` (`theorem`, section SplitMonotonicity) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `invertible_comp_form` | `RadiiPolynomial.invertible_comp_form` (`lemma`, section NeumannSeries) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `invertible_of_norm_sub_id_lt_one` | `RadiiPolynomial.invertible_of_norm_sub_id_lt_one` (`theorem`, section NeumannSeries) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `isUnit_of_norm_sub_id_lt_one` | `RadiiPolynomial.isUnit_of_norm_sub_id_lt_one` (`theorem`, section NeumannSeries) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `newton_operator_Y_bound` | `RadiiPolynomial.newton_operator_Y_bound` (`lemma`, section OperatorBounds) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `newton_operator_derivative_bound_general` | `RadiiPolynomial.newton_operator_derivative_bound_general` (`lemma`, section OperatorBounds) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `newton_operator_derivative_bound_simple` | `RadiiPolynomial.newton_operator_derivative_bound_simple` (`lemma`, section OperatorBounds) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `newton_operator_fderiv` | `RadiiPolynomial.newton_operator_fderiv` (`lemma`, section OperatorBounds) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `radiiPolynomial` | `RadiiPolynomial.radiiPolynomial` (`def`, section RadiiPolynomialDefinitions) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `radiiPolynomial_alt_form` | `RadiiPolynomial.radiiPolynomial_alt_form` (`lemma`, section RadiiPolynomialDefinitions) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `radiiPolynomial_is_special_case` | `RadiiPolynomial.radiiPolynomial_is_special_case` (`lemma`, section RadiiPolynomialDefinitions) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `radii_poly_neg_implies_Z_bound_lt_one` | `RadiiPolynomial.radii_poly_neg_implies_Z_bound_lt_one` (`lemma`, section RadiiPolynomialImplications) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `simpleRadiiPolynomial` | `RadiiPolynomial.simpleRadiiPolynomial` (`def`, section RadiiPolynomialDefinitions) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `simple_maps_closedBall_to_itself` | `RadiiPolynomial.simple_maps_closedBall_to_itself` (`lemma`, section HelperLemmas) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `simple_radii_poly_neg_implies_Z_lt_one` | `RadiiPolynomial.simple_radii_poly_neg_implies_Z_lt_one` (`lemma`, section RadiiPolynomialImplications) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `simple_radii_polynomial_theorem_EtoF` | `RadiiPolynomial.simple_radii_polynomial_theorem_EtoF` (`theorem`, section SimpleRadiiPolynomialTheorem) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md`; `p3/evidence_D2/final/fingerprint.diff` |
| `NewtonLikeMap.eq_1` | `RadiiPolynomial.NewtonLikeMap.eq_1` (generated) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md` |
| `Z_bound.eq_1` | `RadiiPolynomial.Z_bound.eq_1` (generated) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md` |
| `radiiPolynomial.eq_1` | `RadiiPolynomial.radiiPolynomial.eq_1` (generated) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md` |
| `fixedPoint_injective_iff_zero._simp_1_1` | `RadiiPolynomial.fixedPoint_injective_iff_zero._simp_1_1` (generated) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md` |
| `general_fixed_point_theorem.match_1_1` | `RadiiPolynomial.general_fixed_point_theorem.match_1_1` (generated) | moved (namespace) | `p3/evidence_D2/final/cmp/STRICT_COMPARE.md` |

- The realized equation lemma `generalRadiiPolynomial.eq_1` becomes `RadiiPolynomial.generalRadiiPolynomial.eq_1`; it is
  realized in `Core/Transport` and in `Certification/RadiiPolynomialQ`, both exact (critic D2 nit).
- `Core/Bounds`, `Core/AlgebraZ2` and `Core/Transport` declare nothing outside `RadiiPolynomial`; the private
  `isDedekindFiniteMonoid_clm` keeps its FQN.

### E1 — decision 2, the WeightedL1 station (`Analysis/SequenceSpace/WeightedL1/*`, `tests/FT`, `tests/FZ`)

The station is indexed by the chosen frame alone (`ft_reindex/CONSENSUS_ft_reindex.md` R1–R3): `lpAlgRingData`,
`lpAlgSmulCompat`, the one-way compatibility layer and their wrappers are deleted; scalar coordinates, scalar singles,
the weight classes and the convolution are indexed by `FiberTrivialization 𝕜 M E`; the carrier, its module structure
and the fiber insertion `fiberSingle` are frame-free. Classes (strict v3.5 compare): retired 60 (34 public), new 24 (20
public), migrated 268 (152 public), exact 258 (127 public). All 172 public migrated/new rows have the axioms
`[propext, Classical.choice, Quot.sound]` (`p3/evidence_E1/final/signatures_E1.out`).

#### Ledger (E1)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `FiberTrivialization.ofLpAlgRingData` | (none: legacy datum deleted; build the frame directly) | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `FiberTrivialization.ofLpAlgRingData_equiv_apply` | (none: legacy datum deleted) | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `FiberTrivialization.ofLpAlgRingData_equiv_symm_apply` | (none: legacy datum deleted) | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `FiberTrivialization.toLpAlgRingData` | (none: the frame is the only datum) | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `FiberTrivialization.toLpAlgRingData_ofReal` | (none: FiberTrivialization.equiv is primary) | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `FiberTrivialization.toLpAlgRingData_toReal` | (none: (FiberTrivialization.equiv m).symm is primary) | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `FiberTrivialization.toLpAlgRingData_weight` | (none: FiberTrivialization.weight is primary) | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `FiberTrivialization.toLpAlgSmulCompat` | (none: map_smul of θ⁻¹) | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `WeightedScalar.lpAlgRingData_weight` | WeightedScalar.fiberTrivialization_weight | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `WeightedScalar.norm_ofReal_eq_mul_norm_one` | FiberTrivialization.norm_equiv_apply | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `WeightedScalar.norm_ofReal_mul_le` | SubMulWeightBase.submul with WeightedScalar.norm_ofReal | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `WeightedScalar.norm_ofReal_one_ge` | SuperUnitWeight.one_le / lpOneAlgWeightSubMul.one_le_weight | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpAlgRingData` | FiberTrivialization (class fields → LinearEquiv API of θ_m) | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpAlgRingData.norm_ofReal_eq` | FiberTrivialization.norm_equiv_apply | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpAlgRingData.ofReal` | FiberTrivialization.equiv (the frame θ_m) | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpAlgRingData.ofReal_add` | FiberTrivialization.equiv_add (map_add of θ_m) | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpAlgRingData.ofReal_toReal` | FiberTrivialization.equiv_apply_equiv_symm; on lpOneAlg: lpOneAlg.equiv_toRealSeq | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpAlgRingData.ofReal_zero` | FiberTrivialization.equiv_zero | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpAlgRingData.toReal` | (FiberTrivialization.equiv m).symm; coordinates lpOneAlg.toRealSeq (toRealSeq_apply) | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpAlgRingData.toReal_add` | FiberTrivialization.equiv_symm_add | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpAlgRingData.toReal_neg` | FiberTrivialization.equiv_symm_neg | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpAlgRingData.toReal_ofReal` | FiberTrivialization.equiv_symm_apply_equiv | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpAlgRingData.toReal_zero` | FiberTrivialization.equiv_symm_zero | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpAlgRingData.weight` | FiberTrivialization.weight | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpAlgRingData.weight_def` | FiberTrivialization.weight_def | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpAlgSmulCompat` | (none: linearity of θ_m) | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpAlgSmulCompat.toReal_smul` | map_smul (FiberTrivialization.equiv m).symm / lpOneAlg.toRealSeq_smul | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpOneAlg.norm_ofReal_one_pos` | FiberTrivialization.weight_pos | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpOneAlgWeightMul.norm_ofReal_mul_le` | lpOneAlgWeightMul.weight_add_le with FiberTrivialization.norm_equiv_apply | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpOneAlgWeightMul.norm_ofReal_one_zero` | lpOneAlgWeightMul.weight_zero | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpOneAlgWeightSubMul.norm_ofReal_one_ge` | lpOneAlgWeightSubMul.one_le_weight | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpOneMulAlgWeightMul.norm_ofReal_mul_le` | lpOneMulAlgWeightMul.weight_mul_le with FiberTrivialization.norm_equiv_apply | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpOneMulAlgWeightMul.norm_ofReal_one_one` | lpOneMulAlgWeightMul.weight_one | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| `lpOneMulAlgWeightSubMul.norm_ofReal_one_ge` | lpOneMulAlgWeightSubMul.one_le_weight | retired | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| — | `lpOneAlg.equiv_mulToRealSeq` : `(FiberTrivialization.equiv m) (lpOneAlg.mulToRealSeq f m) = ↑(lpOneAlg.toLp f) m` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.equiv_toRealSeq` : `(FiberTrivialization.equiv m) (lpOneAlg.toRealSeq f m) = ↑(lpOneAlg.toLp f) m` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.fiberSingle` : `lpOneAlg M E` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.fiberSingle_add` : `lpOneAlg.fiberSingle m (x + y) = lpOneAlg.fiberSingle m x + lpOneAlg.fiberSingle m y` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.fiberSingle_apply` : `↑(lpOneAlg.toLp (lpOneAlg.fiberSingle m x)) k = Pi.single m x k` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.fiberSingle_apply_of_ne` : `k ≠ m → ↑(lpOneAlg.toLp (lpOneAlg.fiberSingle m x)) k = 0` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.fiberSingle_apply_self` : `↑(lpOneAlg.toLp (lpOneAlg.fiberSingle m x)) m = x` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.fiberSingle_smul` : `lpOneAlg.fiberSingle m (c • x) = c • lpOneAlg.fiberSingle m x`; retired again in E1b (below) | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.fiberSingle_zero` : `lpOneAlg.fiberSingle m 0 = 0` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.hasSum_fiberSingle` : `HasSum (fun m => lpOneAlg.fiberSingle m (↑(lpOneAlg.toLp h) m)) h` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.hasSum_fiberSingle_mapCLM` : `HasSum (fun m => W (lpOneAlg.fiberSingle m (↑(lpOneAlg.toLp h) m))) (W h)` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.mulMul_apply` : `↑(lpOneAlg.toLp (f * g)) k = (FiberTrivialization.equiv k) (DiscreteConvolution.ringConvolution (lpOneAlg.mulToRealSeq f) (lpOneAlg.mulToRealSeq g) k)` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.mulOne_apply` : `↑(lpOneAlg.toLp 1) m = (FiberTrivialization.equiv m) (DiscreteConvolution.delta 1 m)` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.mulToRealSeq_apply` : `lpOneAlg.mulToRealSeq f m = (LinearEquiv.symm (FiberTrivialization.equiv m)) (↑(lpOneAlg.toLp f) m)` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.mulToRealSeq_smul` : `lpOneAlg.mulToRealSeq (r • f) = r • lpOneAlg.mulToRealSeq f` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.mul_apply` : `↑(lpOneAlg.toLp (f * g)) k = (FiberTrivialization.equiv k) (DiscreteConvolution.addRingConvolution (lpOneAlg.toRealSeq f) (lpOneAlg.toRealSeq g) k)` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.norm_fiberSingle` : `‖lpOneAlg.fiberSingle m x‖ = ‖x‖` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.one_apply` : `↑(lpOneAlg.toLp 1) m = (FiberTrivialization.equiv m) (DiscreteConvolution.addDelta 1 m)` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.single_eq_fiberSingle` : `lpOneAlg.single j x = lpOneAlg.fiberSingle j ((FiberTrivialization.equiv j) x)` | added | `p3/evidence_E1/final/signatures_E1.out` |
| — | `lpOneAlg.toRealSeq_apply` : `lpOneAlg.toRealSeq f m = (LinearEquiv.symm (FiberTrivialization.equiv m)) (↑(lpOneAlg.toLp f) m)` | added | `p3/evidence_E1/final/signatures_E1.out` |
| the 152 public migrated rows of the station (268 rows with auxiliaries): instances, weight and convolution classes, coordinates, singles, universal property, column principles | binders `[lpAlgRingData 𝕜 M E] [lpAlgSmulCompat 𝕜 M E]` → `[∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]` where a frame is needed (the `NormedSpace` binder now precedes the frame, so positional `@` uses shift); `Ring`/`NormedRing` from the index monoid + `DecidableEq` + `lpOneAlgConvCompat`, `Algebra` from the linearity of θ⁻¹; no row gained a hypothesis (critic E1 item 4); seven rows change again in E1b | migrated (frame re-index) | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/final/signatures_E1.out`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.cols_le_opNorm` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.cols_le_opNorm₂` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.cols_le_opNorm₃` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.eq_liftAlgHom_of_atoms` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.eq_liftCLM_of_cols` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.exists_eq_liftAlgHom` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.exists_eq_liftCLM` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.finsum_norm_le_of_cols` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.liftAlgHom` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.liftAlgHom_apply` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.liftAlgHom_single` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.liftAlgHom_toContinuousLinearMap` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.liftCLM` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.liftCLM_apply` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.liftCLM_mul` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.liftCLM_one` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.liftCLM_single` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.liftCLM_summable` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.norm_eq_abs_mulToReal_mul_weight` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.norm_eq_abs_toReal_mul_weight` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.norm_le_of_cols` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.norm_le_of_cols₂` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.norm_le_of_cols₃` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.norm_liftAlgHom_apply_le` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.norm_liftCLM_apply_le` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.norm_liftCLM_le` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.norm_one_eq` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.norm_single` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.norm_singleCLM` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.opNorm_eq_iSup_cols₂` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.opNorm_eq_iSup_cols₃` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.opNorm_le_iff_cols` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.opNorm_le_iff_cols₂` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.opNorm_le_iff_cols₃` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.opNorm_le_of_cols` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.opNorm_le_of_cols₂` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.opNorm_le_of_cols₃` | `‖lpAlgRingData.ofReal m 1‖` → `FiberTrivialization.weight m` in the statement (`rfl`-equal to `‖θ_m 1‖`) | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlgWeightMul.weight_add_le` | class field: `lpAlgRingData.weight` → `FiberTrivialization.weight` | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlgWeightMul.weight_zero` | class field: `lpAlgRingData.weight` → `FiberTrivialization.weight` | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlgWeightSubMul.one_le_weight` | class field: `lpAlgRingData.weight` → `FiberTrivialization.weight` | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneMulAlgWeightMul.weight_mul_le` | class field: `lpAlgRingData.weight` → `FiberTrivialization.weight` | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneMulAlgWeightMul.weight_one` | class field: `lpAlgRingData.weight` → `FiberTrivialization.weight` | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneMulAlgWeightSubMul.one_le_weight` | class field: `lpAlgRingData.weight` → `FiberTrivialization.weight` | statement changed | `p3/evidence_E1/final/CLASSIFICATION_E1.json`; `p3/evidence_E1/CRITIC_E1.md` |
| ↳ `lpOneAlg.colRatio`, `lpOneAlg.instAlgebra`, `lpOneAlg.instCommRing`, `lpOneAlg.instMul`, `lpOneAlg.instMulMul`, `lpOneAlg.instMulNormedRing`, `lpOneAlg.instMulOne`, `lpOneAlg.instMulRing`, `lpOneAlg.instNormedAlgebra`, `lpOneAlg.instNormedCommRing`, `lpOneAlg.instNormedRing`, `lpOneAlg.instOne`, `lpOneAlg.instRing`, `lpOneAlg.liftAlgHom`, `lpOneAlg.liftCLM`, `lpOneAlg.mulLeftCLM`, `lpOneAlg.mulRightCLM`, `lpOneAlg.mulToRealSeq`, `lpOneAlg.single`, `lpOneAlg.singleCLM`, `lpOneAlg.toRealSeq`, `lpOneAlg.toRealSeqAddHom` | type as in the family row; the body is written through θ_m / θ_m⁻¹ (coordinates `θ_m⁻¹ (f m)`, singles `fiberSingle m (θ_m x)`, product `θ_k ((θ⁻¹f ⋆ θ⁻¹g)_k)`, unit `θ_m (δ_m)`) | redefined | `p3/evidence_E1/final/CLASSIFICATION_E1.json` |

- The 26 generated children of the retired declarations (structures, recursors, `noConfusion`, `_proof_n`, `eq_1`, the
  private `lpOneAlg.ofReal_neg`) and the 4 auxiliary new rows are listed in `p3/evidence_E1/final/CLASSIFICATION_E1.json`.
- The `−1` frame (`θ(r) = −r`) has the same weights and the negated product with unit `−δ₀`; it is never selected by
  instance search (`tests/FT/FrameReindexProbes.lean`; `p3/evidence_E1/final/negframe_E1.out`). The environment has
  one `FiberTrivialization` instance, `WeightedScalar.instFiberTrivialization`.
- Tests: `tests/FT/FrameReindexProbes.lean`, `tests/FT/ImportOrderA.lean` and `tests/FT/ImportOrderB.lean` are new;
  `tests/FT/FiberTrivializationProbes.lean` and five `tests/FZ` modules follow the new contract.

### E2 — decision 2, the consumers (22 modules of Chebyshev, CrossGeometry, Geometric, Applications/IVP/Chebyshev, Certification)

Every touched statement selects the standard frame `WeightedScalar.instFiberTrivialization` through its concrete fiber
(`ScaledReal`, `ScaledRealZ`, `geomFiber`, `geomFiberZ`, `BorderedScaledReal`, `OmegaScaledReal` are `WeightedScalar`
abbreviations). Classes (strict v3.5 compare over the 22 modules): retired 27 (4 public), new 7 (2 public), migrated
670 (442 public), exact 913 (361 public); all 444 public migrated/new rows have the standard axioms and the endpoint
axioms are identical to the pre-E1 generation (`p3/evidence_E2/CRITIC_E2.md`).

#### Ledger (E2)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `RadiiPolynomial.ScaledRealZ.norm_lpAlgRingData_ofReal` | `RadiiPolynomial.ScaledRealZ.norm_equiv_apply : ‖FiberTrivialization.equiv (E := ScaledRealZ ν) k r‖ = \|r\| * ν ^ k.natAbs` (`@[simp]` kept); at a weight site (after `norm_single`/`norm_eq_abs_toReal_mul_weight`/column lemmas) `WeightedScalar.fiberTrivialization_weight` (drop `abs_one, one_mul`) | retired | `p3/evidence_E2/final/CLASSIFICATION_E2.json`; `p3/evidence_E2/CRITIC_E2.md` |
| `RadiiPolynomial.BorderedScaledReal.norm_lpAlgRingData_ofReal` | `RadiiPolynomial.BorderedScaledReal.norm_equiv_apply : ‖FiberTrivialization.equiv (E := BorderedScaledReal ν) n r‖ = \|r\| * borderedWeight ν n` (`@[simp]` kept); weight sites as above | retired | `p3/evidence_E2/final/CLASSIFICATION_E2.json`; `p3/evidence_E2/CRITIC_E2.md` |
| `RadiiPolynomial.ScaledReal.norm_lpAlgRingData_ofReal` | deleted (no use left): weight sites `WeightedScalar.fiberTrivialization_weight`; general `r`: `FiberTrivialization.norm_equiv_apply` + `WeightedScalar.fiberTrivialization_weight` + `Real.norm_eq_abs` | retired | `p3/evidence_E2/final/CLASSIFICATION_E2.json`; `p3/evidence_E2/CRITIC_E2.md` |
| `ChebyshevIVP.fiber_eq_zero` | deleted (a specialization of Mathlib once the frame is a `LinearEquiv`): `(LinearEquiv.map_eq_zero_iff (FiberTrivialization.equiv (E := ScaledRealZ ν) k).symm).mp` | retired | `p3/evidence_E2/final/CLASSIFICATION_E2.json`; `p3/evidence_E2/CRITIC_E2.md` |
| — | `RadiiPolynomial.ScaledRealZ.norm_equiv_apply` `(ν : PosReal) (k : ℤ) (r : ℝ) : ‖FiberTrivialization.equiv (E := ScaledRealZ ν) k r‖ = \|r\| * ↑ν ^ k.natAbs` (`@[simp]`) | added | `p3/evidence_E2/final/signatures_E2.out` |
| — | `RadiiPolynomial.BorderedScaledReal.norm_equiv_apply` `(ν : PosReal) (n : ℕ) (r : ℝ) : ‖FiberTrivialization.equiv (E := BorderedScaledReal ν) n r‖ = \|r\| * borderedWeight ν n` (`@[simp]`) | added | `p3/evidence_E2/final/signatures_E2.out` |
| the 442 public migrated consumer rows (670 with auxiliaries), per module: `Chebyshev.Algebra` 7; `Chebyshev.Bordered` 27; `Chebyshev.LaurentSpectrum` 10; `Chebyshev.OneSided` 50; `Chebyshev.Scalar` 2; `Chebyshev.Spectrum.Series` 9; `Chebyshev.SymmetricSubalgebra` 19; `Chebyshev.Symmetrize` 9; `Chebyshev.UConversion` 27; `Chebyshev.UnitLift` 41; `CrossGeometry.ChebyshevTaylor` 18; `CrossGeometry.Derivative` 10; `Geometric.Aeval` 37; `Geometric.Basic` 58; `Geometric.Omega` 24; `Applications.IVP.Chebyshev.Analytic` 11; `Applications.IVP.Chebyshev.Lambda` 21; `Applications.IVP.Chebyshev.Operator` 24; `Applications.IVP.Chebyshev.Standard` 5; `Certification.IVP.Chebyshev` 31; `Certification.Residual.FiniteSupport` 2 | printed statement unchanged except the `↳` rows; the elaborated types carry the station telescope `[∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E]` and the frame-indexed weight/convolution witnesses; no consumer gained a hypothesis | migrated (frame re-index) | `p3/evidence_E2/final/CLASSIFICATION_E2.json`; `p3/evidence_E2/final/signatures_E2.out`; `p3/evidence_E2/CRITIC_E2.md` |
| ↳ `RadiiPolynomial.geomFiberZ_weight` | `‖lpAlgRingData.ofReal (E := geomFiberZ 𝕜 ν) k (1 : 𝕜)‖ = ν ^ k.natAbs` → `FiberTrivialization.weight (E := geomFiberZ 𝕜 ν) k = ν ^ k.natAbs` (proof `WeightedScalar.fiberTrivialization_weight k`; the shape E1's FZ test edits assumed) | statement changed | `p3/evidence_E2/final/printed_changes_E2.json` |
| ↳ `RadiiPolynomial.geomFiber_weight` | `‖lpAlgRingData.ofReal (E := geomFiber 𝕜 ν) n (1 : 𝕜)‖ = ν ^ n` → `FiberTrivialization.weight (E := geomFiber 𝕜 ν) n = ν ^ n` | statement changed | `p3/evidence_E2/final/printed_changes_E2.json` |
| ↳ `RadiiPolynomial.lpOneAlg.pow_le_geomFiber_weight` | `… → ‖x ^ n‖ ≤ C * ‖lpAlgRingData.ofReal n 1‖` → `… → ‖x ^ n‖ ≤ C * FiberTrivialization.weight (E := geomFiber 𝕜 ν) n` | statement changed | `p3/evidence_E2/final/printed_changes_E2.json` |
| ↳ `RadiiPolynomial.lpOneAlg.unit_zpow_le_weight` | `… → ‖↑(u ^ k)‖ ≤ C * ‖lpAlgRingData.ofReal k 1‖` → `… → ‖↑(u ^ k)‖ ≤ C * FiberTrivialization.weight (E := geomFiberZ 𝕜 ν) k` | statement changed | `p3/evidence_E2/final/printed_changes_E2.json` |
| ↳ `ChebyshevIVP.embedNatToInt_natCast` | `embedNatToInt seq ↑n = lpAlgRingData.ofReal (↑n) (seq n)` → `embedNatToInt seq ↑n = FiberTrivialization.equiv (E := ScaledRealZ ν) ↑n (seq n)` | statement changed | `p3/evidence_E2/final/printed_changes_E2.json` |
| ↳ `ChebyshevIVP.embedWithPassThrough_natCast` | `… = lpAlgRingData.ofReal (E := ScaledRealZ ν) (↑n) (seq n)` → `… = FiberTrivialization.equiv (E := ScaledRealZ ν) (↑n) (seq n)` | statement changed | `p3/evidence_E2/final/printed_changes_E2.json` |
| ↳ `RadiiPolynomial.Residual.exists_finiteSupport_candidate_of_bezout` | binders `[lpAlgRingData 𝕜 M E] [lpOneAlgConvCompat 𝕜 M E]` → `[∀ m, NormedSpace 𝕜 (E m)] [FiberTrivialization 𝕜 M E] [lpOneAlgConvCompat 𝕜 M E]` (weakest for the ring: index monoid + `DecidableEq` + frame-indexed ConvCompat; `dense_lpOneAlg_finiteSupport` stays frame-free, exact) | statement changed | `p3/evidence_E2/final/printed_changes_E2.json` |
| ↳ `RadiiPolynomial.Residual.exists_bezout_iff_finiteSupport_certificate` | binders `[lpAlgRingData 𝕜 M E] [lpOneAlgConvCompat 𝕜 M E]` → the binders of the row above | statement changed | `p3/evidence_E2/final/printed_changes_E2.json` |
| ↳ `RadiiPolynomial.nonnegRestrict` | type exact; fibers built as `FiberTrivialization.equiv (E := X) k r`, `rfl`-equal to the old `WeightedScalar.ofReal r` on the standard frame | redefined | `p3/evidence_E2/CRITIC_E2.md` (item 3, F2) |
| ↳ `RadiiPolynomial.borderedFromU` | type exact; fibers built as `FiberTrivialization.equiv (E := X) k r`, `rfl`-equal to the old `WeightedScalar.ofReal r` on the standard frame | redefined | `p3/evidence_E2/CRITIC_E2.md` (item 3, F2) |
| ↳ `RadiiPolynomial.l1Chebyshev.symmetrize` | type exact; fibers built as `FiberTrivialization.equiv (E := X) k r`, `rfl`-equal to the old `WeightedScalar.ofReal r` on the standard frame | redefined | `p3/evidence_E2/CRITIC_E2.md` (item 3, F2) |
| ↳ `RadiiPolynomial.uIntegrate` | type exact; fibers built as `FiberTrivialization.equiv (E := X) k r`, `rfl`-equal to the old `WeightedScalar.ofReal r` on the standard frame | redefined | `p3/evidence_E2/CRITIC_E2.md` (item 3, F2) |
| ↳ `RadiiPolynomial.chebyshevFromU` | type exact; fibers built as `FiberTrivialization.equiv (E := X) k r`, `rfl`-equal to the old `WeightedScalar.ofReal r` on the standard frame | redefined | `p3/evidence_E2/CRITIC_E2.md` (item 3, F2) |
| ↳ `ChebyshevIVP.embedNatToInt` | type exact; fibers built as `FiberTrivialization.equiv (E := X) k r`, `rfl`-equal to the old `WeightedScalar.ofReal r` on the standard frame | redefined | `p3/evidence_E2/CRITIC_E2.md` (item 3, F2) |
| ↳ `ChebyshevIVP.embedWithPassThrough` | type exact; fibers built as `FiberTrivialization.equiv (E := X) k r`, `rfl`-equal to the old `WeightedScalar.ofReal r` on the standard frame | redefined | `p3/evidence_E2/CRITIC_E2.md` (item 3, F2) |

- The 23 auxiliary retired rows (renumbered `_proof_n`, equation lemmas no longer requested: `embedNatToInt.eq_1/2`,
  `borderedFromU.eq_1`, `chebyshevFromU.eq_1`, `nonnegRestrict.eq_1`, `uIntegrate.eq_1`, the private
  `embedNatToInt.match_1` equations) and the 5 new `_proof_n` rows are listed in `p3/evidence_E2/final/RULES_E2.json`.
- Private statements re-spelled the same way (no public face): Bordered `nonnegRestrict_mem`, `borderedFromU_fiber_le`,
  `borderedFromU_mem`; Symmetrize `natEmbedFun`, `natEmbed_memℓp`, `symmetrizeSeq_norm`, `symmetrize_memℓp`;
  SymmetricSubalgebra `borderedEmbed`, `borderedEmbed_memℓp`; UConversion `uIntegrate_*`, `chebyshevFromU_*`;
  CrossGeometry column bounds (conclusion `≤ FiberTrivialization.weight (E := X) k`).

### E1b — decision 2, station API quality (`WeightedL1/{FiberTrivialization,Carrier,UniversalProperty,Scalar}`, consumers)

Bundled maps replace scattered lemmas (`FiberTrivialization.equivL`, `lpOneAlg.fiberSingleₗᵢ`, `lpOneAlg.toRealSeqₗ`),
over-strong hypotheses are weakened, and the standard-model simp lemma `WeightedScalar.toReal_ofReal` closes the
stalled `θ⁻¹ (θ r) = r` goals. Classes after the critic's F1/F2: retired 4 (3 public), new 10 (8 public), migrated 7,
aux regenerated with changed types 2 (`singleCLM._proof_1/2`); all public new/migrated rows have the standard axioms
(`p3/evidence_E1b/final/signatures_E1b.out`).

#### Ledger (E1b)

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `lpOneAlg.toRealSeqAddHom` | `lpOneAlg.toRealSeqₗ : lpOneAlg M E →ₗ[𝕜] (M → 𝕜)` (S2; `.toAddMonoidHom` recovers the →+) | retired | `p3/evidence_E1b/final/CLASSIFICATION_E1b.json`; `p3/evidence_E1b/CRITIC_E1b.md` |
| `lpOneAlg.toRealSeqAddHom_apply` | `lpOneAlg.toRealSeqₗ_apply` | retired | `p3/evidence_E1b/final/CLASSIFICATION_E1b.json`; `p3/evidence_E1b/CRITIC_E1b.md` |
| `lpOneAlg.fiberSingle_smul` | `map_smul (lpOneAlg.fiberSingleₗᵢ m) c x` (no consumer) | retired | `p3/evidence_E1b/final/CLASSIFICATION_E1b.json`; `p3/evidence_E1b/CRITIC_E1b.md` |
| `lpOneAlg.fiberSingle_zero` | kept: deleted by E1b, then restored by the coordinator as a scalar-free `@[simp]` primitive (`simp` cannot reach `map_zero` through `coe_fiberSingleₗᵢ`) | restored | `p3/evidence_E1b/CRITIC_E1b.md` (F1); `DECISIONS.md` ~04:45Z |
| — | `FiberTrivialization.equivL` : `(m : M) → 𝕜 ≃L[𝕜] E m` (θ_m bundled as a continuous linear equivalence from `continuous_equiv`, `continuous_equiv_symm`) | added | `p3/evidence_E1b/final/signatures_E1b.out` |
| — | `FiberTrivialization.coe_equivL` (simp) : `⇑(equivL m) = ⇑(equiv m)` (rfl) | added | `p3/evidence_E1b/final/signatures_E1b.out` |
| — | `FiberTrivialization.coe_equivL_symm` (simp) : `⇑(equivL m).symm = ⇑(equiv m).symm` (rfl) | added | `p3/evidence_E1b/final/signatures_E1b.out` |
| — | `lpOneAlg.fiberSingleₗᵢ` : `[∀ m, NormedSpace 𝕜 (E m)] [DecidableEq M] (m : M) → E m →ₗᵢ[𝕜] lpOneAlg M E` (frame-free) | added | `p3/evidence_E1b/final/signatures_E1b.out` |
| — | `lpOneAlg.coe_fiberSingleₗᵢ` (simp) : `⇑(fiberSingleₗᵢ m) = fiberSingle m` (rfl) | added | `p3/evidence_E1b/final/signatures_E1b.out` |
| — | `lpOneAlg.toRealSeqₗ` : `lpOneAlg M E →ₗ[𝕜] (M → 𝕜)` (frame-indexed) | added | `p3/evidence_E1b/final/signatures_E1b.out` |
| — | `lpOneAlg.toRealSeqₗ_apply` (simp) : `toRealSeqₗ f = toRealSeq f` (rfl) | added | `p3/evidence_E1b/final/signatures_E1b.out` |
| — | `WeightedScalar.toReal_ofReal` (simp) : `toReal (ofReal r : WeightedScalar 𝕜 w m) = r` (rfl) | added | `p3/evidence_E1b/final/signatures_E1b.out` |
| `lpOneAlg.abs_toRealSeq_le` | `[AddMonoid M] [lpOneAlgWeightSubMul 𝕜 M E] (f) (m)` → `(hw : ∀ m, 1 ≤ FiberTrivialization.weight (E := E) m) (f) (m)`; monoid dropped (S3) | weakening | `p3/evidence_E1b/final/CLASSIFICATION_E1b.json`; `p3/evidence_E1b/CRITIC_E1b.md` |
| `lpOneAlg.abs_mulToRealSeq_le` | `[Monoid M] [lpOneMulAlgWeightSubMul 𝕜 M E]` → the same `hw` (S3) | weakening | `p3/evidence_E1b/final/CLASSIFICATION_E1b.json`; `p3/evidence_E1b/CRITIC_E1b.md` |
| `lpOneAlg.summable_abs_toRealSeq` | as `abs_toRealSeq_le`: `hw` explicit first argument (S3) | weakening | `p3/evidence_E1b/final/CLASSIFICATION_E1b.json`; `p3/evidence_E1b/CRITIC_E1b.md` |
| `lpOneAlg.summable_abs_mulToRealSeq` | as `abs_mulToRealSeq_le` (S3) | weakening | `p3/evidence_E1b/final/CLASSIFICATION_E1b.json`; `p3/evidence_E1b/CRITIC_E1b.md` |
| `lpOneAlg.norm_one_eq` | `[lpOneAlgConvCompat 𝕜 M E]` dropped (the unit needs none); statement `‖1‖ = weight 0` unchanged (S3) | weakening | `p3/evidence_E1b/final/CLASSIFICATION_E1b.json`; `p3/evidence_E1b/CRITIC_E1b.md` |
| `lpOneAlg.instNormOneClass` | `[lpOneAlgConvCompat 𝕜 M E]` dropped; keeps `[lpOneAlgWeightMul 𝕜 M E]`, the smallest existing class carrying `weight_zero` (no class invented) (S3) | weakening | `p3/evidence_E1b/final/CLASSIFICATION_E1b.json`; `p3/evidence_E1b/CRITIC_E1b.md` |
| `lpOneAlg.singleCLM` | type unchanged; value re-bodied: `(fiberSingleₗᵢ m).toContinuousLinearMap.comp (equivL m)` (S1); `singleCLM_apply` (rfl) and `norm_singleCLM` unchanged in print and type | redefined | `p3/evidence_E1b/final/CLASSIFICATION_E1b.json`; `p3/evidence_E1b/CRITIC_E1b.md` |

- Proof only (exact rows): `single_smul` (`map_smul` of `fiberSingleₗᵢ`), `toRealSeq_finset_sum` (`map_sum` of
  `toRealSeqₗ`), `ChebyshevIVP.StdChebIVPData.abar_toSeq_eq`, the private `l1Chebyshev.summable_coeff`.
- Auxiliaries: `singleCLM._proof_3` retired; `fiberSingleₗᵢ._proof_1` and `ChebyshevIVP.StdChebIVPData.abar.eq_1` new;
  `singleCLM._proof_1/2` regenerated with changed types (critic E1b F2).
- Consumer recipe: `abs_toRealSeq_le f m` and `summable_abs_toRealSeq f` take a proof of `∀ m, 1 ≤ weight m` (for
  example `lpOneAlgWeightSubMul.one_le_weight`) as their first explicit argument.

### Trust record — native auxiliaries (DEFER round)

No native auxiliary was renamed and no API name of a native auxiliary changed. The endpoint axiom sets (`main_theorem`
of Ex77/81/83/1421/245, both `ivp_main_theorem`) are identical across D1, D2, E1/E2 and E1b: Ex81 carries 1 native
auxiliary and Ex83 7, under the names of the C14b trust record (`p3/evidence_D1/item8/ex83_axioms_after.out`,
`p3/evidence_D2/final/axioms_after.out`, `p3/evidence_E2/final/endpoint_axioms_after.out`,
`p3/evidence_E1b/final/endpoint_axioms_after.out`).

### Read-through cleanups 2026-10-13 (user: "ask codex to golf totalDegree_pderiv_le"; "Cleanup that fits the rule, yah go")

Two proof-level cleanups found during the user's read-through of READING_ORDER.md; no statement, name or binder of a
surviving declaration changed. Record: `exterior/Unformalization/_records/golf_bridge_20261013/` (unit report,
source and companion hashes); companions re-drafted as working-tree drafts for the same commit.

- `MvPolynomial.totalDegree_pderiv_le` (`Algebra/Polynomial/MvPolynomial/Core.lean`): proof golfed by Codex, 27 → 9
  lines, through `MvPolynomial.coeff_pderiv` and the support of `p` (no monomial expansion, no case split).
- Bridge-first cleanup of the block-matrix composition identity (`Operators/BlockDiagonal/Basic.lean`; Opus unit
  `exterior/tmp/blockdiag_bridge_20261013`): the finite-mode action is the flattened matrix acting on the flattened
  coefficient vector, so the composition law is Mathlib's `Matrix.mulVec_mulVec` read through `FiniteBlockMatrix.toMatrix`.

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| — | `RadiiPolynomial.SystemBlockDiagData.action_fin_eq_toMatrix_mulVec` (`A.action b l n = (A.finBlock.toMatrix *ᵥ fun p => b p.1 p.2) (l, n)`) | new | unit REPORT.md |
| — | `RadiiPolynomial.SystemBlockDiagData.comp_finBlock_toMatrix` (`(A.comp B).finBlock.toMatrix = A.finBlock.toMatrix * B.finBlock.toMatrix`; `= toMatrix_blockMul`) | new | unit REPORT.md |
| `RadiiPolynomial.blockFinite_mulVec_assoc` | `action_fin_eq_toMatrix_mulVec` + `Matrix.mulVec_mulVec` (+ `toMatrix_blockMul`); both callers (`BlockDiagonal/WeightedL1` `defectOfBlockDiagOp_coeff_finite`, `IVP/Taylor/Theorem` `composedApprox_eq_fderiv_fin`) rerouted and shorter | deleted | unit REPORT.md |
| `RadiiPolynomial.SystemBlockDiagData.comp_action_finite` | (none: no caller after the re-proof of `comp_action_eq_action_comp_finite`) | deleted | unit REPORT.md |
| `RadiiPolynomial.NormHelpers.sum4_swap_pairs` (`Analysis/Norm/FiniteSum.lean`) | (none: its only caller was the deleted hand proof) | deleted | unit REPORT.md |

`RadiiPolynomial.SystemBlockDiagData.comp_action_eq_action_comp_finite` is re-proved (statement unchanged) from the two
new lemmas; `action_comp_finite` and `action_fin_eq_sum_mulVec` stay (callers in `BlockDiagonal/WeightedL1` and
`BlockDiagonal/Composition`). `open scoped Matrix` added to `BlockDiagonal/Basic`, `BlockDiagonal/WeightedL1` and
`IVP/Taylor/Theorem` for `*ᵥ`. The ReferenceBook sources name none of the deleted declarations.

### Supersessions of earlier rows (history kept)

- `RadiiPolynomial.CauchyProduct.*`, `CauchyProduct_eq_finiteAddConvolution` and `map_CauchyProduct` in the
  DiscreteConvolution-adoption, bundled power-series bridge, C1, C3-A, C3-B, R10b, R10d and C9-A rows now read
  `RadiiPolynomial.cauchyProduct.*`, `cauchyProduct_eq_finiteAddConvolution`, `map_cauchyProduct` (D1 above); module
  names are unchanged.
- C4 rows naming `lpAlgRingData`, `lpAlgSmulCompat`, `FiberTrivialization.ofLpAlgRingData`/`toLpAlgRingData`,
  `lpOneAlg.norm_ofReal_one_pos` (E1) and `lpOneAlg.toRealSeqAddHom(_apply)` (E1b) describe retired declarations; the
  replacements are in the E1 and E1b ledgers.
- C7-A and C10-A rows naming `ScaledReal.norm_lpAlgRingData_ofReal` and `ScaledRealZ.norm_lpAlgRingData_ofReal`: retired
  by E2 (replacements in the E2 ledger).
- C9-A rows naming `l1Weighted.*` declarations of `Geometric/Evaluation` (for example the replacement
  `l1Weighted.evalAlgHom`): these are now `RadiiPolynomial.l1Weighted.*` (D1 decision 4).
- C12 and the 2026-09 sections naming `IsAnalyticSolution` or `x_analytic_isAnalyticSolution*`: now `IsBallSolution`,
  `x_analytic_isBallSolution*` (D1 decision 5).
- Rows naming the root `Core/Theorem` family (`general_radii_polynomial_theorem`, `generalRadiiPolynomial`, …): the
  FQNs are now `RadiiPolynomial.<name>` (D2).
- The C15 T-4 row (`tests/FT/FiberTrivializationProbes.lean`) stands; E1 rewrote the file's contents for the new
  contract.

