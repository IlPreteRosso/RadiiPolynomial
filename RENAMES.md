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


## WN-1 — submultiplicativity and independent unit normalization

API-v2 copy change: full copied build, all 630 saved endpoint-type/axiom checks, and the independent normalization controls passed. The frozen pre-repair changed-module/control audit recorded 643 checked declarations on the three standard axioms, twelve actual compatibility producer selections, and priorities 1100/1000. The repaired copy passed a fresh default build (4,423 jobs), the unchanged saved 630-endpoint type/axiom gate, and the changed-module/control audit with 636 checked declarations (564 imported + 68 controls/helpers + 4 support). Four unused normalization instances were removed and nine test witnesses changed to theorem form. The initial prediction of 639 omitted three lazily generated `pow2Z.eq_1` declarations that disappear when their only `simp [pow2Z]` requests are removed; the failed prediction and all prior evidence are retained. All surviving imported types, universe parameters and axiom sets are unchanged; six local scratch-control types differ only in pinned hygienic binder names caused by the audit file relocation. All twelve stored producer expressions remain identical. The rebuilt production/default and FT stages have no warnings; the external diagnostic leaf retains its 26 pre-existing control warnings. Fresh evidence and the exact reconciliation are under `REPAIR_v2/`; the final packet is `freeze_v2/`. Independent peer acceptance remains separate; evidence is under the WN-1 directory named next. Source contract: `exterior/tmp/lp_api_campaign_20261017/codex/WEIGHT_NORMALIZATION_SPLIT_v1/BRIEF.md`; exact eleven-file candidate: its `CANDIDATE.json`. This entry supersedes the normalization-field rows in E1 and the `instNormOneClass` assumption recorded in E1b; those historical records stay intact.

| Old declaration or contract | Canonical replacement or revised contract | Kind |
|---|---|---|
| `RadiiPolynomial.lpOneAlgWeightMul`, `RadiiPolynomial.lpOneMulAlgWeightMul` | Submultiplicativity only; the identity-weight equations are removed. Their extensions by weight ≥ 1 also carry no normalization. | Weakened contract |
| `RadiiPolynomial.SubMulWeightBase`, `RadiiPolynomial.SubMulWeight` | Positive submultiplicativity, with weight ≥ 1 in the latter; neither contains normalization. Existing index assumptions stay fixed. | Weakened contract |
| `RadiiPolynomial.lpOneAlgWeightMul.weight_zero` | `RadiiPolynomial.lpOneAlgWeightNormalized.weight_zero`, supplied independently for the actual chosen frame. | Removed projection; no alias |
| `RadiiPolynomial.SubMulWeightBase.weight_zero` | `RadiiPolynomial.NormalizedWeight.weight_zero`; the new Prop class assumes only `Zero M`, independently of positivity and submultiplicativity. | Removed projection; no alias |
| `RadiiPolynomial.lpOneMulAlgWeightMul.weight_one` | An explicit identity-weight equation where needed. The former projection-only tests now take that equation as a hypothesis; WN-1 adds no multiplicative normalization class. | Removed projection; no alias |
| `RadiiPolynomial.lpOneAlg.instNormOneClass` | Uses `lpOneAlgWeightNormalized` instead of `lpOneAlgWeightMul`; still needs no convolution compatibility. `lpOneAlg.norm_one_eq : ‖1‖ = weight 0` needs neither weight class. | Revised hypothesis |
| Standard-frame normalization previously bundled into `WeightedScalar.instLpOneAlgWeightMul` | `RadiiPolynomial.WeightedScalar.instLpOneAlgWeightNormalized` from `PosWeight w` and `NormalizedWeight w`. The existing submultiplicativity bridge retains its own service. | Split instance |
| Geometric, bilateral and bordered constructors' bundled `weight_zero` fields | Independent `ScaledReal.instNormalizedWeight` and `ScaledRealZ.instNormalizedWeight`. Bilateral normalization holds for every positive radius; its submultiplicativity still requires radius ≥ 1. The unused bordered normalization instance is removed: the saved endpoint trail reaches no norm-one unit on `l1Bordered`, whose automatic ring is not the physical Chebyshev product. The equation `borderedWeight_zero` remains. | Split instances; unused bordered instance removed |

The convolution compatibility abstraction and both producers, the physical norm, product, ring/algebra structures and route priorities retain their existing roles. Ring and normed-algebra consumers need no identity-weight normalization. Norm-one consumers receive the independent witness. All affected FT constructors and normalization probes migrate directly; no compatibility layer is introduced.


## PLANNED (deferred; logged 2026-10-15 on the user's instruction — executes with the ℓ^p/ℓ² revamp, not before)
| old | new | file | step | reason |
|---|---|---|---|---|
| `l1Weighted.evalContinuousAlgHom` (+ `_apply`, `_gen`, `_comp_radiusRestrict` faces) | the lift face `l1Weighted.aeval_of_norm_le ν z hz` / `evalC` (C = 1 evaluation through `liftAlgHom → geomAeval → geomAeval_of_norm_le`) | `Analysis/SequenceSpace/Geometric/Evaluation.lean:301` (def; multiplicativity by Mertens) | **EXECUTED (U25)**; historical revamp (WeightedLp/ℓ² adoption) plan ([U25 section](#u25--one-universal-geometric-evaluator)) | **Historical rationale and then-current source locators:** OLDER ARROW that does not factor through the lift. `Aeval.lean:367–371` (`aeval_eq_evalContinuousAlgHom`) proves it EQUAL to the lift face by uniqueness on the generator, so retiring it is a re-route, not a statement change. Consumers to re-route: `Applications/IVP/Taylor/Boundary.lean:22` (`taylorBoundaryCharacter`), `Applications/IVP/Chebyshev/Boundary.lean`, `CrossGeometry/Joukowski.lean` (:373, :393, :542, :561), `CrossGeometry/ChebyshevTaylor.lean` (:121–133), `Geometric/RadiusRestriction.lean`, `Geometric/EvalC.lean:68` (the bridge itself). Keep the bridge theorem as the migration witness until the last consumer moves; then RETIRE with the replacement named here. Model of the target shape: `Applications/IVP/Taylor/ComplexTime.lean:29–33` `complexEval_evalBanach = CompPoly.map_evalBanach (evalC ν z hz).toAlgHom p a` → `Examples/IVP/Taylor/Example83/ComplexTime.lean:38` `lorenz_complex_ivp`. User's words (2026-10-15): "this should be logged as deprecate when we revamp the codebase to include lp Mul and l2 stuff". |

## W2 integration: carrier and completeness (2026-10-19)

- Added the generic `WeightedLp.Carrier` and the minimal `WeightedLp.Module` services to the API copy as integration modules; public facade unchanged until their consumer landing.
- Moved `exponent_toReal_pos` from the scratch RowBound file into Carrier. The unused RowBound API stays in the probe record; no forwarding alias.
- Kept coefficient reconstruction and fibre/carrier completeness from scratch Module; omitted index-group symbol-action sections until the Fourier consumer reaches them. Completeness now assumes `NormedField` and `CompleteSpace` instead of `RCLike`.
- Removed diagnostic commands from the library modules; pinned originals and type/axiom evidence are under `exterior/api_v2/probes/records/W2_originals` and the campaign W2 integration record. R1/R2 each build and pass all 630 saved endpoint-type and unchanged-axiom checks.


## W2 R4: Taylor regression witness (2026-10-19)

The accepted scratch chain is relocated to the API copy. Its library services stay outside the public facade pending the named production-consumer gate; the separate ℓ² witness lives under `Examples/tests/WL/Example81L2`. The generic tail kernel and its Taylor return now have separate owning modules. `Differential` remains example-local. No compatibility aliases are introduced.

| Previous public name | Current public name |
|---|---|
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Araw` | `Example81.L2.Araw` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.DFraw` | `Example81.L2.DFraw` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Data.A_col` | `Example81.L2.Data.A_col` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Data.DF_col` | `Example81.L2.Data.DF_col` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Data.abar_0` | `Example81.L2.Data.abar_0` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Ddiag` | `Example81.L2.Ddiag` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.H_aStar` | `Example81.L2.H_aStar` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.H_eq_logistic` | `Example81.L2.H_eq_logistic` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.H_eq_zero_iff` | `Example81.L2.H_eq_zero_iff` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.aStar` | `Example81.L2.aStar` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.aStar_mem` | `Example81.L2.aStar_mem` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.abs_xStar_sub_le` | `Example81.L2.abs_xStar_sub_le` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.embedXL1` | `Example81.L2.embedXL1` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.eqOn_xStar_of_solution` | `Example81.L2.eqOn_xStar_of_solution` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.eqOn_x_analytic_of_isBallSolution` | `Example81.L2.eqOn_x_analytic_of_isBallSolution` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.eq_aStar_of_H_eq_zero` | `Example81.L2.eq_aStar_of_H_eq_zero` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.eq_of_H_eq_zero` | `Example81.L2.eq_of_H_eq_zero` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.example81_l2_solution` | `Example81.L2.example81_l2_solution` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.example81_l2_solution_existsUnique` | `Example81.L2.example81_l2_solution_existsUnique` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.example81_l2_solution_spec` | `Example81.L2.example81_l2_solution_spec` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.hasDerivAt_sumSeries_of_H_eq_zero` | `Example81.L2.hasDerivAt_sumSeries_of_H_eq_zero` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.hasDerivAt_xStar` | `Example81.L2.hasDerivAt_xStar` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.isBallSolution_aStar` | `Example81.L2.isBallSolution_aStar` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.ivpCoeffs_embedXL1_eq_zero` | `Example81.L2.ivpCoeffs_embedXL1_eq_zero` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.logistic_recurrence_unique` | `Example81.L2.logistic_recurrence_unique` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.norm_embedXL1_aStar_le` | `Example81.L2.norm_embedXL1_aStar_le` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.sumSeries` | `Example81.L2.sumSeries` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.sumSeries_eq_x_analytic` | `Example81.L2.sumSeries_eq_x_analytic` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.sumSeries_zero_of_H_eq_zero` | `Example81.L2.sumSeries_zero_of_H_eq_zero` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.toCoeff_embedXL1` | `Example81.L2.toCoeff_embedXL1` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.trajRadius` | `Example81.L2.trajRadius` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.xStar` | `Example81.L2.xStar` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.FunctionSpace.xStar_zero` | `Example81.L2.xStar_zero` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.H` | `Example81.L2.H` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.H_apply` | `Example81.L2.H_apply` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.L` | `Example81.L2.L` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.L_comp_P` | `Example81.L2.L_comp_P` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.L_eq_id_sub_Pi_S` | `Example81.L2.L_eq_id_sub_Pi_S` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Lhead` | `Example81.L2.Lhead` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.LheadQ` | `Example81.L2.LheadQ` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.LheadQ_entries` | `Example81.L2.LheadQ_entries` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.LheadQ_mul_PheadQ` | `Example81.L2.LheadQ_mul_PheadQ` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Lhead_entries` | `Example81.L2.Lhead_entries` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Lhead_mul_Phead` | `Example81.L2.Lhead_mul_Phead` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.N` | `Example81.L2.N` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.P` | `Example81.L2.P` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.P_H_abar` | `Example81.L2.P_H_abar` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.P_comp_L` | `Example81.L2.P_comp_L` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.P_comp_Q` | `Example81.L2.P_comp_Q` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.P_delta_eleven` | `Example81.L2.P_delta_eleven` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.P_delta_zero_coeff_two` | `Example81.L2.P_delta_zero_coeff_two` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.P_injective` | `Example81.L2.P_injective` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.P_injective_bound` | `Example81.L2.P_injective_bound` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.P_norm_le` | `Example81.L2.P_norm_le` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.PcolSupport` | `Example81.L2.PcolSupport` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Phead` | `Example81.L2.Phead` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.PheadQ` | `Example81.L2.PheadQ` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.PheadQ_col_bound` | `Example81.L2.PheadQ_col_bound` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.PheadQ_mul_LheadQ` | `Example81.L2.PheadQ_mul_LheadQ` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.PheadQ_row_bound` | `Example81.L2.PheadQ_row_bound` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Phead_col_bound` | `Example81.L2.Phead_col_bound` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Phead_mul_Lhead` | `Example81.L2.Phead_mul_Lhead` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Phead_row_bound` | `Example81.L2.Phead_row_bound` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Pi` | `Example81.L2.Pi` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Pi_comp_S_comp_Q` | `Example81.L2.Pi_comp_S_comp_Q` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Pkernel` | `Example81.L2.Pkernel` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.PkernelQ` | `Example81.L2.PkernelQ` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.PkernelQ_column_zero_sq` | `Example81.L2.PkernelQ_column_zero_sq` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Pkernel_col_support` | `Example81.L2.Pkernel_col_support` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Pkernel_fin` | `Example81.L2.Pkernel_fin` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Pkernel_row_support` | `Example81.L2.Pkernel_row_support` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Pkernel_schur` | `Example81.L2.Pkernel_schur` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.ProwSupport` | `Example81.L2.ProwSupport` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.PschurCLM` | `Example81.L2.PschurCLM` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.PschurCLM_eq_P` | `Example81.L2.PschurCLM_eq_P` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Q` | `Example81.L2.Q` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Q_comp_P` | `Example81.L2.Q_comp_P` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.S` | `Example81.L2.S` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.S_eq` | `Example81.L2.S_eq` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.T` | `Example81.L2.T` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.T_eq_tailIntegratedProduct` | `Example81.L2.T_eq_tailIntegratedProduct` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.T_eq_tailKernelCLM` | `Example81.L2.T_eq_tailKernelCLM` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.X` | `Example81.L2.X` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Y0_bound` | `Example81.L2.Y0_bound` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Z0_bound` | `Example81.L2.Z0_bound` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Z0_identity` | `Example81.L2.Z0_identity` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Z0_slot` | `Example81.L2.Z0_slot` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Z1_bound` | `Example81.L2.Z1_bound` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Z2_ball_bound` | `Example81.L2.Z2_ball_bound` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Z2_difference_bound` | `Example81.L2.Z2_difference_bound` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.Z2_slot` | `Example81.L2.Z2_slot` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.abar` | `Example81.L2.abar` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.abarQ` | `Example81.L2.abarQ` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.beta` | `Example81.L2.beta` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.betaQ` | `Example81.L2.betaQ` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.betaQ_explicit` | `Example81.L2.betaQ_explicit` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff` | `Example81.L2.coeff` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff_H_abar` | `Example81.L2.coeff_H_abar` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff_H_abar_eleven_ne_zero` | `Example81.L2.coeff_H_abar_eleven_ne_zero` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff_H_abar_head` | `Example81.L2.coeff_H_abar_head` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff_H_abar_of_gt` | `Example81.L2.coeff_H_abar_of_gt` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff_P_delta` | `Example81.L2.coeff_P_delta` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff_Q` | `Example81.L2.coeff_Q` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff_S` | `Example81.L2.coeff_S` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff_S_fin` | `Example81.L2.coeff_S_fin` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff_T` | `Example81.L2.coeff_T` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff_T_range` | `Example81.L2.coeff_T_range` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff_abar` | `Example81.L2.coeff_abar` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff_abar_fin` | `Example81.L2.coeff_abar_fin` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff_abar_of_gt` | `Example81.L2.coeff_abar_of_gt` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff_beta` | `Example81.L2.coeff_beta` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.coeff_beta_of_gt` | `Example81.L2.coeff_beta_of_gt` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.contraction_value` | `Example81.L2.contraction_value` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.delta` | `Example81.L2.delta` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.differentiable_H` | `Example81.L2.differentiable_H` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.example81_l2_coefficient_zero` | `Example81.L2.example81_l2_coefficient_zero` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.example81_l2_coefficient_zero_nondegenerate` | `Example81.L2.example81_l2_coefficient_zero_nondegenerate` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.fderiv_H_abar` | `Example81.L2.fderiv_H_abar` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.hasFDerivAt_H` | `Example81.L2.hasFDerivAt_H` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.hasFDerivWithinAt_H` | `Example81.L2.hasFDerivWithinAt_H` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.kernel` | `Example81.L2.kernel` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.kernel_11_10` | `Example81.L2.kernel_11_10` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.kernel_11_9` | `Example81.L2.kernel_11_9` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.kernel_12_10` | `Example81.L2.kernel_12_10` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.kernel_13_11` | `Example81.L2.kernel_13_11` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.kernel_row_finite` | `Example81.L2.kernel_row_finite` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.kernel_row_summable` | `Example81.L2.kernel_row_summable` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.normFact` | `Example81.L2.normFact` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.normPosWeight` | `Example81.L2.normPosWeight` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.norm_P_H_abar_pos` | `Example81.L2.norm_P_H_abar_pos` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.norm_T_le` | `Example81.L2.norm_T_le` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.norm_comp_fderiv_H_sub_le` | `Example81.L2.norm_comp_fderiv_H_sub_le` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.norm_comp_fderiv_H_sub_le_of_norm_le` | `Example81.L2.norm_comp_fderiv_H_sub_le_of_norm_le` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.norm_sq_P_H_abar` | `Example81.L2.norm_sq_P_H_abar` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.norm_sq_P_delta_zero` | `Example81.L2.norm_sq_P_delta_zero` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.not_P_norm_le_one` | `Example81.L2.not_P_norm_le_one` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.one_lt_norm_P_delta_zero` | `Example81.L2.one_lt_norm_P_delta_zero` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.radii_neg` | `Example81.L2.radii_neg` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.radii_value` | `Example81.L2.radii_value` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.residualCoeff` | `Example81.L2.residualCoeff` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.residualFact` | `Example81.L2.residualFact` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.residualPosWeight` | `Example81.L2.residualPosWeight` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.symbolMass_beta` | `Example81.L2.symbolMass_beta` |
| `RadiiPolynomial.WeightedLpCodex.Example81L2.tailKernel_eq_kernel` | `Example81.L2.tailKernel_eq_kernel` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.Pi` | `RadiiPolynomial.WeightedLp.WithHead.Pi` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.Pi_comp_Pi` | `RadiiPolynomial.WeightedLp.WithHead.Pi_comp_Pi` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.Pi_comp_Q` | `RadiiPolynomial.WeightedLp.WithHead.Pi_comp_Q` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.Q` | `RadiiPolynomial.WeightedLp.WithHead.Q` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.Q_comp_Pi` | `RadiiPolynomial.WeightedLp.WithHead.Q_comp_Pi` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.Q_comp_Q` | `RadiiPolynomial.WeightedLp.WithHead.Q_comp_Q` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.Q_comp_withHead` | `RadiiPolynomial.WeightedLp.WithHead.Q_comp_withHead` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.Xp` | `RadiiPolynomial.WeightedLp.WithHead.Xp` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.coeff_Pi` | `RadiiPolynomial.WeightedLp.WithHead.coeff_Pi` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.coeff_Pi_fin` | `RadiiPolynomial.WeightedLp.WithHead.coeff_Pi_fin` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.coeff_Pi_of_gt` | `RadiiPolynomial.WeightedLp.WithHead.coeff_Pi_of_gt` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.coeff_Q_fin` | `RadiiPolynomial.WeightedLp.WithHead.coeff_Q_fin` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.coeff_Q_of_gt` | `RadiiPolynomial.WeightedLp.WithHead.coeff_Q_of_gt` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.coeff_headCore_fin` | `RadiiPolynomial.WeightedLp.WithHead.coeff_headCore_fin` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.coeff_headCore_of_gt` | `RadiiPolynomial.WeightedLp.WithHead.coeff_headCore_of_gt` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.coeff_withHead_fin` | `RadiiPolynomial.WeightedLp.WithHead.coeff_withHead_fin` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.coeff_withHead_of_gt` | `RadiiPolynomial.WeightedLp.WithHead.coeff_withHead_of_gt` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.headCore` | `RadiiPolynomial.WeightedLp.WithHead.headCore` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.withHead` | `RadiiPolynomial.WeightedLp.WithHead.withHead` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.withHead_comp` | `RadiiPolynomial.WeightedLp.WithHead.withHead_comp` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.withHead_comp_Q` | `RadiiPolynomial.WeightedLp.WithHead.withHead_comp_Q` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.withHead_one` | `RadiiPolynomial.WeightedLp.WithHead.withHead_one` |
| `RadiiPolynomial.WeightedLpCodex.FiniteBlock.withHead_zero` | `RadiiPolynomial.WeightedLp.WithHead.withHead_zero` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.Tests.H` | `Example81.L2.Logistic.H` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.Tests.H_eq_zero_iff` | `Example81.L2.Logistic.H_eq_zero_iff` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.Tests.H_half_delta_half_ne_zero` | `Example81.L2.Logistic.H_half_delta_half_ne_zero` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.Tests.coeff_H_succ` | `Example81.L2.Logistic.coeff_H_succ` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.Tests.coeff_H_zero` | `Example81.L2.Logistic.coeff_H_zero` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.Tests.q` | `Example81.L2.Logistic.q` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.X` | `RadiiPolynomial.WeightedLp.Taylor.X` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.coeff` | `RadiiPolynomial.WeightedLp.Taylor.coeff` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.coeff_integratedProduct_succ` | `RadiiPolynomial.WeightedLp.Taylor.coeff_integratedProduct_succ` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.coeff_integratedProduct_zero` | `RadiiPolynomial.WeightedLp.Taylor.coeff_integratedProduct_zero` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.coeff_integrationCLM_succ` | `RadiiPolynomial.WeightedLp.Taylor.coeff_integrationCLM_succ` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.coeff_integrationCLM_zero` | `RadiiPolynomial.WeightedLp.Taylor.coeff_integrationCLM_zero` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.delta` | `RadiiPolynomial.WeightedLp.Taylor.delta` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.differentiable_quadraticMap` | `Example81.L2.Differential.differentiable_quadraticMap` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.differentiable_residual` | `Example81.L2.Differential.differentiable_residual` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.fderiv_quadraticMap` | `Example81.L2.Differential.fderiv_quadraticMap` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.fderiv_quadraticMap_zero` | `Example81.L2.Differential.fderiv_quadraticMap_zero` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.fderiv_residual` | `Example81.L2.Differential.fderiv_residual` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.fderiv_residual_zero` | `Example81.L2.Differential.fderiv_residual_zero` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.geoPos` | `RadiiPolynomial.WeightedLp.Taylor.geoPos` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.geoWeight` | `RadiiPolynomial.WeightedLp.Taylor.geoWeight` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.hasFDerivAt_quadraticMap` | `Example81.L2.Differential.hasFDerivAt_quadraticMap` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.hasFDerivAt_residual` | `Example81.L2.Differential.hasFDerivAt_residual` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.integratedProduct` | `RadiiPolynomial.WeightedLp.Taylor.integratedProduct` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.integratedProduct_delta_zero` | `RadiiPolynomial.WeightedLp.Taylor.integratedProduct_delta_zero` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.integratedProduct_single_single` | `RadiiPolynomial.WeightedLp.Taylor.integratedProduct_single_single` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.integratedProduct_symm` | `RadiiPolynomial.WeightedLp.Taylor.integratedProduct_symm` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.integrationCLM` | `RadiiPolynomial.WeightedLp.Taylor.integrationCLM` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.norm_comp_fderiv_residual_sub_le` | `Example81.L2.Differential.norm_comp_fderiv_residual_sub_le` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.norm_comp_fderiv_residual_sub_le_of_norm_le` | `Example81.L2.Differential.norm_comp_fderiv_residual_sub_le_of_norm_le` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.norm_delta` | `RadiiPolynomial.WeightedLp.Taylor.norm_delta` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.norm_fderiv_quadraticMap_sub_le` | `Example81.L2.Differential.norm_fderiv_quadraticMap_sub_le` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.norm_integratedProduct_apply_le` | `RadiiPolynomial.WeightedLp.Taylor.norm_integratedProduct_apply_le` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.norm_integratedProduct_eq` | `RadiiPolynomial.WeightedLp.Taylor.norm_integratedProduct_eq` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.norm_integratedProduct_le` | `RadiiPolynomial.WeightedLp.Taylor.norm_integratedProduct_le` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.norm_integratedProduct_left_le` | `RadiiPolynomial.WeightedLp.Taylor.norm_integratedProduct_left_le` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.norm_integrationCLM_eq` | `RadiiPolynomial.WeightedLp.Taylor.norm_integrationCLM_eq` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.norm_sq_eq_tsum` | `RadiiPolynomial.WeightedLp.Taylor.norm_sq_eq_tsum` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.not_bound_below_radius` | `RadiiPolynomial.WeightedLp.Taylor.not_bound_below_radius` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.quadraticMap` | `Example81.L2.Differential.quadraticMap` |
| `RadiiPolynomial.WeightedLpCodex.Taylor.residual` | `Example81.L2.Differential.residual` |


### W2 scalar and consumer-premise correction

Schur construction and coordinate laws now use `NormedField` plus scalar completeness; only operator-norm laws retain `NontriviallyNormedField`. No public names changed. Example81.L2 differential upper-bound laws remove the redundant `0 ≤ M` premise (already implied by `‖P‖ ≤ M`), and the Z₂ consumer no longer supplies that hint. Exact source deltas and before/after types are retained in the W2 integration evidence.


## W2 R5: finite-synthesis contract and ℓ¹ adapter (2026-10-19)

The generic finite-p LiftBound construction, atom computation, uniqueness and converse enter together. Specialized unconsumed producers stay in the archived scratch record. WeightedL1Iso bounds an existing arrow without scalar completeness; completeness remains on construction of the extension. `TaylorTailL1` now owns only the coefficient-to-ℓ¹ operator bridge; the family certificate declarations move to `Certification/IVP/TaylorKernel.lean`, keeping their names. Example81.NewAPI preserves the production coefficient and raw-residual theorem statements; its test module moves under `Examples/tests/WL`. No public aliases or facade imports are added. Test projection Q uses the retained WithHead.Q service.


### U51: scalar completeness via the frame

`WeightedScalar.instCompleteSpace` now needs `NormedField` and `CompleteSpace` rather than `NontriviallyNormedField`. Its proof transfers completeness through the existing scalar identity frame with bounds `w m` and `(w m)⁻¹`; no extra instance or alias is introduced. The API-copy gate checks a complete trivially normed field as well as ℝ and ℂ.

The finite-p LiftBound extension, generator computation, uniqueness, pointwise bounds and kernel/Schur identification now use `NormedField` with completeness only where a limit is constructed. The six operator-norm faces retain `NontriviallyNormedField`; the separate reverse implication from unconditional to absolute summability retains `RCLike`. Matrix.Continuous and Chebyshev.Galerkin explicitly import their finite-dimensional continuity interface, which no longer arrives through scalar completeness.

## Isolated-copy U10 retirement — 2026-10-19

Earlier migration rows remain provenance, not an inventory of the current copy.

| Old family | Disposition | Capability removed from this copy | Recovery |
| --- | --- | --- | --- |
| `Analysis/SequenceSpace/Fourier`, `Applications/Fourier`, `Algebra/Ring/HeadTailIdentities`, `Operators/HeadTail`, FZ tests | Archived to probe; no replacement alias | ℓ¹ exact finite-window/attainment and Γ semilinear defect calculus, head-tail identities | `../probes/records/U10_retired_20261019/` |
| `Algebra/Rees/Laurent` and RS tests | Retired, no replacement | Filtered Laurent/Rees family, Euler/Γ and finite-core diagonal specialization calculus | Same source/type/axiom archive |

The Fourier ℓ² replacement is a different operator-bound route, not a claim that these exact ℓ¹ capabilities are equivalent or superseded mathematically. Re-entry requires a concrete consumer and a fresh minimality review. Five root import edges were removed; essential classical example paths are preserved. No LIVE source changed; ReferenceBook compatibility is deferred.

## Isolated-copy Fourier ℓ² integration — 2026-10-19

| Source service | Current home | Disposition |
| --- | --- | --- |
| Accepted scratch Module and Schur action/diagonal/Laurent faces | `WeightedLp/Module`, `Operators/Schur` | Restore only the consumed services; preserve the weaker M0 frames |
| CF0–CF4 bilateral product, return map, shared norm split and defect | `WeightedLp/Bilateral/*`, `Operators/{TailDiagonal,HeadProj,TailDefect}` | Selected structural services, no ℓ² convolution algebra |
| Scratch `Fourier/LinearDefect` four action faces | `Fourier/ConvolutionAction` | Module rename; four public names unchanged; no forwarding alias |
| Scratch Chebyshev ψ1 helper | `WeightedLp/Operators/TailDiagonal` | Pure real summability/majorant at the neutral owner; no Chebyshev tail import |
| Scratch Schur `matrixOf` | `WeightedLp/Operators/FiniteBlock` | Exact physical coefficient definition restored as a genuine consumer dependency; generic normed-field frame |
| CF5a.1 finite matrix/leakage | `WeightedLp/Operators/FiniteBlock` | Composition before modulus; existing-arrow norm bound no longer assumes scalar completeness |
| CF5a.2/CF5b Duffing coefficient endpoint | `Examples/Fourier/Duffing/{IkData,Numbers,Algebra,Certificate}` | Namespace `FourierDuffing`, numerical namespace `.Numbers`, terminal namespace `.Certificate`; four coefficient endpoints, no C² reconstruction |
| Phantom forcing parameter of the head `Cert` | `FourierDuffing.Cert c₁ c₂ N ν` | c₃ removed only from this structure; retained in forcing, residual hypotheses and equation |

Exact selected-head provenance and parent repairs are recorded under
`exterior/tmp/lp_api_campaign_20261017/codex/W2_INTEGRATION_v1/` at the workspace root.
The old ℓ¹/Rees stack remains in the recoverable U10 archive; its exact-norm capabilities are
not claimed to be interchangeable with the ℓ² operator upper bounds. The M0 Taylor witness
chains remain explicit tests pending their production-consumer decision.

M1 facade correction: the generic `Operators/LiftBound` contract remains SHIP-PENDING U37a outside the shipped root, as required by MERGE_EXECUTION_PLAN §1.3/D10. The Fourier chain consumes the independent Schur producer and weighted ℓ¹ algebra action; no artificial liftCLM edge is inserted.

## M1 fix-forward — direct series and retained specifications (2026-10-19)

- Removed `Fourier.L`, `Fourier.coeff_L`, `Fourier.norm_L_le` and the consumer's
  `symbolAction₀_eq_L` round trip. `ConvolutionAction` supplies geometric moderation only.
- Renamed `coeff_incl_L`, `prodCLM_eq_incl_L`, `two_smul_prodCLM_eq_incl_L` to their
  `*_symbolAction₀` names and stated them directly on the operator series; no aliases.
- Moved `coeff_sum` and `coeff_sum_single` from LiftBound to Carrier, with their original
  arbitrary-p NormedField statements. FiniteBlock's duplicate `coeff_finset_sum_single` is retired.
- Moved `dense_span_single` and the three p=∞ boundary faces to LiftBound, outside the root
  while the generic contract is pending. The boundary is a contract condition, not a p=∞ consumer.
- Moved `norm_kernelCLM_two_le` and `schurBound_weightedScalar_iff` into Taylor/TailKernel,
  preserving its pending D6 consumers; NormBounds now imports the owning module.
- Parked the named unused wrapper/producer faces, including the diagonal Schur trio, in the
  exact before/span archives under W2_INTEGRATION_v1/M1_FIX_v1. Per-name actions and replacements
  are in CORE/DECLARATION_DISPOSITIONS.json, CONSUMER/REMOVED.json and NAME_MAP.json.
- The complete Module lift remains a contract of `symbolAction₀` under submultiplicativity,
  with F=0 where no actual endpoint reaches it. It is not counted as a synthetic consumer gain.
- Weakened both Quadratic Lipschitz bounds to NontriviallyNormedField + CompleteSpace, with
  unchanged numerical bounds. The four closed Duffing statements, numerical data and radii are unchanged.

## Early U37a — production kernel-column route (isolated-copy migration record)

| Before | After | Disposition |
|---|---|---|
| Certification/IVP/TaylorKernel F6 | Certification/IVP/Taylor, same retained FQNs | Real move; staging owner retires only after production/AllGenerated pass; no shim |
| StdIVPData column/kernel assembly copies | Z₁_le_of_pairBound and its private sign helper | Both old bound statements use one assembly; no third proof copy |
| colSupQ_nonneg / kerColMaxQ_nonneg | Exact source recovery spans | Unused after assembly replacement; private pair-bound sign test supplies the needed sign |
| ChecksZ₁By .column → ChecksZ₁col/Z₁col_sound | ChecksZ₁ker/Z₁ker_sound | CHANGED-SUBST; no unconditional nonpositive-weight equivalence claim |
| Example81.Cert.z1_checks / Z₁_le_exact | Same names; kernel predicate/soundness | Production statements/data/Y₀ proof unchanged; original630 pin classification remains an execution gate |
| Tests.TY.all81 / main81 | Same active test and generic call | Generated predicate substitution recorded; endpoint type preserved |
| Examples/tests/WL/Example81L1NewAPI | Real production Certificate and active AllGenerated | Retire duplicate only after validation; recoverable source/statement controls, no lower-axiom Y₀ adoption claim |

The original630 baseline and old frozen controls are immutable. Generic C1/C2/p=∞ controls
remain independently checked. The D6 ℓ² Taylor chain remains pending; the old column/Omega
capabilities are not retired wholesale. The candidate retirement actions are not execution
receipts; parent records the actual before/after generation and per-theorem axiom result.

The private `z1_checks` implementation row is classified as CHANGED-SUBST: the executed census checks 629 unchanged saved types and one evidence-only transport of that private row to its original saved type, with all 630 original axiom sets unchanged. This is not a claim of 630 direct definitional type preservations. The original oracle and failed resource-limit runs remain immutable. The transport is not in the library. Complete declaration comparison covers 222 declarations in five current owners, with the seven-to-five owner/retirement mapping explicit. The recovery and post-retirement validation records are under `codex/W2_INTEGRATION_v1/EARLY_U37A_v1/` in the local campaign evidence.

## Post-U37a M1-PARK successor (scoped migration)

| Before | After | Disposition |
|---|---|---|
| Carrier.invWeightSeq / norm_apply_invWeightSeq / norm_equiv_inv_weight | Operators/LiftBound, same FQNs | Exact move of the witness and necessary norm support for the generic finite-p boundary; no alias |
| Carrier.invWeightSeq_apply / coeff_invWeightSeq | Recoverable exact source/type record | Unused coordinate views parked under F1 |
| TailDiagonal.norm_tailDiagInf_eq and its exclusively used attainment support | Recoverable exact source/type record | Proved in the frozen records; parked from shipped API under N-a |
| TailDiagonal.norm_tailDiagInf_le and its construction/coordinate/upper-bound support | Same declarations and proofs | Actual Fourier upper-bound route unchanged |

This supersedes the earlier exact-attainment contract/support disposition only. Historical
packets, probes, audit tables and FINAL_FIX1.json retain their original bytes; consult the
separate M1_PARK successor status note. No numerical data, upper bound, physical endpoint or
U37a proof route is changed by this migration.


## U32 — one realization chain from a proved evaluator bound

The generic chain takes `C : NNReal` and a proved uniform bound for the existing evaluation CLM. The default and contractive polynomial sockets select bounds 2 and 1 internally. The canonical coefficient witness also supplies the analytic socket.

| Before | After | Disposition |
|---|---|---|
| `ChebyshevIVP.eval_traj_in_closedBall` | `ChebyshevIVP.eval_traj_in_closedBall_of_evalBound` | Merged into the generic evaluator-bound service; existing polynomial socket statements retained |
| `ChebyshevIVP.eval_traj_in_closedBall_of_two_le` | `ChebyshevIVP.eval_traj_in_closedBall_of_evalBound` | Merged into the generic evaluator-bound service; existing polynomial socket statements retained |
| `ChebyshevIVP.StdChebIVPData.x_sol_mem_closedBall` | `ChebyshevIVP.StdChebIVPData.x_sol_mem_closedBall_of_evalBound` | Merged into the generic evaluator-bound service; existing polynomial socket statements retained |
| `ChebyshevIVP.StdChebIVPData.x_sol_mem_closedBall_of_two_le` | `ChebyshevIVP.StdChebIVPData.x_sol_mem_closedBall_of_evalBound` | Merged into the generic evaluator-bound service; existing polynomial socket statements retained |
| `ChebyshevIVP.StdChebIVPData.x_sol_isSolution` | `ChebyshevIVP.StdChebIVPData.x_sol_isSolution_of_evalBound` | Merged into the generic evaluator-bound service; existing polynomial socket statements retained |
| `ChebyshevIVP.StdChebIVPData.x_sol_isSolution_of_two_le` | `ChebyshevIVP.StdChebIVPData.x_sol_isSolution_of_evalBound` | Merged into the generic evaluator-bound service; existing polynomial socket statements retained |
| `ChebyshevIVP.StdChebIVPData.solution_eq_canonical` | `ChebyshevIVP.StdChebIVPData.solution_eq_canonical_of_evalBound` | Merged into the generic evaluator-bound service; existing polynomial socket statements retained |
| `ChebyshevIVP.StdChebIVPData.solution_eq_canonical_of_two_le` | `ChebyshevIVP.StdChebIVPData.solution_eq_canonical_of_evalBound` | Merged into the generic evaluator-bound service; existing polynomial socket statements retained |
| `ChebyshevIVP.StdChebIVPData.solution_existsUnique` | `ChebyshevIVP.StdChebIVPData.solution_existsUnique_of_evalBound` | Merged into the generic evaluator-bound service; existing polynomial socket statements retained |
| `ChebyshevIVP.StdChebIVPData.solution_existsUnique_of_two_le` | `ChebyshevIVP.StdChebIVPData.solution_existsUnique_of_evalBound` | Merged into the generic evaluator-bound service; existing polynomial socket statements retained |

The ten generic-core names above are replaced without aliases. `RadiiPolynomial.l1Chebyshev.norm_evalAtCLM_le_of_two_le` exposes the existing sharp pointwise bound as a norm bound for the same CLM. `ChebyshevIVP.StdChebIVPData.exists_canonical_solution_of_compPoly_of_evalBound` derives polynomial structural obligations once for the three retained sockets. The five Example1421 endpoints, coefficient data, radii and competitor class are preserved; the two example source files are unchanged. Execution, actual proof-use and trust evidence: `exterior/tmp/lp_api_campaign_20261017/codex/W2_INTEGRATION_v1/U32_v1/`.


### U32 migration follow-up — explicit witness and default-radius service

The retired `StdChebIVPData.solution_existsUnique` maps to `solution_existsUnique_of_evalBound`, whose conclusion is now `∃ xTilde, IsSolution … (x_sol xTilde) ∧ …` rather than `∃ g, IsSolution … g ∧ …`. A former default caller supplies `C = 2` with `l1Chebyshev.norm_evalAtCLM_le`. The retired `solution_existsUnique_of_two_le` maps to the same new canonical-witness conclusion, supplying `C = 1` with `l1Chebyshev.norm_evalAtCLM_le_of_two_le hν`.

The `C = 2` socket is retained for the preserved default `Example1421.Cert.main_solution_existsUnique` radius `2 * (‖abar‖ + r)`. Its retention does not establish an intermediate-weight production consumer.


## U15a — retire transport demonstrations and their two Example1421 residues

The following 42 original census roots are RETIRED without replacement. Exact whole source files remain recoverable in the linked archive; [current complete types, raw Names and axioms](../probes/records/U15a_kappa_demo_roots42/evidence/CAPTURE42.jsonl) are pinned in the U15a record. Original ordinals below are zero based and retained without renumbering survivors.

This step removes KappaToy's native-versus-transport comparison and TwinTransport's generic κ-budget/scalar-collapse demonstrations, plus the two residues used only by TwinTransport. Generic non-isometric repricing in Core/Transport remains present pending the separate U15b disposition. No isometric replacement of that capability is claimed. Re-entry requires a concrete consumer and reviewed capability case.

| Original ordinal | Module | Exact original root | Disposition | Replacement | Recovery |
|---:|---|---|---|---|---|
| 58 | `RadiiPolynomial.Examples.IVP.Chebyshev.Example1421.Certificate` | `Example1421.Cert.margin_clears_gate` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/IVP/Chebyshev/Example1421/Certificate.lean) |
| 67 | `RadiiPolynomial.Examples.IVP.Chebyshev.Example1421.Algebra` | `Example1421.G_diff` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/IVP/Chebyshev/Example1421/Algebra.lean) |
| 403 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.A` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 404 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.Adag` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 405 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.F'` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 406 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.bside_accepts_half` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 407 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.c` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 408 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.f` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 409 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.f_xBar` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 410 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.fderiv_at_xBar` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 411 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.fderiv_f` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 412 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.fderiv_f_affine` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 413 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.gate_rejects_half` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 414 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.hAinj` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 415 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.hAnorm` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 416 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.hY₀` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 417 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.hZ₀` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 418 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.hZ₁` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 419 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.hZ₂` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 420 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.hasFDerivAt_f` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 421 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.hdiff` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 422 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.hsquare` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 423 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.hα` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 424 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.hβ` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 425 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.instFactLeRealOfNatToRealν₂` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 426 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.instFactLtRealOfNatToRealν₂` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 427 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.kdata` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 428 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.kdata_checks` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 429 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.leftMul_one` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 430 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.transported_existsUnique` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 431 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.u` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 432 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.xBar` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 433 | `RadiiPolynomial.Examples.Transport.KappaToy` | `KappaToy.ν₂` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 434 | `RadiiPolynomial.Examples.Transport.TwinTransport` | `TwinTransport.finOneCollapse` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/TwinTransport.lean) |
| 435 | `RadiiPolynomial.Examples.Transport.TwinTransport` | `TwinTransport.norm_collapse_le` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/TwinTransport.lean) |
| 436 | `RadiiPolynomial.Examples.Transport.TwinTransport` | `TwinTransport.norm_collapse_symm_le` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/TwinTransport.lean) |
| 437 | `RadiiPolynomial.Examples.Transport.TwinTransport` | `TwinTransport.twin_scalar_certificate` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/TwinTransport.lean) |
| 438 | `RadiiPolynomial.Examples.Transport.TwinTransport` | `TwinTransport.twin_transports` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/TwinTransport.lean) |
| 626 | `RadiiPolynomial.Examples.Transport.KappaToy` | `_private.RadiiPolynomial.Examples.Transport.KappaToy.0.KappaToy.hc` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 627 | `RadiiPolynomial.Examples.Transport.KappaToy` | `_private.RadiiPolynomial.Examples.Transport.KappaToy.0.KappaToy.hx` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 628 | `RadiiPolynomial.Examples.Transport.KappaToy` | `_private.RadiiPolynomial.Examples.Transport.KappaToy.0.KappaToy.hν` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/KappaToy.lean) |
| 629 | `RadiiPolynomial.Examples.Transport.TwinTransport` | `_private.RadiiPolynomial.Examples.Transport.TwinTransport.0.TwinTransport.expandCLM` | RETIRED (κ) | none | [whole source](../probes/records/U15a_kappa_demo_roots42/source/src/RadiiPolynomial/Examples/Transport/TwinTransport.lean) |


## U15b — retain the consumed transport services

The five κ-repricing declarations below are RETIRED without replacement. Their lost service is generic certificate repricing between possibly non-isometric real normed spaces along a supplied commuting square, with bounds `(αY₀, αβZ₀, αβZ₁, αβ²Z₂(β·))`, radius equation `r₀ = βr₁`, target completeness and approximate-inverse injectivity; the margin form uses `β > 0`, and the rational gate proves its numerical premise. Retained metric-isometry zero transport does not replace this repricing service.

The four derivative/Z₂ helpers and linear-isometry convenience face are ARCHIVED to a probe as separate capabilities. The former provide derivative conjugation and local pulled-back Z₂ estimates; the latter supplies a convenience signature over a linear isometry. Re-entry requires a concrete consumer and reviewed capability case. No aliases or new replacement wrappers are introduced.

Complete [old module source](../probes/records/U15b_core_transport/source/src/RadiiPolynomial/Core/Transport.lean) is retained. Current full elaborated types, raw Names, per-declaration axioms and actual generated-owner inventory are bound in the [U15b typed archive](../probes/records/U15b_core_transport/MANIFEST.json) and its [full fourteen-declaration capture](../probes/records/U15b_core_transport/evidence/TRANSPORT.jsonl). The archive records exactly five RETIRED and five ARCHIVED/probe faces; two kept services and two auxiliaries are contextual evidence, with auxiliary compiler ranges explicitly null.

| Exact original declaration | Disposition | Replacement | Recovery |
|---|---|---|---|
| `RadiiPolynomial.transported_radii_identity` | RETIRED (κ) | none | [whole source](../probes/records/U15b_core_transport/source/src/RadiiPolynomial/Core/Transport.lean) |
| `RadiiPolynomial.transport_radii_polynomial` | RETIRED (κ) | none | [whole source](../probes/records/U15b_core_transport/source/src/RadiiPolynomial/Core/Transport.lean) |
| `RadiiPolynomial.transport_radii_polynomial_of_margin` | RETIRED (κ) | none | [whole source](../probes/records/U15b_core_transport/source/src/RadiiPolynomial/Core/Transport.lean) |
| `RadiiPolynomial.gateQ` | RETIRED (κ) | none | [whole source](../probes/records/U15b_core_transport/source/src/RadiiPolynomial/Core/Transport.lean) |
| `RadiiPolynomial.gateQ_sound` | RETIRED (κ) | none | [whole source](../probes/records/U15b_core_transport/source/src/RadiiPolynomial/Core/Transport.lean) |
| `RadiiPolynomial.hasFDerivAt_conj` | ARCHIVED to probe | none | [whole source](../probes/records/U15b_core_transport/source/src/RadiiPolynomial/Core/Transport.lean) |
| `RadiiPolynomial.fderiv_conj_apply` | ARCHIVED to probe | none | [whole source](../probes/records/U15b_core_transport/source/src/RadiiPolynomial/Core/Transport.lean) |
| `RadiiPolynomial.Z₂_transport` | ARCHIVED to probe | none | [whole source](../probes/records/U15b_core_transport/source/src/RadiiPolynomial/Core/Transport.lean) |
| `RadiiPolynomial.Z₂_transport_lip` | ARCHIVED to probe | none | [whole source](../probes/records/U15b_core_transport/source/src/RadiiPolynomial/Core/Transport.lean) |
| `RadiiPolynomial.existsUnique_zero_transport_linear` | ARCHIVED to probe | none | [whole source](../probes/records/U15b_core_transport/source/src/RadiiPolynomial/Core/Transport.lean) |

`RadiiPolynomial.rp_transport_local` and `RadiiPolynomial.existsUnique_zero_transport` are kept byte-for-byte, together with their existing importers. Core.Transport owns no original630 census root, so this adds no original-root retirements to U15a's `587 direct + 1 existing private transport + 42 RETIRED` classification. Actual generated-name changes are recorded separately after compiler enumeration.


## U39/K13 — archive inverse T↔U transport and split monotonicity

The exact ChebyshevFromU, BorderedTransport and SplitMonotonicity sections are archived as probes. This removes inverse series/membership/linearity/norm/round-trip and conditioning services, the bordered Banach linear equivalence and compatibility formulas, and the two packaged split-monotonicity/override faces. The retained one-way conversion, integration, physical-carrier equivalence and isometric zero transport do not replace these capabilities. Re-entry requires a concrete consumer and reviewed capability case. No replacement wrapper or alias is added.

The [typed archive](../probes/records/U39_transport_monotonicity/MANIFEST.json), [exact63 compiler-name joins](../probes/records/U39_transport_monotonicity/evidence/SELECTED63.json) and [full297-owner context](../probes/records/U39_transport_monotonicity/evidence/STRUCTURED_INDEX.json) preserve the63 explicit source commands (47 public,16 private) and complete types, raw Names, kinds, axioms and compiler ranges. Only those63 source commands have the direct archive disposition. Unselected context comprises 129 compiler-ranged retained source records and 105 records without compiler ranges. The completed AFTER global checks found 47 unchanged observed profiles and 58 absent names. The absent names were assessed as removed-section support: 32 have stored-value paths from removed source declarations, 5 have reverse type/value paths to removed source declarations, and 21 have qualified compiler-support inferences from simp preprocessing or elaboration. The last group is an explicitly qualified inference, not a stored dependency-path claim; range absence alone establishes neither generation nor survival. Eleven simp registrations and the section-local Fact instance leave with their complete sections.

| Source owner and original head line | Actual compiler declaration | Disposition | Typed/source recovery |
|---|---|---|---|
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:270` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Bordered.0.RadiiPolynomial.borderedToU_mem` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:307` | `RadiiPolynomial.borderedToU` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:310` | `RadiiPolynomial.borderedToU_toSeq` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:314` | `RadiiPolynomial.borderedToU_add` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:320` | `RadiiPolynomial.borderedToU_smul` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:329` | `RadiiPolynomial.borderedToU_norm_le` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:391` | `RadiiPolynomial.borderedToU_CLM` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:400` | `RadiiPolynomial.borderedToU_CLM_apply` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:406` | `RadiiPolynomial.borderedToU_nonnegRestrict` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:420` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Bordered.0.RadiiPolynomial.borderedFromU_fiber_le` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:440` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Bordered.0.RadiiPolynomial.borderedFromU_mem` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:452` | `RadiiPolynomial.borderedFromU` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:457` | `RadiiPolynomial.borderedFromU_toSeq` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:462` | `RadiiPolynomial.borderedFromU_add` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:472` | `RadiiPolynomial.borderedFromU_smul` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:485` | `RadiiPolynomial.nonnegRestrict_chebyshevFromU` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:493` | `RadiiPolynomial.borderedFromU_norm_le` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:505` | `RadiiPolynomial.borderedToU_borderedFromU` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:513` | `RadiiPolynomial.borderedFromU_borderedToU` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:539` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.Bordered.0.RadiiPolynomial.fact_one_le_of_one_lt` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:544` | `RadiiPolynomial.borderedFromU_CLM` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:552` | `RadiiPolynomial.borderedFromU_CLM_apply` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:557` | `RadiiPolynomial.borderedTU_equiv` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:562` | `RadiiPolynomial.borderedTU_equiv_apply` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:565` | `RadiiPolynomial.borderedTU_equiv_symm_apply` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:568` | `RadiiPolynomial.coe_borderedTU_equiv` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:571` | `RadiiPolynomial.coe_borderedTU_equiv_symm` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:584` | `RadiiPolynomial.borderedToU_CLM_norm_mul_borderedFromU_CLM_norm_le` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean:596` | `RadiiPolynomial.norm_borderedTU_equiv_mul_norm_symm_le` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/Bordered.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:372` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion.0.RadiiPolynomial.one_lt_nu` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:373` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion.0.RadiiPolynomial.one_le_nu` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:376` | `RadiiPolynomial.invsq_nonneg` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:378` | `RadiiPolynomial.one_lt_nusq` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:381` | `RadiiPolynomial.invsq_lt_one` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:385` | `RadiiPolynomial.summable_abs_toSeq_shift` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:393` | `RadiiPolynomial.summable_toSeq_shift` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:398` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion.0.RadiiPolynomial.chebyshevFromU_seq` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:403` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion.0.RadiiPolynomial.chebyshevFromU_seq_ofNat` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:407` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion.0.RadiiPolynomial.chebyshevFromU_seq_negSucc` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:413` | `RadiiPolynomial.fromU_row_le` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:438` | `RadiiPolynomial.fromU_prod_summable` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:459` | `RadiiPolynomial.fromU_marginal_summable` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:468` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion.0.RadiiPolynomial.chebyshevFromU_fiber_le` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:487` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion.0.RadiiPolynomial.chebyshevFromU_memℓp` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:511` | `RadiiPolynomial.chebyshevFromU` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:517` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion.0.RadiiPolynomial.chebyshevFromU_toSeq` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:521` | `RadiiPolynomial.chebyshevFromU_toSeq_natCast` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:526` | `RadiiPolynomial.chebyshevFromU_toSeq_negSucc` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:530` | `RadiiPolynomial.chebyshevFromU_add` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:549` | `RadiiPolynomial.chebyshevFromU_smul` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:573` | `RadiiPolynomial.chebyshevToU_chebyshevFromU` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:598` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion.0.RadiiPolynomial.summable_toRealSeq_even` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:610` | `RadiiPolynomial.chebyshevFromU_chebyshevToU_toSeq` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:636` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion.0.RadiiPolynomial.chebyshevFromU_elem_negSucc` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:641` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion.0.RadiiPolynomial.chebyshevFromU_elem_natCast_le` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:648` | `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.UConversion.0.RadiiPolynomial.chebyshevFromU_norm_support` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:661` | `RadiiPolynomial.chebyshevFromU_norm_le` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:708` | `RadiiPolynomial.chebyshevFromU_CLM` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:716` | `RadiiPolynomial.chebyshevFromU_CLM_apply` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:728` | `RadiiPolynomial.chebyshevToU_CLM_norm_mul_chebyshevFromU_CLM_norm_le` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean:743` | `RadiiPolynomial.chebyshevToU_CLM_comp_chebyshevFromU_CLM` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Analysis/SequenceSpace/Chebyshev/UConversion.lean) |
| `RadiiPolynomial/Core/Theorem.lean:907` | `RadiiPolynomial.generalRadiiPolynomial_anti_bounds` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Core/Theorem.lean) |
| `RadiiPolynomial/Core/Theorem.lean:921` | `RadiiPolynomial.general_radii_polynomial_theorem_of_le` | ARCHIVED to probe | [type/raw](../probes/records/U39_transport_monotonicity/evidence/OWNERS.jsonl); [whole source](../probes/records/U39_transport_monotonicity/source/src/RadiiPolynomial/Core/Theorem.lean) |


## NORMONE — use the generic normalized algebra API

| Old declaration | Canonical mathematical service | Disposition and recovery |
|---|---|---|
| `RadiiPolynomial.l1Weighted.norm_one_eq` | `norm_one` via the existing `lpOneAlg.instNormOneClass` | Retired duplicate hand-tsum lemma. [Actual type and axioms](../probes/records/NORMONE_generic_norm/evidence/OWNERS.jsonl); [whole source](../probes/records/NORMONE_generic_norm/source/src/RadiiPolynomial/Analysis/SequenceSpace/Geometric/Basic.lean). |
| `RadiiPolynomial.l1Weighted.norm_algebraMap` | Mathlib `norm_algebraMap'` on `l1Weighted ν`, for every `ν : PosReal` | Retired specialized wrapper. [Actual type and axioms](../probes/records/NORMONE_generic_norm/evidence/OWNERS.jsonl); [whole source](../probes/records/NORMONE_generic_norm/source/src/RadiiPolynomial/Analysis/SequenceSpace/Geometric/Basic.lean). The MvPolynomial constant-norm proof calls the generic theorem directly at its unchanged statement. |

The [recovery record](../probes/records/NORMONE_generic_norm/MANIFEST.json) preserves both whole owner sources, the two actual old typed rows and the complete 166-declaration BEFORE context (140 geometric and 26 polynomial); the other 164 records are contextual, including the retained constant-norm theorem. The [executed BEFORE checks](../probes/records/NORMONE_generic_norm/evidence/PARENT_CAPTURE_CHECKS.json) record 4,694 actual and predicted imports, 44,378 unchanged artifact pins and 224 unchanged source/config/doc pins. The [generic proof probe](../probes/records/NORMONE_generic_norm/evidence/BEFORE_PROBE_RESULT.json) passed for all positive radii and explicitly for ν = 1/2. Its six proof roots exclude both retired geometric Names from their actual stored proof/type dependency closure and use `propext`, `Classical.choice` and `Quot.sound`.

The old names retire while the mathematical norm-one and norm-map services remain supplied by the canonical generic API, with no new premise, alias, wrapper or instance. The deferred Ch08 call is `ReferenceBook/Ch08/Sec2Theorem.lean:341`, in private `SystemBoundsPoly.norm_aeval_monomial_le`; its source trail is Hessian/ζ majorant → Lemma 8.2.10 → Theorem 8.2.2 → Theorem 8.2.11. The replacement is `rw [_root_.norm_algebraMap', Real.norm_eq_abs]`; RBC source is unchanged. `algebraMap_apply`, the ℚ action and the distinct generic `lpOneAlg.norm_one_eq` remain unchanged. Neither removed helper owns an original 630-census root.

The later [NORMONE AFTER source status](../probes/records/NORMONE_generic_norm/CURRENT.md) and [acceptance evidence](../probes/records/NORMONE_generic_norm/AFTER_ACCEPTANCE.json) record bilateral source acceptance at freeze `0bfa90b9`. The original archive README, MANIFEST and ARCHIVE_ACCEPTANCE remain immutable creation-time records; their earlier AFTER-pending wording is historical. The accepted premises were already minimal and remain unchanged.

## Z₀ example residue — retain the finite-block and family services

| Old declaration | Disposition | Recovery and retained service |
|---|---|---|
| `Example1421.Cert.Z₀_le` (original 630 ordinal 45) | Retired unused example wrapper; no replacement declaration or alias. | [Actual old type and axioms](../probes/records/Z0_example1421_operator_bound/evidence/OWNERS.jsonl); [whole old Certificate source](../probes/records/Z0_example1421_operator_bound/source/src/RadiiPolynomial/Examples/IVP/Chebyshev/Example1421/Certificate.lean). The unchanged `Z₀_finBlockNorm_le`, grid check and family `ChebyshevIVP.StdChebIVPData.Z₀_le` still supply the bound. |

The [recovery record](../probes/records/Z0_example1421_operator_bound/MANIFEST.json) preserves one retirement row, 82 other owner records and five separately labelled endpoint controls. The [executed BEFORE capture checks](../probes/records/Z0_example1421_operator_bound/evidence/PARENT_CAPTURE_CHECKS.json) record 83 actual Certificate declarations (44 with compiler ranges, 39 without), 6,665 actual/predicted imports and 67,130 unchanged artifact pins. Four function/analytic endpoints explicitly pass the retained local finite-block bound; `main_theorem` instead supplies `checksK_data` through `certified_of_checksK`, which reconstructs the same finite-block/operator bound. All numerical data, bounds, radii, endpoint statements and competitor classes are unchanged.

## U31 — one rational block action for Taylor and Chebyshev certificates

| Removed family declaration | Existing canonical service | Recovery |
|---|---|---|
| `IVP.actionQ` | `RadiiPolynomial.blockActionQ` with head columns `fun l j k => A_col l j k.val` and tail `(fun _ n => (n : ℚ)⁻¹)` | [Whole old Taylor source](../probes/records/U31_rational_block_action/source/src/RadiiPolynomial/Certification/IVP/Taylor.lean); [typed recovery](../probes/records/U31_rational_block_action/MANIFEST.json). |
| `ChebyshevIVP.actionQ` | The same `blockActionQ`, with tail `(fun _ n => (2 * (n : ℚ))⁻¹)` | [Whole old Chebyshev source](../probes/records/U31_rational_block_action/source/src/RadiiPolynomial/Certification/IVP/Chebyshev.lean); [typed recovery](../probes/records/U31_rational_block_action/MANIFEST.json). |
| `IVP.StdIVPData.action_eq_actionQ` | Direct `SystemBlockDiagData.action_eq_blockActionQ` in the Taylor Y₀ soundness proof | [Typed/source recovery](../probes/records/U31_rational_block_action/MANIFEST.json). |
| `ChebyshevIVP.StdChebIVPData.action_eq_actionQ` | Direct `SystemBlockDiagData.action_eq_blockActionQ` in the Chebyshev Y₀ soundness proof | [Typed/source recovery](../probes/records/U31_rational_block_action/MANIFEST.json). |

The four duplicate definitions/normalization wrappers retire outright, with no alias, instance or new interface. Reciprocal multiplication equals the old total rational division, including at divisor zero; finite-head indices are unchanged. The existing matrix action and bridge are unchanged. Each family retains its residual interpreter, support window and weighted norm sum; support still uses `N ≤ M`. Matrix and Example1421 Certificate source bytes remain unchanged.

**CHANGED-SUBST, executed:** Independent old/new Y₀ and whole-checker/data-field substitutions were kernel-checked on both BEFORE and AFTER generations. At the fixed Example1421 data, the independent old and canonical new Y₀ computations equal the exact rational `q = a/b`; `q ≤ 10⁻²¹` and rejection at `(a−1)/b < q` were kernel-checked. The original630 AFTER accounting is `583 direct + 3 CHANGED-SUBST + 1 previous original566 transport + 43 retired`. The three substituted original rows are zero-based ordinal 450 (`checksK`), 451 (`checksK_data`) and 460 (`k_Y₀`). All non-Y₀ clauses, numerical inputs, radii, equation/initial value and five Example1421 endpoint statements were preserved. The [canonical AFTER record](../probes/records/U31_rational_block_action/AFTER_ACCEPTANCE.json) records the executed source result; declaration-head equality alone is not its semantic evidence.

The BEFORE original630 accounting was `586 direct + 1 existing private original566 transport + 43 retired`; the executed substitution evidence yields the AFTER split above. The 43 existing retirements and original566 transport retain their identities. The [historical recovery record](../probes/records/U31_rational_block_action/MANIFEST.json) preserves the four actual old types, stored values and axioms, both whole old sources and their object companions, the 381-owner context and 24 controls. The [status guide](../probes/records/U31_rational_block_action/CURRENT.md) separates historical archive publication from later source acceptance. [Executed BEFORE evidence](../probes/records/U31_rational_block_action/evidence/BEFORE_CAPTURE_RESULT.json) records 6,768 actual/predicted imports, 67,669 artifact POST pins and 52,891 recursive trust nodes; [trust facts](../probes/records/U31_rational_block_action/evidence/TRUST_FACTS.json) retain native-axiom context explicitly. The 41 [independent BEFORE controls](../probes/records/U31_rational_block_action/evidence/BEFORE_CONTROLS_RESULT.json) establish old/new action and predicate facts with standard three or fewer axioms; these are distinct from production AFTER verification.


**Required consumer reach:** Production Examples 8.1/8.3 bound Y₀ through `IVP.ivp_Y₀_le` with LeanCert `finsum_bound`, not the exact-ℚ Taylor Y₀ socket. In the reviewed required consumer set, that Taylor socket (`StdIVPDataQ.ChecksY₀`, `Y₀_sound`, `certified_of_checksBy`) is reached only by the selected `Examples/tests/TY/AllGenerated` test (`Tests.TY.main81`); it is calibration/test-only and remains with the agreed later U42b staging together with its test. The shared generic action is justified by Example 14.2.1 production reach. This rider adds no new unit or staging change.

## B1 — canonical replacements and inactive-root omissions (U12/U13/U17/U20/U35e)

| Retired declaration | Canonical mathematical service |
|---|---|
| `IVP.tail_shiftDivN_sum_le` | `RadiiPolynomial.tail_shiftDivN_sum_le`, with the same finite-set tail bound. |
| `MvPolyBridge.CompPoly.Chebyshev.chebDerivativeLipschitzBound_mono` | `MvPolyBridge.CompPoly.Chebyshev.derivativeLipschitzBound_mono`; the Chebyshev radii-monotonicity law, not its base-polynomial counterpart. |
| `MvPolyBridge.CompPoly.norm_sum_mul_pi_le` | `RadiiPolynomial.NormHelpers.norm_sum_mul_pi_le` over any `NonUnitalSeminormedRing` and finite index. |
| `MvPolyBridge.norm_sum_mul_pi_le` | The same generic law at the existing weighted-ℓ¹/Pi types. |
| `RadiiPolynomial.cauchyProduct.ratCast` | `cauchyProduct.map_cauchyProduct (Rat.castHom ℝ)` directly at the coefficient consumer. The Real-only module and its two import edges are removed. |
| `IVP.StdIVPDataQ.weight` | Explicit positive-real subtype `⟨(q.ν_q : ℝ), by exact_mod_cast hpos⟩`; no new public helper. |
| `IVP.StdIVPDataQ.toStd` | Existing `q.toStdIVPData ν hν`, with that explicit subtype and `rfl` for the old default. `ofStd` remains; the round trip `toStdIVPData_ofStd` was deleted at the merge (R-ELAB row below). |

The [recovery record](../probes/records/B1_canonical_replacements/MANIFEST.json) is the typed/source recovery archive for the seven retired names and omitted copy-root bytes. Alias/forward spellings retire without compatibility aliases. The finite-sum consumers use the existing generic law directly; their norms and hypotheses are unchanged. B1's executed BEFORE joins identify the actual weight/default helpers with the preserved old-weight/default constructor bodies. The canonical inline realization was kernel-checked at the captured dependent type after the explicit old-weight substitution, with unchanged axioms; this is a verified transport, not literal preservation of the removed raw head. The original proof-recovery limitations are recorded below.

U13 omits only the inactive copy-root `Makefile`, `lake-manifest.json.disable`, `REFACTORING_LOG.md`, `MARKER_DIFF.txt` and `STMT_DIFF.txt`. Active Lake configuration/package pins, `.gitignore` patterns and the separate checkdecls dependency remain unchanged. The module `Algebra/Convolution/CauchyProductReal.lean` is retired separately under U20. No numerical data, bound, radius or competitor class changes.

Deferred ReferenceBook repoints, without an RBC edit or build gate: `Ch08/Sec2Theorem.lean:516` uses `MvPolyBridge.norm_sum_mul_pi_le`; `Ch10/Sec2BoundsZ2.lean:309,417` uses the CompPoly forward. Each call moves to `RadiiPolynomial.NormHelpers.norm_sum_mul_pi_le` at the same arguments. B1's source and required-consumer checks were executed; the [canonical AFTER record](../probes/records/B1_canonical_replacements/AFTER_ACCEPTANCE.json) binds the accepted source generation and observations. B1's original630 shape partition is `586 ordinary shape pins + 1 previous original566 transport + 43 retired`; its semantic partition is `583 direct + 3 inherited CHANGED-SUBST + 1 previous original566 transport + 43 retired`. The three inherited substitutions retain their exact identities. The two additional auxiliary exits are separately qualified: `toStd._proof_1` has a full captured original proof value; `weight._proof_1` has an independent witness at its exact old positivity type and unchanged axioms, without an original proof-byte identity claim. Both statements and full original source remain recoverable. This wording does not promote the archival BEFORE record into AFTER evidence.

## B2 — recoverable mathematical records (U18/U33/U41/U42a)

The [typed recovery record](../probes/records/B2_staged_services/MANIFEST.json) preserves
original source, full types and stored values where available, actual private/generated
identities and axioms for the services below. Their statements remain mathematical evidence
outside the shipped root. Execution, acceptance, source-generation and row-disposition facts
are recorded in the bound B2 task records; a recovery entry alone does not assert global
unusedness or mathematical irrelevance.

| Slice | Full declaration name outside the shipped root | Mathematical service |
|---|---|---|
| U18 | `RadiiPolynomial.CrossGeometry.real_laurent_character_joukowski_ne_zero` | No real Laurent character kills the Joukowski generator. |
| U18 | `RadiiPolynomial.CrossGeometry.physical_zero_character_has_no_real_extension` | No real continuous Laurent extension of the physical zero character. |
| U18 | `RadiiPolynomial.CrossGeometry.circle_character_restriction` | Complex circle evaluation restricts to physical real evaluation. |
| U18 | `RadiiPolynomial.CrossGeometry.physical_zero_character_has_complex_extension` | Complex Laurent extension above zero at I. |
| U18 | `RadiiPolynomial.CrossGeometry.physical_zero_character_has_second_complex_extension` | Second complex extension above zero at −I. |
| U18 | `RadiiPolynomial.CrossGeometry.complex_restriction_not_injective` | Complex Laurent restriction is not injective. |
| U33 | `MvPolyBridge.norm_fderiv_diff_evalInBanach_of_const_second_pderiv` | Semantic derivative-difference bound from a supplied constant second-derivative table. |
| U33 | `MvPolyBridge.fderiv_diff_zero_of_D₂_zero` | Zero derivative difference for a component with zero supplied table. |
| U33 | `MvPolynomial.totalDegree_pderiv_pderiv_eq_zero` | Second partial derivative has degree zero under degree ≤ 2. |
| U33 | `MvPolynomial.pderiv_pderiv_eq_C_of_totalDegree_le_two` | Second partial derivative is a constant under degree ≤ 2. |
| U42a | `RadiiPolynomial.l1Chebyshev.ext_of_evalLaurentC_circle` | Boundary complex characters separate bilateral elements. |
| U42a | `RadiiPolynomial.l1Chebyshev.ext_of_eventuallyEq_eval` | Local physical determination at ν > 1. |
| U42a | `RadiiPolynomial.CrossGeometry.chebyshevToTaylorAeval_injective` | Injective reverse restriction under its semiMinor gate. |

U18's six countermodel witnesses, U33's four semantic/degree faces and U42a's three
determination/injectivity faces retain their original typed statements and source in that record.
Re-entry requires a concrete consumer of the corresponding mathematical service. The protected
`MvPolynomial.C_ofNat_eq`, `MvPolynomial.totalDegree_pderiv_le` and generic bilinear norm bound
remain library interfaces; no unconsumed Hessian replacement pair was added.

### U41 — finite-fiber carrier and algebra interfaces

| API part | Actual public names represented in recovery |
|---|---|
| Carriers | `RadiiPolynomial.FiniteFiberConvolution`, `RadiiPolynomial.FiniteFiberAddConvolution` |
| Coordinate and atom interfaces | `RadiiPolynomial.FiniteFiberConvolution.ofFun`, `RadiiPolynomial.FiniteFiberConvolution.toFun`, `RadiiPolynomial.FiniteFiberConvolution.coeff`, `RadiiPolynomial.FiniteFiberConvolution.single`, `RadiiPolynomial.FiniteFiberConvolution.ext`; `RadiiPolynomial.FiniteFiberAddConvolution.ofFun`, `RadiiPolynomial.FiniteFiberAddConvolution.toFun`, `RadiiPolynomial.FiniteFiberAddConvolution.coeff`, `RadiiPolynomial.FiniteFiberAddConvolution.single`, `RadiiPolynomial.FiniteFiberAddConvolution.ext` |
| Registered algebra interfaces | `RadiiPolynomial.FiniteFiberConvolution.instSemiring`, `RadiiPolynomial.FiniteFiberConvolution.instRing`, `RadiiPolynomial.FiniteFiberConvolution.instAlgebra`; `RadiiPolynomial.FiniteFiberAddConvolution.instSemiring`, `RadiiPolynomial.FiniteFiberAddConvolution.instRing`, `RadiiPolynomial.FiniteFiberAddConvolution.instAlgebra` |
| Monoid-algebra embedding and range | `RadiiPolynomial.FiniteFiberConvolution.ofMonoidAlgebra`, `RadiiPolynomial.FiniteFiberConvolution.toMonoidAlgebra`, `RadiiPolynomial.FiniteFiberConvolution.mem_rangeS_ofMonoidAlgebra`, `RadiiPolynomial.FiniteFiberConvolution.ofMonoidAlgebraEquivRangeS`; `RadiiPolynomial.FiniteFiberAddConvolution.ofAddMonoidAlgebra`, `RadiiPolynomial.FiniteFiberAddConvolution.toAddMonoidAlgebra`, `RadiiPolynomial.FiniteFiberAddConvolution.mem_rangeS_ofAddMonoidAlgebra`, `RadiiPolynomial.FiniteFiberAddConvolution.ofAddMonoidAlgebraEquivRangeS` |
| Power-series ring equivalences | `RadiiPolynomial.FiniteFiberAddConvolution.toPowerSeriesRingEquiv`, `RadiiPolynomial.FiniteFiberAddConvolution.toMvPowerSeriesRingEquiv` |
| Computation, inverse and scalar laws for the equivalences | `RadiiPolynomial.FiniteFiberAddConvolution.toPowerSeriesRingEquiv_apply`, `RadiiPolynomial.FiniteFiberAddConvolution.coeff_toPowerSeriesRingEquiv`, `RadiiPolynomial.FiniteFiberAddConvolution.coeff_toPowerSeriesRingEquiv_symm`, `RadiiPolynomial.FiniteFiberAddConvolution.toPowerSeriesRingEquiv_smul`; `RadiiPolynomial.FiniteFiberAddConvolution.coeff_toMvPowerSeriesRingEquiv`, `RadiiPolynomial.FiniteFiberAddConvolution.coeff_toMvPowerSeriesRingEquiv_symm`, `RadiiPolynomial.FiniteFiberAddConvolution.toMvPowerSeriesRingEquiv_smul` |

The [complete typed recovery inventory](../probes/records/B2_staged_services/evidence/DECLARATION_RECORD_INDEX.json)
includes all 389 actual declarations of the three U41 library owners, with full Names and raw-row
locators. Source/compiler joins identify 145 named API entries: 76 written public source commands,
67 actual `to_additive` translations selected at their source attributes, and the two intentional
`ext_iff` API companions. Their module split is 108 carrier/algebra, 28 monoid-algebra and 9 power-series
entries. This is source-facing named API coverage, not an exhaustive public-status classification
of generated or anonymous declarations. Proof auxiliaries and the other 244 rows retain their
context roles. The three exclusive CV tests remain in the full recovery context. Re-entry requires
a concrete wrapper/embedding/ring-equivalence consumer; the generic raw finite convolution core,
Cauchy product and PowerSeries linear bridge remain library services.

There is no replacement alias, deprecation layer or newly invented generic Hessian interface.
Geometric.AnalyticExt, Chebyshev reverse-map construction/evaluation/algebra/generator faces,
the required classical/function/complex-time endpoints, fixed tests and four Duffing roots
including reality retain their interfaces. No Duffing C² reconstruction or hint gain is claimed.


## B3 — canonical finite-Pi spaces and polynomial evaluation (U16/U22/U29)

The generic state-space spellings `RadiiPolynomial.X` and `RadiiPolynomial.Y` are
replaced by their finite-Pi types. `RadiiPolynomial.XL1 ν L` remains the concrete
abbreviation `Fin L → l1Weighted ν`; its coefficient and block-operator services
remain. The six shortcut instances `instXL1Ring`, `instXL1CommRing`,
`instXL1NormedRing`, `instXL1NormOneClass`, `instXL1Algebra` and
`instXL1NormedAlgebra` give way to the existing Pi instances. The norm-one instance
still needs a nonempty index. The four generic norm services retain their original
real normed-space hypotheses; no completeness or stronger weight premise is added.

`ChebyshevIVP.clm_apply_eq_sum` is replaced at its two callers by the component
identity from `ContinuousLinearMap.sum_comp_single`. The implementation helpers
`zmax`, `zmin`, `zsum` and the dependent proof `zsum_eq` become private in the same
module. `list_range_map_sum`, `evalFast`, `evalFast_eq` and `evalChebFast` retain their
services. The clipped exact-rational algorithm and its support premise are unchanged.
The sole `ball_lt_add` call uses the local natural-number split in Example14.2.1.

`MvPolyBridge.evalInBanach p a` is replaced by `MvPolynomial.aeval a p`, with the
argument order reversed. The consumed semantic services have the following names.

| Previous name | Canonical name |
|---|---|
| `MvPolyBridge.toSeq_evalInBanach_of_coeffs` | `MvPolyBridge.toSeq_aeval_of_coeffs` |
| `MvPolyBridge.fderiv_evalInBanach` | `MvPolyBridge.fderiv_aeval` |
| `MvPolyBridge.fderiv_diff_evalInBanach` | `MvPolyBridge.fderiv_diff_aeval` |
| `MvPolyBridge.toSeq_fderiv_evalInBanach` | `MvPolyBridge.toSeq_fderiv_aeval` |
| `MvPolyBridge.norm_evalInBanach_sub_le` | `MvPolyBridge.norm_aeval_sub_le` |
| `MvPolyBridge.norm_fderiv_evalInBanach_le` | `MvPolyBridge.norm_fderiv_aeval_le` |
| `MvPolyBridge.norm_fderiv_diff_evalInBanach_bilinear` | `MvPolyBridge.norm_fderiv_diff_aeval_bilinear` |
| `MvPolyBridge.compPoly_evalBanach_eq_evalInBanach` | `MvPolyBridge.compPoly_evalBanach_eq_aeval` |
| `MvPolyBridge.CompPoly.sum_norm_evalInBanach_pderiv_le` | `MvPolyBridge.CompPoly.sum_norm_aeval_pderiv_le` |

The C/X/add/mul/neg/sub and partial-of-X forwards use the existing `aeval` and map
laws. The constant-norm formula uses `MvPolynomial.aeval_C` and
`norm_algebraMap'`; differentiability uses `MvPolynomial.hasFDerivAt_aeval` and its
`differentiableAt` consequence. The unused CompPoly algebra-evaluation forward uses
`MvPolyBridge.CompPoly.evalAlg_eq_aeval` directly. The retained rational
CompPoly-to-Banach bridge remains rational; it introduces no real-coefficient
mapping or scalar-tower premise. The pointwise bilinear derivative bound retains
its hypothesis at the supplied pair.

Eight specialized simp registrations leave with their forwards. Canonical formulas
and consumer elaboration are separate from a claim that every former `simp` call
behaves identically. The typed recovery record at
`../probes/records/B3_canonical_pi_aeval/` records old source, exact compiler Names,
old and normalized types, captured values, and trust evidence. The executed disposition
is bound by `../probes/records/B3_canonical_pi_aeval/AFTER_ACCEPTANCE.json`. A source name
map alone is not a compiler census or an unusedness proof.

ReferenceBook Ch08 uses of the generic state-space spelling in `Sec2`, `Sec2Theorem`,
`Sec5Taylor` and `Sec5Verified` are deferred repoints; no ReferenceBook file or published
theorem is edited by this copy-only migration.

## U25 — one universal geometric evaluator

The independent real algebra-hom construction is retired. `l1Weighted.aeval_of_norm_le`
is the bounded arrow; its real series identity is proved first, and `eval_mul` is derived
from its multiplication law. The earlier planned-revamp entry is historical.

At installation, [`AFTER_ACCEPTANCE.json`](../probes/records/U25_universal_geometric_evaluation/AFTER_ACCEPTANCE.json) binds the accepted source/object generation, executed owner/consumer and independent model/data checks, and declaration dispositions.

| Source head | Disposition and retained service |
| --- | --- |
| `RadiiPolynomial.l1Weighted.eval_mul_trunc` | No retained service requires the finite truncation detour; exact eval_mul remains via canonical map_mul. |
| `RadiiPolynomial.l1Weighted.evalAlgHom'` | Retired captured BEFORE construction `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.evalAlgHom'` and its captured auxiliaries `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.evalAlgHom'._proof_1`, `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.evalAlgHom'._proof_2`, `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Evaluation.0.RadiiPolynomial.l1Weighted.evalAlgHom'._proof_3`. No replacement private construction; the canonical arrow is `l1Weighted.aeval_of_norm_le ν z hz`. |
| `RadiiPolynomial.l1Weighted.evalContinuousAlgHom` | l1Weighted.aeval_of_norm_le ν z hz |
| `RadiiPolynomial.l1Weighted.evalContinuousAlgHom_apply` | New l1Weighted.aeval_of_norm_le_apply_real, independently proved from series FIRST. |
| `RadiiPolynomial.l1Weighted.eval_CLM` | (l1Weighted.aeval_of_norm_le ν z hz).toContinuousLinearMap |
| `RadiiPolynomial.l1Weighted.eval_CLM_apply` | ContinuousAlgHom.coe_toContinuousLinearMap plus new real series bridge. |
| `RadiiPolynomial.l1Weighted.evalAlgHom` | (l1Weighted.aeval_of_norm_le ν z hz).toAlgHom |
| `RadiiPolynomial.l1Weighted.evalAlgHom_apply` | Canonical toAlgHom coercion plus new real series bridge. |
| `RadiiPolynomial.l1Weighted.evalContinuousAlgHom_gen` | Existing aeval_of_norm_le_gen; convert l1Weighted.single using single_eq_lpOneAlg_single when necessary. |
| `RadiiPolynomial.l1Weighted.aeval_eq_evalContinuousAlgHom` | No old hom remains. The new coordinate series bridge does not use old uniqueness/hom proofs. |
| `RadiiPolynomial.l1Weighted.evalContinuousAlgHom_comp_radiusRestrict` | Existing generic aeval_of_norm_le_comp_radiusRestrict at B=ℝ; real coordinate consequences use new series bridge. |
| `RadiiPolynomial.CrossGeometry.evalContinuousAlgHom_comp_chebyshevToTaylorAeval` | Same geometric gates and physical character; canonical real aeval replaces old constructed hom. |
| `RadiiPolynomial.l1Weighted.aeval_of_norm_le_apply_real` | Universal series formula → coefficient identification + real scalar multiplication; no old hom or real multiplicativity. |
| `RadiiPolynomial.l1Weighted.eval_mul` | map_mul.symm of canonical real arrow, rewritten by FIRST bridge; old orientation retained. |
| `RadiiPolynomial.l1Weighted.hasDerivAt_eval` | Coordinate analytic series theorem; module docstring only changed. |

This list identifies twelve selected old source heads: eleven removals and one renamed
naturality service. It is not a count of compiler-generated declarations. The actual private
constructor and its auxiliaries are identified by the captured compiler inventory. No
compatibility aliases are introduced. The coordinate evaluator, derivative statements,
canonical boundary data and required classical, EX81-L2 and Duffing consumers are retained.
The zero-boundary construction does not acquire a weight-at-least-one premise.

## B4 — explicit weight bounds and staged generated Taylor services

B4 follows the U34 execution decision, U42b staging ruling and U48 hypothesis split. The [binding B4 record](../probes/records/B4_weight_and_generated_services/AFTER_ACCEPTANCE.json)
is the authority for the installed generation, executed verification, exact compiler Names,
full types/data and axioms, and recoverable BEFORE sources. Counts below concern selected
source heads, not compiler-generated declarations; the exact capture is supplied through
that record.

`Tactic/PDerivSimp.lean` and its root import retire together. U34's completed experiment
built the 23 required module/root groups without that edge, compared all 39 selected endpoint
full types and stored proof terms exactly, and checked root-importing predicate replays with
the positive canary and expected negative tactic-presence control. The retained owner records
and actual tactic absence were checked separately. This supports deletion in the required
consumer environment, not equivalence of every possible future `simp` call. No replacement
tactic, alias or additional theorem premise is introduced; the other tactic services remain.

The generated-only Taylor contract is staged with its test, not shipped through a new module.
Its thirteen selected source heads are `IVP.TaylorCertQ`, its `margin`, `ChecksRadii` and
`ChecksBy`, `IVP.Z₁Slot`, and `IVP.StdIVPDataQ.ChecksZ₁By`, `instDecidableChecksZ₁By`,
`radii_sound`, `certified_of_bounds`, `certified_ivpCoeffs_of_bounds`, `Z₁By_sound`,
`certified_of_checksBy` and `certified_ivpCoeffs_of_checksBy`. The four test heads
`Tests.TY.dataQ`, `C81`, `all81` and `main81` move with it. The complete extension and test
are recoverable as [`staged/U42bGeneratedContract.lean`](../probes/records/B4_weight_and_generated_services/staged/U42bGeneratedContract.lean)
and [`staged/AllGenerated.lean`](../probes/records/B4_weight_and_generated_services/staged/AllGenerated.lean)
under the same B4 record. The five rational certificate numbers, exact split conjunction,
selected kernel-column predicate, override bounds and unique-zero/raw-residual conclusions
are retained in that record. Production keeps `StdIVPDataQ`, `ofStd` and realization (the named
round-trip lemma `toStdIVPData_ofStd` is deleted, R-ELAB row below, executed DELETE; realization recovers the data
definitionally), the per-bound checks and soundness that the merge retained (`ChecksZ₀`, `ChecksZ₀By`,
`ChecksZ₂` with `Z₀_sound`, `ChecksZ₀By_sound`, `Z₂_sound`; `ChecksZ₁ker` and `ChecksDF` with `Z₁ker_sound`;
the `Y₀` clause and its soundness are staged and the column `Z₁` clauses are deleted, B5 ledger below), and
the essential Example81 kernel-column route.
The U31 rider above describes the earlier test-only reach and planned staging; B4 records
that staging disposition without rewriting its historical evidence or the closed B3/U25 records.

U48 removes these eight selected source heads. The positive, submultiplicative and normalized
classes remain separate; the actual extraction bound is retained explicitly.

| Removed source head | Canonical assumption or retained service |
| --- | --- |
| `RadiiPolynomial.SuperUnitWeight` | Explicit `∀ m, 1 ≤ w m` at extraction; positivity remains `PosWeight w`. |
| `RadiiPolynomial.SubMulWeight` | `SubMulWeightBase w` for convolution; separate explicit lower bound for extraction. |
| `RadiiPolynomial.lpOneAlgWeightSubMul` | `lpOneAlgWeightMul` for additive convolution; separate explicit frame-weight lower bound for extraction. |
| `RadiiPolynomial.lpOneMulAlgWeightSubMul` | `lpOneMulAlgWeightMul` for multiplicative convolution; separate explicit frame-weight lower bound for extraction. |
| `RadiiPolynomial.WeightedScalar.instLpOneAlgWeightSubMul` | Translate the supplied bound by `WeightedScalar.fiberTrivialization_weight` at extraction. |
| `RadiiPolynomial.ScaledReal.instSubMulWeight` | Existing positive-radius submultiplicativity and independent normalization remain; supply the power lower bound when needed. |
| `RadiiPolynomial.ScaledRealZ.instSubMulWeight` | Bilateral submultiplicativity still requires `Fact (1 ≤ ν)`; supply the power lower bound explicitly at extraction. |
| `RadiiPolynomial.borderedWeight.instSubMulWeight` | Existing positivity and submultiplicativity remain; supply the bordered-weight lower bound when needed. |

The retained extraction theorem types and bodies are unchanged. Scalar `PosWeight`,
`SubMulWeightBase` and `NormalizedWeight`, and frame `lpOneAlgWeightMul`,
`lpOneMulAlgWeightMul` and `lpOneAlgWeightNormalized`, retain their distinct contracts.
The two updated FT examples exercise extraction using the explicit bound. No replacement
bundle, hidden `Fact` packaging of that bound, or compatibility alias is introduced. Existing
analytic radius assumptions are not erased, and unit normalization does not imply
submultiplicativity or replace the extraction bound.

`RadiiPolynomial.SeqL1` is the one selected source shortcut retired from
`Operators/BlockDiagonal/WeightedL1.lean`; its captured type/body remain recoverable through
the B4 record. This removes only the unused spelling `fun ν : PosReal => l1Weighted ν`,
not the carrier, the production Pi state spaces or any block-diagonal mathematical service.

## B5 — operation coherence and selective mathematical recovery

The weighted ℓ¹ carrier has one globally registered additive-index operation family.
The multiplicative constructors `instMulMul`, `instMulOne`, `instMulRing`,
`instMulNormedRing` are explicit data; the compatibility families retain their own instances, and
arbitrary multiplicative monoids have the `Additive M` index/fiber presentation. This keeps
the original weight, completeness and normalization hypotheses separate.

Selective records own the finite-fiber law family, column and head/tail principles,
operator/IVP extensions, analytic/spectral families and the Example81 ℓ² route. These records
import surviving primitives and earlier records; they do not ship or restore the whole old API.
The two finite-convolution tests accompany their record, and the Example81 ℓ² route keeps
its six exact controls with its library/caller/test chain.

Surviving consumers use canonical maps and laws: coefficient singles use `coeff_single`
and `Pi.single_eq_of_ne`; generic lift bounds replace the geometric restatement; negation
and subtraction use the retained bundled maps' `map_neg`/`map_sub`; projection derivatives
and polynomial powers use Mathlib calculus. Validation of retained services follows these
repoints, while tests of staged mathematics accompany their owning records. Polynomial
derivative macros and `compPolyOf%` reification are retired interfaces with historical source
recovery. Dyadic syntax/checker/test ownership is staged; production `finmatrix_bound`,
Taylor `t_bound` and shared certificate data remain in the library.

The final B5 record binds source dispositions, exact generated-name accounting, typed/axiom
preservation, consumer controls and executed recovery. Historical B1–B4 and U25 entries
above retain their original evidence scope; their former live-surface descriptions are read
with the later B5 dispositions.

## B5 exact retirement and recovery ledger (FF-B5-1/2/4)

The canonical [B5 AFTER record](../probes/records/B5_universal_api_retirement/AFTER_ACCEPTANCE.json) binds execution and installation status for this ledger. The [exact retired-Name catalog](../probes/records/B5_universal_api_retirement/RETIRED_NAME_CATALOG.json) records all 1943 shipping absences, their accepted v3 classes and executed command/module bases. NON-FACE entries are owned private/generated/support Names, not additional accepted v3 faces.

Staged rows identify selective recovery sources outside the shipping API. The [30 private-helper relocations](../probes/records/B5_universal_api_retirement/PRIVATE_HELPER_RELOCATIONS.md) preserve exact old/new Names and source ownership; their mathematical claims remain bound to each executed TYPE/DATA/trust/cone record. No production compatibility aliases are introduced.

Packet-completeness records: [original630 census](../probes/records/B5_universal_api_retirement/ORIGINAL630_CENSUS.json) (444 present +143 B5 retirements:105 EXAMPLE-DELETE,10 R-ELAB,28 C13 private supports;43 historical), [retrospective term-derived P9 roots](../probes/records/B5_universal_api_retirement/P9_TERM_ROOTS.json), [three build-preflight repairs](../probes/records/B5_universal_api_retirement/BUILD_PREFLIGHT_REPAIR.json), and [immutable executed shipping reader](../probes/records/B5_universal_api_retirement/EXECUTED_SHIPPING_READER.json). These supersede incomplete earlier packet pointers without rewriting B1–B4 or U25 history.

| Retired exact Name | Accepted v3 class | Executed action | Selective record source |
|---|---|---|---|
| `ChebyshevIVP.StdChebIVPData.A_finBlock_eq` | R-ELAB | DELETE | — |
| `ChebyshevIVP.StdChebIVPData.G_toSeq_negSucc` | STAGE | STAGE | [staged/B5RecordChebNegativeModes.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordChebNegativeModes.lean) |
| `ChebyshevIVP.StdChebIVPData.TA_apply` | R-ELAB | DELETE | — |
| `ChebyshevIVP.StdChebIVPData.TC_apply` | R-ELAB | DELETE | — |
| `ChebyshevIVP.StdChebIVPData.TCblock_apply` | R-ELAB | DELETE | — |
| `ChebyshevIVP.StdChebIVPData.Z₁_le_semiMajor_of_Q` | STAGE | STAGE | [staged/B5RecordChebSemiMajor.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordChebSemiMajor.lean) |
| `ChebyshevIVP.StdChebIVPData.Z₁_le_semiMajor_of_checksK` | STAGE | STAGE | [staged/B5RecordChebSemiMajor.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordChebSemiMajor.lean) |
| `ChebyshevIVP.StdChebIVPData.composedApprox` | DELETE | DELETE | — |
| `ChebyshevIVP.StdChebIVPData.differentiable_G` | DELETE | DELETE | — |
| `ChebyshevIVP.StdChebIVPData.fderiv_G` | DELETE | DELETE | — |
| `ChebyshevIVP.StdChebIVPData.neg_modes_zero_of_G_zero` | STAGE | STAGE | [staged/B5RecordChebNegativeModes.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordChebNegativeModes.lean) |
| `ChebyshevIVP.StdChebIVPData.tailCancel` | DELETE | DELETE | — |
| `ChebyshevIVP.TCtailElem_norm_le` | DELETE | DELETE | — |
| `ChebyshevIVP.TCtail_apply` | R-ELAB | DELETE | — |
| `ChebyshevIVP.banachField_apply` | R-ELAB | DELETE | — |
| `ChebyshevIVP.chebyshevShiftDiv_add` | DELETE | DELETE | — |
| `ChebyshevIVP.chebyshevShiftDiv_eq_neg_uIntegrate_chebyshevToU` | R-ELAB | STAGE | [staged/B5RecordChebShiftDiv.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordChebShiftDiv.lean) |
| `ChebyshevIVP.chebyshevShiftDiv_norm_le` | DELETE | DELETE | — |
| `ChebyshevIVP.chebyshevShiftDiv_norm_le'` | STAGE | STAGE | [staged/B5RecordChebShiftDiv.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordChebShiftDiv.lean) |
| `ChebyshevIVP.chebyshevShiftDiv_smul` | DELETE | DELETE | — |
| `ChebyshevIVP.chebyshevShiftDiv_tailTsum_le_div` | DELETE | DELETE | — |
| `ChebyshevIVP.chebyshevShiftDiv_tailTsum_le_half` | DELETE | DELETE | — |
| `ChebyshevIVP.chebyshev_Z₁_le` | DELETE | DELETE | — |
| `ChebyshevIVP.composedApproxCheb_eq_id_sub` | DELETE | DELETE | — |
| `ChebyshevIVP.composedApproxCheb_tail_toReal` | DELETE | DELETE | — |
| `ChebyshevIVP.defectChebCLM` | DELETE | DELETE | — |
| `ChebyshevIVP.embedWithPassThrough_natCast` | R-ELAB | DELETE | — |
| `ChebyshevIVP.embedWithPassThrough_negSucc` | R-ELAB | DELETE | — |
| `ChebyshevIVP.liftDefect_eq_defectCheb_apply` | R-ELAB | DELETE | — |
| `ChebyshevIVP.norm_compPolyDerivative_le` | DELETE | DELETE | — |
| `ChebyshevPolynomialExample.affineConstant_reified` | R-ELAB | DELETE | — |
| `ChebyshevPolynomialExample.algebraMapConstant_reified` | R-ELAB | DELETE | — |
| `ChebyshevPolynomialExample.first_partial_coefficients` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.first_partial_coefficients._native.native_decide.ax_1_1` | NON-FACE | DELETE | — |
| `ChebyshevPolynomialExample.highMode` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.high_mode_square` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.high_mode_square._native.native_decide.ax_1_1` | NON-FACE | DELETE | — |
| `ChebyshevPolynomialExample.inputs_supported` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.inputs_supported_padded` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.logisticReal` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.logisticReal_eq_logisticReified` | R-ELAB | DELETE | — |
| `ChebyshevPolynomialExample.logisticReal_lipschitzBound` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.logisticReified_derivativeBound` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.logisticReified_derivativeLipschitzBound` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.logisticReified_eq_literal` | R-ELAB | DELETE | — |
| `ChebyshevPolynomialExample.minimalRadii` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.mixedReified` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.mixedReified_eq_literal` | R-ELAB | DELETE | — |
| `ChebyshevPolynomialExample.mixed_coefficients_all` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.rationalConstant_reified` | R-ELAB | DELETE | — |
| `ChebyshevPolynomialExample.second_partial_coefficients` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.second_partial_coefficients._native.native_decide.ax_1_1` | NON-FACE | DELETE | — |
| `ChebyshevPolynomialExample.squarePolynomial` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.support_bound_independent` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.symmetricInputs` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.taylor_interpreter_misses_constant` | EXAMPLE-DELETE | DELETE | — |
| `ChebyshevPolynomialExample.taylor_interpreter_misses_constant._native.native_decide.ax_1_1` | NON-FACE | DELETE | — |
| `ContinuousLinearMap.precompR.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example1421.Cert.FQ` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.Cert.FQ_eq_zero` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.Cert.Z₁_le_semiMajor` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.Cert.abar_0_size` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.Cert.computed_residual_eq` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.Cert.foldQ` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.Cert.phiQ` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.Cert.phiQ_eq_zero` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.Cert.qbar` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.Cert.qbar_eq_zero` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.Dphi` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.Dphi_eq_derivative` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.Z₁_semiMajor_bound` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.compPolyDerivative_apply_eq_Dphi` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.computed_DF_columns` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.computed_DF_columns._native.native_decide.ax_1_1` | NON-FACE | DELETE | — |
| `Example1421.computed_DF_entries` | EXAMPLE-DELETE | DELETE | — |
| `Example1421.f_cpoly_reified` | R-ELAB | DELETE | — |
| `Example1421.instFactLtRealOfNatToRealν_val` | R-ELAB | DELETE | — |
| `Example1421.rawDerivative_single_eq_dataDF` | EXAMPLE-DELETE | DELETE | — |
| `Example245.Cert.A` | EXAMPLE-DELETE | DELETE | — |
| `Example245.Cert.A_dag` | EXAMPLE-DELETE | DELETE | — |
| `Example245.Cert.Y₀_bound` | EXAMPLE-DELETE | DELETE | — |
| `Example245.Cert.Z₀_bound` | EXAMPLE-DELETE | DELETE | — |
| `Example245.Cert.Z₂_bound` | EXAMPLE-DELETE | DELETE | — |
| `Example245.Z₂_bound_sq_sub_const` | EXAMPLE-DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `Example245.differentiable_sq_sub_const` | EXAMPLE-DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `Example245.fderiv_sq_sub_const` | EXAMPLE-DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `Example245.id_eq_smulCLM_one` | EXAMPLE-DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `Example245.id_sub_smulCLM` | EXAMPLE-DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `Example245.norm_smulCLM` | EXAMPLE-DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `Example245.smulCLM` | EXAMPLE-DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `Example245.smulCLM._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `Example245.smulCLM._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `Example245.smulCLM.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `Example245.smulCLM_apply` | R-ELAB | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `Example245.smulCLM_comp` | EXAMPLE-DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `Example245.smulCLM_comp._simp_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `Example245.smulCLM_comp._simp_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `Example245.smulCLM_comp._simp_1_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `Example245.smulCLM_comp._simp_1_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `Example245.smulCLM_comp._simp_1_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `Example245.smulCLM_comp._simp_1_6` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `Example245.smulCLM_comp._simp_1_7` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `Example245.smulCLM_injective` | EXAMPLE-DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `Example245.smulCLM_sub` | EXAMPLE-DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `Example77.Cert.A_col0` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.A_col1` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.A_col2` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.A_colOf` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.A_dag` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.A_diag` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.A_injective` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.A_inv` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.A_mat` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.A_norm_le` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.A_norm_le._native.native_decide.ax_1_1` | NON-FACE | DELETE | — |
| `Example77.Cert.A_sub1` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.A_sub2` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.Y₀_bound` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.Y₀_le` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.Y₀_le._native.native_decide.ax_1_1` | NON-FACE | DELETE | — |
| `Example77.Cert.Z₀_bound` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.Z₀_le` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.Z₁_bound` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.Z₁_le` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.Z₂_bound` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.Z₂_le` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.radii_neg` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.r₀_pos` | EXAMPLE-DELETE | DELETE | — |
| `Example77.Cert.xTilde_ball` | EXAMPLE-DELETE | DELETE | — |
| `Example77.F_toSeq` | EXAMPLE-DELETE | DELETE | — |
| `Example77.approxInverse_tailDiag_ne_zero` | EXAMPLE-DELETE | DELETE | — |
| `Example77.tailCancel` | EXAMPLE-DELETE | DELETE | — |
| `Example81.Cert.A_norm_le` | EXAMPLE-DELETE | DELETE | — |
| `Example81.Cert.A_norm_le._native.native_decide.ax_1_1` | NON-FACE | DELETE | — |
| `Example81.Cert.Z₁_le_cert` | EXAMPLE-DELETE | DELETE | — |
| `Example81.Cert.analytic_unique` | EXAMPLE-DELETE | DELETE | — |
| `Example81.Cert.radii_neg` | EXAMPLE-DELETE | DELETE | — |
| `Example81.Df` | EXAMPLE-DELETE | DELETE | — |
| `Example81.Df_eq_fderiv` | EXAMPLE-DELETE | DELETE | — |
| `Example81.F_abar_mem` | EXAMPLE-DELETE | DELETE | — |
| `Example81.L2.Araw` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Araw._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.DFraw` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Data.A_col` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `Example81.L2.Data.A_col.match_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `Example81.L2.Data.DF_col` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `Example81.L2.Data.abar_0` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `Example81.L2.Data.abar_0.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Ddiag` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Differential.differentiable_quadraticMap` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.differentiable_residual` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.fderiv_quadraticMap` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.fderiv_quadraticMap_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.fderiv_residual` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.fderiv_residual_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.hasFDerivAt_quadraticMap` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.hasFDerivAt_residual` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.instPosWeightNatGeoWeight` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.norm_comp_fderiv_residual_sub_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.norm_comp_fderiv_residual_sub_le._abel_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.norm_comp_fderiv_residual_sub_le_of_norm_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.norm_fderiv_quadraticMap_sub_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.quadraticMap` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.quadraticMap._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.quadraticMap._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.quadraticMap._proof_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.quadraticMap._proof_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.quadraticMap._proof_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.quadraticMap._proof_6` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.quadraticMap.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Differential.residual` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.residual._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Differential.lean) |
| `Example81.L2.Differential.residual.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.H` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.H._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.H._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.H.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.H_aStar` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.H_apply` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.H_apply._abel_1_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.H_eq_logistic` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.H_eq_zero_iff` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.L` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.L.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.L_comp_P` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.L_eq_id_sub_Pi_S` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.L_eq_id_sub_Pi_S._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Lhead` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Lhead.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_10` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_100` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_101` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_102` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_103` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_104` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_105` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_106` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_107` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_108` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_109` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_11` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_110` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_111` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_112` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_113` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_114` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_115` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_116` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_117` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_118` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_119` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_12` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_120` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_121` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_13` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_14` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_15` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_16` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_17` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_18` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_19` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_20` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_21` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_22` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_23` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_24` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_25` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_26` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_27` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_28` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_29` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_30` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_31` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_32` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_33` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_34` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_35` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_36` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_37` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_38` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_39` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_40` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_41` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_42` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_43` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_44` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_45` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_46` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_47` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_48` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_49` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_50` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_51` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_52` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_53` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_54` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_55` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_56` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_57` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_58` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_59` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_6` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_60` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_61` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_62` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_63` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_64` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_65` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_66` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_67` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_68` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_69` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_7` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_70` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_71` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_72` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_73` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_74` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_75` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_76` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_77` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_78` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_79` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_8` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_80` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_81` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_82` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_83` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_84` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_85` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_86` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_87` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_88` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_89` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_9` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_90` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_91` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_92` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_93` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_94` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_95` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_96` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_97` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_98` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_entries._proof_1_99` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_mul_PheadQ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.LheadQ_mul_PheadQ._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Lhead_entries` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Lhead_mul_Phead` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Logistic.H` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean) |
| `Example81.L2.Logistic.H._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean) |
| `Example81.L2.Logistic.H._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean) |
| `Example81.L2.Logistic.H._proof_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean) |
| `Example81.L2.Logistic.H._proof_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean) |
| `Example81.L2.Logistic.H.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean) |
| `Example81.L2.Logistic.H_eq_zero_iff` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean) |
| `Example81.L2.Logistic.H_half_delta_half_ne_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean) |
| `Example81.L2.Logistic.coeff_H_succ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean) |
| `Example81.L2.Logistic.coeff_H_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean) |
| `Example81.L2.Logistic.instPosWeightNatGeoWeight` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean) |
| `Example81.L2.Logistic.q` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean) |
| `Example81.L2.Logistic.q.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Logistic.lean) |
| `Example81.L2.N` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.P` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.P.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.P_H_abar` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.P_H_abar._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.P_comp_L` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.P_comp_Q` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.P_delta_eleven` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.P_delta_eleven._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.P_delta_zero_coeff_two` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.P_delta_zero_coeff_two._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.P_injective` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.P_injective._simp_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.P_injective_bound` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.P_norm_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PcolSupport` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PcolSupport.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.Phead` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Phead.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.PheadQ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.PheadQ_col_bound` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PheadQ_col_bound._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PheadQ_mul_LheadQ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.PheadQ_mul_LheadQ._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.PheadQ_row_bound` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PheadQ_row_bound._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.Phead_col_bound` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.Phead_mul_Lhead` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Phead_row_bound` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.Pi` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Pi.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Pi_comp_S_comp_Q` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Pi_comp_S_comp_Q._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Pkernel` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.Pkernel.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PkernelQ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PkernelQ.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PkernelQ_column_zero_sq` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PkernelQ_column_zero_sq._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.Pkernel_col_support` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.Pkernel_col_support._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.Pkernel_fin` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.Pkernel_row_support` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.Pkernel_schur` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.ProwSupport` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.ProwSupport.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PschurCLM` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PschurCLM._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PschurCLM._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PschurCLM._proof_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PschurCLM._proof_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PschurCLM._proof_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PschurCLM._proof_6` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PschurCLM.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PschurCLM_eq_P` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.PschurCLM_eq_P._proof_1_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.Q` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Q.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Q_comp_P` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.S` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.S._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.S._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.S._proof_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.S._proof_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.S.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.S_eq` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.T` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.T._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.T._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.T.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.T_eq_tailIntegratedProduct` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.T_eq_tailIntegratedProduct._abel_1_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.T_eq_tailKernelCLM` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean) |
| `Example81.L2.X` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Y0_bound` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.Z0_bound` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.Z0_identity` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.Z0_slot` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean) |
| `Example81.L2.Z1_bound` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean) |
| `Example81.L2.Z2_ball_bound` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.Z2_ball_bound._simp_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.Z2_difference_bound` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.Z2_slot` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean) |
| `Example81.L2.aStar` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.aStar._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.aStar._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.aStar_mem` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.abar` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.abar._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.abar._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.abar.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.abarQ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.abarQ.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.abs_xStar_sub_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.beta` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.beta._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.beta._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.beta.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.betaQ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.betaQ.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.betaQ_explicit` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.betaQ_explicit._proof_1_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.betaQ_explicit._proof_1_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.betaQ_explicit._proof_1_6` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.betaQ_explicit._proof_1_7` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.betaQ_explicit._proof_1_8` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.betaQ_explicit._proof_1_9` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_H_abar` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar._proof_1_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar._proof_1_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar._proof_1_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar._proof_1_6` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar._proof_1_7` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar_eleven_ne_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar_head` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar_head._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar_head._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar_head._proof_1_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar_head._proof_1_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar_head._proof_1_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar_of_gt` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar_of_gt._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar_of_gt._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar_of_gt._proof_1_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_H_abar_of_gt._proof_1_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.coeff_P_delta` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.coeff_Q` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean) |
| `Example81.L2.coeff_Q._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean) |
| `Example81.L2.coeff_S` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_S_fin` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_T` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_T_range` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_T_range._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_abar` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_abar._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_abar_fin` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_abar_of_gt` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_abar_of_gt._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_beta` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_beta_of_gt` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_beta_of_gt._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_beta_of_gt._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_beta_of_gt._proof_1_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_beta_of_gt._proof_1_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.coeff_beta_of_gt._proof_1_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.contraction_value` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean) |
| `Example81.L2.delta` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.differentiable_H` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.embedXL1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.embedXL1._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.embedXL1._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.embedXL1._proof_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.embedXL1._proof_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.embedXL1._proof_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.eqOn_xStar_of_solution` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.eqOn_x_analytic_of_isBallSolution` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.eq_aStar_of_H_eq_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.eq_of_H_eq_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.example81_l2_coefficient_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean) |
| `Example81.L2.example81_l2_coefficient_zero_nondegenerate` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean) |
| `Example81.L2.example81_l2_solution` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.example81_l2_solution_existsUnique` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.example81_l2_solution_spec` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.fderiv_H_abar` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.fderiv_H_abar._abel_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.hasDerivAt_sumSeries_of_H_eq_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.hasDerivAt_xStar` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.hasFDerivAt_H` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.hasFDerivWithinAt_H` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean) |
| `Example81.L2.instFactLtRealOfNat_radiiPolynomial` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.instFactLtRealOfNat_radiiPolynomial_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean) |
| `Example81.L2.instFactLtRealOfNat_radiiPolynomial_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.instPosWeightNatGeoWeightOfNatReal` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.isBallSolution_aStar` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.ivpCoeffs_embedXL1_eq_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.kernel` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.kernel.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.kernel_11_10` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.kernel_11_9` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.kernel_12_10` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.kernel_13_11` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.kernel_row_finite` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.kernel_row_summable` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.logistic_recurrence_unique` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.normFact` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.normPosWeight` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.norm_P_H_abar_pos` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.norm_T_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean) |
| `Example81.L2.norm_T_le._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean) |
| `Example81.L2.norm_comp_fderiv_H_sub_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.norm_comp_fderiv_H_sub_le_of_norm_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `Example81.L2.norm_embedXL1_aStar_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.norm_sq_P_H_abar` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.norm_sq_P_H_abar._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.norm_sq_P_delta_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.norm_sq_P_delta_zero._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.not_P_norm_le_one` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.one_lt_norm_P_delta_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/NormBounds.lean) |
| `Example81.L2.radii_neg` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean) |
| `Example81.L2.radii_value` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Certificate.lean) |
| `Example81.L2.residualCoeff` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.residualCoeff.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.residualFact` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.residualPosWeight` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `Example81.L2.sumSeries` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.sumSeries_eq_x_analytic` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.sumSeries_zero_of_H_eq_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.symbolMass_beta` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean) |
| `Example81.L2.tailKernel_eq_kernel` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Z1.lean) |
| `Example81.L2.toCoeff_embedXL1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.trajRadius` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.xStar` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.L2.xStar_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `Example81.Z₁_bound` | EXAMPLE-DELETE | DELETE | — |
| `Example81.composedApprox_eq_fderiv_G_fin` | EXAMPLE-DELETE | DELETE | — |
| `Example81.differentiable_f_component` | EXAMPLE-DELETE | DELETE | — |
| `Example81.f_abar_support` | EXAMPLE-DELETE | DELETE | — |
| `Example81.f_cpoly_reified` | R-ELAB | DELETE | — |
| `Example81.f_eq_spec` | EXAMPLE-DELETE | DELETE | — |
| `Example81.f_spec` | EXAMPLE-DELETE | DELETE | — |
| `Example81.fderiv_f` | EXAMPLE-DELETE | DELETE | — |
| `Example81.two_abar_sub_one_Q` | EXAMPLE-DELETE | DELETE | — |
| `Example81.two_abar_sub_one_support` | EXAMPLE-DELETE | DELETE | — |
| `Example81.two_abar_sub_one_toSeq` | EXAMPLE-DELETE | DELETE | — |
| `Example81.two_abar_sub_one_toSeq._native.native_decide.ax_1_1` | NON-FACE | DELETE | — |
| `Example83.Cert.A_norm_le` | EXAMPLE-DELETE | DELETE | — |
| `Example83.Cert.A_norm_le._native.native_decide.ax_1_1` | NON-FACE | DELETE | — |
| `Example83.Cert.analytic_unique` | EXAMPLE-DELETE | DELETE | — |
| `Example83.F_abar_mem` | EXAMPLE-DELETE | DELETE | — |
| `Example83.differentiable_f_component` | EXAMPLE-DELETE | DELETE | — |
| `Example83.f_abar_support` | EXAMPLE-DELETE | DELETE | — |
| `Example83.f_eq_spec` | EXAMPLE-DELETE | DELETE | — |
| `Example83.f_spec` | EXAMPLE-DELETE | DELETE | — |
| `ExampleDiblock.J_eq_Jσ` | EXAMPLE-DELETE | DELETE | — |
| `ExampleDiblock.cube_centred_Q` | EXAMPLE-DELETE | DELETE | — |
| `ExampleDiblock.cube_centred_lt_lipschitz_Q` | EXAMPLE-DELETE | DELETE | — |
| `ExampleFisher.fisherQuad_centred_Q` | EXAMPLE-DELETE | DELETE | — |
| `ExampleFisher.hAnorm_of_carrier` | EXAMPLE-DELETE | DELETE | — |
| `ExampleFisher.norm_amb_symm_ν₁` | EXAMPLE-DELETE | DELETE | — |
| `IVP.DfExactQ` | DELETE | DELETE | — |
| `IVP.SplitBoundary` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary._sizeOf_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.SplitBoundary._sizeOf_inst` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.SplitBoundary.anchoredPrimitive` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.anchoredPrimitive._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.SplitBoundary.anchoredPrimitive.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.SplitBoundary.casesOn` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.ctorIdx` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.SplitBoundary.equiv` | DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `IVP.SplitBoundary.equiv._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.SplitBoundary.equiv_fst` | R-ELAB | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `IVP.SplitBoundary.equiv_snd_coe` | R-ELAB | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `IVP.SplitBoundary.extension` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.extension_add_zeroPart` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.extension_add_zeroPart._abel_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.SplitBoundary.fiber_eq_translate_ker` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.fiber_eq_translate_ker._abel_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.SplitBoundary.mk` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.mk._flat_ctor` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.SplitBoundary.mk.inj` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.SplitBoundary.mk.injEq` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.SplitBoundary.mk.noConfusion` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.mk.sizeOf_spec` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.SplitBoundary.noConfusion` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.noConfusionType` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.SplitBoundary.rec` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.recOn` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.trace` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.trace_anchoredPrimitive` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.trace_extension` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.trace_extension_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.trace_zeroPart` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.zeroPart` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.SplitBoundary.zeroPart._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.SplitBoundary.zeroPart_coe` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP5.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP5.lean) |
| `IVP.StdIVPData.Y₀_le_of_Q` | STAGE | STAGE | [staged/B5RecordTaylorY0P1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTaylorY0P1.lean) |
| `IVP.StdIVPData.Z₁_le_col_of_Q` | DELETE | DELETE | — |
| `IVP.StdIVPData.Z₁_le_of_Q` | DELETE | DELETE | — |
| `IVP.StdIVPData.analytic_unique` | DELETE | DELETE | — |
| `IVP.StdIVPData.analytic_unique_of_compPoly` | DELETE | DELETE | — |
| `IVP.StdIVPData.analytic_unique_of_compPoly_of_radii` | DELETE | DELETE | — |
| `IVP.StdIVPData.ivpCoeffs_abar_mem_of_compPoly` | DELETE | DELETE | — |
| `IVP.StdIVPData.norm_evalBanach_abar_eq` | DELETE | DELETE | — |
| `IVP.StdIVPData.tail_evalBanach_mul_le` | DELETE | DELETE | — |
| `IVP.StdIVPDataQ.A_finBlock_eq` | R-ELAB | DELETE | — |
| `IVP.StdIVPDataQ.ChecksY₀` | STAGE | STAGE | [staged/B5RecordTaylorY0P1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTaylorY0P1.lean) |
| `IVP.StdIVPDataQ.ChecksZ₁` | DELETE | DELETE | — |
| `IVP.StdIVPDataQ.ChecksZ₁col` | DELETE | DELETE | — |
| `IVP.StdIVPDataQ.DF_finBlock_eq` | R-ELAB | DELETE | — |
| `IVP.StdIVPDataQ.Y₀_sound` | STAGE | STAGE | [staged/B5RecordTaylorY0P1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTaylorY0P1.lean) |
| `IVP.StdIVPDataQ.Z₁_sound` | DELETE | DELETE | — |
| `IVP.StdIVPDataQ.Z₁col_sound` | DELETE | DELETE | — |
| `IVP.StdIVPDataQ.abar_toSeq` | DELETE | DELETE | — |
| `IVP.StdIVPDataQ.composedApprox_eq_of_checksDF` | DELETE | DELETE | — |
| `IVP.StdIVPDataQ.norm_abar` | DELETE | DELETE | — |
| `IVP.StdIVPDataQ.toStdIVPData_A_col` | R-ELAB | DELETE | — |
| `IVP.StdIVPDataQ.toStdIVPData_DF_col` | R-ELAB | DELETE | — |
| `IVP.StdIVPDataQ.toStdIVPData_abar_Q` | R-ELAB | DELETE | — |
| `IVP.StdIVPDataQ.toStdIVPData_ofStd` | R-ELAB | DELETE | — |
| `IVP.StdIVPDataQ.toStdIVPData_ν_q` | R-ELAB | DELETE | — |
| `IVP.Y₀Q` | STAGE | STAGE | [staged/B5RecordTaylorY0P1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTaylorY0P1.lean) |
| `IVP.Z₁colQ` | DELETE | DELETE | — |
| `IVP.abs_chebyshevBoundary_le_norm_of_two_le` | DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `IVP.chebyshevAnchoredPrimitive` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP6.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP6.lean) |
| `IVP.chebyshevAnchoredPrimitive.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.chebyshevAnchoredPrimitive_zero_boundary` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP6.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP6.lean) |
| `IVP.chebyshevBoundary` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP6.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP6.lean) |
| `IVP.chebyshevBoundary._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.chebyshevBoundary_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP6.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP6.lean) |
| `IVP.chebyshevBoundary_factor_symmetric` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP6.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP6.lean) |
| `IVP.chebyshevBoundary_not_multiplicative` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP6.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP6.lean) |
| `IVP.chebyshevBoundary_not_multiplicative._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.chebyshevBoundary_not_multiplicative._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.chebyshevBoundary_one` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP6.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP6.lean) |
| `IVP.chebyshevIntegrateCLM` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP6.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP6.lean) |
| `IVP.chebyshevIntegrateCLM._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.chebyshevIntegrateCLM_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP6.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP6.lean) |
| `IVP.chebyshevSplitBoundary` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP6.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP6.lean) |
| `IVP.chebyshevSplitBoundary._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.chebyshevSplitBoundary._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.chebyshevSplitBoundary._proof_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.chebyshevSplitBoundary._proof_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.colSupQ` | DELETE | DELETE | — |
| `IVP.contDiff_vectorField` | DELETE | DELETE | — |
| `IVP.contDiff_vectorField_pi` | DELETE | DELETE | — |
| `IVP.differentiable_vectorField` | DELETE | DELETE | — |
| `IVP.differentiable_vectorField_pi` | DELETE | DELETE | — |
| `IVP.eval_chebyshevAnchoredPrimitive` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP6.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP6.lean) |
| `IVP.ivp_DF_of_Dφ_nat_eq` | R-ELAB | DELETE | — |
| `IVP.ivp_system_theorem` | DELETE | DELETE | — |
| `IVP.ivp_system_theorem_local` | DELETE | DELETE | — |
| `IVP.norm_complexTrajectory_le` | DELETE | DELETE | — |
| `IVP.norm_taylorReborderingDefect` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP7.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP7.lean) |
| `IVP.norm_taylorReborderingDefect._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.norm_taylorReborderingDefect_apply_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP7.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP7.lean) |
| `IVP.norm_taylorReborderingDefect_apply_le._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.norm_taylorReborderingDefect_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP7.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP7.lean) |
| `IVP.seqNormQ` | DELETE | DELETE | — |
| `IVP.symmetricEndpointCharacter` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP6.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP6.lean) |
| `IVP.symmetricEndpointCharacter.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.symmetricEndpointCharacter_comp_joukowskiAevalSymm` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Applications/IVP/Chebyshev/Boundary.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Applications/IVP/Chebyshev/Boundary.lean) |
| `IVP.taylorAnchoredPrimitive` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP7.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP7.lean) |
| `IVP.taylorAnchoredPrimitive.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.taylorAnchoredPrimitive_coe` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP7.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP7.lean) |
| `IVP.taylorBoundaryCharacter` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP7.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP7.lean) |
| `IVP.taylorBoundaryCharacter._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.taylorBoundaryCharacter._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.taylorBoundaryCharacter.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.taylorBoundaryCharacter_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP7.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP7.lean) |
| `IVP.taylorBoundary_shiftDivN` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP7.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP7.lean) |
| `IVP.taylorEndpointCharacter` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP7.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP7.lean) |
| `IVP.taylorEndpointCharacter._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.taylorEndpointCharacter.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.taylorEndpointCharacter_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP7.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP7.lean) |
| `IVP.taylorReborderingDefect` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP7.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP7.lean) |
| `IVP.taylorReborderingDefect._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.taylorReborderingDefect._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.taylorReborderingDefect.congr_simp` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.taylorReborderingDefect.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.taylorReborderingDefect_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP7.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP7.lean) |
| `IVP.taylorSplitBoundary` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP7.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP7.lean) |
| `IVP.taylorSplitBoundary._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.taylorSplitBoundary._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `IVP.taylorSplitBoundary_trace` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordIVPBoundaryP7.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP7.lean) |
| `MvPolyBridge.CompPoly.Chebyshev.differentiable_eval` | DELETE | DELETE | — |
| `MvPolyBridge.CompPoly.Chebyshev.eval_isSymmetric` | STAGE | STAGE | [staged/B5RecordSymmetricStorageBordered.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordSymmetricStorageBordered.lean) |
| `MvPolyBridge.CompPoly.Chebyshev.fderiv_eval` | DELETE | DELETE | — |
| `MvPolyBridge.CompPoly.Chebyshev.norm_derivative_le` | DELETE | DELETE | — |
| `MvPolyBridge.CompPoly.Chebyshev.norm_derivative_sub_le_max` | DELETE | DELETE | — |
| `MvPolyBridge.CompPoly.Chebyshev.norm_eval_le` | DELETE | DELETE | — |
| `MvPolyBridge.CompPoly.Chebyshev.norm_eval_sub_le` | DELETE | DELETE | — |
| `MvPolyBridge.CompPoly.Chebyshev.norm_eval_sub_le_of_norm_sub` | DELETE | DELETE | — |
| `MvPolyBridge.CompPoly.derivativeCentredBound_ratCast` | R-ELAB | DELETE | — |
| `MvPolyBridge.CompPoly.evalLaurentCoeffSeq_eq_of_support` | STAGE | STAGE | [staged/B5RecordLaurentInterpreter.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordLaurentInterpreter.lean) |
| `MvPolyBridge.CompPoly.evalQ_cast` | DELETE | DELETE | — |
| `MvPolyBridge.CompPoly.lipschitzBound_add_op` | R-ELAB | DELETE | — |
| `MvPolyBridge.CompPoly.lipschitzBound_mul_op` | R-ELAB | DELETE | — |
| `MvPolyBridge.CompPoly.lipschitzBound_neg_op` | R-ELAB | DELETE | — |
| `MvPolyBridge.CompPoly.lipschitzBound_sub_op` | R-ELAB | DELETE | — |
| `MvPolyBridge.CompPoly.norm_evalBanach_sub_le_max` | DELETE | DELETE | — |
| `MvPolyBridge.CompPoly.norm_fderiv_evalBanach_apply_le` | STAGE | STAGE | [staged/B5RecordTaylorDerivativeP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTaylorDerivativeP1.lean) |
| `MvPolyBridge.CompPoly.norm_fderiv_evalBanach_le` | DELETE | DELETE | — |
| `MvPolyBridge.CompPoly.pderiv_pderiv_toMvPoly` | DELETE | DELETE | — |
| `MvPolyBridge.CompPoly.toMvPoly_add_op` | R-ELAB | DELETE | — |
| `MvPolyBridge.CompPoly.toMvPoly_mul_op` | R-ELAB | DELETE | — |
| `MvPolyBridge.CompPoly.toMvPoly_neg_op` | R-ELAB | DELETE | — |
| `MvPolyBridge.CompPoly.toMvPoly_sub_op` | R-ELAB | DELETE | — |
| `MvPolyBridge.contDiff_evalBanach` | DELETE | DELETE | — |
| `MvPolyBridge.differentiable_evalBanach` | DELETE | DELETE | — |
| `MvPolyBridge.instDecidableEqCompPoly` | R-ELAB | fragment | — |
| `MvPolyBridge.instDecidableEqCompPoly.decEq` | R-ELAB | fragment | — |
| `MvPolyBridge.mvPolyCoeff_C_fun` | R-ELAB | DELETE | — |
| `MvPolyBridge.mvPolyCoeff_one` | R-ELAB | DELETE | — |
| `MvPolyBridge.mvPolyCoeff_zero` | R-ELAB | DELETE | — |
| `MvPolyBridge.norm_aeval_sub_le` | DELETE | DELETE | — |
| `MvPolyBridge.norm_fderiv_aeval_le` | STAGE | STAGE | [staged/B5RecordTaylorDerivativeP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTaylorDerivativeP2.lean) |
| `MvPolynomial.C_ofNat_eq` | R-ELAB | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `MvPolynomial.contDiff_aeval` | STAGE | STAGE | [staged/B5RecordMvPolynomialCalculus.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordMvPolynomialCalculus.lean) |
| `MvPolynomial.totalDegree_pderiv_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordMvPolynomialCalculus.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordMvPolynomialCalculus.lean) |
| `RadiiPolynomial.Certification.Rational.Z₀Slot.ofNat` | R-ELAB | fragment | — |
| `RadiiPolynomial.Certification.Rational.Z₀Slot.ofNat_ctorIdx` | R-ELAB | fragment | — |
| `RadiiPolynomial.Certification.Rational.axpyB_nil` | R-ELAB | DELETE | — |
| `RadiiPolynomial.Certification.Rational.instDecidableEqZ₀Slot` | R-ELAB | fragment | — |
| `RadiiPolynomial.CrossGeometry.add_inv_le_add_inv_of_inv_le_of_le` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.aeval_of_norm_le_comp_chebyshevToTaylorAeval` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.bernsteinParameter` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.bernsteinParameter.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.CrossGeometry.bernsteinParameter_le_iff_le_semiMinor` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.chebPolyTaylor` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.chebPolyTaylor._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.CrossGeometry.chebPolyTaylor.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.CrossGeometry.chebPolyTaylor_norm_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.chebPolyTaylor_one` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.chebPolyTaylor_toSeq` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.chebyshevDerivativeToTaylorCLM` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.chebyshevDerivativeToUCLM` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.chebyshevDerivativeToUCLM_toSeq` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.chebyshevStorageFactor` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.chebyshevStorageFactor._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.CrossGeometry.chebyshevStorageFactor.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.CrossGeometry.chebyshevStorageFactor_nonneg` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorAeval` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorAeval._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorAeval_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorAeval_comp_joukowskiAevalSymm` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorAeval_joukowskiGenSymm` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorBorderedCLM` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorBorderedCLM._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorBorderedCLM._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorBorderedCLM._proof_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorBorderedCLM.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorBorderedCLM_norm_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorBorderedCLM_single` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorCLM` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorCLM._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorCLM._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorCLM._proof_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorCLM._proof_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.CrossGeometry.chebyshevToTaylorCLM.congr_simp` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.CrossGeometry.coe_joukowskiAevalSymm` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.comp_joukowskiAeval_eq_evalC` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.derivShift_CLM_comp_chebyshevToTaylorCLM` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.derivShift_chebPolyTaylor` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.endpointJoukowskiAevalSymm` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.endpointJoukowskiAevalSymm_gen` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.endpointJoukowskiGen` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.endpointJoukowskiGenSymm` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.endpointJoukowskiGen_isSymmetric` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.evalLaurentC_comp_joukowskiAeval` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.evalLaurentC_neg_one_comp_joukowskiAeval` | DELETE | DELETE | — |
| `RadiiPolynomial.CrossGeometry.eval_chebyshevToTaylorCLM` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.eval_joukowskiGen` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.joukowskiAeval` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.joukowskiAevalSymm` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.joukowskiAevalSymm_gen` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.joukowskiAevalSymm_injective` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.joukowskiAeval_gen` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.joukowskiAeval_injective` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.norm_chebyshevDerivativeToTaylorCLM_apply_le` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.norm_chebyshevDerivativeToTaylorCLM_le` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.norm_chebyshevDerivativeToUCLM_apply_le` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.norm_chebyshevDerivativeToUCLM_le` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.norm_chebyshevToTaylorAeval` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.norm_chebyshevToTaylorAeval_apply_le` | DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `RadiiPolynomial.CrossGeometry.norm_chebyshevToTaylorAeval_le` | DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `RadiiPolynomial.CrossGeometry.norm_chebyshevToTaylorCLM_apply_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.norm_chebyshevToTaylorCLM_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `RadiiPolynomial.CrossGeometry.norm_endpointJoukowskiGen_pow_le` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.norm_endpointJoukowskiGen_pow_le_of_gate` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.norm_joukowskiGen_pow_le` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.norm_joukowskiGen_pow_le_of_gate` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.norm_joukowski_le` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.norm_joukowski_le_semiMajor` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.norm_uPolyOmegaSynthesisCLM_apply_le` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.norm_uPolyOmegaSynthesisCLM_le` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.one_le_of_semiMajor_le` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.one_le_semiMajor` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.one_lt_of_pos_le_semiMinor` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.roundtrip_radius_lt` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.roundtrip_radius_sq_le` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.semiMajor` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.semiMajor_pos` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.semiMajor_sq_sub_semiMinor_sq` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.semiMinor` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.semiMinor_nonneg` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.symmetricEndpointCharacter_comp_endpointJoukowskiAevalSymm` | DELETE | DELETE | — |
| `RadiiPolynomial.CrossGeometry.symmetricEvalCharacter_comp_endpointJoukowskiAevalSymm` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.symmetricEvalCharacter_comp_joukowskiAevalSymm` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `RadiiPolynomial.CrossGeometry.uPolyOmega` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.uPolyOmegaSynthesisCLM` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.uPolyOmegaSynthesisCLM_apply` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.uPolyOmegaSynthesisCLM_comp_chebyshevDerivativeToUCLM` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.uPolyOmega_toSeq` | STAGE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `RadiiPolynomial.CrossGeometry.valA_comp_joukowskiAevalSymm` | R-ELAB | DELETE | — |
| `RadiiPolynomial.DiscreteConvolution.addDelta_eq_single` | R-ELAB | DELETE | — |
| `RadiiPolynomial.DiscreteConvolution.addRingConvolution_eq_finiteAddConvolution` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.DiscreteConvolution.delta_eq_single` | R-ELAB | DELETE | — |
| `RadiiPolynomial.DiscreteConvolution.ringConvolution_eq_finiteMulConvolution` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.FiberTrivialization.atom_def` | R-ELAB | DELETE | — |
| `RadiiPolynomial.FiberTrivialization.coe_equivL` | R-ELAB | DELETE | — |
| `RadiiPolynomial.FiberTrivialization.coe_equivL_symm` | R-ELAB | DELETE | — |
| `RadiiPolynomial.FiberTrivialization.equiv_symm_add` | R-ELAB | DELETE | — |
| `RadiiPolynomial.FiberTrivialization.equiv_symm_neg` | R-ELAB | DELETE | — |
| `RadiiPolynomial.FiberTrivialization.weight_def` | R-ELAB | DELETE | — |
| `RadiiPolynomial.FinWeighted.ofVec_add` | R-ELAB | DELETE | — |
| `RadiiPolynomial.FinWeighted.ofVec_smul` | R-ELAB | DELETE | — |
| `RadiiPolynomial.FinWeighted.ofVec_sub` | R-ELAB | DELETE | — |
| `RadiiPolynomial.FinWeighted.stdBasis_apply_ne` | R-ELAB | DELETE | — |
| `RadiiPolynomial.FinWeighted.stdBasis_apply_self` | R-ELAB | DELETE | — |
| `RadiiPolynomial.FinWeighted.toVec_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.FinWeightedMatrix.toVec_toWeightedCLM` | R-ELAB | DELETE | — |
| `RadiiPolynomial.FinWeightedMatrix.toWeightedCLM_mul` | DELETE | DELETE | — |
| `RadiiPolynomial.FinWeightedMatrix.toWeightedCLM_one` | DELETE | DELETE | — |
| `RadiiPolynomial.FiniteBlockMatrix.toMatrix_blockId` | DELETE | DELETE | — |
| `RadiiPolynomial.FiniteBlockMatrix.toMatrix_eq_comp` | R-ELAB | DELETE | — |
| `RadiiPolynomial.FiniteWeightedNorm.finWeightedMatrixNorm_le_of_dyadic` | STAGE | STAGE | [staged/B5RecordDyadicP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordDyadicP1.lean) |
| `RadiiPolynomial.FiniteWeightedNorm.finWeightedMatrixNorm_le_of_matrixColNorm_le` | DELETE | DELETE | — |
| `RadiiPolynomial.FiniteWeightedNorm.finWeightedMatrixNorm_le_via_cols` | STAGE | STAGE | [staged/B5RecordDyadicP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordDyadicP1.lean) |
| `RadiiPolynomial.FiniteWeightedNorm.matrixColNorm_le_of_arrayColNormIccSum` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.FνN.norm_mk_single` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.FνN.sub_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.Galerkin.FνN.wnorm_nonneg` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.Jσ` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.Jσ_apply_emb` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.Tσ` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.Tσ_Jσ` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.amb` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.ambL` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.coe_gradCLM` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.evenLift_neg` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.fderiv_galerkin` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.hasFDerivAt_galerkin` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.hasFDerivAt_galerkinFace` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.norm_Jσ` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.norm_Jσ_Tσ_le` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.norm_amb_symm` | R-ELAB | DELETE | — |
| `RadiiPolynomial.Galerkin.norm_fderiv_galerkinFace_sub_le` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.truncConv` | DELETE | DELETE | — |
| `RadiiPolynomial.Galerkin.πN_mul_ιN` | DELETE | DELETE | — |
| `RadiiPolynomial.Gelfand.continuous_character_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CharacterTopology.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CharacterTopology.lean) |
| `RadiiPolynomial.Gelfand.continuous_of_continuous_apply` | DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `RadiiPolynomial.Gelfand.instTopologicalSpaceContinuousAlgHom_radiiPolynomial` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CharacterTopology.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CharacterTopology.lean) |
| `RadiiPolynomial.Gelfand.pointwiseTopology` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CharacterTopology.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CharacterTopology.lean) |
| `RadiiPolynomial.Icc_subset_ordConnectedComponent_of_neg` | DELETE | DELETE | — |
| `RadiiPolynomial.LaurentSpectrum.Annulus` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.Character` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.Character._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.LaurentSpectrum.annulusCharacter` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.annulusCharacter._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.LaurentSpectrum.annulusCharacter_gen` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.annulusCharacter_single` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.annulus_norm_zpow_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.characterEquivAnnulus` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.characterEquivAnnulus._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.LaurentSpectrum.characterEquivAnnulus._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.LaurentSpectrum.characterEquivAnnulus._proof_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.LaurentSpectrum.characterEquivAnnulus._proof_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.LaurentSpectrum.characterHomeomorphAnnulus` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.characterHomeomorphAnnulus._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.LaurentSpectrum.characterHomeomorphAnnulus_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.continuous_annulusCharacter` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.continuous_annulusCharacter_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.continuous_character_apply` | DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `RadiiPolynomial.LaurentSpectrum.instTopologicalSpaceCharacter` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.norm_powerColumn_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.pointwiseTopology` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.powerColumn` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.powerColumn._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.LaurentSpectrum.powerColumn_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.synthesis` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.LaurentSpectrum.synthesis._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.LaurentSpectrum.synthesis._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.LaurentSpectrum.synthesis.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.LaurentSpectrum.synthesis_eq_character` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/LaurentSpectrum.lean) |
| `RadiiPolynomial.MakeCompPoly.reifyBody` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyBody._sparseCasesOn_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyBody._unsafe_rec` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyBody.match_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyBody.match_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyBody.match_6` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyFinIdx` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyFinIdx.match_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyNat` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyNat._sparseCasesOn_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyNat._sparseCasesOn_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyNat._sparseCasesOn_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyNat._sparseCasesOn_6` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyNat._unsafe_rec` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyNat.match_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyNat.match_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyRatScalar` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyRatScalar._unsafe_rec` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyRatScalar.match_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.MakeCompPoly.reifyRatScalar.match_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.NewtonLikeMap.differentiable` | DELETE | DELETE | — |
| `RadiiPolynomial.OmegaScaledReal.omegaWeight_nonneg` | DELETE | DELETE | — |
| `RadiiPolynomial.PairEnclosure` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.PairEnclosure.Icc_subset_component` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.PairEnclosure.casesOn` | NON-FACE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.PairEnclosure.lower` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.PairEnclosure.mk` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.PairEnclosure.neg` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.PairEnclosure.rec` | NON-FACE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.PairEnclosure.recOn` | NON-FACE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.PairEnclosure.upper` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.PhysicalSpectrum.analyticAt_eval_endpoints` | DELETE | DELETE | — |
| `RadiiPolynomial.PhysicalSpectrum.characterEquivEllipse` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Ellipse.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Ellipse.lean) |
| `RadiiPolynomial.PhysicalSpectrum.characterEquivEllipse_apply` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Ellipse.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Ellipse.lean) |
| `RadiiPolynomial.PhysicalSpectrum.characterEquivEllipse_restriction` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Ellipse.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Ellipse.lean) |
| `RadiiPolynomial.PhysicalSpectrum.characterHomeomorphEllipse` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Topology.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Topology.lean) |
| `RadiiPolynomial.PhysicalSpectrum.characterHomeomorphEllipse._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.PhysicalSpectrum.characterHomeomorphEllipse_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Topology.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Topology.lean) |
| `RadiiPolynomial.PhysicalSpectrum.character_apply_eq_tsum` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean) |
| `RadiiPolynomial.PhysicalSpectrum.character_gen_mem_ellipse` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Ellipse.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Ellipse.lean) |
| `RadiiPolynomial.PhysicalSpectrum.chebyshevColumn` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean) |
| `RadiiPolynomial.PhysicalSpectrum.chebyshevColumn_apply` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean) |
| `RadiiPolynomial.PhysicalSpectrum.complexEval_eq_ellipseCharacter` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Holomorphic.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Holomorphic.lean) |
| `RadiiPolynomial.PhysicalSpectrum.continuous_character_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Topology.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Topology.lean) |
| `RadiiPolynomial.PhysicalSpectrum.continuous_ellipseCharacter` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Topology.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Topology.lean) |
| `RadiiPolynomial.PhysicalSpectrum.continuous_ellipseCharacter_apply` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean) |
| `RadiiPolynomial.PhysicalSpectrum.exists_character_iff` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Ellipse.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Ellipse.lean) |
| `RadiiPolynomial.PhysicalSpectrum.focal_sum_le_iff_le_two_mul_semiMajor` | DELETE | DELETE | — |
| `RadiiPolynomial.PhysicalSpectrum.instTopologicalSpaceCharacter` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Topology.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Topology.lean) |
| `RadiiPolynomial.PhysicalSpectrum.joukowski_mem_ellipse` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Ellipse.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Ellipse.lean) |
| `RadiiPolynomial.PhysicalSpectrum.norm_chebyshevColumn_le` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean) |
| `RadiiPolynomial.PhysicalSpectrum.pointwiseTopology` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Topology.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Topology.lean) |
| `RadiiPolynomial.PhysicalSpectrum.pointwiseTopology._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.PhysicalSpectrum.restriction_eq_iff` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Basic.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Basic.lean) |
| `RadiiPolynomial.PhysicalSpectrum.restriction_surjective` | DELETE | DELETE | — |
| `RadiiPolynomial.PhysicalSpectrum.retract_coe` | R-ELAB | DELETE | — |
| `RadiiPolynomial.PhysicalSpectrum.summable_character_series` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean) |
| `RadiiPolynomial.PhysicalSpectrum.synthesis` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean) |
| `RadiiPolynomial.PhysicalSpectrum.synthesis_eq_character` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean) |
| `RadiiPolynomial.PhysicalSpectrum.synthesis_mode` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean) |
| `RadiiPolynomial.PhysicalSpectrum.synthesis_one` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean) |
| `RadiiPolynomial.PhysicalSpectrum.synthesis_single` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Series.lean) |
| `RadiiPolynomial.PhysicalSpectrum.two_mul_semiMajor` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/Spectrum/Ellipse.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/Spectrum/Ellipse.lean) |
| `RadiiPolynomial.PolyZeroData.existsUnique_ofArray` | DELETE | DELETE | — |
| `RadiiPolynomial.Residual.continuous_residual` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.correction` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.correction.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.Residual.correction_identity` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.correction_identity._simp_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.Residual.correction_identity._simp_1_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.Residual.dense_lpOneAlg_finiteSupport` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP2.lean) |
| `RadiiPolynomial.Residual.exists_bezout_iff_dense_certificate` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.exists_bezout_iff_finiteSupport_certificate` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP2.lean) |
| `RadiiPolynomial.Residual.exists_bezout_of_perturbation` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.exists_bezout_of_residual_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.exists_dense_candidate_of_bezout` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.exists_finiteSupport_candidate_of_bezout` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP2.lean) |
| `RadiiPolynomial.Residual.exists_left_inverse_of_residual_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.exists_right_inverse_of_residual_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.leftInverseCorrection` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.leftInverseCorrection.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.Residual.leftInverseCorrection_mul` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.mul_rightInverseCorrection` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.norm_correction_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.norm_correction_sub_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.norm_leftInverseCorrection_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.norm_leftInverseCorrection_le._simp_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.Residual.norm_leftInverseCorrection_sub_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.norm_leftInverseCorrection_sub_le._simp_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.Residual.norm_leftInverseCorrection_sub_le._simp_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.Residual.norm_mul_geomSeries_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.norm_mul_geomSeries_sub_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.norm_residual_add_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.norm_rightInverseCorrection_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.norm_rightInverseCorrection_sub_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.residual` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.residual.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.Residual.residual_add` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.residual_add._abel_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.Residual.rightInverseCorrection` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.rightInverseCorrection.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.Residual.sum_norm_correction_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.Residual.sum_norm_correction_sub_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `RadiiPolynomial.ScalarBlockDiagData.Z₀_norm_le_of_eq_defect` | DELETE | DELETE | — |
| `RadiiPolynomial.ScalarBlockDiagData.finBlock0_ofParts` | R-ELAB | DELETE | — |
| `RadiiPolynomial.ScalarBlockDiagData.injective_toScalarCLM_of_parts` | DELETE | DELETE | — |
| `RadiiPolynomial.ScalarBlockDiagData.norm_toCLM_le` | DELETE | DELETE | — |
| `RadiiPolynomial.ScalarBlockDiagData.norm_toScalarCLM_le` | DELETE | DELETE | — |
| `RadiiPolynomial.ScalarBlockDiagData.tailDiag0_ofParts` | R-ELAB | DELETE | — |
| `RadiiPolynomial.ScalarBlockDiagData.toScalarCLM_toSeq_eq_action` | DELETE | DELETE | — |
| `RadiiPolynomial.StdFinDimData.existsUnique_of_bounds` | DELETE | DELETE | — |
| `RadiiPolynomial.StdFinDimData.isUnit_fderivC` | DELETE | DELETE | — |
| `RadiiPolynomial.SystemBlockDiagData.Z₀_norm_le_of_eq_defect` | DELETE | DELETE | — |
| `RadiiPolynomial.SystemBlockDiagData.Z₁_le_of_fin_kill_tail_dom` | STAGE | STAGE | [staged/B5RecordFinKillP3.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFinKillP3.lean) |
| `RadiiPolynomial.SystemBlockDiagData.actionFinite_eq_zero_of_coeff_fin_zero` | STAGE | STAGE | [staged/B5RecordFinKillP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFinKillP2.lean) |
| `RadiiPolynomial.SystemBlockDiagData.action_comp_finite` | DELETE | DELETE | — |
| `RadiiPolynomial.SystemBlockDiagData.comp_finBlock` | R-ELAB | DELETE | — |
| `RadiiPolynomial.SystemBlockDiagData.comp_tailDiag` | R-ELAB | DELETE | — |
| `RadiiPolynomial.SystemBlockDiagData.norm_comp_of_fin_kill` | STAGE | STAGE | [staged/B5RecordFinKillP3.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFinKillP3.lean) |
| `RadiiPolynomial.SystemBlockDiagData.norm_toCLM_apply_le` | STAGE | STAGE | [staged/B5RecordTaylorY0P2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTaylorY0P2.lean) |
| `RadiiPolynomial.SystemBlockDiagData.norm_toCLM_component_eq_Icc_sum` | STAGE | STAGE | [staged/B5RecordTaylorY0P2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTaylorY0P2.lean) |
| `RadiiPolynomial.SystemBlockDiagData.toBlockDiagOp_finBlock` | R-ELAB | DELETE | — |
| `RadiiPolynomial.SystemBlockDiagData.toBlockDiagOp_tailDiag` | R-ELAB | DELETE | — |
| `RadiiPolynomial.SystemBlockDiagData.toCLM_support` | STAGE | STAGE | [staged/B5RecordTaylorY0P2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTaylorY0P2.lean) |
| `RadiiPolynomial.SystemBlockDiagData.toCoeff_comp_toCLM_eq_action` | DELETE | DELETE | — |
| `RadiiPolynomial.SystemBlockDiagData.toCoeff_id_sub_comp_toCLM` | DELETE | DELETE | — |
| `RadiiPolynomial.SystemBlockDiagData.toCoeff_id_sub_comp_toCLM_finite` | DELETE | DELETE | — |
| `RadiiPolynomial.SystemBlockDiagData.toCoeff_id_sub_comp_toCLM_tail` | DELETE | DELETE | — |
| `RadiiPolynomial.Tactic._aux_RadiiPolynomial_Tactic_FinMatrixBound___elabRules_RadiiPolynomial_Tactic_finMatrixDyadic_1` | NON-FACE | STAGE | [staged/B5RecordDyadicSyntax.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordDyadicSyntax.lean) |
| `RadiiPolynomial.Tactic.finMatrixDyadic` | NON-FACE | STAGE | [staged/B5RecordDyadicSyntax.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordDyadicSyntax.lean) |
| `RadiiPolynomial.TaylorSpectrum.Character` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.Character._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.TaylorSpectrum.Disc` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.characterEquivDisc` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.characterEquivDisc._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.TaylorSpectrum.characterEquivDisc._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.TaylorSpectrum.characterEquivDisc._proof_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.TaylorSpectrum.characterEquivDisc._proof_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.TaylorSpectrum.characterHomeomorphDisc` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.characterHomeomorphDisc._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.TaylorSpectrum.characterHomeomorphDisc_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.continuous_character_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.continuous_discCharacter` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.continuous_discCharacter_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.discCharacter` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.discCharacter._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.TaylorSpectrum.discCharacter_gen` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.discCharacter_single` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.instTopologicalSpaceCharacter` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.norm_powerColumn_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.pointwiseTopology` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.powerColumn` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.powerColumn._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.TaylorSpectrum.powerColumn._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.TaylorSpectrum.powerColumn_apply` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.synthesis` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.TaylorSpectrum.synthesis._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.TaylorSpectrum.synthesis._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.TaylorSpectrum.synthesis.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.TaylorSpectrum.synthesis_eq_character` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/Spectrum.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Spectrum.lean) |
| `RadiiPolynomial.WeightedLp.ColSum.ofFinsets` | DELETE | DELETE | — |
| `RadiiPolynomial.WeightedLp.KernelLiftBound.mono` | DELETE | DELETE | — |
| `RadiiPolynomial.WeightedLp.KernelLiftBound.of_clm` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.RowSum.ofFinsets` | DELETE | DELETE | — |
| `RadiiPolynomial.WeightedLp.TailCheck` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.Q` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.Q.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.b` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.b._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.b.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.bddAbove_tailIndicator` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.check` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.check._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.check_half` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.check_half._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.coeff_Q` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.coeff_Q._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.coeff_Q_integratedProduct_b_11` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.coeff_b` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.coeff_b._proof_1_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.coeff_b._simp_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.coeff_b_of_gt` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.colMass_mQ_10_lt_9` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.colMass_mQ_10_lt_9._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.colMass_mQ_9` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.colMass_mQ_9._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.colMass_mQ_le_9` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.colMass_mQ_le_9._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.colMax_mQ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.instFactLtRealOfNat` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.instFactLtRealOfNatHDiv` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.mQ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.mQ.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.mQhalf` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.mQhalf.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.norm_Q_comp_integratedProduct_b_half_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.norm_Q_comp_integratedProduct_b_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.norm_Q_comp_integratedProduct_b_le_of_check` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.norm_Q_comp_integratedProduct_b_le_row` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.not_check_21` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.not_check_21._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.not_check_col10` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.not_check_col10._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.remainder` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.rowConst_mQ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.rowConst_mQ._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.rowConst_mul_colMax` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.rowMass_mQ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.rowMass_mQ._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.symbolMass_b_half` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.symbolMass_b_one` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.tailKernelCLM_b` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.tailKernel_11_10` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.tailKernel_11_10._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.tailKernel_11_9` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.tailKernel_11_9._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.tailKernel_12_10` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.tailKernel_12_10._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.tailKernel_13_11` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.tailKernel_13_11._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.βQ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.βQ.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.βQ_of_gt` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.βQ_of_gt._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.βQ_of_gt._proof_1_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.βQ_of_gt._proof_1_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.βQ_of_gt._proof_1_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.TailKernelChecks.βQ_of_gt._proof_1_6` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/TailKernelChecks.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.X` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.X._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.X.congr_simp` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.coeff` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.coeff.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.coeff_integratedProduct_succ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.coeff_integratedProduct_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.coeff_integrationCLM_succ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.coeff_integrationCLM_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.delta` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.geoPos` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.geoWeight` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.geoWeight.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.integratedProduct` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.integratedProduct._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.integratedProduct_delta_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.integratedProduct_single_single` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.integratedProduct_symm` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.integrationCLM` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.integrationCLM._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.integrationCLM._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.integrationCLM._proof_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.integrationCLM._proof_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.integrationCLM.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.norm_delta` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.norm_integratedProduct_apply_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.norm_integratedProduct_eq` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.norm_integratedProduct_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.norm_integratedProduct_left_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.norm_integrationCLM_eq` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.norm_sq_eq_tsum` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.Taylor.not_bound_below_radius` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.Pi` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.Pi.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.Pi_comp_Pi` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.Pi_comp_Q` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.Q` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.Q._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.Q.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.Q_comp_Pi` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.Q_comp_Q` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.Q_comp_withHead` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.Xp` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.coeff_Pi` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.coeff_Pi._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.coeff_Pi._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.coeff_Pi_fin` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.coeff_Pi_of_gt` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.coeff_Q_fin` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.coeff_Q_of_gt` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.coeff_headCore_fin` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.coeff_headCore_of_gt` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.coeff_headCore_of_gt._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.coeff_withHead_fin` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.coeff_withHead_of_gt` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.headCore` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.headCore._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.headCore._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.headCore._proof_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.headCore._proof_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.headCore._proof_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.headCore._proof_6` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.headCore._proof_7` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.headCore.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.withHead` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.withHead.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.withHead_comp` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.withHead_comp_Q` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.withHead_one` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.WithHead.withHead_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `RadiiPolynomial.WeightedLp.abs_eval_embedCLM_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.cast_rowMass` | STAGE | STAGE | [staged/B5RecordTailKernelSchur.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTailKernelSchur.lean) |
| `RadiiPolynomial.WeightedLp.coeff_embedCLM` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.coeff_injective` | DELETE | DELETE | — |
| `RadiiPolynomial.WeightedLp.coeff_kernelCLM_single` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.coeff_kernelLiftCLM` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.coeff_neg` | R-ELAB | DELETE | — |
| `RadiiPolynomial.WeightedLp.coeff_single_of_ne` | DELETE | DELETE | — |
| `RadiiPolynomial.WeightedLp.coeff_sum_smul_kcol` | DELETE | DELETE | — |
| `RadiiPolynomial.WeightedLp.coeff_symbolAction₀_apply` | DELETE | DELETE | — |
| `RadiiPolynomial.WeightedLp.coeff_tailKernelCLM` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.colMass_le_colMax` | DELETE | DELETE | — |
| `RadiiPolynomial.WeightedLp.colMass_le_rowMass_div` | STAGE | STAGE | [staged/B5RecordTailKernelSchur.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTailKernelSchur.lean) |
| `RadiiPolynomial.WeightedLp.colSum_tailKernel` | STAGE | STAGE | [staged/B5RecordTailKernelSchur.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTailKernelSchur.lean) |
| `RadiiPolynomial.WeightedLp.conjL1_apply_toLp` | R-ELAB | DELETE | — |
| `RadiiPolynomial.WeightedLp.conjL1_eq_kernelLiftCLM` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP1.lean) |
| `RadiiPolynomial.WeightedLp.embedCLM` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.embedCLM._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.embedCLM.congr_simp` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Solution.lean) |
| `RadiiPolynomial.WeightedLp.embedConst` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.embedConst.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.embedConst_pos` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.embedConst_sq` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.embedLM` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.embedLM._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.embedLM._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.embedLM._proof_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.embedLM._proof_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.embedLM._proof_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.embedLM._proof_6` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.embedLM._proof_7` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.embedLM._proof_8` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.eq_kernelLiftCLM` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.eval_embedCLM` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.hasSum_coeff_kernelLiftCLM` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.hasSum_row_tailKernel` | STAGE | STAGE | [staged/B5RecordTailKernelSchur.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTailKernelSchur.lean) |
| `RadiiPolynomial.WeightedLp.instDecidableTailCheck` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.instDecidableTailCheck._aux_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.invWeightSeq` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.kcol_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.WeightedLp.kernelLiftCLM` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.kernelLiftCLM_congr` | R-ELAB | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.kernelLiftCLM_eq_kernelCLM` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.kernelLiftCLM_single` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.liftCLM_congr` | R-ELAB | DELETE | — |
| `RadiiPolynomial.WeightedLp.mem_l1Weighted_coeff` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.norm_Q_comp_integratedProduct_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.norm_Q_comp_integratedProduct_le_of_check` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.norm_apply_eq_abs_coeff` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.norm_apply_invWeightSeq` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.norm_embedCLM_apply_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.norm_embedCLM_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.norm_equiv_inv_weight` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.norm_kernelCLM_two_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.norm_kernelLiftCLM_le` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.norm_sum_single` | DELETE | DELETE | — |
| `RadiiPolynomial.WeightedLp.norm_sum_single_two_sq` | R-ELAB | DELETE | — |
| `RadiiPolynomial.WeightedLp.norm_tailKernelCLM_le_of_sq` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.norm_tailKernelCLM_le_row` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.norm_tailKernelCLM_two_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.not_dense_finsupp_top` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.one_le_dist_invWeightSeq` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.one_le_norm_invWeightSeq_sub` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.opNorm_le_of_colSum` | DELETE | DELETE | — |
| `RadiiPolynomial.WeightedLp.rawSymbol_single` | DELETE | DELETE | — |
| `RadiiPolynomial.WeightedLp.rowMass` | STAGE | STAGE | [staged/B5RecordTailKernelSchur.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTailKernelSchur.lean) |
| `RadiiPolynomial.WeightedLp.rowMass_mono` | STAGE | STAGE | [staged/B5RecordTailKernelSchur.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTailKernelSchur.lean) |
| `RadiiPolynomial.WeightedLp.rowMass_nonneg` | STAGE | STAGE | [staged/B5RecordTailKernelSchur.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTailKernelSchur.lean) |
| `RadiiPolynomial.WeightedLp.rowSum_tailKernel` | STAGE | STAGE | [staged/B5RecordTailKernelSchur.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTailKernelSchur.lean) |
| `RadiiPolynomial.WeightedLp.schurBound_tailKernel` | STAGE | STAGE | [staged/B5RecordTailKernelSchur.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTailKernelSchur.lean) |
| `RadiiPolynomial.WeightedLp.schurBound_tailKernel_of_le` | STAGE | STAGE | [staged/B5RecordTailKernelSchur.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTailKernelSchur.lean) |
| `RadiiPolynomial.WeightedLp.schurBound_weightedScalar_iff` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.sq_ratio_lt_one` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.sum_abs_coeff_mul_pow_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.sum_abs_coeff_mul_pow_le._simp_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.sum_abs_coeff_mul_pow_le._simp_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.sum_abs_coeff_mul_pow_le._simp_1_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.sum_abs_coeff_mul_pow_le._simp_1_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.sum_abs_coeff_mul_pow_le._simp_1_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.sum_abs_coeff_mul_pow_le._simp_1_6` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.sum_abs_coeff_mul_pow_le._simp_1_7` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `RadiiPolynomial.WeightedLp.sum_range_symbolMass_le` | STAGE | STAGE | [staged/B5RecordTailKernelSchur.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTailKernelSchur.lean) |
| `RadiiPolynomial.WeightedLp.summable_norm_kernel` | STAGE | STAGE | [staged/B5RecordFiniteSynthesisP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteSynthesisP2.lean) |
| `RadiiPolynomial.WeightedLp.tailKernelCLM` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.tailKernelCLM._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.tailKernelCLM.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.tailKernelCLM_eq_Q_comp_integratedProduct` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.tailKernelCLM_eq_Q_comp_integratedProduct._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/TailKernel.lean) |
| `RadiiPolynomial.WeightedLp.tailKernel_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.WeightedLp.tsum_row_tailKernel` | STAGE | STAGE | [staged/B5RecordTailKernelSchur.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTailKernelSchur.lean) |
| `RadiiPolynomial.WeightedScalar.equiv_toAddEquiv` | R-ELAB | DELETE | — |
| `RadiiPolynomial.WeightedScalar.fiberTrivialization_equiv` | R-ELAB | DELETE | — |
| `RadiiPolynomial.WeightedScalar.instCoeOut` | R-ELAB | DELETE | — |
| `RadiiPolynomial.WeightedScalar.norm_neg'` | R-ELAB | DELETE | — |
| `RadiiPolynomial.WeightedScalar.norm_zero'` | R-ELAB | DELETE | — |
| `RadiiPolynomial.WeightedScalar.toReal_ofReal` | R-ELAB | DELETE | — |
| `RadiiPolynomial.XL1.ext_iff` | R-ELAB | fragment | — |
| `RadiiPolynomial.XL1.opNorm_le_of_fin_kill_tail_eq` | STAGE | STAGE | [staged/B5RecordFinKillP3.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFinKillP3.lean) |
| `RadiiPolynomial.XL1_fin1_eq_const` | DELETE | DELETE | — |
| `RadiiPolynomial.Z_bound` | DELETE | DELETE | — |
| `RadiiPolynomial.Z₀_norm_le_of_defect_plus_tail_error` | DELETE | DELETE | — |
| `RadiiPolynomial.Z₂_ball_bound_of_affine_leftMul_of_poly` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct._aux_RadiiPolynomial_Algebra_Convolution_CauchyProduct___unexpand_RadiiPolynomial_cauchyProduct_1` | NON-FACE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.assoc` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.coeff_toPowerSeriesLinearEquiv` | R-ELAB | DELETE | — |
| `RadiiPolynomial.cauchyProduct.comm` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.delta_left` | R-ELAB | DELETE | — |
| `RadiiPolynomial.cauchyProduct.delta_right` | R-ELAB | DELETE | — |
| `RadiiPolynomial.cauchyProduct.eq_coeff_mul` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.left_distrib` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.mul_one` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.mul_smul` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.mul_zero` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.one` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.one_eq_single` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.one_mul` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.one_succ` | R-ELAB | DELETE | — |
| `RadiiPolynomial.cauchyProduct.one_zero` | R-ELAB | DELETE | — |
| `RadiiPolynomial.cauchyProduct.right_distrib` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.single_mul_single` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.toPowerSeriesLinearEquiv` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.toPowerSeriesLinearEquiv_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.cauchyProduct.toPowerSeriesLinearEquiv_symm_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.cauchyProduct.toPowerSeriesLinearEquiv_symm_apply_coeff` | R-ELAB | DELETE | — |
| `RadiiPolynomial.cauchyProduct.toPowerSeries_injective` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.toPowerSeries_mul` | STAGE | STAGE | [staged/B5RecordPowerSeriesBridge.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordPowerSeriesBridge.lean) |
| `RadiiPolynomial.cauchyProduct.toPowerSeries_one` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.toPowerSeries_single` | STAGE | STAGE | [staged/B5RecordPowerSeriesBridge.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordPowerSeriesBridge.lean) |
| `RadiiPolynomial.cauchyProduct.zero_mul` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.zero_of_support` | DELETE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.«_aux_RadiiPolynomial_Algebra_Convolution_CauchyProduct___macroRules_RadiiPolynomial_cauchyProduct_term_⋆__1»` | NON-FACE | DELETE | — |
| `RadiiPolynomial.cauchyProduct.«term_⋆_»` | R-ELAB | DELETE | — |
| `RadiiPolynomial.chebyshevToU_CLM_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.chebyshevToU_norm_le` | DELETE | DELETE | — |
| `RadiiPolynomial.checkMatrixNormDyadic` | STAGE | STAGE | [staged/B5RecordDyadicP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordDyadicP1.lean) |
| `RadiiPolynomial.colNormSumDyadic` | STAGE | STAGE | [staged/B5RecordDyadicP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordDyadicP1.lean) |
| `RadiiPolynomial.colNormTermEval` | STAGE | STAGE | [staged/B5RecordDyadicP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordDyadicP1.lean) |
| `RadiiPolynomial.colNormTermEval_correct` | STAGE | STAGE | [staged/B5RecordDyadicP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordDyadicP1.lean) |
| `RadiiPolynomial.colTailQ` | DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `RadiiPolynomial.colTailQ_nonneg` | DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `RadiiPolynomial.colTailTermQ` | DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `RadiiPolynomial.convexOn_hornerEval_mul_pow` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.convexOn_radiiPolynomial_of_poly` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.defectOfBlockDiagOp_toCLM_eq` | DELETE | DELETE | — |
| `RadiiPolynomial.derivShift_CLM` | STAGE | STAGE | [staged/B5RecordOmegaWeightFamily.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOmegaWeightFamily.lean) |
| `RadiiPolynomial.derivShift_CLM_apply` | STAGE | STAGE | [staged/B5RecordOmegaWeightFamily.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOmegaWeightFamily.lean) |
| `RadiiPolynomial.derivShift_linear_add` | STAGE | STAGE | [staged/B5RecordOmegaWeightFamily.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOmegaWeightFamily.lean) |
| `RadiiPolynomial.derivShift_linear_smul` | STAGE | STAGE | [staged/B5RecordOmegaWeightFamily.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOmegaWeightFamily.lean) |
| `RadiiPolynomial.derivShift_norm_le` | STAGE | STAGE | [staged/B5RecordOmegaWeightFamily.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOmegaWeightFamily.lean) |
| `RadiiPolynomial.enclosure_Icc` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.enclosure_Icc_poly` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.enclosure_of_differentiable` | DELETE | DELETE | — |
| `RadiiPolynomial.enclosure_of_differentiableOn` | DELETE | DELETE | — |
| `RadiiPolynomial.enclosure_pair` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.enclosure_pair_poly` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.fderiv_diff_of_affine_leftMul` | DELETE | DELETE | — |
| `RadiiPolynomial.finBlockAction_eq_zero_of_coeff_zero` | STAGE | STAGE | [staged/B5RecordFinKillP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFinKillP2.lean) |
| `RadiiPolynomial.finiteAddConvolution.add_left` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteAddConvolution.add_right` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteAddConvolution.assoc` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteAddConvolution.comm` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteAddConvolution.single_single` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteAddConvolution.single_zero_left` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteAddConvolution.single_zero_left_apply` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteAddConvolution.single_zero_right` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteAddConvolution.single_zero_right_apply` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteAddConvolution.smul_right` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteAddConvolution.zero_left` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteAddConvolution.zero_right` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteBlockMatrixNorm_le_of_blockRowNorm_le` | DELETE | DELETE | — |
| `RadiiPolynomial.finiteMulConvolution.add_left` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteMulConvolution.add_right` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteMulConvolution.assoc` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteMulConvolution.comm` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteMulConvolution.single_one_left` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteMulConvolution.single_one_left_apply` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteMulConvolution.single_one_right` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteMulConvolution.single_one_right_apply` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteMulConvolution.single_single` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteMulConvolution.smul_right` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteMulConvolution.zero_left` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.finiteMulConvolution.zero_right` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.generalRadiiPolynomial_neg_of_Q` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.general_fixed_point_theorem` | DELETE | DELETE | — |
| `RadiiPolynomial.hasFDerivWithinAt_fderiv_of_differentiable` | DELETE | DELETE | — |
| `RadiiPolynomial.hasFDerivWithinAt_fderiv_of_differentiableOn` | DELETE | DELETE | — |
| `RadiiPolynomial.hornerEval` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.hornerEval_cons` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.hornerEval_nil` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.l1Chebyshev.IsSymmetric.neg` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.IsSymmetric.sub` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.OneSided.C₂` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.C₂_le_C₃` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.C₂_le_three` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.C₂_nonneg` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.C₃` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.C₃_eq_left_iff` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.C₃_le_five` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.C₃_nonneg` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.borderedToWeighted_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.OneSided.borderedToWeighted_toSeq` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.OneSided.cosMul` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.cosMul_apply` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.cosMul_assoc` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.cosMul_comm` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.cosMul_cosMul` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.cosMul_one_left` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.cosMul_one_right` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.cosMul_single_self` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.cosMul_single_single` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.cosMul_toSeq` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.cosMul₃` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.cosMul₃_apply` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.cosMul₃_eq` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.cosMul₃_single` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.isSymmetric_symExt` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.norm_borderedToWeighted_le` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.OneSided.norm_cosMul_le` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.norm_cosMul_single_self` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.norm_cosMul_single_single_le` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.norm_cosMul₃_le` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.norm_cosMul₃_single_le` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.norm_restr_single` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.norm_symExt_le` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.one_le_C₂` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.opNorm_cosMul_eq` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.opNorm_cosMul_le` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.opNorm_cosMul₃_eq` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.opNorm_cosMul₃_le` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.opNorm_restr_le` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.OneSided.opNorm_symExt_le` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.restr_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.OneSided.restr_single_int` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.restr_single_natCast` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.restr_single_negSucc` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.restr_symExt` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.symExt` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.symExt_apply` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.symExt_mem_symmetricSubalgebra` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.symExt_restr` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.symExt_single` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.symExt_single_zero` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.symExt_toSeq` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.t` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.t_le_half_iff` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.t_le_one` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.OneSided.t_pos` | STAGE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `RadiiPolynomial.l1Chebyshev.algHom_ext` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.coe_symmetricRetract` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.conj_evalLaurentC` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/UnitLift.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/UnitLift.lean) |
| `RadiiPolynomial.l1Chebyshev.conj_evalLaurentC_of_isSymmetric` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/UnitLift.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/UnitLift.lean) |
| `RadiiPolynomial.l1Chebyshev.eq_unitLift_gen` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.evalAtCLM_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.evalLaurentC_eq_re_of_isSymmetric` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/UnitLift.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/UnitLift.lean) |
| `RadiiPolynomial.l1Chebyshev.evalLaurentC_gen` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.evalLaurentC_inv_of_isSymmetric` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/UnitLift.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/UnitLift.lean) |
| `RadiiPolynomial.l1Chebyshev.evalLaurentC_symmetrize_eq_re` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/UnitLift.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/UnitLift.lean) |
| `RadiiPolynomial.l1Chebyshev.eval_at_one` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.eval_neg` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.eval_sub` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.eval_symmetrize` | STAGE | STAGE | [staged/B5RecordIVPBoundaryP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP1.lean) |
| `RadiiPolynomial.l1Chebyshev.finSum_le_norm` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.hasSum_single` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.hasSum_single_mapCLM` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.inv_le_norm_genUnit` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.isClosed_symmetricSubalgebra` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/SymmetricSubalgebra.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/SymmetricSubalgebra.lean) |
| `RadiiPolynomial.l1Chebyshev.isSymmetric_zero` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.mem_symmetricSubalgebra` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.natEmbed_single` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.nonnegRestrictCLM_apply` | R-ELAB | STAGE | [staged/B5Records/Spectra/Chebyshev/SymmetricSubalgebra.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/SymmetricSubalgebra.lean) |
| `RadiiPolynomial.l1Chebyshev.nonnegRestrictCLM_norm_le` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.nonnegRestrictCLM_norm_of_isSymmetric` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.nonnegRestrict_symmetrize` | STAGE | STAGE | [staged/B5RecordSymmetricStorageBordered.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordSymmetricStorageBordered.lean) |
| `RadiiPolynomial.l1Chebyshev.norm_genUnit_le` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.norm_symmetricRetract_le` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.norm_unitLift_apply_le` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.opNorm_eq_iSup_cols₂` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.opNorm_eq_iSup_cols₃` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.physicalBorderedEquiv` | STAGE | STAGE | [staged/B5RecordSymmetricStorageBordered.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordSymmetricStorageBordered.lean) |
| `RadiiPolynomial.l1Chebyshev.physicalBorderedEquiv_apply` | STAGE | STAGE | [staged/B5RecordSymmetricStorageBordered.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordSymmetricStorageBordered.lean) |
| `RadiiPolynomial.l1Chebyshev.single_smul` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.symmetricEvalCharacter_apply` | R-ELAB | STAGE | [staged/B5Records/Spectra/Chebyshev/SymmetricSubalgebra.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/SymmetricSubalgebra.lean) |
| `RadiiPolynomial.l1Chebyshev.symmetricRetract_coe` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.symmetricSubalgebra.instCompleteSpace` | R-ELAB | STAGE | [staged/B5RecordSymmetricStorageBordered.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordSymmetricStorageBordered.lean) |
| `RadiiPolynomial.l1Chebyshev.symmetrize_CLM_norm_le` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.toSeq_eq_toRealSeq` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.unitLift` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.unitLift_gen` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Chebyshev.unitLift_gen_inv` | DELETE | DELETE | — |
| `RadiiPolynomial.l1OfArrayQ` | DELETE | DELETE | — |
| `RadiiPolynomial.l1OfArrayQ_toSeq` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Omega.add_toSeq` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Omega.eval_add` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Omega.eval_at_zero` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Omega.eval_smul` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Omega.ext` | STAGE | STAGE | [staged/B5RecordOmegaWeightFamily.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOmegaWeightFamily.lean) |
| `RadiiPolynomial.l1Omega.geom_to_omega_mem` | STAGE | STAGE | [staged/B5RecordOmegaWeightFamily.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOmegaWeightFamily.lean) |
| `RadiiPolynomial.l1Omega.mem_sub` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Omega.mk_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Omega.neg_toSeq` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Omega.norm_eq_tsum` | STAGE | STAGE | [staged/B5RecordOmegaWeightFamily.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOmegaWeightFamily.lean) |
| `RadiiPolynomial.l1Omega.smul_toSeq` | R-ELAB | STAGE | [staged/B5Records/Spectra/Geometric/Omega.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Omega.lean) |
| `RadiiPolynomial.l1Omega.sub_toSeq` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Omega.toSeq_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Omega.zero_toSeq` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.aeval` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.aeval_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.aeval_gen` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.aeval_of_norm_le'` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.aeval_of_norm_le'_gen` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.aeval_of_norm_le_comp_radiusRestrict` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/RadiusRestriction.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/RadiusRestriction.lean) |
| `RadiiPolynomial.l1Weighted.aeval_single` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.character_classification_evalC` | STAGE | STAGE | [staged/B5Records/Spectra/Geometric/EvalC.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/EvalC.lean) |
| `RadiiPolynomial.l1Weighted.coeff_trunc` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.continuous_eval` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.differentiable_toSeq` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.eq_aeval_gen` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.eval_double_finset_sum` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.eval_finset_sum` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.eval_neg` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.eval_one` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.eval_single` | R-ELAB | STAGE | [staged/B5RecordIVPBoundaryP3.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP3.lean) |
| `RadiiPolynomial.l1Weighted.eval_sub` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.eval_zero` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.exists_eval_eq_of_analyticAt` | STAGE | STAGE | [staged/B5RecordTaylorAnalytic.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTaylorAnalytic.lean) |
| `RadiiPolynomial.l1Weighted.ext_of_eventuallyEq_eval` | STAGE | STAGE | [staged/B5RecordTaylorAnalytic.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordTaylorAnalytic.lean) |
| `RadiiPolynomial.l1Weighted.hasDerivAt_eval_single` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.hasFPowerSeriesAt_eval` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.leftMul_add` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.leftMul_sub` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.mk_val_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.norm_aeval_apply_le` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.norm_aeval_of_norm_le'_apply_le` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.norm_aeval_of_norm_le_apply_le` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.norm_evalC_le` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.norm_gen_le` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.norm_radiusRestrict` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/RadiusRestriction.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/RadiusRestriction.lean) |
| `RadiiPolynomial.l1Weighted.norm_radiusRestrict_apply_le` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/RadiusRestriction.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/RadiusRestriction.lean) |
| `RadiiPolynomial.l1Weighted.norm_radiusRestrict_le` | DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `RadiiPolynomial.l1Weighted.norm_tailProj_CLM_le` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.norm_trunc_CLM_le` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.one_toSeq_succ` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.one_toSeq_zero` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.opNorm_eq_iSup_cols₂` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.opNorm_eq_iSup_cols₃` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.radiusRestrict` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/RadiusRestriction.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/RadiusRestriction.lean) |
| `RadiiPolynomial.l1Weighted.radiusRestrict._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.l1Weighted.radiusRestrict._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.l1Weighted.radiusRestrict.congr_simp` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.l1Weighted.radiusRestrict.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.l1Weighted.radiusRestrict_comp` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/RadiusRestriction.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/RadiusRestriction.lean) |
| `RadiiPolynomial.l1Weighted.radiusRestrict_gen` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/RadiusRestriction.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/RadiusRestriction.lean) |
| `RadiiPolynomial.l1Weighted.radiusRestrict_injective` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/RadiusRestriction.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/RadiusRestriction.lean) |
| `RadiiPolynomial.l1Weighted.radiusRestrict_refl` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/RadiusRestriction.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/RadiusRestriction.lean) |
| `RadiiPolynomial.l1Weighted.ratSmul_eq` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.single_CLM_toSeq_of_ne` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.single_CLM_toSeq_same` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.single_mul` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.single_toSeq_of_ne` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.single_toSeq_same` | R-ELAB | STAGE | [staged/B5RecordIVPBoundaryP2.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP2.lean) |
| `RadiiPolynomial.l1Weighted.smul_proj_eq_leftMul_comp_proj` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.tendsto_trunc` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.toSeq_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.toSeq_nsmul_sub_one` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.toSeq_radiusRestrict` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/RadiusRestriction.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/RadiusRestriction.lean) |
| `RadiiPolynomial.l1Weighted.toSeq_smul_sub_one` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.trunc` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.trunc_CLM` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.trunc_CLM_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.l1Weighted.trunc_eq_sum` | DELETE | DELETE | — |
| `RadiiPolynomial.l1Weighted.zero_toSeq` | R-ELAB | STAGE | [staged/B5RecordFinKillP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFinKillP1.lean) |
| `RadiiPolynomial.lambdaN` | DELETE | DELETE | — |
| `RadiiPolynomial.lambdaN_CLM` | DELETE | DELETE | — |
| `RadiiPolynomial.lambdaN_CLM_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lambdaN_gt_mode` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lambdaN_le_mode` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lambdaN_linear_add` | DELETE | DELETE | — |
| `RadiiPolynomial.lambdaN_linear_smul` | DELETE | DELETE | — |
| `RadiiPolynomial.lambdaN_norm_le` | DELETE | DELETE | — |
| `RadiiPolynomial.le_of_forall_pow_le_mul_pow` | STAGE | STAGE | [staged/B5Records/Spectra/WeightedL1/UniversalProperty.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/WeightedL1/UniversalProperty.lean) |
| `RadiiPolynomial.lpOneAlg.abs_mulToRealSeq_le` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.abs_toRealSeq_le` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.coe_fiberSingleₗᵢ` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.colRatio` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.colRatio_add_of_comp_split` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.colRatio_add_of_head_tail` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.colRatio_add_of_head_zero` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.colRatio_bddAbove` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.colRatio_eq_zero_of_comp_headProj` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.colRatio_eq_zero_of_comp_tailProj` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.colRatio_le_opNorm` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.colRatio_nonneg` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.cols_le_opNorm` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.cols_le_opNorm₂` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.cols_le_opNorm₃` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.continuousLinearMap_ext'` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.diagCLM_comp_headProj` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.evalCLM_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.evalLaurent` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.evalLaurent_apply` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.evalLaurent_gen` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.evalLaurent_single` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.exists_eq_geomAeval` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.exists_eq_geomUnitLift` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.fiberSingle_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.fiberSingle_zero` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.geomAeval_of_norm_le'` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.geomAeval_of_norm_le'_gen` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.geomAeval_toContinuousLinearMap` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.geomUnitLift_gen_inv` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.geomUnitLift_toContinuousLinearMap` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.hasSum_fiberSingle_mapCLM` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.headProj_add_tailProj` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.headProj_apply_eq_self_iff` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.headProj_apply_eq_self_iff_fiber` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.headProj_comp_diagCLM` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.headProj_comp_headProj` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.headProj_comp_tailProj` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.headProj_single` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.headSymbol_eq_indicator` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.head_comp_eq_zero_iff_tail_comp_eq_self` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.inv_le_norm_genUnit` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/UnitLift.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/UnitLift.lean) |
| `RadiiPolynomial.lpOneAlg.isIdempotentElem_headProj` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.liftAlgHom_toContinuousLinearMap` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.mulMul_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.mul_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.norm_add_of_head_tail` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.norm_evalLaurent_apply_le` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.norm_genUnit_le` | STAGE | STAGE | [staged/B5Records/Spectra/Chebyshev/UnitLift.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Chebyshev/UnitLift.lean) |
| `RadiiPolynomial.lpOneAlg.norm_gen_le` | STAGE | STAGE | [staged/B5Records/Spectra/Geometric/Aeval.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Aeval.lean) |
| `RadiiPolynomial.lpOneAlg.norm_gen_pow` | STAGE | STAGE | [staged/B5Records/Spectra/Geometric/Aeval.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/Aeval.lean) |
| `RadiiPolynomial.lpOneAlg.norm_geomAeval_apply_le` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.norm_geomAeval_of_norm_le'_apply_le` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.norm_headProj_apply_le` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.norm_le_of_cols₂` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.norm_le_of_cols₃` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.norm_mulLeftCLM_le` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.norm_mulRightCLM_le` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.norm_singleCLM` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.norm_single_geomFiberZ` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.opNorm_add_eq_iSup` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.opNorm_add_eq_iSup_of_head_zero` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.opNorm_eq_iSup_cols` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.opNorm_eq_iSup_cols₂` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.opNorm_eq_iSup_cols₃` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.opNorm_joint_eq_iSup` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.opNorm_le_iff_cols` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.opNorm_le_iff_cols₂` | DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `RadiiPolynomial.lpOneAlg.opNorm_le_iff_cols₃` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.opNorm_le_of_cols` | DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `RadiiPolynomial.lpOneAlg.opNorm_le_of_cols₂` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.opNorm_le_of_cols₃` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `RadiiPolynomial.lpOneAlg.pow_le_of_norm_le'` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.singleCLM` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.singleCLM_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.summable_abs_mulToRealSeq` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.summable_abs_toRealSeq` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.summable_norm_shift` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.tailProj_apply_eq_self_iff` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.tailProj_apply_eq_self_iff_fiber` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.tailProj_comp_diagCLM` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.tailProj_comp_headProj` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.tailProj_comp_tailProj` | DELETE | DELETE | — |
| `RadiiPolynomial.lpOneAlg.tailProj_single` | STAGE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `RadiiPolynomial.lpOneAlg.toLp_add` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.toLp_neg` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.toLp_single` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.toLp_sub` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.toLp_toLpₗᵢ_symm` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.toLp_zero` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.toLpₗᵢ_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.toLpₗᵢ_symm_single` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpOneAlg.toRealSeq_injective` | DELETE | DELETE | — |
| `RadiiPolynomial.lpWeighted.add_toSeq` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpWeighted.ext` | DELETE | DELETE | — |
| `RadiiPolynomial.lpWeighted.mk_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpWeighted.mk_val_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpWeighted.neg_toSeq` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpWeighted.smul_toSeq` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpWeighted.sub_toSeq` | R-ELAB | DELETE | — |
| `RadiiPolynomial.lpWeighted.zero_toSeq` | R-ELAB | DELETE | — |
| `RadiiPolynomial.map_finiteAddConvolution` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.map_finiteMulConvolution` | STAGE | STAGE | [staged/B5RecordFiniteFiberConvolution.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordFiniteFiberConvolution.lean) |
| `RadiiPolynomial.map_hornerEval` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.mem_colNormSumDyadic` | STAGE | STAGE | [staged/B5RecordDyadicP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordDyadicP1.lean) |
| `RadiiPolynomial.minimalPeriod_eq_of_no_smaller` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordPeriodicPoint.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordPeriodicPoint.lean) |
| `RadiiPolynomial.newton_operator_Y_bound` | DELETE | DELETE | — |
| `RadiiPolynomial.newton_operator_derivative_bound_general` | DELETE | DELETE | — |
| `RadiiPolynomial.newton_operator_derivative_bound_simple` | DELETE | DELETE | — |
| `RadiiPolynomial.newton_operator_fderiv` | DELETE | DELETE | — |
| `RadiiPolynomial.nonnegRestrict_norm_of_isSymmetric` | STAGE | STAGE | [staged/B5RecordSymmetricStorageBordered.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordSymmetricStorageBordered.lean) |
| `RadiiPolynomial.norm_XL1_fin1` | DELETE | DELETE | — |
| `RadiiPolynomial.norm_fderiv_diff_of_affine_leftMul` | DELETE | DELETE | — |
| `RadiiPolynomial.norm_toCLM_le_of_Q` | DELETE | DELETE | — |
| `RadiiPolynomial.ofCoeff_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.omegaWeight_le_nu_mul_pow` | STAGE | STAGE | [staged/B5RecordOmegaWeightFamily.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOmegaWeightFamily.lean) |
| `RadiiPolynomial.periodicPoint_of_differentiableOn` | STAGE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordPeriodicPoint.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordPeriodicPoint.lean) |
| `RadiiPolynomial.radiiPolyQ` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.radiiPolyQ_cast` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.radiiPoly_neg_on_Icc_of_convexOn` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.radiiPolynomial_alt_form` | DELETE | DELETE | — |
| `RadiiPolynomial.radiiPolynomial_neg_of_Q` | STAGE | STAGE | [staged/B5RecordRadiiIntervals.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordRadiiIntervals.lean) |
| `RadiiPolynomial.radii_poly_neg_implies_Z_bound_lt_one` | DELETE | DELETE | — |
| `RadiiPolynomial.radii_polynomial_theorem_EtoF_local` | DELETE | DELETE | — |
| `RadiiPolynomial.scalarBlockDiagAction` | DELETE | DELETE | — |
| `RadiiPolynomial.scalarBlockDiagActionEval` | DELETE | DELETE | — |
| `RadiiPolynomial.scalarBlockDiagActionEval_correct` | DELETE | DELETE | — |
| `RadiiPolynomial.shift` | DELETE | DELETE | — |
| `RadiiPolynomial.shiftDivN_leftMul_tail_col_antitone` | DELETE | DELETE | — |
| `RadiiPolynomial.shiftDivN_leftMul_tail_cols_le_of_Q` | DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `RadiiPolynomial.shiftDivN_leftMul_tail_cols_le_of_Q._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.shiftDivN_leftMul_tail_cols_le_of_Q._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.shiftDivN_leftMul_tail_le_of_cols` | DELETE | DELETE | — |
| `RadiiPolynomial.shiftDivN_single_tailTsum_eq_colTailQ` | DELETE | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `RadiiPolynomial.shiftDivN_single_tailTsum_eq_colTailQ._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.shiftDivN_single_tailTsum_eq_colTailQ._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.shiftDivN_single_tailTsum_eq_colTailQ._proof_1_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.shiftDivN_single_tailTsum_eq_colTailQ._proof_1_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `RadiiPolynomial.shiftDivN_zero_mode` | STAGE | STAGE | [staged/B5RecordIVPBoundaryP4.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordIVPBoundaryP4.lean) |
| `RadiiPolynomial.shift_CLM` | DELETE | DELETE | — |
| `RadiiPolynomial.shift_CLM_apply` | R-ELAB | DELETE | — |
| `RadiiPolynomial.shift_linear_add` | DELETE | DELETE | — |
| `RadiiPolynomial.shift_linear_smul` | DELETE | DELETE | — |
| `RadiiPolynomial.shift_norm_le` | DELETE | DELETE | — |
| `RadiiPolynomial.shift_succ_mode` | R-ELAB | DELETE | — |
| `RadiiPolynomial.shift_zero_mode` | R-ELAB | DELETE | — |
| `RadiiPolynomial.simple_maps_closedBall_to_itself` | DELETE | DELETE | — |
| `RadiiPolynomial.simple_radii_polynomial_theorem_EtoF` | DELETE | DELETE | — |
| `RadiiPolynomial.toCoeff_neg` | R-ELAB | DELETE | — |
| `RadiiPolynomial.toCoeff_sub` | R-ELAB | DELETE | — |
| `RadiiPolynomial.uIntegrate_CLM_apply` | R-ELAB | DELETE | — |
| `_aux_RadiiPolynomial_Tactic_AutoPolyFDeriv___macroRules_tacticAuto_hasFDerivAt_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `_aux_RadiiPolynomial_Tactic_AutoPolyFDeriv___macroRules_tacticAuto_poly_fderiv_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `_private.RadiiPolynomial.Algebra.Polynomial.CompPoly.Chebyshev.Bounds.0.MvPolyBridge.CompPoly.Chebyshev.symmetrize_pi_sub` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Algebra.Polynomial.CompPoly.Laurent.0.MvPolyBridge.CompPoly.sum_laurentModes_eq_of_support` | NON-FACE | STAGE | [staged/B5RecordLaurentInterpreter.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordLaurentInterpreter.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.eight_terms_le` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.norm_cosMul_e1_e1` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.norm_cosMul₃_e1_e1_e1` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.norm_cosMul₃_e1_e1_e2` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.norm_eq_sum_of_support` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.norm_lpSingle` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.norm_restr_add_le_of` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.norm_restr_single_eq_posPow` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.posPow` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.posPow_le` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.posPow_le_t` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.posPow_le_t_sq` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.posPow_of_neg` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.pow_le_t_mul` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.pow_le_t_sq_mul` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.OneSided.0.RadiiPolynomial.l1Chebyshev.OneSided.toSeq_lpSingle` | NON-FACE | STAGE | [staged/B5RecordOneSidedCosine.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordOneSidedCosine.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.SymmetricSubalgebra.0.RadiiPolynomial.l1Chebyshev.borderedEmbed` | NON-FACE | STAGE | [staged/B5RecordSymmetricStorageBordered.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordSymmetricStorageBordered.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.SymmetricSubalgebra.0.RadiiPolynomial.l1Chebyshev.borderedEmbed_memℓp` | NON-FACE | STAGE | [staged/B5RecordSymmetricStorageBordered.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordSymmetricStorageBordered.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.SymmetricSubalgebra.0.RadiiPolynomial.l1Chebyshev.borderedEmbed_toSeq` | NON-FACE | STAGE | [staged/B5RecordSymmetricStorageBordered.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordSymmetricStorageBordered.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Chebyshev.SymmetricSubalgebra.0.RadiiPolynomial.l1Chebyshev.nonnegRestrict_borderedEmbed` | NON-FACE | STAGE | [staged/B5RecordSymmetricStorageBordered.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordSymmetricStorageBordered.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.T_cast_add_two` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.borderedEvalCLM` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.borderedEvalCLM._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.borderedEvalCLM.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.borderedEvalCLM_nonnegRestrict` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.borderedEvalCLM_nonnegRestrict._simp_1_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.borderedEvalColumn_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.chebColumn_le_borderedWeight` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.chebPolyTaylor_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.chebyshevToTaylorAlgHom` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.chebyshevToTaylorAlgHom._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.chebyshevToTaylorAlgHom._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.chebyshevToTaylorAlgHom._proof_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.chebyshevToTaylorCLM_map_mul` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.chebyshevToTaylorCLM_map_one` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.evalCLM_comp_chebyshevToTaylorBorderedCLM` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.eval_chebPolyTaylor` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.eventually_abs_le_one_and_sigma` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.ChebyshevTaylor.0.RadiiPolynomial.CrossGeometry.toSeq_aeval_generator` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/ChebyshevTaylor.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.chebyshevDerivativeToTaylorBorderedCLM` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.chebyshevDerivativeToTaylorColumn` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.chebyshevDerivativeToTaylorColumn_le` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.chebyshevDerivativeToUBorderedCLM` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.chebyshevDerivativeToUBorderedCLM_toSeq` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.chebyshevDerivativeToUColumn` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.chebyshevDerivativeToUColumn_le` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.coeff_derivative_T` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.derivShift_comp_chebyshevToTaylorBorderedCLM` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.l1OmegaWrapped` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.norm_omegaSingle` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.norm_uPolyOmega_natCast_le` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.omegaSingle` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.omegaSingle_toSeq` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.omegaToSeqCLM` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.omegaToSeqCLM_apply` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.omegaWrapCLM` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.omegaWrapCLM_omegaSingle` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.uPolyOmegaSynthesisCLM_omegaSingle` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.uPolyOmegaSynthesisColumn_le` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.uPolyOmegaSynthesisWrappedCLM` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Derivative.0.RadiiPolynomial.CrossGeometry.uPolyOmegaSynthesis_comp_chebyshevDerivativeToUBorderedCLM` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Derivative.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Derivative.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Joukowski.0.RadiiPolynomial.CrossGeometry.abs_neg_one_le_one` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Joukowski.0.RadiiPolynomial.CrossGeometry.abs_one_add_le_two` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Joukowski.0.RadiiPolynomial.CrossGeometry.joukowskiGen_binomial_term` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.CrossGeometry.Joukowski.0.RadiiPolynomial.CrossGeometry.pow_natAbs_diff_le` | NON-FACE | STAGE | [staged/B5Records/Spectra/CrossGeometry/Joukowski.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/CrossGeometry/Joukowski.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic.0.RadiiPolynomial.l1Weighted.trunc_add` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic.0.RadiiPolynomial.l1Weighted.trunc_norm_le` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Basic.0.RadiiPolynomial.l1Weighted.trunc_smul` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega.0.RadiiPolynomial.lambdaN_mem` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega.0.RadiiPolynomial.lambdaN_seq` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega.0.RadiiPolynomial.lambdaN_toSeq` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega.0.RadiiPolynomial.shift_mem` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega.0.RadiiPolynomial.shift_seq` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.Omega.0.RadiiPolynomial.shift_toSeq` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.Geometric.RadiusRestriction.0.RadiiPolynomial.l1Weighted.radiusRestrict_power_bound` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5Records/Spectra/Geometric/RadiusRestriction.lean](../probes/records/B5_universal_api_retirement/staged/B5Records/Spectra/Geometric/RadiusRestriction.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Diagonal.0.RadiiPolynomial.lpOneAlg.apply_single_eq_zero_of_colRatio_eq_zero` | NON-FACE | STAGE | [staged/B5RecordL1HeadTail.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1HeadTail.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Multilinear.0.RadiiPolynomial.lpOneAlg.applyRight` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Multilinear.0.RadiiPolynomial.lpOneAlg.applyRight._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Multilinear.0.RadiiPolynomial.lpOneAlg.applyRight._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Multilinear.0.RadiiPolynomial.lpOneAlg.applyRight._proof_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Multilinear.0.RadiiPolynomial.lpOneAlg.applyRight._proof_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Multilinear.0.RadiiPolynomial.lpOneAlg.applyRight._proof_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Multilinear.0.RadiiPolynomial.lpOneAlg.applyRight_apply` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedL1.Multilinear.0.RadiiPolynomial.lpOneAlg.ringHomIsometric_id'` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordL1ColumnPrinciple.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordL1ColumnPrinciple.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Compatibility.EmbedL1.0.RadiiPolynomial.WeightedLp.sum_sq_norm_apply_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Compatibility.EmbedL1.0.RadiiPolynomial.WeightedLp.sum_sq_ratio_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Compatibility/EmbedL1.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.WithHead.0.RadiiPolynomial.WeightedLp.WithHead.coeff_sum` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.WithHead.0.RadiiPolynomial.WeightedLp.WithHead.ext_head_tail` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.WithHead.0.RadiiPolynomial.WeightedLp.WithHead.ext_head_tail._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Operators.WithHead.0.RadiiPolynomial.WeightedLp.WithHead.ext_head_tail._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Operators/WithHead.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.atom_sum` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.atom_sum._proof_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.atom_sum._proof_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.coeff_product` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.norm_coord` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.norm_sq_tsum` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.product` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.product.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.productLM` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.productLM._proof_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.productLM._proof_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.product_add_left` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.product_add_right` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.product_bound` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.product_smul_left` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.product_smul_left._simp_1_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.product_smul_right` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.product_smul_right._simp_1_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.raw` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.raw.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.raw.eq_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.raw.match_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.raw.match_1.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.raw.match_1.eq_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.raw.match_1.splitter` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.rawFiber` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.rawFiber.eq_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.rawFiber_norm_succ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.rawFiber_sq` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.raw_bound` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.raw_bound._simp_1_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.raw_bound._simp_1_6` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.raw_mem` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Analysis.SequenceSpace.WeightedLp.Taylor.Smoothing.0.RadiiPolynomial.WeightedLp.Taylor.summable_sq` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Analysis/SequenceSpace/WeightedLp/Taylor/Smoothing.lean) |
| `_private.RadiiPolynomial.Certification.LeanCertAdapter.0.RadiiPolynomial.mem_foldl_colNorm` | NON-FACE | STAGE | [staged/B5RecordDyadicP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordDyadicP1.lean) |
| `_private.RadiiPolynomial.Certification.LeanCertAdapter.0.RadiiPolynomial.mem_zeroDyadic` | NON-FACE | STAGE | [staged/B5RecordDyadicP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordDyadicP1.lean) |
| `_private.RadiiPolynomial.Certification.LeanCertAdapter.0.RadiiPolynomial.zeroDyadic` | NON-FACE | STAGE | [staged/B5RecordDyadicP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordDyadicP1.lean) |
| `_private.RadiiPolynomial.Certification.Residual.0.RadiiPolynomial.Residual.hasSummableGeomSeries_opposite` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `_private.RadiiPolynomial.Certification.Residual.0.RadiiPolynomial.Residual.norm_mul_pow_le` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `_private.RadiiPolynomial.Certification.Residual.0.RadiiPolynomial.Residual.op_leftInverseCorrection` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL/STAGE | [staged/B5RecordResidualP1.lean](../probes/records/B5_universal_api_retirement/staged/B5RecordResidualP1.lean) |
| `_private.RadiiPolynomial.Certification.Residual.0.RadiiPolynomial.Residual.op_leftInverseCorrection._simp_1_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `_private.RadiiPolynomial.Examples.IVP.Chebyshev.Example1421.Certificate.0.Example1421.Cert.computed_phi_eq` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.IVP.Taylor.Example81.Algebra.0.Example81.abar_toSeq_zero` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.IVP.Taylor.Example81.Algebra.0.Example81.hDF_nat` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.IVP.Taylor.Example81.Algebra.0.Example81.proj_L` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.IVP.Taylor.Example81.Certificate.0.Example81.Cert.Df_norm_le` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.IVP.Taylor.Example81.Certificate.0.Example81.Cert.radii_neg_icc` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.AF_ā_support` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.A_colR` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.A_colR_eq` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.A_col_bridge` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.A_col_bridge_q` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.A_inv_tailBound_eq` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.A_tailDiag_eq` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.A_tail_R` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.A_tail_coeff` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.DF_colOf` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.DF_col_bridge` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.F_ā_R` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.F_ā_support` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.F_ā_toSeq_eq` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.F_ā_vec` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.Y₀_eval` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.defect_cols` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.defect_cols_bridge` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.defect_matrixNorm_le` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.radii_neg_icc` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.sol_toSeq_eq` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.PowerSeries.Example77.Certificate.0.Example77.Cert.ν_val_eq_q` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.A_col_0` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.A_col_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.A_col_10` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.A_col_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.A_col_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.A_col_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.A_col_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.A_col_6` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.A_col_7` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.A_col_8` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.A_col_9` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.DF_col_0` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.DF_col_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.DF_col_10` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.DF_col_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.DF_col_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.DF_col_4` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.DF_col_5` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.DF_col_6` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.DF_col_7` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.DF_col_8` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Data.0.Example81.L2.Data.DF_col_9` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Data.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Maps.0.Example81.L2.coeff_S_Q_fin` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Maps.0.Example81.L2.coeff_sum` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Maps.0.Example81.L2.sum_fin_restrict` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Maps.0.Example81.L2.sum_fin_restrict._proof_1_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Maps.0.Example81.L2.sum_fin_restrict._simp_1_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.Maps.0.Example81.L2.sum_fin_restrict._simp_1_2` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/Maps.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.ResidualBounds.0.Example81.L2.coeff_H_succ` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `_private.RadiiPolynomial.Examples.tests.WL.Example81L2.ResidualBounds.0.Example81.L2.coeff_H_zero` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | [staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean](../probes/records/B5_universal_api_retirement/staged/RadiiPolynomial/Examples/tests/WL/Example81L2/ResidualBounds.lean) |
| `_private.RadiiPolynomial.Operators.BlockDiagonal.WeightedL1.0.RadiiPolynomial.defectOfBlockDiagOp_coeff_finite` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Operators.BlockDiagonal.WeightedL1.0.RadiiPolynomial.defectOfBlockDiagOp_coeff_tail` | NON-FACE | DELETE | — |
| `_private.RadiiPolynomial.Tactic.AutoPolyFDeriv.0.proj₃` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `_private.RadiiPolynomial.Tactic.MakeCompPoly.0.RadiiPolynomial.MakeCompPoly.mkRatNatLit` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `fderiv_pi_apply` | R-ELAB | APPLIED_SOURCE_MODULE_REMOVAL/DELETE | — |
| `tacticAuto_hasFDerivAt` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `tacticAuto_poly_fderiv` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `«_aux_RadiiPolynomial_Tactic_AutoPolyFDeriv___macroRules_tacticAuto_hasFDerivAt[_,,]_1»` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `«_aux_RadiiPolynomial_Tactic_AutoPolyFDeriv___macroRules_tacticAuto_poly_fderiv[_,,]_1»` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `«_aux_RadiiPolynomial_Tactic_MakeCompPoly___elabRules_termCompPolyOf%__1»` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `«_aux_RadiiPolynomial_Tactic_MakeCompPoly___elabRules_termCompPolyOf%__1»._sparseCasesOn_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `«_aux_RadiiPolynomial_Tactic_MakeCompPoly___elabRules_termCompPolyOf%__1».match_1` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `«_aux_RadiiPolynomial_Tactic_MakeCompPoly___elabRules_termCompPolyOf%__1».match_3` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `«tacticAuto_hasFDerivAt[_,,]»` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `«tacticAuto_poly_fderiv[_,,]»` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |
| `«termCompPolyOf%_»` | NON-FACE | APPLIED_SOURCE_MODULE_REMOVAL | — |

## Chebyshev certification split (2026-10-22)

`Certification/IVP/Chebyshev.lean` becomes a facade over eight modules in `Certification/IVP/Chebyshev/`
(`QLayer`, `Common`, `Y0Z0`, `TC`, `Z1`, `Face`, `Kernel/QLayer`, `Kernel/Face`). Every declaration
keeps its FQN, type, binder order and proof; two change section: `FCe` (used by
`FCseq_single_nat`) to `Common`, and `StdChebIVPData.norm_symmetrize_abar_eq` (used by `Z₂_le_of_Q`
and `Z₁_hDφ`) to `Y0Z0`.

| old FQN | new FQN or replacement | kind | evidence |
|---|---|---|---|
| `ChebyshevIVP.radiusF`, `ChebyshevIVP.MY`, `ChebyshevIVP.Y₀Q`, `ChebyshevIVP.SnormQ` | unchanged FQNs, types and binder order; `Certification/IVP/Chebyshev.lean` → `Certification/IVP/Chebyshev/QLayer.lean` | moved | `exterior/tmp/lp_api_campaign_20261017/POST_MERGE/chebyshev_split/REPORT.md` |
| `ChebyshevIVP.FCseq_eq_zero_of_nat`, `ChebyshevIVP.FAseq_eq_zero_of_nat`, `ChebyshevIVP.toSeq_pi_single_nat`, `ChebyshevIVP.toSeq_pi_single_negSucc_nat`, `ChebyshevIVP.FCseq_single_nat` | unchanged FQNs, types and binder order; `Certification/IVP/Chebyshev.lean` → `Certification/IVP/Chebyshev/Common.lean` | moved | `exterior/tmp/lp_api_campaign_20261017/POST_MERGE/chebyshev_split/REPORT.md` |
| `ChebyshevIVP.StdChebIVPData.ν_q_pos`, `ChebyshevIVP.StdChebIVPData.one_le_ν_q`, `ChebyshevIVP.StdChebIVPData.abar_Q_getD_eq_zero`, `ChebyshevIVP.StdChebIVPData.defect_finBlockNorm_le_of_Q`, `ChebyshevIVP.StdChebIVPData.Z₀_sound`, `ChebyshevIVP.StdChebIVPData.ivpCoeffsQ_support`, `ChebyshevIVP.StdChebIVPData.Y₀_le_of_Q` | unchanged FQNs, types and binder order; `Certification/IVP/Chebyshev.lean` → `Certification/IVP/Chebyshev/Y0Z0.lean` | moved | `exterior/tmp/lp_api_campaign_20261017/POST_MERGE/chebyshev_split/REPORT.md` |
| `ChebyshevIVP.TCcolQ`, `ChebyshevIVP.TCcolNormQ`, `ChebyshevIVP.TCblockGen`, `ChebyshevIVP.TCnormGen`, `ChebyshevIVP.TCcolQ_eq_zero_of_ge`, `ChebyshevIVP.TCblockGen_nonneg`, `ChebyshevIVP.TCcolNormQ_le`, `ChebyshevIVP.TCnormGen_nonneg`, `ChebyshevIVP.StdChebIVPData.TClj`, `ChebyshevIVP.StdChebIVPData.TClj_apply`, `ChebyshevIVP.StdChebIVPData.TCblock_single_toSeq`, `ChebyshevIVP.StdChebIVPData.TCblock_single_negSucc_toSeq`, `ChebyshevIVP.StdChebIVPData.TCblock_single_norm_le`, `ChebyshevIVP.StdChebIVPData.TClj_col_le`, `ChebyshevIVP.StdChebIVPData.TC_norm_le_gen`, `ChebyshevIVP.StdChebIVPData.Z₂_le_of_Q` | unchanged FQNs, types and binder order; `Certification/IVP/Chebyshev.lean` → `Certification/IVP/Chebyshev/TC.lean` | moved | `exterior/tmp/lp_api_campaign_20261017/POST_MERGE/chebyshev_split/REPORT.md` |
| `ChebyshevIVP.jacColQ`, `ChebyshevIVP.DcolAux`, `ChebyshevIVP.colNormAux`, `ChebyshevIVP.chebColNormQ`, `ChebyshevIVP.Mfar`, `ChebyshevIVP.rowA0Q`, `ChebyshevIVP.epsBlockGen`, `ChebyshevIVP.epsGen`, `ChebyshevIVP.DcolAux_jac`, `ChebyshevIVP.compPolyDFQ_far`, `ChebyshevIVP.chebColNormQ_far`, `ChebyshevIVP.epsBlockGen_nonneg`, `ChebyshevIVP.chebColNormQ_le_eps`, `ChebyshevIVP.StdChebIVPData.composed_toSeq_nat`, `ChebyshevIVP.StdChebIVPData.composed_toSeq_neg`, `ChebyshevIVP.StdChebIVPData.fderiv_toSeq`, `ChebyshevIVP.StdChebIVPData.Z₁_hneg`, `ChebyshevIVP.StdChebIVPData.Z₁_htail`, `ChebyshevIVP.StdChebIVPData.Z₁_hDφ`, `ChebyshevIVP.StdChebIVPData.Tlj`, `ChebyshevIVP.StdChebIVPData.defect_actionFinite_single`, `ChebyshevIVP.StdChebIVPData.Tlj_single_toSeq`, `ChebyshevIVP.StdChebIVPData.Tlj_single_negSucc_toSeq`, `ChebyshevIVP.StdChebIVPData.Tlj_col_le`, `ChebyshevIVP.StdChebIVPData.Z₁_hfin`, `ChebyshevIVP.StdChebIVPData.Z₁_le_of_Q` | unchanged FQNs, types and binder order; `Certification/IVP/Chebyshev.lean` → `Certification/IVP/Chebyshev/Z1.lean` | moved | `exterior/tmp/lp_api_campaign_20261017/POST_MERGE/chebyshev_split/REPORT.md` |
| `ChebyshevIVP.ChebCertQ`, `ChebyshevIVP.ChebCertQ.Checks`, `ChebyshevIVP.StdChebIVPData.certified_of_Y₀Z₀`, `ChebyshevIVP.StdChebIVPData.certified_of_checks` | unchanged FQNs, types and binder order; `Certification/IVP/Chebyshev.lean` → `Certification/IVP/Chebyshev/Face.lean` | moved | `exterior/tmp/lp_api_campaign_20261017/POST_MERGE/chebyshev_split/REPORT.md` |
| `ChebyshevIVP.list_range_map_sum`, `ChebyshevIVP.evalFast`, `ChebyshevIVP.evalFast_eq`, `ChebyshevIVP.evalChebFast`, `ChebyshevIVP.evalChebFast_eq`, `ChebyshevIVP.dphiFast`, `ChebyshevIVP.dfFast`, `ChebyshevIVP.dfFast_eq`, `ChebyshevIVP.wQ`, `ChebyshevIVP.wSupp`, `ChebyshevIVP.DcolS`, `ChebyshevIVP.colNormS`, `ChebyshevIVP.DcolS_eq`, `ChebyshevIVP.colNormS_eq`, `ChebyshevIVP.epsGen_le_of_cols`, `ChebyshevIVP.TCcolF`, `ChebyshevIVP.TCcolQ_eq_F`, `ChebyshevIVP.TCcolNormF`, `ChebyshevIVP.TCblockF`, `ChebyshevIVP.TCnormF`, `ChebyshevIVP.TCnormF_eq` | unchanged FQNs, types and binder order; `Certification/IVP/Chebyshev.lean` → `Certification/IVP/Chebyshev/Kernel/QLayer.lean` | moved | `exterior/tmp/lp_api_campaign_20261017/POST_MERGE/chebyshev_split/REPORT.md` |
| private `ChebyshevIVP.zmax`, `ChebyshevIVP.zmin`, `ChebyshevIVP.zsum`, `ChebyshevIVP.zsum_eq` | unchanged declarations; `Certification/IVP/Chebyshev.lean` → `Certification/IVP/Chebyshev/Kernel/QLayer.lean`; the module-mangled private names change with the file | moved (private) | `exterior/tmp/lp_api_campaign_20261017/POST_MERGE/chebyshev_split/REPORT.md` |
| `ChebyshevIVP.ChebCertQ.ChecksK`, `ChebyshevIVP.checks_of_checksK`, `ChebyshevIVP.StdChebIVPData.Z₁_le_of_checksK`, `ChebyshevIVP.StdChebIVPData.certified_of_checksK` | unchanged FQNs, types and binder order; `Certification/IVP/Chebyshev.lean` → `Certification/IVP/Chebyshev/Kernel/Face.lean` | moved | `exterior/tmp/lp_api_campaign_20261017/POST_MERGE/chebyshev_split/REPORT.md` |
| `ChebyshevIVP.FCe` | unchanged FQN, type and binder order; `Certification/IVP/Chebyshev.lean` (section `QLayerTC`) → `Certification/IVP/Chebyshev/Common.lean` | moved | `exterior/tmp/lp_api_campaign_20261017/POST_MERGE/chebyshev_split/REPORT.md` |
| `ChebyshevIVP.StdChebIVPData.norm_symmetrize_abar_eq` | unchanged FQN, type and binder order; `Certification/IVP/Chebyshev.lean` (section `BridgesTC`) → `Certification/IVP/Chebyshev/Y0Z0.lean` | moved | `exterior/tmp/lp_api_campaign_20261017/POST_MERGE/chebyshev_split/REPORT.md` |
| `Certification/IVP/Chebyshev.lean` | facade: its four imports (`Applications.IVP.Chebyshev.Polynomial`, `Certification.Rational.Matrix`, `Certification.Rational.Grid`, `Certification.RadiiPolynomialQ`) replaced by the imports of the eight modules; the importers `RadiiPolynomial.lean`, `Example1421/Certificate.lean` and `tests/CH/L2.lean` keep their import line | import change | `exterior/tmp/lp_api_campaign_20261017/POST_MERGE/chebyshev_split/REPORT.md` |
