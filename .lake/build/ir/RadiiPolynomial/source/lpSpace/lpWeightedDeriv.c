// Lean compiler output
// Module: RadiiPolynomial.source.lpSpace.lpWeightedDeriv
// Imports: public import Init public import Mathlib.Analysis.Calculus.FDeriv.Linear public import Mathlib.Analysis.Calculus.FDeriv.Add public import RadiiPolynomial.source.lpSpace.lpWeighted
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_FDeriv_Linear(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_FDeriv_Add(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_lpWeighted(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_lpWeightedDeriv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_FDeriv_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_FDeriv_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_lpWeighted(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
