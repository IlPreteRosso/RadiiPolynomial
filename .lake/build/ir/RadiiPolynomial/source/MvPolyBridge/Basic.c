// Lean compiler output
// Module: RadiiPolynomial.source.MvPolyBridge.Basic
// Imports: public import Init public import Mathlib.Algebra.MvPolynomial.Basic public import Mathlib.Algebra.MvPolynomial.Eval public import Mathlib.Algebra.MvPolynomial.PDeriv public import Mathlib.RingTheory.PowerSeries.Basic public import RadiiPolynomial.source.lpSpace.CauchyProduct public import RadiiPolynomial.source.lpSpace.LpOneBanachAlgebra
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_MvPolyBridge_arrayToPowerSeries___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalNNRealRPow_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_MvPolyBridge_arrayToPowerSeries___lam__0___boxed(lean_object*, lean_object*);
static lean_object* lp_RadiiPolynomial_MvPolyBridge_arrayToPowerSeries___lam__0___closed__0;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_MvPolyBridge_arrayToPowerSeries(lean_object*, lean_object*);
lean_object* lp_mathlib_PowerSeries_mk___redArg(lean_object*, lean_object*);
static lean_object* _init_lp_RadiiPolynomial_MvPolyBridge_arrayToPowerSeries___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lp_mathlib_Nat_cast___at___00Mathlib_Meta_NormNum_evalNNRealRPow_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_MvPolyBridge_arrayToPowerSeries___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lp_RadiiPolynomial_MvPolyBridge_arrayToPowerSeries___lam__0___closed__0;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
lean_inc(x_6);
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_MvPolyBridge_arrayToPowerSeries___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RadiiPolynomial_MvPolyBridge_arrayToPowerSeries___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_MvPolyBridge_arrayToPowerSeries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(lp_RadiiPolynomial_MvPolyBridge_arrayToPowerSeries___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lp_mathlib_PowerSeries_mk___redArg(x_3, x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_MvPolynomial_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_MvPolynomial_Eval(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_MvPolynomial_PDeriv(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_PowerSeries_Basic(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_CauchyProduct(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_LpOneBanachAlgebra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_MvPolyBridge_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_MvPolynomial_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_MvPolynomial_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_MvPolynomial_PDeriv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_PowerSeries_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_CauchyProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_LpOneBanachAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RadiiPolynomial_MvPolyBridge_arrayToPowerSeries___lam__0___closed__0 = _init_lp_RadiiPolynomial_MvPolyBridge_arrayToPowerSeries___lam__0___closed__0();
lean_mark_persistent(lp_RadiiPolynomial_MvPolyBridge_arrayToPowerSeries___lam__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
