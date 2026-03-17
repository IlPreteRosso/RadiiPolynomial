// Lean compiler output
// Module: RadiiPolynomial.source.lpSpace.FiniteWeightedNorm
// Imports: public import Init public import RadiiPolynomial.source.lpSpace.ScaledReal public import RadiiPolynomial.source.lpSpace.NormHelpers
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
lean_object* lp_mathlib_abs___at___00EReal_abs_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_Multiset_sum___at___00Finset_sum___at___00RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_Finset_sum___at___00RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* lp_RadiiPolynomial_Multiset_sum___at___00Finset_sum___at___00RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm_spec__0_spec__0___closed__0;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_Finset_sum___at___00RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_RadiiPolynomial_npowRec___at___00RadiiPolynomial_ScaledReal_toNNReal_spec__0(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lp_mathlib_abs___at___00EReal_abs_spec__0(x_4);
x_6 = lp_RadiiPolynomial_npowRec___at___00RadiiPolynomial_ScaledReal_toNNReal_spec__0(x_3, x_2);
lean_dec(x_3);
x_7 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
return x_7;
}
}
static lean_object* _init_lp_RadiiPolynomial_Multiset_sum___at___00Finset_sum___at___00RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_Multiset_sum___at___00Finset_sum___at___00RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lp_RadiiPolynomial_Multiset_sum___at___00Finset_sum___at___00RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm_spec__0_spec__0___closed__0;
x_3 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_4 = l_List_foldrTR___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_Finset_sum___at___00RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_mathlib_Multiset_map___redArg(x_2, x_1);
x_4 = lp_RadiiPolynomial_Multiset_sum___at___00Finset_sum___at___00RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_closure((void*)(lp_RadiiPolynomial_RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_1, x_5);
x_7 = l_List_finRange(x_6);
x_8 = lp_RadiiPolynomial_Finset_sum___at___00RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm_spec__0___redArg(x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RadiiPolynomial_RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_Finset_sum___at___00RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RadiiPolynomial_Finset_sum___at___00RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm_spec__0___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_ScaledReal(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_NormHelpers(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_FiniteWeightedNorm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_ScaledReal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_NormHelpers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_RadiiPolynomial_Multiset_sum___at___00Finset_sum___at___00RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm_spec__0_spec__0___closed__0 = _init_lp_RadiiPolynomial_Multiset_sum___at___00Finset_sum___at___00RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm_spec__0_spec__0___closed__0();
lean_mark_persistent(lp_RadiiPolynomial_Multiset_sum___at___00Finset_sum___at___00RadiiPolynomial_FiniteWeightedNorm_finl1WeightedNorm_spec__0_spec__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
