// Lean compiler output
// Module: RadiiPolynomial.source.lpSpace.CauchyProduct
// Imports: public import Init public import Mathlib.Algebra.BigOperators.NatAntidiagonal public import Mathlib.Algebra.Order.Antidiag.Prod public import Mathlib.RingTheory.PowerSeries.Basic public import Mathlib.Data.Real.Basic public import RadiiPolynomial.source.lpSpace.DiscreteConvolution
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
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct_one___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct_one(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct_one___redArg___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct_one___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct_toPowerSeries___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_List_Nat_antidiagonal(lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct_toPowerSeries(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_PowerSeries_mk___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_apply_1(x_2, x_6);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lp_mathlib_Semiring_toNonAssocSemiring___redArg(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lp_mathlib_List_Nat_antidiagonal(x_4);
x_11 = lean_alloc_closure((void*)(lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct___redArg___lam__0), 4, 3);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_9);
x_12 = lp_mathlib_Finset_sum___redArg(x_7, x_10, x_11);
lean_dec_ref(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct_one___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lp_mathlib_Semiring_toNonAssocSemiring___redArg(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lp_mathlib_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lp_mathlib_Semiring_toNonAssocSemiring___redArg(x_1);
x_10 = lp_mathlib_NonAssocSemiring_toAddCommMonoidWithOne___redArg(x_9);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec_ref(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct_one___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct_one___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct_one(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct_one___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct_one___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct_one(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct_toPowerSeries___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_mathlib_PowerSeries_mk___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_RadiiPolynomial_RadiiPolynomial_CauchyProduct_toPowerSeries(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_mathlib_PowerSeries_mk___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_NatAntidiagonal(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Order_Antidiag_Prod(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_PowerSeries_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Real_Basic(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_DiscreteConvolution(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_CauchyProduct(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_NatAntidiagonal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Order_Antidiag_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_PowerSeries_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Real_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_DiscreteConvolution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
