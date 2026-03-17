// Lean compiler output
// Module: RadiiPolynomial
// Imports: public import Init public import RadiiPolynomial.source.lpSpace.ScaledReal public import RadiiPolynomial.source.lpSpace.NormHelpers public import RadiiPolynomial.source.lpSpace.FiniteWeightedNorm public import RadiiPolynomial.source.lpSpace.DiscreteConvolution public import RadiiPolynomial.source.lpSpace.CauchyProduct public import RadiiPolynomial.source.lpSpace.lpWeighted public import RadiiPolynomial.source.lpSpace.lpWeightedDeriv public import RadiiPolynomial.source.lpSpace.LpOneBanachAlgebra public import RadiiPolynomial.source.lpSpace.MatrixCLM public import RadiiPolynomial.source.lpSpace.OperatorNorm public import RadiiPolynomial.source.lpSpace.OmegaWeighted public import RadiiPolynomial.source.RadiiPolyGeneral public import RadiiPolynomial.source.Core public import RadiiPolynomial.source.BlockDiag.Base public import RadiiPolynomial.source.BlockDiag.Concrete public import RadiiPolynomial.source.BlockDiag.Scalar public import RadiiPolynomial.source.WitnessSpec public import RadiiPolynomial.source.LeanCertEval public import RadiiPolynomial.source.IVP.Setup public import RadiiPolynomial.source.Tactic.AutoPolyFDeriv public import RadiiPolynomial.source.MvPolyBridge.Basic
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
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_ScaledReal(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_NormHelpers(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_FiniteWeightedNorm(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_DiscreteConvolution(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_CauchyProduct(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_lpWeighted(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_lpWeightedDeriv(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_LpOneBanachAlgebra(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_MatrixCLM(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_OperatorNorm(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_OmegaWeighted(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_RadiiPolyGeneral(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_Core(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_BlockDiag_Base(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_BlockDiag_Concrete(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_BlockDiag_Scalar(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_WitnessSpec(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_LeanCertEval(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_IVP_Setup(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_Tactic_AutoPolyFDeriv(uint8_t builtin);
lean_object* initialize_RadiiPolynomial_RadiiPolynomial_source_MvPolyBridge_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RadiiPolynomial_RadiiPolynomial(uint8_t builtin) {
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
res = initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_FiniteWeightedNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_DiscreteConvolution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_CauchyProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_lpWeighted(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_lpWeightedDeriv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_LpOneBanachAlgebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_MatrixCLM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_OperatorNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_lpSpace_OmegaWeighted(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_RadiiPolyGeneral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_BlockDiag_Base(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_BlockDiag_Concrete(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_BlockDiag_Scalar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_WitnessSpec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_LeanCertEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_IVP_Setup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_Tactic_AutoPolyFDeriv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_RadiiPolynomial_RadiiPolynomial_source_MvPolyBridge_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
