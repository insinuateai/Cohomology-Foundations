// Lean compiler output
// Module: H1Characterization.OneSkeleton
// Imports: public import Init public import H1Characterization.Basic public import Mathlib.Combinatorics.SimpleGraph.Basic public import Mathlib.Combinatorics.SimpleGraph.Walks.Maps public import Mathlib.Combinatorics.SimpleGraph.Paths
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
LEAN_EXPORT lean_object* lp_CohomologyFoundations_H1Characterization_oneSkeleton(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_H1Characterization_oneSkeleton(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_H1Characterization_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Combinatorics_SimpleGraph_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Combinatorics_SimpleGraph_Walks_Maps(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Combinatorics_SimpleGraph_Paths(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_H1Characterization_OneSkeleton(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_H1Characterization_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Combinatorics_SimpleGraph_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Combinatorics_SimpleGraph_Walks_Maps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Combinatorics_SimpleGraph_Paths(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
