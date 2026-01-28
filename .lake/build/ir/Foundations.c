// Lean compiler output
// Module: Foundations
// Imports: public import Init public import Foundations.Basic public import Foundations.Simplex public import Foundations.Cochain public import Foundations.Coboundary public import Foundations.Cohomology
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
lean_object* initialize_CohomologyFoundations_Foundations_Basic(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_Foundations_Simplex(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_Foundations_Cochain(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_Foundations_Coboundary(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_Foundations_Cohomology(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_Foundations(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_Foundations_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_Foundations_Simplex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_Foundations_Cochain(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_Foundations_Coboundary(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_Foundations_Cohomology(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
