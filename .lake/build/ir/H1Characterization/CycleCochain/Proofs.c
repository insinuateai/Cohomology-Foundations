// Lean compiler output
// Module: H1Characterization.CycleCochain.Proofs
// Imports: public import Init public import H1Characterization.CycleCochain.Definitions public import H1Characterization.ForestCoboundary
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
LEAN_EXPORT lean_object* lp_CohomologyFoundations_H1Characterization_OrientedEdge_toSym2___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_H1Characterization_OrientedEdge_toSym2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_H1Characterization_OrientedEdge_toSym2___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_H1Characterization_OrientedEdge_toSym2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_H1Characterization_OrientedEdge_toSym2___redArg(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_H1Characterization_CycleCochain_Definitions(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_H1Characterization_ForestCoboundary(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_H1Characterization_CycleCochain_Proofs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_H1Characterization_CycleCochain_Definitions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_H1Characterization_ForestCoboundary(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
