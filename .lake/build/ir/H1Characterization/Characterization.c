// Lean compiler output
// Module: H1Characterization.Characterization
// Imports: public import Init public import H1Characterization.ForestCoboundary public import H1Characterization.CycleCochain.Definitions public import Perspective.AlignmentEquivalence
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
LEAN_EXPORT uint8_t l_H1Characterization_hollowTriangle__not__oneConnected__axiom___nativeDecide__1__3;
LEAN_EXPORT uint8_t l_H1Characterization_hollowTriangle__not__oneConnected__axiom___nativeDecide__1__1;
LEAN_EXPORT uint8_t l_H1Characterization_hollowTriangle__not__oneConnected__axiom___nativeDecide__1__2;
static uint8_t _init_l_H1Characterization_hollowTriangle__not__oneConnected__axiom___nativeDecide__1__1() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_H1Characterization_hollowTriangle__not__oneConnected__axiom___nativeDecide__1__2() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_H1Characterization_hollowTriangle__not__oneConnected__axiom___nativeDecide__1__3() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_H1Characterization_ForestCoboundary(uint8_t builtin);
lean_object* initialize_H1Characterization_CycleCochain_Definitions(uint8_t builtin);
lean_object* initialize_Perspective_AlignmentEquivalence(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_H1Characterization_Characterization(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_H1Characterization_ForestCoboundary(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_H1Characterization_CycleCochain_Definitions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_AlignmentEquivalence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_H1Characterization_hollowTriangle__not__oneConnected__axiom___nativeDecide__1__1 = _init_l_H1Characterization_hollowTriangle__not__oneConnected__axiom___nativeDecide__1__1();
l_H1Characterization_hollowTriangle__not__oneConnected__axiom___nativeDecide__1__2 = _init_l_H1Characterization_hollowTriangle__not__oneConnected__axiom___nativeDecide__1__2();
l_H1Characterization_hollowTriangle__not__oneConnected__axiom___nativeDecide__1__3 = _init_l_H1Characterization_hollowTriangle__not__oneConnected__axiom___nativeDecide__1__3();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
