// Lean compiler output
// Module: Perspective.Hysteresis
// Imports: public import Init public import Perspective.Bifurcation
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
static lean_object* l_Hysteresis_generateHysteresisReport___redArg___closed__0;
LEAN_EXPORT lean_object* l_Hysteresis_HysteresisReport_ctorIdx___boxed(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_ParameterPath_finish___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_optimalPath___redArg(lean_object*, lean_object*);
lean_object* l_List_getLast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_HysteresisLoop_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_ParameterPath_start(lean_object*);
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_dynamicUpdate___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Hysteresis_finalState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_stateAlongPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_DynamicState_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_optimalPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_ParameterPath_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_ParameterPath_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_finalState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_ParameterPath_finish(lean_object*);
lean_object* l_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Hysteresis_stateAlongPath___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_systemMemory___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_HysteresisReport_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_stateAlongPath___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Bifurcation_alignmentStatus___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Bifurcation_criticalEpsilon___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_hysteresisLoopArea___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_hysteresisWidth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_ParameterPath_start___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_dynamicUpdate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Hysteresis_hysteresisLoopArea___closed__0;
LEAN_EXPORT lean_object* l_Hysteresis_hysteresisLoopArea(lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_generateHysteresisReport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_generateHysteresisReport___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_finalState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_DynamicState_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_stateAlongPath___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_HysteresisLoop_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_dynamicUpdate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_systemMemory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_hysteresisWidth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_optimalPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Hysteresis_hysteresisWidth___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Hysteresis_finalState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hysteresis_ParameterPath_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_ParameterPath_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Hysteresis_ParameterPath_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_ParameterPath_start(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_ParameterPath_start___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Hysteresis_ParameterPath_start(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_ParameterPath_finish(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_getLast___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_ParameterPath_finish___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Hysteresis_ParameterPath_finish(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Hysteresis_stateAlongPath___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Bifurcation_alignmentStatus___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_stateAlongPath___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Hysteresis_stateAlongPath___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
x_6 = lean_box(0);
x_7 = l_List_mapTR_loop___redArg(x_5, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_stateAlongPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Hysteresis_stateAlongPath___redArg(x_2, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_stateAlongPath___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Hysteresis_stateAlongPath___redArg___lam__0(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Hysteresis_finalState___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_List_getLast___redArg(x_4);
x_6 = l_Bifurcation_alignmentStatus___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Hysteresis_finalState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Hysteresis_finalState___redArg(x_2, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_finalState___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Hysteresis_finalState___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_finalState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Hysteresis_finalState(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
x_9 = lean_box(x_8);
return x_9;
}
}
static lean_object* _init_l_Hysteresis_hysteresisWidth___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Rat_instNatCast___lam__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_hysteresisWidth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Hysteresis_hysteresisWidth___closed__0;
return x_6;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_hysteresisWidth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Hysteresis_hysteresisWidth(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_DynamicState_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_DynamicState_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Hysteresis_DynamicState_ctorIdx(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_dynamicUpdate___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 2, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Hysteresis_dynamicUpdate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Hysteresis_dynamicUpdate___redArg(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_dynamicUpdate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Hysteresis_dynamicUpdate(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_HysteresisLoop_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_HysteresisLoop_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Hysteresis_HysteresisLoop_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Hysteresis_hysteresisLoopArea___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_hysteresisLoopArea(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Hysteresis_hysteresisLoopArea___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_hysteresisLoopArea___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Hysteresis_hysteresisLoopArea(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_optimalPath___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_optimalPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Hysteresis_optimalPath___redArg(x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_optimalPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Hysteresis_optimalPath(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_systemMemory(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Hysteresis_hysteresisWidth___closed__0;
return x_6;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_systemMemory___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Hysteresis_systemMemory(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_HysteresisReport_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_HysteresisReport_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Hysteresis_HysteresisReport_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Hysteresis_generateHysteresisReport___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("System has no hysteresis. All parameter changes are reversible.", 63, 63);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_generateHysteresisReport___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Bifurcation_criticalEpsilon___redArg(x_1, x_2, x_3);
x_5 = 0;
x_6 = l_Hysteresis_hysteresisWidth___closed__0;
x_7 = 1;
x_8 = l_Hysteresis_generateHysteresisReport___redArg___closed__0;
lean_inc_ref(x_4);
x_9 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*5 + 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Hysteresis_generateHysteresisReport(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Hysteresis_generateHysteresisReport___redArg(x_2, x_3, x_6);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Perspective_Bifurcation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Perspective_Hysteresis(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_Bifurcation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Hysteresis_hysteresisWidth___closed__0 = _init_l_Hysteresis_hysteresisWidth___closed__0();
lean_mark_persistent(l_Hysteresis_hysteresisWidth___closed__0);
l_Hysteresis_hysteresisLoopArea___closed__0 = _init_l_Hysteresis_hysteresisLoopArea___closed__0();
lean_mark_persistent(l_Hysteresis_hysteresisLoopArea___closed__0);
l_Hysteresis_generateHysteresisReport___redArg___closed__0 = _init_l_Hysteresis_generateHysteresisReport___redArg___closed__0();
lean_mark_persistent(l_Hysteresis_generateHysteresisReport___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
