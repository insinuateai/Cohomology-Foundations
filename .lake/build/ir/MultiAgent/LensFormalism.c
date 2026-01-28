// Lean compiler output
// Module: MultiAgent.LensFormalism
// Imports: public import Init public import Mathlib.Data.Finset.Basic public import Mathlib.Data.Finset.Card public import Mathlib.Logic.Function.Basic public import MultiAgent.AgentNetworks
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
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_id___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_LensPath_length___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_id___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_cycleComposition___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_cycleComposition___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_comp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentLens_reverse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentLens_mk_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_LensPath_length(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_cycleComposition(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_fieldLens___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_cycleComposition___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_fieldLens___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_LensPath_empty___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_numLenses(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentLens_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_id(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_fieldLens___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentLens_mk_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_id___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_LensPath_length___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_id___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_LensPath_length___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_comp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_viewLens___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_fieldLens;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_numLenses___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentLens_reverse___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentLens_mk_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_viewLens(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_LensPath_empty(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_id___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_id___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_id___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_PerspectiveLens_id___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_id___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_PerspectiveLens_id___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_id(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_PerspectiveLens_id___lam__0___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_PerspectiveLens_id___lam__1___boxed), 2, 0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const___redArg___lam__1___boxed), 2, 0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_PerspectiveLens_const___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_comp___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_apply_1(x_5, x_3);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_comp___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
lean_inc(x_3);
x_8 = lean_apply_1(x_5, x_3);
x_9 = lean_apply_2(x_7, x_8, x_4);
x_10 = lean_apply_2(x_6, x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_comp___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_PerspectiveLens_comp___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_PerspectiveLens_comp___redArg___lam__1), 4, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_PerspectiveLens_comp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_MultiAgent_PerspectiveLens_comp___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentLens_mk_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentLens_mk_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentLens_mk_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_CohomologyFoundations_MultiAgent_AgentLens_mk_x27(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentLens_reverse___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentLens_reverse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_AgentLens_reverse___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentLens_reverse___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_AgentLens_reverse(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_numLenses(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_lengthTR___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_numLenses___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_numLenses(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_LensPath_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_LensPath_empty___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_LensPath_empty(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_LensPath_length(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lengthTR___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_LensPath_length___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_lengthTR___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_LensPath_length___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_LensPath_length(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_LensPath_length___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_LensPath_length___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_cycleComposition(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_cycleComposition___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_cycleComposition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_cycleComposition(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_cycleComposition___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_cycleComposition___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_fieldLens___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_fieldLens___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_fieldLens___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_fieldLens___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_fieldLens() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_fieldLens___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_fieldLens___lam__1), 2, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_viewLens(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_viewLens___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Card(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Logic_Function_Basic(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_MultiAgent_AgentNetworks(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_MultiAgent_LensFormalism(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Card(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Logic_Function_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_MultiAgent_AgentNetworks(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_CohomologyFoundations_MultiAgent_fieldLens = _init_lp_CohomologyFoundations_MultiAgent_fieldLens();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_fieldLens);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
