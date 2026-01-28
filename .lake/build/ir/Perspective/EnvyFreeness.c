// Lean compiler output
// Module: Perspective.EnvyFreeness
// Imports: public import Init public import Perspective.ParetoTopology
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
uint8_t l_Rat_instDecidableLe(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__2;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_totalEnvy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__1;
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyAmount___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyReductionStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyAmount(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__3;
static lean_object* lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__0;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_EnvyFreeness_envyAmount___redArg___closed__0;
lean_object* lp_CohomologyFoundations_Finset_sum___at___00Foundations_coboundary_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyReductionStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyEdgeCount(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyReductionStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_maxEnvyAmount___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyEdgeCount___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_totalEnvy___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_maxEnvyAmount___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_maxEnvyAmount(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyAmount___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyEdgeCount___redArg(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_totalEnvy___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_CohomologyFoundations_EnvyFreeness_envyAmount___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyAmount___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lp_CohomologyFoundations_EnvyFreeness_envyAmount___redArg___closed__0;
lean_inc_ref(x_1);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_apply_2(x_1, x_3, x_4);
lean_inc_ref(x_2);
x_7 = lean_apply_1(x_2, x_4);
x_8 = l_Rat_mul(x_6, x_7);
lean_dec_ref(x_6);
lean_inc_n(x_3, 2);
x_9 = lean_apply_2(x_1, x_3, x_3);
x_10 = lean_apply_1(x_2, x_3);
x_11 = l_Rat_mul(x_9, x_10);
lean_dec_ref(x_9);
x_12 = l_Rat_sub(x_8, x_11);
lean_inc_ref(x_12);
x_13 = l_Rat_instDecidableLe(x_5, x_12);
if (x_13 == 0)
{
lean_dec_ref(x_12);
return x_5;
}
else
{
return x_12;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyAmount(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_EnvyFreeness_envyAmount___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyAmount___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_EnvyFreeness_envyAmount(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_totalEnvy___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_CohomologyFoundations_EnvyFreeness_envyAmount___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_totalEnvy___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(lp_CohomologyFoundations_EnvyFreeness_totalEnvy___lam__0), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
x_6 = lp_CohomologyFoundations_Finset_sum___at___00Foundations_coboundary_spec__0___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_totalEnvy(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_List_finRange(x_1);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(lp_CohomologyFoundations_EnvyFreeness_totalEnvy___lam__1), 4, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
x_6 = lp_CohomologyFoundations_Finset_sum___at___00Foundations_coboundary_spec__0___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyEdgeCount___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_List_finRange(x_1);
lean_inc(x_3);
x_4 = lp_mathlib_Multiset_product___redArg(x_3, x_3);
x_5 = lp_mathlib_Multiset_filter___redArg(x_2, x_4);
x_6 = l_List_lengthTR___redArg(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyEdgeCount(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_CohomologyFoundations_EnvyFreeness_envyEdgeCount___redArg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyEdgeCount___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_CohomologyFoundations_EnvyFreeness_envyEdgeCount(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyReductionStep___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_5, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = lean_nat_dec_eq(x_5, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_4);
lean_dec(x_3);
x_8 = lean_apply_1(x_1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_apply_1(x_1, x_3);
x_10 = l_Rat_sub(x_9, x_4);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
x_11 = lean_apply_1(x_1, x_2);
x_12 = l_Rat_add(x_11, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyReductionStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_CohomologyFoundations_EnvyFreeness_envyReductionStep___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_envyReductionStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_CohomologyFoundations_EnvyFreeness_envyReductionStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_maxEnvyAmount___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(lp_CohomologyFoundations_EnvyFreeness_totalEnvy___lam__0), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_6);
x_8 = l_List_finRange(x_3);
x_9 = lp_mathlib_Finset_fold___redArg(x_4, x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_maxEnvyAmount___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_3 = l_Rat_instDecidableLe(x_1, x_2);
if (x_3 == 0)
{
lean_dec_ref(x_2);
return x_1;
}
else
{
lean_dec_ref(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_maxEnvyAmount(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_closure((void*)(lp_CohomologyFoundations_EnvyFreeness_maxEnvyAmount___lam__0), 2, 0);
x_5 = lp_CohomologyFoundations_EnvyFreeness_envyAmount___redArg___closed__0;
lean_inc_ref(x_4);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(lp_CohomologyFoundations_EnvyFreeness_maxEnvyAmount___lam__2), 6, 5);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_1);
lean_closure_set(x_6, 3, x_4);
lean_closure_set(x_6, 4, x_5);
x_7 = l_List_finRange(x_1);
x_8 = lp_mathlib_Finset_fold___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Rat_instNatCast___lam__0(x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Significant envy exists. Consider reallocation.", 47, 47);
return x_1;
}
}
static lean_object* _init_lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Allocation is EF1. Envy is bounded by one item's value.", 55, 55);
return x_1;
}
}
static lean_object* _init_lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Allocation is envy-free. No agent envies another.", 49, 49);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_5 = lp_CohomologyFoundations_EnvyFreeness_totalEnvy(x_1, x_2, x_3);
x_6 = lp_CohomologyFoundations_EnvyFreeness_maxEnvyAmount(x_1, x_2, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__0;
x_9 = l_instDecidableEqRat_decEq(x_5, x_8);
lean_inc_ref(x_6);
x_10 = l_Rat_instDecidableLe(x_6, x_4);
if (x_9 == 0)
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__1;
x_12 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*4 + 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__2;
x_14 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_7);
lean_ctor_set(x_14, 2, x_6);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*4, x_9);
lean_ctor_set_uint8(x_14, sizeof(void*)*4 + 1, x_10);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__3;
x_16 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_6);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_9);
lean_ctor_set_uint8(x_16, sizeof(void*)*4 + 1, x_10);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_Perspective_ParetoTopology(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_Perspective_EnvyFreeness(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_Perspective_ParetoTopology(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_CohomologyFoundations_EnvyFreeness_envyAmount___redArg___closed__0 = _init_lp_CohomologyFoundations_EnvyFreeness_envyAmount___redArg___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_EnvyFreeness_envyAmount___redArg___closed__0);
lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__0 = _init_lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__0);
lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__1 = _init_lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__1();
lean_mark_persistent(lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__1);
lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__2 = _init_lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__2();
lean_mark_persistent(lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__2);
lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__3 = _init_lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__3();
lean_mark_persistent(lp_CohomologyFoundations_EnvyFreeness_generateEnvyReport___redArg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
