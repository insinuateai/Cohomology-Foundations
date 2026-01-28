// Lean compiler output
// Module: Perspective.FairnessAlignmentTradeoff
// Imports: public import Init public import Perspective.Proportionality
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
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_allocationTradeoff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_allocationTradeoff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Rat_instDecidableLe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_compromiseScore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__6;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_alignmentScore___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_CohomologyFoundations_Proportionality_totalShortfall___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfFairness___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfFairness(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_alignmentScore___closed__0;
lean_object* lp_CohomologyFoundations_Finset_sum___at___00Foundations_coboundary_spec__0___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(lean_object*);
uint8_t l_Rat_blt(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* lp_mathlib_abs___at___00Rat_nnabs_spec__0(lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__4;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_compromiseScore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfAlignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__1;
lean_object* l_Rat_add(lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__2;
static lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__0;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore___redArg___closed__0;
lean_object* l_Rat_div(lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfFairness___closed__0;
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfAlignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_alignmentScore(lean_object*, lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__3;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__5;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_alignmentScore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_3);
x_6 = l_Rat_sub(x_4, x_5);
x_7 = lp_mathlib_abs___at___00Rat_nnabs_spec__0(x_6);
return x_7;
}
}
static lean_object* _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_alignmentScore___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_alignmentScore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_alloc_closure((void*)(lp_CohomologyFoundations_FairnessAlignmentTradeoff_alignmentScore___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_alignmentScore___closed__0;
lean_inc(x_1);
x_6 = l_List_finRange(x_1);
x_7 = lp_CohomologyFoundations_Finset_sum___at___00Foundations_coboundary_spec__0___redArg(x_6, x_4);
x_8 = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
x_9 = l_Rat_div(x_7, x_8);
lean_dec_ref(x_7);
x_10 = l_Rat_sub(x_5, x_9);
return x_10;
}
}
static lean_object* _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Rat_instNatCast___lam__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore___redArg___closed__0;
lean_inc_ref(x_3);
x_5 = lp_CohomologyFoundations_Proportionality_totalShortfall___redArg(x_1, x_2, x_3);
x_6 = l_Rat_div(x_5, x_3);
lean_dec_ref(x_5);
x_7 = l_Rat_sub(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_allocationTradeoff___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc_ref(x_2);
lean_inc(x_1);
x_5 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_alignmentScore(x_1, x_2, x_3);
x_6 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore___redArg(x_1, x_2, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_allocationTradeoff(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_allocationTradeoff___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfFairness___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Rat_instNatCast___lam__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfFairness(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfFairness___closed__0;
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfFairness___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfFairness(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfAlignment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore___redArg___closed__0;
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfAlignment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfAlignment(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_compromiseScore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore___redArg___closed__0;
lean_inc_ref(x_5);
x_7 = l_Rat_sub(x_6, x_5);
lean_inc_ref(x_2);
lean_inc(x_1);
x_8 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_alignmentScore(x_1, x_2, x_3);
x_9 = l_Rat_mul(x_7, x_8);
lean_dec_ref(x_7);
x_10 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore___redArg(x_1, x_2, x_4);
x_11 = l_Rat_mul(x_5, x_10);
lean_dec_ref(x_5);
x_12 = l_Rat_add(x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_compromiseScore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_compromiseScore___redArg(x_1, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Allocation balances fairness and alignment. On the tradeoff frontier.", 69, 69);
return x_1;
}
}
static lean_object* _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Allocation prioritizes fairness over alignment. Consider rebalancing.", 69, 69);
return x_1;
}
}
static lean_object* _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Allocation prioritizes alignment over fairness. Consider rebalancing.", 69, 69);
return x_1;
}
}
static lean_object* _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Fairness and alignment are compatible. Current allocation is near-optimal.", 74, 74);
return x_1;
}
}
static lean_object* _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = l_Rat_instNatCast___lam__0(x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = l_Rat_instNatCast___lam__0(x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__5;
x_2 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__4;
x_3 = l_Rat_div(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_21; uint8_t x_22; 
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_5 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_alignmentScore(x_1, x_2, x_3);
lean_inc_ref(x_4);
lean_inc(x_1);
x_6 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore___redArg(x_1, x_2, x_4);
x_7 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfFairness(x_1, lean_box(0), lean_box(0), x_3, x_4);
x_8 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfAlignment(x_1, lean_box(0), lean_box(0), x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_21 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__6;
lean_inc_ref(x_5);
x_22 = l_Rat_instDecidableLe(x_21, x_5);
if (x_22 == 0)
{
x_9 = x_22;
goto block_20;
}
else
{
uint8_t x_23; 
lean_inc_ref(x_6);
x_23 = l_Rat_instDecidableLe(x_21, x_6);
x_9 = x_23;
goto block_20;
}
block_20:
{
if (x_9 == 0)
{
uint8_t x_10; 
lean_inc_ref(x_5);
lean_inc_ref(x_6);
x_10 = l_Rat_blt(x_6, x_5);
if (x_10 == 0)
{
uint8_t x_11; 
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_11 = l_Rat_blt(x_5, x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__0;
x_13 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_6);
lean_ctor_set(x_13, 2, x_7);
lean_ctor_set(x_13, 3, x_8);
lean_ctor_set(x_13, 4, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__1;
x_15 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_7);
lean_ctor_set(x_15, 3, x_8);
lean_ctor_set(x_15, 4, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_9);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__2;
x_17 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_7);
lean_ctor_set(x_17, 3, x_8);
lean_ctor_set(x_17, 4, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_9);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__3;
x_19 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
lean_ctor_set(x_19, 2, x_7);
lean_ctor_set(x_19, 3, x_8);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*5, x_9);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg(x_1, x_3, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_Perspective_Proportionality(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_Perspective_FairnessAlignmentTradeoff(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_Perspective_Proportionality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_CohomologyFoundations_FairnessAlignmentTradeoff_alignmentScore___closed__0 = _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_alignmentScore___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_FairnessAlignmentTradeoff_alignmentScore___closed__0);
lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore___redArg___closed__0 = _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore___redArg___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_FairnessAlignmentTradeoff_fairnessScore___redArg___closed__0);
lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfFairness___closed__0 = _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfFairness___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_FairnessAlignmentTradeoff_priceOfFairness___closed__0);
lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__0 = _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__0);
lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__1 = _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__1();
lean_mark_persistent(lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__1);
lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__2 = _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__2();
lean_mark_persistent(lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__2);
lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__3 = _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__3();
lean_mark_persistent(lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__3);
lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__5 = _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__5();
lean_mark_persistent(lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__5);
lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__4 = _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__4();
lean_mark_persistent(lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__4);
lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__6 = _init_lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__6();
lean_mark_persistent(lp_CohomologyFoundations_FairnessAlignmentTradeoff_generateTradeoffReport___redArg___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
