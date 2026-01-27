// Lean compiler output
// Module: Perspective.Stability
// Imports: public import Init public import Perspective.AgentCoordination public import H1Characterization.Characterization public import H1Characterization.LinearComplexity
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
LEAN_EXPORT lean_object* l_Stability_DriftRate_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Stability_timeToFailure___redArg___closed__0;
LEAN_EXPORT lean_object* l_Stability_computeMonitoringStatus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Finset_inf_x27___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Stability_computeMonitoringStatus___redArg___closed__0;
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
static lean_object* l_Stability_timeToFailure___redArg___closed__1;
LEAN_EXPORT lean_object* l_Stability_stabilityMargin___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Rat_instDistribLattice;
LEAN_EXPORT lean_object* l_Stability_MonitoringStatus_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Stability_computeMonitoringStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Rat_instSemilatticeSup;
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Stability_edgeSlack___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_timeToFailure___redArg(lean_object*, lean_object*);
extern lean_object* l_Rat_instSemilatticeInf;
LEAN_EXPORT lean_object* l_Stability_stabilityMarginSimple___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Stability_timeToFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_valueDistance___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(lean_object*);
uint8_t l_Rat_blt(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_computeMonitoringStatus(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_computeMargin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_stabilityMarginSimple(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_computeMonitoringStatus___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_abs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_stabilityMarginSimple___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_stabilityMargin___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Stability_computeMargin___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_computeMargin___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_valueDistance___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_edgeSlack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_DriftRate_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_valueDistance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Finset_sup_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_timeToFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Stability_edgeSlack___redArg___closed__0;
static lean_object* l_Stability_computeMargin___redArg___closed__0;
lean_object* l_Rat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_stabilityMarginSimple___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Stability_stabilityMargin(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_computeMargin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_stabilityMargin___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Stability_timeToFailure___redArg___boxed(lean_object*, lean_object*);
extern lean_object* l_Rat_addCommGroup;
LEAN_EXPORT lean_object* l_Stability_valueDistance___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Stability_MonitoringStatus_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Stability_valueDistance___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_5);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_apply_1(x_2, x_5);
x_8 = l_Rat_sub(x_6, x_7);
x_9 = l_abs___redArg(x_3, x_4, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Stability_valueDistance___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Rat_instSemilatticeSup;
x_5 = l_Rat_instDistribLattice;
x_6 = l_Rat_addCommGroup;
x_7 = lean_alloc_closure((void*)(l_Stability_valueDistance___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_6);
x_8 = l_Finset_sup_x27___redArg(x_4, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Stability_valueDistance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Stability_valueDistance___redArg(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Stability_valueDistance___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Stability_valueDistance___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_6;
}
}
static lean_object* _init_l_Stability_edgeSlack___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Rat_instNatCast___lam__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Stability_edgeSlack___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Rat_instSemilatticeInf;
x_6 = l_Rat_instDistribLattice;
x_7 = l_Rat_addCommGroup;
x_8 = lean_alloc_closure((void*)(l_Stability_valueDistance___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_6);
lean_closure_set(x_8, 3, x_7);
x_9 = l_Stability_edgeSlack___redArg___closed__0;
x_10 = l_Rat_mul(x_9, x_4);
x_11 = l_Finset_inf_x27___redArg(x_5, x_1, x_8);
x_12 = l_Rat_sub(x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Stability_edgeSlack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Stability_edgeSlack___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Stability_stabilityMargin___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Stability_stabilityMargin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc_ref(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Stability_stabilityMargin___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Stability_stabilityMargin___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Stability_stabilityMargin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Stability_stabilityMargin(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Stability_stabilityMarginSimple___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Stability_stabilityMarginSimple(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc_ref(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Stability_stabilityMarginSimple___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Stability_stabilityMarginSimple___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Stability_stabilityMarginSimple___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Stability_stabilityMarginSimple(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Stability_computeMargin___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Stability_computeMargin___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc_ref(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Stability_computeMargin___redArg___closed__0;
x_4 = l_Rat_div(x_1, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Stability_computeMargin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Stability_computeMargin___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Stability_computeMargin___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Stability_computeMargin___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Stability_computeMargin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Stability_computeMargin(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Stability_DriftRate_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Stability_DriftRate_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Stability_DriftRate_ctorIdx(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Stability_timeToFailure___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
return x_2;
}
}
static lean_object* _init_l_Stability_timeToFailure___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000000u);
x_2 = l_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Stability_timeToFailure___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Stability_timeToFailure___redArg___closed__0;
x_4 = l_instDecidableEqRat_decEq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Rat_div(x_1, x_2);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec_ref(x_2);
x_6 = l_Stability_timeToFailure___redArg___closed__1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Stability_timeToFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Stability_timeToFailure___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Stability_timeToFailure___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Stability_timeToFailure___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Stability_timeToFailure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Stability_timeToFailure(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Stability_MonitoringStatus_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Stability_MonitoringStatus_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Stability_MonitoringStatus_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Stability_computeMonitoringStatus___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(100u);
x_2 = l_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Stability_computeMonitoringStatus___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_25; 
if (x_2 == 0)
{
lean_object* x_32; 
x_32 = l_Stability_timeToFailure___redArg___closed__0;
x_25 = x_32;
goto block_31;
}
else
{
lean_inc_ref(x_1);
x_25 = x_1;
goto block_31;
}
block_24:
{
uint8_t x_8; 
lean_inc_ref(x_4);
lean_inc_ref(x_7);
x_8 = l_Rat_blt(x_7, x_4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec_ref(x_5);
x_9 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_2);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 1, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = l_Rat_blt(x_5, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_3);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_7);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*4, x_2);
lean_ctor_set_uint8(x_14, sizeof(void*)*4 + 1, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Rat_div(x_6, x_11);
lean_ctor_set(x_3, 0, x_15);
x_16 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_3);
lean_ctor_set(x_16, 3, x_4);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_2);
lean_ctor_set_uint8(x_16, sizeof(void*)*4 + 1, x_8);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
lean_inc(x_17);
x_18 = l_Rat_blt(x_5, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_7);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_4);
lean_ctor_set_uint8(x_20, sizeof(void*)*4, x_2);
lean_ctor_set_uint8(x_20, sizeof(void*)*4 + 1, x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Rat_div(x_6, x_17);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_4);
lean_ctor_set_uint8(x_23, sizeof(void*)*4, x_2);
lean_ctor_set_uint8(x_23, sizeof(void*)*4 + 1, x_8);
return x_23;
}
}
}
}
block_31:
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Stability_timeToFailure___redArg___closed__0;
lean_inc_ref(x_1);
x_27 = l_Rat_blt(x_26, x_1);
if (x_27 == 0)
{
lean_dec_ref(x_1);
x_5 = x_26;
x_6 = x_25;
x_7 = x_26;
goto block_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l_Rat_div(x_25, x_1);
x_29 = l_Stability_computeMonitoringStatus___redArg___closed__0;
x_30 = l_Rat_mul(x_28, x_29);
lean_dec_ref(x_28);
x_5 = x_26;
x_6 = x_25;
x_7 = x_30;
goto block_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Stability_computeMonitoringStatus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Stability_computeMonitoringStatus___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Stability_computeMonitoringStatus___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Stability_computeMonitoringStatus___redArg(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Stability_computeMonitoringStatus___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
x_9 = l_Stability_computeMonitoringStatus(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Perspective_AgentCoordination(uint8_t builtin);
lean_object* initialize_H1Characterization_Characterization(uint8_t builtin);
lean_object* initialize_H1Characterization_LinearComplexity(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Perspective_Stability(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_AgentCoordination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_H1Characterization_Characterization(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_H1Characterization_LinearComplexity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Stability_edgeSlack___redArg___closed__0 = _init_l_Stability_edgeSlack___redArg___closed__0();
lean_mark_persistent(l_Stability_edgeSlack___redArg___closed__0);
l_Stability_computeMargin___redArg___closed__0 = _init_l_Stability_computeMargin___redArg___closed__0();
lean_mark_persistent(l_Stability_computeMargin___redArg___closed__0);
l_Stability_timeToFailure___redArg___closed__0 = _init_l_Stability_timeToFailure___redArg___closed__0();
lean_mark_persistent(l_Stability_timeToFailure___redArg___closed__0);
l_Stability_timeToFailure___redArg___closed__1 = _init_l_Stability_timeToFailure___redArg___closed__1();
lean_mark_persistent(l_Stability_timeToFailure___redArg___closed__1);
l_Stability_computeMonitoringStatus___redArg___closed__0 = _init_l_Stability_computeMonitoringStatus___redArg___closed__0();
lean_mark_persistent(l_Stability_computeMonitoringStatus___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
