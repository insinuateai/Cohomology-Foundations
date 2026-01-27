// Lean compiler output
// Module: Perspective.GroupFairness
// Imports: public import Init public import Perspective.FairnessBarriers
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
lean_object* l_Finset_inf_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_maxIntersectionalGroups(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_demographicParityConstraint___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_withinGroupInequality___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_totalWithinInequality(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_IntersectionalIdentity_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_demographicParityConstraint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_GroupPartition_ctorIdx___boxed(lean_object*, lean_object*);
extern lean_object* l_Rat_instSemilatticeSup;
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_groupDisparity___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Rat_instSemilatticeInf;
LEAN_EXPORT lean_object* l_GroupFairness_equalOpportunityConstraint___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_GroupFairness_equalOpportunityConstraint___closed__0;
LEAN_EXPORT lean_object* l_GroupFairness_maxIntersectionalGroups___boxed(lean_object*, lean_object*);
lean_object* l_Finset_sum___at___00Foundations_coboundary_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_GroupFairness_groupMembers___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_equalOpportunityConstraint(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_groupDisparity(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_IntersectionalIdentity_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_withinGroupInequality(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_abs___at___00Rat_nnabs_spec__0(lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_GroupFairnessReport_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_GroupPartition_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_groupSize(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_GroupFairnessReport_ctorIdx(lean_object*, lean_object*);
static lean_object* l_GroupFairness_demographicParityConstraint___closed__0;
LEAN_EXPORT lean_object* l_GroupFairness_groupAllocation(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Finset_sup_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_groupMembers___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_groupDisparity___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_groupMembers(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_totalWithinInequality___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_GroupFairness_GroupPartition_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_GroupPartition_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_GroupFairness_GroupPartition_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_GroupFairness_groupMembers___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_nat_dec_eq(x_5, x_2);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_groupMembers(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_GroupFairness_groupMembers___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = l_List_finRange(x_1);
x_6 = l_Multiset_filter___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_groupMembers___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_GroupFairness_groupMembers___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_groupSize(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_GroupFairness_groupMembers(x_1, x_2, x_3);
x_5 = l_List_lengthTR___redArg(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_groupAllocation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_GroupFairness_groupMembers(x_1, x_3, x_4);
x_6 = l_Finset_sum___at___00Foundations_coboundary_spec__0___redArg(x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_IntersectionalIdentity_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_IntersectionalIdentity_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_GroupFairness_IntersectionalIdentity_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_maxIntersectionalGroups(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_pow(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_maxIntersectionalGroups___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_GroupFairness_maxIntersectionalGroups(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_groupDisparity___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
x_5 = l_GroupFairness_groupAllocation(x_1, x_2, x_3, x_4);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_GroupFairness_groupSize(x_1, x_3, x_4);
x_12 = lean_nat_dec_le(x_10, x_11);
if (x_12 == 0)
{
lean_dec(x_11);
x_6 = x_10;
goto block_9;
}
else
{
x_6 = x_11;
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Rat_instNatCast___lam__0(x_6);
x_8 = l_Rat_div(x_5, x_7);
lean_dec_ref(x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_GroupFairness_groupDisparity___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Rat_instSemilatticeSup;
x_5 = l_Rat_instSemilatticeInf;
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_GroupFairness_groupDisparity___redArg___lam__0), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
x_8 = l_List_finRange(x_6);
lean_inc_ref(x_7);
lean_inc(x_8);
x_9 = l_Finset_sup_x27___redArg(x_4, x_8, x_7);
x_10 = l_Finset_inf_x27___redArg(x_5, x_8, x_7);
x_11 = l_Rat_sub(x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_groupDisparity(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_GroupFairness_groupDisparity___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_withinGroupInequality___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = l_Rat_sub(x_4, x_2);
x_6 = l_abs___at___00Rat_nnabs_spec__0(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_withinGroupInequality(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
x_5 = l_GroupFairness_groupMembers(x_1, x_3, x_4);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_6 = l_GroupFairness_groupAllocation(x_1, x_2, x_3, x_4);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_GroupFairness_groupSize(x_1, x_3, x_4);
x_15 = lean_nat_dec_le(x_13, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
x_7 = x_13;
goto block_12;
}
else
{
x_7 = x_14;
goto block_12;
}
block_12:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_7);
x_9 = l_Rat_div(x_6, x_8);
lean_dec_ref(x_6);
x_10 = lean_alloc_closure((void*)(l_GroupFairness_withinGroupInequality___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Finset_sum___at___00Foundations_coboundary_spec__0___redArg(x_5, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_GroupFairness_totalWithinInequality___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_GroupFairness_withinGroupInequality(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_totalWithinInequality(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_GroupFairness_totalWithinInequality___lam__0), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
x_6 = l_List_finRange(x_4);
x_7 = l_Finset_sum___at___00Foundations_coboundary_spec__0___redArg(x_6, x_5);
return x_7;
}
}
static lean_object* _init_l_GroupFairness_demographicParityConstraint___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Demographic parity within tolerance", 35, 35);
return x_1;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_demographicParityConstraint(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_GroupFairness_demographicParityConstraint___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_demographicParityConstraint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_GroupFairness_demographicParityConstraint(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_GroupFairness_equalOpportunityConstraint___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Equal opportunity for qualified individuals", 43, 43);
return x_1;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_equalOpportunityConstraint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_GroupFairness_equalOpportunityConstraint___closed__0;
return x_5;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_equalOpportunityConstraint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_GroupFairness_equalOpportunityConstraint(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_GroupFairnessReport_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_GroupFairness_GroupFairnessReport_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_GroupFairness_GroupFairnessReport_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Perspective_FairnessBarriers(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Perspective_GroupFairness(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_FairnessBarriers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_GroupFairness_demographicParityConstraint___closed__0 = _init_l_GroupFairness_demographicParityConstraint___closed__0();
lean_mark_persistent(l_GroupFairness_demographicParityConstraint___closed__0);
l_GroupFairness_equalOpportunityConstraint___closed__0 = _init_l_GroupFairness_equalOpportunityConstraint___closed__0();
lean_mark_persistent(l_GroupFairness_equalOpportunityConstraint___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
