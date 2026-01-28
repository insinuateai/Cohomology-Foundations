// Lean compiler output
// Module: MultiAgent.CoalitionCohomology
// Imports: public import Init public import Mathlib.Data.Finset.Basic public import Mathlib.Data.Finset.Card public import Mathlib.Data.Finset.Powerset public import Mathlib.Data.Rat.Defs public import Mathlib.Algebra.BigOperators.Group.Finset.Basic public import MultiAgent.AgentNetworks
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
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_coalitionNetwork___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Coalition_empty;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionStructure_singletons(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_politicalGame___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_researchGame(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionGame_shapleyValue(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_internationalGame___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_supplyChainGame___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t lp_CohomologyFoundations___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_sum___at___00MultiAgent_internationalGame_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Multiset_sum___at___00Finset_sum___at___00MultiAgent_internationalGame_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Coalition_size___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_supplyChainGame(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionStructure_singletons___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionStructure_numCoalitions(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_teamGame(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_sum___at___00MultiAgent_internationalGame_spec__0(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionStructure_grand___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_politicalGame___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionGame_grandValue(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionStructure_numCoalitions___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_coalitionH1___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_internationalGame___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_politicalGame(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionStructure_grand(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Coalition_size(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0(lean_object*);
static lean_object* lp_CohomologyFoundations_Multiset_sum___at___00Finset_sum___at___00MultiAgent_internationalGame_spec__0_spec__0___closed__0;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_coalitionNetwork(lean_object*);
uint8_t lp_mathlib_Multiset_decidableMem___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_MultiAgent_researchGame___closed__0;
LEAN_EXPORT lean_object* lp_CohomologyFoundations___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* lp_CohomologyFoundations_MultiAgent_instDecidableEqAgent___boxed(lean_object*, lean_object*);
uint8_t l_List_decidablePerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Coalition_singleton(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_internationalGame(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionGame_shapleyValue___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_marketGame(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_coalitionH1(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_marketGame___redArg(lean_object*, lean_object*);
uint8_t l_List_decidableBAll___redArg(lean_object*, lean_object*);
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_Coalition_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Coalition_singleton(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Coalition_size(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_lengthTR___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Coalition_size___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_Coalition_size(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionStructure_numCoalitions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_List_lengthTR___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionStructure_numCoalitions___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_CoalitionStructure_numCoalitions(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionStructure_grand___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
lean_inc(x_1);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionStructure_grand(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_CoalitionStructure_grand___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_CohomologyFoundations___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_instDecidableEqAgent___boxed), 2, 0);
x_5 = l_List_decidablePerm___redArg(x_4, x_1, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
x_5 = lp_CohomologyFoundations___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_box(x_5);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(lp_CohomologyFoundations___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
lean_inc(x_4);
x_11 = l_List_decidableBAll___redArg(x_10, x_4);
if (x_11 == 0)
{
lean_dec(x_8);
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_4);
x_2 = x_7;
x_4 = x_13;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_array_mk(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec_ref(x_3);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_4);
x_8 = 0;
x_9 = lp_CohomologyFoundations___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0(x_3, x_7, x_8, x_1);
lean_dec_ref(x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lp_CohomologyFoundations_List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_mathlib_Multiset_map___redArg(x_1, x_2);
x_4 = lp_CohomologyFoundations_Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionStructure_singletons___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionStructure_singletons(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_CoalitionStructure_singletons___lam__0), 1, 0);
lean_inc(x_1);
x_3 = lp_CohomologyFoundations_Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0___redArg(x_2, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lp_CohomologyFoundations___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_pwFilter___at___00List_dedup___at___00Multiset_dedup___at___00Multiset_toFinset___at___00Finset_image___at___00MultiAgent_CoalitionStructure_singletons_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionGame_grandValue(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_CoalitionGame_shapleyValue___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_CoalitionGame_shapleyValue(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_instDecidableEqAgent___boxed), 2, 0);
lean_inc(x_2);
x_7 = lp_mathlib_Multiset_decidableMem___redArg(x_6, x_2, x_4);
if (x_7 == 0)
{
lean_object* x_8; 
lean_free_object(x_1);
lean_dec_ref(x_5);
lean_dec(x_2);
x_8 = lp_CohomologyFoundations_MultiAgent_CoalitionGame_shapleyValue___closed__0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_2);
x_10 = lean_apply_1(x_5, x_1);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_instDecidableEqAgent___boxed), 2, 0);
lean_inc(x_2);
x_14 = lp_mathlib_Multiset_decidableMem___redArg(x_13, x_2, x_11);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_12);
lean_dec(x_2);
x_15 = lp_CohomologyFoundations_MultiAgent_CoalitionGame_shapleyValue___closed__0;
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_apply_1(x_12, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_coalitionNetwork(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_coalitionNetwork___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_coalitionNetwork(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_coalitionH1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_List_lengthTR___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_coalitionH1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_coalitionH1(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_politicalGame___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_List_lengthTR___redArg(x_1);
x_3 = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_politicalGame___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_politicalGame___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_politicalGame(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_politicalGame___lam__0___boxed), 1, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_marketGame(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_marketGame___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_researchGame___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_politicalGame___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_researchGame(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lp_CohomologyFoundations_MultiAgent_researchGame___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_teamGame(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lp_CohomologyFoundations_MultiAgent_researchGame___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_supplyChainGame(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_supplyChainGame___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_lp_CohomologyFoundations_Multiset_sum___at___00Finset_sum___at___00MultiAgent_internationalGame_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_add___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Multiset_sum___at___00Finset_sum___at___00MultiAgent_internationalGame_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lp_CohomologyFoundations_Multiset_sum___at___00Finset_sum___at___00MultiAgent_internationalGame_spec__0_spec__0___closed__0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_foldrTR___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_sum___at___00MultiAgent_internationalGame_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_mathlib_Multiset_map___redArg(x_2, x_1);
x_4 = lp_CohomologyFoundations_Multiset_sum___at___00Finset_sum___at___00MultiAgent_internationalGame_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_sum___at___00MultiAgent_internationalGame_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_Finset_sum___at___00MultiAgent_internationalGame_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_internationalGame___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_3);
x_4 = lp_CohomologyFoundations_Finset_sum___at___00MultiAgent_internationalGame_spec__0___redArg(x_3, x_1);
x_5 = lean_nat_dec_le(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lp_CohomologyFoundations_MultiAgent_CoalitionGame_shapleyValue___closed__0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_List_lengthTR___redArg(x_3);
lean_dec(x_3);
x_8 = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_internationalGame___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_internationalGame___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_internationalGame(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_internationalGame___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Card(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Powerset(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Rat_Defs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_Group_Finset_Basic(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_MultiAgent_AgentNetworks(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_MultiAgent_CoalitionCohomology(uint8_t builtin) {
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
res = initialize_mathlib_Mathlib_Data_Finset_Powerset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Rat_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_Group_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_MultiAgent_AgentNetworks(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_CohomologyFoundations_MultiAgent_Coalition_empty = _init_lp_CohomologyFoundations_MultiAgent_Coalition_empty();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_Coalition_empty);
lp_CohomologyFoundations_MultiAgent_CoalitionGame_shapleyValue___closed__0 = _init_lp_CohomologyFoundations_MultiAgent_CoalitionGame_shapleyValue___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_CoalitionGame_shapleyValue___closed__0);
lp_CohomologyFoundations_MultiAgent_researchGame___closed__0 = _init_lp_CohomologyFoundations_MultiAgent_researchGame___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_researchGame___closed__0);
lp_CohomologyFoundations_Multiset_sum___at___00Finset_sum___at___00MultiAgent_internationalGame_spec__0_spec__0___closed__0 = _init_lp_CohomologyFoundations_Multiset_sum___at___00Finset_sum___at___00MultiAgent_internationalGame_spec__0_spec__0___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_Multiset_sum___at___00Finset_sum___at___00MultiAgent_internationalGame_spec__0_spec__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
