// Lean compiler output
// Module: MultiAgent.MemoryPerspective
// Imports: public import Init public import Mathlib.Data.Finset.Basic public import Mathlib.Data.Finset.Card public import Mathlib.Data.Finset.Lattice.Basic public import Mathlib.Logic.Function.Basic public import MultiAgent.AgentNetworks
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
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Perspective_merge(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_toNetwork___redArg___boxed(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_updateMemory___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_overlap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_instDecidableEqMemoryState___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_singleton___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_empty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_removeFact(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_singleton(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_empty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_numAgents(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_size___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_union(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_empty___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_instDecidableEqMemoryState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_addFact(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndinter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_toNetwork___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_updateMemory___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_numAgents___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_singleton___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_inter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_singleton(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_singleton___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_CohomologyFoundations_MultiAgent_instDecidableEqMemoryState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_updateMemory___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_removeFact___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_addFact___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_CohomologyFoundations_MultiAgent_instDecidableEqMemoryState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_inter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Perspective_merge___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_overlap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_toNetwork(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_updateMemory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_numAgents___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_singleton___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_empty___lam__0(lean_object*);
uint8_t l_List_decidablePerm___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndinsert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_numAgents___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_toNetwork___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_updateMemory___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_singleton___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndunion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_singleton___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_CohomologyFoundations_MultiAgent_instDecidableEqMemoryState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_List_decidablePerm___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_CohomologyFoundations_MultiAgent_instDecidableEqMemoryState___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_decidablePerm___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_instDecidableEqMemoryState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_CohomologyFoundations_MultiAgent_instDecidableEqMemoryState(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_instDecidableEqMemoryState___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_CohomologyFoundations_MultiAgent_instDecidableEqMemoryState___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_size(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_lengthTR___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_size___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_lengthTR___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_MemoryState_size(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_size___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_MemoryState_size___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_empty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_empty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_MemoryState_empty(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_singleton___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_singleton(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_MemoryState_singleton___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_singleton___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_MemoryState_singleton(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_addFact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_mathlib_Multiset_ndinsert___redArg(x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_addFact___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_mathlib_Multiset_ndinsert___redArg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_removeFact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_mathlib_Multiset_erase___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_removeFact___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_mathlib_Multiset_erase___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_union(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_mathlib_Multiset_ndunion___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_union___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_mathlib_Multiset_ndunion___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_inter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_mathlib_Multiset_ndinter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_MemoryState_inter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_mathlib_Multiset_ndinter___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_numAgents___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_List_lengthTR___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_numAgents(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_AgentMemory_numAgents___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_numAgents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_AgentMemory_numAgents(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_numAgents___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_AgentMemory_numAgents___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_empty___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_empty___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_AgentMemory_empty___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_empty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_AgentMemory_empty___lam__0___boxed), 1, 0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_empty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_AgentMemory_empty(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_singleton___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_singleton___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_AgentMemory_singleton___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_singleton___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_AgentMemory_singleton___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_singleton(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_CohomologyFoundations_MultiAgent_AgentMemory_singleton___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_singleton___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_CohomologyFoundations_MultiAgent_AgentMemory_singleton(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_updateMemory___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_1(x_2, x_4);
return x_6;
}
else
{
lean_dec(x_4);
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_updateMemory___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_CohomologyFoundations_MultiAgent_AgentMemory_updateMemory___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_updateMemory___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_AgentMemory_updateMemory___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_3);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_AgentMemory_updateMemory___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_updateMemory(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_MultiAgent_AgentMemory_updateMemory___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_updateMemory___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_MultiAgent_AgentMemory_updateMemory(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_overlap___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
lean_inc(x_5);
x_6 = lean_apply_1(x_5, x_3);
x_7 = lean_apply_1(x_5, x_4);
x_8 = lp_mathlib_Multiset_ndinter___redArg(x_1, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_overlap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_MultiAgent_AgentMemory_overlap___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_toNetwork(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_toNetwork___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_toNetwork___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_AgentMemory_toNetwork(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_AgentMemory_toNetwork___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_AgentMemory_toNetwork___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Perspective_merge(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_mathlib_Multiset_ndunion___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Perspective_merge___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_mathlib_Multiset_ndunion___redArg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Card(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Lattice_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Logic_Function_Basic(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_MultiAgent_AgentNetworks(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_MultiAgent_MemoryPerspective(uint8_t builtin) {
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
res = initialize_mathlib_Mathlib_Data_Finset_Lattice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Logic_Function_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_MultiAgent_AgentNetworks(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
