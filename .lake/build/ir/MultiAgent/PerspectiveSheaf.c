// Lean compiler output
// Module: MultiAgent.PerspectiveSheaf
// Imports: public import Init public import Mathlib.Data.Finset.Basic public import Mathlib.Data.Finset.Card public import Mathlib.Algebra.Group.Defs public import MultiAgent.AgentNetworks
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
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_empty(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentRAGSystem___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_constant(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_const___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_coboundary0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_intPresheaf___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_trivial___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ragPerspectiveSheaf___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_perspectiveSheaf___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_sum___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_empty___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_sum___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_sessionPerspectiveSheaf(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_instCoeFunForallAgentFinsetNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_chatPerspectiveSheaf___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_coboundary0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentRAGSystem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ragPerspectiveSheaf(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_getData(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_intPresheaf___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_empty___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_const(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_trivial___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_perspectiveSheaf___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ragPerspectiveSheaf___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_constant___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_localSection___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_natPresheaf___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_instCoeFunForallAgentFinsetNat(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_intPresheaf(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_chatPerspectiveSheaf___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_chatPerspectiveSheaf(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_constant___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_getData___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_localSection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_const___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_trivial___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_empty___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_constant___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_trivial___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_const___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_sessionPerspectiveSheaf___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_natPresheaf(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_constant___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_const___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_natPresheaf___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_constant___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_getData___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_sum(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentRAGSystem___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_sessionPerspectiveSheaf___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_List_getD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_instCoeFunForallAgentFinsetNat___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_perspectiveSheaf(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_trivial;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_constant___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_constant___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_constant___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_Presheaf_constant___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_constant___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_Presheaf_constant___redArg___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_constant___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_Presheaf_constant___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_Presheaf_constant___redArg___lam__1___boxed), 3, 0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_constant(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_Presheaf_constant___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_trivial___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_trivial___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_trivial___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_Presheaf_trivial___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_trivial___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_Presheaf_trivial___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_Presheaf_trivial() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_Presheaf_trivial___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_Presheaf_trivial___lam__1___boxed), 3, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_intPresheaf___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_intPresheaf___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_Presheaf_intPresheaf___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_intPresheaf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_Presheaf_intPresheaf___lam__0___boxed), 3, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_natPresheaf___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_natPresheaf___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_Presheaf_natPresheaf___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_natPresheaf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_Presheaf_natPresheaf___lam__0___boxed), 3, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_sum___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
lean_inc(x_4);
x_7 = lean_apply_1(x_5, x_4);
x_8 = lean_apply_1(x_6, x_4);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_sum___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_3(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_sum___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc_ref(x_2);
x_4 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_Presheaf_sum___redArg___lam__0), 4, 3);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_1);
x_5 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_Presheaf_sum___redArg___lam__1), 4, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_sum(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_CohomologyFoundations_MultiAgent_Presheaf_sum___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_localSection___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Presheaf_localSection(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_Presheaf_localSection___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_coboundary0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_apply_1(x_2, x_3);
x_7 = lean_apply_2(x_1, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_coboundary0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_MultiAgent_coboundary0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_instCoeFunForallAgentFinsetNat___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_instCoeFunForallAgentFinsetNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_instCoeFunForallAgentFinsetNat___lam__0), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_instCoeFunForallAgentFinsetNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_instCoeFunForallAgentFinsetNat(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_empty___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_empty___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_empty___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_empty___lam__0___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_empty___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_empty(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_const___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_const___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_const___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_const(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_const___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_const___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_const___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_const___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_const(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_getData(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_getData___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_getData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_ConsistentAgentSystem_getData(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_perspectiveSheaf___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_perspectiveSheaf___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_perspectiveSheaf___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_perspectiveSheaf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_perspectiveSheaf___lam__0___boxed), 3, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ragPerspectiveSheaf___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_getD___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ragPerspectiveSheaf___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_ragPerspectiveSheaf___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ragPerspectiveSheaf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_ragPerspectiveSheaf___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lp_CohomologyFoundations_MultiAgent_perspectiveSheaf(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_chatPerspectiveSheaf___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_getD___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_chatPerspectiveSheaf___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_chatPerspectiveSheaf___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_chatPerspectiveSheaf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_chatPerspectiveSheaf___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lp_CohomologyFoundations_MultiAgent_perspectiveSheaf(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_sessionPerspectiveSheaf___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_getD___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_sessionPerspectiveSheaf___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_sessionPerspectiveSheaf___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_sessionPerspectiveSheaf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_sessionPerspectiveSheaf___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lp_CohomologyFoundations_MultiAgent_perspectiveSheaf(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentRAGSystem___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_ragPerspectiveSheaf___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentRAGSystem(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_ConsistentRAGSystem___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ConsistentRAGSystem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_MultiAgent_ConsistentRAGSystem(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Card(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Group_Defs(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_MultiAgent_AgentNetworks(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_MultiAgent_PerspectiveSheaf(uint8_t builtin) {
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
res = initialize_mathlib_Mathlib_Algebra_Group_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_MultiAgent_AgentNetworks(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_CohomologyFoundations_MultiAgent_Presheaf_trivial = _init_lp_CohomologyFoundations_MultiAgent_Presheaf_trivial();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_Presheaf_trivial);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
