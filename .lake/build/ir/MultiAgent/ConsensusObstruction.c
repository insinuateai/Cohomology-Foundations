// Lean compiler output
// Module: MultiAgent.ConsensusObstruction
// Imports: public import Init public import Mathlib.Data.Finset.Basic public import Mathlib.Data.Finset.Card public import Mathlib.Data.Finset.Lattice.Basic public import MultiAgent.AgentNetworks
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
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_singleton___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_toNetwork___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_toNetwork___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_numAgents___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_MultiAgent_ConsensusInstance_decidableAcceptable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_singleton___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_singleton___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_numAgents___redArg(lean_object*);
LEAN_EXPORT uint8_t l_MultiAgent_ConsensusInstance_decidableAcceptable___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_singleton(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_numAgents___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_numAgents(lean_object*, lean_object*);
uint8_t l_Multiset_decidableMem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_singleton___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_decidableAcceptable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_decidableAcceptable___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_toNetwork___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_singleton___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_toNetwork(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MultiAgent_ConsensusInstance_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_numAgents___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_List_lengthTR___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_numAgents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MultiAgent_ConsensusInstance_numAgents___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_numAgents___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MultiAgent_ConsensusInstance_numAgents___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_numAgents___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MultiAgent_ConsensusInstance_numAgents(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_singleton___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_singleton___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_singleton___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_closure((void*)(l_MultiAgent_ConsensusInstance_singleton___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l_MultiAgent_ConsensusInstance_singleton___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_singleton(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_MultiAgent_ConsensusInstance_singleton___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_singleton___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MultiAgent_ConsensusInstance_singleton___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_singleton___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MultiAgent_ConsensusInstance_singleton___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_MultiAgent_ConsensusInstance_decidableAcceptable___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_apply_1(x_5, x_3);
x_7 = l_Multiset_decidableMem___redArg(x_1, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_MultiAgent_ConsensusInstance_decidableAcceptable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_MultiAgent_ConsensusInstance_decidableAcceptable___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_decidableAcceptable___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_MultiAgent_ConsensusInstance_decidableAcceptable___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_decidableAcceptable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_MultiAgent_ConsensusInstance_decidableAcceptable(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_toNetwork___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_toNetwork(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_toNetwork___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MultiAgent_ConsensusInstance_toNetwork___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MultiAgent_ConsensusInstance_toNetwork___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_MultiAgent_ConsensusInstance_toNetwork(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Finset_Card(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Finset_Lattice_Basic(uint8_t builtin);
lean_object* initialize_MultiAgent_AgentNetworks(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MultiAgent_ConsensusObstruction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Card(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Lattice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MultiAgent_AgentNetworks(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
