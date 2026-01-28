// Lean compiler output
// Module: MultiAgent.ObservationalEquivalence
// Imports: public import Init public import Mathlib.Data.Finset.Basic public import Mathlib.Data.Finset.Card public import Mathlib.Logic.Equiv.Basic public import MultiAgent.AgentNetworks
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
LEAN_EXPORT uint8_t lp_CohomologyFoundations_MultiAgent_instDecidableEqObservation(lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__16;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr(lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__7;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Lens_singleton(lean_object*);
lean_object* lp_CohomologyFoundations_MultiAgent_instReprAgent_repr___redArg(lean_object*);
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__10;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ObservationSystem_obsH0___boxed(lean_object*);
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__19;
LEAN_EXPORT uint8_t lp_CohomologyFoundations_MultiAgent_instDecidableEqObservation_decEq(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__15;
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__1;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__11;
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__3;
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__18;
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__8;
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__2;
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__17;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Lens_size(lean_object*);
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__12;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___boxed(lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__9;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__14;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_instDecidableEqObservation_decEq___boxed(lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__6;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ObservationSystem_obsH0(lean_object*);
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation___closed__0;
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__13;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Lens_size___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Observation_self(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ObservationSystem_profileOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_instDecidableEqObservation___boxed(lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__5;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg(lean_object*);
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__4;
static lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__0;
LEAN_EXPORT uint8_t lp_CohomologyFoundations_MultiAgent_instDecidableEqObservation_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_nat_dec_eq(x_3, x_6);
if (x_9 == 0)
{
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_4, x_7);
if (x_10 == 0)
{
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_5, x_8);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_instDecidableEqObservation_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_CohomologyFoundations_MultiAgent_instDecidableEqObservation_decEq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_CohomologyFoundations_MultiAgent_instDecidableEqObservation(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_instDecidableEqObservation_decEq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_instDecidableEqObservation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_CohomologyFoundations_MultiAgent_instDecidableEqObservation(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("observer", 8, 8);
return x_1;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__5;
x_2 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__3;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("observed", 8, 8);
return x_1;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("result", 6, 6);
return x_1;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__16;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__5;
x_6 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__6;
x_7 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__7;
x_8 = lp_CohomologyFoundations_MultiAgent_instReprAgent_repr___redArg(x_2);
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = 0;
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
x_13 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__9;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__11;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
x_20 = lp_CohomologyFoundations_MultiAgent_instReprAgent_repr___redArg(x_3);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_10);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_13);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_15);
x_26 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__13;
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
x_29 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__14;
x_30 = l_Nat_reprFast(x_4);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_10);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
x_35 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__17;
x_36 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__18;
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
x_38 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__19;
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_10);
return x_41;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_MultiAgent_instReprObservation_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_lp_CohomologyFoundations_MultiAgent_instReprObservation() {
_start:
{
lean_object* x_1; 
x_1 = lp_CohomologyFoundations_MultiAgent_instReprObservation___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Observation_self(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ObservationSystem_profileOf(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 0);
lean_dec(x_5);
lean_inc(x_2);
x_6 = lean_apply_1(x_4, x_2);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_2);
x_8 = lean_apply_1(x_7, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Lens_size(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_List_lengthTR___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Lens_size___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_Lens_size(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_Lens_singleton(lean_object* x_1) {
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
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ObservationSystem_obsH0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_MultiAgent_ObservationSystem_obsH0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_MultiAgent_ObservationSystem_obsH0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Card(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Logic_Equiv_Basic(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_MultiAgent_AgentNetworks(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_MultiAgent_ObservationalEquivalence(uint8_t builtin) {
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
res = initialize_mathlib_Mathlib_Logic_Equiv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_MultiAgent_AgentNetworks(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__4 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__4();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__4);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__5 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__5();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__5);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__1 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__1();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__1);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__2 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__2();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__2);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__3 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__3();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__3);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__6 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__6();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__6);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__7 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__7();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__7);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__8 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__8();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__8);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__9 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__9();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__9);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__10 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__10();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__10);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__11 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__11();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__11);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__12 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__12();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__12);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__13 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__13();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__13);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__14 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__14();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__14);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__0 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__0);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__16 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__16();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__16);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__17 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__17();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__17);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__18 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__18();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__18);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__15 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__15();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__15);
lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__19 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__19();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation_repr___redArg___closed__19);
lp_CohomologyFoundations_MultiAgent_instReprObservation___closed__0 = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation___closed__0);
lp_CohomologyFoundations_MultiAgent_instReprObservation = _init_lp_CohomologyFoundations_MultiAgent_instReprObservation();
lean_mark_persistent(lp_CohomologyFoundations_MultiAgent_instReprObservation);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
