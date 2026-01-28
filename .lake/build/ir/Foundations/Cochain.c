// Lean compiler output
// Module: Foundations.Cochain
// Imports: public import Init public import Foundations.Simplex
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
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instSub(lean_object*, lean_object*);
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instZero___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instSub___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instAdd___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instSMulCoeff___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instZero___lam__0___boxed(lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instSMulCoeff___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instAdd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instZero___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instNeg(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instSub___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instSMulCoeff___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instNeg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instNeg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instZero(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instSMulCoeff(lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_Foundations_Cochain_instZero___lam__0___closed__0;
lean_object* l_Rat_neg(lean_object*);
static lean_object* _init_lp_CohomologyFoundations_Foundations_Cochain_instZero___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Rat_instNatCast___lam__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instZero___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_Foundations_Cochain_instZero___lam__0___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instZero___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_Foundations_Cochain_instZero___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instZero(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_CohomologyFoundations_Foundations_Cochain_instZero___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instZero___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_Foundations_Cochain_instZero(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instAdd___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_3);
x_6 = l_Rat_add(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instAdd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_CohomologyFoundations_Foundations_Cochain_instAdd___lam__0), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instAdd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_Foundations_Cochain_instAdd(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instNeg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = l_Rat_neg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instNeg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_CohomologyFoundations_Foundations_Cochain_instNeg___lam__0), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instNeg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_Foundations_Cochain_instNeg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instSMulCoeff___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = l_Rat_mul(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instSMulCoeff___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_Foundations_Cochain_instSMulCoeff___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instSMulCoeff(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_CohomologyFoundations_Foundations_Cochain_instSMulCoeff___lam__0___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instSMulCoeff___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_Foundations_Cochain_instSMulCoeff(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instSub___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_3);
x_6 = l_Rat_sub(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instSub(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(lp_CohomologyFoundations_Foundations_Cochain_instSub___lam__0), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_Cochain_instSub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_Foundations_Cochain_instSub(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_Foundations_Simplex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_Foundations_Cochain(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_Foundations_Simplex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_CohomologyFoundations_Foundations_Cochain_instZero___lam__0___closed__0 = _init_lp_CohomologyFoundations_Foundations_Cochain_instZero___lam__0___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_Foundations_Cochain_instZero___lam__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
