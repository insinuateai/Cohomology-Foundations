// Lean compiler output
// Module: Perspective.ValueSystem
// Imports: public import Init public import Foundations.Cohomology public import Mathlib.Data.Rat.Defs
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
LEAN_EXPORT uint8_t lp_CohomologyFoundations_Perspective_instDecidableLocallyAgree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_CohomologyFoundations_Perspective_AgreementSet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Rat_instDistribLattice;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Perspective_instDecidableLocallyAgree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Perspective_AgreementSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_abs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Perspective_AgreementSet___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_CohomologyFoundations_Perspective_instDecidableLocallyAgree___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Perspective_AgreementSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Rat_addCommGroup;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Perspective_instDecidableLocallyAgree___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_CohomologyFoundations_Perspective_instDecidableLocallyAgree___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lp_mathlib_Rat_instDistribLattice;
x_6 = lp_mathlib_Rat_addCommGroup;
lean_inc(x_3);
x_7 = lean_apply_1(x_1, x_3);
x_8 = lean_apply_1(x_2, x_3);
x_9 = l_Rat_sub(x_7, x_8);
x_10 = lp_mathlib_abs___redArg(x_5, x_6, x_9);
x_11 = l_Rat_instDecidableLe(x_10, x_4);
return x_11;
}
}
LEAN_EXPORT uint8_t lp_CohomologyFoundations_Perspective_instDecidableLocallyAgree(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lp_CohomologyFoundations_Perspective_instDecidableLocallyAgree___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Perspective_instDecidableLocallyAgree___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lp_CohomologyFoundations_Perspective_instDecidableLocallyAgree(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Perspective_instDecidableLocallyAgree___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_CohomologyFoundations_Perspective_instDecidableLocallyAgree___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_CohomologyFoundations_Perspective_AgreementSet___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lp_CohomologyFoundations_Perspective_instDecidableLocallyAgree___redArg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Perspective_AgreementSet___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_CohomologyFoundations_Perspective_AgreementSet___redArg___lam__0(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Perspective_AgreementSet___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(lp_CohomologyFoundations_Perspective_AgreementSet___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
x_6 = lp_mathlib_Multiset_filter___redArg(x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Perspective_AgreementSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_Perspective_AgreementSet___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_Foundations_Cohomology(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Rat_Defs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_Perspective_ValueSystem(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_Foundations_Cohomology(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Rat_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
