// Lean compiler output
// Module: H1Characterization.ForestCoboundary
// Imports: public import Init public import H1Characterization.PathIntegral public import Mathlib.Algebra.BigOperators.Fin
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
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_inf___at___00Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_H1Characterization_toVertex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_H1Characterization_vertexOfSimplex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_inf___at___00Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_inf___at___00Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_H1Characterization_toVertex___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_inf___at___00Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_H1Characterization_vertexOfSimplex___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0___redArg___lam__0___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_inf___at___00Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc_ref(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_inc_ref(x_2);
return x_2;
}
else
{
lean_inc_ref(x_1);
return x_1;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_inf___at___00Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_Finset_inf___at___00Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0_spec__0___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_inf___at___00Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(lp_CohomologyFoundations_Finset_inf___at___00Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0_spec__0___redArg___lam__0___boxed), 2, 0);
x_4 = lean_box(0);
x_5 = lp_mathlib_Finset_fold___redArg(x_3, x_4, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(lp_CohomologyFoundations_Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lp_CohomologyFoundations_Finset_inf___at___00Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0_spec__0___redArg(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_CohomologyFoundations_Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_inf___at___00Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_Finset_inf___at___00Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(lp_CohomologyFoundations_Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0___redArg___lam__0___boxed), 1, 0);
x_3 = lp_CohomologyFoundations_Finset_inf_x27___at___00Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0_spec__0___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_H1Characterization_vertexOfSimplex(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_H1Characterization_vertexOfSimplex___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_H1Characterization_toVertex(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_H1Characterization_toVertex___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_Finset_min_x27___at___00H1Characterization_vertexOfSimplex_spec__0___redArg(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_H1Characterization_PathIntegral(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_Fin(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_H1Characterization_ForestCoboundary(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_H1Characterization_PathIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
