// Lean compiler output
// Module: Perspective.ParetoTopology
// Imports: public import Init public import Perspective.FairnessFoundations
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
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_frontierCurvature(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_frontierDimension(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_distanceToFrontier___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_marginalRateOfSubstitution___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_generateParetoReport___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_marginalRateOfSubstitution___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix___redArg___closed__0;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_frontierDimension___boxed(lean_object*);
static lean_object* lp_CohomologyFoundations_ParetoTopology_generateParetoReport___redArg___closed__0;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__1;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_generateParetoReport(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_distanceToFrontier(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_marginalRateOfSubstitution(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_ParetoTopology_distanceToFrontier___closed__0;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_generateParetoReport___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_marginalRateOfSubstitution___redArg___boxed(lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__0;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_frontierCurvature___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_generateParetoReport___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
static lean_object* _init_lp_CohomologyFoundations_ParetoTopology_distanceToFrontier___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_distanceToFrontier(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_ParetoTopology_distanceToFrontier___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_distanceToFrontier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_ParetoTopology_distanceToFrontier(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_frontierDimension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_frontierDimension___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_ParetoTopology_frontierDimension(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__1;
x_2 = lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__0;
x_3 = l_Rat_div(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_frontierCurvature(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__2;
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_frontierCurvature___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_ParetoTopology_frontierCurvature(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_marginalRateOfSubstitution___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__0;
x_4 = lp_CohomologyFoundations_ParetoTopology_frontierCurvature(x_1, x_2, lean_box(0));
x_5 = l_Rat_add(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_marginalRateOfSubstitution(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_ParetoTopology_marginalRateOfSubstitution___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_marginalRateOfSubstitution___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_ParetoTopology_marginalRateOfSubstitution(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_marginalRateOfSubstitution___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_ParetoTopology_marginalRateOfSubstitution___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__0;
x_2 = l_Rat_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_ParetoTopology_marginalRateOfSubstitution___redArg(x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix___redArg___closed__0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_lp_CohomologyFoundations_ParetoTopology_generateParetoReport___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Pareto analysis requires optimization solver for full evaluation.", 65, 65);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_generateParetoReport___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lp_CohomologyFoundations_ParetoTopology_distanceToFrontier(x_1, x_2, lean_box(0));
x_4 = lp_CohomologyFoundations_ParetoTopology_frontierDimension(x_1);
x_5 = lp_CohomologyFoundations_ParetoTopology_frontierCurvature(x_1, x_2, lean_box(0));
x_6 = 1;
x_7 = lp_CohomologyFoundations_ParetoTopology_generateParetoReport___redArg___closed__0;
x_8 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*4 + 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_generateParetoReport(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_CohomologyFoundations_ParetoTopology_generateParetoReport___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_generateParetoReport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_CohomologyFoundations_ParetoTopology_generateParetoReport(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_ParetoTopology_generateParetoReport___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_CohomologyFoundations_ParetoTopology_generateParetoReport___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_Perspective_FairnessFoundations(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_Perspective_ParetoTopology(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_Perspective_FairnessFoundations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_CohomologyFoundations_ParetoTopology_distanceToFrontier___closed__0 = _init_lp_CohomologyFoundations_ParetoTopology_distanceToFrontier___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_ParetoTopology_distanceToFrontier___closed__0);
lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__0 = _init_lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__0);
lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__1 = _init_lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__1();
lean_mark_persistent(lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__1);
lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__2 = _init_lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__2();
lean_mark_persistent(lp_CohomologyFoundations_ParetoTopology_frontierCurvature___closed__2);
lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix___redArg___closed__0 = _init_lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix___redArg___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_ParetoTopology_tradeoffMatrix___redArg___closed__0);
lp_CohomologyFoundations_ParetoTopology_generateParetoReport___redArg___closed__0 = _init_lp_CohomologyFoundations_ParetoTopology_generateParetoReport___redArg___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_ParetoTopology_generateParetoReport___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
