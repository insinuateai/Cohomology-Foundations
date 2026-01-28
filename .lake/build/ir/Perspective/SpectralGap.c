// Lean compiler output
// Module: Perspective.SpectralGap
// Imports: public import Init public import Perspective.Persistence public import H1Characterization.Characterization
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
LEAN_EXPORT lean_object* lp_CohomologyFoundations_SpectralGap_optimalEdgeToAdd___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_SpectralGap_spectralGapLowerBound___closed__1;
lean_object* lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_SpectralGap_spectralGapUpperBound(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_SpectralGap_spectralGapLowerBound(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_SpectralGap_optimalEdgeToAdd(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_SpectralGap_spectralGapLowerBound___closed__0;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_SpectralGap_optimalEdgeToAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_SpectralGap_optimalEdgeToAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_CohomologyFoundations_SpectralGap_optimalEdgeToAdd(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_lp_CohomologyFoundations_SpectralGap_spectralGapLowerBound___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_SpectralGap_spectralGapLowerBound___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_SpectralGap_spectralGapLowerBound(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lp_CohomologyFoundations_SpectralGap_spectralGapLowerBound___closed__0;
x_5 = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
lean_inc_ref(x_5);
x_6 = l_Rat_mul(x_5, x_5);
lean_dec_ref(x_5);
x_7 = l_Rat_div(x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lp_CohomologyFoundations_SpectralGap_spectralGapLowerBound___closed__1;
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_SpectralGap_spectralGapUpperBound(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_Perspective_Persistence(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_H1Characterization_Characterization(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_Perspective_SpectralGap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_Perspective_Persistence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_H1Characterization_Characterization(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_CohomologyFoundations_SpectralGap_spectralGapLowerBound___closed__0 = _init_lp_CohomologyFoundations_SpectralGap_spectralGapLowerBound___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_SpectralGap_spectralGapLowerBound___closed__0);
lp_CohomologyFoundations_SpectralGap_spectralGapLowerBound___closed__1 = _init_lp_CohomologyFoundations_SpectralGap_spectralGapLowerBound___closed__1();
lean_mark_persistent(lp_CohomologyFoundations_SpectralGap_spectralGapLowerBound___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
