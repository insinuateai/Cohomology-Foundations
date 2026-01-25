// Lean compiler output
// Module: Perspective.InformationBound
// Imports: public import Init public import Perspective.SpectralGap public import H1Characterization.Characterization
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
static lean_object* l_InformationBound_informationThreshold___closed__0;
LEAN_EXPORT lean_object* l_InformationBound_SharingRecommendation_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_InformationBound_SharingRecommendation_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_InformationBound_informationThreshold(lean_object*, lean_object*);
lean_object* l_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(lean_object*);
uint8_t l_Rat_blt(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
static lean_object* l_InformationBound_informationThreshold___closed__1;
LEAN_EXPORT lean_object* l_InformationBound_InformationStatus_ctorIdx(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_InformationBound_InformationStatus_ctorIdx___boxed(lean_object*);
static lean_object* _init_l_InformationBound_informationThreshold___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
return x_2;
}
}
static lean_object* _init_l_InformationBound_informationThreshold___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_InformationBound_informationThreshold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_10; 
x_3 = l_InformationBound_informationThreshold___closed__0;
lean_inc_ref(x_2);
x_10 = l_Rat_blt(x_3, x_2);
if (x_10 == 0)
{
lean_dec_ref(x_2);
goto block_9;
}
else
{
uint8_t x_11; 
lean_inc_ref(x_1);
x_11 = l_Rat_instDecidableLe(x_3, x_1);
if (x_11 == 0)
{
lean_dec_ref(x_2);
goto block_9;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_InformationBound_informationThreshold___closed__1;
x_13 = l_Rat_div(x_1, x_2);
lean_dec_ref(x_1);
x_14 = l_Rat_sub(x_12, x_13);
lean_inc_ref(x_14);
x_15 = l_Rat_instDecidableLe(x_12, x_14);
if (x_15 == 0)
{
x_4 = x_14;
goto block_6;
}
else
{
lean_dec_ref(x_14);
x_4 = x_12;
goto block_6;
}
}
}
block_6:
{
uint8_t x_5; 
lean_inc_ref(x_4);
x_5 = l_Rat_instDecidableLe(x_3, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_4);
return x_3;
}
else
{
return x_4;
}
}
block_9:
{
uint8_t x_7; 
x_7 = l_Rat_blt(x_1, x_3);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; 
x_8 = l_InformationBound_informationThreshold___closed__1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_InformationBound_InformationStatus_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_InformationBound_InformationStatus_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_InformationBound_InformationStatus_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_InformationBound_SharingRecommendation_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_InformationBound_SharingRecommendation_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_InformationBound_SharingRecommendation_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Perspective_SpectralGap(uint8_t builtin);
lean_object* initialize_H1Characterization_Characterization(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Perspective_InformationBound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_SpectralGap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_H1Characterization_Characterization(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_InformationBound_informationThreshold___closed__0 = _init_l_InformationBound_informationThreshold___closed__0();
lean_mark_persistent(l_InformationBound_informationThreshold___closed__0);
l_InformationBound_informationThreshold___closed__1 = _init_l_InformationBound_informationThreshold___closed__1();
lean_mark_persistent(l_InformationBound_informationThreshold___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
