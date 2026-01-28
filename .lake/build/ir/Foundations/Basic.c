// Lean compiler output
// Module: Foundations.Basic
// Imports: public import Init public import Mathlib.Algebra.Field.Defs public import Mathlib.Data.Rat.Defs public import Mathlib.Data.Finset.Basic public import Mathlib.Tactic.Ring
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
static lean_object* lp_CohomologyFoundations_Foundations_sign___closed__1;
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_sign(lean_object*);
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_sign___boxed(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* lp_CohomologyFoundations_Foundations_sign___closed__0;
lean_object* l_Rat_neg(lean_object*);
static lean_object* _init_lp_CohomologyFoundations_Foundations_sign___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Ring_ExProd_mkNat_spec__0(x_1);
return x_2;
}
}
static lean_object* _init_lp_CohomologyFoundations_Foundations_sign___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_CohomologyFoundations_Foundations_sign___closed__0;
x_2 = l_Rat_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_sign(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lp_CohomologyFoundations_Foundations_sign___closed__1;
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lp_CohomologyFoundations_Foundations_sign___closed__0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_CohomologyFoundations_Foundations_sign___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_CohomologyFoundations_Foundations_sign(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Field_Defs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Rat_Defs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_Ring(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_Foundations_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Field_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Rat_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_CohomologyFoundations_Foundations_sign___closed__0 = _init_lp_CohomologyFoundations_Foundations_sign___closed__0();
lean_mark_persistent(lp_CohomologyFoundations_Foundations_sign___closed__0);
lp_CohomologyFoundations_Foundations_sign___closed__1 = _init_lp_CohomologyFoundations_Foundations_sign___closed__1();
lean_mark_persistent(lp_CohomologyFoundations_Foundations_sign___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
