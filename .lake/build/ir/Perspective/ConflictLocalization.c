// Lean compiler output
// Module: Perspective.ConflictLocalization
// Imports: public import Init public import Perspective.AlignmentEquivalence public import Perspective.ImpossibilityStrong public import H1Characterization.Characterization public import H1Characterization.CycleCochain.Definitions
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
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_ctorIdx___boxed(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_involvedEdges___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_size(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Perspective_AlignmentConflict_toDiagnostic_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Perspective_AlignmentConflict_toDiagnostic___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Perspective_ConflictDiagnostic_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Perspective_AlignmentConflict_toDiagnostic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* l_SimpleGraph_Walk_support___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Perspective_ConflictDiagnostic_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_involvedVertices___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Perspective_AlignmentConflict_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_involvedVertices(lean_object*, lean_object*);
lean_object* l_SimpleGraph_Walk_edges___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_involvedEdges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Perspective_AlignmentConflict_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Perspective_AlignmentConflict_toDiagnostic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Perspective_ConflictWitness_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_involvedVertices___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_SimpleGraph_Walk_support___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_involvedVertices(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Perspective_ConflictWitness_involvedVertices___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_involvedEdges___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_box(0);
x_5 = l_SimpleGraph_Walk_edges___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_involvedEdges(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Perspective_ConflictWitness_involvedEdges___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_size___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_SimpleGraph_Walk_support___redArg(x_2, x_3);
x_5 = l_List_lengthTR___redArg(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Perspective_ConflictWitness_size(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Perspective_ConflictWitness_size___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Perspective_AlignmentConflict_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(0u);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Perspective_AlignmentConflict_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Perspective_AlignmentConflict_ctorIdx(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Perspective_ConflictDiagnostic_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Perspective_ConflictDiagnostic_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Perspective_ConflictDiagnostic_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Perspective_AlignmentConflict_toDiagnostic_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Perspective_AlignmentConflict_toDiagnostic___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = lean_box(0);
lean_inc(x_1);
x_3 = l_List_mapTR_loop___at___00Perspective_AlignmentConflict_toDiagnostic_spec__0(x_1, x_2);
x_4 = l_List_lengthTR___redArg(x_1);
x_5 = 0;
x_6 = l_List_head_x3f___redArg(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Perspective_AlignmentConflict_toDiagnostic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Perspective_AlignmentConflict_toDiagnostic___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Perspective_AlignmentConflict_toDiagnostic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Perspective_AlignmentConflict_toDiagnostic(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Perspective_AlignmentEquivalence(uint8_t builtin);
lean_object* initialize_Perspective_ImpossibilityStrong(uint8_t builtin);
lean_object* initialize_H1Characterization_Characterization(uint8_t builtin);
lean_object* initialize_H1Characterization_CycleCochain_Definitions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Perspective_ConflictLocalization(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_AlignmentEquivalence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_ImpossibilityStrong(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_H1Characterization_Characterization(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_H1Characterization_CycleCochain_Definitions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
