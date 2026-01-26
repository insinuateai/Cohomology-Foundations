// Lean compiler output
// Module: Perspective
// Imports: public import Init public import Perspective.ValueSystem public import Perspective.Alignment public import Perspective.ValueComplex public import Perspective.AlignmentEquivalence public import Perspective.AlignmentTheorem public import Perspective.ImpossibilityStrong public import Perspective.ConflictLocalization public import Perspective.ConflictResolution public import Perspective.AgentCoordination public import Perspective.Stability public import Perspective.ObstructionClassification public import Perspective.IncrementalUpdates public import Perspective.HierarchicalAlignment public import Perspective.MayerVietoris public import Perspective.DimensionBound public import Perspective.Persistence public import Perspective.SpectralGap public import Perspective.InformationBound public import Perspective.OptimalRepair public import Perspective.Compositional public import Perspective.Barrier
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Perspective_ValueSystem(uint8_t builtin);
lean_object* initialize_Perspective_Alignment(uint8_t builtin);
lean_object* initialize_Perspective_ValueComplex(uint8_t builtin);
lean_object* initialize_Perspective_AlignmentEquivalence(uint8_t builtin);
lean_object* initialize_Perspective_AlignmentTheorem(uint8_t builtin);
lean_object* initialize_Perspective_ImpossibilityStrong(uint8_t builtin);
lean_object* initialize_Perspective_ConflictLocalization(uint8_t builtin);
lean_object* initialize_Perspective_ConflictResolution(uint8_t builtin);
lean_object* initialize_Perspective_AgentCoordination(uint8_t builtin);
lean_object* initialize_Perspective_Stability(uint8_t builtin);
lean_object* initialize_Perspective_ObstructionClassification(uint8_t builtin);
lean_object* initialize_Perspective_IncrementalUpdates(uint8_t builtin);
lean_object* initialize_Perspective_HierarchicalAlignment(uint8_t builtin);
lean_object* initialize_Perspective_MayerVietoris(uint8_t builtin);
lean_object* initialize_Perspective_DimensionBound(uint8_t builtin);
lean_object* initialize_Perspective_Persistence(uint8_t builtin);
lean_object* initialize_Perspective_SpectralGap(uint8_t builtin);
lean_object* initialize_Perspective_InformationBound(uint8_t builtin);
lean_object* initialize_Perspective_OptimalRepair(uint8_t builtin);
lean_object* initialize_Perspective_Compositional(uint8_t builtin);
lean_object* initialize_Perspective_Barrier(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Perspective(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_ValueSystem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_Alignment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_ValueComplex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_AlignmentEquivalence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_AlignmentTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_ImpossibilityStrong(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_ConflictLocalization(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_ConflictResolution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_AgentCoordination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_Stability(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_ObstructionClassification(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_IncrementalUpdates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_HierarchicalAlignment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_MayerVietoris(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_DimensionBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_Persistence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_SpectralGap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_InformationBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_OptimalRepair(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_Compositional(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Perspective_Barrier(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
