// Lean compiler output
// Module: MultiAgent
// Imports: public import Init public import MultiAgent.AgentNetworks public import MultiAgent.MemoryPerspective public import MultiAgent.MemoryConsistency public import MultiAgent.CoordinationTopology public import MultiAgent.ConsensusObstruction public import MultiAgent.ScalableH1
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
lean_object* initialize_CohomologyFoundations_MultiAgent_AgentNetworks(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_MultiAgent_MemoryPerspective(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_MultiAgent_MemoryConsistency(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_MultiAgent_CoordinationTopology(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_MultiAgent_ConsensusObstruction(uint8_t builtin);
lean_object* initialize_CohomologyFoundations_MultiAgent_ScalableH1(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CohomologyFoundations_MultiAgent(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_MultiAgent_AgentNetworks(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_MultiAgent_MemoryPerspective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_MultiAgent_MemoryConsistency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_MultiAgent_CoordinationTopology(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_MultiAgent_ConsensusObstruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CohomologyFoundations_MultiAgent_ScalableH1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
