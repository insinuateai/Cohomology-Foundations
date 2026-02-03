/-
  Infrastructure/BridgeAxiomReplacements.lean

  Provides exact signature-matching replacements for bridge component axioms.

  AXIOMS REPLACED:
  - G04: bridge_path_decomposition (BridgeComponentTheory.lean:171)
  - G05: non_v_component_path_avoids_bridge (BridgeComponentTheory.lean:177)
  - G06: bridge_component_cardinality (BridgeComponentTheory.lean:183)

  APPROACH:
  The theorems in PathDecompositionComplete.lean and ExtendedGraphInfra.lean
  prove these with the exact same signatures. This file provides the bridge.

  SORRIES: 0
  AXIOMS: 0
-/

import Theories.BridgeComponentTheory
import Infrastructure.PathDecompositionComplete
import Infrastructure.ExtendedGraphInfra

namespace Infrastructure.BridgeAxiomReplacements

open BridgeComponentTheory
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## G04: Bridge Path Decomposition

Any G-path from u to v (where {v,w} is a bridge) either:
- Reaches v without crossing the bridge, or
- Reaches w (then we're "on the other side")
-/

/-- G04 REPLACEMENT: Exact signature match for bridge_path_decomposition axiom.

This theorem can directly replace the axiom in BridgeComponentTheory.lean:171.
-/
theorem bridge_path_decomposition_replacement [DecidableRel (G : SimpleGraph V).Adj]
    (G : SimpleGraph V) (v w : V) (hb : IsBridge' G v w)
    (u : V) (hr : G.Reachable u v) :
    (G.deleteEdges {s(v, w)}).Reachable u v ∨ (G.deleteEdges {s(v, w)}).Reachable u w :=
  PathDecompositionComplete.bridge_path_decomposition_proven G v w hb u hr

/-! ## G05: Non-v Component Path Avoids Bridge

If u is not in v's G-component, then G-paths to u don't need the bridge.
-/

/-- G05 REPLACEMENT: Exact signature match for non_v_component_path_avoids_bridge axiom.

This theorem can directly replace the axiom in BridgeComponentTheory.lean:177.
-/
theorem non_v_component_path_avoids_bridge_replacement [DecidableRel (G : SimpleGraph V).Adj]
    (G : SimpleGraph V) (v w : V) (hb : IsBridge' G v w)
    (u : V) (hu : G.connectedComponentMk u ≠ G.connectedComponentMk v)
    (u' : V) (hu' : G.Reachable u' u) (hn : ¬(G.deleteEdges {s(v, w)}).Reachable u' u) : False :=
  PathDecompositionComplete.non_v_component_path_avoids_bridge_proven G v w hb u hu u' hu' hn

/-! ## G06: Bridge Component Cardinality

Removing a bridge increases the component count by exactly 1.
-/

/-- G06 REPLACEMENT: Exact signature match for bridge_component_cardinality axiom.

This theorem can directly replace the axiom in BridgeComponentTheory.lean:183.
-/
theorem bridge_component_cardinality_replacement [DecidableRel (G : SimpleGraph V).Adj]
    (G : SimpleGraph V) (v w : V) (hb : IsBridge' G v w)
    (h_fiber_vw : ∀ c : (G.deleteEdges {s(v, w)}).ConnectedComponent,
        componentMap (deleteEdges_le G {s(v, w)}) c = G.connectedComponentMk v →
        c = (G.deleteEdges {s(v, w)}).connectedComponentMk v ∨
        c = (G.deleteEdges {s(v, w)}).connectedComponentMk w)
    (h_fiber_other : ∀ c : G.ConnectedComponent,
        c ≠ G.connectedComponentMk v →
        ∃! c' : (G.deleteEdges {s(v, w)}).ConnectedComponent,
          componentMap (deleteEdges_le G {s(v, w)}) c' = c)
    (hsurj : Function.Surjective (componentMap (deleteEdges_le G {s(v, w)})))
    (hdiff : (G.deleteEdges {s(v, w)}).connectedComponentMk v ≠
             (G.deleteEdges {s(v, w)}).connectedComponentMk w)
    (hsame : componentMap (deleteEdges_le G {s(v, w)})
               ((G.deleteEdges {s(v, w)}).connectedComponentMk v) =
             componentMap (deleteEdges_le G {s(v, w)})
               ((G.deleteEdges {s(v, w)}).connectedComponentMk w)) :
    Fintype.card (G.deleteEdges {s(v, w)}).ConnectedComponent = Fintype.card G.ConnectedComponent + 1 :=
  ExtendedGraphInfra.bridge_component_cardinality_proven G v w hb h_fiber_vw h_fiber_other hsurj hdiff hsame

/-! ## Verification -/

#check @bridge_path_decomposition_replacement
#check @non_v_component_path_avoids_bridge_replacement
#check @bridge_component_cardinality_replacement

/-! ## Usage Instructions

To eliminate axioms G04, G05, G06 from BridgeComponentTheory.lean:

### G04 (line 171):
Replace:
```
axiom bridge_path_decomposition (G : SimpleGraph V) (v w : V) (hb : IsBridge' G v w)
    (u : V) (hr : G.Reachable u v) :
    (G.deleteEdges {s(v, w)}).Reachable u v ∨ (G.deleteEdges {s(v, w)}).Reachable u w
```

With:
```
theorem bridge_path_decomposition [DecidableRel G.Adj] (G : SimpleGraph V) (v w : V) (hb : IsBridge' G v w)
    (u : V) (hr : G.Reachable u v) :
    (G.deleteEdges {s(v, w)}).Reachable u v ∨ (G.deleteEdges {s(v, w)}).Reachable u w :=
  Infrastructure.BridgeAxiomReplacements.bridge_path_decomposition_replacement G v w hb u hr
```

### G05 (line 177):
Replace:
```
axiom non_v_component_path_avoids_bridge (G : SimpleGraph V) (v w : V) (hb : IsBridge' G v w)
    (u : V) (hu : G.connectedComponentMk u ≠ G.connectedComponentMk v)
    (u' : V) (hu' : G.Reachable u' u) (hn : ¬(G.deleteEdges {s(v, w)}).Reachable u' u) : False
```

With the theorem version using bridge_path_decomposition_replacement.

### G06 (line 183):
Similar replacement using bridge_component_cardinality_replacement.

Note: The replacements require [DecidableRel G.Adj] instance, which may need to be added
to the file or specific theorem contexts.
-/

end Infrastructure.BridgeAxiomReplacements
