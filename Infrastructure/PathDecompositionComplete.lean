/-
# Path Decomposition Complete

Bridge-based path splitting proofs using ExtendedGraphInfra infrastructure.

## Main Results

1. `bridge_path_decomposition_proven` - Path through bridge splits at bridge (G04)
2. `non_v_component_path_avoids_bridge_proven` - Non-bridge component paths avoid bridge (G05)

## Axioms Eliminated

- G04: bridge_path_decomposition (BridgeComponentTheory.lean:171)
- G05: non_v_component_path_avoids_bridge (BridgeComponentTheory.lean:177)

SORRIES: 0
AXIOMS: 0

Author: Infrastructure Team
Date: February 2026
-/

import Infrastructure.WalkDecomposition
import Infrastructure.ExtendedGraphInfra
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Infrastructure.PathDecompositionComplete

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Section 1: Bridge Path Decomposition (G04)

The key insight is that any path from u to v either:
1. Avoids the bridge edge entirely → stays connected to v in the reduced graph
2. Uses the bridge edge → the prefix reaches w before crossing to v
-/

/-- Alternative bridge definition matching BridgeComponentTheory -/
def IsBridge' (G : SimpleGraph V) (v w : V) : Prop :=
  G.Adj v w ∧ ¬(G.deleteEdges {s(v, w)}).Reachable v w

/-- THEOREM G04: Path decomposition through a bridge.

    If u is reachable from v in G, then after removing bridge {v,w},
    u is reachable from either v or w.

    Proof: Take any G-path from u to v.
    - If it doesn't use edge {v,w}: the path works in G' = G \ {v,w}, so u ~G'~ v
    - If it uses edge {v,w}: the prefix before the edge reaches w (or v),
      and that prefix works in G' since it doesn't include the removed edge after
      the first crossing.

    The key lemma `vertex_in_v_or_w_component` from ExtendedGraphInfra.lean
    proves exactly this: every vertex in v's G-component is in either v's or w's
    G'-component after edge removal.
-/
theorem bridge_path_decomposition_proven (G : SimpleGraph V) [DecidableRel G.Adj]
    (v w : V) (hb : IsBridge' G v w) (u : V) (hr : G.Reachable u v) :
    (G.deleteEdges {s(v, w)}).Reachable u v ∨
    (G.deleteEdges {s(v, w)}).Reachable u w := by
  -- Use ExtendedGraphInfra.vertex_in_v_or_w_component
  -- which shows: every vertex in v's G-component is in v's or w's G'-component
  have hu_comp : G.connectedComponentMk u = G.connectedComponentMk v :=
    ConnectedComponent.eq.mpr hr
  -- Apply the key lemma from ExtendedGraphInfra
  have key := ExtendedGraphInfra.vertex_in_v_or_w_component G s(v,w) v w rfl hb.1 u hu_comp
  -- key : G'.connectedComponentMk u = G'.connectedComponentMk v ∨
  --       G'.connectedComponentMk u = G'.connectedComponentMk w
  cases key with
  | inl hv =>
    left
    exact ConnectedComponent.eq.mp hv
  | inr hw =>
    right
    exact ConnectedComponent.eq.mp hw

/-! ## Section 2: Non-v Component Path Avoidance (G05)

If u is not in v's G-component, then any G-path from u' to u
doesn't need to use the bridge {v,w}.
-/

/-- THEOREM G05: Paths outside v's component don't need the bridge.

    If u is not in v's G-component, then u' reaching u in G
    implies u' reaches u in G' = G \ {v,w}.

    Proof by contradiction: if u' can't reach u in G', the G-path must use {v,w}.
    But {v,w} only connects v's component to w's component (which equals v's in G).
    Since u ∉ v's G-component, the path can't need to cross through {v,w}.
-/
theorem non_v_component_path_avoids_bridge_proven (G : SimpleGraph V) [DecidableRel G.Adj]
    (v w : V) (hb : IsBridge' G v w)
    (u : V) (hu : G.connectedComponentMk u ≠ G.connectedComponentMk v)
    (u' : V) (hu' : G.Reachable u' u)
    (hn : ¬(G.deleteEdges {s(v, w)}).Reachable u' u) : False := by
  -- u' and u are in the same G-component
  have hu'_comp : G.connectedComponentMk u' = G.connectedComponentMk u :=
    ConnectedComponent.eq.mpr hu'
  -- So u' is also not in v's G-component
  have hu'_not_v : G.connectedComponentMk u' ≠ G.connectedComponentMk v := by
    rwa [hu'_comp]
  -- The bridge only affects v's G-component
  -- Vertices outside v's component have the same reachability in G and G'
  -- Get a G-path from u' to u
  obtain ⟨p⟩ := hu'
  -- Check if the path uses the bridge edge
  by_cases h_uses : s(v, w) ∈ p.edges
  · -- Path uses bridge: then u' reaches v or w, contradiction with hu'_not_v
    have hv_support := Walk.fst_mem_support_of_mem_edges p h_uses
    have hw_support := Walk.snd_mem_support_of_mem_edges p h_uses
    -- u' is in same component as some vertex on the path
    -- The path goes u' → ... → v/w → ... → u
    -- This means u' is in v's component (since v,w are adjacent)
    have hv_comp : G.connectedComponentMk v = G.connectedComponentMk w :=
      ConnectedComponent.eq.mpr hb.1.reachable
    -- Take prefix of path to v (first occurrence)
    let p_to_v := p.takeUntil v hv_support
    have hu'_reach_v : G.Reachable u' v := ⟨p_to_v⟩
    have hu'_in_v_comp : G.connectedComponentMk u' = G.connectedComponentMk v :=
      ConnectedComponent.eq.mpr hu'_reach_v
    exact hu'_not_v hu'_in_v_comp
  · -- Path doesn't use bridge: can transfer to G'
    have h_in_G' : ∀ e ∈ p.edges, e ∈ (G.deleteEdges {s(v, w)}).edgeSet := by
      intro e he
      simp only [edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · exact Walk.edges_subset_edgeSet p he
      · intro heq
        rw [heq] at he
        exact h_uses he
    -- Transfer the walk to G'
    have hr' : (G.deleteEdges {s(v, w)}).Reachable u' u := by
      have p' := p.transfer (G.deleteEdges {s(v, w)}) h_in_G'
      exact ⟨p'⟩
    exact hn hr'

/-! ## Section 3: Summary -/

#check bridge_path_decomposition_proven  -- G04: PROVEN
#check non_v_component_path_avoids_bridge_proven  -- G05: PROVEN

end Infrastructure.PathDecompositionComplete
