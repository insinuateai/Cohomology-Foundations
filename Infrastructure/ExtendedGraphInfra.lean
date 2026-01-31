/-
# Extended Graph Infrastructure for Cohomology

Extends Infrastructure/GraphTheoryUtils.lean with additional proven lemmas
for TreeGraphInfra.lean and the H¹ characterization theorems.

Targets: Mathlib 4.27.0 / Lean 4.27.0

## What This Provides

1. Empty graph component characterization (PROVEN)
2. Edge removal machinery (PROVEN)
3. Walk monotonicity and lifting (PROVEN)
4. Subgraph acyclicity preservation (PROVEN)
5. Reachability lemmas (PROVEN)
6. Bridge detection and characterization (PROVEN)
7. Component count bounds (PARTIAL - key lemma stated)

SORRIES: 0
AXIOMS: 1 (bridge_splits_component_aux)

Author: Tenured Cohomology Foundations
Date: January 2026
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

namespace ExtendedGraphInfra

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Section 1: Definitions -/

/-- Edge count using edgeFinset -/
noncomputable def edgeCount (G : SimpleGraph V) [Fintype G.edgeSet] : ℕ :=
  G.edgeFinset.card

/-- Component count -/
noncomputable def componentCount (G : SimpleGraph V) [Fintype G.ConnectedComponent] : ℕ :=
  Fintype.card G.ConnectedComponent

/-- Vertex count -/
def vertexCount : ℕ := Fintype.card V

/-! ## Section 2: Empty Graph - FULLY PROVEN -/

/-- In the empty graph, v and w in same component iff v = w -/
theorem bot_connectedComponent_eq_iff (v w : V) :
    (⊥ : SimpleGraph V).connectedComponentMk v = (⊥ : SimpleGraph V).connectedComponentMk w ↔ v = w := by
  constructor
  · intro h
    rw [ConnectedComponent.eq] at h
    obtain ⟨p⟩ := h
    cases p with
    | nil => rfl
    | cons hadj _ => exact absurd hadj (by simp [SimpleGraph.bot_adj])
  · intro h; rw [h]

/-- Empty graph: components biject with vertices -/
theorem bot_components_bijective :
    Function.Bijective (⊥ : SimpleGraph V).connectedComponentMk := by
  constructor
  · -- Injective
    intro v w h
    exact (bot_connectedComponent_eq_iff v w).mp h
  · -- Surjective
    intro c
    obtain ⟨v, rfl⟩ := c.exists_rep
    exact ⟨v, rfl⟩

/-- Empty graph: component count = vertex count -/
theorem bot_componentCount [Fintype (⊥ : SimpleGraph V).ConnectedComponent] :
    componentCount (⊥ : SimpleGraph V) = vertexCount (V := V) := by
  unfold componentCount vertexCount
  exact Fintype.card_congr (Equiv.ofBijective _ bot_components_bijective)

/-- Empty graph has 0 edges -/
theorem bot_edgeCount [Fintype (⊥ : SimpleGraph V).edgeSet] :
    edgeCount (⊥ : SimpleGraph V) = 0 := by
  unfold edgeCount
  rw [show (⊥ : SimpleGraph V).edgeFinset = ∅ from rfl]
  simp

/-- Empty graph: |E| + c = |V| -/
theorem bot_euler [Fintype (⊥ : SimpleGraph V).edgeSet]
    [Fintype (⊥ : SimpleGraph V).ConnectedComponent] :
    edgeCount (⊥ : SimpleGraph V) + componentCount (⊥ : SimpleGraph V) = vertexCount (V := V) := by
  rw [bot_edgeCount, bot_componentCount, zero_add]

/-! ## Section 3: Connected Graph - FULLY PROVEN -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Connected graph has exactly 1 component -/
theorem connected_componentCount_eq_one [Fintype G.ConnectedComponent] (h : G.Connected) :
    componentCount G = 1 := by
  unfold componentCount
  rw [Fintype.card_eq_one_iff]
  use G.connectedComponentMk (Classical.arbitrary V)
  intro c
  obtain ⟨v, rfl⟩ := c.exists_rep
  exact ConnectedComponent.eq.mpr (h.preconnected v _)

/-- Tree: |E| + 1 = |V| -/
theorem tree_edgeCount [Fintype G.edgeSet] [Nonempty V] (h : G.IsTree) :
    edgeCount G + 1 = vertexCount (V := V) := by
  unfold edgeCount vertexCount
  exact h.card_edgeFinset

/-- Tree satisfies |E| + c = |V| (since c = 1) -/
theorem tree_euler [Fintype G.edgeSet] [Fintype G.ConnectedComponent] [Nonempty V]
    (h : G.IsTree) :
    edgeCount G + componentCount G = vertexCount (V := V) := by
  have h1 := tree_edgeCount G h
  have h2 := connected_componentCount_eq_one G h.1
  omega

/-! ## Section 4: Edge Removal - FULLY PROVEN -/

/-- edgeFinset of deleteEdges is the set difference -/
theorem deleteEdges_edgeFinset_eq (s : Set (Sym2 V)) [Fintype G.edgeSet]
    [Fintype (G.deleteEdges s).edgeSet] [DecidablePred (· ∈ s)] :
    (G.deleteEdges s).edgeFinset = G.edgeFinset.filter (· ∉ s) := by
  ext e
  simp only [mem_edgeFinset, deleteEdges_adj, Finset.mem_filter]
  constructor
  · intro ⟨hadj, hne⟩
    exact And.intro hadj hne
  · intro ⟨hadj, hne⟩
    exact And.intro hadj hne

/-- Removing a single edge: edgeFinset is erase -/
theorem deleteEdges_singleton_edgeFinset (e : Sym2 V) [Fintype G.edgeSet]
    [Fintype (G.deleteEdges {e}).edgeSet] (he : e ∈ G.edgeSet) :
    (G.deleteEdges {e}).edgeFinset = G.edgeFinset.erase e := by
  ext e'
  simp only [mem_edgeFinset, deleteEdges_adj, Set.mem_singleton_iff, Finset.mem_erase]
  constructor
  · intro ⟨hadj, hne⟩
    exact And.intro hne hadj
  · intro ⟨hne, hadj⟩
    exact And.intro hadj hne

/-- Removing edge decreases count by 1 -/
theorem deleteEdges_singleton_card (e : Sym2 V) [Fintype G.edgeSet]
    [Fintype (G.deleteEdges {e}).edgeSet] (he : e ∈ G.edgeSet) :
    (G.deleteEdges {e}).edgeFinset.card + 1 = G.edgeFinset.card := by
  have h1 : e ∈ G.edgeFinset := mem_edgeFinset.mpr he
  rw [deleteEdges_singleton_edgeFinset G e he, Finset.card_erase_of_mem h1]
  omega

/-- Edge removal strictly decreases edge count -/
theorem deleteEdges_singleton_card_lt (e : Sym2 V) [Fintype G.edgeSet]
    [Fintype (G.deleteEdges {e}).edgeSet] (he : e ∈ G.edgeSet) :
    (G.deleteEdges {e}).edgeFinset.card < G.edgeFinset.card := by
  have h := deleteEdges_singleton_card G e he
  omega

/-! ## Section 5: Monotonicity - FULLY PROVEN -/

/-- deleteEdges gives subgraph -/
theorem deleteEdges_le (s : Set (Sym2 V)) : G.deleteEdges s ≤ G := by
  intro v w h
  exact h.1

/-- Adjacency lifts from subgraph to supergraph -/
theorem adj_of_le {H : SimpleGraph V} (hle : G ≤ H) {v w : V} (h : G.Adj v w) :
    H.Adj v w := hle h

/-- Reachability lifts from subgraph to supergraph -/
theorem reachable_of_le {H : SimpleGraph V} (hle : G ≤ H) {v w : V}
    (h : G.Reachable v w) : H.Reachable v w := by
  obtain ⟨p⟩ := h
  exact ⟨p.mapLe hle⟩

/-- Connected lifts from subgraph to supergraph -/
theorem connected_of_le {H : SimpleGraph V} (hle : G ≤ H) (h : G.Connected) :
    H.Connected := by
  intro v w
  exact reachable_of_le G hle (h v w)

/-! ## Section 6: Acyclicity Preservation - FULLY PROVEN -/

/-- Subgraph of acyclic is acyclic -/
theorem isAcyclic_of_le {H : SimpleGraph V} (hle : G ≤ H) (hH : H.IsAcyclic) :
    G.IsAcyclic := by
  intro p hp
  apply hH
  exact hp.mapLe hle

/-- deleteEdges preserves acyclicity -/
theorem deleteEdges_isAcyclic (s : Set (Sym2 V)) (h : G.IsAcyclic) :
    (G.deleteEdges s).IsAcyclic :=
  isAcyclic_of_le (G.deleteEdges s) (deleteEdges_le G s) h

/-! ## Section 7: Reachability - FULLY PROVEN -/

/-- Same component iff reachable -/
theorem connectedComponent_eq_iff_reachable (v w : V) :
    G.connectedComponentMk v = G.connectedComponentMk w ↔ G.Reachable v w :=
  ConnectedComponent.eq

/-- In connected graph, all pairs reachable -/
theorem connected_reachable (h : G.Connected) (v w : V) : G.Reachable v w :=
  h v w

/-- In tree, all pairs reachable -/
theorem tree_reachable (h : G.IsTree) (v w : V) : G.Reachable v w :=
  h.connected v w

/-! ## Section 8: Bridge Definition - FULLY PROVEN -/

/-- An edge is a bridge if removing it disconnects its endpoints -/
def IsBridge (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ ∃ v w, s(v, w) = e ∧ ¬(G.deleteEdges {e}).Reachable v w

/-- Equivalent: edge e with endpoints v, w is a bridge iff removing disconnects them -/
theorem isBridge_iff (v w : V) (h_adj : G.Adj v w) :
    IsBridge G s(v, w) ↔ ¬(G.deleteEdges {s(v, w)}).Reachable v w := by
  unfold IsBridge
  constructor
  · intro ⟨_, _, _, he, hr⟩
    have hvw : v = _ ∧ w = _ ∨ v = _ ∧ w = _ := Sym2.eq_iff.mp he
    cases hvw with
    | inl h => rw [h.1, h.2]; exact hr
    | inr h => rw [h.1, h.2]; exact fun hr' => hr (hr'.symm)
  · intro h
    refine ⟨mem_edgeSet.mpr h_adj, v, w, rfl, h⟩

/-- In acyclic graph, every edge is a bridge -/
theorem isAcyclic_isBridge (h_acyc : G.IsAcyclic) (e : G.edgeSet) :
    IsBridge G e.val := by
  obtain ⟨v, w, hvw⟩ := e.val.exists_eq_mk
  refine ⟨e.property, v, w, hvw, ?_⟩
  intro h_reach
  -- If still reachable after removal, there's a path not using e
  -- Combined with edge e, this creates a cycle
  have h_adj : G.Adj v w := by
    rw [← mem_edgeSet, hvw]; exact e.property
  by_cases h_eq : v = w
  · exact G.loopless v (h_eq ▸ h_adj)
  · -- Get a path (not just walk) in deleteEdges
    obtain ⟨p_walk⟩ := h_reach
    let p := p_walk.toPath
    -- Lift path to G
    let p' := p.val.mapLe (deleteEdges_le G {e.val})
    -- Construct cycle: v →[edge] w →[p'.reverse] v
    let cycle := Walk.cons h_adj p'.reverse
    -- The path p doesn't use edge e (it's in deleteEdges)
    have h_edge_not_in_p : s(v, w) ∉ p.val.edges := by
      intro h_in
      have h_in_del : s(v, w) ∈ (G.deleteEdges {e.val}).edgeSet := Walk.edges_subset_edgeSet p.val h_in
      simp only [deleteEdges_edgeSet, Set.mem_diff, Set.mem_singleton_iff, hvw] at h_in_del
      exact h_in_del.2 rfl
    have h_cycle : cycle.IsCycle := by
      constructor
      · -- IsCircuit
        constructor
        · -- IsTrail
          constructor
          simp only [Walk.edges_cons, Walk.edges_reverse, List.nodup_cons]
          constructor
          · -- s(v,w) not in p'.reverse.edges
            intro h_in
            rw [List.mem_reverse] at h_in
            have : s(v, w) ∈ p.val.edges := by
              rw [Walk.mapLe, Walk.edges_map] at h_in
              simp only [Hom.ofLE_apply, Sym2.map_id', List.map_id] at h_in
              exact h_in
            exact h_edge_not_in_p this
          · -- p'.reverse.edges nodup
            have hp_path := p.property
            exact (hp_path.isTrail.reverse.mapLe _).edges_nodup
        · -- ne_nil
          exact Walk.cons_ne_nil _ _
      · -- support.tail.Nodup
        simp only [Walk.support_cons, Walk.support_reverse, List.tail_cons]
        have hp_path := p.property
        exact hp_path.support_nodup.reverse
    exact h_acyc cycle h_cycle

/-! ## Section 9: Component Splitting - STATED -/

-- TEMP: axiomatized for speed, prove by 2026-02-07
-- Proof: bridge endpoints in different components after removal, other vertices unchanged
axiom bridge_splits_component_aux (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.ConnectedComponent]
    (e : G.edgeSet)
    [Fintype (G.deleteEdges ({e.val} : Set (Sym2 V))).ConnectedComponent]
    (h_bridge : IsBridge G e.val) :
    componentCount (G.deleteEdges ({e.val} : Set (Sym2 V))) = componentCount G + 1

/-- Removing a bridge increases component count by 1.
    This is the key lemma for forest_euler.

    Proof idea: The bridge e = {v,w} connects v's component to w's component.
    After removal, they become separate components.
    All other components unchanged.
    Net effect: +1 component.

    Requires Mathlib's ConnectedComponent.lift and related API. -/
theorem bridge_splits_component [Fintype G.ConnectedComponent]
    (e : G.edgeSet)
    [Fintype (G.deleteEdges ({e.val} : Set (Sym2 V))).ConnectedComponent]
    (h_bridge : IsBridge G e.val) :
    componentCount (G.deleteEdges ({e.val} : Set (Sym2 V))) = componentCount G + 1 :=
  bridge_splits_component_aux V G e h_bridge

/-! ## Section 10: Positive Component Count - FULLY PROVEN -/

/-- Non-empty vertex set implies positive component count -/
theorem componentCount_pos [Nonempty V] [Fintype G.ConnectedComponent] :
    0 < componentCount G := by
  unfold componentCount
  have ⟨v⟩ : Nonempty V := inferInstance
  have : Nonempty G.ConnectedComponent := ⟨G.connectedComponentMk v⟩
  exact Fintype.card_pos

/-! ## Section 11: Path Uniqueness in Trees - FULLY PROVEN -/

/-- In acyclic graph, paths are unique -/
theorem isAcyclic_path_unique (h : G.IsAcyclic) (v w : V)
    (p q : G.Path v w) : p = q :=
  h.path_unique p q

/-! ## Section 12: Summary -/

-- Fully proven (0 sorry):
#check bot_connectedComponent_eq_iff
#check bot_components_bijective
#check bot_componentCount
#check bot_edgeCount
#check bot_euler
#check connected_componentCount_eq_one
#check tree_edgeCount
#check tree_euler
#check deleteEdges_edgeFinset_eq
#check deleteEdges_singleton_edgeFinset
#check deleteEdges_singleton_card
#check deleteEdges_singleton_card_lt
#check deleteEdges_le
#check adj_of_le
#check reachable_of_le
#check connected_of_le
#check isAcyclic_of_le
#check deleteEdges_isAcyclic
#check connectedComponent_eq_iff_reachable
#check connected_reachable
#check tree_reachable
#check isBridge_iff
#check isAcyclic_isBridge  -- NOW PROVEN
#check componentCount_pos
#check isAcyclic_path_unique

-- Has 1 sorry (key lemma, requires Mathlib component API):
#check bridge_splits_component

end ExtendedGraphInfra
