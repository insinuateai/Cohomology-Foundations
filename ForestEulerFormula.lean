/-
Copyright (c) 2025 COBOUND. All rights reserved.
Released under Apache 2.0 license.
Authors: COBOUND

# Forest Euler Formula

This file proves the fundamental relationship between edges, vertices, and
connected components in graphs, with special characterization for forests.

## Main Theorems

1. `edges_plus_components_ge_vertices`: For any finite graph, |E| + c ≥ |V|
2. `acyclic_euler_eq`: For any forest (acyclic graph), |E| + c = |V|
3. `euler_eq_implies_acyclic`: If |E| + c = |V|, then the graph is acyclic

Together these establish: **G is acyclic ⟺ |E| + c = |V|**

This is a fundamental result connecting graph topology (cycles) to
combinatorics (counting formula).
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Helper Lemmas -/

section Helpers

/-- A graph has a cycle if and only if it is not acyclic -/
theorem has_cycle_iff_not_acyclic (G : SimpleGraph V) :
    (∃ v : V, ∃ p : G.Walk v v, p.IsCycle) ↔ ¬G.IsAcyclic := by
  constructor
  · intro ⟨v, p, hp⟩ h_acyc
    exact h_acyc p hp
  · intro h_not_acyc
    rw [IsAcyclic] at h_not_acyc
    push_neg at h_not_acyc
    exact h_not_acyc

/-- If a graph has a cycle, then it has at least one non-bridge edge -/
theorem cycle_implies_nonbridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_cycle : ∃ v : V, ∃ p : G.Walk v v, p.IsCycle) :
    ∃ e, e ∈ G.edgeSet ∧ ¬G.IsBridge e := by
  by_contra h_all_bridge
  push_neg at h_all_bridge
  have h_acyc : G.IsAcyclic := isAcyclic_iff_forall_edge_isBridge.mpr h_all_bridge
  obtain ⟨v, p, hp⟩ := h_cycle
  exact h_acyc p hp

/-- Helper: In a graph with no edges, each vertex is its own component -/
private theorem components_eq_vertices_of_no_edges
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent]
    (h_empty : G.edgeSet = ∅) :
    Fintype.card G.ConnectedComponent = Fintype.card V := by
  apply Fintype.card_eq.mpr
  refine ⟨⟨fun c => c.exists_rep.choose, G.connectedComponentMk, ?_, ?_⟩⟩
  · intro c; exact c.exists_rep.choose_spec
  · intro v
    have h := (G.connectedComponentMk v).exists_rep.choose_spec
    have h_reach : G.Reachable (G.connectedComponentMk v).exists_rep.choose v :=
      ConnectedComponent.eq.mp h
    obtain ⟨p⟩ := h_reach
    cases hp : p.length with
    | zero => exact Walk.eq_of_length_eq_zero hp
    | succ m =>
      exfalso
      have hadj : G.Adj (p.getVert 0) (p.getVert 1) := p.adj_getVert_succ (by omega)
      have h_in_edge : s(p.getVert 0, p.getVert 1) ∈ G.edgeSet := mem_edgeSet.mpr hadj
      rw [h_empty] at h_in_edge
      exact h_in_edge

/-- Helper: Edge set is empty iff edgeFinset has card 0 -/
private theorem edgeSet_empty_of_card_zero
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (h : G.edgeFinset.card = 0) : G.edgeSet = ∅ := by
  have h1 : Fintype.card G.edgeSet = 0 := by rw [← edgeFinset_card]; exact h
  have hempty : IsEmpty G.edgeSet := Fintype.card_eq_zero_iff.mp h1
  exact @Set.eq_empty_of_isEmpty _ G.edgeSet hempty

end Helpers

/-! ## Main Theorems -/

section MainTheorems

/--
**Theorem 1: Edge-Component Inequality**

For any finite simple graph G: |E| + c ≥ |V|

**Proof:** Strong induction on edges. Base: 0 edges means c = |V|.
Step: Delete an edge. Components can only increase or stay same.
-/
theorem edges_plus_components_ge_vertices
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent] [Nonempty V] :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent ≥ Fintype.card V := by
  -- Strong induction on number of edges
  induction hn : G.edgeFinset.card using Nat.strong_induction_on generalizing G with
  | ind n ih =>
    by_cases h_zero : n = 0
    · -- Base case: no edges
      subst h_zero
      have h_empty := edgeSet_empty_of_card_zero G hn
      have h_eq := components_eq_vertices_of_no_edges G h_empty
      rw [h_eq, hn]
      omega
    · -- Inductive step: at least one edge
      have h_pos : 0 < n := Nat.pos_of_ne_zero h_zero
      have h_edge_pos : 0 < G.edgeFinset.card := by omega
      have h_nonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp h_edge_pos
      obtain ⟨e, he⟩ := h_nonempty
      have he_set : e ∈ G.edgeSet := by simp only [edgeFinset, Set.mem_toFinset] at he; exact he
      -- Delete the edge
      let G' := G.deleteEdges {e}
      haveI : DecidableRel G'.Adj := by
        intro a b; simp only [deleteEdges]; exact And.decidable
      haveI : Fintype G'.edgeSet := by
        apply Set.fintypeSubset G.edgeSet
        intro x hx; simp [deleteEdges_edgeSet] at hx; exact hx.1
      haveI : Fintype G'.ConnectedComponent := ConnectedComponent.fintype G'
      -- G' has fewer edges
      have h_card' : G'.edgeFinset.card < G.edgeFinset.card := by
        have hsub : G'.edgeFinset ⊆ G.edgeFinset := by
          intro x hx
          simp only [edgeFinset, Set.mem_toFinset] at hx ⊢
          simp [deleteEdges_edgeSet] at hx
          exact hx.1
        have hne : G'.edgeFinset ≠ G.edgeFinset := by
          intro heq
          have : e ∈ G'.edgeFinset := by rw [heq]; exact he
          simp only [edgeFinset, Set.mem_toFinset] at this
          simp [deleteEdges_edgeSet] at this
        exact Finset.card_lt_card (Finset.ssubset_of_subset_of_ne hsub hne)
      -- Component count can only increase
      have h_comp_le : Fintype.card G.ConnectedComponent ≤ Fintype.card G'.ConnectedComponent := by
        apply Fintype.card_le_of_surjective (fun c => G'.connectedComponentMk c.exists_rep.choose)
        intro c'
        obtain ⟨w, hw⟩ := c'.exists_rep
        use G.connectedComponentMk w
        simp only
        have h1 := (G.connectedComponentMk w).exists_rep.choose_spec
        have h2 : G'.Reachable (G.connectedComponentMk w).exists_rep.choose w := by
          have hr : G.Reachable (G.connectedComponentMk w).exists_rep.choose w :=
            ConnectedComponent.eq.mp h1
          rw [← hw]; exact Reachable.refl w
        exact ConnectedComponent.eq.mpr h2
      -- Apply IH
      have h_ih := ih G'.edgeFinset.card (by omega) G' rfl
      -- Combine
      omega

/--
**Theorem 2: Forest Euler Formula**

For any forest (acyclic graph): |E| + c = |V|

**Proof:** We have ≥ from theorem 1. For ≤, use that every edge in
a forest is a bridge, so removing any edge increases component count by 1.
-/
theorem acyclic_euler_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent] [Nonempty V]
    (h_acyc : G.IsAcyclic) :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent = Fintype.card V := by
  have h_ge := edges_plus_components_ge_vertices G
  suffices h_le : G.edgeFinset.card + Fintype.card G.ConnectedComponent ≤ Fintype.card V by omega
  -- Strong induction on number of edges
  induction hn : G.edgeFinset.card using Nat.strong_induction_on generalizing G with
  | ind n ih =>
    by_cases h_zero : n = 0
    · -- Base case
      subst h_zero
      have h_empty := edgeSet_empty_of_card_zero G hn
      have h_eq := components_eq_vertices_of_no_edges G h_empty
      rw [h_eq, hn]
    · -- Inductive step
      have h_pos : 0 < n := Nat.pos_of_ne_zero h_zero
      have h_edge_pos : 0 < G.edgeFinset.card := by omega
      have h_nonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp h_edge_pos
      obtain ⟨e, he⟩ := h_nonempty
      have he_set : e ∈ G.edgeSet := by simp only [edgeFinset, Set.mem_toFinset] at he; exact he
      -- Every edge is a bridge in an acyclic graph
      have h_bridge : G.IsBridge e := isAcyclic_iff_forall_edge_isBridge.mp h_acyc e he_set
      -- Get endpoints
      obtain ⟨u, v, huv⟩ := Sym2.exists_eq_mk e
      have hadj : G.Adj u v := by rw [← huv] at he_set; exact mem_edgeSet.mp he_set
      -- Delete the edge
      let G' := G.deleteEdges {e}
      haveI : DecidableRel G'.Adj := by
        intro a b; simp only [deleteEdges]; exact And.decidable
      haveI : Fintype G'.edgeSet := by
        apply Set.fintypeSubset G.edgeSet
        intro x hx; simp [deleteEdges_edgeSet] at hx; exact hx.1
      haveI : Fintype G'.ConnectedComponent := ConnectedComponent.fintype G'
      -- G' is still acyclic
      have h_acyc' : G'.IsAcyclic := by
        intro p hp
        have h_cycle_G : (p.map (Hom.ofLE deleteEdges_le)).IsCycle := by
          constructor
          · simp [Walk.length_map]
            have := hp.three_le_length
            omega
          · have := hp.support_nodup
            simp only [Walk.support_map] at this ⊢
            exact List.Nodup.map (Hom.ofLE deleteEdges_le).injective this
        exact h_acyc _ h_cycle_G
      -- G' has one fewer edge
      have h_card' : G'.edgeFinset.card = n - 1 := by
        have h1 : G'.edgeFinset = G.edgeFinset.erase e := by
          ext x
          simp only [edgeFinset, Set.mem_toFinset, Finset.mem_erase]
          simp [deleteEdges_edgeSet]
          constructor
          · intro ⟨hx, hne⟩; exact ⟨hne, hx⟩
          · intro ⟨hne, hx⟩; exact ⟨hx, hne⟩
        rw [h1, Finset.card_erase_of_mem he, hn]
      -- Bridge removal increases component count by 1
      have h_comp_increase : Fintype.card G.ConnectedComponent + 1 ≤
          Fintype.card G'.ConnectedComponent := by
        rw [huv] at h_bridge
        have h_not_reach : ¬G'.Reachable u v := by
          rw [isBridge_iff] at h_bridge
          rw [huv] at h_bridge
          exact h_bridge.2
        have h_same_G : G.connectedComponentMk u = G.connectedComponentMk v := by
          exact ConnectedComponent.eq.mpr (Adj.reachable hadj)
        have h_diff_G' : G'.connectedComponentMk u ≠ G'.connectedComponentMk v := by
          intro heq; exact h_not_reach (ConnectedComponent.eq.mp heq)
        -- Map from G'-components to G-components
        let f : G'.ConnectedComponent → G.ConnectedComponent :=
          fun c' => G.connectedComponentMk c'.exists_rep.choose
        have hf_surj : Function.Surjective f := by
          intro c
          obtain ⟨w, hw⟩ := c.exists_rep
          use G'.connectedComponentMk w
          simp only [f]
          have h1 := (G'.connectedComponentMk w).exists_rep.choose_spec
          have h2 : G'.Reachable (G'.connectedComponentMk w).exists_rep.choose w :=
            ConnectedComponent.eq.mp h1
          have h3 : G.Reachable (G'.connectedComponentMk w).exists_rep.choose w :=
            Reachable.mono deleteEdges_le h2
          rw [← hw]
          exact ConnectedComponent.eq.mpr h3
        -- f maps u and v to the same G-component but they're different in G'
        have h_two_preimages : f (G'.connectedComponentMk u) = f (G'.connectedComponentMk v) := by
          simp only [f]
          have h1 := (G'.connectedComponentMk u).exists_rep.choose_spec
          have h2 := (G'.connectedComponentMk v).exists_rep.choose_spec
          have h3 : G.Reachable (G'.connectedComponentMk u).exists_rep.choose u :=
            Reachable.mono deleteEdges_le (ConnectedComponent.eq.mp h1)
          have h4 : G.Reachable (G'.connectedComponentMk v).exists_rep.choose v :=
            Reachable.mono deleteEdges_le (ConnectedComponent.eq.mp h2)
          have h5 : G.connectedComponentMk (G'.connectedComponentMk u).exists_rep.choose =
              G.connectedComponentMk u := ConnectedComponent.eq.mpr h3
          have h6 : G.connectedComponentMk (G'.connectedComponentMk v).exists_rep.choose =
              G.connectedComponentMk v := ConnectedComponent.eq.mpr h4
          rw [h5, h6, h_same_G]
        -- Strict inequality
        have h_strict : Fintype.card G.ConnectedComponent < Fintype.card G'.ConnectedComponent := by
          by_contra h_not_lt
          push_neg at h_not_lt
          have h_card_ge : Fintype.card G.ConnectedComponent ≤
              Fintype.card G'.ConnectedComponent :=
            Fintype.card_le_of_surjective f hf_surj
          have h_card_eq : Fintype.card G'.ConnectedComponent =
              Fintype.card G.ConnectedComponent := by omega
          have h_inj : Function.Injective f := by
            have h_equiv := Fintype.bijective_iff_surjective_and_card f
            rw [h_card_eq] at h_equiv
            exact (h_equiv.mpr ⟨hf_surj, rfl⟩).1
          exact h_diff_G' (h_inj h_two_preimages)
        omega
      -- Apply IH
      have h_ih := ih (n - 1) (by omega) G' h_acyc' h_card'
      omega

/--
**Theorem 3: Converse of Forest Euler Formula**

If |E| + c = |V|, then the graph is acyclic.

**Proof:** Contrapositive. If G has a cycle, it has a non-bridge edge.
Removing it doesn't increase components but decreases edges, giving
|E| + c > |V|.
-/
theorem euler_eq_implies_acyclic
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent] [Nonempty V]
    (h_euler : G.edgeFinset.card + Fintype.card G.ConnectedComponent = Fintype.card V) :
    G.IsAcyclic := by
  by_contra h_not_acyc
  have h_cycle := (has_cycle_iff_not_acyclic G).mpr h_not_acyc
  obtain ⟨e, he_set, h_not_bridge⟩ := cycle_implies_nonbridge G h_cycle
  obtain ⟨u, v, huv⟩ := Sym2.exists_eq_mk e
  have hadj : G.Adj u v := by rw [← huv] at he_set; exact mem_edgeSet.mp he_set
  -- e is not a bridge
  rw [huv] at h_not_bridge
  rw [isBridge_iff] at h_not_bridge
  push_neg at h_not_bridge
  rw [huv] at he_set
  have h_still_reach : (G.deleteEdges {s(u, v)}).Reachable u v := h_not_bridge he_set
  -- Delete the edge
  let G' := G.deleteEdges {e}
  haveI : DecidableRel G'.Adj := by
    intro a b; simp only [deleteEdges]; exact And.decidable
  haveI : Fintype G'.edgeSet := by
    apply Set.fintypeSubset G.edgeSet
    intro x hx; simp [deleteEdges_edgeSet] at hx; exact hx.1
  haveI : Fintype G'.ConnectedComponent := ConnectedComponent.fintype G'
  -- G' has one fewer edge
  have h_fewer_edge : G'.edgeFinset.card = G.edgeFinset.card - 1 := by
    have he : e ∈ G.edgeFinset := by simp only [edgeFinset, Set.mem_toFinset, huv]; exact he_set
    have h1 : G'.edgeFinset = G.edgeFinset.erase e := by
      ext x
      simp only [edgeFinset, Set.mem_toFinset, Finset.mem_erase]
      simp [deleteEdges_edgeSet]
      constructor
      · intro ⟨hx, hne⟩; exact ⟨hne, hx⟩
      · intro ⟨hne, hx⟩; exact ⟨hx, hne⟩
    rw [h1, Finset.card_erase_of_mem he]
  -- Components stay the same (non-bridge)
  have h_same_comp : Fintype.card G.ConnectedComponent = Fintype.card G'.ConnectedComponent := by
    apply le_antisymm
    · apply Fintype.card_le_of_surjective (fun c => G'.connectedComponentMk c.exists_rep.choose)
      intro c'
      obtain ⟨w, hw⟩ := c'.exists_rep
      use G.connectedComponentMk w
      simp only
      rw [← hw]; exact ConnectedComponent.eq.mpr (Reachable.refl w)
    · apply Fintype.card_le_of_surjective (fun c' => G.connectedComponentMk c'.exists_rep.choose)
      intro c
      obtain ⟨w, hw⟩ := c.exists_rep
      use G'.connectedComponentMk w
      simp only
      have h1 := (G'.connectedComponentMk w).exists_rep.choose_spec
      have h2 : G'.Reachable (G'.connectedComponentMk w).exists_rep.choose w :=
        ConnectedComponent.eq.mp h1
      have h3 : G.Reachable (G'.connectedComponentMk w).exists_rep.choose w :=
        Reachable.mono deleteEdges_le h2
      rw [← hw]
      exact ConnectedComponent.eq.mpr h3
  -- Apply inequality to G'
  have h_ge := edges_plus_components_ge_vertices G'
  have h_edge_pos : G.edgeFinset.card > 0 := by
    have : e ∈ G.edgeFinset := by simp only [edgeFinset, Set.mem_toFinset, huv]; exact he_set
    exact Finset.card_pos.mpr ⟨e, this⟩
  rw [h_same_comp, h_fewer_edge] at h_ge
  omega

/--
**Corollary: Full Characterization of Forests**

A graph is acyclic if and only if |E| + c = |V|
-/
theorem isAcyclic_iff_euler_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent] [Nonempty V] :
    G.IsAcyclic ↔ G.edgeFinset.card + Fintype.card G.ConnectedComponent = Fintype.card V :=
  ⟨acyclic_euler_eq G, euler_eq_implies_acyclic G⟩

end MainTheorems

end SimpleGraph
