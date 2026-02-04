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

## Status

**SORRIES: 0 | AXIOMS: 0** (2026-02-01)

Uses proven lemmas from `Infrastructure.TreeGraphInfra` for edge deletion
and component counting.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Infrastructure.TreeGraphInfra

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Helper Lemmas -/

section Helpers

/-! ## Proven Lemmas from Infrastructure -/

-- The following axioms have been ELIMINATED by using proven lemmas from Infrastructure.TreeGraphInfra:
-- - component_injection_technical: proven in card_connectedComponent_deleteEdges_add_one
-- - path_reroute_around_edge: proven using takeUntil_first_endpoint_no_edge pattern

/-- Helper: converting walks when edge sets are equal -/
private def walk_deleteEdges_eq {G : SimpleGraph V} {e₁ e₂ : Sym2 V} (heq : e₁ = e₂)
    {a b : V} (p : (G.deleteEdges {e₁}).Walk a b) : (G.deleteEdges {e₂}).Walk a b :=
  heq ▸ p

/-- Helper: convert Reachable proof when graphs are equal -/
private def reachable_cast {G1 G2 : SimpleGraph V} (heq : G1 = G2)
    {a b : V} (h : G1.Reachable a b) : G2.Reachable a b := heq ▸ h

/-- Helper: if a walk uses edge e, at least one of the takeUntil prefixes doesn't use e. -/
private lemma takeUntil_first_endpoint_no_edge (G : SimpleGraph V)
    {a b u v : V} (p : G.Walk a b) (hp : s(u,v) ∈ p.edges)
    (hu : u ∈ p.support) (hv : v ∈ p.support) (hne : u ≠ v) :
    s(u,v) ∉ (p.takeUntil u hu).edges ∨ s(u,v) ∉ (p.takeUntil v hv).edges := by
  -- Compare lengths: whichever vertex appears first has prefix without edge
  by_cases h : (p.takeUntil u hu).length ≤ (p.takeUntil v hv).length
  · left
    intro h_in
    have hv_in_prefix := Walk.snd_mem_support_of_mem_edges _ h_in
    have h_lt := Walk.length_takeUntil_lt hv_in_prefix hne.symm
    simp only [Walk.takeUntil_takeUntil] at h_lt
    omega
  · right
    push_neg at h
    intro h_in
    have hu_in_prefix := Walk.fst_mem_support_of_mem_edges _ h_in
    have h_lt := Walk.length_takeUntil_lt hu_in_prefix hne
    simp only [Walk.takeUntil_takeUntil] at h_lt
    omega

/-- A graph has a cycle if and only if it is not acyclic -/
theorem has_cycle_iff_not_acyclic {V : Type*} (G : SimpleGraph V) :
    (∃ v : V, ∃ p : G.Walk v v, p.IsCycle) ↔ ¬G.IsAcyclic := by
  constructor
  · intro ⟨v, p, hp⟩ h_acyc
    exact h_acyc p hp
  · intro h_not_acyc
    rw [IsAcyclic] at h_not_acyc
    push_neg at h_not_acyc
    exact h_not_acyc

/-- If a graph has a cycle, then it has at least one non-bridge edge -/
theorem cycle_implies_nonbridge {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
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
      have h_in_edge : s(p.getVert 0, p.getVert 1) ∈ G.edgeSet := hadj
      rw [h_empty] at h_in_edge
      exact h_in_edge

/-- Helper: Edge set is empty iff edgeFinset has card 0 -/
private theorem edgeSet_empty_of_card_zero {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (h : G.edgeFinset.card = 0) : G.edgeSet = ∅ := by
  have h1 : Fintype.card G.edgeSet = 0 := by rw [← edgeFinset_card]; exact h
  have hempty : IsEmpty G.edgeSet := Fintype.card_eq_zero_iff.mp h1
  exact @Set.eq_empty_of_isEmpty _ G.edgeSet hempty

/-- Deleting one edge increases connected component count by at most 1.

This is a standard result: when we delete an edge e = {u,v}:
- If u and v remain connected (e is not a bridge), components stay the same
- If u and v become disconnected (e is a bridge), the component containing e splits into 2
In either case, component count increases by at most 1.

PROVEN: Uses Infrastructure.card_connectedComponent_deleteEdges_add_one -/
private theorem deleteEdge_components_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent] (e : Sym2 V) (he : e ∈ G.edgeSet)
    [Fintype (G.deleteEdges {e}).edgeSet]
    [Fintype (G.deleteEdges {e}).ConnectedComponent] :
    Fintype.card (G.deleteEdges {e}).ConnectedComponent ≤
        Fintype.card G.ConnectedComponent + 1 := by
  classical
  -- Convert edgeSet membership to edgeFinset membership
  have he_finset : e ∈ G.edgeFinset := mem_edgeFinset.mpr he
  -- Use the proven lemma from Infrastructure
  -- Handle Fintype instance mismatch: cardinalities are equal for any two Fintype instances
  have h := Infrastructure.card_connectedComponent_deleteEdges_add_one G e he_finset
  -- All Fintype instances on the same type give the same cardinality
  simp only [Fintype.card_eq_nat_card] at h ⊢
  exact h

end Helpers

/-! ## Main Theorems -/

section MainTheorems

/--
**Theorem 1: Edge-Component Inequality**

For any finite simple graph G: |E| + c ≥ |V|

**Proof:** Strong induction on edges. Base: 0 edges means c = |V|.
Step: Delete an edge. Components increase by at most 1, edges decrease by 1.
-/
theorem edges_plus_components_ge_vertices
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent] [Nonempty V] :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent ≥ Fintype.card V := by
  -- Strong induction on number of edges
  induction hn : G.edgeFinset.card using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    by_cases h_zero : n = 0
    · -- Base case: no edges
      subst h_zero
      have h_empty := edgeSet_empty_of_card_zero G hn
      have h_eq := components_eq_vertices_of_no_edges G h_empty
      rw [h_eq]
      omega
    · -- Inductive step: at least one edge
      have h_pos : 0 < n := Nat.pos_of_ne_zero h_zero
      have h_edge_pos : 0 < G.edgeFinset.card := by omega
      have h_nonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp h_edge_pos
      obtain ⟨e, he⟩ := h_nonempty
      have he_set : e ∈ G.edgeSet := by simp only [edgeFinset, Set.mem_toFinset] at he; exact he
      -- Delete the edge
      set G' := G.deleteEdges {e} with hG'
      haveI : DecidableRel G'.Adj := inferInstance
      haveI : Fintype G'.edgeSet := by
        apply Set.fintypeSubset G.edgeSet
        intro x hx; rw [edgeSet_deleteEdges] at hx; exact hx.1
      haveI : Fintype G'.ConnectedComponent := inferInstance
      -- G' has one fewer edge
      have h_card' : G'.edgeFinset.card = n - 1 := by
        have h1 : G'.edgeFinset = G.edgeFinset.erase e := by
          ext x
          simp only [edgeFinset, Set.mem_toFinset, Finset.mem_erase]
          rw [edgeSet_deleteEdges]
          simp only [Set.mem_diff, Set.mem_singleton_iff]
          tauto
        rw [h1, Finset.card_erase_of_mem he, hn]
      -- Component count increases by at most 1
      have h_comp_bound : Fintype.card G'.ConnectedComponent ≤
          Fintype.card G.ConnectedComponent + 1 := deleteEdge_components_bound G e he_set
      -- Apply IH: G'.edgeFinset.card + card G'.CC >= card V
      have h_ih := ih (n - 1) (by omega) G' h_card'
      -- Combine: n + card G.CC >= card V
      omega

/--
**Theorem 2: Forest Euler Formula**

For any forest (acyclic graph): |E| + c = |V|

**Proof:** We have ≥ from theorem 1. For ≤, use that every edge in
a forest is a bridge, so removing any edge increases component count by exactly 1.
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
  | _ n ih =>
    by_cases h_zero : n = 0
    · -- Base case
      subst h_zero
      have h_empty := edgeSet_empty_of_card_zero G hn
      have h_eq := components_eq_vertices_of_no_edges G h_empty
      rw [h_eq]; omega
    · -- Inductive step
      have h_pos : 0 < n := Nat.pos_of_ne_zero h_zero
      have h_edge_pos : 0 < G.edgeFinset.card := by omega
      have h_nonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp h_edge_pos
      obtain ⟨e, he⟩ := h_nonempty
      have he_set : e ∈ G.edgeSet := by simp only [edgeFinset, Set.mem_toFinset] at he; exact he
      -- Every edge is a bridge in an acyclic graph
      have h_bridge : G.IsBridge e := isAcyclic_iff_forall_edge_isBridge.mp h_acyc he_set
      -- Get endpoints
      rcases Sym2.mk_surjective e with ⟨⟨u, v⟩, huv⟩
      have hadj : G.Adj u v := by rw [← huv] at he_set; exact he_set
      -- Delete the edge
      set G' := G.deleteEdges {e} with hG'
      haveI : DecidableRel G'.Adj := inferInstance
      haveI : Fintype G'.edgeSet := by
        apply Set.fintypeSubset G.edgeSet
        intro x hx; rw [edgeSet_deleteEdges] at hx; exact hx.1
      haveI : Fintype G'.ConnectedComponent := inferInstance
      -- G' is still acyclic (subgraph of acyclic is acyclic)
      have h_acyc' : G'.IsAcyclic := by
        intro w c hc
        -- Map the cycle from G' to G using mapLe
        have hle : G' ≤ G := deleteEdges_le {e}
        -- mapLe preserves cycles
        exact h_acyc _ (hc.mapLe (h := hle))
      -- G' has one fewer edge
      have h_card' : G'.edgeFinset.card = n - 1 := by
        have h1 : G'.edgeFinset = G.edgeFinset.erase e := by
          ext x
          simp only [edgeFinset, Set.mem_toFinset, Finset.mem_erase]
          rw [edgeSet_deleteEdges]
          simp only [Set.mem_diff, Set.mem_singleton_iff]
          tauto
        rw [h1, Finset.card_erase_of_mem he, hn]
      -- Bridge removal increases component count by exactly 1
      have h_comp_increase : Fintype.card G.ConnectedComponent + 1 =
          Fintype.card G'.ConnectedComponent := by
        -- Use that e is a bridge: removing it disconnects u from v
        rw [← huv] at h_bridge
        rw [isBridge_iff] at h_bridge
        -- h_bridge : G.Adj u v ∧ ¬(G \ fromEdgeSet {s(u, v)}).Reachable u v
        -- Note: G.deleteEdges {e} = G \ fromEdgeSet {e} by definition
        have h_not_reach : ¬G'.Reachable u v := by
          -- G' = G.deleteEdges {e} = G.deleteEdges {s(u,v)} = G \ fromEdgeSet {s(u,v)}
          have heq : G' = G \ fromEdgeSet {s(u, v)} := by
            simp only [hG', huv, deleteEdges]
          rw [heq]
          exact h_bridge.2
        have h_same_G : G.connectedComponentMk u = G.connectedComponentMk v :=
          ConnectedComponent.eq.mpr (Adj.reachable hadj)
        have h_diff_G' : G'.connectedComponentMk u ≠ G'.connectedComponentMk v := by
          intro heq; exact h_not_reach (ConnectedComponent.eq.mp heq)
        -- The map f : G'.CC → G.CC is surjective
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
            Reachable.mono (deleteEdges_le {e}) h2
          rw [← hw]
          exact ConnectedComponent.eq.mpr h3
        -- f maps both u and v's G'-components to the same G-component
        have h_two_preimages : f (G'.connectedComponentMk u) = f (G'.connectedComponentMk v) := by
          simp only [f]
          have h1 := (G'.connectedComponentMk u).exists_rep.choose_spec
          have h2 := (G'.connectedComponentMk v).exists_rep.choose_spec
          have h3 : G.Reachable (G'.connectedComponentMk u).exists_rep.choose u :=
            Reachable.mono (deleteEdges_le {e}) (ConnectedComponent.eq.mp h1)
          have h4 : G.Reachable (G'.connectedComponentMk v).exists_rep.choose v :=
            Reachable.mono (deleteEdges_le {e}) (ConnectedComponent.eq.mp h2)
          have h5 : G.connectedComponentMk (G'.connectedComponentMk u).exists_rep.choose =
              G.connectedComponentMk u := ConnectedComponent.eq.mpr h3
          have h6 : G.connectedComponentMk (G'.connectedComponentMk v).exists_rep.choose =
              G.connectedComponentMk v := ConnectedComponent.eq.mpr h4
          rw [h5, h6, h_same_G]
        -- card G.CC <= card G'.CC (f is surjective)
        have h_le : Fintype.card G.ConnectedComponent ≤ Fintype.card G'.ConnectedComponent :=
          Fintype.card_le_of_surjective f hf_surj
        -- card G'.CC <= card G.CC + 1 (from deleteEdge_components_bound)
        have h_bound : Fintype.card G'.ConnectedComponent ≤
            Fintype.card G.ConnectedComponent + 1 := deleteEdge_components_bound G e he_set
        -- Since u and v are in different G'-components but same G-component,
        -- and f is surjective, we have card G'.CC = card G.CC + 1
        have h_strict : Fintype.card G.ConnectedComponent < Fintype.card G'.ConnectedComponent := by
          by_contra h_not_lt
          push_neg at h_not_lt
          have h_eq : Fintype.card G'.ConnectedComponent = Fintype.card G.ConnectedComponent :=
            le_antisymm h_not_lt h_le
          -- If card G'.CC = card G.CC, then f is a bijection
          have h_bij : Function.Bijective f := by
            rw [Fintype.bijective_iff_surjective_and_card]
            exact ⟨hf_surj, h_eq⟩
          -- But f maps different elements to the same element
          exact h_diff_G' (h_bij.1 h_two_preimages)
        omega
      -- Apply IH
      have h_ge' := edges_plus_components_ge_vertices G'
      have h_ih := ih (n - 1) (by omega) G' h_acyc' h_ge' h_card'
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
  rcases Sym2.mk_surjective e with ⟨⟨u, v⟩, huv⟩
  have hadj : G.Adj u v := by rw [← huv] at he_set; exact he_set
  -- e is not a bridge, so removing it doesn't disconnect u and v
  have h_still_reach : (G.deleteEdges {s(u, v)}).Reachable u v := by
    rw [← huv] at h_not_bridge
    rw [isBridge_iff] at h_not_bridge
    push_neg at h_not_bridge
    rw [← huv] at he_set
    have h := h_not_bridge he_set
    -- G.deleteEdges {s(u,v)} = G \ fromEdgeSet {s(u,v)} by definition
    simp only [deleteEdges] at h ⊢
    exact h
  -- Delete the edge
  set G' := G.deleteEdges {s(u, v)} with hG'
  haveI : DecidableRel G'.Adj := inferInstance
  haveI : Fintype G'.edgeSet := by
    apply Set.fintypeSubset G.edgeSet
    intro x hx
    rw [edgeSet_deleteEdges] at hx
    exact hx.1
  haveI : Fintype G'.ConnectedComponent := inferInstance
  -- G' has one fewer edge
  have he_mem : s(u, v) ∈ G.edgeSet := by rw [huv]; exact he_set
  have h_fewer_edge : G'.edgeFinset.card = G.edgeFinset.card - 1 := by
    have he : s(u, v) ∈ G.edgeFinset := by
      simp only [edgeFinset, Set.mem_toFinset]
      exact he_mem
    have h1 : G'.edgeFinset = G.edgeFinset.erase s(u, v) := by
      ext x
      simp only [edgeFinset, Set.mem_toFinset, Finset.mem_erase]
      rw [edgeSet_deleteEdges]
      simp only [Set.mem_diff, Set.mem_singleton_iff]
      tauto
    rw [h1, Finset.card_erase_of_mem he]
  -- Components stay the same (non-bridge means u and v stay connected)
  have h_same_comp : Fintype.card G.ConnectedComponent = Fintype.card G'.ConnectedComponent := by
    apply le_antisymm
    · -- G.CC <= G'.CC: use surjective map f : G'.CC → G.CC
      let f : G'.ConnectedComponent → G.ConnectedComponent :=
        fun c' => G.connectedComponentMk c'.exists_rep.choose
      apply Fintype.card_le_of_surjective f
      intro c
      obtain ⟨w, hw⟩ := c.exists_rep
      use G'.connectedComponentMk w
      simp only [f]
      have h1 := (G'.connectedComponentMk w).exists_rep.choose_spec
      have h2 : G'.Reachable (G'.connectedComponentMk w).exists_rep.choose w :=
        ConnectedComponent.eq.mp h1
      have h3 : G.Reachable (G'.connectedComponentMk w).exists_rep.choose w :=
        Reachable.mono (deleteEdges_le {s(u, v)}) h2
      rw [← hw]
      exact ConnectedComponent.eq.mpr h3
    · -- G'.CC <= G.CC: show f is injective (so card G'.CC <= card G.CC)
      let f : G'.ConnectedComponent → G.ConnectedComponent :=
        fun c' => G.connectedComponentMk c'.exists_rep.choose
      apply Fintype.card_le_of_injective f
      intro c1' c2' hf_eq
      -- hf_eq says the G-components are equal
      -- Need to show the G'-components are equal
      have h1 := c1'.exists_rep.choose_spec
      have h2 := c2'.exists_rep.choose_spec
      set w1 := c1'.exists_rep.choose with hw1_def
      set w2 := c2'.exists_rep.choose with hw2_def
      -- w1 and w2 are in the same G-component (from hf_eq)
      have hG_same : G.connectedComponentMk w1 = G.connectedComponentMk w2 := hf_eq
      have hG_reach : G.Reachable w1 w2 := ConnectedComponent.eq.mp hG_same
      -- Since {u,v} is not a bridge, G-connected implies G'-connected
      -- Use a helper function to convert G-paths to G'-paths
      have path_to_G' : ∀ {a b : V} (p : G.Walk a b), s(u, v) ∉ p.edges → G'.Reachable a b := by
        intro a b p h_not_in
        induction p with
        | nil => exact Reachable.refl (G := G') _
        | @cons x y z hadj tail ih =>
          have h_xy_not_edge : s(x, y) ≠ s(u, v) := by
            intro heq
            apply h_not_in
            simp only [Walk.edges_cons, List.mem_cons]
            left; exact heq.symm
          have h_not_in_tail : s(u, v) ∉ tail.edges := by
            intro hin
            apply h_not_in
            simp only [Walk.edges_cons, List.mem_cons]
            right; exact hin
          have hadj' : G'.Adj x y := by
            simp only [hG', deleteEdges_adj]
            exact ⟨hadj, h_xy_not_edge⟩
          exact Reachable.trans (Adj.reachable hadj') (ih h_not_in_tail)
      have hG'_reach : G'.Reachable w1 w2 := by
        obtain ⟨p⟩ := hG_reach
        -- Check if the path uses the deleted edge
        by_cases h_uses : s(u, v) ∈ p.edges
        · -- The path uses the edge - reroute through alternate path
          -- Since s(u,v) is not a bridge, u and v are still G'-reachable
          have hu_in : u ∈ p.support := Walk.fst_mem_support_of_mem_edges p h_uses
          have hv_in : v ∈ p.support := Walk.snd_mem_support_of_mem_edges p h_uses
          have hne : u ≠ v := hadj.ne
          -- Take prefixes to u and v
          let pu := p.takeUntil u hu_in
          let pv := p.takeUntil v hv_in
          -- At least one prefix doesn't use s(u,v) (whichever endpoint appears first)
          by_cases hpu : s(u, v) ∈ pu.edges
          · -- pu uses s(u,v), so v appears before u in p; therefore pv doesn't use s(u,v)
            have hpv : s(u, v) ∉ pv.edges := by
              intro h
              have hcontra := takeUntil_first_endpoint_no_edge G p h_uses hu_in hv_in hne
              cases hcontra with
              | inl h_not_pu => exact h_not_pu hpu
              | inr h_not_pv => exact h_not_pv h
            -- G'-path from w1 to v
            have h1 : G'.Reachable w1 v :=
              ⟨walk_deleteEdges_eq rfl (pv.toDeleteEdge (s(u,v)) hpv)⟩
            -- G'-path from v to u (since s(u,v) is not a bridge)
            have h2 : G'.Reachable v u :=
              ⟨(Classical.choice h_still_reach).reverse⟩
            -- G'-path from u to w2: use dropUntil
            let qu := p.dropUntil u hu_in
            by_cases hqu : s(u, v) ∈ qu.edges
            · -- qu uses s(u,v), handle via reverse walk
              let p' := p.reverse
              have hp' : s(u, v) ∈ p'.edges := Walk.edges_reverse p ▸ List.mem_reverse.mpr h_uses
              have hv_in' : v ∈ p'.support := Walk.support_reverse p ▸ List.mem_reverse.mpr hv_in
              let rv := p'.takeUntil v hv_in'
              by_cases hrv : s(u, v) ∈ rv.edges
              · -- Use takeUntil_first_endpoint_no_edge on p' to get alternate path
                have hu_in' : u ∈ p'.support := Walk.fst_mem_support_of_mem_edges p' hp'
                have hcontra := takeUntil_first_endpoint_no_edge G p' hp' hu_in' hv_in' hne
                let ru' := p'.takeUntil u hu_in'
                have hru'_no_e : s(u, v) ∉ ru'.edges := by
                  cases hcontra with
                  | inl h_not => exact h_not
                  | inr h_not_rv => exact absurd hrv h_not_rv
                -- G'-path from w2 to u
                have h3 : G'.Reachable w2 u :=
                  ⟨walk_deleteEdges_eq rfl (ru'.toDeleteEdge (s(u,v)) hru'_no_e)⟩
                exact h1.trans (h2.trans h3.symm)
              · -- rv doesn't use s(u,v), so G'-path from w2 to v
                have h3 : G'.Reachable w2 v :=
                  ⟨walk_deleteEdges_eq rfl (rv.toDeleteEdge (s(u,v)) hrv)⟩
                exact h1.trans h3.symm
            · -- qu doesn't use s(u,v), so G'-path from u to w2
              have h3 : G'.Reachable u w2 :=
                ⟨walk_deleteEdges_eq rfl (qu.toDeleteEdge (s(u,v)) hqu)⟩
              exact h1.trans (h2.trans h3)
          · -- pu doesn't use s(u,v), so G'-path from w1 to u
            have h1 : G'.Reachable w1 u :=
              ⟨walk_deleteEdges_eq rfl (pu.toDeleteEdge (s(u,v)) hpu)⟩
            -- G'-path from u to v (since s(u,v) is not a bridge)
            have h2 : G'.Reachable u v :=
              ⟨Classical.choice h_still_reach⟩
            -- G'-path from v to w2: use dropUntil
            let qv := p.dropUntil v hv_in
            by_cases hqv : s(u, v) ∈ qv.edges
            · -- qv uses s(u,v), handle via reverse walk
              let p' := p.reverse
              have hp' : s(u, v) ∈ p'.edges := Walk.edges_reverse p ▸ List.mem_reverse.mpr h_uses
              have hu_in' : u ∈ p'.support := Walk.support_reverse p ▸ List.mem_reverse.mpr hu_in
              let ru := p'.takeUntil u hu_in'
              by_cases hru : s(u, v) ∈ ru.edges
              · -- Use takeUntil_first_endpoint_no_edge on p' to get path via v
                have hv_in' : v ∈ p'.support := Walk.snd_mem_support_of_mem_edges p' hp'
                have hcontra := takeUntil_first_endpoint_no_edge G p' hp' hu_in' hv_in' hne
                let rv' := p'.takeUntil v hv_in'
                have hrv'_no_e : s(u, v) ∉ rv'.edges := by
                  cases hcontra with
                  | inl h_not_ru => exact absurd hru h_not_ru
                  | inr h_not => exact h_not
                -- G'-path from w2 to v
                have h3 : G'.Reachable w2 v :=
                  ⟨walk_deleteEdges_eq rfl (rv'.toDeleteEdge (s(u,v)) hrv'_no_e)⟩
                exact h1.trans (h2.trans h3.symm)
              · -- ru doesn't use s(u,v), so G'-path from w2 to u
                have h3 : G'.Reachable w2 u :=
                  ⟨walk_deleteEdges_eq rfl (ru.toDeleteEdge (s(u,v)) hru)⟩
                exact h1.trans h3.symm
            · -- qv doesn't use s(u,v), so G'-path from v to w2
              have h3 : G'.Reachable v w2 :=
                ⟨walk_deleteEdges_eq rfl (qv.toDeleteEdge (s(u,v)) hqv)⟩
              exact h1.trans (h2.trans h3)
        · -- The path doesn't use the edge, so it's valid in G'
          exact path_to_G' p h_uses
      rw [← h1, ← h2]
      exact ConnectedComponent.eq.mpr hG'_reach
  -- Apply inequality to G'
  have h_ge := edges_plus_components_ge_vertices G'
  have h_edge_pos : G.edgeFinset.card > 0 := by
    have : s(u, v) ∈ G.edgeFinset := by
      simp only [edgeFinset, Set.mem_toFinset]
      exact he_mem
    exact Finset.card_pos.mpr ⟨s(u, v), this⟩
  -- h_ge : G'.edgeFinset.card + card G'.CC >= card V
  -- Rewrite to express in terms of G
  rw [h_fewer_edge, ← h_same_comp] at h_ge
  -- Now h_ge : (G.edgeFinset.card - 1) + card G.CC >= card V
  -- But h_euler : G.edgeFinset.card + card G.CC = card V
  -- So (G.edgeFinset.card - 1) + card G.CC >= G.edgeFinset.card + card G.CC
  -- This implies -1 >= 0, contradiction (since h_edge_pos : G.edgeFinset.card > 0)
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
