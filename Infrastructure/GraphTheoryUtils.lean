/-
  Infrastructure/GraphTheoryUtils.lean

  Graph theory utilities for forests, cycles, and path properties.
  Includes tree characterization by edge count, forest-Euler relations,
  and cycle creation when adding edges to connected graphs.

  SORRIES: 1 (complex walk argument in add_edge_creates_cycle)
  AXIOMS: 0
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

namespace Infrastructure

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Section 1: Path Uniqueness in Trees -/

/-- In an acyclic graph, paths are unique -/
theorem acyclic_path_unique' (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_acyclic : G.IsAcyclic) (u v : V) (p q : G.Path u v) : p = q :=
  h_acyclic.path_unique p q

/-! ## Section 2: Cycle Detection -/

/-- A graph has a cycle iff it's not acyclic -/
theorem has_cycle_iff_not_acyclic (G : SimpleGraph V) :
    (∃ v : V, ∃ p : G.Walk v v, p.IsCycle) ↔ ¬G.IsAcyclic := by
  constructor
  · intro ⟨v, p, hp⟩ h_acyclic
    exact h_acyclic p hp
  · intro h_not_acyclic
    unfold IsAcyclic at h_not_acyclic
    push_neg at h_not_acyclic
    exact h_not_acyclic

/-! ## Section 3: Walk and Edge Properties -/

/-- A walk of length n has exactly n edges -/
theorem walk_length_eq_edges {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.length = p.edges.length := (Walk.length_edges p).symm

/-- A cycle has at least 3 edges -/
theorem cycle_min_length {G : SimpleGraph V} {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) : 3 ≤ p.length := hp.three_le_length

/-- Trail (no repeated edges) property -/
theorem trail_edges_nodup {G : SimpleGraph V} {u v : V} {p : G.Walk u v}
    (ht : p.IsTrail) : p.edges.Nodup := ht.edges_nodup

/-! ## Section 4: Small Graph Lemmas -/

/-- Single vertex graph is acyclic -/
theorem single_vertex_acyclic (G : SimpleGraph V) (h : Fintype.card V = 1) :
    G.IsAcyclic := by
  intro v p hp
  have h_len := hp.three_le_length
  have h_tail_nodup := hp.support_nodup
  have h_card_ge : 3 ≤ Fintype.card V := by
    have := List.Nodup.length_le_card h_tail_nodup
    have h_tail_len : p.support.tail.length ≥ p.length := by
      have h1 : p.support.length = p.length + 1 := Walk.length_support p
      simp only [List.length_tail]
      omega
    omega
  omega

/-- Two vertex graph is acyclic -/
theorem two_vertex_acyclic (G : SimpleGraph V) (h : Fintype.card V = 2) :
    G.IsAcyclic := by
  intro v p hp
  have h_len := hp.three_le_length
  have h_tail_nodup := hp.support_nodup
  have h_card_ge : 3 ≤ Fintype.card V := by
    have := List.Nodup.length_le_card h_tail_nodup
    have h_tail_len : p.support.tail.length ≥ p.length := by
      have h1 : p.support.length = p.length + 1 := Walk.length_support p
      simp only [List.length_tail]
      omega
    omega
  omega

/-- Less than 3 vertices implies acyclic -/
theorem lt_three_acyclic (G : SimpleGraph V) (h : Fintype.card V < 3) :
    G.IsAcyclic := by
  intro v p hp
  have h_len := hp.three_le_length
  have h_tail_nodup := hp.support_nodup
  have h_card_ge : 3 ≤ Fintype.card V := by
    have := List.Nodup.length_le_card h_tail_nodup
    have h_tail_len : p.support.tail.length ≥ p.length := by
      have h1 : p.support.length = p.length + 1 := Walk.length_support p
      simp only [List.length_tail]
      omega
    omega
  omega

/-! ## Section 5: Tree Characterization by Edge Count -/

/-- A connected graph is a tree iff it has exactly n-1 edges.
    This uses Mathlib's `isTree_iff_connected_and_card`. -/
theorem connected_tree_iff_edge_count (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsTree ↔ G.Connected ∧ Nat.card G.edgeSet + 1 = Fintype.card V := by
  simp only [isTree_iff_connected_and_card, Nat.card_eq_fintype_card]

/-- Variant using edgeFinset cardinality -/
theorem connected_tree_iff_edge_finset_count (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet] :
    G.IsTree ↔ G.Connected ∧ G.edgeFinset.card + 1 = Fintype.card V := by
  rw [connected_tree_iff_edge_count]
  constructor
  · intro ⟨hc, he⟩
    rw [Nat.card_eq_fintype_card] at he
    rw [← edgeFinset_card] at he
    exact ⟨hc, he⟩
  · intro ⟨hc, he⟩
    rw [edgeFinset_card] at he
    rw [← Nat.card_eq_fintype_card (α := G.edgeSet)] at he
    exact ⟨hc, he⟩

/-! ## Section 6: Forest and Euler Characteristic -/

/-- For a connected tree, edges = vertices - 1 (Euler formula for trees) -/
theorem tree_euler_formula (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (h_tree : G.IsTree) :
    G.edgeFinset.card + 1 = Fintype.card V :=
  h_tree.card_edgeFinset

/-- For an acyclic connected graph (tree), edge count is exactly |V| - 1 -/
theorem forest_iff_euler (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (h_conn : G.Connected) :
    G.IsAcyclic ↔ G.edgeFinset.card + 1 = Fintype.card V := by
  constructor
  · intro h_acyc
    exact (IsTree.mk h_conn h_acyc).card_edgeFinset
  · intro h_card
    have h_tree : G.IsTree := by
      rw [connected_tree_iff_edge_finset_count]
      exact ⟨h_conn, h_card⟩
    exact h_tree.IsAcyclic

/-! ## Section 7: Adding Edges Creates Cycles -/

/-- Adding an edge between reachable distinct non-adjacent vertices creates a cycle.
    This follows from the fact that u,v are reachable, so adding edge v→u closes a cycle.
    The detailed walk argument for constructing the cycle is deferred (see sorry). -/
theorem add_edge_creates_cycle (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (h_neq : u ≠ v) (h_reach : G.Reachable u v) (h_not_adj : ¬G.Adj u v) :
    ¬(G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).IsAcyclic := by
  intro h_acyc
  -- Get a path from u to v
  obtain ⟨p⟩ := h_reach
  -- Convert to a simple path (no repeated vertices)
  let pp := p.toPath
  -- The path has length ≥ 2 since u ≠ v and not adjacent
  have h_len_ge_2 : pp.val.length ≥ 2 := by
    match hlen : pp.val.length with
    | 0 =>
      have heq := Walk.eq_of_length_eq_zero hlen
      exact absurd heq h_neq
    | 1 =>
      have hadj := pp.val.adj_of_length_eq_one hlen
      exact absurd hadj h_not_adj
    | n + 2 => omega
  -- Construct the edge from v back to u in the augmented graph
  have h_sup_adj : (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Adj v u := by
    simp only [sup_adj, fromEdgeSet_adj, Set.mem_singleton_iff]
    right
    exact ⟨Sym2.eq_swap, h_neq.symm⟩
  -- Lift the path to the augmented graph
  let pp' : (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).Walk u v := pp.val.mapLe le_sup_left
  -- Create the cycle: path u→v then edge v→u
  let c := pp'.concat h_sup_adj
  -- The cycle construction shows c is a valid cycle
  -- Trail: edges nodup (pp is a path, and new edge is not in pp since ¬G.Adj u v)
  -- Support nodup: tail of support is nodup (pp is a path with u at start)
  have h_is_cycle : c.IsCycle := by
    -- c = pp'.concat h_sup_adj where pp' is a path lifted to augmented graph
    -- IsCycle requires: IsCircuit (IsTrail + ne_nil) + support.tail.Nodup
    -- Key facts:
    -- 1. pp' is a path (hence trail with nodup edges)
    -- 2. The new edge s(v,u) is not in pp' since ¬G.Adj u v
    -- 3. Support tail nodup follows from pp' being a path
    -- TODO: Complete using Walk.IsTrail and Walk.IsPath properties
    sorry
  -- But h_acyc says no cycles exist - contradiction
  exact h_acyc c h_is_cycle

/-- In a connected graph, adding any new edge creates a cycle -/
theorem connected_add_edge_creates_cycle (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_conn : G.Connected) (u v : V) (h_neq : u ≠ v) (h_not_adj : ¬G.Adj u v) :
    ¬(G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).IsAcyclic :=
  add_edge_creates_cycle G u v h_neq (h_conn u v) h_not_adj

/-! ## Summary -/

#check acyclic_path_unique'
#check has_cycle_iff_not_acyclic
#check single_vertex_acyclic
#check two_vertex_acyclic
#check lt_three_acyclic
#check connected_tree_iff_edge_count
#check forest_iff_euler
#check connected_add_edge_creates_cycle

end Infrastructure
