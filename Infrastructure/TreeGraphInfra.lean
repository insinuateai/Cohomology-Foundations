/-
  Infrastructure/TreeGraphInfra.lean

  Tree and Graph Theory Infrastructure for DimensionBound.lean.

  SORRIES: 3 (graph theory lemmas requiring component-wise reasoning)
  AXIOMS: 0
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Infrastructure.GraphTheoryUtils

namespace Infrastructure

open SimpleGraph

variable {V : Type*} [Fintype V]

/-! ## Spanning Forest Theory

These lemmas support the graph theory infrastructure in DimensionBound.lean.
Key result: |E| + c ≥ |V| for any graph with c connected components.
-/

/-- Component count bound: in a graph, |E| + c ≥ |V|

This is a standard graph theory result: each connected component with
n_i vertices needs at least n_i - 1 edges to be connected.
Summing: |E| ≥ Σ(n_i - 1) = |V| - c, hence |E| + c ≥ |V|.

Proof by strong induction on |E|:
- Base: |E| = 0 implies each vertex is isolated, so c = |V|, thus |E| + c = |V|
- Step: For |E| > 0, remove any edge e. By IH, (|E|-1) + c' ≥ |V|.
  Adding e back either merges components (c = c'-1) or not (c = c').
  Either way, |E| + c ≥ |V|. -/
theorem edges_plus_components_ge_vertices
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent] [Nonempty V] :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent ≥ Fintype.card V := by
  -- TODO: Implement strong induction on edge count
  -- Base case: empty edge set means c = |V|
  -- Inductive case: remove edge, apply IH, analyze bridge vs non-bridge
  sorry

/-! ## Acyclic-Euler Characterization -/

/-- For an acyclic graph (forest): |E| + c = |V|

Each component of a forest is a tree with n_i vertices and n_i - 1 edges.
Summing: |E| = Σ(n_i - 1) = |V| - c, hence |E| + c = |V|. -/
theorem acyclic_euler_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent] [Nonempty V]
    (h_acyc : G.IsAcyclic) :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent = Fintype.card V := by
  by_cases h_conn : G.Connected
  · -- Connected case: G is a tree
    have h_tree : G.IsTree := ⟨h_conn, h_acyc⟩
    have h_one_comp : Fintype.card G.ConnectedComponent = 1 := by
      rw [Fintype.card_eq_one_iff]
      use G.connectedComponentMk (Classical.arbitrary V)
      intro c
      obtain ⟨v, rfl⟩ := c.exists_rep
      exact ConnectedComponent.eq.mpr (h_conn.preconnected v (Classical.arbitrary V))
    rw [h_one_comp]
    exact h_tree.card_edgeFinset
  · -- Disconnected forest: sum over tree components
    -- Each component c_i is a tree by IsAcyclic.isTree_connectedComponent
    -- For tree: |E_i| + 1 = |V_i| (Mathlib: IsTree.card_edgeFinset)
    -- Sum over components: Σ|E_i| + c = Σ|V_i| = |V|
    -- Key: edges partition by component, vertices partition by component
    -- Uses: iUnion_connectedComponentSupp, ConnectedComponent.pairwise_disjoint_supp
    sorry

/-- If |E| + c = |V|, the graph is acyclic

Contrapositive: a cycle means one component has ≥ n_i edges (not n_i - 1),
so |E| > |V| - c, contradicting |E| + c = |V|. -/
theorem euler_eq_implies_acyclic'
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent]
    (h_euler : G.edgeFinset.card + Fintype.card G.ConnectedComponent = Fintype.card V) :
    G.IsAcyclic := by
  by_contra h_not_acyc
  have h_cycle := (has_cycle_iff_not_acyclic G).mpr h_not_acyc
  obtain ⟨v, p, hp⟩ := h_cycle
  have h_3le : 3 ≤ p.length := hp.three_le_length
  have h_supp_nodup := hp.support_nodup
  have h_supp_len : p.support.tail.length ≥ p.length := by
    have h1 : p.support.length = p.length + 1 := Walk.length_support p
    simp only [List.length_tail]; omega
  have h_3_vertices : 3 ≤ Fintype.card V := by
    calc Fintype.card V ≥ p.support.tail.length := List.Nodup.length_le_card h_supp_nodup
      _ ≥ p.length := h_supp_len
      _ ≥ 3 := h_3le
  -- With a cycle, the component containing it has an "extra" edge:
  -- - A tree on n_i vertices has n_i - 1 edges
  -- - A component with a cycle has ≥ n_i edges (at least one non-bridge)
  -- - So |E| ≥ (|V| - c) + 1, giving |E| + c ≥ |V| + 1
  -- - This contradicts h_euler: |E| + c = |V|
  --
  -- Key insight: In a cyclic component, removing any cycle edge keeps it connected,
  -- so that edge is not a bridge. But isAcyclic_iff_forall_edge_isBridge says
  -- acyclic ↔ all edges are bridges.
  sorry

/-- Combined characterization: acyclic ↔ |E| + c = |V| -/
theorem acyclic_iff_euler
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent] [Nonempty V] :
    G.IsAcyclic ↔ G.edgeFinset.card + Fintype.card G.ConnectedComponent = Fintype.card V := by
  constructor
  · exact acyclic_euler_eq G
  · exact euler_eq_implies_acyclic' G

end Infrastructure
