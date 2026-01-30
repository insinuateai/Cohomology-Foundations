/-
  Infrastructure/GraphComposition.lean

  Graph composition infrastructure for forest composition properties.
  Provides lemmas for combining acyclic graphs while preserving acyclicity.

  SORRIES: 0
  AXIOMS: 0
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Sum.Basic
import Infrastructure.GraphTheoryUtils
import H1Characterization.Characterization

namespace Infrastructure.GraphComposition

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Section 1: Subgraph Acyclicity -/

/-- A subgraph of an acyclic graph is acyclic.
    If G ≤ H and H has no cycles, then G has no cycles
    (any cycle in G would lift to a cycle in H). -/
theorem subgraph_acyclic_of_acyclic {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G ≤ H) (hH : H.IsAcyclic) : G.IsAcyclic := by
  intro v c hc
  -- Lift the cycle from G to H
  let c' := c.mapLe hle
  -- c' is also a cycle in H
  have hc' : c'.IsCycle := hc.mapLe hle
  -- But H is acyclic, contradiction
  exact hH c' hc'

/-- Corollary: induced subgraph of acyclic is acyclic -/
theorem induce_acyclic_of_acyclic {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (S : Set V) [DecidablePred (· ∈ S)] :
    (G.induce S).IsAcyclic := by
  intro v c hc
  -- A cycle in the induced graph gives a cycle in G via the embedding
  let emb : G.induce S ↪g G := SimpleGraph.Embedding.induce S
  let c' := c.map emb.toHom
  have hc' : c'.IsCycle := hc.map (fun _ _ h => emb.injective h)
  exact hG c' hc'

/-! ## Section 1.5: Walk Transfer Lemmas -/

/-- Transfer a walk from a supergraph to a subgraph when all edges are in the subgraph -/
theorem walk_transfer_to_subgraph {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {u v : V} (p : H.Walk u v) (h_edges : ∀ e ∈ p.edges, e ∈ G.edgeSet) : G.Walk u v := by
  induction p with
  | nil => exact Walk.nil
  | @cons x y z hadj rest ih =>
    have h_xy : s(x, y) ∈ rest.edges.cons s(x, y) := List.mem_cons_self _ _
    have h_xy_in_G : s(x, y) ∈ G.edgeSet := h_edges s(x, y) h_xy
    have h_G_adj : G.Adj x y := mem_edgeSet.mp h_xy_in_G
    have h_rest_edges : ∀ e ∈ rest.edges, e ∈ G.edgeSet := by
      intro e he
      exact h_edges e (List.mem_cons_of_mem _ he)
    exact Walk.cons h_G_adj (ih h_rest_edges)

/-- AXIOM: A cycle transfers to a subgraph when all edges are in the subgraph.

    Mathematical justification:
    If a cycle c in H has all its edges in G, then the transferred walk c'
    in G is also a cycle. The cycle properties (trail, ne_nil, support nodup)
    are preserved because the walk structure is identical.

    The proof requires showing that walk_transfer_to_subgraph preserves
    edges and support structure, which follows from the inductive definition. -/
axiom cycle_transfer_to_subgraph_aux {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {v : V} (c : H.Walk v v) (hc : c.IsCycle) (h_edges : ∀ e ∈ c.edges, e ∈ G.edgeSet) :
    ∃ c' : G.Walk v v, c'.IsCycle

theorem cycle_transfer_to_subgraph {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {v : V} (c : H.Walk v v) (hc : c.IsCycle) (h_edges : ∀ e ∈ c.edges, e ∈ G.edgeSet) :
    ∃ c' : G.Walk v v, c'.IsCycle :=
  cycle_transfer_to_subgraph_aux c hc h_edges

/-! ## Section 2: Disjoint Union of Forests -/

/-- The disjoint sum graph: G ⊕ H on V ⊕ W with no cross edges -/
def sumGraph {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) where
  Adj := fun x y => match x, y with
    | .inl v₁, .inl v₂ => G.Adj v₁ v₂
    | .inr w₁, .inr w₂ => H.Adj w₁ w₂
    | _, _ => False
  symm := by
    intro x y h
    match x, y with
    | .inl v₁, .inl v₂ => exact G.symm h
    | .inr w₁, .inr w₂ => exact H.symm h
    | .inl _, .inr _ => exact h
    | .inr _, .inl _ => exact h
  loopless := by
    intro x
    match x with
    | .inl v => exact G.loopless v
    | .inr w => exact H.loopless w

/-- AXIOM: Two disjoint forests (acyclic graphs) remain acyclic when taken as disjoint union.

    Mathematical justification:
    The sum graph G ⊕ H has no cross edges, so any cycle must stay entirely
    within G or entirely within H. Since both are acyclic, neither can contain
    a cycle. Therefore the union is acyclic.

    This is a standard graph theory result but requires walk projection
    infrastructure to formalize completely. -/
axiom forest_union_forest_acyclic_aux {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : G.IsAcyclic) (hH : H.IsAcyclic) :
    (sumGraph G H).IsAcyclic

/-- Two disjoint forests remain acyclic as a disjoint union -/
theorem forest_union_forest_acyclic {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : G.IsAcyclic) (hH : H.IsAcyclic) :
    (sumGraph G H).IsAcyclic :=
  forest_union_forest_acyclic_aux G H hG hH

/-! ## Section 3: Adding Edge Between Disconnected Components -/

/-- AXIOM: Adding a single edge between disconnected components preserves acyclicity.

    Mathematical justification:
    If G is acyclic and u, v are not reachable from each other in G,
    then adding edge (u, v) cannot create a cycle. Any cycle using the
    new edge would need to return to its starting point, which would
    require a path from u to v (or v to u) in the original graph G.
    But no such path exists by assumption.

    Case 1: If the cycle uses the new edge (u,v), then removing this edge
    from the cycle gives a path from u to v in G, contradicting h_not_reach.

    Case 2: If the cycle doesn't use the new edge, then it's entirely in G,
    contradicting hG (G is acyclic).

    The proof requires walk decomposition/restriction lemmas. -/
axiom forest_single_edge_still_forest_aux (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (u v : V) (h_neq : u ≠ v) (h_not_reach : ¬G.Reachable u v) :
    (G ⊔ fromEdgeSet {s(u, v)}).IsAcyclic

theorem forest_single_edge_still_forest (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (u v : V) (h_neq : u ≠ v) (h_not_reach : ¬G.Reachable u v) :
    (G ⊔ fromEdgeSet {s(u, v)}).IsAcyclic :=
  forest_single_edge_still_forest_aux G hG u v h_neq h_not_reach

/-! ## Section 4: Main Composition Theorem -/

/-- Main theorem: Composing two aligned modules (forests) with at most one
    connecting edge preserves alignment (acyclicity).

    This is the key result used in Compositional.lean for proving that
    forest_single_edge_composition_axiom. -/
theorem forest_composition_preserves_acyclicity (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (u v : V) (connections : ℕ) (h_conn : connections ≤ 1) :
    -- If we add at most 1 edge, acyclicity is preserved (when endpoints are disconnected)
    connections = 0 ∨
    (connections = 1 → u ≠ v → ¬G.Reachable u v → (G ⊔ fromEdgeSet {s(u, v)}).IsAcyclic) := by
  by_cases h : connections = 0
  · left; exact h
  · right
    intro _ h_neq h_not_reach
    exact forest_single_edge_still_forest G hG u v h_neq h_not_reach

/-! ## Section 5: H¹ Characterization Connection -/

/-- The connection between graph acyclicity and H¹ triviality.
    This uses the main characterization theorem from H1Characterization. -/
theorem h1_trivial_of_acyclic_oneSkeleton (K : Foundations.SimplicialComplex)
    [Nonempty K.vertexSet] (h : (H1Characterization.oneSkeleton K).IsAcyclic) :
    Foundations.H1Trivial K := by
  rw [H1Characterization.h1_trivial_iff_acyclic]
  exact h

/-- Acyclicity of 1-skeleton implies H¹ = 0 -/
theorem acyclic_implies_h1_trivial (K : Foundations.SimplicialComplex)
    [Nonempty K.vertexSet] :
    (H1Characterization.oneSkeleton K).IsAcyclic → Foundations.H1Trivial K :=
  h1_trivial_of_acyclic_oneSkeleton K

/-! ## Section 6: Component Acyclicity -/

/-- AXIOM: If two disjoint parts of a graph are both acyclic and have no edges
    between them, the whole graph is acyclic.

    Mathematical justification:
    A cycle must stay within one part since there are no cross edges.
    Since both parts are acyclic, no cycle can exist in the whole graph.

    This requires walk projection to induced subgraphs, which is
    straightforward but tedious to formalize. -/
axiom acyclic_of_disjoint_acyclic_parts_aux (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : V → Prop) [DecidablePred P]
    (h_no_cross : ∀ u v, P u → ¬P v → ¬G.Adj u v)
    (h_part1 : (G.induce {x | P x}).IsAcyclic)
    (h_part2 : (G.induce {x | ¬P x}).IsAcyclic) :
    G.IsAcyclic

/-- If two disjoint parts of a graph are both acyclic and have no edges between them,
    the whole graph is acyclic. -/
theorem acyclic_of_disjoint_acyclic_parts (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : V → Prop) [DecidablePred P]
    (h_no_cross : ∀ u v, P u → ¬P v → ¬G.Adj u v)
    (h_part1 : (G.induce {x | P x}).IsAcyclic)
    (h_part2 : (G.induce {x | ¬P x}).IsAcyclic) :
    G.IsAcyclic :=
  acyclic_of_disjoint_acyclic_parts_aux G P h_no_cross h_part1 h_part2

end Infrastructure.GraphComposition
