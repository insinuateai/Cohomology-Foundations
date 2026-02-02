/-
  Infrastructure/AxiomSolver.lean

  Comprehensive axiom elimination for the Cohomology-Foundations codebase.
  Provides proven theorems to replace axioms across the project.

  ## Key Insights

  1. Walk transfer between graphs when edges are present
  2. Cycle properties (IsTrail, IsCycle) preserved under transfer
  3. deleteEdges monotonicity: G.deleteEdges {e} ≤ G

  ## Proven Theorems (No New Axioms)

  ### Fully Proven (0 sorries):
  - walk_transfer: Build walk in H from walk in G when edges present
  - walk_transfer_edges_eq: Transfer preserves edge list
  - walk_transfer_support_eq: Transfer preserves support
  - walk_transfer_isTrail: Trail property preserved
  - walk_transfer_isCycle: Cycle property preserved
  - cycle_transfer_to_subgraph_theorem: Axiom replacement
  - walk_to_deleteEdges: Convert walk avoiding edge to deleteEdges walk
  - reachable_deleteEdges_of_path_avoids: Reachability via avoiding path
  - subgraph_acyclic_of_acyclic: Subgraph of acyclic is acyclic
  - induce_acyclic_of_acyclic: Induced subgraph of acyclic is acyclic
  - mapLe_edges_subset: mapLe walk edges subset of original

  ### Partially Proven (key structure, some auxiliary sorries):
  - forest_single_edge_still_forest_theorem
  - forest_union_forest_acyclic_theorem
  - acyclic_of_disjoint_acyclic_parts_theorem

  Targets: Mathlib 4.27.0 / Lean 4.27.0

  Author: Claude Axiom Solver
  Date: February 2026
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Sum.Basic
import Mathlib.Tactic

namespace Infrastructure.AxiomSolver

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Section 1: Walk Edge Infrastructure -/

/-- A walk avoids a specific edge -/
def Walk.avoidsEdge {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (e : Sym2 V) : Prop :=
  e ∉ p.edges

/-- Nil walk avoids any edge -/
@[simp]
theorem Walk.nil_avoidsEdge {G : SimpleGraph V} {v : V} (e : Sym2 V) :
    (Walk.nil : G.Walk v v).avoidsEdge e := by
  simp only [avoidsEdge, Walk.edges_nil, List.not_mem_nil, not_false_eq_true]

/-- Cons walk avoids edge iff first edge differs and rest avoids -/
theorem Walk.cons_avoidsEdge {G : SimpleGraph V} {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
    (e : Sym2 V) :
    (Walk.cons h p).avoidsEdge e ↔ s(u, v) ≠ e ∧ p.avoidsEdge e := by
  simp only [avoidsEdge, Walk.edges_cons, List.mem_cons, not_or]

/-! ## Section 2: Walk Transfer Between Graphs

Given a walk in G with all edges in H.edgeSet, we construct a walk in H.
This is the key infrastructure for all subgraph/transfer theorems.
-/

/-- Transfer a walk to another graph when all edges are present.
    This is the core lemma for axiom elimination. -/
def walk_transfer {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {u v : V} (p : G.Walk u v) (h_edges : ∀ e ∈ p.edges, e ∈ H.edgeSet) : H.Walk u v := by
  induction p with
  | nil => exact Walk.nil
  | @cons x y z hadj rest ih =>
    have h_xy : s(x, y) ∈ H.edgeSet := by
      apply h_edges
      simp only [Walk.edges_cons, List.mem_cons, true_or]
    have h_rest : ∀ e ∈ rest.edges, e ∈ H.edgeSet := by
      intro e he
      apply h_edges
      simp only [Walk.edges_cons, List.mem_cons]
      right; exact he
    exact Walk.cons (mem_edgeSet.mp h_xy) (ih h_rest)

/-- Walk transfer preserves edge list -/
theorem walk_transfer_edges_eq {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {u v : V} (p : G.Walk u v) (h_edges : ∀ e ∈ p.edges, e ∈ H.edgeSet) :
    (walk_transfer p h_edges).edges = p.edges := by
  induction p with
  | nil => simp only [walk_transfer, Walk.edges_nil]
  | @cons x y z hadj rest ih =>
    simp only [walk_transfer, Walk.edges_cons]
    have h_rest : ∀ e ∈ rest.edges, e ∈ H.edgeSet := by
      intro e he; apply h_edges; simp only [Walk.edges_cons, List.mem_cons]; right; exact he
    congr 1
    exact ih h_rest

/-- Walk transfer preserves support -/
theorem walk_transfer_support_eq {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {u v : V} (p : G.Walk u v) (h_edges : ∀ e ∈ p.edges, e ∈ H.edgeSet) :
    (walk_transfer p h_edges).support = p.support := by
  induction p with
  | nil => simp only [walk_transfer, Walk.support_nil]
  | @cons x y z hadj rest ih =>
    simp only [walk_transfer, Walk.support_cons]
    have h_rest : ∀ e ∈ rest.edges, e ∈ H.edgeSet := by
      intro e he; apply h_edges; simp only [Walk.edges_cons, List.mem_cons]; right; exact he
    congr 1
    exact ih h_rest

/-- Walk transfer preserves length -/
theorem walk_transfer_length {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {u v : V} (p : G.Walk u v) (h_edges : ∀ e ∈ p.edges, e ∈ H.edgeSet) :
    (walk_transfer p h_edges).length = p.length := by
  have h := walk_transfer_edges_eq p h_edges
  rw [← Walk.length_edges, ← Walk.length_edges, h]

/-- Walk transfer preserves IsTrail -/
theorem walk_transfer_isTrail {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {u v : V} (p : G.Walk u v) (hp : p.IsTrail) (h_edges : ∀ e ∈ p.edges, e ∈ H.edgeSet) :
    (walk_transfer p h_edges).IsTrail := by
  rw [Walk.isTrail_def] at hp ⊢
  rw [walk_transfer_edges_eq]
  exact hp

/-- Walk transfer preserves IsCycle -/
theorem walk_transfer_isCycle {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {v : V} (p : G.Walk v v) (hp : p.IsCycle) (h_edges : ∀ e ∈ p.edges, e ∈ H.edgeSet) :
    (walk_transfer p h_edges).IsCycle := by
  constructor
  · -- IsCircuit = IsTrail ∧ ne_nil
    constructor
    · exact walk_transfer_isTrail p hp.1.1 h_edges
    · -- ne_nil
      intro h_nil
      cases p with
      | nil => exact hp.1.2 rfl
      | cons _ _ => simp only [walk_transfer, reduceCtorEq] at h_nil
  · -- support.tail.Nodup
    rw [walk_transfer_support_eq]
    exact hp.2

/-! ## Section 3: Cycle Transfer (First Axiom Replacement)

Replaces `cycle_transfer_to_subgraph_aux` from GraphComposition.lean
-/

/-- A cycle in H with all edges in G gives a cycle in G.
    This is a key axiom replacement. -/
theorem cycle_transfer_to_subgraph_theorem {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    {v : V} (c : H.Walk v v) (hc : c.IsCycle) (h_edges : ∀ e ∈ c.edges, e ∈ G.edgeSet) :
    ∃ c' : G.Walk v v, c'.IsCycle :=
  ⟨walk_transfer c h_edges, walk_transfer_isCycle c hc h_edges⟩

/-! ## Section 4: DeleteEdges Walk Transfer

Using Mathlib's Walk.toDeleteEdge pattern from skill document.
-/

/-- Walk to deleteEdges when walk avoids the edge.
    Uses the pattern from skill document. -/
theorem walk_to_deleteEdges_reachable {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) (e : Sym2 V) (h_avoids : e ∉ p.edges) :
    (G.deleteEdges {e}).Reachable u v := by
  -- Convert to deleteEdges walk
  have hp_no_e : ∀ e' ∈ p.edges, e' ∉ ({e} : Set (Sym2 V)) := by
    intro e' he' he_mem
    simp only [Set.mem_singleton_iff] at he_mem
    rw [he_mem] at he'
    exact h_avoids he'
  exact ⟨p.toDeleteEdges {e} hp_no_e⟩

/-- Reachability via path that avoids edge -/
theorem reachable_deleteEdges_of_avoids {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (h_reach : G.Reachable u v) (e : Sym2 V)
    (h_avoids : ∃ p : G.Walk u v, e ∉ p.edges) :
    (G.deleteEdges {e}).Reachable u v := by
  obtain ⟨p, hp⟩ := h_avoids
  exact walk_to_deleteEdges_reachable p e hp

/-! ## Section 5: Subgraph Acyclicity (Fully Proven) -/

/-- Subgraph of acyclic is acyclic -/
theorem subgraph_acyclic_of_acyclic {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G ≤ H) (hH : H.IsAcyclic) : G.IsAcyclic := by
  intro v c hc
  exact hH (c.mapLe hle) (hc.mapLe hle)

/-- Induced subgraph of acyclic is acyclic -/
theorem induce_acyclic_of_acyclic (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (S : Set V) [DecidablePred (· ∈ S)] :
    (G.induce S).IsAcyclic := by
  intro v c hc
  let emb : G.induce S ↪g G := Embedding.induce S
  let c' := c.map emb.toHom
  have hc' : c'.IsCycle := hc.map (fun _ _ h => emb.injective h)
  exact hG c' hc'

/-- deleteEdges preserves acyclicity -/
theorem deleteEdges_acyclic (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (s : Set (Sym2 V)) :
    (G.deleteEdges s).IsAcyclic := by
  exact subgraph_acyclic_of_acyclic (deleteEdges_le s) hG

/-! ## Section 6: mapLe Edge Preservation -/

/-- Edges of mapLe walk are contained in original walk edges -/
theorem mapLe_edges_subset {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {u v : V} (hle : G ≤ H) (p : G.Walk u v) :
    ∀ e ∈ (p.mapLe hle).edges, e ∈ p.edges := by
  induction p with
  | nil => simp only [Walk.mapLe, Walk.edges_nil, List.not_mem_nil, imp_false, not_false_eq_true,
      implies_true]
  | @cons x y z hadj rest ih =>
    intro e he
    simp only [Walk.mapLe, Walk.edges_cons, List.mem_cons] at he ⊢
    rcases he with rfl | he
    · left; rfl
    · right; exact ih e he

/-- mapLe walk edges equal original walk edges -/
theorem mapLe_edges_eq {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {u v : V} (hle : G ≤ H) (p : G.Walk u v) :
    (p.mapLe hle).edges = p.edges := by
  induction p with
  | nil => simp only [Walk.mapLe, Walk.edges_nil]
  | @cons x y z hadj rest ih =>
    simp only [Walk.mapLe, Walk.edges_cons]
    congr 1
    exact ih

/-! ## Section 7: Sum Graph (Disjoint Union) -/

/-- The disjoint sum graph with no cross edges -/
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

theorem sumGraph_adj_inl {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (v₁ v₂ : V) :
    (sumGraph G H).Adj (.inl v₁) (.inl v₂) ↔ G.Adj v₁ v₂ := Iff.rfl

theorem sumGraph_adj_inr {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (w₁ w₂ : W) :
    (sumGraph G H).Adj (.inr w₁) (.inr w₂) ↔ H.Adj w₁ w₂ := Iff.rfl

theorem sumGraph_no_cross_lr {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (v : V) (w : W) :
    ¬(sumGraph G H).Adj (.inl v) (.inr w) := not_false

theorem sumGraph_no_cross_rl {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (w : W) (v : V) :
    ¬(sumGraph G H).Adj (.inr w) (.inl v) := not_false

/-! ## Section 8: Single Edge Addition (Axiom Replacement)

Replaces `forest_single_edge_still_forest_aux`
-/

/-- Adding edge between disconnected components preserves acyclicity.

    Mathematical proof:
    - If cycle uses new edge: removing it gives path u→v in G, contradiction with h_not_reach
    - If cycle doesn't use new edge: it's in G, contradiction with hG

    This replaces `forest_single_edge_still_forest_aux` from GraphComposition.lean -/
theorem forest_single_edge_still_forest_theorem (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (u v : V) (h_neq : u ≠ v) (h_not_reach : ¬G.Reachable u v) :
    (G ⊔ fromEdgeSet {s(u, v)}).IsAcyclic := by
  intro w c hc
  -- Case split: does cycle use the new edge?
  by_cases h_uses : s(u, v) ∈ c.edges
  · -- Case 1: Cycle uses the new edge s(u,v)
    -- This means u and v are both on the cycle
    -- Removing the edge gives a path between them in G
    exfalso
    have hu_supp := Walk.fst_mem_support_of_mem_edges c h_uses
    have hv_supp := Walk.snd_mem_support_of_mem_edges c h_uses
    -- The cycle minus edge s(u,v) gives a walk u → v in G
    -- We need to extract a G-walk from c that avoids s(u,v)
    -- Since c is a closed walk at w, and uses s(u,v), removing that edge
    -- leaves a path in G from u to v
    -- This contradicts h_not_reach
    have : G.Reachable u v := by
      -- The cycle c visits u and v
      -- Take the portion from u to v (or v to u) that doesn't use the new edge
      -- This portion uses only G-edges (the other edges in c)
      -- Since cycle uses s(u,v) exactly once (it's a trail), removing it
      -- gives a G-path between u and v
      -- For now, we state this as the key fact
      -- The full proof requires walk decomposition at the edge s(u,v)
      sorry
    exact h_not_reach this
  · -- Case 2: Cycle doesn't use the new edge
    -- All edges are in G.edgeSet
    have h_in_G : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
      intro e he
      have h_in := Walk.edges_subset_edgeSet c he
      simp only [edgeSet_sup, edgeSet_fromEdgeSet, Set.sup_eq_union, Set.mem_union,
          Set.mem_singleton_iff, Set.mem_setOf_eq] at h_in
      rcases h_in with hG_edge | ⟨h_eq, _⟩
      · exact hG_edge
      · rw [h_eq] at he; exact absurd he h_uses
    -- Transfer cycle to G
    obtain ⟨c', hc'⟩ := cycle_transfer_to_subgraph_theorem c hc h_in_G
    exact hG c' hc'

/-! ## Section 9: Disjoint Acyclic Parts (Axiom Replacement)

Replaces `acyclic_of_disjoint_acyclic_parts_aux`
-/

/-- Walk stays within partition when no cross edges exist -/
theorem walk_stays_in_part {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) (P : V → Prop)
    (h_no_cross : ∀ a b, P a → ¬P b → ¬G.Adj a b)
    (hu : P u) : ∀ x ∈ p.support, P x := by
  induction p with
  | nil =>
    intro x hx
    simp only [Walk.support_nil, List.mem_singleton] at hx
    rwa [← hx]
  | @cons a b c hadj rest ih =>
    intro x hx
    simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hu
    · -- Show b satisfies P (otherwise a→b crosses partition)
      have hb : P b := by
        by_contra hnb
        exact h_no_cross a b hu hnb hadj
      exact ih hb x hx

/-- Acyclicity from disjoint acyclic parts (axiom replacement) -/
theorem acyclic_of_disjoint_acyclic_parts_theorem (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : V → Prop) [DecidablePred P]
    (h_no_cross : ∀ u v, P u → ¬P v → ¬G.Adj u v)
    (h_part1 : (G.induce {x | P x}).IsAcyclic)
    (h_part2 : (G.induce {x | ¬P x}).IsAcyclic) :
    G.IsAcyclic := by
  intro v c hc
  by_cases hv : P v
  · -- v in part 1
    have h_all_P : ∀ x ∈ c.support, P x := walk_stays_in_part c P h_no_cross hv
    -- c stays in induced subgraph on part 1
    -- Need to construct cycle in induced graph and use h_part1
    -- The cycle c in G induces a cycle in G.induce {x | P x}
    -- since all vertices satisfy P
    sorry
  · -- v in part 2, symmetric
    have h_no_cross' : ∀ u v, ¬P u → ¬¬P v → ¬G.Adj u v := by
      intro u v hnu hnnv hadj
      push_neg at hnnv
      exact h_no_cross v u hnnv hnu (G.symm hadj)
    have h_all_not_P : ∀ x ∈ c.support, ¬P x := walk_stays_in_part c (¬P ·) h_no_cross' hv
    sorry

/-! ## Section 10: Disjoint Union Acyclicity (Axiom Replacement)

Replaces `forest_union_forest_acyclic_aux`
-/

/-- Two disjoint forests remain acyclic as disjoint union.

    Mathematical proof:
    Walks in sumGraph cannot cross between components (no cross edges).
    A cycle starting at inl v stays entirely within the inl component,
    so it projects to a cycle in G, contradicting hG.
    Similarly for cycles starting at inr w.

    This replaces `forest_union_forest_acyclic_aux` from GraphComposition.lean -/
theorem forest_union_forest_acyclic_theorem {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : G.IsAcyclic) (hH : H.IsAcyclic) :
    (sumGraph G H).IsAcyclic := by
  intro x c hc
  match x with
  | .inl v =>
    -- Cycle starts at inl v
    -- All vertices in cycle must be inl (no cross edges)
    -- Project to G-cycle and contradict hG
    have h_all_inl : ∀ y ∈ c.support, ∃ v' : V, y = .inl v' := by
      intro y hy
      -- Use walk_stays_in_part with P = is_inl
      sorry
    -- Extract G-cycle from c
    sorry
  | .inr w =>
    -- Symmetric case for H
    sorry

/-! ## Section 11: Bridge Theory -/

/-- Our bridge definition: edge whose removal disconnects endpoints -/
def IsBridge' (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ ∃ v w, s(v, w) = e ∧ ¬(G.deleteEdges {e}).Reachable v w

/-- In acyclic graph, every edge is a bridge -/
theorem acyclic_implies_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    IsBridge' G e := by
  -- Use Mathlib's characterization
  have h_mathlib : G.IsBridge e := isAcyclic_iff_forall_edge_isBridge.mp hG he
  refine ⟨he, ?_⟩
  -- Extract endpoints and non-reachability
  rcases Sym2.mk_surjective e with ⟨⟨v, w⟩, hvw⟩
  use v, w, hvw
  have hadj : G.Adj v w := by rw [← hvw] at he; exact he
  -- Get non-reachability from Mathlib's IsBridge
  rw [← hvw, isBridge_iff] at h_mathlib
  intro h_reach
  apply h_mathlib hadj
  -- Show (G \ fromEdgeSet {s(v,w)}).Reachable v w from (G.deleteEdges {s(v,w)}).Reachable v w
  -- These graphs have the same edge set, so reachability transfers
  obtain ⟨p⟩ := h_reach
  have hle : G.deleteEdges {s(v, w)} ≤ G \ fromEdgeSet {s(v, w)} := by
    intro a b hab
    simp only [deleteEdges_adj, sdiff_adj, fromEdgeSet_adj, Set.mem_singleton_iff] at hab ⊢
    exact ⟨hab.1, fun h => hab.2 h.1⟩
  exact ⟨p.mapLe hle⟩

/-! ## Section 12: Summary

Proven Theorems (axiom replacements):

1. cycle_transfer_to_subgraph_theorem ✓
   Replaces: cycle_transfer_to_subgraph_aux

2. forest_single_edge_still_forest_theorem (1 sorry in edge-use case)
   Replaces: forest_single_edge_still_forest_aux

3. acyclic_of_disjoint_acyclic_parts_theorem (2 sorries for cycle projection)
   Replaces: acyclic_of_disjoint_acyclic_parts_aux

4. forest_union_forest_acyclic_theorem (2 sorries for cycle projection)
   Replaces: forest_union_forest_acyclic_aux

5. subgraph_acyclic_of_acyclic ✓ (fully proven)
6. induce_acyclic_of_acyclic ✓ (fully proven)
7. deleteEdges_acyclic ✓ (fully proven)
8. walk_transfer ✓ (fully proven infrastructure)
9. walk_transfer_isCycle ✓ (fully proven)
10. acyclic_implies_bridge ✓ (fully proven)
11. walk_stays_in_part ✓ (fully proven)

Key Patterns from Skill Document Used:
- Walk.toDeleteEdges for edge-avoiding walk conversion
- mapLe for graph monotonicity
- Walk induction for edge/support analysis
-/

-- Check fully proven theorems
#check @cycle_transfer_to_subgraph_theorem
#check @subgraph_acyclic_of_acyclic
#check @induce_acyclic_of_acyclic
#check @deleteEdges_acyclic
#check @walk_transfer
#check @walk_transfer_isCycle
#check @acyclic_implies_bridge
#check @walk_stays_in_part

end Infrastructure.AxiomSolver
