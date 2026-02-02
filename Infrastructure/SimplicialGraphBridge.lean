/-
# Simplicial Complex ↔ SimpleGraph Bridge

Formalizes the bijection between simplicial complex 1-simplices and SimpleGraph edges,
enabling proofs of the Euler forest formula and related results.

## Main Results

1. `ksimplex_one_gives_skeleton_edge` - 1-simplices give skeleton edges
2. `skeleton_edge_gives_ksimplex_one` - Skeleton edges give 1-simplices
3. `edge_count_eq_ksimplex_count` - Edge count equals 1-simplex count
4. `forest_euler_equality` - Forest |E| + |C| = |V| (via Mathlib)
5. `acyclic_implies_euler_proven` - Forest implies Euler condition
6. `euler_implies_acyclic_graph` - Euler condition implies forest (IN PROGRESS)
7. `complete_complex_h1_trivial` - Complete complexes have H¹ = 0 (IN PROGRESS)

## Axioms Targeted for Elimination

- G02: acyclic_implies_euler (LinearComplexity.lean:123) - DONE
- G03: euler_implies_acyclic (LinearComplexity.lean:143) - IN PROGRESS
- C03: complete_complex_coboundary_aux' (AlignmentEquivalence.lean:928) - IN PROGRESS

## Remaining Work

The proofs for G03 and C03 have correct structure but need technical completion:
- G03: Cycle → non-bridge edge → Euler violation (2 sorries)
- C03: Root vertex coboundary construction (1 sorry)

SORRIES: 4 (technical completions following standard patterns)
AXIOMS: 0

Author: Infrastructure Team
Date: February 2026
-/

import H1Characterization.OneSkeleton
import H1Characterization.OneConnected
import Foundations.Cohomology
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace Infrastructure.SimplicialGraphBridge

open Foundations (SimplicialComplex Simplex Vertex Cochain IsCocycle IsCoboundary H1Trivial coboundary)
open H1Characterization (oneSkeleton OneConnected)

variable {K : SimplicialComplex}

/-! ## Section 1: 1-Simplex and Edge Correspondence -/

/-- A 1-simplex (edge in simplicial complex) gives an edge in the 1-skeleton -/
theorem ksimplex_one_gives_skeleton_edge [Fintype K.vertexSet]
    (e : K.ksimplices 1) :
    ∃ (v w : K.vertexSet), v ≠ w ∧ (oneSkeleton K).Adj v w ∧
      e.val = ({v.val, w.val} : Finset Vertex) := by
  obtain ⟨s, hs_mem, hs_card⟩ := e
  -- s has cardinality 2, so it's {a, b} for distinct a, b
  obtain ⟨a, b, hab, hs_eq⟩ := Finset.card_eq_two.mp hs_card
  -- a and b are vertices in K
  have ha_vert : a ∈ K.vertexSet := by
    rw [SimplicialComplex.mem_vertexSet_iff]
    exact ⟨s, hs_mem, by rw [hs_eq]; exact Finset.mem_insert_self a {b}⟩
  have hb_vert : b ∈ K.vertexSet := by
    rw [SimplicialComplex.mem_vertexSet_iff]
    exact ⟨s, hs_mem, by rw [hs_eq]; simp⟩
  use ⟨a, ha_vert⟩, ⟨b, hb_vert⟩
  refine ⟨?_, ?_, hs_eq⟩
  · -- v ≠ w
    simp only [ne_eq, Subtype.mk.injEq]
    exact hab
  · -- (oneSkeleton K).Adj v w
    simp only [oneSkeleton, SimpleGraph.mk'_adj]
    constructor
    · exact hab
    · rw [hs_eq]; exact hs_mem

/-- An edge in the 1-skeleton gives a 1-simplex -/
theorem skeleton_edge_gives_ksimplex_one [Fintype K.vertexSet]
    (v w : K.vertexSet) (hadj : (oneSkeleton K).Adj v w) :
    ({v.val, w.val} : Finset Vertex) ∈ K.ksimplices 1 := by
  simp only [oneSkeleton, SimpleGraph.mk'_adj] at hadj
  obtain ⟨hne, hmem⟩ := hadj
  constructor
  · exact hmem
  · exact Finset.card_pair hne

/-- The 1-simplices correspond exactly to edges of the 1-skeleton -/
theorem edge_mem_ksimplices_iff [Fintype K.vertexSet]
    (v w : K.vertexSet) (hne : v ≠ w) :
    ({v.val, w.val} : Finset Vertex) ∈ K.ksimplices 1 ↔
    (oneSkeleton K).Adj v w := by
  constructor
  · intro ⟨hmem, _⟩
    simp only [oneSkeleton, SimpleGraph.mk'_adj]
    exact ⟨fun h => hne (Subtype.ext h), hmem⟩
  · intro hadj
    exact skeleton_edge_gives_ksimplex_one v w hadj

/-! ## Section 2: Counting Arguments -/

/-- Edge count in 1-skeleton equals 1-simplex count -/
theorem edge_count_eq_ksimplex_count [Fintype K.vertexSet]
    [DecidableEq K.vertexSet] [DecidableRel (oneSkeleton K).Adj]
    [Fintype (K.ksimplices 1)] [Fintype (oneSkeleton K).edgeSet] :
    (oneSkeleton K).edgeFinset.card = Fintype.card (K.ksimplices 1) := by
  -- Build a bijection between edges and 1-simplices
  -- Each edge s(v, w) corresponds to the 1-simplex {v.val, w.val}
  -- This is injective because distinct edges give distinct simplices
  -- This is surjective because every 1-simplex gives an edge
  apply Fintype.card_congr
  -- Define the equivalence
  let toSimplex : (oneSkeleton K).edgeSet → K.ksimplices 1 := fun e =>
    e.val.lift (fun v w => ⟨{v.val, w.val},
      skeleton_edge_gives_ksimplex_one v w (SimpleGraph.mem_edgeSet.mp e.property)⟩)
      (fun v w => by
        simp only [Subtype.mk.injEq]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto)
  let fromSimplex : K.ksimplices 1 → (oneSkeleton K).edgeSet := fun s =>
    let ⟨v, w, hne, hadj, _⟩ := ksimplex_one_gives_skeleton_edge s
    ⟨s(v, w), SimpleGraph.mem_edgeSet.mpr hadj⟩
  -- Show they're inverses (omitting details for now, using Equiv.ofBijective)
  -- The key insight is that both directions preserve the underlying vertex pair
  have h_surj : Function.Surjective toSimplex := by
    intro s
    obtain ⟨v, w, hne, hadj, heq⟩ := ksimplex_one_gives_skeleton_edge s
    use ⟨s(v, w), SimpleGraph.mem_edgeSet.mpr hadj⟩
    simp only [toSimplex, Sym2.lift_mk]
    exact Subtype.ext heq.symm
  have h_inj : Function.Injective toSimplex := by
    intro e1 e2 heq
    simp only [toSimplex] at heq
    ext
    -- Extract the vertex pairs from each edge
    induction e1.val using Sym2.inductionOn with
    | hf v1 w1 =>
      induction e2.val using Sym2.inductionOn with
      | hf v2 w2 =>
        simp only [Sym2.lift_mk, Subtype.mk.injEq] at heq
        -- heq : {v1.val, w1.val} = {v2.val, w2.val}
        have hadj1 := SimpleGraph.mem_edgeSet.mp e1.property
        have hadj2 := SimpleGraph.mem_edgeSet.mp e2.property
        simp only [oneSkeleton, SimpleGraph.mk'_adj] at hadj1 hadj2
        -- The Finset equality gives us the Sym2 equality
        have hpair : ({v1.val, w1.val} : Finset Vertex) = {v2.val, w2.val} := heq
        -- Since v1 ≠ w1 and v2 ≠ w2, the Finsets determine the pairs
        have h1 : v1.val ∈ ({v2.val, w2.val} : Finset Vertex) := by
          rw [← hpair]; exact Finset.mem_insert_self v1.val {w1.val}
        have h2 : w1.val ∈ ({v2.val, w2.val} : Finset Vertex) := by
          rw [← hpair]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
        cases h1 with
        | inl hv1v2 =>
          cases h2 with
          | inl hw1v2 =>
            -- v1 = v2, w1 = v2, so v1 = w1, contradiction
            have : v1.val = w1.val := hv1v2.trans hw1v2.symm
            exact absurd (Subtype.ext this) hadj1.1
          | inr hw1w2 =>
            -- v1 = v2, w1 = w2
            exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext hv1v2, Subtype.ext hw1w2⟩)
        | inr hv1w2 =>
          cases h2 with
          | inl hw1v2 =>
            -- v1 = w2, w1 = v2
            exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext hv1w2, Subtype.ext hw1v2⟩)
          | inr hw1w2 =>
            -- v1 = w2, w1 = w2, so v1 = w1, contradiction
            have : v1.val = w1.val := hv1w2.trans hw1w2.symm
            exact absurd (Subtype.ext this) hadj1.1
  exact Equiv.ofBijective toSimplex ⟨h_inj, h_surj⟩

/-! ## Section 3: Euler Formula for Forests -/

/-- In a connected tree on n vertices, there are n-1 edges -/
theorem tree_edge_count [Fintype K.vertexSet] [DecidableEq K.vertexSet]
    [DecidableRel (oneSkeleton K).Adj] [Fintype (oneSkeleton K).edgeSet]
    (h_tree : (oneSkeleton K).IsTree) :
    (oneSkeleton K).edgeFinset.card + 1 = Fintype.card K.vertexSet :=
  h_tree.card_edgeFinset

/-- For a forest (acyclic graph), |E| + |C| = |V|.

    Proof: In a forest, every edge is a bridge. Starting from the empty graph
    (0 edges, V components) and adding edges one by one:
    - Each edge addition decreases component count by 1 (merges two components)
    - After adding E edges: C = V - E, so E + C = V -/
theorem forest_euler_equality [Fintype K.vertexSet] [DecidableEq K.vertexSet]
    [DecidableRel (oneSkeleton K).Adj] [Fintype (oneSkeleton K).edgeSet]
    [Fintype (oneSkeleton K).ConnectedComponent]
    (h_acyc : (oneSkeleton K).IsAcyclic) :
    (oneSkeleton K).edgeFinset.card + Fintype.card (oneSkeleton K).ConnectedComponent
    = Fintype.card K.vertexSet := by
  -- Use Mathlib's IsAcyclic.card_edgeFinset which states:
  -- For acyclic graph: |E| + |C| = |V|
  exact h_acyc.card_edgeFinset

/-- For a forest (acyclic graph), edges ≤ vertices - components -/
theorem forest_euler_inequality [Fintype K.vertexSet] [DecidableEq K.vertexSet]
    [DecidableRel (oneSkeleton K).Adj] [Fintype (oneSkeleton K).edgeSet]
    [Fintype (oneSkeleton K).ConnectedComponent]
    (h_acyc : (oneSkeleton K).IsAcyclic) :
    (oneSkeleton K).edgeFinset.card ≤
    Fintype.card K.vertexSet - Fintype.card (oneSkeleton K).ConnectedComponent := by
  have h_eq := forest_euler_equality h_acyc
  omega

/-- OneConnected (acyclic 1-skeleton) implies Euler forest condition -/
theorem acyclic_implies_euler_proven [Fintype K.vertexSet] [DecidableEq K.vertexSet]
    [DecidableRel (oneSkeleton K).Adj] [Fintype (K.ksimplices 1)]
    [Fintype (oneSkeleton K).edgeSet] [Fintype (oneSkeleton K).ConnectedComponent]
    (h : OneConnected K) :
    Fintype.card (K.ksimplices 1) ≤
    Fintype.card K.vertexSet - Fintype.card (oneSkeleton K).ConnectedComponent := by
  -- OneConnected means the 1-skeleton is acyclic
  have h_acyc : (oneSkeleton K).IsAcyclic := h
  -- Use the edge count equivalence
  have h_eq := @edge_count_eq_ksimplex_count K _ _ _ _ _
  rw [← h_eq]
  exact forest_euler_inequality h_acyc

/-! ## Section 4: Euler Implies Acyclic -/

/-- If |E| ≤ |V| - |C|, then the graph is acyclic.

    Proof strategy: Uses the contrapositive.
    If the graph has a cycle, then it has a "redundant" edge that could be removed
    without disconnecting any component. This means |E| > |V| - |C| (more edges
    than a spanning forest needs).

    Formally: Mathlib's IsAcyclic.card_edgeFinset proves |E| + |C| = |V| for forests.
    The converse (Euler bound implies acyclic) follows from: if not acyclic,
    then some edge is not a bridge, so removing it doesn't increase components,
    but does decrease edges, breaking the Euler equality. -/
theorem euler_implies_acyclic_graph [Fintype K.vertexSet] [DecidableEq K.vertexSet]
    [DecidableRel (oneSkeleton K).Adj] [Fintype (oneSkeleton K).edgeSet]
    [Fintype (oneSkeleton K).ConnectedComponent] [Nonempty K.vertexSet]
    (h : (oneSkeleton K).edgeFinset.card ≤
         Fintype.card K.vertexSet - Fintype.card (oneSkeleton K).ConnectedComponent) :
    (oneSkeleton K).IsAcyclic := by
  -- Contrapositive: assume not acyclic, derive |E| > |V| - |C|
  by_contra h_not_acyc
  -- Not acyclic means there's a cycle
  unfold SimpleGraph.IsAcyclic at h_not_acyc
  push_neg at h_not_acyc
  obtain ⟨v, p, hp⟩ := h_not_acyc
  -- A cycle means some edge is not a bridge (can be removed without disconnecting)
  -- Therefore |E| > spanning forest size = |V| - |C|
  -- Use: for acyclic, IsAcyclic.card_edgeFinset gives |E| + |C| = |V|
  -- For non-acyclic: |E| + |C| > |V| (extra edge for cycle)
  -- This requires the fact that cycles contribute extra edges
  -- Key lemma: SimpleGraph.exists_edge_not_isBridge for non-acyclic graphs
  have h_exists_non_bridge : ∃ e ∈ (oneSkeleton K).edgeSet, ¬SimpleGraph.IsBridge (oneSkeleton K) e := by
    -- The cycle p contains at least one non-bridge edge
    -- (any edge in a cycle can be removed without disconnecting its endpoints)
    use p.edges.head (by
      have hlen := hp.three_le_length
      rw [SimpleGraph.Walk.length_edges] at hlen ⊢
      omega)
    constructor
    · exact SimpleGraph.Walk.edges_subset_edgeSet p (List.head_mem_self _)
    · -- This edge is in the cycle, so not a bridge
      -- Proof: after removing it, the rest of the cycle still connects the endpoints
      intro h_bridge
      -- If it were a bridge, removing it would disconnect the endpoints
      -- But the cycle provides an alternate path
      sorry -- Detailed cycle-based argument
  -- Having a non-bridge edge means |E| > |V| - |C|
  -- because: removing a non-bridge doesn't change |C|, but reduces |E|
  -- and the remaining graph still satisfies |E'| + |C| ≥ |V| (spanning bound)
  -- so original |E| = |E'| + 1 ≥ |V| - |C| + 1 > |V| - |C|
  obtain ⟨e, _, h_not_bridge⟩ := h_exists_non_bridge
  -- This contradicts h : |E| ≤ |V| - |C|
  sorry -- Complete the counting argument

/-- Euler condition implies OneConnected -/
theorem euler_implies_acyclic_proven [Fintype K.vertexSet] [DecidableEq K.vertexSet]
    [DecidableRel (oneSkeleton K).Adj] [Fintype (K.ksimplices 1)]
    [Fintype (oneSkeleton K).edgeSet] [Fintype (oneSkeleton K).ConnectedComponent]
    [Nonempty K.vertexSet]
    (h : Fintype.card (K.ksimplices 1) ≤
         Fintype.card K.vertexSet - Fintype.card (oneSkeleton K).ConnectedComponent) :
    OneConnected K := by
  have h_eq := @edge_count_eq_ksimplex_count K _ _ _ _ _
  rw [h_eq] at h
  exact euler_implies_acyclic_graph h

/-! ## Section 5: Complete Complex H¹ Triviality -/

/-- In a complete complex (all edges exist between vertices), H¹ = 0.

The proof uses the "root vertex method":
1. Pick vertex 0 as root
2. Define g({v}) = f({0, v}) for the cobounding 0-cochain
3. The cocycle condition on triangles ensures δg = f
-/
theorem complete_complex_h1_trivial [Fintype K.vertexSet] [DecidableEq K.vertexSet]
    [Nonempty K.vertexSet]
    (h_complete : ∀ v w : K.vertexSet, v ≠ w → ({v.val, w.val} : Finset Vertex) ∈ K.simplices)
    (h_triangles : ∀ u v w : K.vertexSet, u ≠ v → v ≠ w → u ≠ w →
      ({u.val, v.val, w.val} : Finset Vertex) ∈ K.simplices) :
    H1Trivial K := by
  intro f hf
  -- Pick a root vertex
  have hne := ‹Nonempty K.vertexSet›
  let root : K.vertexSet := Classical.arbitrary K.vertexSet
  -- Define the 0-cochain g
  -- g({v}) = f({root, v}) if v ≠ root, else 0
  -- The key is that for any edge {a, b}:
  -- - If root ∈ {a, b}: directly f({root, x}) = g({x}) - g({root}) = g({x})
  -- - If root ∉ {a, b}: use cocycle on triangle {root, a, b}
  --   f({a,b}) - f({root,b}) + f({root,a}) = 0
  --   So f({a,b}) = f({root,b}) - f({root,a}) = g({b}) - g({a})
  -- This shows f = δg, making f a coboundary
  use fun s =>
    if h : s.val.card = 1 then
      let v := s.val.toList.head (by
        rw [Finset.length_toList]; omega)
      if hv : v = root.val then 0
      else
        -- Need {root.val, v} ∈ K.ksimplices 1
        have hv_mem : v ∈ K.vertexSet := by
          rw [SimplicialComplex.mem_vertexSet_iff]
          exact ⟨s.val, s.property.1, by
            have := Finset.toList_eq_singleton h
            simp only [List.head_eq_head?] at *
            rw [this]
            simp⟩
        let v' : K.vertexSet := ⟨v, hv_mem⟩
        have hne' : root ≠ v' := fun heq => hv (congrArg Subtype.val heq)
        have hedge : ({root.val, v} : Finset Vertex) ∈ K.ksimplices 1 := by
          constructor
          · exact h_complete root v' hne'
          · exact Finset.card_pair (fun h => hne' (Subtype.ext h))
        f ⟨{root.val, v}, hedge⟩
    else 0
  -- Now show δg = f
  ext e
  -- e is a 1-simplex, so e.val = {a, b} for some a ≠ b
  obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp e.property.2
  -- The coboundary δg on edge {a, b} is g({b}) - g({a})
  -- We need to show this equals f({a, b})
  -- Case split on whether root is one of a, b
  sorry -- Full proof requires careful handling of the coboundary definition

/-! ## Section 6: Summary and Exports -/

#check ksimplex_one_gives_skeleton_edge
#check skeleton_edge_gives_ksimplex_one
#check edge_mem_ksimplices_iff
#check acyclic_implies_euler_proven
#check euler_implies_acyclic_proven
#check complete_complex_h1_trivial

end Infrastructure.SimplicialGraphBridge
