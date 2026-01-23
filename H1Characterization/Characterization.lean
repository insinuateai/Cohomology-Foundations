/-
  H1Characterization/Characterization.lean

  THE MAIN THEOREM: H¹(K) = 0 ↔ OneConnected K

  Note: Test cases axiomatized due to mathlib 4.16.0 API changes.
  The main theorem is fully proven.
-/

import H1Characterization.ForestCoboundary
import H1Characterization.CycleCochain.Definitions

namespace H1Characterization

/-! ## Main Characterization -/

theorem h1_trivial_iff_oneConnected (K : SimplicialComplex) [Nonempty K.vertexSet] :
    H1Trivial K ↔ OneConnected K := by
  constructor
  · exact h1_trivial_implies_oneConnected K
  · exact fun hK => oneConnected_implies_h1_trivial K hK

theorem h1_trivial_iff_acyclic (K : SimplicialComplex) [Nonempty K.vertexSet] :
    H1Trivial K ↔ (oneSkeleton K).IsAcyclic := h1_trivial_iff_oneConnected K

/-! ## Test Cases -/

/-!
The hollow triangle (boundary of a 2-simplex without the interior) is NOT one-connected.
It has a cycle: 0 → 1 → 2 → 0
Therefore H¹(hollow triangle) ≠ 0

Construction: A simplicial complex with vertices {0, 1, 2} and edges {0,1}, {1,2}, {0,2}
but no 2-simplex {0,1,2}. The 1-skeleton is a triangle (cycle), hence not acyclic.
-/
theorem hollowTriangle_not_oneConnected_axiom :
    ∃ (K : SimplicialComplex) (_ : Nonempty K.vertexSet), ¬OneConnected K := by
  -- Construct the hollow triangle: vertices {0}, {1}, {2} and edges {0,1}, {1,2}, {0,2}
  -- but NO 2-simplex {0,1,2}
  let hollowTriangle : SimplicialComplex := {
    simplices := {∅, {0}, {1}, {2}, {0, 1}, {1, 2}, {0, 2}}
    has_vertices := by
      intro s hs v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (Finset.not_mem_empty v hv).elim
      · simp only [Finset.mem_singleton] at hv; rw [hv]; right; left; rfl
      · simp only [Finset.mem_singleton] at hv; rw [hv]; right; right; left; rfl
      · simp only [Finset.mem_singleton] at hv; rw [hv]; right; right; right; left; rfl
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> [right; left; rfl; right; right; left; rfl]
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> [right; right; left; rfl; right; right; right; left; rfl]
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> [right; left; rfl; right; right; right; left; rfl]
    down_closed := by
      intro s hs i
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact i.elim0  -- ∅ has no faces
      · fin_cases i; left; simp only [Foundations.Simplex.face, Finset.sort_singleton, List.get_cons_zero]; rfl
      · fin_cases i; left; simp only [Foundations.Simplex.face, Finset.sort_singleton, List.get_cons_zero]; rfl
      · fin_cases i; left; simp only [Foundations.Simplex.face, Finset.sort_singleton, List.get_cons_zero]; rfl
      · -- {0, 1}: faces are {1} and {0}
        fin_cases i
        · right; right; left; simp only [Foundations.Simplex.face]; native_decide
        · right; left; simp only [Foundations.Simplex.face]; native_decide
      · -- {1, 2}: faces are {2} and {1}
        fin_cases i
        · right; right; right; left; simp only [Foundations.Simplex.face]; native_decide
        · right; right; left; simp only [Foundations.Simplex.face]; native_decide
      · -- {0, 2}: faces are {2} and {0}
        fin_cases i
        · right; right; right; left; simp only [Foundations.Simplex.face]; native_decide
        · right; left; simp only [Foundations.Simplex.face]; native_decide
  }

  use hollowTriangle

  -- Prove Nonempty vertexSet
  have h_nonempty : Nonempty hollowTriangle.vertexSet := by
    use ⟨0, by simp only [Foundations.SimplicialComplex.vertexSet, Set.mem_setOf_eq,
                          Foundations.Simplex.vertex, Set.mem_insert_iff, Set.mem_singleton_iff]
               right; left; rfl⟩
  use h_nonempty

  -- Prove ¬OneConnected by constructing a cycle
  intro hOC
  -- hOC : OneConnected hollowTriangle means no cycles exist
  -- But we can construct the cycle 0 → 1 → 2 → 0

  -- First, get the vertices as elements of vertexSet
  have h0 : (0 : ℕ) ∈ hollowTriangle.vertexSet := by
    simp only [Foundations.SimplicialComplex.vertexSet, Set.mem_setOf_eq, Foundations.Simplex.vertex,
               Set.mem_insert_iff, Set.mem_singleton_iff]
    right; left; rfl
  have h1 : (1 : ℕ) ∈ hollowTriangle.vertexSet := by
    simp only [Foundations.SimplicialComplex.vertexSet, Set.mem_setOf_eq, Foundations.Simplex.vertex,
               Set.mem_insert_iff, Set.mem_singleton_iff]
    right; right; left; rfl
  have h2 : (2 : ℕ) ∈ hollowTriangle.vertexSet := by
    simp only [Foundations.SimplicialComplex.vertexSet, Set.mem_setOf_eq, Foundations.Simplex.vertex,
               Set.mem_insert_iff, Set.mem_singleton_iff]
    right; right; right; left; rfl

  let v0 : hollowTriangle.vertexSet := ⟨0, h0⟩
  let v1 : hollowTriangle.vertexSet := ⟨1, h1⟩
  let v2 : hollowTriangle.vertexSet := ⟨2, h2⟩

  -- Adjacencies in the 1-skeleton
  have adj01 : (oneSkeleton hollowTriangle).Adj v0 v1 := by
    simp only [oneSkeleton, SimpleGraph.Adj]
    constructor
    · intro h; injection h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      right; right; right; right; left; rfl
  have adj12 : (oneSkeleton hollowTriangle).Adj v1 v2 := by
    simp only [oneSkeleton, SimpleGraph.Adj]
    constructor
    · intro h; injection h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      right; right; right; right; right; left; rfl
  have adj20 : (oneSkeleton hollowTriangle).Adj v2 v0 := by
    simp only [oneSkeleton, SimpleGraph.Adj]
    constructor
    · intro h; injection h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      -- {2, 0} = {0, 2}
      right; right; right; right; right; right
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; omega

  -- Construct the walk 0 → 1 → 2 → 0
  let walk012 : (oneSkeleton hollowTriangle).Walk v0 v0 :=
    SimpleGraph.Walk.cons adj01 (SimpleGraph.Walk.cons adj12 (SimpleGraph.Walk.cons adj20 SimpleGraph.Walk.nil))

  -- Show it's a cycle
  have h_cycle : walk012.IsCycle := by
    constructor
    · -- IsTrail: no repeated edges
      constructor
      · -- IsPath for the underlying structure... actually IsTrail means edges_nodup
        simp only [SimpleGraph.Walk.isTrail_def, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
                   List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
                   List.nodup_nil, and_true, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
        constructor
        · -- s(0,1) ≠ s(1,2) and s(0,1) ≠ s(2,0)
          constructor
          · simp only [not_or, not_and]; constructor <;> intro <;> omega
          · simp only [not_or, not_and]; constructor <;> intro <;> omega
        · -- s(1,2) ≠ s(2,0)
          constructor
          · simp only [not_or, not_and]; constructor <;> intro <;> omega
          · trivial
    · constructor
      · -- length ≥ 3
        simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
        omega
      · -- support nodup (except endpoints)
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons,
                   List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
                   List.nodup_nil, and_true]
        constructor
        · intro h; rcases h with rfl | rfl <;> simp_all
        · constructor
          · intro h; rcases h with rfl; simp_all
          · trivial

  -- Apply OneConnected (which says no cycles exist)
  exact hOC v0 walk012 h_cycle

/-!
A single edge complex IS one-connected (acyclic).
It's a tree with two vertices and one edge.
Therefore H¹(single edge) = 0

Construction: A simplicial complex with vertices {0, 1} and edge {0,1}.
The 1-skeleton is a path (tree), hence acyclic.
-/
theorem singleEdge_oneConnected_axiom :
    ∃ (K : SimplicialComplex) (_ : Nonempty K.vertexSet), OneConnected K := by
  -- A single edge {0, 1} forms an acyclic graph (no cycles possible with 2 vertices)
  -- This is a tree (specifically, a path of length 1)

  -- Define the single edge complex: empty set, vertices {0}, {1} and edge {0, 1}
  let singleEdge : SimplicialComplex := {
    simplices := {∅, {0}, {1}, {0, 1}}
    has_vertices := by
      intro s hs v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · -- s = ∅: no vertices, vacuously true
        exact (Finset.not_mem_empty v hv).elim
      · -- s = {0}
        simp only [Finset.mem_singleton] at hv
        rw [hv]; right; left; rfl
      · -- s = {1}
        simp only [Finset.mem_singleton] at hv
        rw [hv]; right; right; left; rfl
      · -- s = {0, 1}
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · right; left; rfl
        · right; right; left; rfl
    down_closed := by
      intro s hs i
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
      rcases hs with rfl | rfl | rfl | rfl
      · -- s = ∅, card = 0, so Fin 0 is empty - vacuously true
        exact i.elim0
      · -- s = {0}, card = 1, i : Fin 1
        fin_cases i
        -- face {0} ⟨0, _⟩ = ∅
        left
        simp only [Foundations.Simplex.face, Finset.sort_singleton, List.get_cons_zero]
        rfl
      · -- s = {1}, card = 1, i : Fin 1
        fin_cases i
        -- face {1} ⟨0, _⟩ = ∅
        left
        simp only [Foundations.Simplex.face, Finset.sort_singleton, List.get_cons_zero]
        rfl
      · -- s = {0, 1}, card = 2, i : Fin 2
        fin_cases i
        · -- i = 0: face removes element at index 0 (which is 0), giving {1}
          right; right; left
          simp only [Foundations.Simplex.face]
          -- sorted {0,1} = [0, 1], get 0 = 0, erase 0 from {0,1} = {1}
          native_decide
        · -- i = 1: face removes element at index 1 (which is 1), giving {0}
          right; left
          simp only [Foundations.Simplex.face]
          native_decide
  }

  use singleEdge

  -- Prove Nonempty K.vertexSet: 0 is a vertex
  have h_nonempty : Nonempty singleEdge.vertexSet := by
    use ⟨0, by simp only [Foundations.SimplicialComplex.vertexSet, Set.mem_setOf_eq,
                          Foundations.Simplex.vertex, Set.mem_insert_iff, Set.mem_singleton_iff]
               right; left; rfl⟩
  use h_nonempty

  -- Prove OneConnected: the 1-skeleton is acyclic
  -- A graph with 2 vertices cannot have a cycle (cycles need ≥ 3 vertices)
  unfold OneConnected
  intro v p hp
  -- A cycle has length ≥ 3
  have h_len := hp.three_le_length
  -- A cycle is a trail (no repeated edges)
  have h_trail := hp.isTrail
  -- The 1-skeleton has only 2 vertices and 1 edge
  -- A trail in a graph with 1 edge has length ≤ 1
  -- But cycles need length ≥ 3, contradiction

  -- The edges_nodup property means each Sym2 edge appears at most once
  have h_edges_nodup := h_trail.edges_nodup
  -- p.edges is the list of Sym2 edges traversed
  -- Its length equals p.length, and it has no duplicates
  -- So p.length ≤ (number of distinct edges in graph)

  -- In singleEdge, the only edge is {0,1}
  -- So the 1-skeleton has exactly one edge: s(0,1)
  -- Therefore any nodup edge list has length ≤ 1

  -- edges_nodup means p.edges.Nodup
  -- p.edges.length = p.length
  -- If all elements of p.edges are in {s(0,1)}, then length ≤ 1

  exfalso
  -- We show p.length ≤ 2 (at most 2 darts on one edge: 0→1 and 1→0)
  -- But actually we need p.length ≤ 1 for edges (Sym2)

  -- The key insight: p.edges are Sym2 values (undirected edges)
  -- There's only one Sym2 edge: s(0,1) = s(1,0)
  -- So p.edges can only contain this one value
  -- If p.edges.Nodup and all elements equal s(0,1), then p.edges.length ≤ 1

  have h_len_edges : p.edges.length = p.length := SimpleGraph.Walk.length_edges p
  have h_bound : p.edges.length ≤ 1 := by
    by_contra h_gt
    push_neg at h_gt
    -- p.edges has length ≥ 2 and is nodup
    -- All edges in the 1-skeleton of singleEdge are {0,1}
    -- So p.edges contains ≥ 2 copies of s(0,1)... but it's nodup!
    -- Actually, we need to show all edges in p.edges equal s(0,1)
    -- Then nodup + length ≥ 2 is a contradiction

    -- Get two distinct edges from p.edges
    have h_two := List.length_pos_iff_ne_nil.mpr (by omega : p.edges.length ≠ 0)
    obtain ⟨e, he⟩ := List.exists_mem_of_length_pos h_two
    -- e is an edge in the walk, so it's an edge in the 1-skeleton
    -- The 1-skeleton of singleEdge only has one edge

    -- Every edge in the walk is in the 1-skeleton
    -- And the 1-skeleton of singleEdge has only vertices 0, 1 and edge {0,1}
    -- So every edge e in p.edges must be s(0,1)

    -- Since p.edges.Nodup and all elements are s(0,1),
    -- p.edges can have at most 1 element
    have h_all_same : ∀ e ∈ p.edges, e = Sym2.mk (0, 1) := by
      intro e he
      -- e is an edge traversed in walk p
      -- p is a walk in (oneSkeleton singleEdge)
      -- So e connects two adjacent vertices in the 1-skeleton
      -- The only edge in singleEdge's 1-skeleton is {0,1}
      have h_edge_in := SimpleGraph.Walk.edges_subset_edgeSet p he
      -- h_edge_in : e ∈ (oneSkeleton singleEdge).edgeSet
      simp only [SimpleGraph.edgeSet, oneSkeleton, Set.mem_setOf_eq, Sym2.mem_iff,
                 Set.mem_insert_iff, Set.mem_singleton_iff] at h_edge_in
      -- e = s(v, w) where v ≠ w and {v, w} ∈ singleEdge.simplices
      obtain ⟨v, w, hvw, hsimp, he_eq⟩ := h_edge_in
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsimp
      -- hsimp : {v.val, w.val} = ∅ ∨ ... ∨ {v.val, w.val} = {0, 1}
      rcases hsimp with h | h | h | h
      · -- {v.val, w.val} = ∅ : impossible since v, w exist
        have : v.val ∈ ({v.val, w.val} : Finset ℕ) := Finset.mem_insert_self _ _
        rw [h] at this
        exact Finset.not_mem_empty _ this
      · -- {v.val, w.val} = {0} : impossible since v ≠ w
        have hcard : ({v.val, w.val} : Finset ℕ).card = 1 := by rw [h]; rfl
        have hcard2 : ({v.val, w.val} : Finset ℕ).card = 2 := Finset.card_pair (Subtype.val_injective.ne hvw)
        omega
      · -- {v.val, w.val} = {1} : impossible since v ≠ w
        have hcard : ({v.val, w.val} : Finset ℕ).card = 1 := by rw [h]; rfl
        have hcard2 : ({v.val, w.val} : Finset ℕ).card = 2 := Finset.card_pair (Subtype.val_injective.ne hvw)
        omega
      · -- {v.val, w.val} = {0, 1} : so e = s(0, 1)
        rw [he_eq]
        -- v.val and w.val are 0 and 1 (in some order)
        have hv01 : v.val ∈ ({0, 1} : Finset ℕ) := by rw [← h]; exact Finset.mem_insert_self _ _
        have hw01 : w.val ∈ ({0, 1} : Finset ℕ) := by rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv01 hw01
        rcases hv01, hw01 with ⟨rfl | rfl, rfl | rfl⟩
        · exact (hvw rfl).elim
        · rfl
        · simp only [Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk, Prod.mk.injEq, and_self, or_true]
        · exact (hvw rfl).elim

    -- Now: p.edges.Nodup and all elements equal Sym2.mk (0,1)
    -- So p.edges has at most 1 element
    have h_at_most_one := List.Nodup.eq_singleton_or_eq_nil_of_forall_eq h_edges_nodup (Sym2.mk (0, 1)) h_all_same
    rcases h_at_most_one with h_single | h_nil
    · rw [h_single] at h_gt; simp at h_gt
    · rw [h_nil] at h_gt; simp at h_gt

  omega

/-! ## Summary -/

#check h1_trivial_iff_oneConnected  -- THE MAIN THEOREM

/-!
The main theorem states that for a simplicial complex K:

**H¹(K) = 0 if and only if the 1-skeleton is acyclic (a forest)**

This is the fundamental characterization of first cohomology in simplicial cohomology theory.

- Forward direction (h1_trivial_implies_oneConnected):
  If H¹ = 0, then every cocycle is a coboundary. Cycles in the 1-skeleton give rise
  to non-trivial cocycles (cycle indicators), so there can be no cycles.

- Reverse direction (oneConnected_implies_h1_trivial):
  If the 1-skeleton is acyclic, we can construct an explicit coboundary witness
  for any cocycle using path integrals from a root vertex.
-/

end H1Characterization
