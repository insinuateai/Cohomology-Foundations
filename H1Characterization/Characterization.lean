/-
  H1Characterization/Characterization.lean

  THE MAIN THEOREM: H¹(K) = 0 ↔ OneConnected K

  Note: Test cases axiomatized due to mathlib 4.16.0 API changes.
  The main theorem is fully proven.
-/

import H1Characterization.ForestCoboundary
import H1Characterization.CycleCochain.Definitions
import Perspective.AlignmentEquivalence

namespace H1Characterization

-- Bring in hollowTriangle from Perspective
open Perspective (hollowTriangle)

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

/-- There exists a simplicial complex that is not one-connected.
    Example: the hollow triangle with 3 vertices and 3 edges forming a cycle. -/
theorem hollowTriangle_not_oneConnected_axiom :
    ∃ (K : SimplicialComplex) (_ : Nonempty K.vertexSet), ¬OneConnected K := by
  -- First show hollowTriangle has nonempty vertex set
  have hv0 : (0 : Vertex) ∈ hollowTriangle.vertexSet := by
    rw [Foundations.SimplicialComplex.mem_vertexSet_iff]
    simp only [Foundations.Simplex.vertex, hollowTriangle]
    right; left; rfl
  have hv1 : (1 : Vertex) ∈ hollowTriangle.vertexSet := by
    rw [Foundations.SimplicialComplex.mem_vertexSet_iff]
    simp only [Foundations.Simplex.vertex, hollowTriangle]
    right; right; left; rfl
  have hv2 : (2 : Vertex) ∈ hollowTriangle.vertexSet := by
    rw [Foundations.SimplicialComplex.mem_vertexSet_iff]
    simp only [Foundations.Simplex.vertex, hollowTriangle]
    right; right; right; left; rfl
  refine ⟨hollowTriangle, ⟨⟨0, hv0⟩⟩, ?_⟩
  -- Show not one-connected by constructing a cycle 0 → 1 → 2 → 0
  rw [not_oneConnected_iff_exists_cycle]
  -- Define vertices as elements of vertexSet
  let v0 : hollowTriangle.vertexSet := ⟨0, hv0⟩
  let v1 : hollowTriangle.vertexSet := ⟨1, hv1⟩
  let v2 : hollowTriangle.vertexSet := ⟨2, hv2⟩
  use v0
  -- Build the walk 0 → 1 → 2 → 0
  -- We need adjacencies
  have hne01 : (0 : Vertex) ≠ 1 := by native_decide
  have hne12 : (1 : Vertex) ≠ 2 := by native_decide
  have hne20 : (2 : Vertex) ≠ 0 := by native_decide
  -- hollowTriangle.simplices = {∅, {0}, {1}, {2}, {0,1}, {1,2}, {0,2}}
  -- Index: ∅=0, {0}=1, {1}=2, {2}=3, {0,1}=4, {1,2}=5, {0,2}=6
  have hedge01 : ({0, 1} : Simplex) ∈ hollowTriangle.simplices := by
    simp only [hollowTriangle]
    -- Need to reach element 4 (0-indexed: left=first, right=rest)
    right; right; right; right; left; rfl
  have hedge12 : ({1, 2} : Simplex) ∈ hollowTriangle.simplices := by
    simp only [hollowTriangle]
    right; right; right; right; right; left; rfl
  have hedge02 : ({0, 2} : Simplex) ∈ hollowTriangle.simplices := by
    simp only [hollowTriangle]
    right; right; right; right; right; right; rfl
  have hedge20 : ({2, 0} : Simplex) ∈ hollowTriangle.simplices := by
    convert hedge02 using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have h01 : (oneSkeleton hollowTriangle).Adj v0 v1 := ⟨hne01, hedge01⟩
  have h12 : (oneSkeleton hollowTriangle).Adj v1 v2 := ⟨hne12, hedge12⟩
  have h20 : (oneSkeleton hollowTriangle).Adj v2 v0 := ⟨hne20, hedge20⟩
  -- Build the walk
  let w : Walk hollowTriangle v0 v0 :=
    SimpleGraph.Walk.cons h01 (SimpleGraph.Walk.cons h12 (SimpleGraph.Walk.cons h20 SimpleGraph.Walk.nil))
  use w
  -- Show it's a cycle: IsCycle = IsCircuit + support_nodup
  constructor
  · -- IsCircuit: IsTrail + ne_nil
    constructor
    · -- IsTrail: no repeated edges
      constructor
      -- Show edges are nodup
      -- First simplify the edges expression
      show (SimpleGraph.Walk.cons h01 (SimpleGraph.Walk.cons h12 (SimpleGraph.Walk.cons h20 SimpleGraph.Walk.nil))).edges.Nodup
      rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons,
          SimpleGraph.Walk.edges_nil]
      -- edges = [s(v0,v1), s(v1,v2), s(v2,v0)]
      refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩⟩
      · -- s(v0,v1) ∉ [s(v1,v2), s(v2,v0)]
        intro h
        simp only [List.mem_cons] at h
        rcases h with h1 | h1
        · -- s(v0,v1) = s(v1,v2)
          have : v0 = v1 ∨ (v0 = v2 ∧ v1 = v1) := by
            rw [Sym2.eq_iff] at h1
            rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
          rcases this with h | ⟨h, _⟩
          · exact hne01 (congrArg Subtype.val h)
          · exact hne20.symm (congrArg Subtype.val h)
        · -- s(v0,v1) = s(v2,v0)
          have : (v0 = v2 ∧ v1 = v0) ∨ (v0 = v0 ∧ v1 = v2) := by
            rw [Sym2.eq_iff] at h1
            rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
          rcases this with ⟨_, h⟩ | ⟨_, h⟩
          · exact hne01 (congrArg Subtype.val h).symm
          · exact hne12 (congrArg Subtype.val h)
      · -- s(v1,v2) ∉ [s(v2,v0)]
        intro h
        simp only [List.mem_singleton] at h
        have : (v1 = v2 ∧ v2 = v0) ∨ (v1 = v0 ∧ v2 = v2) := by
          rw [Sym2.eq_iff] at h
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
        rcases this with ⟨h, _⟩ | ⟨h, _⟩
        · exact hne12 (congrArg Subtype.val h)
        · exact hne01.symm (congrArg Subtype.val h)
    · -- ne_nil: w ≠ nil
      simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  · -- support_nodup: tail of support is nodup
    -- support = [v0, v1, v2, v0], tail = [v1, v2, v0]
    show (SimpleGraph.Walk.cons h01 (SimpleGraph.Walk.cons h12 (SimpleGraph.Walk.cons h20 SimpleGraph.Walk.nil))).support.tail.Nodup
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.tail_cons]
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩⟩
    · -- v1 ∉ [v2, v0]
      intro h
      -- h : v1 ∈ [v2, v0] = v1 = v2 ∨ v1 = v0
      rw [List.mem_cons, List.mem_singleton] at h
      rcases h with h | h
      · exact hne12 (Subtype.ext_iff.mp h)
      · exact hne01.symm (Subtype.ext_iff.mp h)
    · -- v2 ∉ [v0]
      intro h
      rw [List.mem_singleton] at h
      exact hne20 (Subtype.ext_iff.mp h)

/-!
A single edge complex IS one-connected (acyclic).
It's a tree with two vertices and one edge.
Therefore H¹(single edge) = 0

Construction: A simplicial complex with vertices {0, 1} and edge {0,1}.
The 1-skeleton is a path (tree), hence acyclic.
-/

/-- The single edge complex: 2 vertices, 1 edge, forms a tree. -/
def singleEdge : SimplicialComplex where
  simplices := {∅, {0}, {1}, {0,1}}
  has_vertices := by
    intro s hs v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
    rcases hs with rfl | rfl | rfl | rfl
    · exact absurd hv (Finset.notMem_empty v)
    · simp only [Finset.mem_singleton] at hv; subst hv; right; left; rfl
    · simp only [Finset.mem_singleton] at hv; subst hv; right; right; left; rfl
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · right; left; rfl
      · right; right; left; rfl
  down_closed := by
    intro s hs i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
    rcases hs with rfl | rfl | rfl | rfl
    · exact i.elim0
    · have hi : i = ⟨0, by native_decide⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
      subst hi
      have h_face : Foundations.Simplex.face ({0} : Simplex) ⟨0, by native_decide⟩ = ∅ := by native_decide
      left; exact h_face
    · have hi : i = ⟨0, by native_decide⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
      subst hi
      have h_face : Foundations.Simplex.face ({1} : Simplex) ⟨0, by native_decide⟩ = ∅ := by native_decide
      left; exact h_face
    · have h0 : Foundations.Simplex.face ({0, 1} : Simplex) ⟨0, by native_decide⟩ = {1} := by native_decide
      have h1 : Foundations.Simplex.face ({0, 1} : Simplex) ⟨1, by native_decide⟩ = {0} := by native_decide
      match i with
      | ⟨0, _⟩ => right; right; left; exact h0
      | ⟨1, _⟩ => right; left; exact h1

/-- There exists a simplicial complex that is one-connected.
    Example: a single edge with 2 vertices. -/
theorem singleEdge_oneConnected_axiom :
    ∃ (K : SimplicialComplex) (_ : Nonempty K.vertexSet), OneConnected K := by
  -- Show singleEdge has nonempty vertex set
  have hv0 : (0 : Vertex) ∈ singleEdge.vertexSet := by
    rw [Foundations.SimplicialComplex.mem_vertexSet_iff]
    simp only [Foundations.Simplex.vertex, singleEdge]
    right; left; rfl
  have hv1 : (1 : Vertex) ∈ singleEdge.vertexSet := by
    rw [Foundations.SimplicialComplex.mem_vertexSet_iff]
    simp only [Foundations.Simplex.vertex, singleEdge]
    right; right; left; rfl
  refine ⟨singleEdge, ⟨⟨0, hv0⟩⟩, ?_⟩
  -- Show one-connected: no cycles exist in a single-edge graph
  -- Key insight: singleEdge has only edge {0,1}
  -- A cycle needs ≥ 3 edges, but singleEdge has only 1 edge
  -- Any trail with ≥ 2 edges would repeat the only edge, violating IsTrail
  rw [oneConnected_iff_no_cycles]
  intro v p hp
  -- A cycle needs at least 3 edges (length ≥ 3)
  have h_cycle_len := hp.three_le_length
  -- p.edges.length = p.length for walks
  have h_edges_eq_len : p.edges.length = p.length := SimpleGraph.Walk.length_edges p
  -- But singleEdge has only 1 edge, so any trail can use at most 1 edge
  -- We show p.length ≤ 1, contradicting h_cycle_len
  have h_at_most_one : p.length ≤ 1 := by
    by_contra h_gt
    push_neg at h_gt
    have h_len : 2 ≤ p.length := h_gt
    rw [← h_edges_eq_len] at h_len
    have h_edge0 : 0 < p.edges.length := Nat.lt_of_lt_of_le (by norm_num : 0 < 2) h_len
    have h_edge1 : 1 < p.edges.length := Nat.lt_of_lt_of_le (by norm_num : 1 < 2) h_len
    let e0 := p.edges.get ⟨0, h_edge0⟩
    let e1 := p.edges.get ⟨1, h_edge1⟩
    have htrail := hp.1.1  -- IsTrail
    rw [SimpleGraph.Walk.isTrail_def] at htrail
    have h_ne_idx : (⟨0, h_edge0⟩ : Fin p.edges.length) ≠ ⟨1, h_edge1⟩ := by
      intro h; exact absurd (Fin.ext_iff.mp h) (by norm_num : (0 : ℕ) ≠ 1)
    have h_e0_mem : e0 ∈ p.edges := List.get_mem p.edges ⟨0, h_edge0⟩
    have h_e1_mem : e1 ∈ p.edges := List.get_mem p.edges ⟨1, h_edge1⟩
    -- Any Adj relation in singleEdge must be between vertices 0 and 1
    -- so all edges in the walk are the same Sym2 element
    have h_only_edge : ∀ (a b : singleEdge.vertexSet),
        (oneSkeleton singleEdge).Adj a b → s(a, b) = s(⟨0, hv0⟩, ⟨1, hv1⟩) := by
      intro a b hab
      obtain ⟨hne, hmem⟩ := hab
      simp only [singleEdge, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h_empty | h_0 | h_1 | h01
      · exfalso; have : a.val ∈ (∅ : Finset ℕ) := by rw [← h_empty]; exact Finset.mem_insert_self _ _
        exact Finset.notMem_empty _ this
      · exfalso
        have ha : a.val = 0 := Finset.mem_singleton.mp (by rw [← h_0]; exact Finset.mem_insert_self _ _)
        have hb : b.val = 0 := Finset.mem_singleton.mp (by rw [← h_0]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        exact hne (ha.trans hb.symm)
      · exfalso
        have ha : a.val = 1 := Finset.mem_singleton.mp (by rw [← h_1]; exact Finset.mem_insert_self _ _)
        have hb : b.val = 1 := Finset.mem_singleton.mp (by rw [← h_1]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        exact hne (ha.trans hb.symm)
      · have ha : a.val ∈ ({0, 1} : Finset ℕ) := by rw [← h01]; exact Finset.mem_insert_self _ _
        have hb : b.val ∈ ({0, 1} : Finset ℕ) := by rw [← h01]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1
        · exact absurd (ha0.trans hb0.symm) hne
        · -- a.val = 0, b.val = 1: s(a,b) = s(0,1)
          have heq_a : a = ⟨0, hv0⟩ := Subtype.ext ha0
          have heq_b : b = ⟨1, hv1⟩ := Subtype.ext hb1
          simp only [heq_a, heq_b]
        · -- a.val = 1, b.val = 0: s(a,b) = s(1,0) = s(0,1)
          have heq_a : a = ⟨1, hv1⟩ := Subtype.ext ha1
          have heq_b : b = ⟨0, hv0⟩ := Subtype.ext hb0
          simp only [heq_a, heq_b, Sym2.eq_swap]
        · exact absurd (ha1.trans hb1.symm) hne
    -- All edges in the walk equal s(⟨0,_⟩, ⟨1,_⟩)
    have h_all_same : ∀ e ∈ p.edges, e = s(⟨0, hv0⟩, ⟨1, hv1⟩) := by
      intro e he
      -- Use induction on Sym2 to extract x, y such that e = s(x, y)
      induction e using Sym2.inductionOn with
      | hf x y =>
        -- s(x, y) ∈ p.edges means x, y are adjacent in the walk
        have hadj := SimpleGraph.Walk.adj_of_mem_edges p he
        exact h_only_edge x y hadj
    -- e0 = e1 since both equal the only edge
    have h_eq : e0 = e1 := (h_all_same e0 h_e0_mem).trans (h_all_same e1 h_e1_mem).symm
    -- But they're at different positions in a nodup list - contradiction
    exact h_ne_idx (htrail.get_inj_iff.mp h_eq)
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
