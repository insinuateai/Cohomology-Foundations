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
        simp only [List.mem_cons, List.mem_singleton] at h
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
      exact fun h => SimpleGraph.Walk.noConfusion h
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
    · exact absurd hv (Finset.not_mem_empty v)
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
  -- Any closed non-nil walk must traverse this edge at least twice, violating IsTrail
  rw [oneConnected_iff_no_cycles]
  intro v p hp
  obtain ⟨⟨htrail, hne_nil⟩, _hnodup⟩ := hp
  -- Case analysis on walk structure
  cases p with
  | nil => exact hne_nil rfl
  | cons h p' =>
    -- h : Adj v w for some w, meaning edge {v.val, w.val} ∈ singleEdge.simplices
    obtain ⟨hne_vw, hedge⟩ := h
    -- The only 2-element simplex in singleEdge is {0,1}
    have hedge_is_01 : ({v.val, w.val} : Finset ℕ) = {0, 1} := by
      simp only [singleEdge] at hedge
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hedge
      rcases hedge with rfl | rfl | rfl | rfl
      · have : v.val ∈ (∅ : Finset ℕ) := by rw [← hedge]; exact Finset.mem_insert_self v.val {w.val}
        exact absurd this (Finset.not_mem_empty v.val)
      · have hv_in : v.val ∈ ({0} : Finset ℕ) := by rw [← hedge]; exact Finset.mem_insert_self v.val {w.val}
        have hw_in : w.val ∈ ({0} : Finset ℕ) := by rw [← hedge]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w.val)
        simp only [Finset.mem_singleton] at hv_in hw_in
        exact absurd (hv_in.symm.trans hw_in) hne_vw
      · have hv_in : v.val ∈ ({1} : Finset ℕ) := by rw [← hedge]; exact Finset.mem_insert_self v.val {w.val}
        have hw_in : w.val ∈ ({1} : Finset ℕ) := by rw [← hedge]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w.val)
        simp only [Finset.mem_singleton] at hv_in hw_in
        exact absurd (hv_in.symm.trans hw_in) hne_vw
      · rfl
    -- p' : Walk from w back to v
    cases p' with
    | nil =>
      -- p' = nil means w = v, contradicting hne_vw
      rename_i heq
      have : v.val = w.val := congrArg Subtype.val heq
      exact hne_vw this
    | cons h' p'' =>
      -- p' = cons h' p'' means another edge h' : Adj w w' for some w'
      -- Since singleEdge only has edge {0,1}, both h and h' use this edge
      -- This means edges of p contains s(v,w) and s(w,w') which are both s(0,1)
      -- violating the trail condition (edges.Nodup)
      rename_i w' h' p''
      obtain ⟨hne', hedge'⟩ := h'
      -- hedge' : {w.val, w'.val} ∈ singleEdge.simplices, must be {0,1}
      have hedge'_is_01 : ({w.val, w'.val} : Finset ℕ) = {0, 1} := by
        simp only [singleEdge] at hedge'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hedge'
        rcases hedge' with rfl | rfl | rfl | rfl
        · have : w.val ∈ (∅ : Finset ℕ) := by rw [← hedge']; exact Finset.mem_insert_self w.val {w'.val}
          exact absurd this (Finset.not_mem_empty w.val)
        · have hw_in : w.val ∈ ({0} : Finset ℕ) := by rw [← hedge']; exact Finset.mem_insert_self w.val {w'.val}
          have hw'_in : w'.val ∈ ({0} : Finset ℕ) := by rw [← hedge']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w'.val)
          simp only [Finset.mem_singleton] at hw_in hw'_in
          exact absurd (hw_in.symm.trans hw'_in) hne'
        · have hw_in : w.val ∈ ({1} : Finset ℕ) := by rw [← hedge']; exact Finset.mem_insert_self w.val {w'.val}
          have hw'_in : w'.val ∈ ({1} : Finset ℕ) := by rw [← hedge']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w'.val)
          simp only [Finset.mem_singleton] at hw_in hw'_in
          exact absurd (hw_in.symm.trans hw'_in) hne'
        · rfl
      -- Both edges (v,w) and (w,w') have endpoints in {0,1} with distinct endpoints
      -- Since {v,w} = {0,1} and {w,w'} = {0,1}, and v≠w and w≠w', the Sym2's are equal
      have h_same_edge : Sym2.mk v w = Sym2.mk w w' := by
        have h1 : v.val ∈ ({0, 1} : Finset ℕ) := by rw [← hedge_is_01]; exact Finset.mem_insert_self v.val _
        have h2 : w.val ∈ ({0, 1} : Finset ℕ) := by rw [← hedge_is_01]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w.val)
        have h4 : w'.val ∈ ({0, 1} : Finset ℕ) := by rw [← hedge'_is_01]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w'.val)
        simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h4
        -- v.val, w.val ∈ {0,1} and v.val ≠ w.val
        -- w.val, w'.val ∈ {0,1} and w.val ≠ w'.val
        -- So (v,w) and (w,w') both represent the edge {0,1}
        rcases h1 with rfl | rfl <;> rcases h2 with hw | hw
        · exact absurd hw hne_vw
        · -- v.val = 0, w.val = 1, so w'.val must be 0
          rcases h4 with hw' | hw'
          · -- w'.val = 0: s(0,1) and s(1,0) are equal
            simp only [Sym2.eq, Sym2.rel_iff']
            right; exact ⟨hw, hw'⟩
          · exact absurd hw'.symm hne'
        · -- v.val = 1, w.val = 0, so w'.val must be 1
          rcases h4 with hw' | hw'
          · exact absurd hw'.symm hne'
          · -- w'.val = 1: s(1,0) and s(0,1) are equal
            simp only [Sym2.eq, Sym2.rel_iff']
            right; exact ⟨hw, hw'⟩
        · exact absurd hw hne_vw
      -- The walk edges contain a duplicate, violating htrail
      rw [SimpleGraph.Walk.isTrail_def] at htrail
      rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons] at htrail
      have hdup : Sym2.mk v w ∈ (Sym2.mk w w' :: p''.edges) := by
        rw [← h_same_edge]
        exact List.mem_cons_self _ _
      rw [List.nodup_cons] at htrail
      exact htrail.1 hdup

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
