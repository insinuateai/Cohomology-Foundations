/-
  H1Characterization/SmallGraphs.lean

  Proves H¹ properties for small graphs (0, 1, 2 vertices).

  SORRIES: 0
  AXIOMS: 0

  Key insight: Small graphs are trivially acyclic because cycles need ≥3 vertices.
-/

import H1Characterization.OneConnected
import H1Characterization.Characterization
import Mathlib.Data.Fintype.Card

namespace H1Characterization

open Foundations SimpleGraph

/-! ## Small Graphs are Hollow -/

/-- A simplicial complex with < 3 vertices has no filled triangles.
    A 2-simplex requires at least 3 vertices. -/
theorem small_graph_hollow (K : SimplicialComplex)
    [Fintype K.vertexSet] (h : Fintype.card K.vertexSet < 3) :
    hasNoFilledTriangles K := by
  unfold hasNoFilledTriangles SimplicialComplex.ksimplices
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hs_mem hs_card
  -- s has card 3 but K.vertexSet has < 3 elements
  -- Every vertex in s must be in K.vertexSet
  have h_all_in : ∀ v ∈ s, v ∈ K.vertexSet :=
    fun v hv => SimplicialComplex.vertex_of_mem_simplex K s hs_mem v hv
  -- So s.card ≤ |K.vertexSet|
  have h_card_le : s.card ≤ Fintype.card K.vertexSet := by
    have h_inj : Function.Injective (fun v : s => (⟨v.val, h_all_in v.val v.property⟩ : K.vertexSet)) := by
      intro ⟨a, _⟩ ⟨b, _⟩ hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext hab
    have := Fintype.card_le_of_injective _ h_inj
    simp only [Fintype.card_coe] at this
    exact this
  -- But s.card = 3 and |K.vertexSet| < 3
  omega

/-! ## Single Vertex Graphs -/

/-- A graph on 0 or 1 vertex is acyclic (no cycles possible) -/
theorem single_vertex_acyclic (K : SimplicialComplex)
    [Fintype K.vertexSet] (h : Fintype.card K.vertexSet ≤ 1) :
    OneConnected K := by
  unfold OneConnected IsAcyclic
  intro v p hp
  -- A cycle needs at least 3 distinct vertices in its support
  -- But we have at most 1 vertex, contradiction
  have h_cycle_support := hp.support_nodup
  have h_min_len := hp.three_le_length
  -- Walk of length ≥ 3 visits at least 3 vertices (including start)
  -- support.length = length + 1 for a walk
  have h_support_len : p.support.length = p.length + 1 := Walk.length_support p
  -- For a cycle, tail of support has no duplicates
  -- support = [v, v₁, v₂, ..., v] so support.tail = [v₁, v₂, ..., v]
  -- Cycle means v₁, v₂, ..., vₙ₋₁, v are all distinct
  -- This requires at least 3 distinct vertices (since length ≥ 3)
  have h_tail_len : p.support.tail.length = p.length := by
    simp only [List.length_tail, h_support_len]
    omega
  have h_tail_nodup := h_cycle_support
  -- Nodup tail with length ≥ 3 means ≥ 3 distinct elements
  have h_distinct : 3 ≤ p.support.tail.length := by
    rw [h_tail_len]; exact h_min_len
  -- All elements of support.tail are vertices
  have h_tail_in_vertex : ∀ w ∈ p.support.tail, w ∈ Set.univ := fun w _ => Set.mem_univ w
  -- This means we have ≥ 3 distinct vertices
  have h_card_ge : 3 ≤ Fintype.card K.vertexSet := by
    have h_nodup_card := List.Nodup.length_le_card h_tail_nodup
    calc 3 ≤ p.support.tail.length := h_distinct
         _ ≤ Fintype.card K.vertexSet := h_nodup_card
  -- But we assumed card ≤ 1, contradiction
  omega

/-- A single vertex graph is always connected -/
theorem single_vertex_connected (K : SimplicialComplex)
    [Fintype K.vertexSet] [Nonempty K.vertexSet]
    (h : Fintype.card K.vertexSet = 1) :
    (oneSkeleton K).Connected := by
  constructor
  intro v w
  -- With only 1 vertex, v = w
  have : Subsingleton K.vertexSet := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h)
  have heq : v = w := Subsingleton.elim v w
  rw [heq]

/-- H¹ = 0 for single vertex complexes -/
theorem h1_trivial_single_vertex (K : SimplicialComplex)
    [Fintype K.vertexSet] [Nonempty K.vertexSet]
    (h : Fintype.card K.vertexSet = 1) :
    H1Trivial K := by
  have hhollow : hasNoFilledTriangles K := small_graph_hollow K (by omega)
  rw [h1_trivial_iff_oneConnected (hhollow := hhollow) (hconn := single_vertex_connected K h)]
  exact single_vertex_acyclic K (le_of_eq h)

/-! ## Empty Graph -/

/-- Empty vertex set means trivially acyclic -/
theorem empty_vertex_acyclic (K : SimplicialComplex)
    [Fintype K.vertexSet] (h : Fintype.card K.vertexSet = 0) :
    (oneSkeleton K).IsAcyclic := by
  intro v p hp
  -- No vertices exist, so v can't exist
  have : IsEmpty K.vertexSet := Fintype.card_eq_zero_iff.mp h
  exact IsEmpty.false v

/-! ## Two Vertex Graphs -/

/-- A graph on 2 vertices is acyclic -/
theorem two_vertex_acyclic (K : SimplicialComplex)
    [Fintype K.vertexSet] (h : Fintype.card K.vertexSet = 2) :
    OneConnected K := by
  unfold OneConnected IsAcyclic
  intro v p hp
  -- Same argument: cycle needs ≥ 3 distinct vertices
  have h_min_len := hp.three_le_length
  have h_support_len : p.support.length = p.length + 1 := Walk.length_support p
  have h_tail_len : p.support.tail.length = p.length := by
    simp only [List.length_tail, h_support_len]
    omega
  have h_tail_nodup := hp.support_nodup
  have h_distinct : 3 ≤ p.support.tail.length := by
    rw [h_tail_len]; exact h_min_len
  have h_card_ge : 3 ≤ Fintype.card K.vertexSet := by
    have h_nodup_card := List.Nodup.length_le_card h_tail_nodup
    omega
  -- But card = 2
  omega

/-- H¹ = 0 for two vertex complexes (when connected) -/
theorem h1_trivial_two_vertex (K : SimplicialComplex)
    [Fintype K.vertexSet] [Nonempty K.vertexSet]
    (h : Fintype.card K.vertexSet = 2)
    (hconn : (oneSkeleton K).Connected) :
    H1Trivial K := by
  have hhollow : hasNoFilledTriangles K := small_graph_hollow K (by omega)
  rw [h1_trivial_iff_oneConnected (hhollow := hhollow) (hconn := hconn)]
  exact two_vertex_acyclic K h

/-! ## Path Graphs (Trees) -/

/-- Path uniqueness in acyclic graphs -/
theorem path_unique_acyclic (K : SimplicialComplex)
    (hK : OneConnected K) (v w : K.vertexSet) (p q : Path K v w) :
    p = q := acyclic_path_unique K hK v w p q

/-! ## Walk Properties -/

/-- Walk support is a sublist relating to vertices visited -/
theorem walk_support_vertices (K : SimplicialComplex)
    {v w : K.vertexSet} (p : Walk K v w) :
    ∀ u ∈ p.support, u ∈ Set.univ := fun u _ => Set.mem_univ u

/-- Cycle support tail gives distinct vertices -/
theorem cycle_support_tail_distinct (K : SimplicialComplex)
    {v : K.vertexSet} {p : Walk K v v} (hp : p.IsCycle) :
    p.support.tail.Nodup := hp.support_nodup

/-! ## Cardinality Bounds -/

/-- If K has < 3 vertices, then K is one-connected -/
theorem lt_three_vertices_oneConnected (K : SimplicialComplex)
    [Fintype K.vertexSet] (h : Fintype.card K.vertexSet < 3) :
    OneConnected K := by
  unfold OneConnected IsAcyclic
  intro v p hp
  have h_min := hp.three_le_length
  have h_tail_nodup := hp.support_nodup
  have h_tail_len : p.support.tail.length = p.length := by
    have h1 : p.support.length = p.length + 1 := Walk.length_support p
    simp only [List.length_tail, h1]
    omega
  have h_card_ge : 3 ≤ Fintype.card K.vertexSet := by
    have := List.Nodup.length_le_card h_tail_nodup
    omega
  omega

/-! ## Summary -/

/-- Main small graph theorem: < 3 vertices + connected implies H¹ = 0 -/
theorem h1_trivial_small (K : SimplicialComplex)
    [Fintype K.vertexSet] [Nonempty K.vertexSet]
    (h : Fintype.card K.vertexSet < 3)
    (hconn : (oneSkeleton K).Connected) :
    H1Trivial K := by
  have hhollow : hasNoFilledTriangles K := small_graph_hollow K h
  rw [h1_trivial_iff_oneConnected (hhollow := hhollow) (hconn := hconn)]
  exact lt_three_vertices_oneConnected K h

#check h1_trivial_small  -- Main theorem: small graphs have H¹ = 0

end H1Characterization
