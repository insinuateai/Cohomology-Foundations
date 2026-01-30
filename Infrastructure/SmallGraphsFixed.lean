/-
  Infrastructure/SmallGraphsFixed.lean

  Proves H¹ properties for small graphs (0, 1, 2 vertices).

  Key insight: Small graphs are trivially acyclic because cycles need ≥3 vertices.

  SORRIES: 0
  AXIOMS: 0
-/

import H1Characterization.OneConnected
import H1Characterization.Characterization
import Mathlib.Data.Fintype.Card

namespace H1Characterization

open Foundations SimpleGraph

/-! ## Single Vertex Graphs -/

/-- A graph on 0 or 1 vertex is acyclic (no cycles possible) -/
theorem single_vertex_acyclic (K : SimplicialComplex)
    [Fintype K.vertexSet] (h : Fintype.card K.vertexSet ≤ 1) :
    OneConnected K := by
  unfold OneConnected IsAcyclic
  intro v p hp
  have h_cycle_support := hp.support_nodup
  have h_min_len := hp.three_le_length
  have h_support_len : p.support.length = p.length + 1 := Walk.length_support p
  have h_tail_len : p.support.tail.length = p.length := by
    calc p.support.tail.length
        = p.support.length - 1 := List.length_tail p.support
      _ = (p.length + 1) - 1 := by rw [h_support_len]
      _ = p.length := by omega
  have h_tail_nodup := h_cycle_support
  have h_distinct : 3 ≤ p.support.tail.length := by
    calc 3 ≤ p.length := h_min_len
       _ = p.support.tail.length := h_tail_len.symm
  have h_card_ge : 3 ≤ Fintype.card K.vertexSet := by
    have h_nodup_card := List.Nodup.length_le_card h_tail_nodup
    omega
  omega

/-- Empty vertex set means trivially acyclic -/
theorem empty_vertex_acyclic (K : SimplicialComplex)
    [Fintype K.vertexSet] (h : Fintype.card K.vertexSet = 0) :
    (oneSkeleton K).IsAcyclic := by
  intro v p hp
  have : IsEmpty K.vertexSet := Fintype.card_eq_zero_iff.mp h
  exact IsEmpty.false v

/-! ## Two Vertex Graphs -/

/-- A graph on 2 vertices is acyclic -/
theorem two_vertex_acyclic (K : SimplicialComplex)
    [Fintype K.vertexSet] (h : Fintype.card K.vertexSet = 2) :
    OneConnected K := by
  unfold OneConnected IsAcyclic
  intro v p hp
  have h_min_len := hp.three_le_length
  have h_support_len : p.support.length = p.length + 1 := Walk.length_support p
  have h_tail_len : p.support.tail.length = p.length := by
    calc p.support.tail.length
        = p.support.length - 1 := List.length_tail p.support
      _ = (p.length + 1) - 1 := by rw [h_support_len]
      _ = p.length := by omega
  have h_tail_nodup := hp.support_nodup
  have h_distinct : 3 ≤ p.support.tail.length := by
    calc 3 ≤ p.length := h_min_len
       _ = p.support.tail.length := h_tail_len.symm
  have h_card_ge : 3 ≤ Fintype.card K.vertexSet := by
    have h_nodup_card := List.Nodup.length_le_card h_tail_nodup
    omega
  omega

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
    calc p.support.tail.length
        = p.support.length - 1 := List.length_tail p.support
      _ = (p.length + 1) - 1 := by rw [h1]
      _ = p.length := by omega
  have h_card_ge : 3 ≤ Fintype.card K.vertexSet := by
    have := List.Nodup.length_le_card h_tail_nodup
    omega
  omega

/-! ## Walk Properties -/

/-- Walk support is a sublist relating to vertices visited -/
theorem walk_support_vertices (K : SimplicialComplex)
    {v w : K.vertexSet} (p : Walk K v w) :
    ∀ u ∈ p.support, u ∈ Set.univ := fun u _ => Set.mem_univ u

/-- Cycle support tail gives distinct vertices -/
theorem cycle_support_tail_distinct (K : SimplicialComplex)
    {v : K.vertexSet} {p : Walk K v v} (hp : p.IsCycle) :
    p.support.tail.Nodup := hp.support_nodup

/-! ## Summary -/

#check single_vertex_acyclic
#check empty_vertex_acyclic
#check two_vertex_acyclic
#check lt_three_vertices_oneConnected
#check walk_support_vertices
#check cycle_support_tail_distinct

end H1Characterization
