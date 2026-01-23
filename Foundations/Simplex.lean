/-
# Simplicial Complexes

A simplex is a finite set of vertices.
A simplicial complex is a collection closed under taking faces.
-/

import Foundations.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Insert
import Mathlib.Data.List.Basic

namespace Foundations

open Finset

/-- An abstract simplex is a finite set of vertices -/
abbrev Simplex := Finset Vertex

namespace Simplex

/-- Dimension of a simplex (number of vertices minus 1) -/
def dim (s : Simplex) : ℤ := (s.card : ℤ) - 1

/-- A 0-simplex (vertex) -/
def vertex (v : Vertex) : Simplex := ({v} : Finset Vertex)

/-- An edge (1-simplex) between two vertices -/
def edge (v₀ v₁ : Vertex) : Simplex := ({v₀, v₁} : Finset Vertex)

/-- A triangle (2-simplex) -/
def triangle (v₀ v₁ v₂ : Vertex) : Simplex := ({v₀, v₁, v₂} : Finset Vertex)

/-- The i-th face of a simplex (remove i-th vertex in sorted order) -/
def face (s : Simplex) (i : Fin s.card) : Simplex :=
  let sorted := s.sort (· ≤ ·)
  have h_len : sorted.length = s.card := Finset.length_sort (· ≤ ·)
  have h_get : i.val < sorted.length := by rw [h_len]; exact i.isLt
  s.erase (sorted.get ⟨i.val, h_get⟩)

/-- Removing a vertex decreases cardinality by 1 -/
lemma face_card (s : Simplex) (i : Fin s.card) (h : s.card > 0) :
    (face s i).card = s.card - 1 := by
  unfold face
  -- The face is obtained by erasing an element from s
  -- The sorted list has the same elements as s
  let sorted := s.sort (· ≤ ·)
  have h_len : sorted.length = s.card := Finset.length_sort (· ≤ ·)
  have h_get : i.val < sorted.length := by rw [h_len]; exact i.isLt
  -- The element we're erasing is in the sorted list
  have h_mem_sorted : sorted.get ⟨i.val, h_get⟩ ∈ sorted :=
    List.get_mem sorted ⟨i.val, h_get⟩
  -- And therefore in s (since sort preserves membership)
  have h_mem_s : sorted.get ⟨i.val, h_get⟩ ∈ s := by
    have : sorted.get ⟨i.val, h_get⟩ ∈ sorted := h_mem_sorted
    exact (Finset.mem_sort (· ≤ ·)).mp this
  -- So erasing it decreases the cardinality by 1
  exact Finset.card_erase_of_mem h_mem_s

/-- The face of a simplex is a subset of the original simplex -/
lemma face_subset (s : Simplex) (i : Fin s.card) : face s i ⊆ s := by
  unfold face
  exact Finset.erase_subset _ s

end Simplex

/-- A simplicial complex is a set of simplices closed under taking faces -/
structure SimplicialComplex where
  simplices : Set Simplex
  has_vertices : ∀ (s : Simplex), s ∈ simplices → ∀ (v : Vertex), v ∈ (s : Finset Vertex) → Simplex.vertex v ∈ simplices
  down_closed : ∀ (s : Simplex), s ∈ simplices → ∀ i : Fin s.card, s.face i ∈ simplices

namespace SimplicialComplex

/-- The k-simplices of a complex -/
def ksimplices (K : SimplicialComplex) (k : ℕ) : Set Simplex :=
  { s ∈ K.simplices | s.card = k + 1 }

/-- Vertices (0-simplices) -/
def vertices (K : SimplicialComplex) : Set Simplex := K.ksimplices 0

/-- Edges (1-simplices) -/
def edges (K : SimplicialComplex) : Set Simplex := K.ksimplices 1

/-- Triangles (2-simplices) -/
def triangles (K : SimplicialComplex) : Set Simplex := K.ksimplices 2

/-- The set of vertices (as elements of Vertex type) in a simplicial complex -/
def vertexSet (K : SimplicialComplex) : Set Vertex :=
  { v : Vertex | Simplex.vertex v ∈ K.simplices }

lemma mem_vertexSet_iff (K : SimplicialComplex) (v : Vertex) :
    v ∈ K.vertexSet ↔ Simplex.vertex v ∈ K.simplices := Iff.rfl

lemma vertex_of_mem_simplex (K : SimplicialComplex) (s : Simplex) (hs : s ∈ K.simplices)
    (v : Vertex) (hv : v ∈ s) : v ∈ K.vertexSet := by
  rw [mem_vertexSet_iff]
  exact K.has_vertices s hs v hv

end SimplicialComplex

end Foundations
