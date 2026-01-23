/-
  H1Characterization/OneSkeleton.lean

  Defines the 1-skeleton of a simplicial complex as a SimpleGraph.
  SORRIES: 0
-/

import H1Characterization.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walks.Maps
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace H1Characterization

-- Re-export vertex-related definitions from Foundations
export Foundations.Simplex (vertex)
export Foundations.SimplicialComplex (vertexSet mem_vertexSet_iff vertex_of_mem_simplex)

/-! ## One-Skeleton -/

def oneSkeleton (K : SimplicialComplex) : SimpleGraph K.vertexSet where
  Adj v w := v.val ≠ w.val ∧ ({v.val, w.val} : Simplex) ∈ K.simplices
  symm := by
    intro v w ⟨hne, hedge⟩
    constructor
    · exact hne.symm
    · convert hedge using 1
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  loopless := by intro v ⟨hne, _⟩; exact hne rfl

lemma oneSkeleton_adj_iff (K : SimplicialComplex) (v w : K.vertexSet) :
    (oneSkeleton K).Adj v w ↔ v.val ≠ w.val ∧ ({v.val, w.val} : Simplex) ∈ K.simplices := Iff.rfl

lemma edge_gives_adj (K : SimplicialComplex) (e : Simplex) (he : e ∈ K.ksimplices 1)
    (v w : Vertex) (hv : v ∈ e) (hw : w ∈ e) (hvw : v ≠ w) :
    ∃ (v' : K.vertexSet) (w' : K.vertexSet),
      v'.val = v ∧ w'.val = w ∧ (oneSkeleton K).Adj v' w' := by
  have hv_vert : v ∈ K.vertexSet := vertex_of_mem_simplex K e he.1 v hv
  have hw_vert : w ∈ K.vertexSet := vertex_of_mem_simplex K e he.1 w hw
  use ⟨v, hv_vert⟩, ⟨w, hw_vert⟩
  refine ⟨rfl, rfl, hvw, ?_⟩
  have hcard : e.card = 2 := he.2
  have : e = {v, w} := by
    have ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp hcard
    rw [heq] at hv hw ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hx; rcases hx with rfl | rfl <;> [rcases hv with rfl | rfl; rcases hw with rfl | rfl] <;> tauto
    · intro hx; rcases hx with rfl | rfl <;> [exact hv; exact hw]
  rw [← this]; exact he.1

lemma card_two_iff (s : Simplex) :
    s.card = 2 ↔ ∃ v w : Vertex, v ≠ w ∧ s = {v, w} := by
  constructor
  · intro h
    exact Finset.card_eq_two.mp h
  · intro ⟨v, w, hvw, heq⟩
    rw [heq]; exact Finset.card_pair hvw

/-! ## Connectivity -/

abbrev Walk (K : SimplicialComplex) (v w : K.vertexSet) := (oneSkeleton K).Walk v w

abbrev Path (K : SimplicialComplex) (v w : K.vertexSet) := (oneSkeleton K).Path v w

end H1Characterization
