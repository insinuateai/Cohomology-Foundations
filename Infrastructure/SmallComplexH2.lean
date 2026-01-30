/-
  Infrastructure/SmallComplexH2.lean

  Proves H² properties for small complexes (< 4 vertices).

  Key insight: H² obstructions require at least 4 vertices because the
  minimal H² ≠ 0 structure is the hollow tetrahedron.

  With < 4 vertices:
  - 0-2 vertices: No triangles exist, so H² = 0 trivially
  - 3 vertices: At most 1 triangle, no 3-simplices, so H² = 0

  SORRIES: 0
  AXIOMS: 0
-/

import Foundations.H2Cohomology
import Mathlib.Data.Fintype.Card

namespace Infrastructure

open Foundations

/-! ## Dimension Bounds -/

/-- A simplex in K with finite vertex set has bounded cardinality -/
lemma simplex_card_le_vertex_card (K : SimplicialComplex) [Fintype K.vertexSet]
    (s : Simplex) (hs : s ∈ K.simplices) :
    s.card ≤ Fintype.card K.vertexSet := by
  -- Every vertex in s is in K.vertexSet
  have h_sub : ∀ v ∈ s, v ∈ K.vertexSet := fun v hv => K.vertex_of_mem_simplex s hs v hv
  -- Create a function from s to K.vertexSet
  let f : s → K.vertexSet := fun ⟨v, hv⟩ => ⟨v, h_sub v hv⟩
  -- This function is injective
  have h_inj : Function.Injective f := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ h
    simp only [Subtype.mk.injEq] at h ⊢
    exact h
  -- So s.card ≤ K.vertexSet.card
  have h_card : Fintype.card s ≤ Fintype.card K.vertexSet :=
    Fintype.card_le_of_injective f h_inj
  simp only [Fintype.card_coe] at h_card
  exact h_card

/-! ## No k-Simplices with Too Few Vertices -/

/-- Complexes with ≤ k vertices have no (k+1)-simplices -/
lemma no_high_simplices (K : SimplicialComplex) [Fintype K.vertexSet] (k : ℕ)
    (h : Fintype.card K.vertexSet ≤ k) :
    K.ksimplices k = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro s hs
  simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hs
  have hbound := simplex_card_le_vertex_card K s hs.1
  omega

/-- Complexes with ≤ 2 vertices have no triangles (2-simplices) -/
lemma no_triangles_le_two_vertices (K : SimplicialComplex) [Fintype K.vertexSet]
    (h : Fintype.card K.vertexSet ≤ 2) :
    K.ksimplices 2 = ∅ :=
  no_high_simplices K 2 h

/-- Complexes with ≤ 3 vertices have no 3-simplices -/
lemma no_3simplices_le_three_vertices (K : SimplicialComplex) [Fintype K.vertexSet]
    (h : Fintype.card K.vertexSet ≤ 3) :
    K.ksimplices 3 = ∅ :=
  no_high_simplices K 3 h

/-! ## H² Triviality Theorems -/

/-- Complexes with ≤ 2 vertices have H² = 0 trivially -/
theorem h2_trivial_le_two_vertices (K : SimplicialComplex) [Fintype K.vertexSet]
    (h : Fintype.card K.vertexSet ≤ 2) :
    H2Trivial K := by
  apply h2_trivial_of_no_2simplices
  exact no_triangles_le_two_vertices K h

/-- Complexes with 3 vertices have H² = 0 -/
theorem h2_trivial_three_vertices (K : SimplicialComplex) [Fintype K.vertexSet]
    (h : Fintype.card K.vertexSet = 3) :
    H2Trivial K := by
  intro f hf
  use 0
  funext ⟨s, hs⟩
  simp only [coboundary, Cochain.zero_apply, sign, mul_zero, Finset.sum_const_zero]

/-- H² = 0 for complexes with ≤ 3 vertices -/
theorem h2_trivial_le_three_vertices (K : SimplicialComplex) [Fintype K.vertexSet]
    (h : Fintype.card K.vertexSet ≤ 3) :
    H2Trivial K := by
  rcases Nat.lt_or_eq_of_le h with h_lt | h_eq
  · exact h2_trivial_le_two_vertices K (Nat.lt_succ_iff.mp h_lt)
  · exact h2_trivial_three_vertices K h_eq

/-- MAIN THEOREM: H² = 0 for complexes with < 4 vertices -/
theorem h2_trivial_lt_four_vertices (K : SimplicialComplex) [Fintype K.vertexSet]
    (h : Fintype.card K.vertexSet < 4) :
    H2Trivial K :=
  h2_trivial_le_three_vertices K (Nat.lt_succ_iff.mp h)

/-- Contrapositive: H² ≠ 0 implies ≥ 4 vertices -/
theorem h2_nontrivial_requires_four_vertices (K : SimplicialComplex) [Fintype K.vertexSet]
    (h : ¬H2Trivial K) :
    Fintype.card K.vertexSet ≥ 4 := by
  by_contra h_small
  push_neg at h_small
  exact h (h2_trivial_lt_four_vertices K h_small)

/-! ## Corollaries -/

/-- Empty complex has H² = 0 -/
theorem h2_trivial_empty (K : SimplicialComplex) [Fintype K.vertexSet]
    (h : Fintype.card K.vertexSet = 0) :
    H2Trivial K :=
  h2_trivial_lt_four_vertices K (by omega)

/-- Single-vertex complex has H² = 0 -/
theorem h2_trivial_single_vertex (K : SimplicialComplex) [Fintype K.vertexSet]
    (h : Fintype.card K.vertexSet = 1) :
    H2Trivial K :=
  h2_trivial_lt_four_vertices K (by omega)

/-- Two-vertex complex has H² = 0 -/
theorem h2_trivial_two_vertices (K : SimplicialComplex) [Fintype K.vertexSet]
    (h : Fintype.card K.vertexSet = 2) :
    H2Trivial K :=
  h2_trivial_lt_four_vertices K (by omega)

end Infrastructure
