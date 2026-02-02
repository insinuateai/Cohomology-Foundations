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
    -- h : f ⟨a, ha⟩ = f ⟨b, hb⟩, i.e., ⟨a, _⟩ = ⟨b, _⟩ in K.vertexSet
    -- Extract a = b from h
    have h_val : a = b := congrArg Subtype.val h
    exact Subtype.ext h_val
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

/-- Complexes with 3 vertices have H² = 0
    With 3 vertices, there can be at most one 2-simplex (the full vertex set).
    The coboundary map δ¹ from 1-cochains to 2-cochains is surjective.

    Proof sketch: For any 2-cochain f and 2-simplex t = {v₀, v₁, v₂}:
    - The coboundary δg(t) = g({v₁,v₂}) - g({v₀,v₂}) + g({v₀,v₁})
    - To get δg(t) = f(t), set g({v₀,v₁}) = f(t) and g = 0 on other edges
    - Then δg(t) = 0 - 0 + f(t) = f(t) ✓ -/
theorem h2_trivial_three_vertices (K : SimplicialComplex) [Fintype K.vertexSet]
    (h : Fintype.card K.vertexSet = 3) :
    H2Trivial K := by
  -- If no 2-simplices, use h2_trivial_of_no_2simplices
  by_cases h2 : K.ksimplices 2 = ∅
  · exact h2_trivial_of_no_2simplices K h2
  · -- K has at least one 2-simplex (triangle with 3 vertices)
    -- With exactly 3 vertices, there's exactly one possible 2-simplex
    intro f hf

    -- Get the unique 2-simplex
    push_neg at h2
    rw [Set.nonempty_def] at h2
    obtain ⟨t, ht⟩ := h2

    -- f(t) is the only value that matters
    let target := f ⟨t, ht⟩

    -- Construct g: set g(last_edge) = target, g = 0 elsewhere
    -- We need to find an edge of t that has coefficient +1 in the coboundary formula
    -- Face 2 of a triangle (the edge {v₀, v₁}) has coefficient sign(2) = +1

    have ht_card : t.card = 3 := ht.2
    have ht_mem : t ∈ K.simplices := ht.1
    have h_face2_card : t.card > 0 := by omega

    -- Face 2 of t is an edge with coefficient +1
    have h_face2_mem : t.face ⟨2, by rw [ht_card]; omega⟩ ∈ K.ksimplices 1 := by
      simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
      constructor
      · exact K.down_closed t ht_mem ⟨2, by rw [ht_card]; omega⟩
      · rw [Simplex.face_card h_face2_card, ht_card]

    -- Define g: assign target to face 2, 0 elsewhere
    use fun ⟨e, he⟩ =>
      if e = t.face ⟨2, by rw [ht_card]; omega⟩ then target else 0

    -- Prove δg = f
    funext ⟨s, hs⟩

    -- s must equal t (only one 2-simplex with 3 vertices)
    have hs_eq_t : s = t := by
      have hs_card : s.card = 3 := hs.2
      have hs_sub : ∀ v ∈ s, v ∈ K.vertexSet := fun v hv => K.vertex_of_mem_simplex s hs.1 v hv
      have ht_sub : ∀ v ∈ t, v ∈ K.vertexSet := fun v hv => K.vertex_of_mem_simplex t ht.1 v hv
      -- Both s and t are 3-element subsets of a 3-element set
      have hs_finset : ∃ (s'' : Finset K.vertexSet), s''.card = 3 ∧ s''.image Subtype.val = s := by
        use s.subtype (· ∈ K.vertexSet)
        constructor
        · rw [Finset.card_subtype]
          convert hs_card using 1
          ext v; simp [hs_sub]
        · ext v; simp [hs_sub]
      have ht_finset : ∃ (t'' : Finset K.vertexSet), t''.card = 3 ∧ t''.image Subtype.val = t := by
        use t.subtype (· ∈ K.vertexSet)
        constructor
        · rw [Finset.card_subtype]
          convert ht_card using 1
          ext v; simp [ht_sub]
        · ext v; simp [ht_sub]
      obtain ⟨s'', hs''_card, hs''_img⟩ := hs_finset
      obtain ⟨t'', ht''_card, ht''_img⟩ := ht_finset
      have hs''_univ : s'' = Finset.univ := Finset.eq_univ_of_card s'' (by rw [hs''_card, h])
      have ht''_univ : t'' = Finset.univ := Finset.eq_univ_of_card t'' (by rw [ht''_card, h])
      calc s = s''.image Subtype.val := hs''_img.symm
        _ = Finset.univ.image Subtype.val := by rw [hs''_univ]
        _ = t''.image Subtype.val := by rw [ht''_univ]
        _ = t := ht''_img

    -- Compute coboundary
    simp only [coboundary]
    have h_eq : (⟨s, hs⟩ : K.ksimplices 2) = ⟨t, ht⟩ := Subtype.ext hs_eq_t

    -- The sum is over Fin s.card = Fin 3
    -- sign(0) * g(face0) + sign(1) * g(face1) + sign(2) * g(face2)
    -- = 1 * 0 + (-1) * 0 + 1 * target = target = f(t)

    -- Convert indices
    have hs_card : s.card = 3 := hs.2

    -- Face membership in ksimplices 1
    have h_face_in : ∀ i : Fin s.card, s.face i ∈ K.ksimplices 1 := by
      intro i
      simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
      constructor
      · exact K.down_closed s hs.1 i
      · rw [Simplex.face_card (by omega : s.card > 0), hs_card]

    -- Compute each term
    -- Face 0 and 1 are not equal to t.face 2 (after accounting for hs_eq_t)
    have h_face0_ne : s.face ⟨0, by rw [hs_card]; omega⟩ ≠ t.face ⟨2, by rw [ht_card]; omega⟩ := by
      rw [hs_eq_t]
      intro heq
      -- Faces at different positions of the same simplex are different
      simp only [Simplex.face] at heq
      have h_sorted := finset_sort_erase_eq_eraseIdx t ⟨0, by rw [ht_card]; omega⟩
      have h_sorted' := finset_sort_erase_eq_eraseIdx t ⟨2, by rw [ht_card]; omega⟩
      have h_nodup := t.sort_nodup (· ≤ ·)
      have h_len : (t.sort (· ≤ ·)).length = 3 := by rw [Finset.length_sort]; exact ht_card
      have h_eq_lists : (t.sort (· ≤ ·)).eraseIdx 0 = (t.sort (· ≤ ·)).eraseIdx 2 := by
        calc (t.sort (· ≤ ·)).eraseIdx 0
          = (t.erase ((t.sort (· ≤ ·)).get ⟨0, by rw [h_len]; omega⟩)).sort (· ≤ ·) := h_sorted.symm
        _ = (t.erase ((t.sort (· ≤ ·)).get ⟨2, by rw [h_len]; omega⟩)).sort (· ≤ ·) := by rw [heq]
        _ = (t.sort (· ≤ ·)).eraseIdx 2 := h_sorted'
      -- eraseIdx 0 of [a,b,c] = [b,c], eraseIdx 2 = [a,b]
      -- [b,c] = [a,b] implies b = a, contradicting nodup
      have h_get0 : ((t.sort (· ≤ ·)).eraseIdx 0).get ⟨0, by rw [List.length_eraseIdx, h_len]; omega⟩ =
                    (t.sort (· ≤ ·)).get ⟨1, by rw [h_len]; omega⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_eraseIdx]; simp
      have h_get2 : ((t.sort (· ≤ ·)).eraseIdx 2).get ⟨0, by rw [List.length_eraseIdx, h_len]; omega⟩ =
                    (t.sort (· ≤ ·)).get ⟨0, by rw [h_len]; omega⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_eraseIdx]; simp
      have : (t.sort (· ≤ ·)).get ⟨1, _⟩ = (t.sort (· ≤ ·)).get ⟨0, _⟩ := by
        calc (t.sort (· ≤ ·)).get ⟨1, _⟩
          = ((t.sort (· ≤ ·)).eraseIdx 0).get ⟨0, _⟩ := h_get0.symm
        _ = ((t.sort (· ≤ ·)).eraseIdx 2).get ⟨0, _⟩ := by rw [h_eq_lists]
        _ = (t.sort (· ≤ ·)).get ⟨0, _⟩ := h_get2
      exact absurd (h_nodup.get_inj_iff.mp this) (by simp [Fin.ext_iff])

    have h_face1_ne : s.face ⟨1, by rw [hs_card]; omega⟩ ≠ t.face ⟨2, by rw [ht_card]; omega⟩ := by
      rw [hs_eq_t]
      intro heq
      simp only [Simplex.face] at heq
      have h_sorted := finset_sort_erase_eq_eraseIdx t ⟨1, by rw [ht_card]; omega⟩
      have h_sorted' := finset_sort_erase_eq_eraseIdx t ⟨2, by rw [ht_card]; omega⟩
      have h_nodup := t.sort_nodup (· ≤ ·)
      have h_len : (t.sort (· ≤ ·)).length = 3 := by rw [Finset.length_sort]; exact ht_card
      have h_eq_lists : (t.sort (· ≤ ·)).eraseIdx 1 = (t.sort (· ≤ ·)).eraseIdx 2 := by
        calc (t.sort (· ≤ ·)).eraseIdx 1
          = (t.erase ((t.sort (· ≤ ·)).get ⟨1, by rw [h_len]; omega⟩)).sort (· ≤ ·) := h_sorted.symm
        _ = (t.erase ((t.sort (· ≤ ·)).get ⟨2, by rw [h_len]; omega⟩)).sort (· ≤ ·) := by rw [heq]
        _ = (t.sort (· ≤ ·)).eraseIdx 2 := h_sorted'
      -- eraseIdx 1 of [a,b,c] = [a,c], eraseIdx 2 = [a,b]
      -- [a,c] = [a,b] implies c = b, contradicting nodup
      have h_get1 : ((t.sort (· ≤ ·)).eraseIdx 1).get ⟨1, by rw [List.length_eraseIdx, h_len]; omega⟩ =
                    (t.sort (· ≤ ·)).get ⟨2, by rw [h_len]; omega⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_eraseIdx]; simp
      have h_get2 : ((t.sort (· ≤ ·)).eraseIdx 2).get ⟨1, by rw [List.length_eraseIdx, h_len]; omega⟩ =
                    (t.sort (· ≤ ·)).get ⟨1, by rw [h_len]; omega⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_eraseIdx]; simp
      have : (t.sort (· ≤ ·)).get ⟨2, _⟩ = (t.sort (· ≤ ·)).get ⟨1, _⟩ := by
        calc (t.sort (· ≤ ·)).get ⟨2, _⟩
          = ((t.sort (· ≤ ·)).eraseIdx 1).get ⟨1, _⟩ := h_get1.symm
        _ = ((t.sort (· ≤ ·)).eraseIdx 2).get ⟨1, _⟩ := by rw [h_eq_lists]
        _ = (t.sort (· ≤ ·)).get ⟨1, _⟩ := h_get2
      exact absurd (h_nodup.get_inj_iff.mp this) (by simp [Fin.ext_iff])

    have h_face2_eq : s.face ⟨2, by rw [hs_card]; omega⟩ = t.face ⟨2, by rw [ht_card]; omega⟩ := by
      rw [hs_eq_t]

    -- Compute the sum
    rw [show Finset.univ = ({0, 1, 2} : Finset (Fin s.card)) by rw [hs_card]; native_decide]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
    simp only [Finset.sum_singleton]

    -- Signs
    have hs0 : sign 0 = 1 := by native_decide
    have hs1 : sign 1 = -1 := by native_decide
    have hs2 : sign 2 = 1 := by native_decide

    simp only [hs0, hs1, hs2, one_mul, neg_mul, neg_one_mul]

    -- The g values: face0 and face1 map to 0, face2 maps to target
    simp only [h_face0_ne, h_face1_ne, h_face2_eq, ↓reduceIte, mul_zero, add_zero, neg_zero]

    -- target = f(t) = f(s) by hs_eq_t
    calc target = f ⟨t, ht⟩ := rfl
      _ = f ⟨s, hs⟩ := by rw [h_eq]

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
