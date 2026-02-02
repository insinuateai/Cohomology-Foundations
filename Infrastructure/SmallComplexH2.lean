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
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

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

/-! ## Three-Vertex Coboundary Construction

For a complex with exactly 3 vertices, at most one 2-simplex (triangle) exists.
When a triangle t = {v₀, v₁, v₂} exists, we construct an explicit 1-cochain
primitive using the "last edge" method:

  g(face 2) = f(t), g = 0 elsewhere

where face 2 = {v₀, v₁} has sign coefficient +1 in the coboundary formula.
Then: δg(t) = sign(0)·g(face 0) + sign(1)·g(face 1) + sign(2)·g(face 2)
            = 1·0 + (-1)·0 + 1·f(t) = f(t) ✓
-/

/-- Two faces with different indices are distinct when the simplex has no duplicate vertices -/
lemma face_ne_of_index_ne {s : Simplex} (i j : Fin s.card) (hij : i ≠ j) :
    s.face i ≠ s.face j := by
  intro heq
  -- face i = s.erase (sorted[i]), face j = s.erase (sorted[j])
  -- If they're equal, then sorted[i] = sorted[j] (erase is injective when element exists)
  -- But sorted is nodup, so i = j, contradiction
  let sorted := s.sort (· ≤ ·)
  have h_len : sorted.length = s.card := Finset.length_sort (· ≤ ·)
  have h_nodup := s.sort_nodup (· ≤ ·)

  -- Both sorted[i] and sorted[j] are in s
  have hi_mem : sorted.get ⟨i.val, by rw [h_len]; exact i.isLt⟩ ∈ s :=
    (Finset.mem_sort (· ≤ ·)).mp (List.get_mem sorted ⟨i.val, by rw [h_len]; exact i.isLt⟩)
  have hj_mem : sorted.get ⟨j.val, by rw [h_len]; exact j.isLt⟩ ∈ s :=
    (Finset.mem_sort (· ≤ ·)).mp (List.get_mem sorted ⟨j.val, by rw [h_len]; exact j.isLt⟩)

  -- If s.erase a = s.erase b and both a, b ∈ s, then a = b
  simp only [Simplex.face] at heq
  have h_erase_inj := Finset.erase_injOn s hi_mem hj_mem heq

  -- But sorted is nodup, so sorted[i] = sorted[j] implies i = j
  have h_idx_eq := List.Nodup.get_inj_iff h_nodup |>.mp h_erase_inj
  simp only [Fin.ext_iff] at h_idx_eq
  exact hij (Fin.ext h_idx_eq)

/-- Helper: construct a 1-cochain that maps to a given value on a single triangle.
For triangle t with target value c, set g(last_edge) = c and g = 0 elsewhere. -/
lemma construct_primitive_single_triangle (K : SimplicialComplex)
    (t : Simplex) (ht : t ∈ K.ksimplices 2) (c : Coeff) :
    ∃ g : Cochain K 1, (δ K 1 g) ⟨t, ht⟩ = c := by
  -- t has 3 vertices (card = 3 for 2-simplex)
  have ht_card : t.card = 3 := by
    simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at ht
    exact ht.2

  -- t is in K.simplices
  have ht_mem : t ∈ K.simplices := by
    simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at ht
    exact ht.1

  -- face 2 of t is in K.ksimplices 1 (it's an edge)
  have h_face2_mem : t.face ⟨2, by rw [ht_card]; omega⟩ ∈ K.ksimplices 1 := by
    simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
    constructor
    · exact K.down_closed t ht_mem ⟨2, by rw [ht_card]; omega⟩
    · rw [Simplex.face_card t ⟨2, by rw [ht_card]; omega⟩ (by omega : t.card > 0), ht_card]

  -- Define g: assign c to face 2, 0 elsewhere
  let target_edge := t.face ⟨2, by rw [ht_card]; omega⟩
  use fun ⟨e, he⟩ => if e = target_edge then c else 0

  -- Compute δg(t) = Σᵢ sign(i) * g(face i)
  simp only [coboundary]

  -- Face inequalities
  have h_f0_ne_f2 : t.face ⟨0, by rw [ht_card]; omega⟩ ≠ target_edge :=
    face_ne_of_index_ne ⟨0, by rw [ht_card]; omega⟩ ⟨2, by rw [ht_card]; omega⟩ (by simp [Fin.ext_iff])
  have h_f1_ne_f2 : t.face ⟨1, by rw [ht_card]; omega⟩ ≠ target_edge :=
    face_ne_of_index_ne ⟨1, by rw [ht_card]; omega⟩ ⟨2, by rw [ht_card]; omega⟩ (by simp [Fin.ext_iff])

  -- Signs
  have hs0 : sign 0 = 1 := by native_decide
  have hs1 : sign 1 = -1 := by native_decide
  have hs2 : sign 2 = 1 := by native_decide

  -- The sum over Fin t.card equals sum over {0, 1, 2} since t.card = 3
  -- We need: Σᵢ sign(i) * g(face i) = c
  -- = sign(0)*g(face 0) + sign(1)*g(face 1) + sign(2)*g(face 2)
  -- = 1*0 + (-1)*0 + 1*c = c

  -- Define indices with explicit proofs
  have h0lt : 0 < t.card := by omega
  have h1lt : 1 < t.card := by omega
  have h2lt : 2 < t.card := by omega
  let i0 : Fin t.card := ⟨0, h0lt⟩
  let i1 : Fin t.card := ⟨1, h1lt⟩
  let i2 : Fin t.card := ⟨2, h2lt⟩

  -- Values of indices
  have hv0 : i0.val = 0 := rfl
  have hv1 : i1.val = 1 := rfl
  have hv2 : i2.val = 2 := rfl

  -- Prove the sum equals the expanded form
  have h_univ : (Finset.univ : Finset (Fin t.card)) = {i0, i1, i2} := by
    ext ⟨xval, hxval⟩
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    simp only [hv0, hv1, hv2]
    omega

  -- Distinctness of indices
  have h_i0_ne_i1 : i0 ≠ i1 := by simp only [ne_eq, Fin.ext_iff, hv0, hv1]; omega
  have h_i0_ne_i2 : i0 ≠ i2 := by simp only [ne_eq, Fin.ext_iff, hv0, hv2]; omega
  have h_i1_ne_i2 : i1 ≠ i2 := by simp only [ne_eq, Fin.ext_iff, hv1, hv2]; omega
  have h_i1_notin : i1 ∉ ({i2} : Finset (Fin t.card)) := by
    rw [Finset.mem_singleton]; exact h_i1_ne_i2
  have h_i0_notin : i0 ∉ ({i1, i2} : Finset (Fin t.card)) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg; exact ⟨h_i0_ne_i1, h_i0_ne_i2⟩

  rw [h_univ]
  rw [Finset.sum_insert h_i0_notin, Finset.sum_insert h_i1_notin, Finset.sum_singleton]

  -- Simplify using sign values
  simp only [hv0, hv1, hv2, hs0, hs1, hs2, one_mul, neg_mul]

  -- g(face 0) = 0, g(face 1) = 0, g(face 2) = c
  have hg0 : (if t.face i0 = target_edge then c else 0) = 0 := if_neg h_f0_ne_f2
  have hg1 : (if t.face i1 = target_edge then c else 0) = 0 := if_neg h_f1_ne_f2
  have hg2 : (if t.face i2 = target_edge then c else 0) = c := if_pos rfl
  rw [hg0, hg1, hg2]
  ring

/-- For 3-vertex complexes, every 2-cocycle is a 2-coboundary.
This eliminates the axiom needed for h2_trivial_three_vertices. -/
theorem three_vertex_coboundary_exists (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_three : Fintype.card K.vertexSet = 3)
    (f : Cochain K 2) (_hf : Is2Cocycle K f) :
    Is2Coboundary K f := by
  -- Case 1: No 2-simplices
  by_cases h_empty : K.ksimplices 2 = ∅
  · -- f : Cochain K 2 is a function from an empty type
    use 0
    funext ⟨s, hs⟩
    rw [Set.eq_empty_iff_forall_notMem] at h_empty
    exact absurd hs (h_empty s)
  · -- Case 2: At least one 2-simplex exists
    push_neg at h_empty
    rw [Set.nonempty_def] at h_empty
    obtain ⟨t, ht⟩ := h_empty

    -- With 3 vertices, there's exactly one possible 2-simplex (the full triangle)
    -- Get the value we need: f(t)
    let target_value := f ⟨t, ht⟩

    -- Use the construction lemma
    obtain ⟨g, hg⟩ := construct_primitive_single_triangle K t ht target_value

    use g
    funext ⟨s, hs⟩

    -- s is a 2-simplex; we need to show it equals t
    -- Both are 3-element subsets of K.vertexSet which has exactly 3 elements
    have hs_eq_t : s = t := by
      have hs_card : s.card = 3 := hs.2
      have ht_card : t.card = 3 := ht.2

      -- Both simplices have all their vertices in K.vertexSet
      have hs_sub : ∀ v ∈ s, v ∈ K.vertexSet := fun v hv => K.vertex_of_mem_simplex s hs.1 v hv
      have ht_sub : ∀ v ∈ t, v ∈ K.vertexSet := fun v hv => K.vertex_of_mem_simplex t ht.1 v hv

      -- The canonical set: image of univ under Subtype.val
      let canonical := (Finset.univ : Finset K.vertexSet).image Subtype.val

      -- Both s and t equal the canonical set
      have hs_eq_can : s = canonical := by
        apply Finset.eq_of_subset_of_card_le
        · -- s ⊆ canonical
          intro v hv
          rw [Finset.mem_image]
          exact ⟨⟨v, hs_sub v hv⟩, Finset.mem_univ _, rfl⟩
        · -- card canonical ≤ card s
          rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
          rw [hs_card, h_three]

      have ht_eq_can : t = canonical := by
        apply Finset.eq_of_subset_of_card_le
        · -- t ⊆ canonical
          intro v hv
          rw [Finset.mem_image]
          exact ⟨⟨v, ht_sub v hv⟩, Finset.mem_univ _, rfl⟩
        · -- card canonical ≤ card t
          rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
          rw [ht_card, h_three]

      -- Therefore s = t
      rw [hs_eq_can, ht_eq_can]

    -- Now show δg(s) = f(s) using hs_eq_t
    have h_eq : (⟨s, hs⟩ : K.ksimplices 2) = ⟨t, ht⟩ := Subtype.ext hs_eq_t

    calc (δ K 1 g) ⟨s, hs⟩
      = (δ K 1 g) ⟨t, ht⟩ := by rw [h_eq]
    _ = target_value := hg
    _ = f ⟨t, ht⟩ := rfl
    _ = f ⟨s, hs⟩ := by rw [h_eq]

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
  intro f hf
  exact three_vertex_coboundary_exists K h f hf

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
