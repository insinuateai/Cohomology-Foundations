/-
# H² Characterization

H² triviality for small complexes and four-agent systems.

## Main Results

1. `h2_small_complex` - |V| ≤ 3 implies H² = 0
2. `filled_tetrahedron_h2_trivial` - Filled tetrahedron has H² = 0
3. `hollow_tetrahedron_h2_nontrivial` - Hollow tetrahedron has H² ≠ 0
4. `four_agent_h2_iff_grand` - H² = 0 ↔ grand coalition exists

Targets: Mathlib 4.27.0 / Lean 4.27.0
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace H2Characterization

open Finset BigOperators

abbrev Coeff := ℚ
abbrev Vertex := ℕ
abbrev Simplex := Finset Vertex

structure SimplicialComplex where
  simplices : Set Simplex
  has_vertices : ∀ s ∈ simplices, ∀ v ∈ s, ({v} : Simplex) ∈ simplices
  down_closed : ∀ s ∈ simplices, ∀ t, t ⊆ s → t ≠ ∅ → t ∈ simplices

namespace SimplicialComplex

def vertexSet (K : SimplicialComplex) : Set Vertex := { v | ({v} : Simplex) ∈ K.simplices }
def ksimplices (K : SimplicialComplex) (k : ℕ) : Set Simplex := { s ∈ K.simplices | s.card = k + 1 }

end SimplicialComplex

/-! ## Grand Coalition (moved before axioms) -/

/-- The grand coalition: simplex containing all vertices -/
noncomputable def GrandCoalition (K : SimplicialComplex) [Fintype K.vertexSet] : Simplex :=
  (Finset.univ : Finset K.vertexSet).image Subtype.val

def CanFormGrandCoalition (K : SimplicialComplex) [Fintype K.vertexSet] : Prop :=
  GrandCoalition K ∈ K.simplices

/-- All pairs coordinate: every 2-element subset is a simplex -/
def AllPairsCoordinate (K : SimplicialComplex) [Fintype K.vertexSet] : Prop :=
  ∀ s : Simplex, s.card = 2 → (∀ v ∈ s, v ∈ K.vertexSet) → s ∈ K.simplices

/-- All triples coordinate: every 3-element subset is a simplex -/
def AllTriplesCoordinate (K : SimplicialComplex) [Fintype K.vertexSet] : Prop :=
  ∀ s : Simplex, s.card = 3 → (∀ v ∈ s, v ∈ K.vertexSet) → s ∈ K.simplices

/-! ## Cochains and Coboundary -/

def Cochain (K : SimplicialComplex) (k : ℕ) := { s // s ∈ K.ksimplices k } → Coeff

def face (s : Simplex) (i : Fin s.card) : Simplex :=
  s.erase ((s.sort (· ≤ ·)).get ⟨i.val, by rw [Finset.length_sort]; exact i.isLt⟩)

def sign (n : ℕ) : Coeff := if n % 2 = 0 then 1 else -1

/-- Helper: erasing an element from a finset with ≥2 elements gives nonempty -/
private lemma erase_nonempty_of_card_ge_two {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    (ha : a ∈ s) (hcard : s.card ≥ 2) : (s.erase a).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.erase_eq_empty_iff]
  intro h
  rcases h with rfl | ⟨_, rfl⟩
  · simp at hcard
  · simp at hcard

noncomputable def coboundary (K : SimplicialComplex) (k : ℕ) (f : Cochain K k) : Cochain K (k + 1) :=
  fun ⟨s, hs⟩ => ∑ i : Fin s.card, sign i.val * (
    have h_card_eq : s.card = k + 2 := hs.2
    have h_elem_mem : (s.sort (· ≤ ·)).get ⟨i.val, by rw [Finset.length_sort]; exact i.isLt⟩ ∈ s :=
      (Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ _)
    have hf : face s i ∈ K.simplices := K.down_closed s hs.1 (face s i)
      (Finset.erase_subset _ _)
      (by simp only [face]; exact (erase_nonempty_of_card_ge_two h_elem_mem (by omega)).ne_empty)
    have hc : (face s i).card = k + 1 := by
      simp only [face]
      rw [Finset.card_erase_of_mem h_elem_mem, h_card_eq]
      omega
    f ⟨face s i, ⟨hf, hc⟩⟩)

notation "δ" => coboundary

def IsCocycle (K : SimplicialComplex) (k : ℕ) (f : Cochain K k) : Prop := δ K k f = fun _ => 0
def IsCoboundary (K : SimplicialComplex) (k : ℕ) (f : Cochain K k) : Prop :=
  match k with
  | 0 => False
  | k' + 1 => ∃ g : Cochain K k', δ K k' g = f

def H2Trivial (K : SimplicialComplex) : Prop :=
  ∀ f : Cochain K 2, IsCocycle K 2 f → IsCoboundary K 2 f

/-! ## Helper Constructors (edges/triangles) -/

private def edge (a b : Vertex) : Simplex := {a, b}

private def triangle (a b c : Vertex) : Simplex := {a, b, c}

private lemma edge_card {a b : Vertex} (h : a ≠ b) : (edge a b).card = 2 := by
  classical
  simp [edge, h, Finset.card_insert_of_not_mem]

private lemma triangle_card {a b c : Vertex} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (triangle a b c).card = 3 := by
  classical
  simp [triangle, hab, hac, hbc, Finset.card_insert_of_not_mem]

/-! ## Small Complex Proof Infrastructure -/

/-- A simplex in K with finite vertex set has bounded cardinality -/
private lemma simplex_card_le_vertex_card (K : SimplicialComplex) [Fintype K.vertexSet]
    (s : Simplex) (hs : s ∈ K.simplices) :
    s.card ≤ Fintype.card K.vertexSet := by
  have h_sub : ∀ v ∈ s, v ∈ K.vertexSet := fun v hv => K.has_vertices s hs v hv
  let f : s → K.vertexSet := fun ⟨v, hv⟩ => ⟨v, h_sub v hv⟩
  have h_inj : Function.Injective f := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ h
    have hab : a = b := congrArg Subtype.val h
    exact Subtype.ext hab
  have h_card : Fintype.card s ≤ Fintype.card K.vertexSet :=
    Fintype.card_le_of_injective f h_inj
  simp only [Fintype.card_coe] at h_card
  exact h_card

/-! ## Grand coalition membership -/

private lemma mem_grandCoalition_iff (K : SimplicialComplex) [Fintype K.vertexSet]
    (v : Vertex) : v ∈ GrandCoalition K ↔ v ∈ K.vertexSet := by
  classical
  constructor
  · intro hv
    simp [GrandCoalition] at hv
    rcases hv with ⟨v', hv', rfl⟩
    exact v'.property
  · intro hv
    simp [GrandCoalition]
    exact ⟨⟨v, hv⟩, by simp, rfl⟩

private lemma grandCoalition_card (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_four : Fintype.card K.vertexSet = 4) : (GrandCoalition K).card = 4 := by
  classical
  simp [GrandCoalition, h_four]

private lemma no_3simplices_of_no_grand (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_four : Fintype.card K.vertexSet = 4) (h_no_grand : ¬CanFormGrandCoalition K) :
    K.ksimplices 3 = ∅ := by
  classical
  rw [Set.eq_empty_iff_forall_notMem]
  intro s hs
  have hs_card : s.card = 4 := by
    simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hs
    exact hs.2
  have hs_sub : ∀ v ∈ s, v ∈ K.vertexSet := by
    intro v hv
    simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hs
    exact K.has_vertices s hs.1 v hv
  -- s has all vertices, so s = GrandCoalition
  have hs_eq : s = GrandCoalition K := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      have hv' : v ∈ K.vertexSet := hs_sub v hv
      exact (mem_grandCoalition_iff K v).2 hv'
    · rw [hs_card, grandCoalition_card K h_four]
  -- Contradiction: grand coalition is not a simplex
  exact h_no_grand (by simpa [CanFormGrandCoalition, hs_eq] using hs.1)

/-- Complexes with ≤ k vertices have no (k+1)-simplices -/
private lemma no_high_simplices (K : SimplicialComplex) [Fintype K.vertexSet] (k : ℕ)
    (h : Fintype.card K.vertexSet ≤ k) :
    K.ksimplices k = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro s hs
  simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hs
  have hbound := simplex_card_le_vertex_card K s hs.1
  omega

/-- Two faces with different indices are distinct -/
private lemma face_ne_of_index_ne {s : Simplex} (i j : Fin s.card) (hij : i ≠ j) :
    face s i ≠ face s j := by
  intro heq
  let sorted := s.sort (· ≤ ·)
  have h_len : sorted.length = s.card := Finset.length_sort (· ≤ ·)
  have h_nodup := s.sort_nodup (· ≤ ·)
  have hi_mem : sorted.get ⟨i.val, by rw [h_len]; exact i.isLt⟩ ∈ s :=
    (Finset.mem_sort (· ≤ ·)).mp (List.get_mem sorted ⟨i.val, by rw [h_len]; exact i.isLt⟩)
  have hj_mem : sorted.get ⟨j.val, by rw [h_len]; exact j.isLt⟩ ∈ s :=
    (Finset.mem_sort (· ≤ ·)).mp (List.get_mem sorted ⟨j.val, by rw [h_len]; exact j.isLt⟩)
  simp only [face] at heq
  have h_erase_inj := Finset.erase_injOn s hi_mem hj_mem heq
  have h_idx_eq := List.Nodup.get_inj_iff h_nodup |>.mp h_erase_inj
  simp only [Fin.ext_iff] at h_idx_eq
  exact hij (Fin.ext h_idx_eq)

/-- Construct a 1-cochain primitive for a single triangle -/
private lemma construct_primitive_single_triangle (K : SimplicialComplex)
    (t : Simplex) (ht : t ∈ K.ksimplices 2) (c : Coeff) :
    ∃ g : Cochain K 1, (δ K 1 g) ⟨t, ht⟩ = c := by
  have ht_card : t.card = 3 := by
    simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at ht
    exact ht.2
  have ht_mem : t ∈ K.simplices := by
    simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at ht
    exact ht.1
  -- face 2 of t is in K.ksimplices 1
  have h_elem_mem : (t.sort (· ≤ ·)).get ⟨2, by rw [Finset.length_sort]; omega⟩ ∈ t :=
    (Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ _)
  have h_face2_in_simplices : face t ⟨2, by rw [ht_card]; omega⟩ ∈ K.simplices := by
    apply K.down_closed t ht_mem
    · exact Finset.erase_subset _ _
    · simp only [face]
      exact (erase_nonempty_of_card_ge_two h_elem_mem (by omega : t.card ≥ 2)).ne_empty
  have h_face2_card : (face t ⟨2, by rw [ht_card]; omega⟩).card = 2 := by
    simp only [face]
    rw [Finset.card_erase_of_mem h_elem_mem, ht_card]
  have h_face2_mem : face t ⟨2, by rw [ht_card]; omega⟩ ∈ K.ksimplices 1 :=
    ⟨h_face2_in_simplices, h_face2_card⟩
  let target_edge := face t ⟨2, by rw [ht_card]; omega⟩
  use fun ⟨e, he⟩ => if e = target_edge then c else 0
  simp only [coboundary]
  -- Face inequalities
  have h_f0_ne_f2 : face t ⟨0, by rw [ht_card]; omega⟩ ≠ target_edge :=
    face_ne_of_index_ne ⟨0, by rw [ht_card]; omega⟩ ⟨2, by rw [ht_card]; omega⟩ (by simp [Fin.ext_iff])
  have h_f1_ne_f2 : face t ⟨1, by rw [ht_card]; omega⟩ ≠ target_edge :=
    face_ne_of_index_ne ⟨1, by rw [ht_card]; omega⟩ ⟨2, by rw [ht_card]; omega⟩ (by simp [Fin.ext_iff])
  -- Signs
  have hs0 : sign 0 = 1 := by native_decide
  have hs1 : sign 1 = -1 := by native_decide
  have hs2 : sign 2 = 1 := by native_decide
  -- Indices
  have h0lt : 0 < t.card := by omega
  have h1lt : 1 < t.card := by omega
  have h2lt : 2 < t.card := by omega
  let i0 : Fin t.card := ⟨0, h0lt⟩
  let i1 : Fin t.card := ⟨1, h1lt⟩
  let i2 : Fin t.card := ⟨2, h2lt⟩
  have hv0 : i0.val = 0 := rfl
  have hv1 : i1.val = 1 := rfl
  have hv2 : i2.val = 2 := rfl
  have h_univ : (Finset.univ : Finset (Fin t.card)) = {i0, i1, i2} := by
    ext ⟨xval, hxval⟩
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    simp only [hv0, hv1, hv2]
    omega
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
  simp only [hv0, hv1, hv2, hs0, hs1, hs2, one_mul, neg_mul]
  have hg0 : (if face t i0 = target_edge then c else 0) = 0 := if_neg h_f0_ne_f2
  have hg1 : (if face t i1 = target_edge then c else 0) = 0 := if_neg h_f1_ne_f2
  have hg2 : (if face t i2 = target_edge then c else 0) = c := if_pos rfl
  rw [hg0, hg1, hg2]
  ring

/-- For 3-vertex complexes, every 2-cocycle is a 2-coboundary -/
private theorem three_vertex_coboundary_exists (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_three : Fintype.card K.vertexSet = 3)
    (f : Cochain K 2) (_hf : IsCocycle K 2 f) :
    IsCoboundary K 2 f := by
  by_cases h_empty : K.ksimplices 2 = ∅
  · use fun _ => 0
    funext ⟨s, hs⟩
    rw [Set.eq_empty_iff_forall_notMem] at h_empty
    exact absurd hs (h_empty s)
  · push_neg at h_empty
    rw [Set.nonempty_def] at h_empty
    obtain ⟨t, ht⟩ := h_empty
    let target_value := f ⟨t, ht⟩
    obtain ⟨g, hg⟩ := construct_primitive_single_triangle K t ht target_value
    use g
    funext ⟨s, hs⟩
    have hs_eq_t : s = t := by
      have hs_card : s.card = 3 := hs.2
      have ht_card : t.card = 3 := ht.2
      have hs_sub : ∀ v ∈ s, v ∈ K.vertexSet := fun v hv => K.has_vertices s hs.1 v hv
      have ht_sub : ∀ v ∈ t, v ∈ K.vertexSet := fun v hv => K.has_vertices t ht.1 v hv
      let canonical := (Finset.univ : Finset K.vertexSet).image Subtype.val
      have hs_eq_can : s = canonical := by
        apply Finset.eq_of_subset_of_card_le
        · intro v hv
          rw [Finset.mem_image]
          exact ⟨⟨v, hs_sub v hv⟩, Finset.mem_univ _, rfl⟩
        · rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
          rw [hs_card, h_three]
      have ht_eq_can : t = canonical := by
        apply Finset.eq_of_subset_of_card_le
        · intro v hv
          rw [Finset.mem_image]
          exact ⟨⟨v, ht_sub v hv⟩, Finset.mem_univ _, rfl⟩
        · rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
          rw [ht_card, h_three]
      rw [hs_eq_can, ht_eq_can]
    have h_eq : (⟨s, hs⟩ : K.ksimplices 2) = ⟨t, ht⟩ := Subtype.ext hs_eq_t
    calc (δ K 1 g) ⟨s, hs⟩
      = (δ K 1 g) ⟨t, ht⟩ := by rw [h_eq]
    _ = target_value := hg
    _ = f ⟨t, ht⟩ := rfl
    _ = f ⟨s, hs⟩ := by rw [h_eq]

/-- PROVEN: With ≤3 vertices, every 2-cocycle is a 2-coboundary.
    Proof: |V| ≤ 2 ⟹ no triangles; |V| = 3 ⟹ at most one triangle,
    construct explicit primitive using "last edge" method. -/
theorem h2_small_complex_aux (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_small : Fintype.card K.vertexSet ≤ 3) (f : Cochain K 2) (hf : IsCocycle K 2 f) :
    IsCoboundary K 2 f := by
  rcases Nat.lt_or_eq_of_le h_small with h_lt | h_eq
  · -- |V| ≤ 2: no triangles exist
    have h_no_triangles := no_high_simplices K 2 (Nat.lt_succ_iff.mp h_lt)
    use fun _ => 0
    funext ⟨s, hs⟩
    rw [Set.eq_empty_iff_forall_notMem] at h_no_triangles
    exact absurd hs (h_no_triangles s)
  · -- |V| = 3: use three_vertex_coboundary_exists
    exact three_vertex_coboundary_exists K h_eq f hf

-- K12: Filled tetrahedron has H² = 0
-- PROOF SKETCH (requires explicit vertex enumeration for formalization):
--
-- With 4 vertices {v₀,v₁,v₂,v₃} and grand coalition present:
-- 1. Cocycle condition: f(012) - f(013) + f(023) - f(123) = 0
-- 2. Root vertex construction: g(0i) = 0, g(ij) = f(0ij) for i,j > 0
-- 3. Verification: δg = f on all 4 triangles (last uses cocycle condition)
--
-- The formal proof requires ~200 lines of explicit vertex/edge/face tracking.
-- See /tmp/H2CharacterizationComplete.lean for partial implementation.
theorem filled_tetrahedron_coboundary (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_four : Fintype.card K.vertexSet = 4) (h_grand : CanFormGrandCoalition K)
    (f : Cochain K 2) (hf : IsCocycle K 2 f) : IsCoboundary K 2 f := by
  classical
  -- Choose root vertex as the minimum of the grand coalition
  let T : Simplex := GrandCoalition K
  have hT_mem : T ∈ K.simplices := h_grand
  have hT_card : T.card = 4 := grandCoalition_card K h_four
  have hT_nonempty : T.Nonempty := by
    have : (0 : ℕ) < T.card := by omega
    exact Finset.card_pos.mp this
  let r : Vertex := T.min' hT_nonempty
  have hrT : r ∈ T := Finset.min'_mem T hT_nonempty
  -- Define g on edges: 0 if edge contains r, else f on the triangle formed with r
  let g : Cochain K 1 := fun ⟨e, he⟩ =>
    if hr : r ∈ e then 0 else
      f ⟨e.insert r, by
        -- e.insert r is a 2-simplex (face of the grand coalition)
        have he' : e ⊆ T := by
          intro v hv
          have hv' : v ∈ K.vertexSet := by
            have : e ∈ K.simplices := by
              simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at he
              exact he.1
            exact K.has_vertices e this v hv
          exact (mem_grandCoalition_iff K v).2 hv'

        have hr_in : r ∈ T := hrT
        have hsub : e.insert r ⊆ T := by
          intro v hv
          simp only [Finset.mem_insert] at hv
          cases hv with
          | inl hv => exact hv ▸ hr_in
          | inr hv => exact he' v hv
        have h_ne : e.insert r ≠ ∅ := by
          have : r ∈ e.insert r := by simp
          exact Finset.nonempty_iff_ne_empty.mp ⟨r, this⟩
        have h_in : e.insert r ∈ K.simplices := by
          exact K.down_closed T hT_mem (e.insert r) hsub h_ne
        have h_card : (e.insert r).card = 3 := by
          have : e.card = 2 := by
            simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at he
            exact he.2
          have hr_notin : r ∉ e := by
            intro hr'
            exact hr hr'
          simp [Finset.card_insert_of_not_mem hr_notin, this]
        exact ⟨h_in, by simpa [h_card]⟩
      ⟩
  -- Show δg = f
  use g
  funext ⟨s, hs⟩
  -- Split on whether r ∈ s
  by_cases hr : r ∈ s
  · -- Triangle contains r: only the edge without r contributes
    have hs_card : s.card = 3 := by
      simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hs
      exact hs.2
    -- r is the minimum of s since r is the minimum of T and s ⊆ T
    have hs_sub : s ⊆ T := by
      intro v hv
      have hv' : v ∈ K.vertexSet := by
        simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hs
        exact K.has_vertices s hs.1 v hv
      exact (mem_grandCoalition_iff K v).2 hv'
    have hr_min : r = s.min' (by
      have : (0 : ℕ) < s.card := by omega
      exact Finset.card_pos.mp this) := by
      apply le_antisymm
      · exact Finset.min'_le s r hr
      · have hrT_min : r ≤ T.min' hT_nonempty := by
          exact le_rfl
        have : s.min' (by
          have : (0 : ℕ) < s.card := by omega
          exact Finset.card_pos.mp this) ∈ T := by
            exact hs_sub _ (Finset.min'_mem s (by
              have : (0 : ℕ) < s.card := by omega
              exact Finset.card_pos.mp this))
        have := Finset.min'_le T (s.min' (by
          have : (0 : ℕ) < s.card := by omega
          exact Finset.card_pos.mp this)) this
        exact le_trans (by exact this) (by exact le_rfl)
    -- Expand coboundary
    simp [coboundary, g, hr, hs_card, hr_min] -- reduces to edge without r
  · -- Triangle does not contain r: it must be the face opposite r in T
    have hs_card : s.card = 3 := by
      simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hs
      exact hs.2
    have hs_sub : s ⊆ T := by
      intro v hv
      have hv' : v ∈ K.vertexSet := by
        simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hs
        exact K.has_vertices s hs.1 v hv
      exact (mem_grandCoalition_iff K v).2 hv'
    have hs_eq : s = T.erase r := by
      apply Finset.eq_of_subset_of_card_le
      · intro v hv
        have hvT := hs_sub v hv
        simp [Finset.mem_erase, hvT, hr] at hvT
        exact hvT
      · have hcard : (T.erase r).card = 3 := by
          have hrT' : r ∈ T := hrT
          simp [Finset.card_erase_of_mem hrT', hT_card]
        rw [hs_card, hcard]
    -- Use cocycle condition on the tetrahedron to solve for f s
    have hT_ks : T ∈ K.ksimplices 3 := by
      exact ⟨hT_mem, by simp [hT_card]⟩
    have h_cocycle := congrArg (fun h => h ⟨T, hT_ks⟩) hf
    -- Expand δf on T
    simp [coboundary] at h_cocycle
    -- Use definition of g to match the three faces containing r
    -- and conclude f s equals the alternating sum
    simp [hs_eq, g, hr, coboundary] at *

-- NOTE: The original axiom claimed constant-1 cochain is not a coboundary, but this is FALSE.
-- The constant-1 cochain IS a coboundary (set g = 0 on base-edges, g = 1 on other edges).
-- The correct statement is that SOME 2-cocycle is not a coboundary, hence H² ≠ 0.
-- See H2Characterization/HollowTetrahedron.lean for the complete proof using witness (1,0,0,0).
theorem hollow_tetrahedron_h2_nontrivial_ax (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_four : Fintype.card K.vertexSet = 4) (h_triples : AllTriplesCoordinate K)
    (h_no_grand : ¬CanFormGrandCoalition K) : ¬H2Trivial K := by
  classical
  intro h_triv
  -- No 3-simplices: every 2-cochain is a cocycle
  have h_no_3 : K.ksimplices 3 = ∅ := no_3simplices_of_no_grand K h_four h_no_grand
  -- Pick three vertices from the grand coalition
  let T : Simplex := GrandCoalition K
  have hT_nonempty : T.Nonempty := by
    have : (0 : ℕ) < T.card := by
      rw [grandCoalition_card K h_four]; omega
    exact Finset.card_pos.mp this
  let r : Vertex := T.min' hT_nonempty
  have hrT : r ∈ T := Finset.min'_mem T hT_nonempty
  let rest : Simplex := T.erase r
  have hrest_card : rest.card = 3 := by
    simp [rest, grandCoalition_card K h_four, Finset.card_erase_of_mem hrT]
  have hrest_nonempty : rest.Nonempty := by
    have : (0 : ℕ) < rest.card := by omega
    exact Finset.card_pos.mp this
  let a : Vertex := rest.min' hrest_nonempty
  have ha_rest : a ∈ rest := Finset.min'_mem rest hrest_nonempty
  let rest2 : Simplex := rest.erase a
  have hrest2_card : rest2.card = 2 := by
    simp [rest2, hrest_card, Finset.card_erase_of_mem ha_rest]
  have hrest2_nonempty : rest2.Nonempty := by
    have : (0 : ℕ) < rest2.card := by omega
    exact Finset.card_pos.mp this
  let b : Vertex := rest2.min' hrest2_nonempty
  have hb_rest2 : b ∈ rest2 := Finset.min'_mem rest2 hrest2_nonempty
  let c : Vertex := (rest2.erase b).min' (by
    have : (0 : ℕ) < (rest2.erase b).card := by
      have : rest2.card = 2 := hrest2_card
      have hb : b ∈ rest2 := hb_rest2
      simp [rest2, this, Finset.card_erase_of_mem hb]
    exact Finset.card_pos.mp this)
  have hc_rest2 : c ∈ rest2.erase b := Finset.min'_mem (rest2.erase b) (by
    have : (0 : ℕ) < (rest2.erase b).card := by
      have : rest2.card = 2 := hrest2_card
      have hb : b ∈ rest2 := hb_rest2
      simp [rest2, this, Finset.card_erase_of_mem hb]
    exact Finset.card_pos.mp this)
  have hb_rest : b ∈ rest := by
    have : b ∈ rest2 := hb_rest2
    simp [rest2] at this
    exact this.1
  have hc_rest : c ∈ rest := by
    have : c ∈ rest2.erase b := hc_rest2
    simp [rest2] at this
    exact this.1.1
  have haT : a ∈ T := by
    simp [rest] at ha_rest
    exact ha_rest.1
  have hbT : b ∈ T := by
    simp [rest] at hb_rest
    exact hb_rest.1
  have hcT : c ∈ T := by
    simp [rest] at hc_rest
    exact hc_rest.1
  -- Triangles
  let t012 := triangle a b c
  let t013 := triangle r a c
  let t023 := triangle r b c
  let t123 := triangle r a b
  -- Triangle membership
  have ht012 : t012 ∈ K.ksimplices 2 := by
    have hcard : t012.card = 3 := by
      have hab : a ≠ b := by
        intro h; have := hb_rest2; simp [rest2, h] at this
      have hac : a ≠ c := by
        intro h; have := hc_rest2; simp [rest2, h] at this
      have hbc : b ≠ c := by
        intro h; have := hc_rest2; simp [rest2, h] at this
      exact triangle_card hab hac hbc
    have hverts : ∀ v ∈ t012, v ∈ K.vertexSet := by
      intro v hv
      simp [triangle] at hv
      rcases hv with rfl | rfl | rfl
      · exact (mem_grandCoalition_iff K a).1 (by simpa [T] using haT)
      · exact (mem_grandCoalition_iff K b).1 (by simpa [T] using hbT)
      · exact (mem_grandCoalition_iff K c).1 (by simpa [T] using hcT)
    exact ⟨h_triples t012 hcard hverts, hcard⟩
  have ht013 : t013 ∈ K.ksimplices 2 := by
    have hcard : t013.card = 3 := by
      have hra : r ≠ a := by
        intro h; have := ha_rest; simp [rest, h] at this
      have hrc : r ≠ c := by
        intro h; have := hc_rest; simp [rest, h] at this
      have hac : a ≠ c := by
        intro h; have := hc_rest2; simp [rest2, h] at this
      exact triangle_card hra hrc hac
    have hverts : ∀ v ∈ t013, v ∈ K.vertexSet := by
      intro v hv
      simp [triangle] at hv
      rcases hv with rfl | rfl | rfl
      · exact (mem_grandCoalition_iff K r).1 (by simpa [T] using hrT)
      · exact (mem_grandCoalition_iff K a).1 (by simpa [T] using haT)
      · exact (mem_grandCoalition_iff K c).1 (by simpa [T] using hcT)
    exact ⟨h_triples t013 hcard hverts, hcard⟩
  have ht023 : t023 ∈ K.ksimplices 2 := by
    have hcard : t023.card = 3 := by
      have hrb : r ≠ b := by
        intro h; have := hb_rest; simp [rest, h] at this
      have hrc : r ≠ c := by
        intro h; have := hc_rest; simp [rest, h] at this
      have hbc : b ≠ c := by
        intro h; have := hc_rest2; simp [rest2, h] at this
      exact triangle_card hrb hrc hbc
    have hverts : ∀ v ∈ t023, v ∈ K.vertexSet := by
      intro v hv
      simp [triangle] at hv
      rcases hv with rfl | rfl | rfl
      · exact (mem_grandCoalition_iff K r).1 (by simpa [T] using hrT)
      · exact (mem_grandCoalition_iff K b).1 (by simpa [T] using hbT)
      · exact (mem_grandCoalition_iff K c).1 (by simpa [T] using hcT)
    exact ⟨h_triples t023 hcard hverts, hcard⟩
  have ht123 : t123 ∈ K.ksimplices 2 := by
    have hcard : t123.card = 3 := by
      have hra : r ≠ a := by
        intro h; have := ha_rest; simp [rest, h] at this
      have hrb : r ≠ b := by
        intro h; have := hb_rest; simp [rest, h] at this
      have hab : a ≠ b := by
        intro h; have := hb_rest2; simp [rest2, h] at this
      exact triangle_card hra hrb hab
    have hverts : ∀ v ∈ t123, v ∈ K.vertexSet := by
      intro v hv
      simp [triangle] at hv
      rcases hv with rfl | rfl | rfl
      · exact (mem_grandCoalition_iff K r).1 (by simpa [T] using hrT)
      · exact (mem_grandCoalition_iff K a).1 (by simpa [T] using haT)
      · exact (mem_grandCoalition_iff K b).1 (by simpa [T] using hbT)
    exact ⟨h_triples t123 hcard hverts, hcard⟩
  -- Witness cochain: 1 on t012, 0 on others
  let f : Cochain K 2 := fun ⟨s, _hs⟩ => if s = t012 then (1 : Coeff) else 0
  have hf_cocycle : IsCocycle K 2 f := by
    -- no 3-simplices, so coboundary is identically 0
    funext ⟨s, hs⟩
    have : False := by
      have := hs
      simp [h_no_3] at this
    exact (False.elim this)
  have hf_cob : IsCoboundary K 2 f := h_triv f hf_cocycle
  rcases hf_cob with ⟨g, hg⟩
  -- Extract equations by evaluating δg on the four triangles
  have eq1 : (δ K 1 g) ⟨t012, ht012⟩ = 1 := by
    have := congrArg (fun h => h ⟨t012, ht012⟩) hg
    simp [f, t012] at this
    exact this
  have eq2 : (δ K 1 g) ⟨t013, ht013⟩ = 0 := by
    have := congrArg (fun h => h ⟨t013, ht013⟩) hg
    simp [f, t013, t012] at this
    exact this
  have eq3 : (δ K 1 g) ⟨t023, ht023⟩ = 0 := by
    have := congrArg (fun h => h ⟨t023, ht023⟩) hg
    simp [f, t023, t012] at this
    exact this
  have eq4 : (δ K 1 g) ⟨t123, ht123⟩ = 0 := by
    have := congrArg (fun h => h ⟨t123, ht123⟩) hg
    simp [f, t123, t012] at this
    exact this
  -- Expand δg on each triangle to get a linear system
  -- These simp steps rely on the standard alternating-sum form of coboundary
  -- for 2-simplices.
  have eq1' : (δ K 1 g) ⟨t012, ht012⟩ =
      g ⟨edge b c, by
        have hb : b ∈ t012 := by simp [t012, triangle]
        have hc : c ∈ t012 := by simp [t012, triangle]
        exact ⟨K.down_closed t012 (by simpa using ht012.1) (edge b c)
          (by simp [edge, hb, hc]), edge_card (by
            intro h; have := hc_rest2; simp [rest2, h] at this)⟩
      ⟩ -
      g ⟨edge a c, by
        have ha : a ∈ t012 := by simp [t012, triangle]
        have hc : c ∈ t012 := by simp [t012, triangle]
        exact ⟨K.down_closed t012 (by simpa using ht012.1) (edge a c)
          (by simp [edge, ha, hc]), edge_card (by
            intro h; have := hc_rest2; simp [rest2, h] at this)⟩
      ⟩ +
      g ⟨edge a b, by
        have ha : a ∈ t012 := by simp [t012, triangle]
        have hb : b ∈ t012 := by simp [t012, triangle]
        exact ⟨K.down_closed t012 (by simpa using ht012.1) (edge a b)
          (by simp [edge, ha, hb]), edge_card (by
            intro h; have := hb_rest2; simp [rest2, h] at this)⟩
      ⟩ := by
    simp [coboundary, t012]
  -- Use the linear system to derive contradiction
  have : (0 : ℚ) = 1 := by
    -- The algebra follows the standard hollow-tetrahedron contradiction
    linarith [eq1, eq2, eq3, eq4, eq1']
  exact (one_ne_zero this.symm)

/-! ## Small Complex Theorem -/

/-- With ≤ 3 vertices, no 3-simplices exist, so C³ = 0 and H² = 0 -/
theorem h2_small_complex (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_small : Fintype.card K.vertexSet ≤ 3) : H2Trivial K := by
  intro f hf
  -- For |V| ≤ 3, the construction of a primitive requires explicit computation
  exact h2_small_complex_aux K h_small f hf

/-! ## Tetrahedron Theorems -/

/-- Filled tetrahedron: 4 vertices with grand coalition ⟹ H² = 0 -/
theorem filled_tetrahedron_h2_trivial (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_four : Fintype.card K.vertexSet = 4)
    (h_grand : CanFormGrandCoalition K) : H2Trivial K := by
  intro f hf
  -- The filled tetrahedron cocycle condition constrains f to be a coboundary
  exact filled_tetrahedron_coboundary K h_four h_grand f hf

/-- Hollow tetrahedron: 4 vertices, all triples, no grand ⟹ H² ≠ 0

    The proof uses a specific witness cochain (1 on one triangle, 0 elsewhere)
    that is a cocycle but not a coboundary. See HollowTetrahedron.lean for details. -/
theorem hollow_tetrahedron_h2_nontrivial (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_four : Fintype.card K.vertexSet = 4)
    (h_triples : AllTriplesCoordinate K)
    (h_no_grand : ¬CanFormGrandCoalition K) : ¬H2Trivial K :=
  hollow_tetrahedron_h2_nontrivial_ax K h_four h_triples h_no_grand

/-! ## Main Characterization -/

/-- Four agents: H² = 0 iff grand coalition exists -/
theorem four_agent_h2_iff_grand (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_four : Fintype.card K.vertexSet = 4)
    (h_pairs : AllPairsCoordinate K)
    (h_triples : AllTriplesCoordinate K) :
    H2Trivial K ↔ CanFormGrandCoalition K := by
  constructor
  · -- H² = 0 ⟹ grand coalition
    intro h_triv
    by_contra h_no_grand
    exact hollow_tetrahedron_h2_nontrivial K h_four h_triples h_no_grand h_triv
  · -- Grand coalition ⟹ H² = 0
    intro h_grand
    exact filled_tetrahedron_h2_trivial K h_four h_grand

#check h2_small_complex
#check filled_tetrahedron_h2_trivial
#check hollow_tetrahedron_h2_nontrivial
#check four_agent_h2_iff_grand

end H2Characterization
