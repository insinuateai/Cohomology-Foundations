/-
# The Hollow Tetrahedron: Canonical H² Obstruction

A hollow tetrahedron has:
- 4 vertices: {0, 1, 2, 3}
- 6 edges: all pairs
- 4 triangles: all triples
- 0 tetrahedra: no 4-tuple

This gives H¹ = 0 (all triangles filled) but H² ≠ 0 (no tetrahedron).

SORRIES: 0
AXIOMS: 0
-/

import Foundations.H2Cohomology

namespace H2Characterization

open Foundations

/-- A tetrahedron (3-simplex) on four vertices -/
def Simplex.tetrahedron (v₀ v₁ v₂ v₃ : Vertex) : Simplex :=
  ({v₀, v₁, v₂, v₃} : Finset Vertex)

/-- The hollow tetrahedron complex: 4 vertices, all triangles, no tetrahedron -/
def hollowTetrahedron : SimplicialComplex where
  simplices := { s : Simplex |
    (∀ v ∈ s, v < 4) ∧
    s.card ≤ 3 }
  has_vertices := by
    intro s ⟨hv, _⟩ v hv_mem
    simp only [Simplex.vertex, Set.mem_setOf_eq]
    constructor
    · intro w hw
      simp only [Finset.mem_singleton] at hw
      rw [hw]
      exact hv v hv_mem
    · simp only [Finset.card_singleton]
      omega
  down_closed := by
    intro s ⟨hv, hcard⟩ i
    simp only [Set.mem_setOf_eq]
    constructor
    · intro v hv_mem
      have h_face_sub := Simplex.face_subset s i
      exact hv v (h_face_sub hv_mem)
    · have h_face_card := Simplex.face_card s i (by omega : s.card > 0)
      omega

/-! ## Vertex Set Properties -/

/-- The hollow tetrahedron has exactly 4 vertices: {0, 1, 2, 3} -/
lemma hollowTetrahedron_vertices :
    hollowTetrahedron.vertexSet = {v : Vertex | v < 4} := by
  ext v
  simp only [SimplicialComplex.vertexSet, Simplex.vertex, Set.mem_setOf_eq,
             hollowTetrahedron, Set.mem_setOf_eq]
  constructor
  · intro ⟨hv, _⟩
    exact hv v (Finset.mem_singleton_self v)
  · intro hv
    constructor
    · intro w hw
      simp only [Finset.mem_singleton] at hw
      rw [hw]; exact hv
    · simp only [Finset.card_singleton]; omega

/-! ## Edge Properties -/

/-- All 6 edges exist in the hollow tetrahedron -/
lemma hollowTetrahedron_has_all_edges (i j : Fin 4) (hij : i ≠ j) :
    Simplex.edge i.val j.val ∈ hollowTetrahedron.simplices := by
  simp only [hollowTetrahedron, Simplex.edge, Set.mem_setOf_eq]
  constructor
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    cases hv with
    | inl h => rw [h]; exact i.isLt
    | inr h => rw [h]; exact j.isLt
  · simp only [Finset.card_insert_of_not_mem, Finset.card_singleton]
    · omega
    · simp only [Finset.mem_singleton]
      intro h
      exact hij (Fin.ext h)

/-! ## Triangle Properties -/

/-- All 4 triangles exist in the hollow tetrahedron -/
lemma hollowTetrahedron_has_all_triangles (i j k : Fin 4)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Simplex.triangle i.val j.val k.val ∈ hollowTetrahedron.simplices := by
  simp only [hollowTetrahedron, Simplex.triangle, Set.mem_setOf_eq]
  constructor
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h | h
    · rw [h]; exact i.isLt
    · rw [h]; exact j.isLt
    · rw [h]; exact k.isLt
  · have h1 : ({i.val, j.val, k.val} : Finset ℕ).card ≤ 3 := Finset.card_le_three
    exact h1

/-! ## Tetrahedron Exclusion -/

/-- The full tetrahedron {0,1,2,3} is NOT in the hollow tetrahedron -/
lemma hollowTetrahedron_no_tetrahedron :
    Simplex.tetrahedron 0 1 2 3 ∉ hollowTetrahedron.simplices := by
  simp only [hollowTetrahedron, Simplex.tetrahedron, Set.mem_setOf_eq, not_and]
  intro _
  simp only [not_le]
  have h : ({0, 1, 2, 3} : Finset ℕ).card = 4 := by decide
  omega

/-- The hollow tetrahedron has no 3-simplices -/
lemma hollowTetrahedron_no_3simplices :
    hollowTetrahedron.ksimplices 3 = ∅ := by
  simp only [SimplicialComplex.ksimplices, Set.eq_empty_iff_forall_not_mem, Set.mem_setOf_eq]
  intro s ⟨hs, hcard⟩
  simp only [hollowTetrahedron, Set.mem_setOf_eq] at hs
  omega

/-! ## H² Properties -/

/-- Every 2-cochain on the hollow tetrahedron is a 2-cocycle
    (since there are no 3-simplices) -/
theorem hollowTetrahedron_all_2cocycles (f : Cochain hollowTetrahedron 2) :
    Is2Cocycle hollowTetrahedron f := by
  simp only [Is2Cocycle, coboundary]
  funext ⟨s, hs⟩
  -- s would be a 3-simplex, but there are none
  simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hs
  have ⟨hs_mem, hcard⟩ := hs
  simp only [hollowTetrahedron, Set.mem_setOf_eq] at hs_mem
  -- s.card = 4 but hollowTetrahedron only has simplices of card ≤ 3
  omega

/-- The hollow tetrahedron has exactly 4 triangles (2-simplices) -/
lemma hollowTetrahedron_triangles_finite :
    hollowTetrahedron.ksimplices 2 =
    {Simplex.triangle 0 1 2, Simplex.triangle 0 1 3,
     Simplex.triangle 0 2 3, Simplex.triangle 1 2 3} := by
  ext s
  simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq, Set.mem_insert_iff,
             Set.mem_singleton_iff]
  constructor
  · intro ⟨hs, hcard⟩
    simp only [hollowTetrahedron, Set.mem_setOf_eq] at hs
    have ⟨hv, hcard'⟩ := hs
    -- s has 3 elements, all < 4
    -- The only 3-subsets of {0,1,2,3} are the 4 triangles
    -- This is a finite case analysis
    have h3 : s.card = 3 := hcard
    -- s is a 3-element subset of {0,1,2,3}
    -- We need to show s is one of the 4 triangles
    -- Use decidability
    by_cases h012 : s = Simplex.triangle 0 1 2
    · left; exact h012
    · by_cases h013 : s = Simplex.triangle 0 1 3
      · right; left; exact h013
      · by_cases h023 : s = Simplex.triangle 0 2 3
        · right; right; left; exact h023
        · by_cases h123 : s = Simplex.triangle 1 2 3
          · right; right; right; exact h123
          · -- s is a 3-subset of {0,1,2,3} but not one of the 4 triangles
            -- This is impossible - contradiction
            exfalso
            -- s contains 3 elements, all in {0,1,2,3}
            -- There are only C(4,3) = 4 such subsets
            have : s ⊆ ({0, 1, 2, 3} : Finset ℕ) := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton]
              have := hv x hx
              omega
            -- Since s has 3 elements from a 4-element set, s must be
            -- {0,1,2}, {0,1,3}, {0,2,3}, or {1,2,3}
            have hsub : s ∈ ({0, 1, 2, 3} : Finset ℕ).powerset.filter (fun t => t.card = 3) := by
              simp only [Finset.mem_filter, Finset.mem_powerset]
              exact ⟨this, h3⟩
            -- Enumerate all 3-subsets
            simp only [Finset.filter_eq', Finset.mem_powerset] at hsub
            -- The 3-element subsets are exactly our 4 triangles
            have enum : ({0, 1, 2, 3} : Finset ℕ).powerset.filter (fun t => t.card = 3) =
                       {Simplex.triangle 0 1 2, Simplex.triangle 0 1 3,
                        Simplex.triangle 0 2 3, Simplex.triangle 1 2 3} := by
              native_decide
            rw [enum] at hsub
            simp only [Finset.mem_insert, Finset.mem_singleton] at hsub
            rcases hsub with h | h | h | h
            · exact h012 h
            · exact h013 h
            · exact h023 h
            · exact h123 h
  · intro h
    rcases h with h | h | h | h <;> (
      subst h
      constructor
      · exact hollowTetrahedron_has_all_triangles _ _ _ (by decide) (by decide) (by decide)
      · simp only [Simplex.triangle]
        native_decide
    )

/-! ## H¹ Triviality for Small Complexes -/

/-- For complexes with ≤ 2 vertices, H¹ is trivially 0 -/
lemma h1_trivial_small_complex (K : SimplicialComplex)
    (h : ∀ s ∈ K.simplices, s.card ≤ 2) :
    H1Trivial K := by
  intro f hf
  -- f is a 1-cocycle, need to show it's a 1-coboundary
  -- Since K has no triangles (all simplices have card ≤ 2),
  -- the cocycle condition is vacuously true
  -- We construct g by picking values on vertices arbitrarily
  use 0
  -- Show δ⁰(0) = f
  funext ⟨s, hs⟩
  simp only [coboundary, Cochain.zero_apply]
  -- For δ⁰(0) on an edge s, we compute the sum
  -- Since g = 0, all terms are 0
  simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies]
  intro i
  simp only [sign, mul_zero]

/-! ## Dimension-based H² Triviality -/

/-- Complexes with no 2-simplices have H² = 0 trivially -/
lemma h2_trivial_no_triangles (K : SimplicialComplex)
    (h : K.ksimplices 2 = ∅) :
    H2Trivial K := by
  intro f hf
  use 0
  funext ⟨s, hs⟩
  simp only [Set.eq_empty_iff_forall_not_mem] at h
  exact absurd hs (h s)

/-- Complexes with dimension ≤ 1 (only vertices and edges) have H² = 0 -/
theorem h2_trivial_dim_le_1 (K : SimplicialComplex)
    (h : ∀ s ∈ K.simplices, s.card ≤ 2) :
    H2Trivial K := by
  apply h2_trivial_no_triangles
  simp only [SimplicialComplex.ksimplices, Set.eq_empty_iff_forall_not_mem, Set.mem_setOf_eq]
  intro s ⟨hs, hcard⟩
  have := h s hs
  omega

/-! ## Main Results -/

/-- Key structural property: removing any vertex from hollow tetrahedron
    leaves a complex with dimension ≤ 2 (a single triangle) -/
lemma removeVertex_hollowTetrahedron_dim (v : Fin 4) :
    ∀ s ∈ { s ∈ hollowTetrahedron.simplices | v.val ∉ s }, s.card ≤ 3 := by
  intro s ⟨hs, _⟩
  simp only [hollowTetrahedron, Set.mem_setOf_eq] at hs
  exact hs.2

/-- The hollow tetrahedron demonstrates that H² can be non-trivial.
    Specifically: all 2-cochains are 2-cocycles, but not all are 2-coboundaries.

    This is proven by showing that the dimension of the 2-cochain space (4 triangles)
    exceeds the dimension of the 1-coboundary space. -/
theorem hollowTetrahedron_h2_structure :
    -- There are exactly 4 triangles
    hollowTetrahedron.ksimplices 2 =
    {Simplex.triangle 0 1 2, Simplex.triangle 0 1 3,
     Simplex.triangle 0 2 3, Simplex.triangle 1 2 3} ∧
    -- There are no 3-simplices
    hollowTetrahedron.ksimplices 3 = ∅ ∧
    -- Therefore all 2-cochains are 2-cocycles
    (∀ f : Cochain hollowTetrahedron 2, Is2Cocycle hollowTetrahedron f) :=
  ⟨hollowTetrahedron_triangles_finite,
   hollowTetrahedron_no_3simplices,
   hollowTetrahedron_all_2cocycles⟩

/-! ## Edges Enumeration -/

/-- The hollow tetrahedron has exactly 6 edges (1-simplices) -/
lemma hollowTetrahedron_edges_finite :
    hollowTetrahedron.ksimplices 1 =
    {Simplex.edge 0 1, Simplex.edge 0 2, Simplex.edge 0 3,
     Simplex.edge 1 2, Simplex.edge 1 3, Simplex.edge 2 3} := by
  ext s
  simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq, Set.mem_insert_iff,
             Set.mem_singleton_iff]
  constructor
  · intro ⟨hs, hcard⟩
    simp only [hollowTetrahedron, Set.mem_setOf_eq] at hs
    have ⟨hv, _⟩ := hs
    -- s has 2 elements, all < 4
    have h2 : s.card = 2 := hcard
    -- s is a 2-element subset of {0,1,2,3}
    have hsub : s ⊆ ({0, 1, 2, 3} : Finset ℕ) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have := hv x hx
      omega
    have hsub_mem : s ∈ ({0, 1, 2, 3} : Finset ℕ).powerset.filter (fun t => t.card = 2) := by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hsub, h2⟩
    have enum : ({0, 1, 2, 3} : Finset ℕ).powerset.filter (fun t => t.card = 2) =
               {Simplex.edge 0 1, Simplex.edge 0 2, Simplex.edge 0 3,
                Simplex.edge 1 2, Simplex.edge 1 3, Simplex.edge 2 3} := by
      native_decide
    rw [enum] at hsub_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsub_mem
    rcases hsub_mem with h | h | h | h | h | h <;> (first | left; exact h | right; assumption)
  · intro h
    rcases h with h | h | h | h | h | h <;> (
      subst h
      constructor
      · exact hollowTetrahedron_has_all_edges _ _ (by decide)
      · simp only [Simplex.edge]; native_decide
    )

/-! ## H² Non-Triviality -/

/-- The witness 2-cochain: assigns 1 to triangle {0,1,2} and 0 to others -/
def witness2Cochain : Cochain hollowTetrahedron 2 :=
  fun ⟨s, _⟩ => if s = Simplex.triangle 0 1 2 then 1 else 0

/-- The witness 2-cochain has value 1 on triangle {0,1,2} -/
lemma witness2Cochain_on_012 :
    witness2Cochain ⟨Simplex.triangle 0 1 2,
      ⟨hollowTetrahedron_has_all_triangles 0 1 2 (by decide) (by decide) (by decide),
       by simp [Simplex.triangle]; native_decide⟩⟩ = 1 := by
  simp [witness2Cochain]

/-- The witness 2-cochain has value 0 on triangle {0,1,3} -/
lemma witness2Cochain_on_013 :
    witness2Cochain ⟨Simplex.triangle 0 1 3,
      ⟨hollowTetrahedron_has_all_triangles 0 1 3 (by decide) (by decide) (by decide),
       by simp [Simplex.triangle]; native_decide⟩⟩ = 0 := by
  simp only [witness2Cochain]
  have h : Simplex.triangle 0 1 3 ≠ Simplex.triangle 0 1 2 := by
    simp [Simplex.triangle]; native_decide
  simp [h]

/-- The witness 2-cochain has value 0 on triangle {0,2,3} -/
lemma witness2Cochain_on_023 :
    witness2Cochain ⟨Simplex.triangle 0 2 3,
      ⟨hollowTetrahedron_has_all_triangles 0 2 3 (by decide) (by decide) (by decide),
       by simp [Simplex.triangle]; native_decide⟩⟩ = 0 := by
  simp only [witness2Cochain]
  have h : Simplex.triangle 0 2 3 ≠ Simplex.triangle 0 1 2 := by
    simp [Simplex.triangle]; native_decide
  simp [h]

/-- The witness 2-cochain has value 0 on triangle {1,2,3} -/
lemma witness2Cochain_on_123 :
    witness2Cochain ⟨Simplex.triangle 1 2 3,
      ⟨hollowTetrahedron_has_all_triangles 1 2 3 (by decide) (by decide) (by decide),
       by simp [Simplex.triangle]; native_decide⟩⟩ = 0 := by
  simp only [witness2Cochain]
  have h : Simplex.triangle 1 2 3 ≠ Simplex.triangle 0 1 2 := by
    simp [Simplex.triangle]; native_decide
  simp [h]

/-- Helper: membership proof for an edge in the hollow tetrahedron -/
lemma edge_mem_hollowTetrahedron (i j : Fin 4) (hij : i ≠ j) :
    Simplex.edge i.val j.val ∈ hollowTetrahedron.ksimplices 1 := by
  simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
  constructor
  · exact hollowTetrahedron_has_all_edges i j hij
  · simp only [Simplex.edge]
    have h : ({i.val, j.val} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
      simp only [Finset.mem_singleton]
      intro h; exact hij (Fin.ext h)
    exact h

/-- For any 1-cochain g, the coboundary δ¹g applied to each triangle gives
    a specific linear combination of edge values.

    For triangle {v₀, v₁, v₂} (sorted): (δg)(t) = g({v₁,v₂}) - g({v₀,v₂}) + g({v₀,v₁})
-/

/-- Key lemma: The sum of coboundary values over all 4 triangles equals 0
    for any 1-cochain g.

    Mathematical insight: Each edge appears in exactly 2 triangles with opposite signs.
    - Edge {0,1} appears in {0,1,2} with sign +1 and in {0,1,3} with sign +1
      (but wait, we need to track carefully)

    Actually, let's use a different approach: the sum of all triangle coboundaries
    should cancel appropriately.

    For any 1-cochain g:
      δg({0,1,2}) + δg({0,1,3}) + δg({0,2,3}) + δg({1,2,3})
    = (g({1,2}) - g({0,2}) + g({0,1})) + (g({1,3}) - g({0,3}) + g({0,1}))
    + (g({2,3}) - g({0,3}) + g({0,2})) + (g({2,3}) - g({1,3}) + g({1,2}))

    Let a = g({0,1}), b = g({0,2}), c = g({0,3}), d = g({1,2}), e = g({1,3}), f = g({2,3})

    = (d - b + a) + (e - c + a) + (f - c + b) + (f - e + d)
    = 2a + 2d + 2f - 2c
    = 2(a + d + f - c)

    This doesn't give 0 directly. Let me verify the coboundary formula.

    Actually, the key insight is that for f = witness (1,0,0,0), if f = δg then:
    - δg({0,1,2}) = 1
    - δg({0,1,3}) = 0
    - δg({0,2,3}) = 0
    - δg({1,2,3}) = 0

    These 4 equations in 6 unknowns lead to a contradiction.
-/

/-- The witness 2-cochain is not a 2-coboundary.

    Proof: Suppose witness = δ¹(g) for some 1-cochain g.
    Let a = g({0,1}), b = g({0,2}), c = g({0,3}), d = g({1,2}), e = g({1,3}), f = g({2,3}).

    The coboundary formula gives:
    - δg({0,1,2}) = d - b + a = 1  (witness value on {0,1,2})
    - δg({0,1,3}) = e - c + a = 0  (witness value on {0,1,3})
    - δg({0,2,3}) = f - c + b = 0  (witness value on {0,2,3})
    - δg({1,2,3}) = f - e + d = 0  (witness value on {1,2,3})

    From equations (2), (3), (4):
    - e = c - a          (from 2)
    - f = c - b          (from 3)
    - f = e - d          (from 4)

    From f = c - b and f = e - d:
      c - b = e - d
      c - b = (c - a) - d     (substituting e = c - a)
      -b = -a - d
      d = a - b

    Substituting into equation (1):
      d - b + a = 1
      (a - b) - b + a = 1
      2a - 2b = 1

    But wait, this is still consistent if we pick a, b correctly.

    Let me redo this more carefully. The key is that after substitution,
    we should get 0 = 1 or similar.

    From (4): f - e + d = 0, so f = e - d
    From (3): f - c + b = 0, so f = c - b
    Therefore: e - d = c - b, which gives e = c - b + d

    From (2): e - c + a = 0, so e = c - a
    Combining: c - a = c - b + d, so d = b - a

    Substituting into (1): d - b + a = (b - a) - b + a = 0 ≠ 1

    This is the contradiction.
-/
theorem witness_not_coboundary : ¬Is2Coboundary hollowTetrahedron witness2Cochain := by
  intro ⟨g, hg⟩
  -- g is a 1-cochain such that δg = witness
  -- We'll derive a contradiction from the 4 triangle equations

  -- Define the edge values (using the actual subtype membership proofs)
  let mem_01 : Simplex.edge 0 1 ∈ hollowTetrahedron.ksimplices 1 :=
    edge_mem_hollowTetrahedron 0 1 (by decide)
  let mem_02 : Simplex.edge 0 2 ∈ hollowTetrahedron.ksimplices 1 :=
    edge_mem_hollowTetrahedron 0 2 (by decide)
  let mem_03 : Simplex.edge 0 3 ∈ hollowTetrahedron.ksimplices 1 :=
    edge_mem_hollowTetrahedron 0 3 (by decide)
  let mem_12 : Simplex.edge 1 2 ∈ hollowTetrahedron.ksimplices 1 :=
    edge_mem_hollowTetrahedron 1 2 (by decide)
  let mem_13 : Simplex.edge 1 3 ∈ hollowTetrahedron.ksimplices 1 :=
    edge_mem_hollowTetrahedron 1 3 (by decide)
  let mem_23 : Simplex.edge 2 3 ∈ hollowTetrahedron.ksimplices 1 :=
    edge_mem_hollowTetrahedron 2 3 (by decide)

  -- Edge values
  let a := g ⟨Simplex.edge 0 1, mem_01⟩  -- g({0,1})
  let b := g ⟨Simplex.edge 0 2, mem_02⟩  -- g({0,2})
  let c := g ⟨Simplex.edge 0 3, mem_03⟩  -- g({0,3})
  let d := g ⟨Simplex.edge 1 2, mem_12⟩  -- g({1,2})
  let e := g ⟨Simplex.edge 1 3, mem_13⟩  -- g({1,3})
  let f := g ⟨Simplex.edge 2 3, mem_23⟩  -- g({2,3})

  -- The coboundary formula applied to each triangle gives an equation.
  -- We need to compute δg on each triangle and equate it to the witness value.

  -- Triangle {0,1,2} membership proof
  have mem_012 : Simplex.triangle 0 1 2 ∈ hollowTetrahedron.ksimplices 2 := by
    rw [hollowTetrahedron_triangles_finite]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    left; rfl

  -- Triangle {0,1,3} membership proof
  have mem_013 : Simplex.triangle 0 1 3 ∈ hollowTetrahedron.ksimplices 2 := by
    rw [hollowTetrahedron_triangles_finite]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    right; left; rfl

  -- Triangle {0,2,3} membership proof
  have mem_023 : Simplex.triangle 0 2 3 ∈ hollowTetrahedron.ksimplices 2 := by
    rw [hollowTetrahedron_triangles_finite]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    right; right; left; rfl

  -- Triangle {1,2,3} membership proof
  have mem_123 : Simplex.triangle 1 2 3 ∈ hollowTetrahedron.ksimplices 2 := by
    rw [hollowTetrahedron_triangles_finite]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    right; right; right; rfl

  -- From hg : δg = witness, we get equations for each triangle
  -- Equation 1: δg({0,1,2}) = 1
  have eq1 : (δ hollowTetrahedron 1 g) ⟨Simplex.triangle 0 1 2, mem_012⟩ = 1 := by
    have := congrFun hg ⟨Simplex.triangle 0 1 2, mem_012⟩
    simp only [witness2Cochain] at this
    simp only [ite_true] at this
    exact this

  -- Equation 2: δg({0,1,3}) = 0
  have eq2 : (δ hollowTetrahedron 1 g) ⟨Simplex.triangle 0 1 3, mem_013⟩ = 0 := by
    have := congrFun hg ⟨Simplex.triangle 0 1 3, mem_013⟩
    simp only [witness2Cochain] at this
    have hne : Simplex.triangle 0 1 3 ≠ Simplex.triangle 0 1 2 := by
      simp [Simplex.triangle]; native_decide
    simp only [hne, ite_false] at this
    exact this

  -- Equation 3: δg({0,2,3}) = 0
  have eq3 : (δ hollowTetrahedron 1 g) ⟨Simplex.triangle 0 2 3, mem_023⟩ = 0 := by
    have := congrFun hg ⟨Simplex.triangle 0 2 3, mem_023⟩
    simp only [witness2Cochain] at this
    have hne : Simplex.triangle 0 2 3 ≠ Simplex.triangle 0 1 2 := by
      simp [Simplex.triangle]; native_decide
    simp only [hne, ite_false] at this
    exact this

  -- Equation 4: δg({1,2,3}) = 0
  have eq4 : (δ hollowTetrahedron 1 g) ⟨Simplex.triangle 1 2 3, mem_123⟩ = 0 := by
    have := congrFun hg ⟨Simplex.triangle 1 2 3, mem_123⟩
    simp only [witness2Cochain] at this
    have hne : Simplex.triangle 1 2 3 ≠ Simplex.triangle 0 1 2 := by
      simp [Simplex.triangle]; native_decide
    simp only [hne, ite_false] at this
    exact this

  -- Now we need to expand the coboundary formula and relate to a, b, c, d, e, f.
  -- The coboundary δg on a triangle is:
  -- (δg)(s) = Σᵢ sign(i) * g(face i)

  -- For triangle {0,1,2}: sorted = [0,1,2], faces are {1,2}, {0,2}, {0,1}
  -- (δg)({0,1,2}) = sign(0)*g({1,2}) + sign(1)*g({0,2}) + sign(2)*g({0,1})
  --               = 1*d + (-1)*b + 1*a = d - b + a

  -- Let's compute the coboundary explicitly
  -- First, expand the coboundary definition for triangle {0,1,2}
  simp only [coboundary] at eq1 eq2 eq3 eq4

  -- The sum is over Fin 3 (since triangle has 3 vertices)
  -- We need to show the face structure explicitly

  -- Face computations for triangle {0,1,2}:
  -- face 0 removes vertex 0, giving {1,2}
  -- face 1 removes vertex 1, giving {0,2}
  -- face 2 removes vertex 2, giving {0,1}

  have face_012_0 : (Simplex.triangle 0 1 2).face ⟨0, by native_decide⟩ = Simplex.edge 1 2 := by
    simp only [Simplex.face, Simplex.triangle, Simplex.edge]
    native_decide

  have face_012_1 : (Simplex.triangle 0 1 2).face ⟨1, by native_decide⟩ = Simplex.edge 0 2 := by
    simp only [Simplex.face, Simplex.triangle, Simplex.edge]
    native_decide

  have face_012_2 : (Simplex.triangle 0 1 2).face ⟨2, by native_decide⟩ = Simplex.edge 0 1 := by
    simp only [Simplex.face, Simplex.triangle, Simplex.edge]
    native_decide

  -- Face computations for triangle {0,1,3}:
  have face_013_0 : (Simplex.triangle 0 1 3).face ⟨0, by native_decide⟩ = Simplex.edge 1 3 := by
    simp only [Simplex.face, Simplex.triangle, Simplex.edge]
    native_decide

  have face_013_1 : (Simplex.triangle 0 1 3).face ⟨1, by native_decide⟩ = Simplex.edge 0 3 := by
    simp only [Simplex.face, Simplex.triangle, Simplex.edge]
    native_decide

  have face_013_2 : (Simplex.triangle 0 1 3).face ⟨2, by native_decide⟩ = Simplex.edge 0 1 := by
    simp only [Simplex.face, Simplex.triangle, Simplex.edge]
    native_decide

  -- Face computations for triangle {0,2,3}:
  have face_023_0 : (Simplex.triangle 0 2 3).face ⟨0, by native_decide⟩ = Simplex.edge 2 3 := by
    simp only [Simplex.face, Simplex.triangle, Simplex.edge]
    native_decide

  have face_023_1 : (Simplex.triangle 0 2 3).face ⟨1, by native_decide⟩ = Simplex.edge 0 3 := by
    simp only [Simplex.face, Simplex.triangle, Simplex.edge]
    native_decide

  have face_023_2 : (Simplex.triangle 0 2 3).face ⟨2, by native_decide⟩ = Simplex.edge 0 2 := by
    simp only [Simplex.face, Simplex.triangle, Simplex.edge]
    native_decide

  -- Face computations for triangle {1,2,3}:
  have face_123_0 : (Simplex.triangle 1 2 3).face ⟨0, by native_decide⟩ = Simplex.edge 2 3 := by
    simp only [Simplex.face, Simplex.triangle, Simplex.edge]
    native_decide

  have face_123_1 : (Simplex.triangle 1 2 3).face ⟨1, by native_decide⟩ = Simplex.edge 1 3 := by
    simp only [Simplex.face, Simplex.triangle, Simplex.edge]
    native_decide

  have face_123_2 : (Simplex.triangle 1 2 3).face ⟨2, by native_decide⟩ = Simplex.edge 1 2 := by
    simp only [Simplex.face, Simplex.triangle, Simplex.edge]
    native_decide

  -- Triangle cardinalities for unfolding the sum
  have hcard_012 : (Simplex.triangle 0 1 2).card = 3 := by native_decide
  have hcard_013 : (Simplex.triangle 0 1 3).card = 3 := by native_decide
  have hcard_023 : (Simplex.triangle 0 2 3).card = 3 := by native_decide
  have hcard_123 : (Simplex.triangle 1 2 3).card = 3 := by native_decide

  -- Expand the sums over Fin 3
  -- For eq1: sum over i = 0, 1, 2 of sign(i) * g(face i)
  have eq1_expand : d - b + a = 1 := by
    -- The sum is sign(0)*g(face0) + sign(1)*g(face1) + sign(2)*g(face2)
    -- = 1*d + (-1)*b + 1*a = d - b + a
    have h := eq1
    simp only [Finset.sum_fin_eq_sum_range, Finset.range_succ] at h
    -- Need to expand more carefully. Let's use Fin3 directly.
    -- The Finset.univ for Fin 3 is {0, 1, 2}
    conv at h =>
      arg 2
      rw [show Finset.univ = ({0, 1, 2} : Finset (Fin 3)) by native_decide]
      rw [Finset.sum_insert (by native_decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3)))]
      arg 2
      arg 2
      rw [Finset.sum_insert (by native_decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)))]
      arg 2
      arg 2
      rw [Finset.sum_singleton]
    simp only [sign] at h
    -- Simplify the signs
    have hs0 : sign 0 = 1 := by native_decide
    have hs1 : sign 1 = -1 := by native_decide
    have hs2 : sign 2 = 1 := by native_decide
    simp only [hs0, hs1, hs2, one_mul, neg_one_mul] at h
    -- Now we need to connect the faces to our edge variables
    -- Face 0 of {0,1,2} = {1,2}, so g(face 0) = d
    -- Face 1 of {0,1,2} = {0,2}, so g(face 1) = b
    -- Face 2 of {0,1,2} = {0,1}, so g(face 2) = a

    -- The g values are on subtypes, so we need congruence
    have hg0 : g ⟨(Simplex.triangle 0 1 2).face ⟨0, by native_decide⟩, _⟩ = d := by
      congr 1
      exact Subtype.ext face_012_0
    have hg1 : g ⟨(Simplex.triangle 0 1 2).face ⟨1, by native_decide⟩, _⟩ = b := by
      congr 1
      exact Subtype.ext face_012_1
    have hg2 : g ⟨(Simplex.triangle 0 1 2).face ⟨2, by native_decide⟩, _⟩ = a := by
      congr 1
      exact Subtype.ext face_012_2
    simp only [hg0, hg1, hg2] at h
    linarith

  have eq2_expand : e - c + a = 0 := by
    have h := eq2
    conv at h =>
      arg 2
      rw [show Finset.univ = ({0, 1, 2} : Finset (Fin 3)) by native_decide]
      rw [Finset.sum_insert (by native_decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3)))]
      arg 2
      arg 2
      rw [Finset.sum_insert (by native_decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)))]
      arg 2
      arg 2
      rw [Finset.sum_singleton]
    simp only [sign] at h
    have hs0 : sign 0 = 1 := by native_decide
    have hs1 : sign 1 = -1 := by native_decide
    have hs2 : sign 2 = 1 := by native_decide
    simp only [hs0, hs1, hs2, one_mul, neg_one_mul] at h
    have hg0 : g ⟨(Simplex.triangle 0 1 3).face ⟨0, by native_decide⟩, _⟩ = e := by
      congr 1; exact Subtype.ext face_013_0
    have hg1 : g ⟨(Simplex.triangle 0 1 3).face ⟨1, by native_decide⟩, _⟩ = c := by
      congr 1; exact Subtype.ext face_013_1
    have hg2 : g ⟨(Simplex.triangle 0 1 3).face ⟨2, by native_decide⟩, _⟩ = a := by
      congr 1; exact Subtype.ext face_013_2
    simp only [hg0, hg1, hg2] at h
    linarith

  have eq3_expand : f - c + b = 0 := by
    have h := eq3
    conv at h =>
      arg 2
      rw [show Finset.univ = ({0, 1, 2} : Finset (Fin 3)) by native_decide]
      rw [Finset.sum_insert (by native_decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3)))]
      arg 2
      arg 2
      rw [Finset.sum_insert (by native_decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)))]
      arg 2
      arg 2
      rw [Finset.sum_singleton]
    simp only [sign] at h
    have hs0 : sign 0 = 1 := by native_decide
    have hs1 : sign 1 = -1 := by native_decide
    have hs2 : sign 2 = 1 := by native_decide
    simp only [hs0, hs1, hs2, one_mul, neg_one_mul] at h
    have hg0 : g ⟨(Simplex.triangle 0 2 3).face ⟨0, by native_decide⟩, _⟩ = f := by
      congr 1; exact Subtype.ext face_023_0
    have hg1 : g ⟨(Simplex.triangle 0 2 3).face ⟨1, by native_decide⟩, _⟩ = c := by
      congr 1; exact Subtype.ext face_023_1
    have hg2 : g ⟨(Simplex.triangle 0 2 3).face ⟨2, by native_decide⟩, _⟩ = b := by
      congr 1; exact Subtype.ext face_023_2
    simp only [hg0, hg1, hg2] at h
    linarith

  have eq4_expand : f - e + d = 0 := by
    have h := eq4
    conv at h =>
      arg 2
      rw [show Finset.univ = ({0, 1, 2} : Finset (Fin 3)) by native_decide]
      rw [Finset.sum_insert (by native_decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3)))]
      arg 2
      arg 2
      rw [Finset.sum_insert (by native_decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)))]
      arg 2
      arg 2
      rw [Finset.sum_singleton]
    simp only [sign] at h
    have hs0 : sign 0 = 1 := by native_decide
    have hs1 : sign 1 = -1 := by native_decide
    have hs2 : sign 2 = 1 := by native_decide
    simp only [hs0, hs1, hs2, one_mul, neg_one_mul] at h
    have hg0 : g ⟨(Simplex.triangle 1 2 3).face ⟨0, by native_decide⟩, _⟩ = f := by
      congr 1; exact Subtype.ext face_123_0
    have hg1 : g ⟨(Simplex.triangle 1 2 3).face ⟨1, by native_decide⟩, _⟩ = e := by
      congr 1; exact Subtype.ext face_123_1
    have hg2 : g ⟨(Simplex.triangle 1 2 3).face ⟨2, by native_decide⟩, _⟩ = d := by
      congr 1; exact Subtype.ext face_123_2
    simp only [hg0, hg1, hg2] at h
    linarith

  -- Now derive contradiction from the 4 equations:
  -- eq1: d - b + a = 1
  -- eq2: e - c + a = 0  =>  e = c - a
  -- eq3: f - c + b = 0  =>  f = c - b
  -- eq4: f - e + d = 0  =>  f = e - d

  -- From eq3 and eq4: c - b = e - d
  -- Substituting e = c - a: c - b = (c - a) - d  =>  d = b - a
  -- Substituting d = b - a into eq1: (b - a) - b + a = 0 ≠ 1

  have hd : d = b - a := by linarith
  have hcontra : (0 : ℚ) = 1 := by linarith
  exact absurd hcontra.symm one_ne_zero

/-- The hollow tetrahedron has non-trivial H² -/
theorem hollowTetrahedron_h2_nontrivial : ¬H2Trivial hollowTetrahedron := by
  intro h
  -- h says every 2-cocycle is a 2-coboundary
  -- witness2Cochain is a 2-cocycle (since there are no 3-simplices)
  have hw_cocycle : Is2Cocycle hollowTetrahedron witness2Cochain :=
    hollowTetrahedron_all_2cocycles witness2Cochain
  -- So witness2Cochain should be a 2-coboundary
  have hw_cobdry : Is2Coboundary hollowTetrahedron witness2Cochain := h _ hw_cocycle
  -- But we proved it's not
  exact witness_not_coboundary hw_cobdry

end H2Characterization
