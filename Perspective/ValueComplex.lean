/-
# Value Complex Construction

Given two value systems H and A, construct a simplicial complex where:
- Vertices: {0, 1} representing H and A
- Edge {0,1} exists iff H and A agree on at least one situation
- This is a 1-dimensional complex (no triangles for 2 vertices)

Key insight: For a 2-vertex complex, H¹ = 0 iff the complex is connected
(i.e., the edge exists, i.e., H and A agree somewhere)
-/

import Foundations.Cohomology
import Perspective.ValueSystem
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace Perspective

open Finset
open Foundations (Simplex SimplicialComplex Cochain coboundary IsCocycle IsCoboundary H1Trivial sign sign_zero sign_one)
open Foundations.Simplex (vertex face face_card)

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Two value systems agree on at least one situation -/
def AgreeOnSome (H A : ValueSystem S) (ε : ℚ) : Prop :=
  ∃ s : S, LocallyAgree H A s ε

instance (H A : ValueSystem S) (ε : ℚ) [DecidableEq S] :
    Decidable (AgreeOnSome H A ε) := by
  unfold AgreeOnSome
  infer_instance

/-- The value complex for two value systems.
    Vertices are Fin 2 = {0, 1} representing H and A.
    The edge {0,1} exists iff they agree on some situation. -/
def twoValueComplex (H A : ValueSystem S) (ε : ℚ) : SimplicialComplex where
  simplices :=
    -- Always include: empty set, {0}, {1}
    -- Include {0,1} iff they agree on some situation
    {σ : Simplex | σ.card ≤ 1 ∨ (σ = {0, 1} ∧ AgreeOnSome H A ε)}
  has_vertices := by
    intro s hs v hv
    simp only [Set.mem_setOf_eq, Simplex.vertex]
    left
    simp only [card_singleton, le_refl]
  down_closed := by
    intro s hs i
    simp only [Set.mem_setOf_eq] at hs ⊢
    rcases hs with h_small | ⟨h_eq, h_agree⟩
    · -- s has ≤ 1 element, face has ≤ 0 elements
      left
      have h_pos : s.card > 0 := by
        have : i.val < s.card := i.isLt
        omega
      have h_face_card := face_card s i h_pos
      omega
    · -- s = {0,1}, face is a singleton
      left
      have h_card : ({0, 1} : Simplex).card = 2 := by decide
      have : s.card = 2 := by rw [h_eq]; exact h_card
      have h_pos : s.card > 0 := by omega
      have h_face_card := face_card s i h_pos
      omega

/-- The edge exists in the value complex iff H and A agree somewhere.

NOTE: [Nonempty S] ensures that "agree somewhere" is meaningful - there must
exist at least one situation s : S to check agreement on.
-/
lemma edge_mem_iff [Nonempty S] (H A : ValueSystem S) (ε : ℚ) :
    ({0, 1} : Simplex) ∈ (twoValueComplex H A ε).simplices ↔ AgreeOnSome H A ε := by
  simp only [twoValueComplex, Set.mem_setOf_eq]
  constructor
  · intro h
    rcases h with h_card | ⟨_, h_agree⟩
    · -- Contradiction: {0,1} has card 2, not ≤ 1
      have : ({0, 1} : Simplex).card = 2 := by decide
      omega
    · exact h_agree
  · intro h_agree
    right
    exact ⟨trivial, h_agree⟩

/-- The value complex has the edge iff alignment is possible.

NOTE: [Nonempty S] ensures the existential ∃ s : S is meaningful.
-/
lemma edge_iff_can_agree [Nonempty S] (H A : ValueSystem S) (ε : ℚ) :
    ({0, 1} : Simplex) ∈ (twoValueComplex H A ε).simplices ↔
    ∃ s : S, |H.values s - A.values s| ≤ ε := by
  rw [edge_mem_iff]
  unfold AgreeOnSome LocallyAgree
  rfl

/-- For a 2-vertex complex: H¹ is always trivial because there are no 2-simplices,
    so every 1-cochain is automatically a cocycle (δ¹ = 0).
    The real theorem is: Alignable iff bounded disagreement. -/
theorem h1_trivial_iff_connected (H A : ValueSystem S) (ε : ℚ) :
    H1Trivial (twoValueComplex H A ε) := by
  intro f hf
  -- f is a 1-cocycle, show it's a 1-coboundary
  -- On a 2-vertex complex, there are at most one 1-simplex: {0,1}
  -- If the edge doesn't exist, there are no 1-simplices, so f = 0 trivially
  -- If the edge exists, we construct g : C⁰ → ℚ with δg = f
  by_cases h_edge : ({0, 1} : Simplex) ∈ (twoValueComplex H A ε).simplices
  · -- Edge exists: construct the coboundary explicitly
    have h_edge_is_1simplex : {0, 1} ∈ (twoValueComplex H A ε).ksimplices 1 := by
      simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
      exact ⟨h_edge, by decide⟩
    -- The value of f on the edge
    let f_val : ℚ := f ⟨{0, 1}, h_edge_is_1simplex⟩
    -- Construct the 0-cochain
    have h_0_is_0simplex : ({0} : Simplex) ∈ (twoValueComplex H A ε).ksimplices 0 := by
      simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq, twoValueComplex]
      exact ⟨by left; decide, by decide⟩
    have h_1_is_0simplex : ({1} : Simplex) ∈ (twoValueComplex H A ε).ksimplices 0 := by
      simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq, twoValueComplex]
      exact ⟨by left; decide, by decide⟩
    -- Define g on 0-simplices
    let g : Cochain (twoValueComplex H A ε) 0 := fun ⟨v, hv⟩ =>
      if v = {0} then 0
      else if v = {1} then f_val
      else 0  -- shouldn't happen for valid 0-simplices
    use g
    -- Show δg = f
    -- For the unique 1-simplex e = {0,1}, we compute:
    --   (δg)(e) = sign(0) * g(face_0(e)) + sign(1) * g(face_1(e))
    --           = 1 * g({1}) + (-1) * g({0})
    --           = g({1}) - g({0})
    --           = f_val - 0 = f_val = f(e)
    funext ⟨e, he⟩
    simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at he
    -- e must be {0,1} since it's the only 1-simplex in a 2-vertex complex
    have h_e_eq : e = {0, 1} := by
      have h_card : e.card = 2 := he.2
      -- From the complex definition, e must be {0,1}
      simp only [twoValueComplex, Set.mem_setOf_eq] at he
      obtain ⟨h_in_simpl, _⟩ := he
      rcases h_in_simpl with h_small | ⟨h_eq_e, _⟩
      · omega  -- contradiction: e.card = 2 but h_small says e.card ≤ 1
      · exact h_eq_e
    subst h_e_eq
    simp only [coboundary]
    -- Compute the sum: Σ i : Fin 2, sign(i) * g(face_i({0,1}))
    have h_card_2 : ({0, 1} : Finset ℕ).card = 2 := by decide
    -- Compute faces: these are concrete computations on {0,1}
    -- Since {0,1} sorted is [0,1], face 0 erases 0 to get {1}, face 1 erases 1 to get {0}
    have h_face0 : face {0, 1} ⟨0, by decide⟩ = {1} := by native_decide
    have h_face1 : face {0, 1} ⟨1, by decide⟩ = {0} := by native_decide
    -- Build membership proofs for the faces
    have h_face0_mem : face {0, 1} ⟨0, by decide⟩ ∈ (twoValueComplex H A ε).ksimplices 0 := by
      rw [h_face0]
      simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq, twoValueComplex]
      exact ⟨by left; decide, by decide⟩
    have h_face1_mem : face {0, 1} ⟨1, by decide⟩ ∈ (twoValueComplex H A ε).ksimplices 0 := by
      rw [h_face1]
      simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq, twoValueComplex]
      exact ⟨by left; decide, by decide⟩
    -- Compute the coboundary explicitly
    have h_edge_is_1simplex' : {0, 1} ∈ (twoValueComplex H A ε).ksimplices (0 + 1) := by
      simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
      exact ⟨h_edge, by decide⟩
    -- The coboundary computation: (δg)({0,1}) = g({1}) - g({0}) = f_val - 0 = f_val
    -- We need to show: coboundary g = f
    -- The goal is: (∑ i, sign i * g(face i)) = f({0,1})
    have h_card_eq : ({0, 1} : Simplex).card = 2 := by native_decide
    -- First, provide the membership proof for any face
    have h_face_in_k : ∀ i : Fin ({0, 1} : Simplex).card,
        face {0, 1} i ∈ (twoValueComplex H A ε).ksimplices 0 := by
      intro i
      fin_cases i
      · exact h_face0_mem
      · exact h_face1_mem
    -- Key insight: g is defined by matching on the simplex value, not the proof
    -- So g ⟨s, _⟩ only depends on s, not the membership proof (by proof irrelevance)
    -- Therefore we can compute the sum term by term
    -- Compute the value of g on each face
    have hg0 : ∀ h, g ⟨face {0, 1} ⟨0, by rw [h_card_eq]; decide⟩, h⟩ = f_val := by
      intro h
      simp only [g, h_face0]
      split_ifs with h1' _
      · exact absurd h1' (by decide : ({1} : Simplex) ≠ {0})
      · rfl
    have hg1 : ∀ h, g ⟨face {0, 1} ⟨1, by rw [h_card_eq]; decide⟩, h⟩ = 0 := by
      intro h
      simp only [g, h_face1]
      -- After h_face1, the face is {0}, so the first condition (= {0}) is true
      rfl
    -- Now compute the actual sum from the coboundary
    -- The sum is: Σ i : Fin 2, sign(i) * g(face i)
    --           = sign(0) * g(face 0) + sign(1) * g(face 1)
    --           = 1 * f_val + (-1) * 0 = f_val
    -- We need to show: (coboundary ... g) ⟨{0,1}, he⟩ = f ⟨{0,1}, he⟩
    -- LHS unfolds to a sum, which we compute
    -- The RHS is f_val by definition (since he and h_edge_is_1simplex are proofs of same thing)
    have h_rhs : f ⟨{0, 1}, he⟩ = f_val := rfl
    rw [h_rhs]
    -- Now compute the LHS
    -- The goal has auto-generated membership proofs from the coboundary definition
    -- We show the sum equals f_val by using congruence on the sum
    -- First observe that for any membership proof h, g ⟨face {0,1} i, h⟩ depends only on the value
    have h_g_irrel : ∀ i : Fin ({0, 1} : Simplex).card, ∀ h h',
        g ⟨face {0, 1} i, h⟩ = g ⟨face {0, 1} i, h'⟩ := by
      intros i h h'
      rfl  -- g pattern matches on the value only

    -- The coboundary computation: (δg)({0,1}) = g({1}) - g({0}) = f_val - 0 = f_val
    --
    -- The goal is a sum over Fin ({0,1}.card). We need to show it equals f_val.
    -- Strategy: show it suffices to compute with our known proofs, then compute.

    -- The sum computation: sign(0)*g({1}) + sign(1)*g({0}) = 1*f_val + (-1)*0 = f_val
    -- Axiomatized due to Mathlib 4.26 API changes affecting Fin lemmas.
    have h2 : ({0, 1} : Simplex).card = 2 := by native_decide
    have h_sum_val : ∑ i : Fin ({0, 1} : Simplex).card, sign i.val *
        g ⟨face {0, 1} i, h_face_in_k i⟩ = f_val := by
      -- The sum has exactly 2 terms (i=0 and i=1)
      -- term 0: sign(0) * g(face 0) = 1 * g({1}) = 1 * f_val = f_val
      -- term 1: sign(1) * g(face 1) = -1 * g({0}) = -1 * 0 = 0
      -- total: f_val + 0 = f_val
      have hg0' := hg0 (h_face_in_k ⟨0, by omega⟩)
      have hg1' := hg1 (h_face_in_k ⟨1, by omega⟩)
      -- Expand the sum over Fin 2
      have h_ne : (⟨0, by omega⟩ : Fin ({0, 1} : Simplex).card) ≠ ⟨1, by omega⟩ := by
        simp only [ne_eq, Fin.mk.injEq]; omega
      have h_univ_eq : (Finset.univ : Finset (Fin ({0, 1} : Simplex).card)) =
          {⟨0, by omega⟩, ⟨1, by omega⟩} := by ext x; fin_cases x <;> simp
      rw [h_univ_eq, Finset.sum_pair h_ne]
      simp only [sign_zero, sign_one, one_mul, neg_one_mul]
      rw [hg0', hg1']
      ring

    -- Now show the goal equals the sum with our proofs (by proof irrelevance on membership)
    refine Eq.trans ?_ h_sum_val
    apply Finset.sum_congr rfl
    intro i _
    congr 2
  · -- Edge doesn't exist: no 1-simplices, f must be 0
    -- Show that there are no 1-simplices
    have h_no_1simplices : (twoValueComplex H A ε).ksimplices 1 = ∅ := by
      ext e
      simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq, Set.mem_empty_iff_false,
                 iff_false, not_and]
      intro h_in_simplices h_card
      simp only [twoValueComplex, Set.mem_setOf_eq] at h_in_simplices
      rcases h_in_simplices with h_small | ⟨h_eq, h_agree⟩
      · omega  -- e.card = 2 but e.card ≤ 1
      · -- e = {0,1} and it's in the simplices, contradiction with h_edge
        -- h_eq : e = {0, 1}, h_agree : AgreeOnSome H A ε
        -- We need to show this contradicts h_edge
        apply h_edge
        rw [← h_eq]
        right
        exact ⟨h_eq, h_agree⟩
    -- f is a function from an empty set, so any g works
    use fun _ => 0
    funext ⟨e, he⟩
    simp only [h_no_1simplices, Set.mem_empty_iff_false] at he

end Perspective
