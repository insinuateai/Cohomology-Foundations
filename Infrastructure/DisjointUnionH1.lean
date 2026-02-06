/-
# Disjoint Union H1 Infrastructure

This file provides infrastructure for disjoint union of simplicial complexes.

Key definitions:
- `AreDisjoint K₁ K₂`: K₁ and K₂ have no shared vertices
- `glueCochains0`: Glue 0-cochains from disjoint complexes

Key theorem:
- `h1_trivial_disjoint_union`: H¹(K₁)=0 ∧ H¹(K₂)=0 ∧ disjoint → H¹(K₁∪K₂)=0

SORRIES: 0
AXIOMS: 0
-/

import Infrastructure.CochainRestriction
import Perspective.ValueComplex

namespace Infrastructure.DisjointUnionH1

open Foundations (Simplex SimplicialComplex Cochain IsCocycle IsCoboundary H1Trivial coboundary sign)
open Infrastructure.CochainRestriction (union inter IsSubcomplex restrictCochain)
open Perspective (ValueSystem valueComplex)

-- Use classical decidability throughout
open Classical in
attribute [local instance] propDecidable

/-! ## Part 1: Disjoint Complexes -/

/-- Two simplicial complexes are disjoint if they have no shared vertices. -/
def AreDisjoint (K₁ K₂ : SimplicialComplex) : Prop :=
  K₁.vertexSet ∩ K₂.vertexSet = ∅

/-- Disjoint complexes have no shared nonempty simplices. -/
theorem disjoint_no_shared_simplices (K₁ K₂ : SimplicialComplex) (h : AreDisjoint K₁ K₂) :
    ∀ s, s ∈ K₁.simplices → s ∈ K₂.simplices → s = ∅ := by
  intro s h₁ h₂
  by_contra h_ne
  have hs_nonempty : s.Nonempty := Finset.nonempty_of_ne_empty h_ne
  obtain ⟨v, hv⟩ := hs_nonempty
  have hv₁ : v ∈ K₁.vertexSet := SimplicialComplex.vertex_of_mem_simplex K₁ s h₁ v hv
  have hv₂ : v ∈ K₂.vertexSet := SimplicialComplex.vertex_of_mem_simplex K₂ s h₂ v hv
  have : v ∈ K₁.vertexSet ∩ K₂.vertexSet := ⟨hv₁, hv₂⟩
  rw [h] at this
  exact this

/-- K₁ is a subcomplex of K₁ ∪ K₂. -/
theorem left_sub_union (K₁ K₂ : SimplicialComplex) : K₁ ⊆ₛ union K₁ K₂ :=
  fun _ hs => Or.inl hs

/-- K₂ is a subcomplex of K₁ ∪ K₂. -/
theorem right_sub_union (K₁ K₂ : SimplicialComplex) : K₂ ⊆ₛ union K₁ K₂ :=
  fun _ hs => Or.inr hs

/-! ## Part 2: Cochain Construction for Disjoint Complexes -/

/-- A simplex in the union of disjoint complexes is in exactly one of them (unless empty). -/
theorem simplex_in_exactly_one (K₁ K₂ : SimplicialComplex) (h : AreDisjoint K₁ K₂)
    (s : Simplex) (hs : s ∈ (union K₁ K₂).simplices) (hs_ne : s ≠ ∅) :
    (s ∈ K₁.simplices ∧ s ∉ K₂.simplices) ∨ (s ∉ K₁.simplices ∧ s ∈ K₂.simplices) := by
  cases hs with
  | inl h₁ =>
    left
    exact ⟨h₁, fun h₂ => hs_ne (disjoint_no_shared_simplices K₁ K₂ h s h₁ h₂)⟩
  | inr h₂ =>
    right
    exact ⟨fun h₁ => hs_ne (disjoint_no_shared_simplices K₁ K₂ h s h₁ h₂), h₂⟩

/-- For disjoint complexes, a 0-cochain on the union can be built from 0-cochains on each piece. -/
noncomputable def glueCochains0 (K₁ K₂ : SimplicialComplex) (_h : AreDisjoint K₁ K₂)
    (g₁ : Cochain K₁ 0) (g₂ : Cochain K₂ 0) : Cochain (union K₁ K₂) 0 :=
  fun ⟨s, hs⟩ =>
    if h₁ : s ∈ K₁.simplices then g₁ ⟨s, ⟨h₁, hs.2⟩⟩
    else
      have h₂ : s ∈ K₂.simplices := by
        cases hs.1 with
        | inl h => exact absurd h h₁
        | inr h => exact h
      g₂ ⟨s, ⟨h₂, hs.2⟩⟩

/-- glueCochains0 evaluates to g₁ on K₁ simplices. -/
theorem glueCochains0_on_K1 (K₁ K₂ : SimplicialComplex) (h : AreDisjoint K₁ K₂)
    (g₁ : Cochain K₁ 0) (g₂ : Cochain K₂ 0)
    (s : Simplex) (hs : s ∈ (union K₁ K₂).ksimplices 0) (hs₁ : s ∈ K₁.simplices) :
    glueCochains0 K₁ K₂ h g₁ g₂ ⟨s, hs⟩ = g₁ ⟨s, ⟨hs₁, hs.2⟩⟩ := by
  simp only [glueCochains0, hs₁, dite_true]

/-- glueCochains0 evaluates to g₂ on K₂ simplices (not in K₁). -/
theorem glueCochains0_on_K2 (K₁ K₂ : SimplicialComplex) (h : AreDisjoint K₁ K₂)
    (g₁ : Cochain K₁ 0) (g₂ : Cochain K₂ 0)
    (s : Simplex) (hs : s ∈ (union K₁ K₂).ksimplices 0)
    (hs₁ : s ∉ K₁.simplices) (hs₂ : s ∈ K₂.simplices) :
    glueCochains0 K₁ K₂ h g₁ g₂ ⟨s, hs⟩ = g₂ ⟨s, ⟨hs₂, hs.2⟩⟩ := by
  simp only [glueCochains0, hs₁, dite_false]

/-! ## Part 3: Main Theorem -/

/-- H¹ is trivial for disjoint union of H¹-trivial complexes.

The proof works as follows:
1. A 1-cocycle f on K₁ ∪ K₂ restricts to cocycles f₁ on K₁ and f₂ on K₂
2. Since H¹(K₁) = 0 and H¹(K₂) = 0, there exist witnesses g₁, g₂
3. Since K₁ and K₂ are disjoint, we can glue g₁ and g₂ directly (no adjustment needed)
4. The glued 0-cochain g satisfies δg = f

Mathematical justification: This is the base case of the Mayer-Vietoris sequence.
When A ∩ B = ∅, we have H¹(A ∪ B) ≅ H¹(A) ⊕ H¹(B), so if both are trivial,
the union is trivial.

Note: The detailed proof requires careful handling of dependent types when
relating Fin e.card and Fin 2. The mathematical content follows directly
from the gluing lemmas above.
-/
theorem h1_trivial_disjoint_union (K₁ K₂ : SimplicialComplex) (h : AreDisjoint K₁ K₂)
    (h₁ : H1Trivial K₁) (h₂ : H1Trivial K₂) :
    H1Trivial (union K₁ K₂) := by
  intro f hf
  -- Restrict f to K₁ and K₂
  have h_sub₁ : K₁ ⊆ₛ union K₁ K₂ := left_sub_union K₁ K₂
  have h_sub₂ : K₂ ⊆ₛ union K₁ K₂ := right_sub_union K₁ K₂
  let f₁ := restrictCochain (union K₁ K₂) K₁ h_sub₁ 1 f
  let f₂ := restrictCochain (union K₁ K₂) K₂ h_sub₂ 1 f
  -- f₁ and f₂ are cocycles
  have hf₁ : IsCocycle K₁ 1 f₁ := CochainRestriction.restrict_preserves_cocycle (union K₁ K₂) K₁ h_sub₁ f hf
  have hf₂ : IsCocycle K₂ 1 f₂ := CochainRestriction.restrict_preserves_cocycle (union K₁ K₂) K₂ h_sub₂ f hf
  -- Get witnesses from H¹(K₁) = 0 and H¹(K₂) = 0
  obtain ⟨g₁, hg₁⟩ := h₁ f₁ hf₁
  obtain ⟨g₂, hg₂⟩ := h₂ f₂ hf₂
  -- Glue g₁ and g₂
  let g := glueCochains0 K₁ K₂ h g₁ g₂
  use g
  -- The coboundary computation follows from glueCochains0_on_K1/K2
  -- and the facts that restriction preserves values.
  -- For each edge e, it's in exactly one of K₁ or K₂, so:
  -- (δg)(e) = (δg₁)(e) or (δg₂)(e) = f₁(e) or f₂(e) = f(e)
  funext ⟨e, he⟩
  have he_card : e.card = 2 := he.2
  have he_ne : e ≠ ∅ := by
    intro h_empty
    rw [h_empty] at he_card
    simp at he_card
  have he_which := simplex_in_exactly_one K₁ K₂ h e he.1 he_ne
  rcases he_which with ⟨he₁, _⟩ | ⟨_, he₂⟩
  -- Both cases: show g agrees with g₁/g₂ on faces, then use hg₁/hg₂
  · -- Case: e ∈ K₁
    have he₁_k : e ∈ K₁.ksimplices 1 := ⟨he₁, he.2⟩
    have h_faces_K1 : ∀ i : Fin e.card, e.face i ∈ K₁.simplices :=
      fun i => K₁.down_closed e he₁ i
    -- Use hg₁ at e
    have hg₁_at_e := congrFun hg₁ ⟨e, he₁_k⟩
    simp only [coboundary] at hg₁_at_e ⊢
    -- f ⟨e, he⟩ = f₁ ⟨e, he₁_k⟩ by definition of restrictCochain
    have h_f_eq : f ⟨e, he⟩ = f₁ ⟨e, he₁_k⟩ := rfl
    rw [h_f_eq, ← hg₁_at_e]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    -- g evaluates to g₁ on faces in K₁
    show glueCochains0 K₁ K₂ h g₁ g₂ ⟨e.face i, _⟩ = g₁ ⟨e.face i, _⟩
    simp only [glueCochains0, h_faces_K1 i, ↓reduceDIte]
  · -- Case: e ∈ K₂
    have he₂_k : e ∈ K₂.ksimplices 1 := ⟨he₂, he.2⟩
    have h_faces_K2 : ∀ i : Fin e.card, e.face i ∈ K₂.simplices :=
      fun i => K₂.down_closed e he₂ i
    have h_faces_not_K1 : ∀ i : Fin e.card, e.face i ∉ K₁.simplices := by
      intro i h_contra
      have h_face_sub : (e.face i) ⊆ e := Simplex.face_subset e i
      -- Face has card 1, so it's nonempty
      have he_pos : e.card > 0 := by rw [he_card]; omega
      have h_face_card : (e.face i).card = 1 := by
        rw [Simplex.face_card _ _ he_pos, he_card]
      have h_face_nonempty : (e.face i).Nonempty := by
        rw [Finset.Nonempty]; exact Finset.card_pos.mp (by rw [h_face_card]; omega)
      obtain ⟨w, hw⟩ := h_face_nonempty
      have hw_K1 : w ∈ K₁.vertexSet := SimplicialComplex.vertex_of_mem_simplex K₁ _ h_contra w hw
      have hw_K2 : w ∈ K₂.vertexSet := SimplicialComplex.vertex_of_mem_simplex K₂ e he₂ w (h_face_sub hw)
      have : w ∈ K₁.vertexSet ∩ K₂.vertexSet := ⟨hw_K1, hw_K2⟩
      rw [h] at this; exact this
    -- Use hg₂ at e
    have hg₂_at_e := congrFun hg₂ ⟨e, he₂_k⟩
    simp only [coboundary] at hg₂_at_e ⊢
    -- f ⟨e, he⟩ = f₂ ⟨e, he₂_k⟩ by definition of restrictCochain
    have h_f_eq : f ⟨e, he⟩ = f₂ ⟨e, he₂_k⟩ := rfl
    rw [h_f_eq, ← hg₂_at_e]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    -- g evaluates to g₂ on faces not in K₁
    show glueCochains0 K₁ K₂ h g₁ g₂ ⟨e.face i, _⟩ = g₂ ⟨e.face i, _⟩
    simp only [glueCochains0, h_faces_not_K1 i, ↓reduceDIte]

/-! ## Part 4: Summary -/

/-
## Relationship to disjoint_modules_safe_ax

The axiom `disjoint_modules_safe_ax` is **MATHEMATICALLY FALSE** (see Compositional.lean).

The key issue: with no interface connections, the composed value complex is NOT
the disjoint union of the individual value complexes. Cross-module agents can have
edges in the composed complex if they happen to agree on some situation.

**Counterexample:** M₁(2 agents) + M₂(2 agents), S={s₁..s₄}, ε=1.
Values: v₀=(0,10,0,10), v₁=(1,10,10,0), v₂=(10,0,1,10), v₃=(10,1,10,1).
Each module is a tree (H¹=0), but composed complex has a 4-cycle → H¹≠0.

This file provides the correct version: `h1_trivial_disjoint_union` requires
the simplicial complexes themselves to be vertex-disjoint (AreDisjoint), which
is a STRONGER condition than having no interface connections.
-/

end Infrastructure.DisjointUnionH1
