/-
# Cochain Restriction and Gluing Infrastructure

Lemmas for restricting cochains to subcomplexes and gluing them on unions.
This infrastructure enables proving the Mayer-Vietoris theorem for H¹.

## Key Lemmas Provided

1. `restrictCochain` - Restrict a cochain from K to subcomplex A
2. `restrict_coboundary_comm` - Restriction commutes with coboundary
3. `restrict_preserves_cocycle` - Restriction preserves cocycles
4. `union`, `inter` - Union and intersection of simplicial complexes
5. `coboundary_witness_diff_is_cocycle` - Difference of coboundary witnesses is a cocycle
6. `zero_cocycle_constant_on_connected` - 0-cocycles are constant on connected complexes
7. `coboundary_witnesses_differ_by_constant` - Coboundary witnesses differ by constant
8. `can_adjust_to_agree` - Key gluing lemma for Mayer-Vietoris

SORRIES: 0
AXIOMS: 0
-/

import Foundations.Cohomology
import H1Characterization.ForestCoboundary

namespace Infrastructure.CochainRestriction

open Foundations (Simplex SimplicialComplex Cochain IsCocycle IsCoboundary H1Trivial coboundary sign)
open H1Characterization (oneSkeleton OneConnected)

/-! ## Subcomplex Definition -/

/-- A is a subcomplex of K if A.simplices ⊆ K.simplices -/
def IsSubcomplex (A K : SimplicialComplex) : Prop :=
  A.simplices ⊆ K.simplices

notation:50 A " ⊆ₛ " K => IsSubcomplex A K

/-- Subcomplex k-simplices are k-simplices of the supercomplex -/
theorem subcomplex_ksimplices_sub (A K : SimplicialComplex) (h : A ⊆ₛ K) (k : ℕ) :
    A.ksimplices k ⊆ K.ksimplices k := by
  intro s ⟨hs_mem, hs_card⟩
  exact ⟨h hs_mem, hs_card⟩

/-! ## Cochain Restriction -/

/-- Restrict a cochain from K to a subcomplex A -/
def restrictCochain (K A : SimplicialComplex) (h : A ⊆ₛ K) (k : ℕ)
    (f : Cochain K k) : Cochain A k :=
  fun ⟨s, hs⟩ => f ⟨s, subcomplex_ksimplices_sub A K h k hs⟩

/-- Restriction is a linear map (respects addition) -/
theorem restrict_add (K A : SimplicialComplex) (h : A ⊆ₛ K) (k : ℕ)
    (f g : Cochain K k) :
    restrictCochain K A h k (f + g) = restrictCochain K A h k f + restrictCochain K A h k g := rfl

/-- Restriction is a linear map (respects scalar multiplication) -/
theorem restrict_smul (K A : SimplicialComplex) (h : A ⊆ₛ K) (k : ℕ)
    (c : ℚ) (f : Cochain K k) :
    restrictCochain K A h k (c • f) = c • restrictCochain K A h k f := rfl

/-- Restriction commutes with coboundary -/
theorem restrict_coboundary_comm (K A : SimplicialComplex) (h : A ⊆ₛ K) (k : ℕ)
    (f : Cochain K k) :
    restrictCochain K A h (k + 1) (coboundary K k f) = coboundary A k (restrictCochain K A h k f) := rfl

/-- Restriction preserves cocycles -/
theorem restrict_preserves_cocycle (K A : SimplicialComplex) (h : A ⊆ₛ K)
    (f : Cochain K 1) (hf : IsCocycle K 1 f) :
    IsCocycle A 1 (restrictCochain K A h 1 f) := by
  simp only [IsCocycle] at hf ⊢
  rw [← restrict_coboundary_comm K A h 1 f, hf]
  rfl

/-! ## Union and Intersection Operations -/

/-- Union of two simplicial complexes -/
def union (A B : SimplicialComplex) : SimplicialComplex where
  simplices := A.simplices ∪ B.simplices
  has_vertices := by
    intro s hs v hv
    cases hs with
    | inl hA => exact Or.inl (A.has_vertices s hA v hv)
    | inr hB => exact Or.inr (B.has_vertices s hB v hv)
  down_closed := by
    intro s hs i
    cases hs with
    | inl hA => exact Or.inl (A.down_closed s hA i)
    | inr hB => exact Or.inr (B.down_closed s hB i)

/-- Intersection of two simplicial complexes -/
def inter (A B : SimplicialComplex) : SimplicialComplex where
  simplices := A.simplices ∩ B.simplices
  has_vertices := by
    intro s ⟨hA, hB⟩ v hv
    exact ⟨A.has_vertices s hA v hv, B.has_vertices s hB v hv⟩
  down_closed := by
    intro s ⟨hA, hB⟩ i
    exact ⟨A.down_closed s hA i, B.down_closed s hB i⟩

theorem inter_sub_left (A B : SimplicialComplex) : inter A B ⊆ₛ A :=
  fun _ ⟨hA, _⟩ => hA

theorem inter_sub_right (A B : SimplicialComplex) : inter A B ⊆ₛ B :=
  fun _ ⟨_, hB⟩ => hB

/-- Restriction is transitive: restricting from K to A then to B equals restricting directly to B -/
theorem restrict_trans (K A B : SimplicialComplex) (hA : A ⊆ₛ K) (hB : B ⊆ₛ A) (k : ℕ)
    (f : Cochain K k) :
    restrictCochain A B hB k (restrictCochain K A hA k f) =
    restrictCochain K B (fun s hs => hA (hB hs)) k f := rfl

theorem union_sub_left (A B : SimplicialComplex) : A ⊆ₛ union A B :=
  fun _ h => Or.inl h

theorem union_sub_right (A B : SimplicialComplex) : B ⊆ₛ union A B :=
  fun _ h => Or.inr h

/-! ## Coboundary Linearity -/

/-- Difference of two coboundary witnesses is a 0-cocycle -/
theorem coboundary_witness_diff_is_cocycle (K : SimplicialComplex)
    (f : Cochain K 1) (g₁ g₂ : Cochain K 0)
    (h₁ : coboundary K 0 g₁ = f) (h₂ : coboundary K 0 g₂ = f) :
    IsCocycle K 0 (g₁ - g₂) := by
  simp only [IsCocycle]
  funext ⟨e, he⟩
  simp only [Cochain.zero_apply]
  -- Show δ(g₁ - g₂)(e) = δg₁(e) - δg₂(e) = f(e) - f(e) = 0
  have h_expand : (coboundary K 0 (g₁ - g₂)) ⟨e, he⟩ =
      (coboundary K 0 g₁) ⟨e, he⟩ - (coboundary K 0 g₂) ⟨e, he⟩ := by
    simp only [coboundary]
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext i
    exact mul_sub _ _ _
  rw [h_expand, h₁, h₂, sub_self]

/-! ## Connected Component Lemmas -/

/-- Helper: g values are equal along adjacent vertices for a 0-cocycle -/
theorem cocycle_constant_along_edge (K : SimplicialComplex)
    (g : Cochain K 0) (hg : IsCocycle K 0 g)
    (u v : K.vertexSet) (h_adj : (oneSkeleton K).Adj u v) :
    g ⟨{u.val}, ⟨u.property, Finset.card_singleton _⟩⟩ =
    g ⟨{v.val}, ⟨v.property, Finset.card_singleton _⟩⟩ := by
  have hedge : ({u.val, v.val} : Simplex) ∈ K.simplices := h_adj.2
  have hcard_edge : ({u.val, v.val} : Finset ℕ).card = 2 := Finset.card_pair h_adj.1
  have hedge_k : ({u.val, v.val} : Simplex) ∈ K.ksimplices 1 := ⟨hedge, hcard_edge⟩
  have hcoc : (coboundary K 0 g) ⟨{u.val, v.val}, hedge_k⟩ = 0 := by rw [hg]; rfl
  have hu_simp : {u.val} ∈ K.ksimplices 0 := ⟨K.has_vertices _ hedge u.val (by simp), Finset.card_singleton _⟩
  have hv_simp : {v.val} ∈ K.ksimplices 0 := ⟨K.has_vertices _ hedge v.val (by simp), Finset.card_singleton _⟩
  have h_edge_formula := H1Characterization.coboundary_edge_formula K g ⟨{u.val, v.val}, hedge_k⟩
  obtain ⟨a, b, ha, hb, h_edge_eq, hab_lt, h_formula⟩ := h_edge_formula
  rw [h_formula] at hcoc
  have h_ab_eq : g ⟨{b}, hb⟩ = g ⟨{a}, ha⟩ := sub_eq_zero.mp hcoc
  -- h_edge_eq says the edge simplex value equals {a, b}
  have h_edge_eq' : ({u.val, v.val} : Finset ℕ) = {a, b} := h_edge_eq
  have h_mem_a : a ∈ ({u.val, v.val} : Finset ℕ) := by rw [h_edge_eq']; simp
  have h_mem_b : b ∈ ({u.val, v.val} : Finset ℕ) := by rw [h_edge_eq']; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem_a h_mem_b
  rcases h_mem_a with ha_eq | ha_eq <;> rcases h_mem_b with hb_eq | hb_eq
  · -- a = u.val, b = u.val
    subst ha_eq hb_eq
    exact absurd rfl (ne_of_lt hab_lt)
  · -- a = u.val, b = v.val
    subst ha_eq hb_eq
    exact h_ab_eq.symm
  · -- a = v.val, b = u.val
    subst ha_eq hb_eq
    exact h_ab_eq
  · -- a = v.val, b = v.val
    subst ha_eq hb_eq
    exact absurd rfl (ne_of_lt hab_lt)

/-- Helper: g values are equal along a walk for a 0-cocycle -/
theorem cocycle_constant_along_walk (K : SimplicialComplex)
    (g : Cochain K 0) (hg : IsCocycle K 0 g)
    (u v : K.vertexSet) (w : (oneSkeleton K).Walk u v) :
    g ⟨{u.val}, ⟨u.property, Finset.card_singleton _⟩⟩ =
    g ⟨{v.val}, ⟨v.property, Finset.card_singleton _⟩⟩ := by
  induction w with
  | nil => rfl
  | @cons x y z h_adj _ ih =>
    have h1 := cocycle_constant_along_edge K g hg x y h_adj
    rw [h1, ih]

/-- On a connected complex, a 0-cocycle is constant -/
theorem zero_cocycle_constant_on_connected (K : SimplicialComplex)
    (hconn : (oneSkeleton K).Connected) [Nonempty K.vertexSet]
    (g : Cochain K 0) (hg : IsCocycle K 0 g) :
    ∃ c : ℚ, ∀ v : K.ksimplices 0, g v = c := by
  -- Pick an arbitrary vertex as reference
  obtain ⟨⟨v₀, hv₀⟩⟩ := ‹Nonempty K.vertexSet›
  have hv₀_simp : {v₀} ∈ K.ksimplices 0 := ⟨hv₀, Finset.card_singleton v₀⟩
  use g ⟨{v₀}, hv₀_simp⟩
  intro ⟨s, hs⟩
  -- s is a 0-simplex, so s = {v} for some vertex v
  have hcard : s.card = 1 := hs.2
  rw [Finset.card_eq_one] at hcard
  obtain ⟨v, hv_eq⟩ := hcard
  have hv_vert : v ∈ K.vertexSet := by
    rw [SimplicialComplex.mem_vertexSet_iff]
    have : {v} ∈ K.simplices := by rw [← hv_eq]; exact hs.1
    exact this
  -- Show g({v}) = g({v₀}) by connectivity
  have h_reach : (oneSkeleton K).Reachable ⟨v₀, hv₀⟩ ⟨v, hv_vert⟩ := hconn.preconnected _ _
  obtain ⟨w⟩ := h_reach
  have h_const := cocycle_constant_along_walk K g hg ⟨v₀, hv₀⟩ ⟨v, hv_vert⟩ w
  have hv_simp : {v} ∈ K.ksimplices 0 := ⟨K.has_vertices _ hs.1 v (by rw [hv_eq]; simp), Finset.card_singleton _⟩
  rw [show (⟨s, hs⟩ : K.ksimplices 0) = ⟨{v}, hv_simp⟩ from Subtype.ext hv_eq]
  exact h_const.symm

/-- On a connected complex, coboundary witnesses differ by a constant -/
theorem coboundary_witnesses_differ_by_constant (K : SimplicialComplex)
    (hconn : (oneSkeleton K).Connected) [Nonempty K.vertexSet]
    (f : Cochain K 1) (g₁ g₂ : Cochain K 0)
    (h₁ : coboundary K 0 g₁ = f) (h₂ : coboundary K 0 g₂ = f) :
    ∃ c : ℚ, ∀ v : K.ksimplices 0, g₁ v = g₂ v + c := by
  have h_diff_cocycle := coboundary_witness_diff_is_cocycle K f g₁ g₂ h₁ h₂
  obtain ⟨c, hc⟩ := zero_cocycle_constant_on_connected K hconn (g₁ - g₂) h_diff_cocycle
  use c
  intro v
  have h := hc v
  -- (g₁ - g₂) v = c means g₁ v - g₂ v = c, so g₁ v = g₂ v + c
  have h' : g₁ v - g₂ v = c := h
  -- sub_eq_iff_eq_add: a - b = c ↔ a = c + b
  rw [sub_eq_iff_eq_add, add_comm] at h'
  exact h'

/-! ## Gluing Infrastructure -/

/-- Vertices of a union -/
theorem union_vertexSet (A B : SimplicialComplex) :
    (union A B).vertexSet = A.vertexSet ∪ B.vertexSet := by
  ext v
  simp only [SimplicialComplex.mem_vertexSet_iff, union, Set.mem_union]

/-- HasConnectedIntersection: the intersection's 1-skeleton is connected -/
def HasConnectedIntersection (A B : SimplicialComplex) : Prop :=
  (inter A B).vertexSet.Nonempty → (oneSkeleton (inter A B)).Connected

/-! ## Key Gluing Lemma -/

/-- If A ∩ B is connected and gA, gB are coboundary witnesses for the same cocycle,
    we can adjust gB by a constant so they agree on A ∩ B -/
theorem can_adjust_to_agree (A B K : SimplicialComplex)
    (hA_sub : A ⊆ₛ K) (hB_sub : B ⊆ₛ K)
    (h_inter_conn : HasConnectedIntersection A B)
    (h_inter_nonempty : (inter A B).vertexSet.Nonempty)
    (f : Cochain K 1)
    (gA : Cochain A 0) (gB : Cochain B 0)
    (hgA : coboundary A 0 gA = restrictCochain K A hA_sub 1 f)
    (hgB : coboundary B 0 gB = restrictCochain K B hB_sub 1 f) :
    ∃ c : ℚ, ∀ s : (inter A B).ksimplices 0,
      gA ⟨s.val, ⟨(inter_sub_left A B) s.property.1, s.property.2⟩⟩ =
      gB ⟨s.val, ⟨(inter_sub_right A B) s.property.1, s.property.2⟩⟩ + c := by
  let hAB_sub_A := inter_sub_left A B
  let hAB_sub_B := inter_sub_right A B
  let gA_AB : Cochain (inter A B) 0 := restrictCochain A (inter A B) hAB_sub_A 0 gA
  let gB_AB : Cochain (inter A B) 0 := restrictCochain B (inter A B) hAB_sub_B 0 gB
  have h_fAB_eq1 : coboundary (inter A B) 0 gA_AB =
      restrictCochain K (inter A B) (fun s hs => hA_sub (hAB_sub_A hs)) 1 f := by
    rw [← restrict_coboundary_comm A (inter A B) hAB_sub_A 0 gA, hgA]
    rfl
  have h_fAB_eq2 : coboundary (inter A B) 0 gB_AB =
      restrictCochain K (inter A B) (fun s hs => hB_sub (hAB_sub_B hs)) 1 f := by
    rw [← restrict_coboundary_comm B (inter A B) hAB_sub_B 0 gB, hgB]
    rfl
  have h_same : restrictCochain K (inter A B) (fun s hs => hA_sub (hAB_sub_A hs)) 1 f =
      restrictCochain K (inter A B) (fun s hs => hB_sub (hAB_sub_B hs)) 1 f := rfl
  rw [h_same] at h_fAB_eq1
  have hconn := h_inter_conn h_inter_nonempty
  haveI : Nonempty (inter A B).vertexSet := ⟨⟨h_inter_nonempty.choose, h_inter_nonempty.choose_spec⟩⟩
  obtain ⟨c, hc⟩ := coboundary_witnesses_differ_by_constant (inter A B) hconn
    (restrictCochain K (inter A B) (fun s hs => hB_sub (hAB_sub_B hs)) 1 f) gA_AB gB_AB h_fAB_eq1 h_fAB_eq2
  exact ⟨c, fun s => hc s⟩

end Infrastructure.CochainRestriction
