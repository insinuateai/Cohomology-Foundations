/-
# H² Triviality for Small Complexes

Proof that complexes with < 4 vertices have trivial H².

## Main Results

1. `h2_trivial_three_vertices_ax` - |V| = 3 ⟹ H² = 0 (axiomatized)
2. `h2_trivial_lt_four_ax` - |V| < 4 ⟹ H² = 0 (axiomatized)

Key insight: With < 4 vertices, K.ksimplices 3 = ∅ (no 3-simplices),
so C³(K) = 0, and δ² : C² → C³ is the zero map.
Therefore every 2-cochain is a 2-cocycle (ker δ² = C²).
With at most 1 triangle, δ¹ : C¹ → C² is surjective onto the ≤1-dimensional C²,
so every 2-cocycle is a 2-coboundary (im δ¹ = C²), hence H² = 0.

## Axiom Status

AXIOMS REMAINING: 2 (main theorems - honest Level 2)
- h2_trivial_three_vertices_ax: Requires surjectivity of δ¹ for single-triangle case
- h2_trivial_lt_four_ax: Generalizes to all < 4 vertex cases

ELIMINATED: 2 (IsCocycle, IsCoboundary now proper definitions with δ operator)

Targets: Mathlib 4.27.0 / Lean 4.27.0
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace H2SmallComplex

open Finset BigOperators

abbrev Coeff := ℚ
abbrev Vertex := ℕ
abbrev Simplex := Finset Vertex

/-- Sign function: (-1)^n -/
def sign (n : ℕ) : Coeff := if n % 2 = 0 then 1 else -1

lemma sign_add (a b : ℕ) : sign (a + b) = sign a * sign b := by
  unfold sign
  split_ifs with h1 h2 h2 <;> ring_nf <;> omega

structure SimplicialComplex where
  simplices : Set Simplex
  has_vertices : ∀ s ∈ simplices, ∀ v ∈ s, ({v} : Simplex) ∈ simplices
  down_closed : ∀ s ∈ simplices, ∀ t, t ⊆ s → t ≠ ∅ → t ∈ simplices

namespace SimplicialComplex
def vertexSet (K : SimplicialComplex) : Set Vertex := { v | ({v} : Simplex) ∈ K.simplices }
def ksimplices (K : SimplicialComplex) (k : ℕ) : Set Simplex := { s ∈ K.simplices | s.card = k + 1 }
end SimplicialComplex

def Cochain (K : SimplicialComplex) (k : ℕ) := { s // s ∈ K.ksimplices k } → Coeff

instance (K : SimplicialComplex) (k : ℕ) : Zero (Cochain K k) where
  zero := fun _ => 0

instance (K : SimplicialComplex) (k : ℕ) : Add (Cochain K k) where
  add f g := fun s => f s + g s

/-! ## Face operation -/

/-- The i-th face of a simplex (remove i-th vertex in sorted order) -/
def Simplex.face (s : Simplex) (i : Fin s.card) : Simplex :=
  let sorted := s.sort (· ≤ ·)
  have h_len : sorted.length = s.card := Finset.length_sort (· ≤ ·)
  have h_get : i.val < sorted.length := by rw [h_len]; exact i.isLt
  s.erase (sorted.get ⟨i.val, h_get⟩)

lemma Simplex.face_card (s : Simplex) (i : Fin s.card) (h : s.card > 0) :
    (s.face i).card = s.card - 1 := by
  unfold face
  let sorted := s.sort (· ≤ ·)
  have h_len : sorted.length = s.card := Finset.length_sort (· ≤ ·)
  have h_get : i.val < sorted.length := by rw [h_len]; exact i.isLt
  have h_mem_sorted : sorted.get ⟨i.val, h_get⟩ ∈ sorted :=
    List.get_mem sorted ⟨i.val, h_get⟩
  have h_mem_s : sorted.get ⟨i.val, h_get⟩ ∈ s := by
    exact (Finset.mem_sort (· ≤ ·)).mp h_mem_sorted
  exact Finset.card_erase_of_mem h_mem_s

lemma Simplex.face_subset (s : Simplex) (i : Fin s.card) : s.face i ⊆ s := by
  unfold face
  exact Finset.erase_subset _ s

/-! ## Coboundary operator -/

/-- The coboundary operator δᵏ : Cᵏ(K) → Cᵏ⁺¹(K)

For a (k+1)-simplex σ = [v₀, ..., vₖ₊₁], we have:
(δf)(σ) = Σᵢ (-1)ⁱ f(∂ᵢσ)

where ∂ᵢσ is the i-th face (σ with vᵢ removed).
-/
def coboundary (K : SimplicialComplex) (k : ℕ) (f : Cochain K k) : Cochain K (k + 1) :=
  fun ⟨s, hs⟩ =>
    ∑ i : Fin s.card,
      sign i.val * (
        have h_face_subset : s.face i ⊆ s := Simplex.face_subset s i
        have h_face_nonempty : (s.face i).Nonempty := by
          simp [SimplicialComplex.ksimplices] at hs
          have h_s_card : s.card = k + 1 + 1 := hs.2
          rw [Finset.Nonempty]
          by_contra h_empty
          push_neg at h_empty
          have h_face_card : (s.face i).card = s.card - 1 := by
            apply Simplex.face_card; omega
          have : (s.face i).card = 0 := Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr h_empty)
          omega
        have h_face : s.face i ∈ K.simplices :=
          K.down_closed s hs.1 (s.face i) h_face_subset (Finset.nonempty_iff_ne_empty.mp h_face_nonempty)
        have h_face_card : (s.face i).card = k + 1 := by
          simp [SimplicialComplex.ksimplices] at hs
          have h_s_card : s.card = k + 1 + 1 := hs.2
          have := Simplex.face_card s i (by omega : s.card > 0)
          omega
        have h_face_in_k : s.face i ∈ K.ksimplices k := by
          simp [SimplicialComplex.ksimplices]
          exact ⟨h_face, h_face_card⟩
        f ⟨s.face i, h_face_in_k⟩
      )

notation "δ" => coboundary

/-- A k-cocycle: δf = 0

This is a proper definition using the coboundary operator.
Semantically: f is in the kernel of δᵏ.
-/
def IsCocycle (K : SimplicialComplex) (k : ℕ) (f : Cochain K k) : Prop :=
  δ K k f = 0

/-- A k-coboundary: ∃g, δg = f

This is a proper definition using the coboundary operator.
Semantically: f is in the image of δᵏ⁻¹.
-/
def IsCoboundary (K : SimplicialComplex) (k : ℕ) (f : Cochain K k) : Prop :=
  match k with
  | 0 => f = 0  -- No (-1)-cochains, so only 0 is a 0-coboundary
  | k' + 1 => ∃ g : Cochain K k', δ K k' g = f

/-- H² is trivial iff every 2-cocycle is a 2-coboundary -/
def H2Trivial (K : SimplicialComplex) : Prop :=
  ∀ f : Cochain K 2, IsCocycle K 2 f → IsCoboundary K 2 f

/-! ## Key Lemma: No 3-simplices with < 4 vertices -/

/-- A simplex in K has vertices from K.vertexSet -/
theorem simplex_vertices_in_vertexSet (K : SimplicialComplex) (s : Simplex) (hs : s ∈ K.simplices) :
    ∀ v ∈ s, v ∈ K.vertexSet := fun v hv => K.has_vertices s hs v hv

/-- Card of simplex ≤ card of vertex set -/
theorem simplex_card_le_vertexSet (K : SimplicialComplex) [Fintype K.vertexSet]
    (s : Simplex) (hs : s ∈ K.simplices) :
    s.card ≤ Fintype.card K.vertexSet := by
  have h_sub : ∀ v ∈ s, v ∈ K.vertexSet := simplex_vertices_in_vertexSet K s hs
  let f : s → K.vertexSet := fun ⟨v, hv⟩ => ⟨v, h_sub v hv⟩
  have hf_inj : Function.Injective f := fun ⟨v₁, _⟩ ⟨v₂, _⟩ h => by
    simp only [Subtype.mk.injEq] at h ⊢
    exact congrArg Subtype.val h
  calc s.card
    = Fintype.card s := (Fintype.card_coe s).symm
  _ ≤ Fintype.card K.vertexSet := Fintype.card_le_of_injective f hf_inj

/-- With < 4 vertices, no 3-simplices exist -/
theorem no_3simplices_lt_four (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_small : Fintype.card K.vertexSet < 4) : K.ksimplices 3 = ∅ := by
  ext s
  simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro ⟨hs, hcard⟩
  have h := simplex_card_le_vertexSet K s hs
  omega

/-- With = 3 vertices, no 3-simplices exist -/
theorem no_3simplices_three (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_three : Fintype.card K.vertexSet = 3) : K.ksimplices 3 = ∅ :=
  no_3simplices_lt_four K (by omega)

/-! ## Main Theorems -/

/-- H² is trivial when there are no 2-simplices (triangles) -/
theorem h2_trivial_of_no_2simplices (K : SimplicialComplex)
    (h : K.ksimplices 2 = ∅) : H2Trivial K := by
  intro f _hf
  use 0
  funext ⟨s, hs⟩
  rw [Set.eq_empty_iff_forall_notMem] at h
  exact absurd hs (h s)

/-- With 3 vertices, any two 2-simplices in K are equal (there's at most 1 triangle) -/
theorem unique_triangle (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_three : Fintype.card K.vertexSet = 3)
    (s T : Simplex) (hs : s ∈ K.ksimplices 2) (hT : T ∈ K.ksimplices 2) :
    s = T := by
  simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hs hT
  have hs_card : s.card = 3 := hs.2
  have hT_card : T.card = 3 := hT.2
  have hs_sub : ∀ v ∈ s, v ∈ K.vertexSet := simplex_vertices_in_vertexSet K s hs.1
  have hT_sub : ∀ v ∈ T, v ∈ K.vertexSet := simplex_vertices_in_vertexSet K T hT.1
  -- Both s and T have 3 elements from a 3-element vertex set
  -- Therefore they must be equal
  ext v
  constructor
  · intro hv
    have hv_vs : v ∈ K.vertexSet := hs_sub v hv
    by_contra hv_not_T
    have h_card : (T ∪ {v}).card ≤ Fintype.card K.vertexSet := by
      have h_sub : ∀ w ∈ T ∪ {v}, w ∈ K.vertexSet := by
        intro w hw
        simp only [Finset.mem_union, Finset.mem_singleton] at hw
        cases hw with
        | inl h => exact hT_sub w h
        | inr h => subst h; exact hv_vs
      let f' : ↑(T ∪ {v}) → K.vertexSet := fun ⟨w, hw⟩ => ⟨w, h_sub w hw⟩
      have hf_inj : Function.Injective f' := fun ⟨w₁, _⟩ ⟨w₂, _⟩ h => by
        simp only [Subtype.mk.injEq] at h ⊢
        exact congrArg Subtype.val h
      calc (T ∪ {v}).card
        = Fintype.card ↑(T ∪ {v}) := (Fintype.card_coe _).symm
      _ ≤ Fintype.card K.vertexSet := Fintype.card_le_of_injective f' hf_inj
    have h_card_union : (T ∪ {v}).card = T.card + 1 := by
      rw [Finset.card_union_of_disjoint]
      · simp
      · simp [hv_not_T]
    omega
  · intro hv
    have hv_vs : v ∈ K.vertexSet := hT_sub v hv
    by_contra hv_not_s
    have h_card : (s ∪ {v}).card ≤ Fintype.card K.vertexSet := by
      have h_sub : ∀ w ∈ s ∪ {v}, w ∈ K.vertexSet := by
        intro w hw
        simp only [Finset.mem_union, Finset.mem_singleton] at hw
        cases hw with
        | inl h => exact hs_sub w h
        | inr h => subst h; exact hv_vs
      let f' : ↑(s ∪ {v}) → K.vertexSet := fun ⟨w, hw⟩ => ⟨w, h_sub w hw⟩
      have hf_inj : Function.Injective f' := fun ⟨w₁, _⟩ ⟨w₂, _⟩ h => by
        simp only [Subtype.mk.injEq] at h ⊢
        exact congrArg Subtype.val h
      calc (s ∪ {v}).card
        = Fintype.card ↑(s ∪ {v}) := (Fintype.card_coe _).symm
      _ ≤ Fintype.card K.vertexSet := Fintype.card_le_of_injective f' hf_inj
    have h_card_union : (s ∪ {v}).card = s.card + 1 := by
      rw [Finset.card_union_of_disjoint]
      · simp
      · simp [hv_not_s]
    omega

/-- 3-vertex complex has H² = 0

Proof: With 3 vertices, there's at most 1 triangle. For any 2-cochain f,
we construct a 1-cochain g such that δg = f.

The construction: For the triangle T with sorted vertices [v₀, v₁, v₂]:
- face 2 = {v₀, v₁} has sign +1 in the coboundary formula
- Set g(face 2) = f(T), g(other edges) = 0
- Then (δg)(T) = sign(0)*0 + sign(1)*0 + sign(2)*f(T) = f(T) ✓
-/
theorem h2_trivial_three_vertices (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_three : Fintype.card K.vertexSet = 3) : H2Trivial K := by
  intro f _hf
  simp only [IsCoboundary]
  -- If no triangles, use the trivial proof
  by_cases h_no_tri : K.ksimplices 2 = ∅
  · use 0
    funext ⟨s, hs⟩
    rw [Set.eq_empty_iff_forall_notMem] at h_no_tri
    exact absurd hs (h_no_tri s)
  · -- There exists at least one triangle T
    have h_nonempty : (K.ksimplices 2).Nonempty := Set.nonempty_iff_ne_empty.mpr h_no_tri
    obtain ⟨T, hT⟩ := h_nonempty
    classical
    -- Define face 2 of T
    have hT_card : T.card = 3 := by
      simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hT; exact hT.2
    let face2 : Simplex := T.face ⟨2, by omega⟩
    have hface2_card : face2.card = 2 := by
      simp only [face2]
      rw [Simplex.face_card]; omega; omega
    have hface2_subset : face2 ⊆ T := Simplex.face_subset T ⟨2, by omega⟩
    have hface2_ne : face2 ≠ ∅ := by
      intro h; have : face2.card = 0 := Finset.card_eq_zero.mpr h; omega
    have hface2_mem : face2 ∈ K.simplices := by
      simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hT
      exact K.down_closed T hT.1 face2 hface2_subset hface2_ne
    have hface2_in_1 : face2 ∈ K.ksimplices 1 := by
      simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
      exact ⟨hface2_mem, hface2_card⟩

    -- Construct g: assigns f(⟨T, hT⟩) to face2, 0 to other edges
    use fun ⟨e, he⟩ => if e = face2 then f ⟨T, hT⟩ else 0

    -- Prove δg = f
    funext ⟨s, hs⟩
    simp only [coboundary]

    -- s is the unique triangle (s = T)
    have hs_eq_T : s = T := unique_triangle K h_three s T hs hT

    -- Helper lemma: erasing different sorted elements gives different results
    have erase_inj (σ : Simplex) (i j : ℕ) (hi : i < σ.card) (hj : j < σ.card) (hne : i ≠ j) :
        σ.erase ((σ.sort (· ≤ ·)).get ⟨i, by rw [Finset.length_sort]; exact hi⟩) ≠
        σ.erase ((σ.sort (· ≤ ·)).get ⟨j, by rw [Finset.length_sort]; exact hj⟩) := by
      intro h_eq
      have h_nodup : (σ.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
      have hσ_len : (σ.sort (· ≤ ·)).length = σ.card := Finset.length_sort (· ≤ ·)
      have hi_lt : i < (σ.sort (· ≤ ·)).length := by rw [hσ_len]; exact hi
      have hj_lt : j < (σ.sort (· ≤ ·)).length := by rw [hσ_len]; exact hj
      let vi := (σ.sort (· ≤ ·)).get ⟨i, hi_lt⟩
      let vj := (σ.sort (· ≤ ·)).get ⟨j, hj_lt⟩
      have hvi_mem : vi ∈ σ := (Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ _)
      have hvj_mem : vj ∈ σ := (Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ _)
      have hvi_ne_vj : vi ≠ vj := by
        intro heq
        have h_inj := @List.Nodup.get_inj_iff _ (σ.sort (· ≤ ·)) h_nodup ⟨i, hi_lt⟩ ⟨j, hj_lt⟩
        have h_idx_eq : (⟨i, hi_lt⟩ : Fin (σ.sort (· ≤ ·)).length) = ⟨j, hj_lt⟩ := h_inj.mp heq
        exact hne (Fin.ext_iff.mp h_idx_eq)
      have hvi_in : vi ∈ σ.erase vj := Finset.mem_erase.mpr ⟨hvi_ne_vj, hvi_mem⟩
      have hvi_not : vi ∉ σ.erase vi := by simp [Finset.mem_erase]
      rw [h_eq] at hvi_not; exact hvi_not hvi_in

    -- Key fact: s.face ⟨i, _⟩ for different i give different results
    -- Using s = T, we work with T throughout
    -- face2 = T.face ⟨2, _⟩ = T.erase v₂ where v₂ is 3rd sorted vertex

    -- The sum simplifies because s = T
    -- For i = 0, 1: s.face ⟨i, _⟩ ≠ face2 so contribution is 0
    -- For i = 2: s.face ⟨2, _⟩ = face2 so contribution is sign(2) * f(T) = f(T)

    -- Use cases on hs_eq_T to eliminate s entirely
    cases hs_eq_T

    -- Now s has been replaced by T throughout
    have h0_ne : T.face ⟨0, by omega⟩ ≠ face2 := by
      unfold Simplex.face face2
      exact erase_inj T 0 2 (by omega) (by omega) (by omega)
    have h1_ne : T.face ⟨1, by omega⟩ ≠ face2 := by
      unfold Simplex.face face2
      exact erase_inj T 1 2 (by omega) (by omega) (by omega)
    have h2_eq : T.face ⟨2, by omega⟩ = face2 := rfl

    -- Now compute the sum
    -- LHS is ∑ i : Fin T.card, sign i.val * (if T.face i = face2 then f ⟨T, hT⟩ else 0)
    -- RHS is f ⟨T, hs⟩

    -- Key insight: only i = 2 contributes (others give 0)
    -- And sign(2) = 1, so the sum equals f ⟨T, hT⟩

    -- First, the terms for i = 0, 1 vanish
    have term0 : sign (0 : ℕ) * (if T.face ⟨0, by omega⟩ = face2 then f ⟨T, hT⟩ else 0) = 0 := by
      simp only [h0_ne, ↓reduceIte, mul_zero]
    have term1 : sign (1 : ℕ) * (if T.face ⟨1, by omega⟩ = face2 then f ⟨T, hT⟩ else 0) = 0 := by
      simp only [h1_ne, ↓reduceIte, mul_zero]
    have term2 : sign (2 : ℕ) * (if T.face ⟨2, by omega⟩ = face2 then f ⟨T, hT⟩ else 0) = f ⟨T, hT⟩ := by
      simp only [h2_eq, ↓reduceIte, sign, one_mul]

    -- The sum equals f ⟨T, hT⟩
    -- We need to show: sum over Fin T.card = f ⟨T, hs⟩
    -- Since T.card = 3, we have exactly 3 terms
    have h3 : T.card = 3 := hT_card

    -- Simplify: the sum equals term0 + term1 + term2 = 0 + 0 + f ⟨T, hT⟩ = f ⟨T, hT⟩
    -- And f ⟨T, hs⟩ = f ⟨T, hT⟩ since both are f applied to the same underlying element T
    have hf_eq : f ⟨T, hs⟩ = f ⟨T, hT⟩ := rfl

    -- Direct computation via sum_fin_eq_sum_range and range reduction
    simp only [Finset.sum_fin_eq_sum_range]
    rw [show Finset.range T.card = Finset.range 3 by rw [h3]]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    -- Simplify the dite conditions (0 < 3, 1 < 3, 2 < 3 are all true)
    simp only [show (0 : ℕ) < T.card by omega, show (1 : ℕ) < T.card by omega,
               show (2 : ℕ) < T.card by omega, dif_pos]
    simp only [h0_ne, h1_ne, h2_eq, ↓reduceIte, sign, mul_zero, one_mul, add_zero, zero_add, hf_eq]

/-- < 4 vertices implies H² = 0 -/
theorem h2_trivial_lt_four (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_small : Fintype.card K.vertexSet < 4) : H2Trivial K := by
  -- Case split: |V| < 3 or |V| = 3
  rcases Nat.lt_succ_iff_lt_or_eq.mp h_small with h_lt3 | h_eq3
  · -- |V| < 3: no triangles possible
    apply h2_trivial_of_no_2simplices
    rw [Set.eq_empty_iff_forall_notMem]
    intro s hs
    simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hs
    have h := simplex_card_le_vertexSet K s hs.1
    omega
  · -- |V| = 3: use h2_trivial_three_vertices
    exact h2_trivial_three_vertices K h_eq3

/-- ≤ 3 vertices implies H² = 0 -/
theorem h2_trivial_le_three (K : SimplicialComplex) [Fintype K.vertexSet]
    (h_small : Fintype.card K.vertexSet ≤ 3) : H2Trivial K :=
  h2_trivial_lt_four K (Nat.lt_of_le_of_lt h_small (by norm_num))

-- Legacy aliases for compatibility
alias h2_trivial_three_vertices_ax := h2_trivial_three_vertices
alias h2_trivial_lt_four_ax := h2_trivial_lt_four

#check h2_trivial_three_vertices
#check h2_trivial_lt_four
#check h2_trivial_le_three

end H2SmallComplex
