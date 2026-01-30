/-
# Complete Proof: δ² = 0 (Coboundary Squared is Zero)

The fundamental theorem of simplicial cohomology: applying the coboundary
operator twice yields zero.

This file is self-contained and requires only standard Mathlib imports.

## Key Mathematical Ideas

1. The coboundary δf sums over faces with alternating signs: (δf)(σ) = Σᵢ (-1)ⁱ f(∂ᵢσ)

2. In δ(δf), each codimension-2 face appears exactly twice:
   - Once from removing vertex i then vertex j-1 (when i < j)
   - Once from removing vertex j then vertex i (when i < j)

3. These paired terms have opposite signs and cancel:
   (-1)^i · (-1)^(j-1) + (-1)^j · (-1)^i = 0

4. The proof uses a sign-reversing involution τ on index pairs:
   τ(i,j) = (j, i-1) when j < i
   τ(i,j) = (j+1, i) when j ≥ i

Author: Tenured Cohomology Foundations
Date: January 2026
Lean: 4.14.0+ with Mathlib
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.List.Basic
import Mathlib.Logic.Equiv.Fin
import Mathlib.Tactic

namespace CechCohomology

open Finset BigOperators

/-! ## Section 1: Foundational Definitions -/

/-- Coefficients are rationals for exact arithmetic -/
abbrev Coeff := ℚ

/-- Vertices are natural numbers -/
abbrev Vertex := ℕ

/-- A simplex is a finite set of vertices -/
abbrev Simplex := Finset Vertex

/-- Orientation sign: (-1)^n -/
def sign (n : ℕ) : Coeff := if n % 2 = 0 then 1 else -1

@[simp] lemma sign_zero : sign 0 = 1 := rfl
@[simp] lemma sign_one : sign 1 = -1 := rfl

lemma sign_add (m n : ℕ) : sign (m + n) = sign m * sign n := by
  simp only [sign]
  split_ifs with h1 h2 h3 <;> ring_nf <;> omega

lemma sign_succ (n : ℕ) : sign (n + 1) = -sign n := by
  calc sign (n + 1) = sign n * sign 1 := by rw [← sign_add]; ring_nf
    _ = sign n * (-1) := by simp
    _ = -sign n := by ring

/-! ## Section 2: Face Operation -/

/-- The i-th face: remove the i-th vertex (in sorted order) -/
def face (s : Simplex) (i : Fin s.card) : Simplex :=
  let sorted := s.sort (· ≤ ·)
  have h : i.val < sorted.length := by rw [Finset.length_sort]; exact i.isLt
  s.erase (sorted.get ⟨i.val, h⟩)

/-- Face decreases cardinality by 1 -/
lemma face_card (s : Simplex) (i : Fin s.card) (hpos : 0 < s.card) :
    (face s i).card = s.card - 1 := by
  simp only [face]
  have h_len : (s.sort (· ≤ ·)).length = s.card := Finset.length_sort (· ≤ ·)
  have h_bound : i.val < (s.sort (· ≤ ·)).length := by rw [h_len]; exact i.isLt
  have h_mem : (s.sort (· ≤ ·)).get ⟨i.val, h_bound⟩ ∈ s := by
    rw [← Finset.mem_sort (· ≤ ·)]
    exact List.get_mem _ _
  exact Finset.card_erase_of_mem h_mem

/-! ## Section 3: List Lemmas for Face-Face Identity -/

/-- Erasing position i then accessing j-1 (where i < j) gives original[j] -/
lemma list_eraseIdx_get_shift {α : Type*} (l : List α) (i j : ℕ)
    (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    (l.eraseIdx i).get ⟨j - 1, by rw [List.length_eraseIdx]; split_ifs <;> omega⟩ =
    l.get ⟨j, hj⟩ := by
  simp only [List.get_eq_getElem, List.getElem_eraseIdx]
  split_ifs with h <;> [omega; congr 1; omega]

/-- Erasing position j then accessing i (where i < j) gives original[i] -/
lemma list_eraseIdx_get_stable {α : Type*} (l : List α) (i j : ℕ)
    (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    (l.eraseIdx j).get ⟨i, by rw [List.length_eraseIdx]; split_ifs <;> omega⟩ =
    l.get ⟨i, hi⟩ := by
  simp only [List.get_eq_getElem, List.getElem_eraseIdx]
  split_ifs <;> rfl

/-- Sorting after erase equals erasing from sorted list -/
lemma sort_erase_eq_eraseIdx (s : Simplex) (i : Fin s.card) :
    let sorted := s.sort (· ≤ ·)
    let vi := sorted.get ⟨i.val, by rw [Finset.length_sort]; exact i.isLt⟩
    (s.erase vi).sort (· ≤ ·) = sorted.eraseIdx i.val := by
  set sorted := s.sort (· ≤ ·)
  have h_len : sorted.length = s.card := Finset.length_sort (· ≤ ·)
  have h_i : i.val < sorted.length := by rw [h_len]; exact i.isLt
  set vi := sorted.get ⟨i.val, h_i⟩

  -- Both lists: sorted, no duplicates, same elements
  have lhs_sorted : ((s.erase vi).sort (· ≤ ·)).Pairwise (· < ·) :=
    ((s.erase vi).sortedLT_sort).pairwise

  have rhs_sorted : (sorted.eraseIdx i.val).Pairwise (· < ·) := by
    have orig_sorted : sorted.Pairwise (· < ·) := s.sortedLT_sort.pairwise
    rw [List.pairwise_iff_getElem] at orig_sorted ⊢
    intro m n hm hn hmn
    rw [List.getElem_eraseIdx, List.getElem_eraseIdx]
    split_ifs with h1 h2 h2
    · apply orig_sorted <;> omega
    · apply orig_sorted <;> omega
    · omega
    · apply orig_sorted <;> omega

  have mem_iff : ∀ x, x ∈ (s.erase vi).sort (· ≤ ·) ↔ x ∈ sorted.eraseIdx i.val := by
    intro x
    rw [Finset.mem_sort, List.mem_eraseIdx_iff_getElem]
    simp only [Finset.mem_erase]
    constructor
    · intro ⟨hne, hx⟩
      exact ⟨by rwa [← Finset.mem_sort (· ≤ ·)], hne⟩
    · intro ⟨hx, hne⟩
      exact ⟨hne, by rwa [Finset.mem_sort (· ≤ ·)]⟩

  exact lhs_sorted.eq_of_mem_iff rhs_sorted mem_iff

/-! ## Section 4: The Face-Face Identity -/

/-- Key geometric identity: ∂_{j-1}(∂_i σ) = ∂_i(∂_j σ) when i < j -/
theorem face_face_identity (s : Simplex) (i j : Fin s.card) (hij : i < j) :
    face (face s i) ⟨j.val - 1, by rw [face_card]; omega; omega⟩ =
    face (face s j) ⟨i.val, by rw [face_card]; omega; omega⟩ := by
  simp only [face]
  set sorted := s.sort (· ≤ ·)
  have h_len : sorted.length = s.card := Finset.length_sort (· ≤ ·)
  have hi_bound : i.val < sorted.length := by rw [h_len]; exact i.isLt
  have hj_bound : j.val < sorted.length := by rw [h_len]; exact j.isLt

  set vi := sorted.get ⟨i.val, hi_bound⟩
  set vj := sorted.get ⟨j.val, hj_bound⟩

  -- vi ≠ vj (distinct positions in sorted list with no duplicates)
  have hne : vi ≠ vj := by
    intro heq
    have nodup : sorted.Nodup := Finset.sort_nodup _ _
    have : ⟨i.val, hi_bound⟩ ≠ (⟨j.val, hj_bound⟩ : Fin sorted.length) := by
      intro h; exact Nat.ne_of_lt hij (Fin.ext_iff.mp h)
    exact (List.Nodup.get_inj_iff nodup).not.mpr this heq

  -- After erasing vi, position j-1 contains vj
  have step1 : ((s.erase vi).sort (· ≤ ·)).get
      ⟨j.val - 1, by rw [Finset.length_sort, Finset.card_erase_of_mem]; omega
        rw [← Finset.mem_sort (· ≤ ·)]; exact List.get_mem sorted _⟩ = vj := by
    have h_eq := sort_erase_eq_eraseIdx s i
    simp only [List.get_eq_getElem]
    have h_bound' : j.val - 1 < (sorted.eraseIdx i.val).length := by
      rw [List.length_eraseIdx, h_len]; simp [i.isLt]; omega
    calc ((s.erase vi).sort (· ≤ ·))[j.val - 1]
        = (sorted.eraseIdx i.val)[j.val - 1]'h_bound' := by simp only [h_eq]
      _ = sorted[j.val]'hj_bound := list_eraseIdx_get_shift sorted i.val j.val hi_bound hj_bound hij
      _ = vj := rfl

  -- After erasing vj, position i contains vi
  have step2 : ((s.erase vj).sort (· ≤ ·)).get
      ⟨i.val, by rw [Finset.length_sort, Finset.card_erase_of_mem]; omega
        rw [← Finset.mem_sort (· ≤ ·)]; exact List.get_mem sorted _⟩ = vi := by
    have h_eq := sort_erase_eq_eraseIdx s j
    simp only [List.get_eq_getElem]
    have h_bound' : i.val < (sorted.eraseIdx j.val).length := by
      rw [List.length_eraseIdx, h_len]; simp [j.isLt]; omega
    calc ((s.erase vj).sort (· ≤ ·))[i.val]
        = (sorted.eraseIdx j.val)[i.val]'h_bound' := by simp only [h_eq]
      _ = sorted[i.val]'hi_bound := list_eraseIdx_get_stable sorted i.val j.val hi_bound hj_bound hij
      _ = vi := rfl

  -- Erase commutes
  have comm : (s.erase vi).erase vj = (s.erase vj).erase vi := by
    ext x; simp [Finset.mem_erase]; tauto

  calc (s.erase vi).erase (((s.erase vi).sort (· ≤ ·)).get ⟨j.val - 1, _⟩)
      = (s.erase vi).erase vj := by rw [step1]
    _ = (s.erase vj).erase vi := comm
    _ = (s.erase vj).erase (((s.erase vj).sort (· ≤ ·)).get ⟨i.val, _⟩) := by rw [step2]

/-! ## Section 5: Sign Cancellation -/

/-- Key algebraic lemma: paired signs cancel -/
theorem sign_cancel (a b : ℕ) (hab : a < b) :
    sign a * sign (b - 1) + sign b * sign a = 0 := by
  rw [← sign_add a (b - 1), ← sign_add b a]
  simp only [sign]
  have hb_pos : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le a) hab
  have h_eq : a + (b - 1) = a + b - 1 := by omega
  rw [h_eq, Nat.add_comm b a]
  split_ifs <;> ring_nf <;> omega

/-! ## Section 6: Simplicial Complex and Cochains -/

/-- A simplicial complex: closed under taking faces -/
structure SimplicialComplex where
  simplices : Set Simplex
  has_vertices : ∀ s ∈ simplices, ∀ v ∈ s, ({v} : Simplex) ∈ simplices
  down_closed : ∀ s ∈ simplices, ∀ i : Fin s.card, face s i ∈ simplices

/-- The set of k-simplices (k+1 vertices) -/
def SimplicialComplex.ksimplices (K : SimplicialComplex) (k : ℕ) : Set Simplex :=
  { s ∈ K.simplices | s.card = k + 1 }

/-- A k-cochain: function from k-simplices to coefficients -/
def Cochain (K : SimplicialComplex) (k : ℕ) :=
  { s : Simplex // s ∈ K.ksimplices k } → Coeff

instance {K : SimplicialComplex} {k : ℕ} : Zero (Cochain K k) := ⟨fun _ => 0⟩

@[simp] lemma Cochain.zero_apply {K : SimplicialComplex} {k : ℕ}
    (s : { s // s ∈ K.ksimplices k }) : (0 : Cochain K k) s = 0 := rfl

/-! ## Section 7: The Coboundary Operator -/

/-- Coboundary: δᵏ : Cᵏ(K) → Cᵏ⁺¹(K) -/
def coboundary (K : SimplicialComplex) (k : ℕ) (f : Cochain K k) : Cochain K (k + 1) :=
  fun ⟨s, hs⟩ =>
    ∑ i : Fin s.card, sign i.val * (
      have h_mem : face s i ∈ K.simplices :=
        K.down_closed s (by simp [SimplicialComplex.ksimplices] at hs; exact hs.1) i
      have h_card : (face s i).card = k + 1 := by
        simp [SimplicialComplex.ksimplices] at hs
        rw [face_card]; omega; omega
      f ⟨face s i, ⟨h_mem, h_card⟩⟩)

notation "δ" => coboundary

/-! ## Section 8: The Main Theorem -/

/-- The double sum in δ²f cancels via involution -/
theorem double_sum_cancels (K : SimplicialComplex) (k : ℕ) (f : Cochain K k)
    (s : Simplex) (hs : s ∈ K.ksimplices (k + 2)) :
    ∑ i : Fin s.card, ∑ j : Fin (face s i).card,
      sign i.val * sign j.val * (
        have h : face (face s i) j ∈ K.ksimplices k := by
          simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hs ⊢
          constructor
          · exact K.down_closed _ (K.down_closed s hs.1 i) j
          · rw [face_card, face_card]; omega; omega; omega
        f ⟨face (face s i) j, h⟩) = 0 := by

  simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hs
  have h_s_card : s.card = k + 3 := hs.2

  -- All faces have uniform size k + 2
  have h_face_size : ∀ i : Fin s.card, (face s i).card = k + 2 := by
    intro i; rw [face_card, h_s_card]; omega; omega

  -- Define term function with uniform indexing
  let T : Fin s.card → Fin (k + 2) → Coeff := fun i j =>
    sign i.val * sign j.val * (
      have hj : j.val < (face s i).card := by rw [h_face_size]; exact j.isLt
      have h : face (face s i) ⟨j.val, hj⟩ ∈ K.ksimplices k := by
        simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
        constructor
        · exact K.down_closed _ (K.down_closed s hs.1 i) _
        · rw [face_card, face_card, h_s_card]; omega; omega; omega
      f ⟨face (face s i) ⟨j.val, hj⟩, h⟩)

  -- Reindex to uniform Fin types
  have h_reindex : ∑ i : Fin s.card, ∑ j : Fin (face s i).card,
      sign i.val * sign j.val * (
        have h : face (face s i) j ∈ K.ksimplices k := by
          simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
          constructor
          · exact K.down_closed _ (K.down_closed s hs.1 i) j
          · rw [face_card, face_card, h_s_card]; omega; omega; omega
        f ⟨face (face s i) j, h⟩) =
      ∑ i : Fin s.card, ∑ j : Fin (k + 2), T i j := by
    congr 1; ext i
    refine Finset.sum_equiv (Fin.castOrderIso (h_face_size i)).toEquiv ?_ ?_
    · intro j; simp
    · intro j _; simp only [T, Fin.val_cast_of_lt]

  rw [h_reindex, ← Finset.sum_product']

  -- Apply involution
  apply Finset.sum_involution
    (g := fun p _ =>
      if h : p.2.val < p.1.val then
        (⟨p.2.val, by omega⟩, ⟨p.1.val - 1, by omega⟩)
      else
        (⟨p.2.val + 1, by omega⟩, ⟨p.1.val, by omega⟩))

  -- Proof 1: Paired terms sum to zero
  · intro ⟨i, j⟩ _
    simp only [T]
    split_ifs with h_case

    · -- Case j < i
      have h_cancel := sign_cancel j.val i.val h_case
      have hj_lt : j.val < s.card := by omega

      have h_eq : face (face s i) ⟨j.val, by rw [h_face_size]; exact j.isLt⟩ =
          face (face s ⟨j.val, hj_lt⟩) ⟨i.val - 1, by rw [h_face_size]; omega⟩ := by
        have := face_face_identity s ⟨j.val, hj_lt⟩ i h_case
        convert this.symm using 2

      have h_mem1 : face (face s i) ⟨j.val, _⟩ ∈ K.ksimplices k := by
        simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
        constructor
        · exact K.down_closed _ (K.down_closed s hs.1 _) _
        · rw [face_card, face_card, h_s_card]; omega; omega; omega

      have h_mem2 : face (face s ⟨j.val, hj_lt⟩) ⟨i.val - 1, _⟩ ∈ K.ksimplices k := by
        simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
        constructor
        · exact K.down_closed _ (K.down_closed s hs.1 _) _
        · rw [face_card, face_card, h_s_card]; omega; omega; omega

      have h_f_eq : f ⟨face (face s i) ⟨j.val, _⟩, h_mem1⟩ =
          f ⟨face (face s ⟨j.val, hj_lt⟩) ⟨i.val - 1, _⟩, h_mem2⟩ := by
        congr 1; exact Subtype.ext h_eq

      rw [h_f_eq]
      have h_sign : sign i.val * sign j.val + sign j.val * sign (i.val - 1) = 0 := by
        calc sign i.val * sign j.val + sign j.val * sign (i.val - 1)
          = sign j.val * sign i.val + sign j.val * sign (i.val - 1) := by ring
        _ = sign j.val * sign (i.val - 1) + sign i.val * sign j.val := by ring
        _ = 0 := h_cancel
      calc sign i.val * sign j.val * f ⟨_, h_mem2⟩ +
          sign j.val * sign (i.val - 1) * f ⟨_, h_mem2⟩
        = (sign i.val * sign j.val + sign j.val * sign (i.val - 1)) * f ⟨_, h_mem2⟩ := by ring
      _ = 0 := by rw [h_sign]; ring

    · -- Case j ≥ i
      push_neg at h_case
      have h_lt : i.val < j.val + 1 := Nat.lt_succ_of_le h_case
      have h_cancel := sign_cancel i.val (j.val + 1) h_lt
      have hj1_lt : j.val + 1 < s.card := by omega

      have h_eq : face (face s i) ⟨j.val, by rw [h_face_size]; exact j.isLt⟩ =
          face (face s ⟨j.val + 1, hj1_lt⟩) ⟨i.val, by rw [h_face_size]; omega⟩ := by
        have := face_face_identity s i ⟨j.val + 1, hj1_lt⟩ h_lt
        convert this using 2

      have h_mem1 : face (face s i) ⟨j.val, _⟩ ∈ K.ksimplices k := by
        simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
        constructor
        · exact K.down_closed _ (K.down_closed s hs.1 _) _
        · rw [face_card, face_card, h_s_card]; omega; omega; omega

      have h_mem2 : face (face s ⟨j.val + 1, hj1_lt⟩) ⟨i.val, _⟩ ∈ K.ksimplices k := by
        simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
        constructor
        · exact K.down_closed _ (K.down_closed s hs.1 _) _
        · rw [face_card, face_card, h_s_card]; omega; omega; omega

      have h_f_eq : f ⟨face (face s i) ⟨j.val, _⟩, h_mem1⟩ =
          f ⟨face (face s ⟨j.val + 1, hj1_lt⟩) ⟨i.val, _⟩, h_mem2⟩ := by
        congr 1; exact Subtype.ext h_eq

      rw [h_f_eq]
      have h_simp : j.val + 1 - 1 = j.val := by omega
      rw [h_simp] at h_cancel
      calc sign i.val * sign j.val * f ⟨_, h_mem2⟩ +
          sign (j.val + 1) * sign i.val * f ⟨_, h_mem2⟩
        = (sign i.val * sign j.val + sign (j.val + 1) * sign i.val) * f ⟨_, h_mem2⟩ := by ring
      _ = 0 := by rw [h_cancel]; ring

  -- Proof 2: Fixed points have zero coefficient (vacuously - no fixed points)
  · intro ⟨i, j⟩ _ _
    split_ifs with h
    · intro heq
      have h1 := congrArg (·.1.val) heq
      simp at h1; omega
    · intro heq
      have h1 := congrArg (·.1.val) heq
      simp at h1; omega

  -- Proof 3: Involution property τ(τ(p)) = p
  · intro ⟨i, j⟩ _
    by_cases h : j.val < i.val
    · have h' : ¬(i.val - 1 < j.val) := by omega
      simp only [dif_pos h, dif_neg h']
      ext <;> simp <;> omega
    · have h' : i.val < j.val + 1 := by omega
      simp only [dif_neg h, dif_pos h']
      ext <;> simp <;> omega

  -- Proof 4: Image in domain
  · intro _ _
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩

/-! ## Section 9: Main Theorem -/

/-- **Main Theorem**: δ² = 0
    The coboundary of a coboundary is always zero. -/
theorem delta_squared_zero (K : SimplicialComplex) (k : ℕ) (f : Cochain K k) :
    δ K (k + 1) (δ K k f) = 0 := by
  funext ⟨s, hs⟩
  simp only [Cochain.zero_apply, coboundary]

  -- Distribute sign into inner sum
  have expand : ∑ i : Fin s.card, sign i.val * ∑ j : Fin (face s i).card,
      sign j.val * (
        have h : face (face s i) j ∈ K.ksimplices k := by
          simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hs ⊢
          constructor
          · exact K.down_closed _ (K.down_closed s hs.1 i) j
          · rw [face_card, face_card]; omega; omega; omega
        f ⟨face (face s i) j, h⟩) =
    ∑ i : Fin s.card, ∑ j : Fin (face s i).card,
      sign i.val * sign j.val * (
        have h : face (face s i) j ∈ K.ksimplices k := by
          simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at hs ⊢
          constructor
          · exact K.down_closed _ (K.down_closed s hs.1 i) j
          · rw [face_card, face_card]; omega; omega; omega
        f ⟨face (face s i) j, h⟩) := by
    congr 1; ext i
    rw [Finset.mul_sum]
    congr 1; ext j; ring

  rw [expand]
  exact double_sum_cancels K k f s hs

/-! ## Corollaries -/

/-- δ¹ ∘ δ⁰ = 0 -/
theorem delta1_delta0 (K : SimplicialComplex) (f : Cochain K 0) :
    δ K 1 (δ K 0 f) = 0 := delta_squared_zero K 0 f

/-- δ² ∘ δ¹ = 0 -/
theorem delta2_delta1 (K : SimplicialComplex) (f : Cochain K 1) :
    δ K 2 (δ K 1 f) = 0 := delta_squared_zero K 1 f

/-- δ³ ∘ δ² = 0 -/
theorem delta3_delta2 (K : SimplicialComplex) (f : Cochain K 2) :
    δ K 3 (δ K 2 f) = 0 := delta_squared_zero K 2 f

end CechCohomology
