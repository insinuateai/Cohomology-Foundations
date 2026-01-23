/-
# Coboundary Operator

The key operator δ : Cᵏ → Cᵏ⁺¹ and the crucial theorem δ² = 0.
-/

import Foundations.Cochain
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Foundations

open Finset BigOperators

/-- The coboundary operator δᵏ : Cᵏ(K) → Cᵏ⁺¹(K)

For a (k+1)-simplex σ = [v₀, ..., vₖ₊₁], we have:
(δf)(σ) = Σᵢ (-1)ⁱ f(∂ᵢσ)

where ∂ᵢσ is the i-th face (σ with vᵢ removed).
-/
def coboundary (K : SimplicialComplex) (k : ℕ) (f : Cochain K k) : Cochain K (k + 1) :=
  fun ⟨s, hs⟩ =>
    -- Sum over all faces with alternating signs
    ∑ i : Fin s.card,
      sign i.val * (
        -- The i-th face of s
        -- First, show it's in K.simplices
        have h_face : s.face i ∈ K.simplices := K.down_closed s (by
          simp [SimplicialComplex.ksimplices] at hs
          exact hs.1) i
        -- Second, show it has the right cardinality
        have h_face_card : (s.face i).card = k + 1 := by
          simp [SimplicialComplex.ksimplices] at hs
          -- s is a (k+1)-simplex, so s.card = k + 2
          have h_s_card : s.card = k + 1 + 1 := hs.2
          -- face removes one vertex, so (s.face i).card = s.card - 1
          have h_face_dec : (s.face i).card = s.card - 1 := by
            apply Simplex.face_card
            rw [h_s_card]
            omega
          -- Therefore (s.face i).card = (k + 2) - 1 = k + 1
          rw [h_face_dec, h_s_card]
          omega
        -- Combine to show s.face i ∈ K.ksimplices k
        have h_face_in_k : s.face i ∈ K.ksimplices k := by
          simp [SimplicialComplex.ksimplices]
          exact ⟨h_face, h_face_card⟩
        -- Apply f to this face
        f ⟨s.face i, h_face_in_k⟩
      )

notation "δ" => coboundary

/-- Helper: When we erase the i-th element of a list, the element previously at position j > i
moves to position j-1 -/
lemma list_get_eraseIdx_of_lt {α : Type*} (l : List α) (i j : ℕ) (h_i : i < l.length)
    (h_j : j < l.length) (h_ij : i < j) :
    (l.eraseIdx i).get ⟨j - 1, by
      rw [List.length_eraseIdx]
      split <;> omega
    ⟩ = l.get ⟨j, h_j⟩ := by
  simp only [List.get_eq_getElem]
  rw [List.getElem_eraseIdx]
  split_ifs with h
  · omega  -- contradiction: j - 1 < i but i < j
  · congr 1
    omega

/-- Helper: When we erase an element at position j > i from a list, the element at position i
stays at position i -/
lemma list_get_eraseIdx_of_gt {α : Type*} (l : List α) (i j : ℕ) (h_i : i < l.length)
    (h_j : j < l.length) (h_ij : i < j) :
    (l.eraseIdx j).get ⟨i, by
      rw [List.length_eraseIdx]
      split <;> omega
    ⟩ = l.get ⟨i, h_i⟩ := by
  simp only [List.get_eq_getElem]
  rw [List.getElem_eraseIdx]
  split_ifs <;> rfl

/-- Helper: Sorting and erasing commute for finsets.
    When we erase the i-th element from a sorted list, we get the same result as
    erasing that element from the finset and then sorting.

    Mathematical validity: Both operations yield the same sorted subsequence.
    When we sort a finset and then erase position i, we get the same list as
    erasing the i-th element from the finset and then sorting.

    Proof sketch:
    - Both lists have the same length: |s| - 1
    - Both lists are sorted (ascending order)
    - Both lists contain exactly the same elements: s \ {vi}
    - Two sorted lists with the same elements are equal -/
lemma finset_sort_erase_eq_eraseIdx (s : Simplex) (i : Fin s.card) :
    let sorted := s.sort (· ≤ ·)
    let vi := sorted.get ⟨i.val, by rw [Finset.length_sort]; exact i.isLt⟩
    (s.erase vi).sort (· ≤ ·) = sorted.eraseIdx i.val := by
  set sorted := s.sort (· ≤ ·) with h_sorted
  have h_i_bound : i.val < sorted.length := by rw [Finset.length_sort]; exact i.isLt
  set vi := sorted.get ⟨i.val, h_i_bound⟩ with h_vi
  have h_vi_mem : vi ∈ s := by
    rw [← Finset.mem_sort (· ≤ ·)]
    exact List.get_mem sorted ⟨i.val, h_i_bound⟩

  -- Strategy: Both lists are sorted, both contain the same elements.
  -- By uniqueness of sorted lists (Pairwise.eq_of_mem_iff), they're equal.

  -- 1. LHS is sorted (from Finset.sortedLT_sort for LinearOrder)
  have h_lhs_sorted : ((s.erase vi).sort (· ≤ ·)).Pairwise (· < ·) :=
    ((s.erase vi).sortedLT_sort).pairwise

  -- 2. RHS is sorted (eraseIdx preserves sortedness)
  have h_rhs_sorted : (sorted.eraseIdx i.val).Pairwise (· < ·) := by
    have h_sorted_pairwise : sorted.Pairwise (· < ·) := s.sortedLT_sort.pairwise
    -- eraseIdx preserves pairwise: if all pairs in original satisfy R,
    -- then all pairs in eraseIdx also satisfy R
    rw [List.pairwise_iff_getElem] at h_sorted_pairwise ⊢
    intro m n hm hn hmn
    rw [List.getElem_eraseIdx, List.getElem_eraseIdx]
    -- Map indices back to original list
    have h_len : sorted.length = s.card := Finset.length_sort (· ≤ ·)
    have h_eraseIdx_len : (sorted.eraseIdx i.val).length = sorted.length - 1 := by
      rw [List.length_eraseIdx]; simp [h_i_bound]
    split_ifs with h1 h2 h2
    · -- m < i, n < i: both indices unchanged
      apply h_sorted_pairwise <;> omega
    · -- m < i, n ≥ i: m unchanged, n becomes n+1
      apply h_sorted_pairwise <;> omega
    · -- m ≥ i, n < i: contradiction since m < n and m ≥ i > n
      omega
    · -- m ≥ i, n ≥ i: both shifted by 1
      apply h_sorted_pairwise <;> omega

  -- 3. Both lists have no duplicates
  have h_lhs_nodup : ((s.erase vi).sort (· ≤ ·)).Nodup := (s.erase vi).sort_nodup _
  have h_rhs_nodup : (sorted.eraseIdx i.val).Nodup := by
    have h_sorted_nodup : sorted.Nodup := s.sort_nodup _
    exact h_sorted_nodup.eraseIdx i.val

  -- 4. Both lists have same membership
  have h_mem_iff : ∀ x, x ∈ (s.erase vi).sort (· ≤ ·) ↔ x ∈ sorted.eraseIdx i.val := by
    intro x
    rw [Finset.mem_sort]
    constructor
    · -- x ∈ s.erase vi → x ∈ sorted.eraseIdx i
      intro hx
      simp only [Finset.mem_erase] at hx
      obtain ⟨hne, hx_in_s⟩ := hx
      -- x is in sorted and x ≠ vi
      have hx_in_sorted : x ∈ sorted := (Finset.mem_sort (· ≤ ·)).mpr hx_in_s
      -- Find the index of x in sorted
      have ⟨k, hk_bound, hk_eq⟩ := List.mem_iff_getElem.mp hx_in_sorted
      -- k ≠ i because x ≠ vi = sorted[i]
      have hk_ne_i : k ≠ i.val := by
        intro heq
        subst heq
        simp only [List.get_eq_getElem] at h_vi
        exact hne hk_eq.symm
      -- x = sorted[k] and k ≠ i, so x ∈ sorted.eraseIdx i
      rw [List.mem_iff_getElem]
      by_cases hki : k < i.val
      · use k
        refine ⟨?_, ?_⟩
        · have : (sorted.eraseIdx i.val).length = sorted.length - 1 := by
            rw [List.length_eraseIdx]; simp [h_i_bound]
          omega
        · rw [List.getElem_eraseIdx]
          simp only [hki, ↓reduceIte]
          exact hk_eq
      · use k - 1
        push_neg at hki
        have hk_gt_i : k > i.val := Nat.lt_of_le_of_ne hki (Ne.symm hk_ne_i)
        have h_sorted_len : sorted.length = s.card := Finset.length_sort (· ≤ ·)
        refine ⟨?_, ?_⟩
        · have h_erase_len : (sorted.eraseIdx i.val).length = sorted.length - 1 := by
            rw [List.length_eraseIdx]; simp [h_i_bound]
          -- k - 1 < sorted.length - 1
          -- We have: k < sorted.length and k > i.val
          omega
        · rw [List.getElem_eraseIdx]
          have : ¬(k - 1 < i.val) := by omega
          simp only [this, ↓reduceIte]
          -- Need to show sorted[k-1+1] = x, i.e., sorted[k] = x
          have : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_of_lt hk_gt_i)
          simp only [this]
          exact hk_eq
    · -- x ∈ sorted.eraseIdx i → x ∈ s.erase vi
      intro hx
      rw [List.mem_iff_getElem] at hx
      obtain ⟨k, hk_bound, hk_eq⟩ := hx
      have h_sorted_len : sorted.length = s.card := Finset.length_sort (· ≤ ·)
      have h_erase_len : (sorted.eraseIdx i.val).length = sorted.length - 1 := by
        rw [List.length_eraseIdx]; simp [h_i_bound]
      rw [List.getElem_eraseIdx] at hk_eq
      simp only [Finset.mem_erase]
      split_ifs at hk_eq with hki
      · -- k < i: x = sorted[k]
        constructor
        · intro heq
          subst heq
          simp only [List.get_eq_getElem] at h_vi
          have h_nodup := s.sort_nodup (· ≤ ·)
          have := h_nodup.getElem_inj_iff.mp hk_eq.symm
          omega
        · rw [← Finset.mem_sort (· ≤ ·), ← hk_eq]
          have hk_lt_sorted : k < sorted.length := by omega
          exact List.getElem_mem hk_lt_sorted
      · -- k ≥ i: x = sorted[k+1]
        constructor
        · intro heq
          subst heq
          simp only [List.get_eq_getElem] at h_vi
          have h_nodup := s.sort_nodup (· ≤ ·)
          have := h_nodup.getElem_inj_iff.mp hk_eq.symm
          omega
        · rw [← Finset.mem_sort (· ≤ ·), ← hk_eq]
          have hk1_lt_sorted : k + 1 < sorted.length := by omega
          exact List.getElem_mem hk1_lt_sorted

  -- 5. Apply uniqueness of sorted lists
  exact h_lhs_sorted.eq_of_mem_iff h_rhs_sorted h_mem_iff

/-- Key lemma: Taking the j-th face of the i-th face (i < j) is the same as
taking the (i)-th face of the (j-1)-th face, but with vertices relabeled.

∂ⱼ(∂ᵢσ) = ∂ᵢ(∂ⱼ₋₁σ) when i < j

This is the core identity that makes δ² = 0 work.
-/
lemma face_face_identity (s : Simplex) (i j : Fin s.card) (hij : i < j) :
    (s.face i).face ⟨j.val - 1, by
      rw [Simplex.face_card]
      · omega
      · omega
    ⟩ = (s.face j).face ⟨i.val, by
      rw [Simplex.face_card]
      · omega
      · omega
    ⟩ := by
  -- Both sides erase two vertices: those at positions i and j in the sorted order
  -- We'll show this by proving both equal s.erase(vi).erase(vj)
  simp only [Simplex.face]
  -- The sorted list
  let sorted := s.sort (· ≤ ·)
  have h_len : sorted.length = s.card := Finset.length_sort (· ≤ ·)
  -- The two vertices to remove
  let vi := sorted.get ⟨i.val, by rw [h_len]; exact i.isLt⟩
  let vj := sorted.get ⟨j.val, by rw [h_len]; exact j.isLt⟩

  -- They're distinct (different indices in a list give different elements when no duplicates)
  have h_ne : vi ≠ vj := by
    intro h_eq
    -- If vi = vj, then sorted[i] = sorted[j], but sorted is a finset's sorted list (no dups)
    -- and i < j, so this is impossible
    have h_nodup : sorted.Nodup := Finset.sort_nodup _ _
    have h_i_ne_j : i.val ≠ j.val := by
      intro h_eq2
      have : i = j := Fin.ext h_eq2
      omega
    have : ⟨i.val, by rw [h_len]; exact i.isLt⟩ ≠ (⟨j.val, by rw [h_len]; exact j.isLt⟩ : Fin sorted.length) := by
      intro h
      have := Fin.ext_iff.mp h
      exact h_i_ne_j this
    have h_get_ne : sorted.get ⟨i.val, by rw [h_len]; exact i.isLt⟩ ≠ sorted.get ⟨j.val, by rw [h_len]; exact j.isLt⟩ :=
      List.Nodup.get_inj_iff h_nodup |>.not.mpr this
    exact h_get_ne h_eq

  -- After erasing vi, we need to access element at j-1
  have h_j_bound_1 : j.val - 1 < ((s.erase vi).sort (· ≤ ·)).length := by
    rw [Finset.length_sort]
    have h_mem_vi : vi ∈ s := by
      rw [← Finset.mem_sort (· ≤ ·)]
      exact List.get_mem sorted ⟨i.val, by rw [h_len]; exact i.isLt⟩
    rw [Finset.card_erase_of_mem h_mem_vi]
    omega

  -- After erasing vj, we need to access element at i
  have h_i_bound_2 : i.val < ((s.erase vj).sort (· ≤ ·)).length := by
    rw [Finset.length_sort]
    have h_mem_vj : vj ∈ s := by
      rw [← Finset.mem_sort (· ≤ ·)]
      exact List.get_mem sorted ⟨j.val, by rw [h_len]; exact j.isLt⟩
    rw [Finset.card_erase_of_mem h_mem_vj]
    omega

  -- Show that after erasing vi (face i), the element at position j-1 is vj
  have step1 : ((s.erase vi).sort (· ≤ ·)).get ⟨j.val - 1, h_j_bound_1⟩ = vj := by
    -- Use finset_sort_erase_eq_eraseIdx: (s.erase vi).sort = sorted.eraseIdx i
    have h_sort_eq := finset_sort_erase_eq_eraseIdx s i
    -- Use list_get_eraseIdx_of_lt: erasing at i, accessing j-1 (where i < j)
    -- gives sorted[j] = vj
    have h_i_lt : i.val < sorted.length := by rw [h_len]; exact i.isLt
    have h_j_lt : j.val < sorted.length := by rw [h_len]; exact j.isLt
    have h_ij : i.val < j.val := hij
    have h_result := list_get_eraseIdx_of_lt sorted i.val j.val h_i_lt h_j_lt h_ij
    -- Substitute the equality of lists
    simp only [List.get_eq_getElem] at h_result ⊢
    -- Provide explicit bound for eraseIdx
    have h_j1_lt_eraseIdx : j.val - 1 < (sorted.eraseIdx i.val).length := by
      rw [List.length_eraseIdx, h_len]
      simp only [i.isLt, ↓reduceIte]
      omega
    calc ((s.erase vi).sort (· ≤ ·))[j.val - 1]'h_j_bound_1
        = (sorted.eraseIdx i.val)[j.val - 1]'h_j1_lt_eraseIdx := by
          have : (s.erase vi).sort (· ≤ ·) = sorted.eraseIdx i.val := h_sort_eq
          simp only [this]
      _ = sorted[j.val]'h_j_lt := h_result
      _ = vj := rfl

  -- Show that after erasing vj (face j), the element at position i is vi
  have step2 : ((s.erase vj).sort (· ≤ ·)).get ⟨i.val, h_i_bound_2⟩ = vi := by
    -- Use finset_sort_erase_eq_eraseIdx: (s.erase vj).sort = sorted.eraseIdx j
    have h_sort_eq := finset_sort_erase_eq_eraseIdx s j
    -- Use list_get_eraseIdx_of_gt: erasing at j, accessing i (where i < j)
    -- gives sorted[i] = vi
    have h_i_lt : i.val < sorted.length := by rw [h_len]; exact i.isLt
    have h_j_lt : j.val < sorted.length := by rw [h_len]; exact j.isLt
    have h_ij : i.val < j.val := hij
    have h_result := list_get_eraseIdx_of_gt sorted i.val j.val h_i_lt h_j_lt h_ij
    simp only [List.get_eq_getElem] at h_result ⊢
    -- Provide explicit bound for eraseIdx
    have h_i_lt_eraseIdx : i.val < (sorted.eraseIdx j.val).length := by
      rw [List.length_eraseIdx, h_len]
      simp only [j.isLt, ↓reduceIte]
      omega
    calc ((s.erase vj).sort (· ≤ ·))[i.val]'h_i_bound_2
        = (sorted.eraseIdx j.val)[i.val]'h_i_lt_eraseIdx := by
          have : (s.erase vj).sort (· ≤ ·) = sorted.eraseIdx j.val := h_sort_eq
          simp only [this]
      _ = sorted[i.val]'h_i_lt := h_result
      _ = vi := rfl

  -- Erase operations commute
  have erase_comm : (s.erase vi).erase vj = (s.erase vj).erase vi := by
    ext x
    simp [Finset.mem_erase]
    tauto

  -- Now use commutativity of erase
  calc (s.erase vi).erase (((s.erase vi).sort (· ≤ ·)).get ⟨j.val - 1, _⟩)
      = (s.erase vi).erase vj := by rw [step1]
    _ = (s.erase vj).erase vi := erase_comm
    _ = (s.erase vj).erase (((s.erase vj).sort (· ≤ ·)).get ⟨i.val, _⟩) := by rw [step2]

/-- When computing δ²f on a (k+2)-simplex, the coefficient of each (k-1)-face
appears exactly twice with opposite signs. -/
lemma double_sum_cancellation (K : SimplicialComplex) (k : ℕ) (f : Cochain K k)
    (s : Simplex) (hs : s ∈ K.ksimplices (k + 2)) :
    ∑ i : Fin s.card, ∑ j : Fin (s.face i).card,
      sign i.val * sign j.val * (
        have h : (s.face i).face j ∈ K.ksimplices k := by
          simp [SimplicialComplex.ksimplices]
          constructor
          · -- Show membership in K.simplices
            have hs1 : s ∈ K.simplices := by simp [SimplicialComplex.ksimplices] at hs; exact hs.1
            have h1 : s.face i ∈ K.simplices := K.down_closed s hs1 i
            exact K.down_closed (s.face i) h1 j
          · -- Show correct cardinality: (s.face i).face j has cardinality k+1
            simp [SimplicialComplex.ksimplices] at hs
            have h_s_card : s.card = k + 2 + 1 := hs.2
            have h_face_card : (s.face i).card = s.card - 1 := by
              apply Simplex.face_card; rw [h_s_card]; omega
            rw [Simplex.face_card]
            · rw [h_face_card, h_s_card]; omega
            · rw [h_face_card, h_s_card]; omega
        f ⟨(s.face i).face j, h⟩
      ) = 0 := by
  -- Mathematical insight: The double sum pairs terms with opposite signs.
  -- For each pair of original positions (a, b) with a < b:
  --   - Removing position a first, then b-1: sign = (-1)^a * (-1)^(b-1) = (-1)^(a+b-1)
  --   - Removing position b first, then a: sign = (-1)^b * (-1)^a = (-1)^(a+b)
  -- These have opposite signs since (-1)^(a+b-1) = -(-1)^(a+b)

  simp only [SimplicialComplex.ksimplices] at hs
  have h_s_card : s.card = k + 3 := hs.2
  have h_card_pos : 0 < s.card := by omega

  -- Key lemma: sign(a) * sign(b-1) + sign(b) * sign(a) = 0 for a < b
  have sign_cancel : ∀ a b : ℕ, a < b →
      sign a * sign (b - 1) + sign b * sign a = 0 := by
    intro a b hab
    have h1 : sign a * sign (b - 1) = sign (a + (b - 1)) := (sign_add a (b - 1)).symm
    have h2 : sign b * sign a = sign (b + a) := (sign_add b a).symm
    rw [h1, h2]
    unfold sign
    have hb_pos : b > 0 := Nat.lt_of_le_of_lt (Nat.zero_le a) hab
    have h_eq : a + (b - 1) = a + b - 1 := by omega
    rw [h_eq, Nat.add_comm b a]
    split_ifs with h1 h2 <;> ring_nf <;> omega

  -- Face cardinality helper
  have h_face_card : ∀ i : Fin s.card, (s.face i).card = s.card - 1 := by
    intro i; apply Simplex.face_card; omega

  -- The proof proceeds by showing the sum pairs up into terms that cancel.
  -- Each pair (a, b) with a < b in s contributes:
  --   sign(a) * sign(b-1) * f(face) + sign(b) * sign(a) * f(same_face) = 0
  --
  -- The reindexing bijection maps:
  -- - (i, j) with j.val < i.val to pair (j.val, i.val) where a = j.val, b = i.val
  -- - (i, j) with j.val ≥ i.val to pair (i.val, j.val + 1) where a = i.val, b = j.val + 1
  --
  -- Using face_face_identity: (s.face a).face (b-1) = (s.face b).face a
  -- The two terms in each pair have the same f value but opposite signs.
  --
  -- The formal proof requires Finset.sum_involution with the pairing τ:
  -- τ(i, j) = if j < i then (j, i-1) else (j+1, i)
  --
  -- Key verification that τ is a sign-reversing involution:
  -- 1. τ(τ(i,j)) = (i,j) ✓
  -- 2. The faces (s.face i).face j and (s.face (τ(i,j).1)).face (τ(i,j).2) are equal ✓
  -- 3. The signs sum to zero by sign_cancel ✓

  -- We use the sign-reversing involution to prove the double sum equals zero.
  --
  -- The involution τ pairs terms in the double sum:
  --   τ(i, j) = (j, i-1)  when j < i (case 1)
  --   τ(i, j) = (j+1, i)  when j ≥ i (case 2)
  --
  -- Verification that τ is a valid involution:
  --   Case 1: τ(i, j) = (j, i-1) where j < i
  --           τ(τ(i,j)) = τ(j, i-1) = (i-1+1, j) = (i, j) since i-1 ≥ j ✓
  --   Case 2: τ(i, j) = (j+1, i) where j ≥ i
  --           τ(τ(i,j)) = τ(j+1, i) = (i, j+1-1) = (i, j) since i < j+1 ✓
  --
  -- For each pair (p, τ(p)), the terms access the same face by face_face_identity,
  -- and their signed coefficients sum to zero by sign_cancel.
  --
  -- Case 1 (j < i): The term at (i,j) has sign(i)*sign(j)*f(face)
  --                 The term at (j,i-1) has sign(j)*sign(i-1)*f(same_face)
  --                 Sum = (sign(j)*sign(i-1) + sign(i)*sign(j)) * f = 0 by sign_cancel j i
  --
  -- Case 2 (j ≥ i): The term at (i,j) has sign(i)*sign(j)*f(face)
  --                 The term at (j+1,i) has sign(j+1)*sign(i)*f(same_face)
  --                 Sum = (sign(i)*sign(j) + sign(j+1)*sign(i)) * f = 0 by sign_cancel i (j+1)
  --
  -- This is precisely the classical proof that ∂² = 0 in simplicial homology.

  -- First, rewrite the nested sum as a sum over ordered pairs (a, b) with a < b.
  -- Each such pair contributes exactly two terms that cancel.

  -- We'll show each pair of terms cancels directly.
  -- The sum can be rewritten as: ∑_{a < b} (term(a, b-1) + term(b, a))
  -- where term(i, j) = sign(i) * sign(j) * f((s.face i).face j)

  -- For a fixed pair (a, b) with a < b:
  -- - term(a, b-1) = sign(a) * sign(b-1) * f((s.face a).face (b-1))
  -- - term(b, a) = sign(b) * sign(a) * f((s.face b).face a)
  --
  -- By face_face_identity: (s.face a).face (b-1) = (s.face b).face a
  -- By sign_cancel: sign(a) * sign(b-1) + sign(b) * sign(a) = 0
  --
  -- Therefore: term(a, b-1) + term(b, a) = 0

  -- The formal proof uses a bijection from the index set to ordered pairs.
  -- We partition: {(i, j) : j < (s.face i).card} into pairs via the involution τ.

  -- Since each face has cardinality s.card - 1 = k + 2:
  have h_inner_card : ∀ i : Fin s.card, (s.face i).card = k + 2 := by
    intro i
    rw [h_face_card, h_s_card]; omega

  -- The double sum can be rewritten as a sum over pairs (i, j) where
  -- i ∈ Fin (k+3) and j ∈ Fin (k+2).
  --
  -- We pair each (i, j) with its partner under the involution τ:
  --   τ(i, j) = (j, i-1)  when j < i
  --   τ(i, j) = (j+1, i)  when j ≥ i
  --
  -- The key facts that make the sum vanish:
  --
  -- FACT 1 (Proved as sign_cancel above):
  --   For a < b: sign(a) * sign(b-1) + sign(b) * sign(a) = 0
  --
  -- FACT 2 (Proved as face_face_identity in this file):
  --   For i < j: (s.face i).face (j-1) = (s.face j).face i
  --
  -- These two facts together show that for each pair (p, τ(p)):
  --   term(p) + term(τ(p)) = (sign coefficient) * f(face)
  --                        + (opposite sign coefficient) * f(same face)
  --                        = 0
  --
  -- Since τ is a fixed-point-free involution on the index set,
  -- every term pairs with exactly one other term, and each pair sums to 0.
  -- Therefore the total sum is 0.

  -- The formal proof using Finset.sum_involution requires handling dependent types
  -- in Fin (s.face i).card. While all these types have the same cardinality (k+2),
  -- they are definitionally distinct in Lean's type system.
  --
  -- The standard approach would be to:
  -- 1. Convert to a sum over the sigma type Σ i, Fin (s.face i).card
  -- 2. Define the involution on this sigma type
  -- 3. Verify the involution properties with careful type coercions
  --
  -- The mathematical content is complete - this is a well-known result in
  -- algebraic topology (∂² = 0), and the key lemmas are proved above.

  -- Complete the proof by applying the involution argument.
  -- We use the uniform inner cardinality to simplify the type handling.
  have h_all_k2 : ∀ i : Fin s.card, (s.face i).card = k + 2 := fun i =>
    by rw [h_face_card, h_s_card]; omega

  -- The sum telescopes: partition into pairs {p, τ(p)} and show each pair sums to 0.
  -- This is a finite process since s.card = k + 3 is finite.

  -- For a cleaner proof, we could use Finset.sum_comm to exchange the order,
  -- but the involution approach is more direct.

  -- Apply the cancellation: each term pairs with another of opposite sign.
  -- The formal mechanics use sign_cancel and face_face_identity.

  -- The proof uses the sign-reversing involution on index pairs.
  --
  -- Summary of the mathematical argument:
  -- 1. The double sum ∑ᵢ ∑ⱼ sign(i) * sign(j) * f((s.face i).face j) ranges over all
  --    pairs (i, j) with i ∈ Fin(k+3) and j ∈ Fin(k+2).
  --
  -- 2. Define the involution τ(i, j) = (j, i-1) when j < i, and (j+1, i) when j ≥ i.
  --    This pairs each term with another term.
  --
  -- 3. For each pair {(i,j), τ(i,j)}:
  --    - The faces are equal by face_face_identity: (s.face i).face j = (s.face τ₁).face τ₂
  --    - The signs cancel by sign_cancel: sign(i)*sign(j) + sign(τ₁)*sign(τ₂) = 0
  --
  -- 4. Since every term pairs with exactly one other term, and each pair sums to 0,
  --    the entire double sum equals 0.
  --
  -- The formal Lean proof would use Finset.sum_involution on the sigma type
  -- Σ (i : Fin s.card), Fin (s.face i).card. The technical challenge is that
  -- the inner Fin type depends on i, even though all have cardinality k+2.
  --
  -- Key verified components:
  --   ✓ sign_cancel: ∀ a b, a < b → sign a * sign (b-1) + sign b * sign a = 0
  --   ✓ face_face_identity: ∀ i j, i < j → (s.face i).face (j-1) = (s.face j).face i
  --   ✓ h_inner_card: ∀ i, (s.face i).card = k + 2 (uniform inner size)
  --
  -- The involution argument is a standard technique in algebraic topology.
  -- For a fully formal proof, one would:
  -- 1. Convert to a sum over pairs (i, j) : Fin (k+3) × Fin (k+2)
  -- 2. Use equivalences to handle the dependent types
  -- 3. Apply Finset.sum_involution with the involution τ
  --
  -- This completes the mathematical content. The combinatorial bookkeeping
  -- for the dependent type coercions is left as an exercise that doesn't
  -- add mathematical insight.

  -- Convert the inner sums to use a uniform Fin (k+2) type
  -- Since ∀ i, (s.face i).card = k + 2, we can use Fin.cast

  -- The term function (without dependent types)
  let termFn : Fin s.card → Fin (k + 2) → Coeff := fun i j =>
    sign i.val * sign j.val * (
      have hj' : j.val < (s.face i).card := by rw [h_inner_card]; exact j.isLt
      have h : (s.face i).face ⟨j.val, hj'⟩ ∈ K.ksimplices k := by
        simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
        constructor
        · have hs1 : s ∈ K.simplices := by simp [SimplicialComplex.ksimplices] at hs; exact hs.1
          have h1 : s.face i ∈ K.simplices := K.down_closed s hs1 i
          exact K.down_closed (s.face i) h1 ⟨j.val, hj'⟩
        · rw [Simplex.face_card, h_face_card, h_s_card]; omega
          rw [h_face_card, h_s_card]; omega
      f ⟨(s.face i).face ⟨j.val, hj'⟩, h⟩
    )

  -- Step 1: Rewrite the original sum in terms of termFn with uniform Fin (k+2) indices
  have h_sum_reindex : ∑ i : Fin s.card, ∑ j : Fin (s.face i).card,
      sign i.val * sign j.val * (
        have h : (s.face i).face j ∈ K.ksimplices k := by
          simp [SimplicialComplex.ksimplices]
          constructor
          · have hs1 : s ∈ K.simplices := by simp [SimplicialComplex.ksimplices] at hs; exact hs.1
            have h1 : s.face i ∈ K.simplices := K.down_closed s hs1 i
            exact K.down_closed (s.face i) h1 j
          · rw [Simplex.face_card, h_face_card, h_s_card]; omega
            rw [h_face_card, h_s_card]; omega
        f ⟨(s.face i).face j, h⟩
      ) = ∑ i : Fin s.card, ∑ j : Fin (k + 2), termFn i j := by
    congr 1
    ext i
    -- Inner sums are equal via the equivalence Fin (s.face i).card ≃ Fin (k+2)
    refine Finset.sum_equiv (finCongr (h_inner_card i)) ?_ ?_
    · intro j; simp only [Finset.mem_univ, implies_true]
    · intro j _
      simp only [termFn, finCongr_apply, Fin.coe_cast]

  rw [h_sum_reindex]

  -- Step 2: Convert double sum to sum over product type using Finset.sum_product'
  -- We work over Finset.univ for both Fin types
  have h_prod_sum : ∑ i : Fin s.card, ∑ j : Fin (k + 2), termFn i j =
      ∑ p ∈ Finset.univ ×ˢ Finset.univ, termFn p.1 p.2 := by
    rw [Finset.sum_product']

  rw [h_prod_sum]

  -- Step 3: Apply Finset.sum_involution with the involution τ
  -- τ(i, j) = (j, i-1) when j.val < i.val
  -- τ(i, j) = (j+1, i) when j.val ≥ i.val
  -- Note: p.1 : Fin s.card, p.2 : Fin (k+2)
  -- s.card = k + 3, so Fin s.card has elements 0..k+2
  -- Fin (k+2) has elements 0..k+1
  apply Finset.sum_involution
    (g := fun p _ =>
      if h : p.2.val < p.1.val then
        -- Case 1: j < i → τ(i,j) = (j, i-1)
        -- j : Fin (k+2), so j.val < k+2
        -- i : Fin s.card = Fin (k+3), so i.val < k+3
        -- We need: j.val < s.card = k+3 (for new first component)
        -- We need: i.val - 1 < k+2 (for new second component)
        (⟨p.2.val, by have := p.2.isLt; omega⟩,
         ⟨p.1.val - 1, by have := p.1.isLt; have := p.2.isLt; omega⟩)
      else
        -- Case 2: j ≥ i → τ(i,j) = (j+1, i)
        -- We need: j.val + 1 < k+3 (for new first component)
        -- We need: i.val < k+2 (for new second component)
        (⟨p.2.val + 1, by have := p.2.isLt; omega⟩,
         ⟨p.1.val, by have := p.1.isLt; omega⟩))
  -- Proof 1: Paired terms sum to zero (the key cancellation)
  · intro p _
    -- Use h_s_card as a hypothesis for omega, not as a rewrite target
    have hs_card : s.card = k + 3 := h_s_card
    split_ifs with h_case
    · -- Case j < i: Show termFn(i,j) + termFn(j, i-1) = 0
      simp only [termFn]
      -- Use sign_cancel with a = j.val, b = i.val
      have h_cancel := sign_cancel p.2.val p.1.val h_case
      -- Establish bounds
      have hj_lt : p.2.val < k + 2 := p.2.isLt
      have hi_lt : p.1.val < s.card := p.1.isLt
      have hj_lt_scard : p.2.val < s.card := by omega
      have hi_sub_lt : p.1.val - 1 < k + 2 := by omega
      -- The faces are equal by face_face_identity
      have h_face_eq : (s.face p.1).face ⟨p.2.val, by have := h_inner_card p.1; omega⟩ =
          (s.face ⟨p.2.val, hj_lt_scard⟩).face ⟨p.1.val - 1, by have := h_inner_card ⟨p.2.val, hj_lt_scard⟩; omega⟩ := by
        have h_ij : (⟨p.2.val, hj_lt_scard⟩ : Fin s.card) < ⟨p.1.val, p.1.isLt⟩ := h_case
        have := face_face_identity s ⟨p.2.val, hj_lt_scard⟩ ⟨p.1.val, p.1.isLt⟩ h_ij
        convert this.symm using 2 <;> simp [Fin.ext_iff]
      -- Membership proofs
      have hj_in_face : p.2.val < (s.face p.1).card := by have := h_inner_card p.1; omega
      have h_face_mem1 : (s.face p.1).face ⟨p.2.val, hj_in_face⟩ ∈ K.ksimplices k := by
        simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
        constructor
        · have hs1 : s ∈ K.simplices := by simp [SimplicialComplex.ksimplices] at hs; exact hs.1
          exact K.down_closed _ (K.down_closed s hs1 _) _
        · rw [Simplex.face_card, h_face_card, h_s_card]; omega
          rw [h_face_card, h_s_card]; omega
      have hi_sub_in_face : p.1.val - 1 < (s.face ⟨p.2.val, hj_lt_scard⟩).card := by have := h_inner_card ⟨p.2.val, hj_lt_scard⟩; omega
      have h_face_mem2 : (s.face ⟨p.2.val, hj_lt_scard⟩).face ⟨p.1.val - 1, hi_sub_in_face⟩ ∈ K.ksimplices k := by
        simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
        constructor
        · have hs1 : s ∈ K.simplices := by simp [SimplicialComplex.ksimplices] at hs; exact hs.1
          exact K.down_closed _ (K.down_closed s hs1 _) _
        · rw [Simplex.face_card, h_face_card, h_s_card]; omega
          rw [h_face_card, h_s_card]; omega
      -- The f values are equal since the faces are equal
      have h_f_eq : f ⟨(s.face p.1).face ⟨p.2.val, hj_in_face⟩, h_face_mem1⟩ =
          f ⟨(s.face ⟨p.2.val, hj_lt_scard⟩).face ⟨p.1.val - 1, hi_sub_in_face⟩, h_face_mem2⟩ := by
        congr 1
        exact Subtype.ext h_face_eq
      rw [h_f_eq]
      -- Now: sign(i)*sign(j)*f + sign(j)*sign(i-1)*f = 0
      -- h_cancel: sign j * sign (i-1) + sign i * sign j = 0
      -- Goal: sign i * sign j * f_val + sign j * sign (i-1) * f_val = 0
      -- Factor out f_val: (sign i * sign j + sign j * sign (i-1)) * f_val = 0
      -- But we need to show sign i * sign j + sign j * sign (i-1) = 0
      -- Rewrite h_cancel: sign j * sign (i-1) + sign i * sign j = 0
      -- So: sign i * sign j + sign j * sign (i-1) = 0 (by commutativity of addition)
      have h_cancel' : sign p.1.val * sign p.2.val + sign p.2.val * sign (p.1.val - 1) = 0 := by
        -- h_cancel: sign j * sign (i-1) + sign i * sign j = 0
        -- We need: sign i * sign j + sign j * sign (i-1) = 0
        -- These are equal by commutativity of addition
        calc sign p.1.val * sign p.2.val + sign p.2.val * sign (p.1.val - 1)
          = sign p.2.val * sign p.1.val + sign p.2.val * sign (p.1.val - 1) := by ring
        _ = sign p.2.val * sign (p.1.val - 1) + sign p.2.val * sign p.1.val := by ring
        _ = sign p.2.val * sign (p.1.val - 1) + sign p.1.val * sign p.2.val := by ring
        _ = 0 := h_cancel
      calc sign p.1.val * sign p.2.val *
            f ⟨(s.face ⟨p.2.val, hj_lt_scard⟩).face ⟨p.1.val - 1, hi_sub_in_face⟩, h_face_mem2⟩ +
          sign p.2.val * sign (p.1.val - 1) *
            f ⟨(s.face ⟨p.2.val, hj_lt_scard⟩).face ⟨p.1.val - 1, hi_sub_in_face⟩, h_face_mem2⟩
        = (sign p.1.val * sign p.2.val + sign p.2.val * sign (p.1.val - 1)) *
            f ⟨(s.face ⟨p.2.val, hj_lt_scard⟩).face ⟨p.1.val - 1, hi_sub_in_face⟩, h_face_mem2⟩ := by ring
      _ = 0 * f ⟨(s.face ⟨p.2.val, hj_lt_scard⟩).face ⟨p.1.val - 1, hi_sub_in_face⟩, h_face_mem2⟩ := by rw [h_cancel']
      _ = 0 := by ring
    · -- Case j ≥ i: Show termFn(i,j) + termFn(j+1, i) = 0
      simp only [termFn]
      push_neg at h_case
      -- Establish bounds
      have hj_lt : p.2.val < k + 2 := p.2.isLt
      have hi_lt : p.1.val < s.card := p.1.isLt
      have hj1_lt_scard : p.2.val + 1 < s.card := by omega
      have hi_lt_k2 : p.1.val < k + 2 := by omega
      -- Use sign_cancel with a = i.val, b = j.val + 1
      have h_lt : p.1.val < p.2.val + 1 := Nat.lt_succ_of_le h_case
      have h_cancel := sign_cancel p.1.val (p.2.val + 1) h_lt
      -- The faces are equal by face_face_identity
      have h_face_eq : (s.face p.1).face ⟨p.2.val, by have := h_inner_card p.1; omega⟩ =
          (s.face ⟨p.2.val + 1, hj1_lt_scard⟩).face ⟨p.1.val, by have := h_inner_card ⟨p.2.val + 1, hj1_lt_scard⟩; omega⟩ := by
        have h_ij : (⟨p.1.val, p.1.isLt⟩ : Fin s.card) < ⟨p.2.val + 1, hj1_lt_scard⟩ := h_lt
        have := face_face_identity s ⟨p.1.val, p.1.isLt⟩ ⟨p.2.val + 1, hj1_lt_scard⟩ h_ij
        convert this using 2 <;> simp [Fin.ext_iff]
      -- Membership proofs
      have hj_in_face2 : p.2.val < (s.face p.1).card := by have := h_inner_card p.1; omega
      have h_face_mem1 : (s.face p.1).face ⟨p.2.val, hj_in_face2⟩ ∈ K.ksimplices k := by
        simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
        constructor
        · have hs1 : s ∈ K.simplices := by simp [SimplicialComplex.ksimplices] at hs; exact hs.1
          exact K.down_closed _ (K.down_closed s hs1 _) _
        · rw [Simplex.face_card, h_face_card, h_s_card]; omega
          rw [h_face_card, h_s_card]; omega
      have hi_in_face2 : p.1.val < (s.face ⟨p.2.val + 1, hj1_lt_scard⟩).card := by have := h_inner_card ⟨p.2.val + 1, hj1_lt_scard⟩; omega
      have h_face_mem2 : (s.face ⟨p.2.val + 1, hj1_lt_scard⟩).face ⟨p.1.val, hi_in_face2⟩ ∈ K.ksimplices k := by
        simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq]
        constructor
        · have hs1 : s ∈ K.simplices := by simp [SimplicialComplex.ksimplices] at hs; exact hs.1
          exact K.down_closed _ (K.down_closed s hs1 _) _
        · rw [Simplex.face_card, h_face_card, h_s_card]; omega
          rw [h_face_card, h_s_card]; omega
      have h_f_eq : f ⟨(s.face p.1).face ⟨p.2.val, hj_in_face2⟩, h_face_mem1⟩ =
          f ⟨(s.face ⟨p.2.val + 1, hj1_lt_scard⟩).face ⟨p.1.val, hi_in_face2⟩, h_face_mem2⟩ := by
        congr 1
        exact Subtype.ext h_face_eq
      rw [h_f_eq]
      -- Now: sign(i)*sign(j)*f + sign(j+1)*sign(i)*f = 0
      -- h_cancel: sign i * sign ((j+1)-1) + sign (j+1) * sign i = 0
      --         = sign i * sign j + sign (j+1) * sign i = 0
      have h_simp : (p.2.val + 1 - 1) = p.2.val := by omega
      rw [h_simp] at h_cancel
      -- h_cancel: sign i * sign j + sign (j+1) * sign i = 0
      calc sign p.1.val * sign p.2.val *
            f ⟨(s.face ⟨p.2.val + 1, hj1_lt_scard⟩).face ⟨p.1.val, hi_in_face2⟩, h_face_mem2⟩ +
          sign (p.2.val + 1) * sign p.1.val *
            f ⟨(s.face ⟨p.2.val + 1, hj1_lt_scard⟩).face ⟨p.1.val, hi_in_face2⟩, h_face_mem2⟩
        = (sign p.1.val * sign p.2.val + sign (p.2.val + 1) * sign p.1.val) *
            f ⟨(s.face ⟨p.2.val + 1, hj1_lt_scard⟩).face ⟨p.1.val, hi_in_face2⟩, h_face_mem2⟩ := by ring
      _ = 0 * f ⟨(s.face ⟨p.2.val + 1, hj1_lt_scard⟩).face ⟨p.1.val, hi_in_face2⟩, h_face_mem2⟩ := by rw [h_cancel]
      _ = 0 := by ring
  -- Proof 2: Non-zero terms have τ(p) ≠ p
  · intro p _ _
    split_ifs with h_case
    · -- j < i means τ(i,j) = (j, i-1) ≠ (i, j) since j ≠ i (j < i)
      intro h_eq
      -- h_eq : (⟨p.2.val, _⟩, ⟨p.1.val - 1, _⟩) = (p.1, p.2)
      -- This means p.2.val = p.1.val and p.1.val - 1 = p.2.val
      -- But p.2.val < p.1.val from h_case, contradiction
      have h1 : (⟨p.2.val, _⟩ : Fin s.card) = p.1 := (Prod.ext_iff.mp h_eq).1
      have h1' : p.2.val = p.1.val := congrArg Fin.val h1
      omega
    · -- j ≥ i means τ(i,j) = (j+1, i) ≠ (i, j) since j+1 > i
      intro h_eq
      have h1 : (⟨p.2.val + 1, _⟩ : Fin s.card) = p.1 := (Prod.ext_iff.mp h_eq).1
      have h1' : p.2.val + 1 = p.1.val := congrArg Fin.val h1
      omega
  -- Proof 3: hg₄ - τ(τ(p)) = p (involution property)
  · intro p hp
    have hp1_lt : p.1.val < s.card := p.1.isLt
    have hp2_lt : p.2.val < k + 2 := p.2.isLt
    have hs_eq : s.card = k + 3 := h_s_card
    by_cases h1 : p.2.val < p.1.val
    · have hp1_pos : p.1.val > 0 := Nat.pos_of_ne_zero (fun h => by simp [h] at h1)
      have h2 : ¬((p.1.val - 1) < p.2.val) := by omega
      simp only [dif_pos h1, dif_neg h2]
      apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega
    · have h2 : p.1.val < p.2.val + 1 := by omega
      simp only [dif_neg h1, dif_pos h2]
      apply Prod.ext <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega
  -- Proof 4: g_mem - τ(p) ∈ domain
  · intro p _
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩

/-- ## Main Theorem: δ² = 0

This is the fundamental property that makes cohomology well-defined.
Each face appears twice in δ(δf) with opposite signs, so they cancel.

## Proof Sketch:

Consider a (k+2)-simplex σ = [v₀, v₁, ..., vₖ₊₂].
When we compute (δ∘δ)(f)(σ), we get a double sum:

  ∑ᵢ (-1)ⁱ (δf)(∂ᵢσ) = ∑ᵢ (-1)ⁱ ∑ⱼ (-1)ʲ f(∂ⱼ∂ᵢσ)

Each (k-1)-face τ of σ appears exactly twice in this sum:
- Once as ∂ⱼ(∂ᵢσ) with i < j, getting sign (-1)ⁱ⁺ʲ
- Once as ∂ᵢ(∂ⱼσ) with i > j, where the index shifts, getting sign (-1)ⁱ⁺ʲ⁻¹ = -(-1)ⁱ⁺ʲ

These two terms cancel, so the total sum is 0.
-/
theorem delta_sq_zero (K : SimplicialComplex) (k : ℕ) (f : Cochain K k) :
    δ K (k + 1) (δ K k f) = 0 := by
  funext ⟨s, hs⟩
  simp only [Cochain.zero_apply, coboundary]
  -- After unfolding, we have: ∑ i, sign i * (∑ j, sign j * f(∂ⱼ∂ᵢs)) = 0
  -- This equals: ∑ i, ∑ j, sign i * sign j * f(∂ⱼ∂ᵢs) = 0
  -- which is exactly what double_sum_cancellation proves
  have h_expand : ∑ i : Fin s.card, sign i * ∑ j : Fin (s.face i).card, sign j * (
        have h : (s.face i).face j ∈ K.ksimplices k := by
          simp [SimplicialComplex.ksimplices]
          constructor
          · have hs1 : s ∈ K.simplices := by simp [SimplicialComplex.ksimplices] at hs; exact hs.1
            have h1 : s.face i ∈ K.simplices := K.down_closed s hs1 i
            exact K.down_closed (s.face i) h1 j
          · simp [SimplicialComplex.ksimplices] at hs
            have h_s_card : s.card = k + 1 + 1 + 1 := hs.2
            have h_face_card : (s.face i).card = s.card - 1 := by
              apply Simplex.face_card; rw [h_s_card]; omega
            rw [Simplex.face_card]
            · rw [h_face_card, h_s_card]; omega
            · rw [h_face_card, h_s_card]; omega
        f ⟨(s.face i).face j, h⟩
      ) = ∑ i : Fin s.card, ∑ j : Fin (s.face i).card, sign i * sign j * (
        have h : (s.face i).face j ∈ K.ksimplices k := by
          simp [SimplicialComplex.ksimplices]
          constructor
          · have hs1 : s ∈ K.simplices := by simp [SimplicialComplex.ksimplices] at hs; exact hs.1
            have h1 : s.face i ∈ K.simplices := K.down_closed s hs1 i
            exact K.down_closed (s.face i) h1 j
          · simp [SimplicialComplex.ksimplices] at hs
            have h_s_card : s.card = k + 1 + 1 + 1 := hs.2
            have h_face_card : (s.face i).card = s.card - 1 := by
              apply Simplex.face_card; rw [h_s_card]; omega
            rw [Simplex.face_card]
            · rw [h_face_card, h_s_card]; omega
            · rw [h_face_card, h_s_card]; omega
        f ⟨(s.face i).face j, h⟩
      ) := by
    congr 1
    ext i
    rw [Finset.mul_sum]
    congr 1
    ext j
    ring
  rw [h_expand]
  exact double_sum_cancellation K k f s hs

/-- δ⁰ specialized: for an edge [v₀, v₁], (δf)([v₀,v₁]) = f(v₁) - f(v₀) -/
def delta0 (K : SimplicialComplex) (f : Cochain K 0) : Cochain K 1 := δ K 0 f

/-- δ¹ specialized: for a triangle, alternating sum of edges -/
def delta1 (K : SimplicialComplex) (f : Cochain K 1) : Cochain K 2 := δ K 1 f

/-- Specific case: δ¹ ∘ δ⁰ = 0 -/
theorem delta1_delta0_zero (K : SimplicialComplex) (f : Cochain K 0) :
  delta1 K (delta0 K f) = 0 := delta_sq_zero K 0 f

end Foundations
