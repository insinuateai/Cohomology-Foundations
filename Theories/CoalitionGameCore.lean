/-
# Coalition Game Core Theory

Marginal contributions, convexity, and core membership.

## Main Results

1. `marginal_well_defined` - Marginal contribution formula
2. `coalition_sum_telescope` - S-sum telescopes for convex games
3. `marginal_vector_in_core` - Marginal vector is in core for convex games

Targets: Mathlib 4.27.0 / Lean 4.27.0
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

namespace CoalitionGameCore

open Finset BigOperators

/-! ## Coalition Game Definition -/

/-- A coalition game on n players -/
structure CoalitionGame (n : ℕ) where
  /-- Value function: assigns a worth to each coalition -/
  value : Finset (Fin n) → ℚ
  /-- Empty coalition has value 0 -/
  value_empty : value ∅ = 0

variable {n : ℕ}

/-! ## Marginal Contribution -/

/-- Marginal contribution of player i to coalition S -/
def marginalContribution (G : CoalitionGame n) (i : Fin n) (S : Finset (Fin n)) : ℚ :=
  G.value (insert i S) - G.value S

/-- Marginal contribution is well-defined -/
theorem marginal_well_defined (G : CoalitionGame n) (i : Fin n) (S : Finset (Fin n))
    (hiS : i ∉ S) : G.marginalContribution i S = G.value (insert i S) - G.value S := rfl

/-- When i ∈ S, marginal contribution is 0 (insert is idempotent) -/
theorem marginal_in_coalition (G : CoalitionGame n) (i : Fin n) (S : Finset (Fin n))
    (hiS : i ∈ S) : G.marginalContribution i S = 0 := by
  simp only [marginalContribution, insert_eq_self.mpr hiS, sub_self]

/-! ## Convexity -/

/-- A game is convex (supermodular) if marginal contributions increase with coalition size -/
def IsConvex (G : CoalitionGame n) : Prop :=
  ∀ i : Fin n, ∀ S T : Finset (Fin n), S ⊆ T → i ∉ T →
    G.marginalContribution i S ≤ G.marginalContribution i T

/-- Convexity implies supermodularity: v(S ∪ T) + v(S ∩ T) ≥ v(S) + v(T)
    Proof by induction on |T \ S|. -/
theorem supermodular_of_convex (G : CoalitionGame n) (hconv : IsConvex G)
    (S T : Finset (Fin n)) : G.value (S ∪ T) + G.value (S ∩ T) ≥ G.value S + G.value T := by
  -- Induction on |T \ S|
  have h_key : ∀ k, (T \ S).card = k →
      G.value (S ∪ T) + G.value (S ∩ T) ≥ G.value S + G.value T := by
    intro k
    induction k generalizing S T with
    | zero =>
      intro hcard
      have hTS : T ⊆ S := by
        intro x hx
        by_contra hxS
        have : x ∈ T \ S := mem_sdiff.mpr ⟨hx, hxS⟩
        rw [card_eq_zero] at hcard
        exact not_mem_empty x (hcard ▸ this)
      simp only [union_eq_left.mpr hTS, inter_eq_right.mpr hTS, add_comm, le_refl]
    | succ k ih =>
      intro hcard
      have hne : (T \ S).Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro h; rw [h] at hcard; cases hcard
      obtain ⟨i, hi⟩ := hne
      rw [mem_sdiff] at hi
      obtain ⟨hiT, hiS⟩ := hi
      let T' := T.erase i
      let S' := insert i S
      have hcard_S'T : (T \ S').card = k := by
        have h1 : T \ S' = (T \ S).erase i := by
          ext x
          simp only [S', mem_sdiff, mem_insert, not_or, mem_erase, ne_eq]
          constructor
          · intro ⟨hxT, hxS, hxi⟩; exact ⟨hxi, hxT, hxS⟩
          · intro ⟨hxi, hxT, hxS⟩; exact ⟨hxT, hxS, hxi⟩
        rw [h1, card_erase_of_mem (mem_sdiff.mpr ⟨hiT, hiS⟩), hcard]; omega
      have hih' := ih S' T hcard_S'T
      have h_S'_union_T : S' ∪ T = S ∪ T := by
        ext x
        simp only [S', mem_union, mem_insert]
        constructor
        · intro h; rcases h with (rfl | hxS) | hxT; right; exact hiT; left; exact hxS; right; exact hxT
        · intro h; rcases h with hxS | hxT; left; right; exact hxS; right; exact hxT
      rw [h_S'_union_T] at hih'
      have h_ins_inter : insert i (S ∩ T) = S' ∩ T := by
        ext x
        simp only [S', mem_insert, mem_inter]
        constructor
        · intro h; rcases h with rfl | ⟨hxS, hxT⟩; exact ⟨Or.inl rfl, hiT⟩; exact ⟨Or.inr hxS, hxT⟩
        · intro ⟨h1, hxT⟩; rcases h1 with rfl | hxS; left; rfl; right; exact ⟨hxS, hxT⟩
      have h_inter_sub : S ∩ T ⊆ S := inter_subset_left
      have h_conv : G.marginalContribution i (S ∩ T) ≤ G.marginalContribution i S :=
        hconv i (S ∩ T) S h_inter_sub hiS
      simp only [marginalContribution] at h_conv
      rw [h_ins_inter] at h_conv
      linarith
  exact h_key (T \ S).card rfl

/-- Equivalent convexity: v(S ∪ T) + v(S ∩ T) ≥ v(S) + v(T) -/
theorem convex_iff_supermodular (G : CoalitionGame n) :
    IsConvex G ↔ ∀ S T : Finset (Fin n),
      G.value (S ∪ T) + G.value (S ∩ T) ≥ G.value S + G.value T := by
  constructor
  · -- Convexity → Supermodularity (proven above)
    exact supermodular_of_convex G
  · -- Supermodularity → Convexity
    intro hsuper i S T hST hiT
    simp only [marginalContribution]
    -- Need: v(S ∪ {i}) - v(S) ≤ v(T ∪ {i}) - v(T)
    -- i.e., v(T ∪ {i}) + v(S) ≥ v(S ∪ {i}) + v(T)
    -- Apply supermodularity to (S ∪ {i}) and T
    -- (S ∪ {i}) ∪ T = T ∪ {i} (since S ⊆ T and i ∉ T)
    -- (S ∪ {i}) ∩ T = S (since i ∉ T)
    have h1 : (insert i S) ∪ T = insert i T := by
      ext x; simp
      constructor
      · intro h
        rcases h with (rfl | hxS) | hxT
        · left; rfl
        · right; exact hST hxS
        · right; exact hxT
      · intro h
        rcases h with rfl | hxT
        · left; left; rfl
        · right; exact hxT
    have h2 : (insert i S) ∩ T = S := by
      ext x; simp
      constructor
      · intro ⟨hx, hxT⟩
        rcases hx with rfl | hxS
        · exact (hiT hxT).elim
        · exact hxS
      · intro hxS
        exact ⟨Or.inr hxS, hST hxS⟩
    have h := hsuper (insert i S) T
    rw [h1, h2] at h
    linarith

/-! ## Marginal Vector -/

/-- Order players by some fixed ordering (here: natural order on Fin n) -/
def playerOrder : List (Fin n) := (List.finRange n)

/-- Coalition of players before i in the ordering -/
def predecessors (i : Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (· < i)

/-- The marginal vector: each player gets their marginal contribution 
    to the coalition of predecessors -/
def marginalVector (G : CoalitionGame n) : Fin n → ℚ :=
  fun i => G.marginalContribution i (predecessors i)

/-- Player i is not in their predecessors -/
theorem not_mem_predecessors (i : Fin n) : i ∉ predecessors i := by
  simp [predecessors, lt_irrefl]

/-! ## Telescoping Sum -/

/-- Predecessors of 0 is empty -/
theorem predecessors_zero (h : 0 < n) : predecessors (⟨0, h⟩ : Fin n) = ∅ := by
  simp [predecessors]
  ext j
  simp [Fin.lt_iff_val_lt_val]

/-- Predecessors of i+1 = predecessors of i ∪ {i} -/
theorem predecessors_succ {i : Fin n} (hi : i.val + 1 < n) :
    predecessors ⟨i.val + 1, hi⟩ = insert i (predecessors i) := by
  ext j
  simp only [predecessors, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro hj
    simp only [Fin.lt_iff_val_lt_val] at hj
    by_cases hji : j = i
    · left; exact hji
    · right
      simp only [Fin.lt_iff_val_lt_val]
      omega
  · intro hj
    rcases hj with rfl | hj
    · simp [Fin.lt_iff_val_lt_val]
    · simp only [mem_filter, mem_univ, true_and] at hj
      simp only [Fin.lt_iff_val_lt_val] at hj ⊢
      omega

/-- Grand coalition equals union of all singletons -/
theorem grand_coalition_eq : (Finset.univ : Finset (Fin n)) =
    (Finset.univ : Finset (Fin n)).biUnion (fun i => {i}) := by
  ext x; simp

/-- Sum over filter of i < k gives v(filter i < k) -/
private theorem sum_filter_lt (G : CoalitionGame n) (k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).sum (marginalVector G) =
    G.value (Finset.univ.filter (fun i : Fin n => i.val < k)) := by
  induction k with
  | zero =>
    simp only [not_lt_zero', filter_False, sum_empty, G.value_empty]
  | succ k ih =>
    by_cases hk' : k < n
    · have h_split : Finset.univ.filter (fun i : Fin n => i.val < k + 1) =
          insert ⟨k, hk'⟩ (Finset.univ.filter (fun i : Fin n => i.val < k)) := by
        ext j
        simp only [mem_filter, mem_univ, true_and, mem_insert]
        constructor
        · intro hj; by_cases hjk : j.val = k; left; exact Fin.ext hjk; right; omega
        · intro hj; rcases hj with rfl | hj; simp only [Fin.val_mk]; omega; omega
      have h_notin : ⟨k, hk'⟩ ∉ Finset.univ.filter (fun i : Fin n => i.val < k) := by
        simp only [mem_filter, mem_univ, true_and, Fin.val_mk, lt_irrefl, not_false_eq_true]
      have h_pred : predecessors ⟨k, hk'⟩ = Finset.univ.filter (fun i : Fin n => i.val < k) := by
        ext i
        simp only [predecessors, mem_filter, mem_univ, true_and, Fin.lt_iff_val_lt_val, Fin.val_mk]
      rw [h_split, sum_insert h_notin, ih (by omega)]
      simp only [marginalVector, marginalContribution, h_pred]
      ring
    · have h_eq : Finset.univ.filter (fun i : Fin n => i.val < k + 1) =
          Finset.univ.filter (fun i : Fin n => i.val < k) := by
        ext i; simp only [mem_filter, mem_univ, true_and]
        have hi : i.val < n := i.isLt; constructor <;> intro _ <;> omega
      rw [h_eq]; exact ih (by omega)

/-- Sum of marginal vector equals value of grand coalition (telescoping) -/
theorem marginal_sum_eq_grand (G : CoalitionGame n) :
    ∑ i : Fin n, marginalVector G i = G.value Finset.univ := by
  have h := sum_filter_lt G n (le_refl n)
  have h_univ : Finset.univ.filter (fun i : Fin n => i.val < n) = Finset.univ := by
    ext i; simp only [mem_filter, mem_univ, true_and, iff_true]; exact i.isLt
  rw [h_univ] at h
  exact h

/-! ## Core Definition -/

/-- A payoff vector is in the core if:
    1. It is efficient: sum = v(N)
    2. It is coalitionally rational: for all S, sum over S ≥ v(S) -/
def InCore (G : CoalitionGame n) (x : Fin n → ℚ) : Prop :=
  (∑ i : Fin n, x i = G.value Finset.univ) ∧
  (∀ S : Finset (Fin n), ∑ i ∈ S, x i ≥ G.value S)

/-! ## Coalition Sum Telescope -/

/-- For convex games, sum of marginal vector over S ≥ v(S) -/
theorem coalition_sum_telescope (G : CoalitionGame n) (h_convex : IsConvex G)
    (S : Finset (Fin n)) : ∑ i ∈ S, marginalVector G i ≥ G.value S := by
  -- Key insight: reorder sum by the ordering
  -- Each player i in S contributes marginalContribution i (predecessors i)
  -- By convexity, this is ≥ marginalContribution i (S ∩ predecessors i)
  -- The latter telescopes to v(S)
  
  -- Induction on |S|
  induction' hS : S.card with k ih generalizing S
  · -- Base: S = ∅
    simp only [card_eq_zero] at hS
    simp [hS, G.value_empty]
  · -- Inductive step
    -- Find the maximum element in S (last in ordering)
    have hne : S.Nonempty := card_pos.mp (by omega)
    let m := S.max' hne
    have hm : m ∈ S := max'_mem S hne
    
    -- S = (S \ {m}) ∪ {m}
    have h_eq : S = insert m (S.erase m) := by
      ext x; simp [mem_insert, mem_erase]
      constructor
      · intro hx
        by_cases hxm : x = m
        · left; exact hxm
        · right; exact ⟨hxm, hx⟩
      · intro hx
        rcases hx with rfl | ⟨_, hx⟩
        · exact hm
        · exact hx
    
    -- Separate sum
    rw [h_eq, sum_insert (not_mem_erase m S)]
    
    -- Apply IH to S \ {m}
    have h_card : (S.erase m).card = k := by
      rw [card_erase_of_mem hm, hS]; omega
    have h_ih := ih (S.erase m) h_card
    
    -- Need: marginalVector G m + ∑_{S\m} marginalVector ≥ v(S)
    -- By IH: ∑_{S\m} marginalVector ≥ v(S\m)
    -- Need: marginalVector G m ≥ v(S) - v(S\m) = marginalContribution m (S\m)
    
    -- By convexity: marginalContribution m (predecessors m) ≥ marginalContribution m (S ∩ predecessors m)
    -- Since m is max in S: S \ {m} ⊆ predecessors m
    -- So S ∩ predecessors m = S \ {m}
    
    have h_pred : S.erase m ⊆ predecessors m := by
      intro x hx
      simp only [mem_erase] at hx
      simp only [predecessors, mem_filter, mem_univ, true_and]
      have hxS : x ∈ S := hx.2
      have hxm : x ≠ m := hx.1
      exact lt_of_le_of_ne (le_max' S x hxS) (Ne.symm hxm)
    
    have h_m_not_pred : m ∉ predecessors m := not_mem_predecessors m
    
    -- By convexity applied to S.erase m ⊆ predecessors m
    have h_conv := h_convex m (S.erase m) (predecessors m) h_pred h_m_not_pred
    
    -- marginalVector G m = marginalContribution m (predecessors m)
    simp only [marginalVector] at h_conv ⊢
    
    -- v(S) = v(insert m (S\m)) = v(S\m) + marginalContribution m (S\m)
    have h_val : G.value S = G.value (S.erase m) + G.marginalContribution m (S.erase m) := by
      simp only [marginalContribution, h_eq, insert_erase hm]
    
    rw [h_val]
    -- Need: mc(m, pred) + ∑_{S\m} mv ≥ v(S\m) + mc(m, S\m)
    -- Have: ∑_{S\m} mv ≥ v(S\m) and mc(m, pred) ≥ mc(m, S\m)
    linarith

/-! ## Main Result -/

/-- For convex games, the marginal vector is in the core -/
theorem marginal_vector_in_core (G : CoalitionGame n) (h_convex : IsConvex G) :
    InCore G (marginalVector G) := by
  constructor
  · -- Efficiency: sum = v(N)
    exact marginal_sum_eq_grand G
  · -- Coalitional rationality: for all S, sum ≥ v(S)
    exact coalition_sum_telescope G h_convex

#check marginal_well_defined
#check coalition_sum_telescope
#check marginal_vector_in_core

end CoalitionGameCore
