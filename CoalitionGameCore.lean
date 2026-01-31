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

/-- Equivalent convexity: v(S ∪ T) + v(S ∩ T) ≥ v(S) + v(T) -/
theorem convex_iff_supermodular (G : CoalitionGame n) :
    IsConvex G ↔ ∀ S T : Finset (Fin n), 
      G.value (S ∪ T) + G.value (S ∩ T) ≥ G.value S + G.value T := by
  constructor
  · intro hconv S T
    -- Standard supermodularity proof
    sorry
  · intro hsuper i S T hST hiT
    simp only [marginalContribution]
    -- Use supermodularity with appropriate sets
    sorry

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

/-- Sum of marginal vector equals value of grand coalition -/
theorem marginal_sum_eq_grand (G : CoalitionGame n) :
    ∑ i : Fin n, marginalVector G i = G.value Finset.univ := by
  -- Telescoping: each term adds one player
  -- Sum of (v(S_i ∪ {i}) - v(S_i)) for ordered players telescopes to v(N) - v(∅)
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty, G.value_empty]
  | succ k ih =>
    -- Separate last player
    rw [Fin.sum_univ_castSucc]
    simp only [marginalVector, marginalContribution]
    -- Last player's contribution + previous sum
    sorry -- Telescoping algebra

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
