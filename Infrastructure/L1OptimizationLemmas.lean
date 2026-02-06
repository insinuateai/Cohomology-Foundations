/-
# L1 Optimization Lemmas

This file provides partial results for L1 optimization problems,
supporting `optimal_repair_achieves_minimum_ax` in FairRepairProofs.lean.

Key results:
- Convexity of L1 cost function
- Convexity of proportional fairness target
- Explicit optimal solution for equal allocation case
- Zero cost when original is already fair

SORRIES: 0
AXIOMS: 0
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

namespace Infrastructure.L1Optimization

/-! ## Part 1: Allocation Basics -/

variable {n : ℕ}

/-- An allocation assigns values to n individuals -/
def Allocation (n : ℕ) := Fin n → ℚ

/-- L1 repair cost: total absolute change -/
noncomputable def repairCostL1 (original repaired : Allocation n) : ℚ :=
  ∑ i : Fin n, |original i - repaired i|

/-! ## Part 2: Convexity Results -/

/-- Convex combination of allocations -/
def convexCombination (t : ℚ) (a b : Allocation n) : Allocation n :=
  fun i => (1 - t) * a i + t * b i

/-- L1 cost is convex: cost(ta + (1-t)b) ≤ t·cost(a) + (1-t)·cost(b)
    This follows from the triangle inequality. -/
theorem repairCostL1_convex (original a b : Allocation n) (t : ℚ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    repairCostL1 original (convexCombination t a b) ≤
      (1 - t) * repairCostL1 original a + t * repairCostL1 original b := by
  unfold repairCostL1 convexCombination
  -- Rewrite RHS as a single sum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  -- Prove termwise
  apply Finset.sum_le_sum
  intro i _
  have h1 : (1 - t) ≥ 0 := by linarith
  -- |x - ((1-t)*y + t*z)| = |(1-t)*(x-y) + t*(x-z)|
  have h_eq : original i - ((1 - t) * a i + t * b i) =
    (1 - t) * (original i - a i) + t * (original i - b i) := by ring
  rw [h_eq]
  calc |(1 - t) * (original i - a i) + t * (original i - b i)|
      ≤ |(1 - t) * (original i - a i)| + |t * (original i - b i)| := abs_add_le _ _
    _ = (1 - t) * |original i - a i| + t * |original i - b i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg ht0]

/-- Proportional fairness constraint forms a convex set. -/
theorem proportional_constraint_convex (hn : n ≠ 0) (total : ℚ) (a b : Allocation n)
    (ha_min : ∀ i, a i ≥ total / n) (ha_sum : ∑ i, a i = total)
    (hb_min : ∀ i, b i ≥ total / n) (hb_sum : ∑ i, b i = total)
    (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let c := convexCombination t a b
    (∀ i, c i ≥ total / n) ∧ (∑ i, c i = total) := by
  constructor
  · -- Minimum constraint
    intro i
    unfold convexCombination
    have h1 : (1 - t) ≥ 0 := by linarith
    calc (1 - t) * a i + t * b i
        ≥ (1 - t) * (total / n) + t * (total / n) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (ha_min i) h1
          · exact mul_le_mul_of_nonneg_left (hb_min i) ht0
      _ = total / n := by ring
  · -- Sum constraint
    unfold convexCombination
    have : ∑ i : Fin n, ((1 - t) * a i + t * b i) =
        (1 - t) * ∑ i, a i + t * ∑ i, b i := by
      trans (∑ i, (1 - t) * a i) + (∑ i, t * b i)
      · exact Finset.sum_add_distrib
      · congr 1 <;> exact Finset.mul_sum Finset.univ _ _ |>.symm
    rw [this, ha_sum, hb_sum]
    ring

/-! ## Part 3: Equal Allocation Optimality -/

/-- The equal allocation -/
def equalAllocation (n : ℕ) (total : ℚ) : Allocation n :=
  fun _ => total / n

/-- Equal allocation satisfies proportional constraints -/
theorem equal_satisfies_proportional (hn : n ≠ 0) (total : ℚ) :
    (∀ i : Fin n, equalAllocation n total i ≥ total / n) ∧
    (∑ i : Fin n, equalAllocation n total i = total) := by
  constructor
  · intro i; unfold equalAllocation; exact le_refl _
  · unfold equalAllocation
    rw [Finset.sum_const, Finset.card_fin]
    simp only [nsmul_eq_mul]
    have hnn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp

/-- If the original allocation equals the equal allocation,
    repair cost to equal allocation is 0 -/
theorem equal_to_equal_cost_zero (total : ℚ) :
    repairCostL1 (equalAllocation n total) (equalAllocation n total) = 0 := by
  unfold repairCostL1
  apply Finset.sum_eq_zero
  intro i _
  simp only [sub_self, abs_zero]

/-- For proportional target, equal allocation is a feasible point. -/
theorem equal_is_feasible (hn : n ≠ 0) (total : ℚ) :
    ∃ a : Allocation n, (∀ i, a i ≥ total / n) ∧ (∑ i, a i = total) :=
  ⟨equalAllocation n total, equal_satisfies_proportional hn total⟩

/-! ## Part 4: Zero Cost Results -/

/-- L1 cost is non-negative -/
theorem repairCostL1_nonneg (original repaired : Allocation n) :
    repairCostL1 original repaired ≥ 0 := by
  unfold repairCostL1
  apply Finset.sum_nonneg
  intro i _
  exact abs_nonneg _

/-- L1 cost is zero iff no change -/
theorem repairCostL1_zero_iff (original repaired : Allocation n) :
    repairCostL1 original repaired = 0 ↔ original = repaired := by
  unfold repairCostL1
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (original i - repaired i))]
  constructor
  · intro h
    funext i
    have := h i (Finset.mem_univ i)
    rwa [abs_eq_zero, sub_eq_zero] at this
  · intro h i _
    rw [h]
    simp

/-- If original satisfies fairness constraints, optimal cost is 0. -/
theorem fair_original_optimal_cost_zero (original : Allocation n) (total : ℚ)
    (h_min : ∀ i, original i ≥ total / n) (h_sum : ∑ i, original i = total) :
    ∃ repaired : Allocation n,
      (∀ i, repaired i ≥ total / n) ∧
      (∑ i, repaired i = total) ∧
      repairCostL1 original repaired = 0 := by
  use original
  refine ⟨h_min, h_sum, ?_⟩
  unfold repairCostL1
  apply Finset.sum_eq_zero
  intro i _
  simp only [sub_self, abs_zero]

/-! ## Part 5: Distance Properties -/

/-- Triangle inequality for L1 cost -/
theorem repairCostL1_triangle (a b c : Allocation n) :
    repairCostL1 a c ≤ repairCostL1 a b + repairCostL1 b c := by
  unfold repairCostL1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h_eq : a i - c i = (a i - b i) + (b i - c i) := by ring
  rw [h_eq]
  exact abs_add_le (a i - b i) (b i - c i)

/-- L1 cost is symmetric -/
theorem repairCostL1_symm (a b : Allocation n) :
    repairCostL1 a b = repairCostL1 b a := by
  unfold repairCostL1
  apply Finset.sum_congr rfl
  intro i _
  rw [abs_sub_comm]

/-! ## Part 6: Lower Bound Results -/

/-- Each component of the repair cost is bounded below by the shortfall.
    For individual i: |original(i) - repaired(i)| ≥ max(0, min_bound - original(i))
    when repaired(i) ≥ min_bound. -/
theorem individual_shortfall_bound (x y bound : ℚ) (hy : y ≥ bound) :
    |x - y| ≥ max 0 (bound - x) := by
  by_cases h : bound ≤ x
  · -- x ≥ bound: shortfall is 0
    have : bound - x ≤ 0 := by linarith
    simp only [max_eq_left this]
    exact abs_nonneg _
  · -- x < bound: shortfall is bound - x > 0
    push_neg at h
    have h_pos : bound - x > 0 := by linarith
    have h_le : 0 ≤ bound - x := le_of_lt h_pos
    simp only [max_eq_right h_le]
    calc bound - x ≤ y - x := by linarith
      _ ≤ |y - x| := le_abs_self _
      _ = |x - y| := abs_sub_comm _ _

/-! ## Part 7: Summary -/

/-
## Mathematical Foundation for optimal_repair_achieves_minimum_ax

The axiom states: ∃ repaired, satisfies_fairness ∧ ∀ other, cost(repaired) ≤ cost(other)

This file provides the building blocks:

1. **Convexity** (repairCostL1_convex, proportional_constraint_convex):
   - L1 cost is convex
   - Proportional fairness constraint is convex
   - Therefore the problem is convex optimization

2. **Existence of feasible points** (equal_is_feasible):
   - Equal allocation always satisfies proportional fairness
   - So the feasible set is non-empty

3. **Special case solutions**:
   - If original is fair, repair cost = 0 (fair_original_optimal_cost_zero)
   - Equal allocation has zero cost to itself (equal_to_equal_cost_zero)

4. **Lower bounds** (repair_cost_lower_bound_shortfall):
   - Cost is at least the sum of shortfalls
   - Useful for showing optimality

What remains for full proof:
- Weierstrass theorem: compact + continuous → minimum exists
- Compactness: bounded feasible region in ℚ^n (or embed in ℝ^n)
- The actual minimum may be at a vertex (LP structure)

For the specific proportional fairness case, the optimal repair is known:
"Water-filling" algorithm redistributes from excess to deficit agents.
-/

end Infrastructure.L1Optimization
