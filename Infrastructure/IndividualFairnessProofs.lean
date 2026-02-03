/-
# Individual Fairness Proofs

Proves axioms related to Lipschitz fairness and similarity metrics:
- IF01: optimal_lipschitz_achieves (IndividualFairness.lean:212)

AXIOMS ELIMINATED: 1

## Mathematical Foundation

Individual fairness requires: |T(i) - T(j)| ≤ L × d(i,j)

The optimal Lipschitz constant L* is:
  L* = sup_{i≠j} |T(i) - T(j)| / d(i,j)

## Proof Strategy

1. Define L* as supremum of ratios over pairs with d(i,j) > 0
2. Show L* achieves fairness: multiply both sides by d(i,j)
3. Show L* is minimal: any smaller L fails for the maximizing pair
-/

import Mathlib.Data.Rat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic

namespace IndividualFairnessProofs

/-! ## Part 1: Similarity Metric -/

/-- A similarity metric on n individuals -/
structure SimilarityMetric (n : ℕ) where
  /-- Distance function -/
  dist : Fin n → Fin n → ℚ
  /-- Non-negativity -/
  nonneg : ∀ i j, dist i j ≥ 0
  /-- Symmetry -/
  symm : ∀ i j, dist i j = dist j i
  /-- Identity of indiscernibles -/
  zero_iff : ∀ i j, dist i j = 0 ↔ i = j
  /-- Triangle inequality -/
  triangle : ∀ i j k, dist i k ≤ dist i j + dist j k

variable {n : ℕ}

/-- Distance from self is zero -/
theorem SimilarityMetric.self_zero (m : SimilarityMetric n) (i : Fin n) :
    m.dist i i = 0 := (m.zero_iff i i).mpr rfl

/-- Distance is positive for distinct points -/
theorem SimilarityMetric.pos_of_ne (m : SimilarityMetric n) (i j : Fin n) (h : i ≠ j) :
    m.dist i j > 0 := by
  have h1 : m.dist i j ≥ 0 := m.nonneg i j
  have h2 : m.dist i j ≠ 0 := fun heq => h ((m.zero_iff i j).mp heq)
  exact lt_of_le_of_ne h1 (Ne.symm h2)

/-! ## Part 2: Lipschitz Fairness -/

/-- An allocation assigns values to individuals -/
def Allocation (n : ℕ) := Fin n → ℚ

/-- L-Lipschitz fairness: |T(i) - T(j)| ≤ L × d(i,j) -/
def isLipschitzFair (m : SimilarityMetric n) (L : ℚ) (T : Allocation n) : Prop :=
  ∀ i j : Fin n, |T i - T j| ≤ L * m.dist i j

/-- Zero Lipschitz means constant allocation -/
theorem zero_lipschitz_constant (m : SimilarityMetric n) (T : Allocation n)
    (h : isLipschitzFair m 0 T) : ∀ i j, T i = T j := by
  intro i j
  have := h i j
  simp only [zero_mul, abs_nonpos_iff, sub_eq_zero] at this
  exact this

/-! ## Part 3: Optimal Lipschitz Constant -/

/-- The ratio |T(i) - T(j)| / d(i,j) for distinct points -/
noncomputable def lipschitzRatio (m : SimilarityMetric n) (T : Allocation n)
    (i j : Fin n) (h : i ≠ j) : ℚ :=
  |T i - T j| / m.dist i j

/-- The ratio is non-negative -/
theorem lipschitzRatio_nonneg (m : SimilarityMetric n) (T : Allocation n)
    (i j : Fin n) (h : i ≠ j) : lipschitzRatio m T i j h ≥ 0 := by
  unfold lipschitzRatio
  apply div_nonneg
  · exact abs_nonneg _
  · exact m.nonneg i j

/-- The set of all pairs with i < j (for finite computation) -/
def orderedPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

/-- The optimal Lipschitz constant -/
noncomputable def optimalLipschitz [NeZero n] (m : SimilarityMetric n) (T : Allocation n) : ℚ :=
  if h : n ≤ 1 then 0
  else
    -- Take sup over all pairs with i ≠ j
    Finset.univ.sup' (by
      use (⟨0, NeZero.pos n⟩, ⟨0, NeZero.pos n⟩)
      exact Finset.mem_univ _
    ) (fun p : Fin n × Fin n =>
      if hp : p.1 = p.2 then 0
      else |T p.1 - T p.2| / m.dist p.1 p.2)

/-- The optimal Lipschitz constant is non-negative -/
theorem optimalLipschitz_nonneg [NeZero n] (m : SimilarityMetric n) (T : Allocation n) :
    optimalLipschitz m T ≥ 0 := by
  unfold optimalLipschitz
  split_ifs with h
  · exact le_refl 0
  · apply Finset.le_sup'
    use (⟨0, NeZero.pos n⟩, ⟨0, NeZero.pos n⟩)
    constructor
    · exact Finset.mem_univ _
    · simp

/-! ## Part 4: Main Theorem -/

/-- Key lemma: For any pair, L* × d(i,j) ≥ |T(i) - T(j)| -/
lemma optimalLipschitz_bound_pair [NeZero n] (m : SimilarityMetric n) (T : Allocation n)
    (i j : Fin n) :
    |T i - T j| ≤ optimalLipschitz m T * m.dist i j := by
  by_cases hij : i = j
  · simp [hij]
  · unfold optimalLipschitz
    split_ifs with h
    · -- n ≤ 1, so i = j (contradiction with hij)
      have : Fintype.card (Fin n) ≤ 1 := by simp [h]
      have hi : i = ⟨0, NeZero.pos n⟩ := Fin.eq_of_val_eq (by
        have := Fin.is_lt i
        omega)
      have hj : j = ⟨0, NeZero.pos n⟩ := Fin.eq_of_val_eq (by
        have := Fin.is_lt j
        omega)
      exact (hij (hi.trans hj.symm)).elim
    · -- n > 1, use supremum property
      have hpos : m.dist i j > 0 := m.pos_of_ne i j hij
      have h_ratio : |T i - T j| / m.dist i j ≤
          Finset.univ.sup' _ (fun p : Fin n × Fin n =>
            if hp : p.1 = p.2 then 0
            else |T p.1 - T p.2| / m.dist p.1 p.2) := by
        apply Finset.le_sup'
        use (i, j)
        constructor
        · exact Finset.mem_univ _
        · simp [hij]
      calc |T i - T j|
          = (|T i - T j| / m.dist i j) * m.dist i j := by
            field_simp
          _ ≤ (Finset.univ.sup' _ _) * m.dist i j := by
            apply mul_le_mul_of_nonneg_right h_ratio
            exact le_of_lt hpos

/-- MAIN THEOREM: The optimal Lipschitz constant achieves fairness -/
theorem optimal_lipschitz_achieves [NeZero n] (m : SimilarityMetric n) (T : Allocation n) :
    isLipschitzFair m (optimalLipschitz m T) T := by
  intro i j
  exact optimalLipschitz_bound_pair m T i j

/-- The optimal constant is minimal (requires L ≥ 0 for n ≤ 1 case) -/
theorem optimalLipschitz_minimal [NeZero n] (m : SimilarityMetric n) (T : Allocation n)
    (L : ℚ) (hL_nonneg : L ≥ 0) (hL : isLipschitzFair m L T) :
    optimalLipschitz m T ≤ L := by
  unfold optimalLipschitz
  split_ifs with h
  · -- n ≤ 1: optimalLipschitz = 0, need 0 ≤ L
    exact hL_nonneg
  · -- Prove L ≥ 0 using distinct elements (since n > 1)
    have hL_nonneg : L ≥ 0 := by
      have hn : n ≥ 2 := by omega
      have h01 : (⟨0, NeZero.pos n⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
      have hpos : m.dist ⟨0, NeZero.pos n⟩ ⟨1, by omega⟩ > 0 := m.pos_of_ne _ _ h01
      have hbound := hL ⟨0, NeZero.pos n⟩ ⟨1, by omega⟩
      by_contra hL_neg
      push_neg at hL_neg
      have h1 : L * m.dist ⟨0, NeZero.pos n⟩ ⟨1, by omega⟩ < 0 := mul_neg_of_neg_of_pos hL_neg hpos
      linarith [abs_nonneg (T ⟨0, NeZero.pos n⟩ - T ⟨1, by omega⟩)]
    apply Finset.sup'_le
    intro p _
    split_ifs with hp
    · -- p.1 = p.2: ratio is 0
      exact hL_nonneg
    · -- p.1 ≠ p.2: ratio ≤ L
      have hpos : m.dist p.1 p.2 > 0 := m.pos_of_ne p.1 p.2 hp
      have hbound := hL p.1 p.2
      calc |T p.1 - T p.2| / m.dist p.1 p.2
          ≤ (L * m.dist p.1 p.2) / m.dist p.1 p.2 := by
            apply div_le_div_of_nonneg_right hbound
            exact le_of_lt hpos
        _ = L := by field_simp

/-! ## Part 5: Additional Properties -/

/-- Any allocation is Lipschitz fair for large enough L -/
theorem always_lipschitz_for_large_L [NeZero n] (m : SimilarityMetric n) (T : Allocation n) :
    ∃ L : ℚ, L ≥ 0 ∧ isLipschitzFair m L T := by
  use optimalLipschitz m T
  exact ⟨optimalLipschitz_nonneg m T, optimal_lipschitz_achieves m T⟩

/-- Lipschitz constant scales with allocation scaling -/
theorem lipschitz_scaling [NeZero n] (m : SimilarityMetric n) (T : Allocation n) (c : ℚ) :
    optimalLipschitz m (fun i => c * T i) = |c| * optimalLipschitz m T := by
  unfold optimalLipschitz
  split_ifs with h
  · -- n ≤ 1: both sides are 0
    simp
  · -- n > 1: use scaling property of sup
    -- Need: sup (|c*T i - c*T j| / d) = |c| * sup (|T i - T j| / d)
    by_cases hc : c = 0
    · -- c = 0: LHS has |0 - 0| = 0, RHS has |0| * _ = 0
      simp [hc]
    · -- c ≠ 0: use the fact that |c*a - c*b| = |c| * |a - b|
      congr 1
      ext p
      split_ifs with hp
      · -- p.1 = p.2: both sides are 0
        simp
      · -- p.1 ≠ p.2: compute
        have habs : |c * T p.1 - c * T p.2| = |c| * |T p.1 - T p.2| := by
          rw [← mul_sub]
          exact abs_mul c (T p.1 - T p.2)
        rw [habs]
        ring

/-! ## Part 6: Summary -/

/--
PROOF SUMMARY:

optimal_lipschitz_achieves: PROVEN

Key steps:
1. Define L* = sup_{i≠j} |T(i) - T(j)| / d(i,j)
2. For any pair (i,j):
   - If i = j: |T i - T j| = 0 ≤ L* × 0
   - If i ≠ j: |T i - T j| / d(i,j) ≤ L* by definition of sup
     Hence |T i - T j| ≤ L* × d(i,j)
3. Therefore L* achieves Lipschitz fairness

The proof is constructive: we explicitly define L* and verify the bound.
-/

end IndividualFairnessProofs
