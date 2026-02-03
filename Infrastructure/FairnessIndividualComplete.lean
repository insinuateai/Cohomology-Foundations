/-
COBOUND: Multi-Agent Coordination Framework
Module: Infrastructure/FairnessIndividualComplete.lean
Created: February 2026

Complete proofs for Individual Fairness axioms.

AXIOM ELIMINATION:
- F07: optimal_lipschitz_achieves

QUALITY STANDARDS:
- Axioms: 0
- Sorries: 0
-/

import Perspective.IndividualFairness

namespace FairnessIndividualComplete

open IndividualFairness

variable {n : ℕ}

/-! ## Proof of optimal_lipschitz_achieves (F07)

The optimal Lipschitz constant is defined as:
  L* = sup_{p : Fin n × Fin n} (|T(p.1) - T(p.2)| / d(p.1, p.2))  when d(p.1, p.2) ≠ 0
                                 0                                   when d(p.1, p.2) = 0

We need to show that for any pair (i, j):
  |T(i) - T(j)| ≤ L* × d(i, j)

Case 1: d(i, j) = 0
  By metric.zero_iff, this means i = j, so |T(i) - T(j)| = 0 ≤ L* × 0.

Case 2: d(i, j) ≠ 0
  The ratio |T(i) - T(j)| / d(i, j) is one of the terms in the supremum.
  Therefore |T(i) - T(j)| / d(i, j) ≤ L*.
  Multiplying both sides by d(i, j) > 0 gives |T(i) - T(j)| ≤ L* × d(i, j).
-/

/-- Helper: The ratio function used in optimalLipschitz -/
private def lipschitzRatio (metric : SimilarityMetric n) (treatment : Allocation n)
    (p : Fin n × Fin n) : ℚ :=
  if metric.dist p.1 p.2 = 0 then 0
  else |treatment p.1 - treatment p.2| / metric.dist p.1 p.2

/-- The ratio is non-negative -/
private theorem lipschitzRatio_nonneg (metric : SimilarityMetric n) (treatment : Allocation n)
    (p : Fin n × Fin n) : lipschitzRatio metric treatment p ≥ 0 := by
  unfold lipschitzRatio
  split_ifs with h
  · exact le_refl 0
  · apply div_nonneg
    · exact abs_nonneg _
    · exact metric.nonneg p.1 p.2

/-- When dist = 0, i = j by the metric axiom -/
private theorem dist_zero_eq (metric : SimilarityMetric n) (i j : Fin n)
    (h : metric.dist i j = 0) : i = j :=
  (metric.zero_iff i j).mp h

/-- When dist ≠ 0, the ratio is bounded by the supremum -/
private theorem ratio_le_sup [NeZero n] (metric : SimilarityMetric n) (treatment : Allocation n)
    (i j : Fin n) (h : metric.dist i j ≠ 0) :
    |treatment i - treatment j| / metric.dist i j ≤ optimalLipschitz metric treatment := by
  unfold optimalLipschitz
  -- The pair (i, j) is in the supremum
  have hmem : (i, j) ∈ Finset.univ := Finset.mem_univ _
  -- The ratio for (i, j) is the actual ratio since dist ≠ 0
  have hratio : (fun p : Fin n × Fin n => if metric.dist p.1 p.2 = 0 then 0
                else |treatment p.1 - treatment p.2| / metric.dist p.1 p.2) (i, j) =
                |treatment i - treatment j| / metric.dist i j := by
    simp only [h, ↓reduceIte]
  -- Use that sup' is at least as large as any element
  calc |treatment i - treatment j| / metric.dist i j
      = (fun p : Fin n × Fin n => if metric.dist p.1 p.2 = 0 then 0
                else |treatment p.1 - treatment p.2| / metric.dist p.1 p.2) (i, j) := hratio.symm
    _ ≤ Finset.univ.sup' ⟨((0 : Fin n), (0 : Fin n)), Finset.mem_univ _⟩
          (fun p : Fin n × Fin n => if metric.dist p.1 p.2 = 0 then 0
                else |treatment p.1 - treatment p.2| / metric.dist p.1 p.2) :=
        Finset.le_sup' _ hmem

/-- MAIN THEOREM: The optimal Lipschitz constant achieves fairness.

This proves axiom F07: optimal_lipschitz_achieves.
-/
theorem optimal_lipschitz_achieves_proven [NeZero n] (metric : SimilarityMetric n)
    (treatment : Allocation n) :
    isLipschitzFair metric (optimalLipschitz metric treatment) treatment := by
  unfold isLipschitzFair
  intro i j
  by_cases h : metric.dist i j = 0
  · -- Case 1: d(i, j) = 0, so i = j
    have heq : i = j := dist_zero_eq metric i j h
    subst heq
    simp only [sub_self, abs_zero, h, mul_zero, le_refl]
  · -- Case 2: d(i, j) ≠ 0
    -- The ratio |T(i) - T(j)| / d(i, j) ≤ optimalLipschitz
    have hratio := ratio_le_sup metric treatment i j h
    -- Multiply both sides by d(i, j) > 0
    have hpos : metric.dist i j > 0 := by
      apply lt_of_le_of_ne (metric.nonneg i j)
      exact fun heq => h heq.symm
    calc |treatment i - treatment j|
        = |treatment i - treatment j| / metric.dist i j * metric.dist i j := by
          field_simp
      _ ≤ optimalLipschitz metric treatment * metric.dist i j := by
          apply mul_le_mul_of_nonneg_right hratio (le_of_lt hpos)

end FairnessIndividualComplete
