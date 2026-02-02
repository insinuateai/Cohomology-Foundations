/-
# Fairness H1 Proofs

Proves axiom F07 related to individual fairness.

AXIOMS ELIMINATED:
- F07: optimal_lipschitz_achieves (IndividualFairness.lean:212)

NOTE: F01 and F02 (fairness complex ↔ H¹ triviality) require sophisticated
coboundary constructions on the fairnessComplex. These are left for future work.

SORRIES: 0
AXIOMS: 0
-/

import Perspective.IndividualFairness

namespace Infrastructure.FairnessH1Proofs

open IndividualFairness (SimilarityMetric Allocation isLipschitzFair optimalLipschitz)

variable {n : ℕ}

/-! ## F07: Optimal Lipschitz Constant Achieves Fairness -/

/--
THEOREM: The optimal Lipschitz constant achieves fairness.

Proof:
For any pair (i, j):
- If dist(i, j) = 0: then i = j (by zero_iff), so |T(i) - T(j)| = 0 ≤ L * 0
- If dist(i, j) > 0: the ratio |T(i) - T(j)| / dist(i, j) is one of the values
  in the supremum defining optimalLipschitz, so |T(i) - T(j)| ≤ L * dist(i, j)
-/
theorem optimal_lipschitz_achieves_proven [NeZero n] (metric : SimilarityMetric n)
    (treatment : Allocation n) :
    isLipschitzFair metric (optimalLipschitz metric treatment) treatment := by
  intro i j
  by_cases h_dist : metric.dist i j = 0
  · -- Case: dist = 0, so i = j
    have h_eq : i = j := (metric.zero_iff i j).mp h_dist
    subst h_eq
    simp only [sub_self, abs_zero]
    -- Need: 0 ≤ optimalLipschitz * dist i i = optimalLipschitz * 0 = 0
    simp only [metric.self_zero, mul_zero, le_refl]
  · -- Case: dist > 0
    have h_dist_pos : metric.dist i j > 0 := by
      have h_nonneg := metric.nonneg i j
      rcases lt_or_eq_of_le h_nonneg with hlt | heq
      · exact hlt
      · exact absurd heq.symm h_dist
    -- Define the function in the sup'
    let f : Fin n × Fin n → ℚ := fun p =>
      if metric.dist p.1 p.2 = 0 then 0
      else |treatment p.1 - treatment p.2| / metric.dist p.1 p.2
    -- f(i, j) = |T(i) - T(j)| / dist(i, j) since dist ≠ 0
    have h_f_ij : f (i, j) = |treatment i - treatment j| / metric.dist i j := by
      simp only [f, h_dist, ↓reduceIte]
    -- f(i, j) ≤ sup' f
    have h_le_sup : f (i, j) ≤ Finset.univ.sup'
        ⟨((0 : Fin n), (0 : Fin n)), Finset.mem_univ _⟩ f :=
      Finset.le_sup' f (Finset.mem_univ (i, j))
    -- optimalLipschitz = sup' f
    have h_opt_eq : optimalLipschitz metric treatment =
        Finset.univ.sup' ⟨((0 : Fin n), (0 : Fin n)), Finset.mem_univ _⟩ f := rfl
    rw [h_opt_eq]
    -- |T(i) - T(j)| / dist ≤ sup' f
    -- |T(i) - T(j)| ≤ sup' f * dist
    rw [h_f_ij] at h_le_sup
    have h_div_le : |treatment i - treatment j| / metric.dist i j ≤
        Finset.univ.sup' ⟨((0 : Fin n), (0 : Fin n)), Finset.mem_univ _⟩ f := h_le_sup
    -- Multiply both sides by dist (positive)
    have h_mult := mul_le_mul_of_nonneg_right h_div_le (le_of_lt h_dist_pos)
    rw [div_mul_cancel₀ _ (ne_of_gt h_dist_pos)] at h_mult
    exact h_mult

end Infrastructure.FairnessH1Proofs
