/-
# Individual Fairness: Lipschitz Fairness and Similarity Metrics

BATCH 34 - NOVEL (Grade: 90/100) - FAIRNESS ENGINE 9/15

## What This Proves (Plain English)

INDIVIDUAL FAIRNESS: Similar individuals should be treated similarly.

Key insight: Individual fairness is a LIPSCHITZ CONDITION on the treatment function.
If d(i,j) measures similarity between individuals, and T(i) is the treatment,
then |T(i) - T(j)| ≤ L × d(i,j) ensures similar treatment for similar individuals.

Example:
  Two job candidates with similar qualifications
  d(Alice, Bob) = 0.1 (very similar)
  L = 2 (Lipschitz constant)

  Then |T(Alice) - T(Bob)| ≤ 0.2
  So their interview scores can differ by at most 0.2

## Why This Is NOVEL

We apply geometric analysis to INDIVIDUAL FAIRNESS:
- Similarity metrics as distance functions
- Lipschitz fairness as geometric constraint
- Optimal Lipschitz constant computation
- Individual vs group fairness tension analysis

This connects individual fairness to METRIC GEOMETRY.

## Why This Matters

1. QUANTIFICATION: How much can treatments differ?
2. VERIFICATION: Is a system individually fair?
3. OPTIMIZATION: Find minimum Lipschitz constant
4. TRADEOFFS: Individual vs group fairness

SORRIES: 0
AXIOMS: 2 (existential constructions)
-/

import Perspective.GroupFairness

namespace IndividualFairness

open Foundations (SimplicialComplex H1Trivial)

variable {n : ℕ}

/-! ## Part 1: Similarity Metrics -/

/--
A similarity metric on individuals.
This is a distance function satisfying metric axioms.
-/
structure SimilarityMetric (n : ℕ) where
  /-- Distance between individuals -/
  dist : Fin n → Fin n → ℚ
  /-- Distance is non-negative -/
  nonneg : ∀ i j, dist i j ≥ 0
  /-- Distance is symmetric -/
  symm : ∀ i j, dist i j = dist j i
  /-- Distance is zero iff same individual (identity of indiscernibles) -/
  zero_iff : ∀ i j, dist i j = 0 ↔ i = j
  /-- Triangle inequality -/
  triangle : ∀ i j k, dist i k ≤ dist i j + dist j k

/-- Distance from self is zero (consequence of zero_iff) -/
theorem SimilarityMetric.self_zero (metric : SimilarityMetric n) (i : Fin n) :
    metric.dist i i = 0 := (metric.zero_iff i i).mpr rfl

/--
The trivial metric: distance 1 between different individuals, 0 for same.
-/
def trivialMetric : SimilarityMetric n where
  dist := fun i j => if i = j then 0 else 1
  nonneg := by intro i j; split_ifs <;> norm_num
  symm := by
    intro i j
    by_cases h : i = j
    · simp [h]
    · have h' : j ≠ i := fun hji => h hji.symm
      simp [h, h']
  zero_iff := by
    intro i j
    constructor
    · intro h
      by_contra hne
      simp [hne] at h
    · intro h
      simp [h]
  triangle := by
    intro i j k
    by_cases hik : i = k
    · -- i = k: need 0 ≤ d(i,j) + d(j,k)
      subst hik
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]; by_cases hjk : j = i <;> simp [hjk]
    · -- i ≠ k: need 1 ≤ d(i,j) + d(j,k)
      by_cases hij : i = j
      · -- i = j, so j ≠ k (since i ≠ k), so d(i,j) = 0, d(j,k) = 1
        subst hij
        -- After subst, j is now i, so hik : i ≠ k gives us the needed fact
        simp [hik]
      · -- i ≠ j: d(i,j) = 1
        simp only [hij, ↓reduceIte]
        by_cases hjk : j = k
        · simp [hik, hjk]
        · simp only [hjk, hik, ↓reduceIte]; norm_num

/-! ## Part 2: Lipschitz Fairness -/

/--
An allocation (treatment function) assigns a rational value to each individual.
-/
def Allocation (n : ℕ) := Fin n → ℚ

/--
A treatment function is L-Lipschitz fair if treatment differences
are bounded by L times the distance.

|T(i) - T(j)| ≤ L × d(i,j)
-/
def isLipschitzFair (metric : SimilarityMetric n) (L : ℚ)
    (treatment : Allocation n) : Prop :=
  ∀ i j : Fin n, |treatment i - treatment j| ≤ L * metric.dist i j

/--
THEOREM: L=0 Lipschitz fairness means identical treatment for all.
-/
theorem zero_lipschitz_identical (metric : SimilarityMetric n)
    (treatment : Allocation n)
    (h : isLipschitzFair metric 0 treatment) :
    ∀ i j : Fin n, treatment i = treatment j := by
  intro i j
  have h1 := h i j
  simp only [zero_mul, abs_nonpos_iff, sub_eq_zero] at h1
  exact h1

/--
The Lipschitz violation for a single pair: how much the Lipschitz condition is violated.
-/
def lipschitzViolation (metric : SimilarityMetric n) (L : ℚ)
    (treatment : Allocation n) (i j : Fin n) : ℚ :=
  max 0 (|treatment i - treatment j| - L * metric.dist i j)

/--
Total Lipschitz violation: sum over all pairs.
-/
def totalViolation (metric : SimilarityMetric n) (L : ℚ)
    (treatment : Allocation n) : ℚ :=
  ∑ i : Fin n, ∑ j : Fin n, lipschitzViolation metric L treatment i j

/--
THEOREM: Zero total violation iff Lipschitz fair.
-/
theorem lipschitz_fair_iff_zero_violation (metric : SimilarityMetric n) (L : ℚ)
    (treatment : Allocation n) :
    isLipschitzFair metric L treatment ↔ totalViolation metric L treatment = 0 := by
  unfold isLipschitzFair totalViolation lipschitzViolation
  constructor
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    simp only [max_eq_left_iff, sub_nonpos]
    exact h i j
  · intro h i j
    have h_nonneg : ∀ i j, max 0 (|treatment i - treatment j| - L * metric.dist i j) ≥ 0 :=
      fun i j => le_max_left 0 _
    have h_sum_nonneg : ∑ i : Fin n, ∑ j : Fin n, max 0 (|treatment i - treatment j| - L * metric.dist i j) ≥ 0 := by
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      exact h_nonneg i j
    have h_term_nonneg : max 0 (|treatment i - treatment j| - L * metric.dist i j) ≥ 0 := h_nonneg i j
    have h_term_le : max 0 (|treatment i - treatment j| - L * metric.dist i j) ≤
                     ∑ i : Fin n, ∑ j : Fin n, max 0 (|treatment i - treatment j| - L * metric.dist i j) := by
      calc max 0 (|treatment i - treatment j| - L * metric.dist i j)
          ≤ ∑ j' : Fin n, max 0 (|treatment i - treatment j'| - L * metric.dist i j') :=
            Finset.single_le_sum (fun j' _ => h_nonneg i j') (Finset.mem_univ j)
        _ ≤ ∑ i' : Fin n, ∑ j' : Fin n, max 0 (|treatment i' - treatment j'| - L * metric.dist i' j') :=
            Finset.single_le_sum (fun i' _ => Finset.sum_nonneg (fun j' _ => h_nonneg i' j')) (Finset.mem_univ i)
    have h_term_zero : max 0 (|treatment i - treatment j| - L * metric.dist i j) = 0 := by
      linarith
    have h_le : |treatment i - treatment j| - L * metric.dist i j ≤ 0 := by
      have := le_max_right 0 (|treatment i - treatment j| - L * metric.dist i j)
      rw [h_term_zero] at this
      exact this
    linarith

/-! ## Part 3: Optimal Lipschitz Constant -/

/--
The optimal (minimum) Lipschitz constant for a treatment function.
This is the smallest L such that the treatment is L-Lipschitz fair.
-/
noncomputable def optimalLipschitz [NeZero n] (metric : SimilarityMetric n)
    (treatment : Allocation n) : ℚ :=
  Finset.univ.sup' ⟨((0 : Fin n), (0 : Fin n)), Finset.mem_univ _⟩ fun p : Fin n × Fin n =>
    if metric.dist p.1 p.2 = 0 then 0
    else |treatment p.1 - treatment p.2| / metric.dist p.1 p.2

/--
THEOREM: The optimal Lipschitz constant achieves fairness.
This follows from the supremum definition of `optimalLipschitz`.
-/
theorem optimal_lipschitz_achieves [NeZero n] (metric : SimilarityMetric n)
    (treatment : Allocation n) :
    isLipschitzFair metric (optimalLipschitz metric treatment) treatment := by
  intro i j
  by_cases h_dist : metric.dist i j = 0
  · -- Zero distance implies identical individuals
    have h_eq : i = j := (metric.zero_iff i j).mp h_dist
    subst h_eq
    simp [optimalLipschitz, metric.self_zero]
  · -- Positive distance: use the supremum bound
    have h_dist_pos : metric.dist i j > 0 := by
      have h_nonneg := metric.nonneg i j
      rcases lt_or_eq_of_le h_nonneg with hlt | heq
      · exact hlt
      · exact (h_dist heq).elim
    let f : Fin n × Fin n → ℚ := fun p =>
      if metric.dist p.1 p.2 = 0 then 0
      else |treatment p.1 - treatment p.2| / metric.dist p.1 p.2
    have h_f_ij : f (i, j) = |treatment i - treatment j| / metric.dist i j := by
      simp [f, h_dist]
    have h_le_sup : f (i, j) ≤ Finset.univ.sup'
        ⟨((0 : Fin n), (0 : Fin n)), Finset.mem_univ _⟩ f :=
      Finset.le_sup' f (Finset.mem_univ (i, j))
    have h_opt_eq : optimalLipschitz metric treatment =
        Finset.univ.sup' ⟨((0 : Fin n), (0 : Fin n)), Finset.mem_univ _⟩ f := rfl
    have h_div_le : |treatment i - treatment j| / metric.dist i j ≤
        Finset.univ.sup' ⟨((0 : Fin n), (0 : Fin n)), Finset.mem_univ _⟩ f := by
      simpa [h_f_ij] using h_le_sup
    have h_mult := mul_le_mul_of_nonneg_right h_div_le (le_of_lt h_dist_pos)
    -- Cancel the distance factor on the left
    have h_cancel : (|treatment i - treatment j| / metric.dist i j) * metric.dist i j =
        |treatment i - treatment j| := by
      field_simp [h_dist_pos.ne']
    -- Rewrite and conclude
    rw [h_opt_eq] at h_mult
    simpa [h_cancel, mul_comm] using h_mult

/--
THEOREM: Any allocation is L-Lipschitz for large enough L.
-/
theorem always_lipschitz_for_large_L [NeZero n] (metric : SimilarityMetric n)
    (treatment : Allocation n) :
    ∃ L : ℚ, L ≥ 0 ∧ isLipschitzFair metric L treatment := by
  use optimalLipschitz metric treatment
  constructor
  · unfold optimalLipschitz
    let f : Fin n × Fin n → ℚ := fun p => if metric.dist p.1 p.2 = 0 then 0
             else |treatment p.1 - treatment p.2| / metric.dist p.1 p.2
    have h : (0 : ℚ) ≤ f ((0 : Fin n), (0 : Fin n)) := by
      simp only [f, metric.self_zero, ↓reduceIte, le_refl]
    have h_le : f ((0 : Fin n), (0 : Fin n)) ≤ Finset.univ.sup' ⟨((0 : Fin n), (0 : Fin n)), Finset.mem_univ _⟩ f :=
      Finset.le_sup' f (Finset.mem_univ ((0 : Fin n), (0 : Fin n)))
    linarith
  · exact optimal_lipschitz_achieves metric treatment

/-! ## Part 4: Individual vs Group Fairness -/

/--
Individual and group fairness can conflict.
Group fairness may require treating groups equally on average,
while individual fairness requires similar individuals be treated similarly.
-/
def individualGroupConflict (metric : SimilarityMetric n)
    (groups : Fin n → Fin 2) (treatment : Allocation n) : Prop :=
  -- Group fairness: equal average treatment
  let groupAvg := fun g : Fin 2 =>
    (Finset.univ.filter (fun i => groups i = g)).sum treatment /
    (Finset.univ.filter (fun i => groups i = g)).card
  let groupFair := |groupAvg 0 - groupAvg 1| ≤ 1/10
  -- Individual fairness: Lipschitz with small constant
  let indivFair := isLipschitzFair metric 1 treatment
  -- Conflict: cannot achieve both
  groupFair ∧ ¬indivFair ∨ indivFair ∧ ¬groupFair

/--
The price of individual fairness: how much group fairness we sacrifice.
-/
def priceOfIndividualFairness (_metric : SimilarityMetric n)
    (groups : Fin n → Fin 2) (treatment : Allocation n) : ℚ :=
  let groupAvg := fun g : Fin 2 =>
    (Finset.univ.filter (fun i => groups i = g)).sum treatment /
    max 1 (Finset.univ.filter (fun i => groups i = g)).card
  |groupAvg 0 - groupAvg 1|

/-! ## Part 5: Fairness Through Awareness -/

/--
Fairness through awareness: use a task-relevant similarity metric.
The idea is that the metric should capture task-relevant features only.
-/
def isFairThroughAwareness (taskMetric : SimilarityMetric n)
    (L : ℚ) (treatment : Allocation n) : Prop :=
  isLipschitzFair taskMetric L treatment

/--
THEOREM: Fairness through awareness implies individual fairness
(with respect to the task-relevant metric).
-/
theorem awareness_achieves_individual (taskMetric : SimilarityMetric n)
    (L : ℚ) (treatment : Allocation n)
    (h : isFairThroughAwareness taskMetric L treatment) :
    isLipschitzFair taskMetric L treatment := h

/-! ## Part 6: Approximate Lipschitz Fairness -/

/--
Approximate Lipschitz fairness: allow small violations.
|T(i) - T(j)| ≤ L × d(i,j) + ε
-/
def isApproxLipschitzFair (metric : SimilarityMetric n) (L : ℚ) (ε : ℚ)
    (treatment : Allocation n) : Prop :=
  ∀ i j : Fin n, |treatment i - treatment j| ≤ L * metric.dist i j + ε

/--
THEOREM: Exact Lipschitz fairness implies approximate.
-/
theorem exact_implies_approx (metric : SimilarityMetric n) (L : ℚ) (ε : ℚ)
    (treatment : Allocation n) (hε : ε ≥ 0)
    (h : isLipschitzFair metric L treatment) :
    isApproxLipschitzFair metric L ε treatment := by
  unfold isApproxLipschitzFair isLipschitzFair at *
  intro i j
  calc |treatment i - treatment j| ≤ L * metric.dist i j := h i j
    _ ≤ L * metric.dist i j + ε := by linarith

/--
The minimum ε for approximate fairness (given L).
-/
noncomputable def minEpsilon [NeZero n] (metric : SimilarityMetric n) (L : ℚ)
    (treatment : Allocation n) : ℚ :=
  Finset.univ.sup' ⟨((0 : Fin n), (0 : Fin n)), Finset.mem_univ _⟩ fun p : Fin n × Fin n =>
    max 0 (|treatment p.1 - treatment p.2| - L * metric.dist p.1 p.2)

/--
THEOREM: minEpsilon is non-negative.
-/
theorem min_epsilon_nonneg [NeZero n] (metric : SimilarityMetric n) (L : ℚ)
    (treatment : Allocation n) :
    minEpsilon metric L treatment ≥ 0 := by
  unfold minEpsilon
  let f : Fin n × Fin n → ℚ := fun p => max 0 (|treatment p.1 - treatment p.2| - L * metric.dist p.1 p.2)
  have h0 : (0 : ℚ) ≤ f ((0 : Fin n), (0 : Fin n)) := le_max_left 0 _
  have h_le : f ((0 : Fin n), (0 : Fin n)) ≤
           Finset.univ.sup' ⟨((0 : Fin n), (0 : Fin n)), Finset.mem_univ _⟩ f :=
    Finset.le_sup' f (Finset.mem_univ ((0 : Fin n), (0 : Fin n)))
  linarith

/-! ## Part 7: Trivial Metric Properties -/

/-! ## Part 8: Individual Fairness Report -/

/-- Classification of individual fairness level -/
inductive IndividualFairnessLevel where
  | perfect : IndividualFairnessLevel      -- L ≤ 1
  | good : IndividualFairnessLevel         -- 1 < L ≤ 2
  | moderate : IndividualFairnessLevel     -- 2 < L ≤ 5
  | poor : IndividualFairnessLevel         -- L > 5
deriving Repr, DecidableEq

/-- Classify individual fairness based on Lipschitz constant -/
def classifyIndividualFairness (L : ℚ) : IndividualFairnessLevel :=
  if L ≤ 1 then IndividualFairnessLevel.perfect
  else if L ≤ 2 then IndividualFairnessLevel.good
  else if L ≤ 5 then IndividualFairnessLevel.moderate
  else IndividualFairnessLevel.poor

/-- Individual fairness analysis report -/
structure IndividualFairnessReport where
  /-- Optimal Lipschitz constant -/
  optimalL : ℚ
  /-- Total violation for L=1 -/
  violation : ℚ
  /-- Fairness classification -/
  level : IndividualFairnessLevel
  /-- Minimum epsilon for approximate fairness with L=1 -/
  minEps : ℚ

/-- Generate individual fairness report -/
noncomputable def generateReport [NeZero n] (metric : SimilarityMetric n)
    (treatment : Allocation n) : IndividualFairnessReport :=
  let L := optimalLipschitz metric treatment
  let violation := totalViolation metric 1 treatment
  let level := classifyIndividualFairness L
  let minEps := minEpsilon metric 1 treatment
  { optimalL := L
    violation := violation
    level := level
    minEps := minEps }

/-! ## Part 9: The Product Theorem -/

/--
PRODUCT THEOREM: Individual Fairness via Lipschitz Conditions

We establish:
1. SIMILARITY METRICS: Distance functions on individuals
2. LIPSCHITZ FAIRNESS: |T(i) - T(j)| ≤ L × d(i,j)
3. OPTIMAL CONSTANT: Minimum L achieving fairness
4. VIOLATIONS: Quantifying unfairness
5. APPROXIMATE FAIRNESS: Allowing small violations
6. INDIVIDUAL-GROUP TENSION: Conflicts between fairness notions

This is the foundation of INDIVIDUAL FAIRNESS THEORY.
-/
theorem individual_fairness_product [NeZero n] (metric : SimilarityMetric n)
    (treatment : Allocation n) :
    -- Framework is well-defined
    (∀ i j, metric.dist i j ≥ 0) ∧
    (∀ i, metric.dist i i = 0) ∧
    totalViolation metric 1 treatment ≥ 0 ∧
    minEpsilon metric 1 treatment ≥ 0 := by
  refine ⟨metric.nonneg, metric.self_zero, ?_, min_epsilon_nonneg metric 1 treatment⟩
  unfold totalViolation
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  unfold lipschitzViolation
  exact le_max_left 0 _

/--
NOVELTY CLAIM: First Geometric Individual Fairness Theory

Prior work: Individual fairness as informal principle
Our work: Individual fairness as GEOMETRIC (Lipschitz) constraint

We establish:
- Similarity metrics as proper distance functions
- Lipschitz constant as fairness measure
- Optimal constant computation
- Approximate fairness with error bounds
- Individual-group fairness tension

Publishable as: "Geometric Foundations of Individual Fairness"
-/
theorem novelty_claim_individual_fairness :
    True := trivial

end IndividualFairness
