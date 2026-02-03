/-
  Infrastructure/FairnessAxiomReplacements.lean

  Provides exact signature-matching replacements for fairness axioms.

  AXIOMS REPLACED:
  - F07: optimal_lipschitz_achieves (IndividualFairness.lean:212)

  APPROACH:
  The theorem `optimal_lipschitz_achieves_proven` in FairnessH1Proofs.lean
  has the exact same signature as the axiom. This file provides the bridge.

  SORRIES: 0
  AXIOMS: 0
-/

import Perspective.IndividualFairness
import Infrastructure.FairnessH1Proofs

namespace Infrastructure.FairnessAxiomReplacements

open IndividualFairness (SimilarityMetric Allocation isLipschitzFair optimalLipschitz)

variable {n : ℕ}

/-! ## F07: Optimal Lipschitz Achieves Fairness

The axiom states: The optimal Lipschitz constant achieves fairness.

Proof:
For any pair (i, j):
- If dist(i, j) = 0: then i = j (by zero_iff), so |T(i) - T(j)| = 0 ≤ L * 0
- If dist(i, j) > 0: the ratio |T(i) - T(j)| / dist(i, j) is one of the values
  in the supremum defining optimalLipschitz, so |T(i) - T(j)| ≤ L * dist(i, j)
-/

/-- F07 REPLACEMENT: Exact signature match for optimal_lipschitz_achieves axiom.

This theorem can directly replace the axiom in IndividualFairness.lean:212.
The proof delegates to FairnessH1Proofs.optimal_lipschitz_achieves_proven.
-/
theorem optimal_lipschitz_achieves_replacement [NeZero n] (metric : SimilarityMetric n)
    (treatment : Allocation n) :
    isLipschitzFair metric (optimalLipschitz metric treatment) treatment :=
  Infrastructure.FairnessH1Proofs.optimal_lipschitz_achieves_proven metric treatment

/-! ## Verification -/

#check @optimal_lipschitz_achieves_replacement
-- Expected: [NeZero n] → (metric : SimilarityMetric n) → (treatment : Allocation n) →
--           isLipschitzFair metric (optimalLipschitz metric treatment) treatment

/-! ## Usage Instructions

To eliminate axiom F07 from IndividualFairness.lean:

1. Add import at top:
   ```
   import Infrastructure.FairnessAxiomReplacements
   ```

2. Replace the axiom declaration (line 212):
   ```
   axiom optimal_lipschitz_achieves [NeZero n] (metric : SimilarityMetric n)
       (treatment : Allocation n) :
       isLipschitzFair metric (optimalLipschitz metric treatment) treatment
   ```

   With:
   ```
   theorem optimal_lipschitz_achieves [NeZero n] (metric : SimilarityMetric n)
       (treatment : Allocation n) :
       isLipschitzFair metric (optimalLipschitz metric treatment) treatment :=
     Infrastructure.FairnessAxiomReplacements.optimal_lipschitz_achieves_replacement metric treatment
   ```

This converts the axiom to a theorem with no change in downstream usage.
-/

end Infrastructure.FairnessAxiomReplacements
