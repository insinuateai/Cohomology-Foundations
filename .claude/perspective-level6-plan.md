# Perspective Level‑6 Proof Upgrade Plan (2026‑02‑04)

## Goal
Upgrade all Perspective/ proofs to Level 6 where possible. If a statement cannot yet be fully proven, keep it as an honest axiom (Level 2) and document the blocker.

## Status Update
- Eliminated `h1_dim_components_bound` in [Perspective/DimensionBound.lean](../Perspective/DimensionBound.lean) using `Infrastructure.DimensionBoundProofs.h1_dim_components_bound_proven`.
- Eliminated `optimal_lipschitz_achieves` in [Perspective/IndividualFairness.lean](../Perspective/IndividualFairness.lean) with a local Level‑6 proof.

## Non‑negotiable constraints
- Do not weaken statements or change theorem types.
- Level 2 (honest axiom) is preferred over any weakened proof.
- Avoid new import cycles; reuse existing imports when possible.
- `lake build` must pass after any change.
- If axiom status changes, update the axiom registry and run `make axiom-count`.

## Inventory: Perspective/ axioms (current)

### Compositional.lean
- `forest_single_edge_composition_axiom_aux`
- `general_acyclic_composition_axiom_aux`
- `large_disagreement_breaks_alignment_aux`

### Bifurcation.lean
- `safety_margin_aux`
- `bifurcation_catastrophic_aux`

### IndividualFairness.lean
- `optimal_lipschitz_achieves`

### FairnessFoundations.lean
- `h1_trivial_implies_fair_allocation`

### ConflictLocalization.lean
- `forms_cycle_from_global_failure`
- `minimal_conflict_exists_aux`

### Curvature.lean
- `h1_trivial_implies_bounded_disagreement_ax`
- `barrier_implies_high_curvature_ax`
- `low_curvature_implies_no_barrier_ax`

### EntropyProduction.lean
- `lower_production_lower_cost_aux`

### FairRepair.lean
- `optimal_repair_exists`

### EscapeTime.lean
- `escape_time_finite_ax`
- `escape_time_monotone_ax`
- `escape_time_bounded_ax`

### Stability.lean
- `stability_of_h1_trivial_aux`
- `measurement_robustness_aux`

### MayerVietoris.lean
- `simple_mayer_vietoris`

### DimensionBound.lean
- `h1_dim_components_bound`

### InformationBound.lean
- `alignment_requires_information_aux`

### AgentCoordination.lean
- `composition_deadlock_example_aux`

### FairnessDynamics.lean
- `negative_lyapunov_stable_ax`

### ConflictResolution.lean
- `remove_edge_from_single_cycle_aux'`
- `fill_triangle_h1_trivial_aux'`
- `resolution_edge_exists_maximal_aux`

### CriticalPoints.lean
- `saddle_has_escape_ax`

### HierarchicalAlignment.lean
- `hierarchical_decomposition_aux`

### OptimalRepair.lean
- `aligned_implies_H1_trivial`
- `optimal_repair_exists_ax`

### SpectralGap.lean
- `vertexDegreeAx`
- `laplacianExists`
- `laplacianEigenvalues`
- `eigenvalues_nonneg`
- `spectral_gap_bounded_aux`

## Candidate proof sources (likely matches)
These infrastructure files appear to contain proofs for the same concepts and should be checked first:

- Compositional: Infrastructure/GraphComposition.lean, Infrastructure/TreeAcyclicityComplete.lean, Infrastructure/PathDecompositionComplete.lean
- Bifurcation: Infrastructure/BifurcationProofs.lean, Infrastructure/SafetyMarginProofs.lean
- IndividualFairness: Infrastructure/IndividualFairnessProofs.lean
- FairnessFoundations: Infrastructure/FairnessH1Proofs.lean, Infrastructure/FairnessComplexH1.lean
- ConflictLocalization: Infrastructure/ConflictLocalizationProofs.lean
- Curvature: Infrastructure/CurvatureProofs.lean
- EntropyProduction: Infrastructure/EntropyProductionProofs.lean
- FairRepair: Infrastructure/FairRepairProofs.lean
- EscapeTime: Infrastructure/PathCompatibilityProofs.lean, Infrastructure/StabilityProofs.lean (confirm)
- Stability: Infrastructure/StabilityProofs.lean
- MayerVietoris: Infrastructure/MayerVietorisProofs.lean
- DimensionBound: Infrastructure/DimensionBoundProofs.lean
- InformationBound: Infrastructure/InformationBoundProofs.lean
- AgentCoordination: Infrastructure/CoalitionH2Proofs.lean or GameTheoryBridge.lean (confirm)
- FairnessDynamics: Infrastructure/FairnessDynamicsProofs.lean, Infrastructure/LyapunovProofs.lean
- ConflictResolution: Infrastructure/MinimalConflictProofs.lean, Infrastructure/SmallComplexH2.lean, Infrastructure/CompleteComplexH1.lean
- CriticalPoints: Infrastructure/CriticalPointsProofs.lean
- HierarchicalAlignment: Infrastructure/HierarchicalAlignmentProofs.lean, Infrastructure/HierarchicalCompositionProofs.lean
- OptimalRepair: Infrastructure/OptimalRepairProofs.lean
- SpectralGap: Infrastructure/SpectralGapProofs.lean

## Priority order (shortest gap → longest)
1. Direct proof transfers from matching Infrastructure/*Proofs.lean files (SpectralGap, MayerVietoris, DimensionBound, Curvature, EntropyProduction, Stability, InformationBound).
2. Fairness‑linked lemmas with existing fairness proof bridges (FairnessFoundations, IndividualFairness, FairnessDynamics, FairRepair, OptimalRepair).
3. Graph‑theoretic or topology‑heavy items (ConflictResolution, Compositional, HierarchicalAlignment).
4. EscapeTime and AgentCoordination (likely need new formalization or remain Level 2).

## Execution steps
1. For each axiom above, search for a theorem with the same statement (or stronger) in Infrastructure/.
2. If found, replace axiom with theorem proof (no statement change).
3. If not found, create a local lemma (proof) using existing proven results. If proof fails, keep as axiom and document blocker.
4. Run `lake build` and update `.claude/axiom-registry.md` + `make axiom-count` after each batch.

## Tracking fields (to fill in per axiom)
- Status: {unverified | proven | blocked}
- Proof source: file + theorem name
- Dependencies: list of required lemmas
- Notes: import changes / obstacles
