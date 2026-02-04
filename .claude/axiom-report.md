# Axiom Dependency Report

Generated: 2026-02-01T23:46:14+00:00
Total axioms: 74
Target: ~15 external math axioms

## Summary by Directory

| Directory | Count | % of Total |
|-----------|-------|------------|
| Perspective/         |  41 |  55% |
| MultiAgent/          |  17 |  22% |
| Theories/            |  11 |  14% |
| Infrastructure/      |   3 |   4% |
| H1Characterization/  |   2 |   2% |

## All Axioms

| File | Line | Axiom Name |
|------|------|------------|
| `H1Characterization/LinearComplexity.lean` | 123 | `acyclic_implies_euler` |
| `H1Characterization/LinearComplexity.lean` | 143 | `euler_implies_acyclic` |
| `Infrastructure/AxiomElimination.lean` | 150 | `stability_of_h1_trivial_aux` |
| `Infrastructure/GameTheoryBridge.lean` | 29 | `convex_marginal_sum_ge` |
| `Infrastructure/GraphComposition.lean` | 439 | `forest_single_edge_still_forest_aux` |
| `MultiAgent/CoalitionH2.lean` | 107 | `h1_trivial_h2_nontrivial_obstruction_aux` |
| `MultiAgent/CoalitionH2.lean` | 131 | `four_agent_h2_forward` |
| `MultiAgent/CoalitionH2.lean` | 140 | `four_agent_h2_backward` |
| `MultiAgent/CoalitionH2.lean` | 84 | `h1_h2_trivial_grand_coalition_aux` |
| `MultiAgent/GameTheoreticH1.lean` | 274 | `StrategicGame.actions_nonempty` |
| `MultiAgent/GameTheoreticH1.lean` | 286 | `StrategicGame.coordination_nash_player_bound` |
| `MultiAgent/GlobalLocalDuality.lean` | 381 | `nontrivial_compatible_has_gap` |
| `MultiAgent/HierarchicalNetwork.lean` | 169 | `path_compatible_aux` |
| `MultiAgent/MechanismDesign.lean` | 307 | `h1_zero_local_global_ic` |
| `MultiAgent/TreeAuthSimpleGraph.lean` | 298 | `toSimpleGraph_acyclic_aux` |
| `MultiAgent/TreeAuthSimpleGraph.lean` | 94 | `depth_parent_fuel_analysis` |
| `MultiAgent/TreeAuthorityAcyclicity.lean` | 43 | `path_to_root_unique_aux` |
| `MultiAgent/TreeAuthorityAcyclicity.lean` | 454 | `no_cycle_bookkeeping` |
| `MultiAgent/TreeAuthorityH1.lean` | 232 | `hierarchyComplex_acyclic_aux` |
| `MultiAgent/TreeAuthorityH1.lean` | 314 | `alignment_path_compatible` |
| `MultiAgent/TreeComposition.lean` | 50 | `subtree_partition_aux` |
| `MultiAgent/TreeComposition.lean` | 88 | `compose_acyclic_h2_aux` |
| `Perspective/AgentCoordination.lean` | 622 | `composition_deadlock_example_aux` |
| `Perspective/AlignmentEquivalence.lean` | 928 | `complete_complex_coboundary_aux'` |
| `Perspective/Bifurcation.lean` | 170 | `safety_margin_aux` |
| `Perspective/Bifurcation.lean` | 240 | `bifurcation_catastrophic_aux` |
| `Perspective/Compositional.lean` | 149 | `forest_single_edge_composition_axiom_aux` |
| `Perspective/Compositional.lean` | 244 | `general_acyclic_composition_axiom_aux` |
| `Perspective/Compositional.lean` | 353 | `large_disagreement_breaks_alignment_aux` |
| `Perspective/ConflictLocalization.lean` | 182 | `minimal_conflict_exists_aux` |
| `Perspective/ConflictLocalization.lean` | 43 | `forms_cycle_from_global_failure` |
| `Perspective/ConflictResolution.lean` | 163 | `remove_edge_from_single_cycle_aux'` |
| `Perspective/ConflictResolution.lean` | 196 | `fill_triangle_h1_trivial_aux'` |
| `Perspective/ConflictResolution.lean` | 217 | `resolution_edge_exists_maximal_aux` |
| `Perspective/CriticalPoints.lean` | 276 | `uniform_misalignment_zero_ax` |
| `Perspective/CriticalPoints.lean` | 350 | `saddle_has_escape_ax` |
| `Perspective/CriticalPoints.lean` | 98 | `misalignment_zero_implies_aligned_ax` |
| `Perspective/Curvature.lean` | 187 | `h1_trivial_implies_bounded_disagreement_ax` |
| `Perspective/Curvature.lean` | 341 | `barrier_implies_high_curvature_ax` |
| `Perspective/Curvature.lean` | 373 | `low_curvature_implies_no_barrier_ax` |
| `Perspective/DimensionBound.lean` | 308 | `h1_dim_components_bound` |
| `Perspective/EntropyProduction.lean` | 222 | `lower_production_lower_cost_aux` |
| `Perspective/EscapeTime.lean` | 135 | `escape_time_finite_ax` |
| `Perspective/EscapeTime.lean` | 177 | `escape_time_monotone_ax` |
| `Perspective/EscapeTime.lean` | 296 | `escape_time_bounded_ax` |
| `Perspective/FairRepair.lean` | 175 | `optimal_repair_exists` |
| `Perspective/FairnessDynamics.lean` | 273 | `negative_lyapunov_stable_ax` |
| `Perspective/FairnessFoundations.lean` | 184 | `h1_trivial_implies_fair_allocation` |
| `Perspective/FairnessFoundations.lean` | 195 | `fair_allocation_implies_h1_trivial` |
| `Perspective/FairnessLearning.lean` | 169 | `fairness_loss_bounded` |
| `Perspective/HierarchicalAlignment.lean` | 151 | `hierarchical_decomposition_aux` |
| `Perspective/IndividualFairness.lean` | 212 | `optimal_lipschitz_achieves` |
| `Perspective/InformationBound.lean` | 190 | `alignment_requires_information_aux` |
| `Perspective/MayerVietoris.lean` | 120 | `simple_mayer_vietoris` |
| `Perspective/OptimalRepair.lean` | 156 | `aligned_implies_H1_trivial` |
| `Perspective/OptimalRepair.lean` | 376 | `optimal_repair_exists_ax` |
| `Perspective/SpectralGap.lean` | 135 | `laplacianExists` |
| `Perspective/SpectralGap.lean` | 181 | `laplacianEigenvalues` |
| `Perspective/SpectralGap.lean` | 215 | `eigenvalues_nonneg` |
| `Perspective/SpectralGap.lean` | 551 | `spectral_gap_bounded_aux` |
| `Perspective/SpectralGap.lean` | 84 | `vertexDegreeAx` |
| `Perspective/Stability.lean` | 104 | `stability_of_h1_trivial_aux` |
| `Perspective/Stability.lean` | 113 | `measurement_robustness_aux` |
| `Theories/BridgeComponentTheory.lean` | 171 | `bridge_path_decomposition` |
| `Theories/BridgeComponentTheory.lean` | 177 | `non_v_component_path_avoids_bridge` |
| `Theories/BridgeComponentTheory.lean` | 183 | `bridge_component_cardinality` |
| `Theories/CoalitionGameCore.lean` | 178 | `marginal_sum_telescope_aux` |
| `Theories/CoalitionGameCore.lean` | 61 | `supermodular_of_convex` |
| `Theories/H2Characterization.lean` | 74 | `h2_small_complex_aux` |
| `Theories/H2Characterization.lean` | 81 | `filled_tetrahedron_coboundary` |
| `Theories/H2Characterization.lean` | 87 | `hollow_tetrahedron_no_primitive` |
| `Theories/HierarchicalNetworkComplete.lean` | 136 | `compose_path_reaches_root` |
| `Theories/HierarchicalNetworkComplete.lean` | 182 | `acyclic_periodic_orbit_equiv` |
| `Theories/HierarchicalNetworkComplete.lean` | 188 | `pathToRoot_consecutive_adjacent` |

## Files with Most Axioms

- `Perspective/SpectralGap.lean`: 5 axioms
- `MultiAgent/CoalitionH2.lean`: 4 axioms
- `Theories/HierarchicalNetworkComplete.lean`: 3 axioms
- `Theories/H2Characterization.lean`: 3 axioms
- `Theories/BridgeComponentTheory.lean`: 3 axioms
- `Perspective/EscapeTime.lean`: 3 axioms
- `Perspective/Curvature.lean`: 3 axioms
- `Perspective/CriticalPoints.lean`: 3 axioms
- `Perspective/ConflictResolution.lean`: 3 axioms
- `Perspective/Compositional.lean`: 3 axioms

## Quick Actions

Run these commands to work with axioms:

```bash
# Count axioms
make axiom-count

# Regenerate this report
make axiom-report

# List axioms in a specific file
grep -n "^axiom " Perspective/SpectralGap.lean

# Find usages of an axiom
grep -rln "axiom_name" . --include="*.lean" | grep -v .lake
```

## Notes

- Axioms marked with `-- KEEP` are external math results (spectral theory, etc.)
- See `.claude/axiom-registry.md` for full signatures and elimination status
- Priority: self-contained files with Mathlib-only imports
