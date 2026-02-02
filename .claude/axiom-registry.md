# Axiom Signature Registry

> Authoritative source of axiom declarations. Compare FULL signatures before elimination.
> See `.claude/axiom-justifications.md` for publication-ready citations.
> Last updated: 2026-02-01

## Quick Reference

| Status | Count | Description |
|--------|-------|-------------|
| KEEP | ~15 | External math requiring Mathlib extensions |
| ELIMINATE | ~59 | Provable from current Mathlib |

## By Priority (Recommended Elimination Order)

### Priority 1: Graph Theory (Mathlib infrastructure exists)

| ID | Axiom | File:Line | Notes |
|----|-------|-----------|-------|
| G01 | `forest_single_edge_still_forest_aux` | GraphComposition.lean:439 | Use `IsAcyclic.deleteEdges` |
| G02 | `acyclic_implies_euler` | LinearComplexity.lean:123 | Euler formula for forests |
| G03 | `euler_implies_acyclic` | LinearComplexity.lean:143 | Converse of G02 |
| G04 | `bridge_path_decomposition` | BridgeComponentTheory.lean:171 | Path through bridge |
| G05 | `non_v_component_path_avoids_bridge` | BridgeComponentTheory.lean:177 | Component separation |
| G06 | `bridge_component_cardinality` | BridgeComponentTheory.lean:183 | Component counting |

### Priority 2: Tree Authority (Self-contained, Mathlib-only deps)

| ID | Axiom | File:Line | Notes |
|----|-------|-----------|-------|
| T01 | `depth_parent_fuel_analysis` | TreeAuthSimpleGraph.lean:94 | Prove via Nat.find |
| T02 | `toSimpleGraph_acyclic_aux` | TreeAuthSimpleGraph.lean:298 | Use depth argument |
| T03 | `path_to_root_unique_aux` | TreeAuthorityAcyclicity.lean:43 | Induction on depth |
| T04 | `no_cycle_bookkeeping` | TreeAuthorityAcyclicity.lean:454 | Finset.argmin approach |
| T05 | `hierarchyComplex_acyclic_aux` | TreeAuthorityH1.lean:232 | Follows from T02 |
| T06 | `alignment_path_compatible` | TreeAuthorityH1.lean:314 | Path compatibility |
| T07 | `path_compatible_aux` | HierarchicalNetwork.lean:169 | Similar to T06 |

### Priority 3: Fairness/Game Theory (Algebraic, often straightforward)

| ID | Axiom | File:Line | Notes |
|----|-------|-----------|-------|
| F01 | `h1_trivial_implies_fair_allocation` | FairnessFoundations.lean:184 | Unfold H1Trivial |
| F02 | `fair_allocation_implies_h1_trivial` | FairnessFoundations.lean:195 | Converse |
| F03 | `fairness_loss_bounded` | FairnessLearning.lean:169 | Finset.sup' bounds |
| F04 | `convex_marginal_sum_ge` | GameTheoryBridge.lean:29 | Telescope sum |
| F05 | `supermodular_of_convex` | CoalitionGameCore.lean:61 | Definition unfolding |
| F06 | `marginal_sum_telescope_aux` | CoalitionGameCore.lean:178 | List sum manipulation |
| F07 | `optimal_lipschitz_achieves` | IndividualFairness.lean:212 | Existence argument |

### Priority 4: Cohomology Core

| ID | Axiom | File:Line | Notes |
|----|-------|-----------|-------|
| C01 | `forms_cycle_from_global_failure` | ConflictLocalization.lean:43 | H1 definition work |
| C02 | `minimal_conflict_exists_aux` | ConflictLocalization.lean:182 | Minimal obstruction |
| C03 | `complete_complex_coboundary_aux'` | AlignmentEquivalence.lean:928 | Complete graph H1 |
| C04 | `aligned_implies_H1_trivial` | OptimalRepair.lean:156 | Forward direction |
| C05 | `h1_dim_components_bound` | DimensionBound.lean:308 | Dimension counting |
| C06 | `hierarchical_decomposition_aux` | HierarchicalAlignment.lean:151 | Hierarchy structure |

### Priority 5: Conflict Resolution

| ID | Axiom | File:Line | Notes |
|----|-------|-----------|-------|
| R01 | `remove_edge_from_single_cycle_aux'` | ConflictResolution.lean:163 | Edge removal |
| R02 | `fill_triangle_h1_trivial_aux'` | ConflictResolution.lean:196 | Triangle filling |
| R03 | `resolution_edge_exists_maximal_aux` | ConflictResolution.lean:217 | Maximal element |

### KEEP: External Math (Spectral Theory)

| ID | Axiom | File:Line | Reason |
|----|-------|-----------|--------|
| K01 | `vertexDegreeAx` | SpectralGap.lean:84 | Spectral theory |
| K02 | `laplacianExists` | SpectralGap.lean:135 | Matrix construction |
| K03 | `laplacianEigenvalues` | SpectralGap.lean:181 | Spectral theorem |
| K04 | `eigenvalues_nonneg` | SpectralGap.lean:215 | Positive semidefinite |
| K05 | `spectral_gap_bounded_aux` | SpectralGap.lean:551 | Gap bound |

### KEEP: External Math (Stability/Dynamics)

| ID | Axiom | File:Line | Reason |
|----|-------|-----------|--------|
| K06 | `stability_of_h1_trivial_aux` | Stability.lean:104 | Persistent homology |
| K07 | `measurement_robustness_aux` | Stability.lean:113 | Lipschitz stability |
| K08 | `safety_margin_aux` | Bifurcation.lean:170 | Bifurcation theory |
| K09 | `bifurcation_catastrophic_aux` | Bifurcation.lean:240 | Catastrophe theory |
| K10 | `negative_lyapunov_stable_ax` | FairnessDynamics.lean:273 | Lyapunov functions |

### KEEP: H2 Characterization (Higher cohomology)

| ID | Axiom | File:Line | Reason |
|----|-------|-----------|--------|
| K11 | `h2_small_complex_aux` | H2Characterization.lean:74 | H2 computation |
| K12 | `filled_tetrahedron_coboundary` | H2Characterization.lean:81 | 3-simplex analysis |
| K13 | `hollow_tetrahedron_no_primitive` | H2Characterization.lean:87 | Non-bounding cycle |
| K14 | `h1_h2_trivial_grand_coalition_aux` | CoalitionH2.lean:84 | H1+H2 interaction |
| K15 | `h1_trivial_h2_nontrivial_obstruction_aux` | CoalitionH2.lean:107 | Obstruction theory |

### Remaining (Uncategorized)

| ID | Axiom | File:Line |
|----|-------|-----------|
| X01 | `optimal_repair_exists_ax` | OptimalRepair.lean:376 |
| X02 | `optimal_repair_exists` | FairRepair.lean:175 |
| X03 | `misalignment_zero_implies_aligned_ax` | CriticalPoints.lean:98 |
| X04 | `uniform_misalignment_zero_ax` | CriticalPoints.lean:276 |
| X05 | `saddle_has_escape_ax` | CriticalPoints.lean:350 |
| X06 | `escape_time_finite_ax` | EscapeTime.lean:135 |
| X07 | `escape_time_monotone_ax` | EscapeTime.lean:177 |
| X08 | `escape_time_bounded_ax` | EscapeTime.lean:296 |
| X09 | `composition_deadlock_example_aux` | AgentCoordination.lean:622 |
| X10 | `information_alignment_requires_aux` | InformationBound.lean:190 |
| X11 | `simple_mayer_vietoris` | MayerVietoris.lean:120 |
| X12 | `h1_trivial_implies_bounded_disagreement_ax` | Curvature.lean:187 |
| X13 | `barrier_implies_high_curvature_ax` | Curvature.lean:341 |
| X14 | `low_curvature_implies_no_barrier_ax` | Curvature.lean:373 |
| X15 | `forest_single_edge_composition_axiom_aux` | Compositional.lean:149 |
| X16 | `general_acyclic_composition_axiom_aux` | Compositional.lean:244 |
| X17 | `large_disagreement_breaks_alignment_aux` | Compositional.lean:353 |
| X18 | `lower_production_lower_cost_aux` | EntropyProduction.lean:222 |
| X19 | `nontrivial_compatible_has_gap` | GlobalLocalDuality.lean:381 |
| X20 | `four_agent_h2_forward` | CoalitionH2.lean:131 |
| X21 | `four_agent_h2_backward` | CoalitionH2.lean:140 |
| X22 | `subtree_partition_aux` | TreeComposition.lean:50 |
| X23 | `compose_acyclic_h2_aux` | TreeComposition.lean:88 |
| X24 | `h1_zero_local_global_ic` | MechanismDesign.lean:307 |
| X25 | `StrategicGame.actions_nonempty` | GameTheoreticH1.lean:274 |
| X26 | `StrategicGame.coordination_nash_player_bound` | GameTheoreticH1.lean:286 |
| X27 | `compose_path_reaches_root` | HierarchicalNetworkComplete.lean:136 |
| X28 | `acyclic_periodic_orbit_equiv` | HierarchicalNetworkComplete.lean:182 |
| X29 | `pathToRoot_consecutive_adjacent` | HierarchicalNetworkComplete.lean:188 |

---

## Full Signatures (Key Axioms)

### G01: forest_single_edge_still_forest_aux

```lean
axiom forest_single_edge_still_forest_aux (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (he : e ∈ G.edgeSet) (hF : G.IsAcyclic) :
    (G.deleteEdges {e}).IsAcyclic
```

**Approach**: Deleting an edge from an acyclic graph preserves acyclicity. Check if `SimpleGraph.IsAcyclic.deleteEdges` exists in Mathlib.

---

### T01: depth_parent_fuel_analysis

```lean
axiom depth_parent_fuel_analysis (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) :
    T.depth i = T.depth p + 1
```

**Approach**: If depth is defined via `Nat.find`, unfold definition and use `hp` to show parent chain is one shorter.

---

### C01: forms_cycle_from_global_failure

```lean
axiom forms_cycle_from_global_failure {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {n : ℕ} (systems : Fin n → ValueSystem S) (ε : ℚ) (_hε : ε > 0) (i : Fin n) (j : Fin n)
    (_h_no_global : ¬∃ R : ValueSystem S, ∀ k : Fin n, Reconciles R (systems k) ε) :
    ∃ s : S, |(systems i).values s - (systems j).values s| ≤ 2 * ε
```

**WARNING**: This signature differs from the theorem in AxiomElimination.lean! The AxiomElim version returns cocycle existence, not pairwise bounds.

---

### K06: stability_of_h1_trivial_aux

```lean
axiom stability_of_h1_trivial_aux {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {n : ℕ} [NeZero n] (systems : Fin n → ValueSystem S) (ε : ℚ) (hε : ε > 0)
    (hK : H1Trivial (valueComplex systems ε))
    (systems' : Fin n → ValueSystem S)
    (h_close : ∀ i s, |(systems' i).values s - (systems i).values s| < ε / 4) :
    H1Trivial (valueComplex systems' ε)
```

**Status**: KEEP - Requires persistent homology stability theorem (Cohen-Steiner et al. 2007)

---

## Signature Mismatch Warning

Same-named declarations across files may have DIFFERENT signatures:

| Axiom Name | Location | Returns |
|------------|----------|---------|
| `forms_cycle_from_global_failure` | ConflictLocalization.lean | Pairwise ε-agreement |
| `forms_cycle_from_global_failure` | AxiomElimination.lean (theorem) | Cocycle existence |

Always check source file signature before elimination attempts.

---

## Update Protocol

When eliminating an axiom:
1. Verify signature matches EXACTLY (parameters, constraints, conclusion)
2. Update status in this file
3. Update session log in skill-document.md
4. Run `make axiom-count` to verify count decreased
