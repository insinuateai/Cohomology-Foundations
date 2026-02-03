# Axiom Signature Registry

> **Quick reference**: See `axiom-status.md` (~50 lines) for session startup.
> **Full signatures**: Below, or `axiom-signatures.md` for commonly-needed ones.
> **Citations**: See `axiom-justifications.md` for publication-ready references.
> Last updated: 2026-02-03

## Quick Reference

| Status | Count | Description |
|--------|-------|-------------|
| KEEP | ~19 | External math, structural assumptions, multi-cycle issues |
| ELIMINATED | 16 | G01-G06, C03, C04, X03, X04, X22, X26, X28, X29, F07, T02 |
| ELIMINATE | ~33 | Provable from current Mathlib |

## By Priority (Recommended Elimination Order)

### Priority 1: Graph Theory (Mathlib infrastructure exists)

| ID | Axiom | File:Line | Notes |
|----|-------|-----------|-------|
| G01 | `forest_single_edge_still_forest_aux` | ~~GraphComposition.lean:439~~ | **ELIMINATED** - WalkDecomposition.lean |
| G02 | `acyclic_implies_euler` | ~~LinearComplexity.lean:123~~ | **ELIMINATED** - SimplicialGraphBridge.lean |
| G03 | `euler_implies_acyclic` | ~~LinearComplexity.lean:143~~ | **ELIMINATED** - SimplicialGraphBridge.lean |
| G04 | `bridge_path_decomposition` | ~~BridgeComponentTheory.lean:171~~ | **ELIMINATED** - PathDecompositionComplete.lean |
| G05 | `non_v_component_path_avoids_bridge` | ~~BridgeComponentTheory.lean:177~~ | **ELIMINATED** - PathDecompositionComplete.lean |
| G06 | `bridge_component_cardinality` | ~~BridgeComponentTheory.lean:183~~ | **ELIMINATED** - ExtendedGraphInfra.lean |

### Priority 2: Tree Authority (Self-contained, Mathlib-only deps)

| ID | Axiom | File:Line | Notes |
|----|-------|-----------|-------|
| T01 | `depth_parent_fuel_analysis` | TreeAuthSimpleGraph.lean:94 | Prove via Nat.find |
| T02 | `toSimpleGraph_acyclic_aux` | ~~TreeAuthSimpleGraph.lean:429~~ | **ELIMINATED** - Inlined type bridge to TreeAuthCoreProofs |
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
| F07 | `optimal_lipschitz_achieves` | ~~IndividualFairness.lean:212~~ | **ELIMINATED** - FairnessH1Proofs.lean |

### Priority 4: Cohomology Core

| ID | Axiom | File:Line | Notes |
|----|-------|-----------|-------|
| C01 | `forms_cycle_from_global_failure` | ConflictLocalization.lean:43 | H1 definition work |
| C02 | `minimal_conflict_exists_aux` | ConflictLocalization.lean:182 | Minimal obstruction |
| C03 | `complete_complex_coboundary_aux'` | ~~AlignmentEquivalence.lean:928~~ | **ELIMINATED** - CompleteComplexH1.lean |
| C04 | `aligned_implies_H1_trivial` | ~~OptimalRepair.lean:156~~ | **ELIMINATED** - CriticalPointsCore.lean |
| C05 | `h1_dim_components_bound` | DimensionBound.lean:308 | Dimension counting |
| C06 | `hierarchical_decomposition_aux` | HierarchicalAlignment.lean:151 | Hierarchy structure |

### ~~Priority 5: Conflict Resolution~~ → KEEP (Multi-Cycle Issues)

| ID | Axiom | File:Line | Notes |
|----|-------|-----------|-------|
| R01 | `remove_edge_from_single_cycle_aux'` | ConflictResolution.lean:163 | **KEEP** - False for multi-cycle complexes |
| R02 | `fill_triangle_h1_trivial_aux'` | ConflictResolution.lean:196 | **KEEP** - False for multi-cycle complexes |
| R03 | `resolution_edge_exists_maximal_aux` | ConflictResolution.lean:217 | **KEEP** - False for multi-cycle complexes |

**Why KEEP**: These axioms claim one operation (edge removal/triangle fill) makes H¹=0. This is false when multiple independent cycles exist. Counterexample: two disjoint hollow triangles. See `.claude/axiom-justifications.md` for details.

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

### H2 Characterization (Higher cohomology)

| ID | Axiom | File:Line | Reason |
|----|-------|-----------|--------|
| K11 | `h2_small_complex_aux` | ~~H2Characterization.lean:74~~ | **ELIMINATED** - Proved directly using root vertex method |
| K12 | `filled_tetrahedron_coboundary` | H2Characterization.lean:277 | 3-simplex analysis (needs explicit 4-vertex linear algebra) |
| K13 | `hollow_tetrahedron_h2_nontrivial_ax` | H2Characterization.lean:285 | H² ≠ 0 (proof exists in HollowTetrahedron.lean, needs type bridge) |
| K14 | `h1_h2_trivial_grand_coalition_aux` | CoalitionH2.lean:84 | H1+H2 interaction |
| K15 | `h1_trivial_h2_nontrivial_obstruction_aux` | CoalitionH2.lean:107 | Obstruction theory |

### KEEP: Structural Assumptions (Type System Limitations)

| ID | Axiom | File:Line | Reason |
|----|-------|-----------|--------|
| X25 | `StrategicGame.actions_nonempty` | GameTheoreticH1.lean:274 | Type allows empty action sets |
| X26 | `StrategicGame.coordination_nash_player_bound` | ~~GameTheoreticH1.lean:286~~ | **ELIMINATED** - GameStrategicProofs.lean |

**Why KEEP X25**: X25 is unprovable because `StrategicGame.actions : Agent → Finset ℕ` allows empty sets.

**X26 ELIMINATED** (2026-02-03): Proven via `coordination_nash_player_bound_proof` in Infrastructure/GameStrategicProofs.lean. The proof uses `nash_implies_h1_trivial`: Nash + coordination → forest ∨ ≤2 players. Forest implies ≤1 player, both contradict >2 players.

**Integration Note (2026-02-03)**: The axiom cannot be directly replaced in GameTheoreticH1.lean due to circular dependency (GameStrategicProofs imports GameTheoreticH1). Downstream users should import GameStrategicProofs and use the proven theorem instead.

**G04/G05/G06 Integration Note** (2026-02-03): BridgeComponentTheory.lean has pre-existing build errors unrelated to axioms. Proven replacements exist in Infrastructure/ files but cannot be integrated until the file's build errors are fixed.

### Remaining (Uncategorized)

| ID | Axiom | File:Line |
|----|-------|-----------|
| X01 | `optimal_repair_exists_ax` | OptimalRepair.lean:376 |
| X02 | `optimal_repair_exists` | FairRepair.lean:175 |
| X03 | `misalignment_zero_implies_aligned_ax` | ~~CriticalPoints.lean:98~~ | **ELIMINATED** - CriticalPointsCore.lean |
| X04 | `uniform_misalignment_zero_ax` | ~~CriticalPoints.lean:276~~ | **ELIMINATED** - CriticalPointsCore.lean |
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
| X22 | `subtree_partition_aux` | ~~TreeComposition.lean:50~~ | **ELIMINATED** - TreeComposition.lean (fullSubtree construction) |
| X23 | `compose_acyclic_h2_aux` | TreeComposition.lean:88 |
| X24 | `h1_zero_local_global_ic` | MechanismDesign.lean:307 |
| X25 | `StrategicGame.actions_nonempty` | ~~GameTheoreticH1.lean:274~~ | **KEEP** - Structural assumption |
| X26 | `StrategicGame.coordination_nash_player_bound` | ~~GameTheoreticH1.lean:286~~ | **ELIMINATED** - GameStrategicProofs.lean |
| X27 | `compose_path_reaches_root` | HierarchicalNetworkComplete.lean:136 |
| X28 | `acyclic_periodic_orbit_equiv` | ~~HierarchicalNetworkComplete.lean:182~~ | **ELIMINATED** - TreeAuthCoreProofs.lean |
| X29 | `pathToRoot_consecutive_adjacent` | ~~HierarchicalNetworkComplete.lean:188~~ | **ELIMINATED** - was duplicate of proven theorem |

---

## Full Signatures (Key Axioms)

### G01: forest_single_edge_still_forest_aux — **ELIMINATED**

```lean
-- ELIMINATED 2026-02-02 via Infrastructure/WalkDecomposition.lean
-- Original axiom replaced with proven theorem:
theorem forest_single_edge_still_forest (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (u v : V) (h_neq : u ≠ v) (h_not_reach : ¬G.Reachable u v) :
    (G ⊔ fromEdgeSet {s(u, v)}).IsAcyclic
```

**Resolution**: Proved using walk decomposition (`takeUntil`/`dropUntil`) and the "long way around" theorem for cycles.

---

### G02: acyclic_implies_euler — **ELIMINATED**

```lean
-- ELIMINATED 2026-02-02 via Infrastructure/SimplicialGraphBridge.lean
-- Original axiom replaced with proven theorem:
theorem acyclic_implies_euler (K : SimplicialComplex)
    [Fintype K.vertexSet] [Fintype (K.ksimplices 1)]
    [DecidableEq K.vertexSet] [DecidableRel (oneSkeleton K).Adj]
    [Fintype (oneSkeleton K).edgeSet] [Fintype (oneSkeleton K).ConnectedComponent]
    [Nonempty K.vertexSet]
    (h : OneConnected K) : EulerForestCondition K
```

**Resolution**: Proved via `SimplicialGraphBridge.acyclic_implies_euler_proven` which:
1. Uses bijection between K.ksimplices 1 and (oneSkeleton K).edgeSet
2. Applies `ForestEulerFormula.acyclic_euler_eq`: |E| + |C| = |V| for forests
3. Converts to inequality |E| ≤ |V| - |C|

---

### G03: euler_implies_acyclic — **ELIMINATED**

```lean
-- ELIMINATED 2026-02-02 via Infrastructure/SimplicialGraphBridge.lean
-- Original axiom replaced with proven theorem:
theorem euler_implies_acyclic (K : SimplicialComplex)
    [Fintype K.vertexSet] [Fintype (K.ksimplices 1)]
    [DecidableEq K.vertexSet] [DecidableRel (oneSkeleton K).Adj]
    [Fintype (oneSkeleton K).edgeSet] [Fintype (oneSkeleton K).ConnectedComponent]
    [Nonempty K.vertexSet]
    (h : EulerForestCondition K) : OneConnected K
```

**Resolution**: Proved via `SimplicialGraphBridge.euler_implies_acyclic_proven` which:
1. Uses bijection to convert ksimplex count to edge count
2. Applies `ForestEulerFormula.euler_eq_implies_acyclic`
3. Uses surjectivity of connectedComponentMk to show |C| ≤ |V|
4. Combined with |E| ≤ |V| - |C| gives |E| + |C| = |V|, hence acyclic

---

### C03: complete_complex_coboundary_aux' — **ELIMINATED**

```lean
-- ELIMINATED 2026-02-02 via Infrastructure/CompleteComplexH1.lean
-- Moved valueComplex to ValueComplex.lean to break circular dependency
theorem complete_complex_coboundary_aux' {S' : Type*} [Fintype S'] [DecidableEq S']
    {n : ℕ} (systems : Fin n → ValueSystem S') (ε : ℚ)
    (f : Cochain (valueComplex systems ε) 1)
    (hf : IsCocycle (valueComplex systems ε) 1 f)
    (h_complete : ∀ (i j : ℕ) (hi : i < n) (hj : j < n), i < j →
      ∃ s : S', |(systems ⟨i, hi⟩).values s - (systems ⟨j, hj⟩).values s| ≤ 2 * ε) :
    IsCoboundary (valueComplex systems ε) 1 f
```

**Resolution**: The root vertex method proof in Infrastructure/CompleteComplexH1.lean:
1. Pick vertex 0 as root
2. Define g({0}) = 0, g({v}) = f({0,v}) for v > 0
3. Cocycle condition on triangles {0,u,v} ensures δg = f

**Module reorganization**: Moved `valueComplex` from AlignmentEquivalence.lean to ValueComplex.lean to break circular dependency. Now CompleteComplexH1 imports ValueComplex, and AlignmentEquivalence imports CompleteComplexH1.

---

### X28: acyclic_periodic_orbit_equiv — **ELIMINATED**

```lean
-- ELIMINATED 2026-02-02 via Infrastructure/TreeAuthCoreProofs.lean
-- Original axiom was UNPROVABLE (RHS false for root node: parentOrRoot root = root)
-- Fixed statement adds i ≠ T.root restriction:
theorem acyclic_periodic_orbit_equiv (T : TreeAuth n) :
    (∀ i, ∃ k, T.parentOrRoot^[k] i = T.root) ↔
    ∀ i, i ≠ T.root → ∀ k > 0, T.parentOrRoot^[k] i ≠ i
```

**Resolution**: The original axiom's RHS was false because `parentOrRoot root = root` (root is a fixed point). Added `i ≠ T.root →` restriction to RHS. The non-root proof was already complete in the file; only needed to restructure to use the hypothesis from the corrected statement.

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
