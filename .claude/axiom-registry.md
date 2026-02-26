# Axiom Registry

> Last updated: 2026-02-06 (session 30 — eliminated 2 axioms, 18 remaining)

## Current State Summary

| Status | Count | Description |
|--------|-------|-------------|
| **In Codebase** | **18** | Total `axiom` keyword declarations |
| True trivializations remaining | ~9 | Acceptable tautologies / economics meta-theorems |
| **SORRIES** | 0 | All sorries eliminated |

> **Session 30 Progress (2026-02-06):**
> - **Eliminated 2 axioms** (20 → 18):
>   - `remove_vertex_resolves_ax` → `remove_vertex_resolves` (constructive: `K.removeVertex v`)
>   - `remove_edge_breaks_cycle_ax` → `remove_edge_breaks_cycle` (`K.removeEdge e` + excluded middle)
> - Created `MultiAgent/Protocol.lean` (17 theorems, 0 axioms)
> - Created `MultiAgent/DynamicNetwork.lean` (16 theorems, 0 axioms)
> - Build: clean (3175 jobs, 0 errors)
>
> **Session 28 Progress (2026-02-06):**
> - **Eliminated 7 axioms** (27 → 20):
>   - 2 **redundant** with existing theorems: `distant_connection_best_ax` (= `spectralGap_nonneg`), `curvature_decreases_toward_alignment_ax` (= `aligned_zero_curvature`)
>   - 2 **trivially true by definition**: `deadlock_detection_reduces_to_h1_ax` (`Iff.rfl`), `spectral_gap_h1_connection_ax` (0 ≤ n)
>   - 3 **mathematically false** given placeholder defs: `cycle_implies_h1_nontrivial_ax`, `bottleneck_limits_gap_ax`, `redundancy_speeds_convergence_ax`
> - Build: clean (3175 jobs, 0 errors)

---

## Axiom Inventory (18 total)

### Perspective/CriticalPoints.lean (6 axioms)

| # | Axiom | Line | Mathematical Statement |
|---|-------|------|----------------------|
| 1 | `local_not_global_exists_ax` | 450 | ∃ systems with local min that isn't global min (n≥3) |
| 2 | `saddle_has_escape_ax` | 489 | Saddle point ⇒ escape direction exists |
| 3 | `escape_decreases_misalignment_ax` | 515 | Stepping along escape direction decreases misalignment |
| 4 | `escape_trap_requires_perturbation_ax` | 556 | Escaping trap requires perturbation ≥ basinRadius |
| 5 | `morse_inequality_ax` | 583 | localMinima + localMaxima ≥ saddlePoints |
| 6 | `random_perturbation_escapes_ax` | 623 | Non-global-min ⇒ ∃ perturbation lowering misalignment |

### Perspective/Curvature.lean (3 axioms)

| # | Axiom | Line | Mathematical Statement |
|---|-------|------|----------------------|
| 7 | `small_steps_safe_ax` | 261 | Step ≤ 1/(2κ) doesn't overshoot |
| 8 | `large_steps_can_fail_ax` | 274 | ∃ config where large step increases distance |
| 9 | `curvature_continuous_ax` | 525 | Close points have close curvature values |

> `curvature_decreases_toward_alignment_ax` → proved as theorem (same proof as `aligned_zero_curvature`)

### Perspective/SpectralGap.lean (0 axioms)

> All 4 axioms eliminated in session 28:
> - `distant_connection_best_ax` → redundant with `spectralGap_nonneg`
> - `bottleneck_limits_gap_ax` → false (placeholder eigenvalues always 0)
> - `spectral_gap_h1_connection_ax` → proved as theorem (0 ≤ n)
> - `redundancy_speeds_convergence_ax` → false (placeholder convergence = 1000000)

### Perspective/DimensionBound.lean (3 axioms)

| # | Axiom | Line | Mathematical Statement |
|---|-------|------|----------------------|
| 15 | `add_edge_dimension_change_ax` | 416 | h1Dim(K') ≤ h1Dim(K) + 1 (after adding edge) |
| 16 | `remove_edge_dimension_change_ax` | 432 | h1Dim(K') ≥ h1Dim(K) - 1 (after removing edge) |
| 17 | `dimension_changes_gradual_ax` | 447 | Single edge op changes dim by at most 1 |

### Perspective/AgentCoordination.lean (1 axiom)

| # | Axiom | Line | Mathematical Statement |
|---|-------|------|----------------------|
| 13 | `hub_preserves_deadlock_free_ax` | 686 | Hub addition preserves deadlock-freedom |

> `deadlock_detection_reduces_to_h1_ax` → proved as theorem (`Iff.rfl` — definitional equality)

### Perspective/AttractorBasins.lean (2 axioms)

| # | Axiom | Line | Mathematical Statement |
|---|-------|------|----------------------|
| 20 | `unique_basin_ax` | 203 | Point is in exactly one attractor basin |
| 21 | `small_perturbation_stays_ax` | 292 | Small perturbation stays in basin |

### Perspective/ConflictResolution.lean (0 axioms)

> Both axioms eliminated in session 30:
> - `remove_edge_breaks_cycle_ax` → `remove_edge_breaks_cycle` (theorem, `K.removeEdge e` + LEM)
> - `remove_vertex_resolves_ax` → `remove_vertex_resolves` (theorem, `K.removeVertex v` constructive)

### Perspective/Barrier.lean (1 axiom)

| # | Axiom | Line | Mathematical Statement |
|---|-------|------|----------------------|
| 24 | `barrier_always_resolvable_ax` | 653 | Every barrier has a resolution (≤ n changes) |

### Perspective/OptimalRepair.lean (1 axiom)

| # | Axiom | Line | Mathematical Statement |
|---|-------|------|----------------------|
| 25 | `incremental_repair_converges_ax` | 948 | ∃ repair plan achieving alignment |

### Perspective/Persistence.lean (1 axiom)

| # | Axiom | Line | Mathematical Statement |
|---|-------|------|----------------------|
| 26 | `no_structural_implies_some_aligned_ax` | 338 | No persistent conflict ⇒ ∃ ε with alignment |

### MultiAgent/AgentNetworks.lean (0 axioms)

> `cycle_implies_h1_nontrivial_ax` → deleted (mathematically false: isForest = isTrivial, counterexample: 2 incompatible agents)

---

## Axiom Count by Directory

```
Perspective/           18  (CriticalPoints:6, Curvature:3, DimensionBound:3,
                            AttractorBasins:2, ConflictResolution:0,
                            AgentCoordination:1, Barrier:1, OptimalRepair:1, Persistence:1)
MultiAgent/             0
Infrastructure/         0
Foundations/            0
H1Characterization/     0
────────────────────────
TOTAL                  18
```

> Last verified: 2026-02-06 (session 30 — `make axiom-count`)

---

## Remaining True Trivializations (~9, acceptable)

These are intentionally kept as-is (skip list):

| File | Theorem | Why Acceptable |
|------|---------|----------------|
| ConflictLocalization.lean:83 | `conflict_witness_exists` | `∃ w : ConflictWitness, True` — meaningful existence |
| ConflictLocalization.lean:132 | `alignment_conflict_localization` | `∃ conflict, True` — meaningful existence |
| TreeAuthorityAcyclicity.lean:740 | `no_cycle_in_tree` | `¬∃ c : Cycle, True` — proper proof (no cycle inhabitants) |
| TreeAuthorityAcyclicity.lean:754 | tree acyclicity variant | Same pattern as above |
| Geodesic.lean:239 | `straightLine_is_geodesic` | Tautological sketch |
| MechanismDesign.lean:181 | `revelation_principle` | Economics meta-theorem placeholder |
| MechanismDesign.lean:231 | `myerson_satterthwaite` | Economics meta-theorem placeholder |
| MechanismDesignProofs.lean:209 | `revenue_equivalence_from_h1` | Economics meta-theorem |
| StrategicCoordination.lean:142 | `feasible_implies_possible` | Economics meta-theorem |

---

## Why Not Proven (Classification of remaining 18)

| Category | Count | Examples |
|----------|-------|---------|
| Needs Morse/critical point theory | 6 | All CriticalPoints axioms |
| Needs graph component counting | 3 | DimensionBound edge change axioms |
| Needs Riemannian geometry | 3 | Curvature step size + continuity |
| Needs dynamical systems | 3 | AttractorBasins, Barrier |
| Needs convergence/coordination theory | 2 | hub_preserves, incremental_repair |
| Needs persistence diagrams | 1 | no_structural_implies_some_aligned |

---

## Historical: Session 27 Changes

### Deleted (12 novelty claims)
All theorems of form `novelty_claim_X : True := trivial` removed from:
CriticalPoints, Curvature, SpectralGap, DimensionBound, AttractorBasins,
Bifurcation, Barrier, EscapeTime, FairnessLearning, FairnessFoundations,
OptimalRepair, Geodesic

### Upgraded to Level 2 (26 trivializations → axioms)
All former `theorem X : True := trivial` converted to `axiom X_ax : <real statement>`

### Simplified (2 theorems)
- `memory_theorems_transfer`: Removed `True` third conjunct
- `one_engine_two_products`: Removed `True ∧ True`, kept real biconditional

### Previous Sessions
See git history for sessions 1-26.
