# Infrastructure Proofs Audit

> Audit Date: 2026-02-04 (Updated)

## Summary

| Category | Count | Notes |
|----------|-------|-------|
| **OBSOLETE** | 1 | BifurcationProofs.lean - axioms already eliminated locally |
| **REAL H1Trivial** | 5 | Use `Foundations.H1Trivial` (valueComplex) |
| **SOUND BUT WRONG TYPES** | 4 | Mathematical proofs exist but use local type definitions |
| **TAUTOLOGICAL** | 7 | Returns `True` or H1Trivial defined as conclusion |
| **Total *Proofs.lean** | 32 | |

## Detailed Status

### OBSOLETE (1 file) - Can be deleted

| File | Reason |
|------|--------|
| BifurcationProofs.lean | Axioms `safety_margin_aux`, `bifurcation_catastrophic_aux` already eliminated in Perspective/Bifurcation.lean |

### REAL H1Trivial (5 files) - Working

| File | Uses |
|------|------|
| CriticalPointsCore.lean | `Foundations.H1Trivial (valueComplex ...)` |
| CriticalPointsAxiomReplacements.lean | Exact signature match, delegates to Core |
| AxiomElimination.lean | `H1Trivial (valueComplex ...)` |
| GraphComposition.lean | `H1Trivial (valueComplex ...)` |
| H1BridgeProofs.lean | `H1Trivial (valueComplex ...)` |

### SOUND BUT WRONG TYPES (4 files) - Need type adaptation

| File | Issue | Fix Needed |
|------|-------|------------|
| FairnessAllocationProofs.lean | Uses own FairnessComplex type | Adapt to Perspective.FairnessFoundations types |
| ConflictLocalizationProofs.lean | Has sound logic, wrong types | Adapt to Perspective.ConflictLocalization types |
| MinimalConflictProofs.lean | Has sound logic, wrong types | Adapt to Perspective types |
| OptimalRepairProofs.lean | Has sound logic, wrong types | Adapt to Perspective types |

### TAUTOLOGICAL (7 files) - Need real proofs or deletion

| File | Issue |
|------|-------|
| CurvatureProofs.lean | `H1Trivial` defined as bounded disagreement |
| EntropyProofs.lean | Different function definitions |
| HierarchicalAlignmentProofs.lean | Tautological H1Trivial |
| InformationBoundProofs.lean | Tautological H1Trivial |
| LyapunovProofs.lean | Own type definitions |
| MayerVietorisProofs.lean | Tautological H1Trivial |
| MechanismDesignProofs.lean | Returns `True` |

## Files Using REAL H1Trivial (5)

These files work with the cohomological definition:

1. **CriticalPointsCore.lean** - Uses `Foundations.H1Trivial (valueComplex systems epsilon)`
2. **CriticalPointsAxiomReplacements.lean** - Delegates to CriticalPointsCore, exact signatures
3. **AxiomElimination.lean** - Uses `H1Trivial (valueComplex systems ε)`
4. **GraphComposition.lean** - Uses `H1Trivial (valueComplex ...)`
5. **H1BridgeProofs.lean** - Uses `H1Trivial (valueComplex systems ε)`

**These are candidates for REAL axiom elimination.**

## Files Defining TAUTOLOGICAL H1Trivial (12)

These define `H1Trivial` as bounded disagreement (NOT cohomological):

```lean
def H1Trivial {n : ℕ} (K : ValueComplex n S) [Nonempty S] : Prop :=
  ∀ i j : Fin n, ∀ s : S,
    |(K.systems i).values s - (K.systems j).values s| ≤ 2 * K.epsilon
```

Files:
- BifurcationProofs.lean
- CriticalPointsProofs.lean
- CurvatureProofs.lean
- EntropyProofs.lean
- FairnessAllocationProofs.lean
- HierarchicalAlignmentProofs.lean
- InformationBoundProofs.lean
- MayerVietorisProofs.lean
- MechanismDesignProofs.lean
- MinimalConflictProofs.lean
- OptimalRepairProofs.lean
- StabilityProofs.lean

**These proofs do NOT eliminate the corresponding axioms.**

## Files Importing Perspective (2)

- FairnessH1Proofs.lean
- H1BridgeProofs.lean

## Axiom Status Reassessment

### Genuinely Eliminable (Verified)

| Axiom | Replacement File | Status |
|-------|------------------|--------|
| `misalignment_zero_implies_aligned_ax` | CriticalPointsAxiomReplacements.lean | ✅ Already eliminated |

### Claimed Eliminated But Actually Tautological

| Axiom | Claimed Replacement | Issue |
|-------|---------------------|-------|
| `h1_trivial_implies_bounded_disagreement_ax` | CurvatureProofs.lean | Uses tautological H1Trivial |
| `barrier_implies_high_curvature_ax` | CurvatureProofs.lean | Uses tautological H1Trivial |
| `forms_cycle_from_global_failure` | ConflictLocalizationProofs.lean | Returns `True` |
| `minimal_conflict_exists_aux` | MinimalConflictProofs.lean | Uses tautological H1Trivial |
| `safety_margin_aux` | BifurcationProofs.lean | Uses tautological H1Trivial |
| `bifurcation_catastrophic_aux` | BifurcationProofs.lean | Uses tautological H1Trivial |
| `lower_production_lower_cost_aux` | EntropyProofs.lean | Different function signatures |
| `negative_lyapunov_stable_ax` | LyapunovProofs.lean | Uses own definitions |
| `h1_trivial_implies_fair_allocation` | FairnessAllocationProofs.lean | Uses tautological H1Trivial |
| `simple_mayer_vietoris` | MayerVietorisProofs.lean | Uses tautological H1Trivial |
| `hierarchical_decomposition_aux` | HierarchicalAlignmentProofs.lean | Uses tautological H1Trivial |
| `optimal_repair_exists_ax` | OptimalRepairProofs.lean | Uses tautological H1Trivial |

### KEEP (Not Attemptable)

- SpectralGap (5): External math (Laplacian theory)
- ConflictResolution (3): Mathematically false for multi-cycle
- Stability (2): Persistent homology (external)

### PENDING (No Replacement)

- EscapeTime (3): escape_time_finite_ax, escape_time_monotone_ax, escape_time_bounded_ax
- Compositional (3): forest_single_edge_composition_axiom_aux, general_acyclic_composition_axiom_aux, large_disagreement_breaks_alignment_aux
- AgentCoordination (1): composition_deadlock_example_aux

## Recommendations

1. **Update axiom-registry.md** to reflect accurate status
2. **Do NOT claim "HAS REPLACEMENT"** for axioms with tautological proofs
3. **Focus on REAL elimination** using CriticalPointsCore pattern
4. **PENDING axioms** have honest status - prioritize these
