# Axiom Registry

> Last updated: 2026-02-04 (corrected tautological claims)

## Current State Summary

| Status | Count | Description |
|--------|-------|-------------|
| **In Codebase** | **41** | Total axiom declarations |
| VERIFIED ELIMINATED | 4 | Proven: misalignment_zero, aligned_H1, escape_time_mono/bounded |
| KEEP | 22 | External math, structural, mathematically false/vacuous |
| **HONEST AXIOMS** | ~12 | Infrastructure "proofs" are tautological (headers now corrected) |
| PENDING | 1 | forest_single_edge_composition (may be provable) |

> ✅ **Corrected (2026-02-04):** Infrastructure file headers now accurately state
> "AXIOMS ELIMINATED: 0" instead of false claims. These axioms remain as honest
> Level 2 assumptions until real proofs with Foundations.H1Trivial are written.
> See [infrastructure-audit.md](infrastructure-audit.md) for details.

---

## KEEP Axioms (22 - Do Not Attempt)

### Structural (1)
- `StrategicGame.actions_nonempty` - Type allows empty action sets

### Mathematically False (8)
- `remove_edge_from_single_cycle_aux'` - False for multi-cycle
- `fill_triangle_h1_trivial_aux'` - False for multi-cycle
- `resolution_edge_exists_maximal_aux` - False for multi-cycle
- `large_disagreement_breaks_alignment_aux` - **Counterexample:** 2 agents who disagree have no edge, but the result is still a forest (H¹=0)
- `general_acyclic_composition_axiom_aux` - **False given interfaceIsAcyclic=True:** Cyclic interfaces can break alignment even with compatible modules
- `h1_trivial_implies_bounded_disagreement_ax` - **Counterexample:** Disconnected forest has H¹=0 but unbounded disagreement between disconnected agents
- `escape_time_finite_ax` - **Counterexample:** misalignment=1000, tolerance=1 → escapeTime=1001 > 1000
- `barrier_implies_high_curvature_ax` - **Vacuously true:** HasBarrier is always false (constant adjusted systems have H¹=0)

### External Math - Spectral (5)
- `vertexDegreeAx`, `laplacianExists`, `laplacianEigenvalues`, `eigenvalues_nonneg`, `spectral_gap_bounded_aux`

### External Math - Persistent Homology (4)
- `stability_of_h1_trivial_aux` (AxiomElimination.lean) - Requires persistence stability theorems
- `stability_of_h1_trivial_aux` (Stability.lean) - **Duplicate of above**
- `measurement_robustness_aux` (Stability.lean)
- `measurement_robustness_aux` (AxiomElimination.lean) - **Duplicate if exists**

### External Math - H² (2)
- `filled_tetrahedron_coboundary`, `hollow_tetrahedron_h2_nontrivial_ax`

---

## VERIFIED REPLACEMENTS (Real proofs)

Axioms with Infrastructure proofs using **real** `Foundations.H1Trivial`:

| Axiom | Replacement File | Status |
|-------|------------------|--------|
| `misalignment_zero_implies_aligned_ax` | CriticalPointsAxiomReplacements.lean | ✅ Eliminated |
| `aligned_implies_H1_trivial` | CriticalPointsCore.lean | ✅ Uses real H1Trivial |

Files using real H1Trivial: CriticalPointsCore.lean, CriticalPointsAxiomReplacements.lean, AxiomElimination.lean, GraphComposition.lean, H1BridgeProofs.lean

---

## HONEST AXIOMS (Level 2 - Infrastructure files corrected)

These axioms remain as honest assumptions. The Infrastructure files that claimed to
"eliminate" them have been corrected to state "AXIOMS ELIMINATED: 0".

**Why these are better as honest axioms than tautological "proofs":**
- Level 2 (honest axiom) > Level 1 (trivialized with H1Trivial := True)
- The mathematical statements are meaningful
- Future work can provide real proofs with Foundations.H1Trivial

| Axiom | Infrastructure File | Status |
|-------|---------------------|--------|
| `saddle_has_escape_ax` | CriticalPointsProofs.lean | Header corrected ✅ |
| `h1_trivial_implies_fair_allocation` | FairnessAllocationProofs.lean | Header corrected ✅ |
| `negative_lyapunov_stable_ax` | LyapunovProofs.lean | Header corrected ✅ |
| `forms_cycle_from_global_failure` | ConflictLocalizationProofs.lean | Header corrected ✅ |
| `minimal_conflict_exists_aux` | MinimalConflictProofs.lean | Header corrected ✅ |
| `h1_zero_local_global_ic` | MechanismDesignProofs.lean | Header corrected ✅ |
| `simple_mayer_vietoris` | MayerVietorisProofs.lean | Header corrected ✅ |
| `lower_production_lower_cost_aux` | EntropyProofs.lean | Header corrected ✅ |
| `hierarchical_decomposition_aux` | HierarchicalAlignmentProofs.lean | Header corrected ✅ |
| `optimal_repair_exists_ax` | OptimalRepairProofs.lean | Header corrected ✅ |
| `h1_h2_trivial_grand_coalition_aux` | CoalitionH2Proofs.lean | Needs H² infrastructure |
| `four_agent_h2_forward/backward` | CoalitionH2Proofs.lean | Needs H² infrastructure |

**KEEP (math false):** `h1_trivial_implies_bounded_disagreement_ax`, `barrier_implies_high_curvature_ax`

**Future work:** Write proofs using `Foundations.H1Trivial (valueComplex ...)` following
the pattern in `FairnessAllocationRealProofs.lean`.

---

## PENDING (1 axiom - Potentially Provable)

### Compositional (1) - Requires Flag Complex Mayer-Vietoris
- `forest_single_edge_composition_axiom_aux` - **Mathematically sound**: Forest ∪ Forest ∪ {≤1 edge} = Forest

**Proof approach:** Requires showing:
1. H1Trivial for flag complexes implies acyclic 1-skeleton (or similar)
2. Acyclicity preserved under ≤1 edge addition (Infrastructure/GraphComposition.lean has this)
3. Connection to valueComplex structure

### Eliminated Last Session (2)
- `escape_time_monotone_ax` → `escape_time_monotone_proven` ✅
- `escape_time_bounded_ax` → `escape_time_bounded_proven` ✅

**Moved to KEEP:**
- `escape_time_finite_ax` - Math false (counterexample in handoff)
- `general_acyclic_composition_axiom_aux` - False given `interfaceIsAcyclic = True`
- `large_disagreement_breaks_alignment_aux` - Has counterexample

---

## Axiom Count by Directory

```
Perspective/          28
MultiAgent/           11
Theories/              2
Infrastructure/        0 (1 pending removal)
TOTAL                 41
```
