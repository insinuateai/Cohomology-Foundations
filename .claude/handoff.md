# Agent Handoff Document

> Overwritten each session. Previous versions in git history.
> Read CLAUDE.md and skill-document.md first, then this file.

## Session Metadata

- **Date**: 2026-02-02
- **Primary goal**: Evaluate and integrate AxiomSolver.lean from another branch
- **User intent**: Determine if the file helps eliminate axioms

## What Was Accomplished

### Completed
- [x] Analyzed `Infrastructure/AxiomSolver.lean` from `claude/lean-axiom-solver-TCj6F` branch
- [x] **Deleted AxiomSolver.lean** - Found it was redundant and harmful:
  - Most theorems already proven in GraphComposition.lean
  - Had **7 sorries** violating "0 sorries" goal
  - Key target axiom (G01) wasn't actually eliminated (replacement had sorry)
- [x] Improved G01 axiom documentation with proof strategy

### Analysis Results
| AxiomSolver.lean Content | Status |
|-------------------------|--------|
| `subgraph_acyclic_of_acyclic` | Already in GraphComposition.lean |
| `induce_acyclic_of_acyclic` | Already in GraphComposition.lean |
| `cycle_transfer_to_subgraph` | Already in GraphComposition.lean |
| `forest_union_forest_acyclic` | Already in GraphComposition.lean |
| `acyclic_of_disjoint_acyclic_parts` | Already in GraphComposition.lean |
| `forest_single_edge_still_forest_theorem` | **1 sorry** - incomplete |
| `acyclic_of_disjoint_acyclic_parts_theorem` | **2 sorries** - incomplete |
| `forest_union_forest_acyclic_theorem` | **2 sorries** - incomplete |

### Not Changed
- `forest_single_edge_still_forest_aux` axiom (G01) remains in GraphComposition.lean
  - Proof requires `Walk.support_takeUntil_append_dropUntil` (doesn't exist in Mathlib 4.27.0)
  - Pattern exists in TreeGraphInfra.lean's `takeUntil_first_endpoint_no_edge`

## Key Technical Insights

### G01 Proof Strategy (for future elimination)
```
1. For cycle c using edge s(u,v):
   - Both u, v ∈ c.support
   - By takeUntil_first_endpoint_no_edge, one prefix is clean
2. The "long way around" the cycle gives a path u→v avoiding s(u,v)
3. This path transfers to G, giving G.Reachable u v
4. Contradiction with h_not_reach
```

### Walk Decomposition Lemmas Needed
- `Walk.edges_takeUntil_subset`: edges in takeUntil are subset of original
- Support splitting: showing vertex in either takeUntil or dropUntil
- See TreeGraphInfra.lean lines 60-82 for working `takeUntil_first_endpoint_no_edge`

## Current State

### Files Changed
- `Infrastructure/AxiomSolver.lean` - **DELETED**
- `Infrastructure/GraphComposition.lean` - Improved axiom docstring

### Axiom Status
- G01 (`forest_single_edge_still_forest_aux`) - Still axiom, needs walk decomposition

## Recommended Next Steps

1. Complete G01 elimination by adapting TreeGraphInfra pattern
2. Attack other axiom clusters (see axiom-registry.md)
3. Consider adding missing Mathlib lemmas as local helpers
