# Infrastructure File Archive

> Detailed descriptions of completed/blocked infrastructure work.
> For active targets, see `next-5-targets.md`.

---

## COMPLETED: SimplicialGraphBridge.lean

**Created**: 2026-02-02
**Axioms Eliminated**: G02, G03 (Euler formula bijection)
**Key Implementation**: `ksimplices_one_to_edges_bijection` using `ForestEulerFormula`

```lean
theorem acyclic_implies_euler (K : SimplicialComplex) (h : OneConnected K) : EulerForestCondition K
theorem euler_implies_acyclic (K : SimplicialComplex) (h : EulerForestCondition K) : OneConnected K
```

---

## COMPLETED: PathDecompositionComplete.lean

**Created**: 2026-02-02
**Axioms Eliminated**: G04, G05
**Key Implementation**: Uses `ExtendedGraphInfra.vertex_in_v_or_w_component`

```lean
theorem bridge_path_decomposition_proven ...
theorem non_v_component_path_avoids_bridge_proven ...
```

---

## COMPLETED: Part of DepthTheoryComplete

**Axioms Eliminated**: X28, X29
**Location**: TreeAuthCoreProofs.lean
**Method**: Fixed `acyclic_periodic_orbit_equiv` by adding `i ≠ T.root →` (original was unprovable)

**Still pending** (blocked by sorries):
- T01-T05: Need TreeAuthCoreProofs sorries fixed

---

## COMPLETED: CriticalPointsCore.lean + FairnessH1Proofs.lean

**Created**: 2026-02-02
**Axioms Eliminated**: X03, X04, C04, F07

---

## BLOCKED: R01-R03 (ConflictResolution)

**Status**: KEEP - Mathematically false
**Reason**: Claims one operation makes H¹=0, fails for complexes with multiple independent cycles
**Counterexample**: Two disjoint hollow triangles

---

## BLOCKED: T06, T07, X27 (HierarchicalPath)

**Status**: Blocked by TreeAuthority.lean build errors
**Errors**: `Nat.find` API issues at lines 341, 339, 369, 394, 412, 420, 427, 481, 487
**Prerequisite**: Fix TreeAuthority.lean compilation

---

## BLOCKED: F01, F02 (FairnessFoundations)

**Status**: Blocked by CompleteComplexH1.lean sorries
**Prerequisite**: Fix `coboundary_edge_formula` and `cocycle_triangle_condition`
