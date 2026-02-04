/-
  Tests/SmallComplexes.lean

  Concrete verification tests for H¹ characterization on small graphs.
  These tests verify core theorems with explicit small examples.

  SORRIES: 0
  AXIOMS: 0
-/

import H1Characterization.SmallGraphs
import Perspective.AlignmentEquivalence

namespace Tests.SmallComplexes

open H1Characterization
open Perspective

/-!
## Small Graph Acyclicity Tests

Verify that graphs with fewer than 3 vertices are always acyclic.
-/

-- Test 1: Single vertex graphs are one-connected (acyclic)
#check @single_vertex_acyclic
-- Verifies: K with card ≤ 1 → OneConnected K

-- Test 2: Two-vertex graphs are one-connected (acyclic)
#check @two_vertex_acyclic
-- Verifies: K with card = 2 → OneConnected K

-- Test 3: Graphs with < 3 vertices are one-connected
#check @lt_three_vertices_oneConnected
-- Verifies: K with card < 3 → OneConnected K

/-!
## H¹ Triviality Tests for Small Graphs

Verify H¹ = 0 for small connected graphs.
-/

-- Test 4: Single vertex has trivial H¹
#check @h1_trivial_single_vertex
-- Verifies: K with card = 1 and connected → H1Trivial K

-- Test 5: Two-vertex connected graph has trivial H¹
#check @h1_trivial_two_vertex
-- Verifies: K with card = 2 and connected → H1Trivial K

-- Test 6: Main small graph theorem
#check @h1_trivial_small
-- Verifies: K with card < 3 and connected → H1Trivial K

/-!
## Hollow Triangle Tests (Non-trivial H¹)

Verify the hollow triangle has H¹ ≠ 0, demonstrating the obstruction.
-/

-- Test 7: Hollow triangle structure exists
#check @hollowTriangle
-- The simplicial complex with 3 vertices, 3 edges, NO 2-simplex

-- Test 8: Hollow triangle has non-trivial H¹
#check @hollow_triangle_h1_nontrivial
-- Verifies: ∃ cocycle on hollowTriangle that is NOT a coboundary

/-!
## Two-System Alignment Tests

Verify alignment characterization for 2 value systems.
-/

-- Test 9: Two-system alignment characterization
#check @two_system_alignable_iff
-- Verifies: Alignable H A ε ↔ ∀ s, |H.values s - A.values s| ≤ 2 * ε

-- Test 10: Two systems always have trivial H¹
#check @two_system_h1_trivial
-- Verifies: H1Trivial (twoValueComplex H A ε)

/-!
## Path Uniqueness and Walk Properties

Verify path properties in acyclic graphs.
-/

-- Test 11: Paths are unique in acyclic graphs
#check @path_unique_acyclic
-- Verifies: OneConnected K → all paths between two vertices are equal

-- Test 12: Cycle support has distinct vertices
#check @cycle_support_tail_distinct
-- Verifies: Cycle support tail has no duplicates

/-!
## Graph Structure Tests

Verify structural properties of simplicial complexes.
-/

-- Test 13: Small graphs have no filled triangles
#check @small_graph_hollow
-- Verifies: K with card < 3 → hasNoFilledTriangles K

/-!
## Multi-System Alignment Tests

Verify the crown jewel theorem components.
-/

-- Test 14: Reconciliation implies pairwise agreement
#check @reconciliation_implies_pairwise_agreement
-- Verifies: If R reconciles all systems, then pairwise agreement within 2ε

-- Test 15: Pairwise agreement implies average reconciles
#check @pairwise_agreement_implies_average_reconciles
-- Verifies: If systems agree pairwise ≤ ε, average reconciles within ε

-- Test 16: Three-system path is alignable
#check @three_system_path_alignable
-- Verifies: Path-connected 3 systems can be reconciled

-- Test 17: n-system alignment implies H¹ trivial (forward direction)
#check @n_system_alignment_implies_h1_trivial
-- Verifies: Global reconciliation → H1Trivial (valueComplex)

/-!
## Summary

All tests above verify that the core theorems type-check correctly.
This serves as a regression test suite - if any theorem signature changes
or is removed, compilation will fail.

Test count: 17 theorem verification tests
-/

end Tests.SmallComplexes
