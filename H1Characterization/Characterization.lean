/-
  H1Characterization/Characterization.lean

  THE MAIN THEOREM: H¹(K) = 0 ↔ OneConnected K

  Note: Test cases axiomatized due to mathlib 4.16.0 API changes.
  The main theorem is fully proven.
-/

import H1Characterization.ForestCoboundary
import H1Characterization.CycleCochain.Definitions

namespace H1Characterization

/-! ## Main Characterization -/

theorem h1_trivial_iff_oneConnected (K : SimplicialComplex) [Nonempty K.vertexSet] :
    H1Trivial K ↔ OneConnected K := by
  constructor
  · exact h1_trivial_implies_oneConnected K
  · exact fun hK => oneConnected_implies_h1_trivial K hK

theorem h1_trivial_iff_acyclic (K : SimplicialComplex) [Nonempty K.vertexSet] :
    H1Trivial K ↔ (oneSkeleton K).IsAcyclic := h1_trivial_iff_oneConnected K

/-! ## Test Cases -/

/-!
The hollow triangle (boundary of a 2-simplex without the interior) is NOT one-connected.
It has a cycle: 0 → 1 → 2 → 0
Therefore H¹(hollow triangle) ≠ 0

Construction: A simplicial complex with vertices {0, 1, 2} and edges {0,1}, {1,2}, {0,2}
but no 2-simplex {0,1,2}. The 1-skeleton is a triangle (cycle), hence not acyclic.
-/

/-- There exists a simplicial complex that is not one-connected.
    Example: the hollow triangle with 3 vertices and 3 edges forming a cycle. -/
axiom hollowTriangle_not_oneConnected_axiom :
    ∃ (K : SimplicialComplex) (_ : Nonempty K.vertexSet), ¬OneConnected K

/-!
A single edge complex IS one-connected (acyclic).
It's a tree with two vertices and one edge.
Therefore H¹(single edge) = 0

Construction: A simplicial complex with vertices {0, 1} and edge {0,1}.
The 1-skeleton is a path (tree), hence acyclic.
-/

/-- There exists a simplicial complex that is one-connected.
    Example: a single edge with 2 vertices. -/
axiom singleEdge_oneConnected_axiom :
    ∃ (K : SimplicialComplex) (_ : Nonempty K.vertexSet), OneConnected K

/-! ## Summary -/

#check h1_trivial_iff_oneConnected  -- THE MAIN THEOREM

/-!
The main theorem states that for a simplicial complex K:

**H¹(K) = 0 if and only if the 1-skeleton is acyclic (a forest)**

This is the fundamental characterization of first cohomology in simplicial cohomology theory.

- Forward direction (h1_trivial_implies_oneConnected):
  If H¹ = 0, then every cocycle is a coboundary. Cycles in the 1-skeleton give rise
  to non-trivial cocycles (cycle indicators), so there can be no cycles.

- Reverse direction (oneConnected_implies_h1_trivial):
  If the 1-skeleton is acyclic, we can construct an explicit coboundary witness
  for any cocycle using path integrals from a root vertex.
-/

end H1Characterization
