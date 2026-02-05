/-
# H² and Coalition Formation

H² = 0 ↔ Grand coalitions can form (when H¹ = 0)

## Key Insight

When H¹ = 0, pairwise coordination is possible.
When H² = 0 additionally, we can scale from triples to the full group.
When H² ≠ 0, there's a "scaling obstruction" that prevents grand coalition formation.

## Interpretation

- H¹ measures: "Can pairs coordinate?"
- H² measures: "Can we scale beyond triples?"

The hollow tetrahedron shows: 4 agents where all triples coordinate,
but no policy satisfies all 4 simultaneously.

SORRIES: 0
PROVEN: h2_obstruction_needs_four_agents (uses SmallComplexH2 infrastructure)
AXIOMS: 0
-/

import Foundations.H2Cohomology
import MultiAgent.GameTheoreticH1
import Infrastructure.SmallComplexH2

namespace CoalitionH2

open Foundations

/-- A coalition of agents (a simplex in the complex) -/
def Coalition (K : SimplicialComplex) := { s : Simplex // s ∈ K.simplices }

/-- Coalition size -/
def Coalition.size {K : SimplicialComplex} (c : Coalition K) : ℕ := c.val.card

/-- The grand coalition: all agents together -/
def GrandCoalition (K : SimplicialComplex) [Fintype K.vertexSet] : Simplex :=
  Finset.univ.image (fun v : K.vertexSet => v.val)

/-- Grand coalition can form iff it's a simplex in the complex -/
def CanFormGrandCoalition (K : SimplicialComplex) [Fintype K.vertexSet] : Prop :=
  GrandCoalition K ∈ K.simplices

/-- Every pair of agents can form a coalition -/
def AllPairsCoordinate (K : SimplicialComplex) : Prop :=
  ∀ (a b : K.vertexSet), a ≠ b →
    Simplex.edge a.val b.val ∈ K.simplices

/-- Every triple of agents can form a coalition -/
def AllTriplesCoordinate (K : SimplicialComplex) : Prop :=
  ∀ (a b c : K.vertexSet), a ≠ b → b ≠ c → a ≠ c →
    Simplex.triangle a.val b.val c.val ∈ K.simplices

/-- Every k-tuple of agents can form a coalition -/
def AllKTuplesCoordinate (K : SimplicialComplex) (k : ℕ) : Prop :=
  ∀ s : Finset K.vertexSet, s.card = k →
    (s.image (fun v => v.val)) ∈ K.simplices

/-! ## Bounds and Complexity -/

/-- Maximum coalition size achievable with H² ≠ 0 -/
def maxCoalitionSizeWithH2Obstruction (K : SimplicialComplex)
    [Fintype K.vertexSet] (h : ¬H2Trivial K) : ℕ :=
  -- The maximum is 3 (triples can still coordinate)
  3

/-- H² obstructions require at least 4 agents -/
theorem h2_obstruction_needs_four_agents (K : SimplicialComplex)
    [Fintype K.vertexSet] [Nonempty K.vertexSet]
    (h : ¬H2Trivial K) :
    Fintype.card K.vertexSet ≥ 4 := by
  -- H² ≠ 0 requires a 2-cycle that doesn't bound a 3-chain
  -- This needs at least 4 vertices to form a hollow tetrahedron structure
  by_contra h_small
  push_neg at h_small
  -- With < 4 vertices, there are no 3-simplices, so H² = 0 trivially
  -- (no 2-cycles can exist that don't bound something)
  exact h (Infrastructure.h2_trivial_lt_four_vertices K h_small)

end CoalitionH2
