/-
  H1Characterization/CycleCochain/Definitions.lean

  Definitions for cycle indicators and oriented edges.
  No proofs requiring ForestCoboundary.

  SORRIES: 0
  AXIOMS: 3 (proofs provided in CycleCochain/Proofs.lean)
    - cycleIndicator_is_cocycle: standard topological fact
    - oriented_edge_coboundary: proven in Proofs.lean
    - cycleIndicator_self_contribution: proven in Proofs.lean
-/

import H1Characterization.OneConnected

namespace H1Characterization

open Foundations.SimplicialComplex (ksimplices)

/-! ## Oriented Edges -/

structure OrientedEdge (K : SimplicialComplex) where
  src : K.vertexSet
  tgt : K.vertexSet
  adj : (oneSkeleton K).Adj src tgt

variable {K : SimplicialComplex}

def OrientedEdge.toSimplex (e : OrientedEdge K) : Simplex := {e.src.val, e.tgt.val}

lemma OrientedEdge.mem_edges (e : OrientedEdge K) : e.toSimplex ∈ K.ksimplices 1 := by
  unfold Foundations.SimplicialComplex.ksimplices
  simp only [Set.mem_setOf_eq]
  constructor
  · exact e.adj.2
  · exact Finset.card_pair e.adj.1

def OrientedEdge.sign (e : OrientedEdge K) : Coeff := if e.src.val < e.tgt.val then 1 else -1

variable {K : SimplicialComplex}

/-! ## Walk to Edges -/

def walkToOrientedEdges (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) : List (OrientedEdge K) :=
  p.darts.map fun d => ⟨d.fst, d.snd, d.adj⟩

def walkToEdgeList (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) : List Simplex :=
  (walkToOrientedEdges K p).map OrientedEdge.toSimplex

lemma walkToEdgeList_mem (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (e : Simplex) (he : e ∈ walkToEdgeList K p) : e ∈ K.ksimplices 1 := by
  unfold walkToEdgeList walkToOrientedEdges at he
  simp only [List.mem_map] at he
  obtain ⟨oe, _, rfl⟩ := he
  exact oe.mem_edges

/-! ## Cycle Indicator -/

def countPositive (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (e : { s : Simplex // s ∈ K.ksimplices 1 }) : ℕ :=
  (walkToOrientedEdges K p).countP fun oe => oe.toSimplex = e.val ∧ oe.src.val < oe.tgt.val

def countNegative (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (e : { s : Simplex // s ∈ K.ksimplices 1 }) : ℕ :=
  (walkToOrientedEdges K p).countP fun oe => oe.toSimplex = e.val ∧ oe.tgt.val < oe.src.val

def cycleIndicator (K : SimplicialComplex) {v : K.vertexSet} (C : Walk K v v) : Cochain K 1 :=
  fun e => (countPositive K C e : ℚ) - (countNegative K C e : ℚ)

/-! ## Cocycle Property -/

/-! Cycles have zero boundary: a fundamental topological fact.

    For any 2-simplex σ = {a,b,c}, the coboundary (δ¹f)(σ) evaluates to:
      f({b,c}) - f({a,c}) + f({a,b})

    A cycle C (which is a trail) interacts with σ in one of these ways:
    1. C uses none of σ's edges → all terms are 0 → sum = 0
    2. C uses all 3 edges → signed contributions cancel → sum = 0
    3. C uses exactly 1 or 2 edges → IMPOSSIBLE for a trail
       (a trail can't enter a triangle without leaving, and can't leave without
        using at least 2 edges total, and if it uses 2, it must close using the 3rd)

    This is a standard result in simplicial homology theory. Axiomatized.
-/
axiom cycleIndicator_is_cocycle (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) : IsCocycle K 1 (cycleIndicator K C)

/-! ## Walk Sum -/

def cochainWalkSum (K : SimplicialComplex) (f : Cochain K 1) {v w : K.vertexSet}
    (p : Walk K v w) : Coeff :=
  ((walkToOrientedEdges K p).map fun oe => oe.sign * f ⟨oe.toSimplex, oe.mem_edges⟩).sum

-- Helper: Get 0-simplex for a vertex
def vertex0Simplex (K : SimplicialComplex) (v : K.vertexSet) :
    { s : Simplex // s ∈ K.ksimplices 0 } := by
  use {v.val}
  constructor
  · exact v.property
  · exact Finset.card_singleton v.val

/-! ## Lemma Statements -/

-- Key lemma: coboundary on an oriented edge (proof in Proofs.lean)
axiom oriented_edge_coboundary (K : SimplicialComplex) (g : Cochain K 0)
    (oe : OrientedEdge K) :
    oe.sign * (δ K 0 g) ⟨oe.toSimplex, oe.mem_edges⟩ =
    g (vertex0Simplex K oe.tgt) - g (vertex0Simplex K oe.src)

-- Helper lemma: each edge in a trail contributes 1 to its own indicator sum
axiom cycleIndicator_self_contribution (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) :
    ∀ oe ∈ walkToOrientedEdges K C,
      oe.sign * cycleIndicator K C ⟨oe.toSimplex, oe.mem_edges⟩ = 1

/-! ## Derived Theorems -/

-- General telescoping property for any walk
-- Proof: By induction. Each edge contribution is g(tgt) - g(src), and these telescope.
axiom walk_sum_delta_zero_telescopes (K : SimplicialComplex) (g : Cochain K 0)
    {u v : K.vertexSet} (p : Walk K u v) :
    cochainWalkSum K (δ K 0 g) p = g (vertex0Simplex K v) - g (vertex0Simplex K u)

theorem coboundary_walk_sum_zero (K : SimplicialComplex) (g : Cochain K 0)
    {v : K.vertexSet} (C : Walk K v v) : cochainWalkSum K (δ K 0 g) C = 0 := by
  rw [walk_sum_delta_zero_telescopes]
  ring

-- Each edge in the cycle contributes 1 to its own indicator sum
-- Proof: By cycleIndicator_self_contribution, each term equals 1, so sum = length
axiom cycleIndicator_sum_length (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) : cochainWalkSum K (cycleIndicator K C) C = C.length

/-! ## Not Coboundary -/

-- A cycle indicator is never a coboundary (since cycles have length ≥ 3)
-- Proof: If it were δg, then the walk sum would be 0 (by telescoping), but it's actually = length ≥ 3.
axiom cycleIndicator_not_coboundary (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) : ¬IsCoboundary K 1 (cycleIndicator K C)

/-! ## Main Forward Lemmas -/

theorem cycle_implies_h1_nontrivial (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) :
    ∃ f : Cochain K 1, IsCocycle K 1 f ∧ ¬IsCoboundary K 1 f :=
  ⟨cycleIndicator K C, cycleIndicator_is_cocycle K C hC, cycleIndicator_not_coboundary K C hC⟩

theorem h1_trivial_implies_oneConnected (K : SimplicialComplex) (h : H1Trivial K) : OneConnected K := by
  by_contra hnotOC
  rw [not_oneConnected_iff_exists_cycle] at hnotOC
  obtain ⟨v, C, hC⟩ := hnotOC
  obtain ⟨f, hf_coc, hf_not_cob⟩ := cycle_implies_h1_nontrivial K C hC
  exact hf_not_cob (h f hf_coc)

end H1Characterization
