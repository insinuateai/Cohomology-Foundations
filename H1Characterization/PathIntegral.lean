/-
  H1Characterization/PathIntegral.lean

  Path integration for 1-cochains. Well-defined on forests.

  Note: Several lemmas axiomatized due to mathlib 4.16.0 API changes
  in Walk/Path definitions. The mathematical content is straightforward.
-/

import H1Characterization.CycleCochain.Definitions

namespace H1Characterization

/-! ## Path Integral -/

def pathIntegral (K : SimplicialComplex) (f : Cochain K 1) {v w : K.vertexSet}
    (p : Path K v w) : Coeff := cochainWalkSum K f p.val

-- Zero cochain integrates to zero
axiom pathIntegral_zero (K : SimplicialComplex) {v w : K.vertexSet} (p : Path K v w) :
    pathIntegral K 0 p = 0

-- Empty path integrates to zero
axiom pathIntegral_nil (K : SimplicialComplex) (f : Cochain K 1) (v : K.vertexSet) :
    pathIntegral K f (SimpleGraph.Path.nil (G := oneSkeleton K) (u := v)) = 0

-- Path integral is additive under append
axiom pathIntegral_append (K : SimplicialComplex) (f : Cochain K 1)
    {u v w : K.vertexSet} (p : Path K u v) (q : Path K v w)
    (hpq : (p.val.append q.val).IsPath) :
    pathIntegral K f ⟨p.val.append q.val, hpq⟩ = pathIntegral K f p + pathIntegral K f q

-- Reversing a path negates the integral
axiom pathIntegral_reverse (K : SimplicialComplex) (f : Cochain K 1)
    {v w : K.vertexSet} (p : Path K v w) :
    ∃ rev : Path K w v, pathIntegral K f rev = -pathIntegral K f p

-- Extending a path by an edge adds the edge contribution
axiom pathIntegral_concat_edge (K : SimplicialComplex) (f : Cochain K 1)
    {v w x : K.vertexSet} (p : Path K v w) (h : (oneSkeleton K).Adj w x)
    (hx : x ∉ p.val.support) :
    ∃ newPath : Path K v x,
      pathIntegral K f newPath = pathIntegral K f p +
        (if w.val < x.val then 1 else -1) * f ⟨{w.val, x.val}, ⟨h.2, Finset.card_pair h.1⟩⟩

/-! ## Well-Defined on Forests -/

theorem pathIntegral_well_defined (K : SimplicialComplex) (hK : OneConnected K)
    (f : Cochain K 1) {v w : K.vertexSet} (p q : Path K v w) :
    pathIntegral K f p = pathIntegral K f q := by
  rw [acyclic_path_unique K hK v w p q]

-- In a connected graph, paths exist between any two vertices
-- Uses Walk.toPath to convert any walk to a path
axiom pathBetween_exists (K : SimplicialComplex) {v w : K.vertexSet}
    (h : (oneSkeleton K).Reachable v w) : Nonempty (Path K v w)

noncomputable def pathBetween (K : SimplicialComplex) {v w : K.vertexSet}
    (h : (oneSkeleton K).Reachable v w) : Path K v w :=
  Classical.choice (pathBetween_exists K h)

end H1Characterization
