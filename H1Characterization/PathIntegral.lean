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
theorem pathIntegral_zero (K : SimplicialComplex) {v w : K.vertexSet} (p : Path K v w) :
    pathIntegral K 0 p = 0 := by
  unfold pathIntegral cochainWalkSum
  have h : ∀ oe : OrientedEdge K, oe.sign * (0 : Cochain K 1) ⟨oe.toSimplex, oe.mem_edges⟩ = 0 := by
    intro oe
    simp only [Foundations.Cochain.zero_apply, mul_zero]
  simp only [h, List.map_const', List.sum_replicate, smul_zero]

-- Empty path integrates to zero
theorem pathIntegral_nil (K : SimplicialComplex) (f : Cochain K 1) (v : K.vertexSet) :
    pathIntegral K f (SimpleGraph.Path.nil (G := oneSkeleton K) (u := v)) = 0 := by
  unfold pathIntegral cochainWalkSum walkToOrientedEdges
  rfl

-- Path integral is additive under append
theorem pathIntegral_append (K : SimplicialComplex) (f : Cochain K 1)
    {u v w : K.vertexSet} (p : Path K u v) (q : Path K v w)
    (hpq : (p.val.append q.val).IsPath) :
    pathIntegral K f ⟨p.val.append q.val, hpq⟩ = pathIntegral K f p + pathIntegral K f q := by
  unfold pathIntegral cochainWalkSum walkToOrientedEdges
  simp only [SimpleGraph.Walk.darts_append, List.map_append, List.sum_append]

-- Helper lemma: symm'd oriented edge contribution is negated
private lemma orientedEdge_symm_neg (K : SimplicialComplex) (f : Cochain K 1)
    (d : (oneSkeleton K).Dart) :
    (⟨d.symm.fst, d.symm.snd, d.symm.adj⟩ : OrientedEdge K).sign *
      f ⟨(⟨d.symm.fst, d.symm.snd, d.symm.adj⟩ : OrientedEdge K).toSimplex,
        (⟨d.symm.fst, d.symm.snd, d.symm.adj⟩ : OrientedEdge K).mem_edges⟩ =
    -((⟨d.fst, d.snd, d.adj⟩ : OrientedEdge K).sign *
      f ⟨(⟨d.fst, d.snd, d.adj⟩ : OrientedEdge K).toSimplex,
        (⟨d.fst, d.snd, d.adj⟩ : OrientedEdge K).mem_edges⟩) := by
  -- d.symm.fst = d.snd, d.symm.snd = d.fst
  have hfst : d.symm.fst = d.snd := rfl
  have hsnd : d.symm.snd = d.fst := rfl
  simp only [hfst, hsnd]
  have h_simplex : ({d.snd.val, d.fst.val} : Simplex) = {d.fst.val, d.snd.val} :=
    Finset.pair_comm d.snd.val d.fst.val
  simp only [OrientedEdge.sign, OrientedEdge.toSimplex, h_simplex]
  split_ifs with h1 h2 h2
  · exact absurd (lt_trans h2 h1) (lt_irrefl _)
  · ring
  · ring
  · have h_ne := d.adj.1
    have h_eq : d.fst.val = d.snd.val := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
    exact absurd h_eq h_ne

-- Helper: sum of map (- ·) = - sum
private lemma list_sum_map_neg {l : List ℚ} : (l.map (- ·)).sum = -l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]; ring

-- Helper: sum of reversed list equals sum (addition is commutative)
private lemma list_sum_reverse {l : List ℚ} : l.reverse.sum = l.sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    rw [ih]
    ring

-- Reversing a path negates the integral
theorem pathIntegral_reverse (K : SimplicialComplex) (f : Cochain K 1)
    {v w : K.vertexSet} (p : Path K v w) :
    ∃ rev : Path K w v, pathIntegral K f rev = -pathIntegral K f p := by
  use p.reverse
  unfold pathIntegral cochainWalkSum walkToOrientedEdges
  -- p.reverse.val.darts = (p.val.darts.map Dart.symm).reverse
  simp only [SimpleGraph.Path.reverse, SimpleGraph.Walk.darts_reverse]
  -- Expand and simplify
  simp only [List.map_reverse, List.map_map]
  rw [list_sum_reverse]
  -- Now show the sum of symm'd contributions equals negative of original
  suffices h : ∀ l : List ((oneSkeleton K).Dart),
      (l.map (fun d => (⟨d.symm.fst, d.symm.snd, d.symm.adj⟩ : OrientedEdge K).sign *
        f ⟨(⟨d.symm.fst, d.symm.snd, d.symm.adj⟩ : OrientedEdge K).toSimplex,
          (⟨d.symm.fst, d.symm.snd, d.symm.adj⟩ : OrientedEdge K).mem_edges⟩)).sum =
      -((l.map (fun d => (⟨d.fst, d.snd, d.adj⟩ : OrientedEdge K).sign *
        f ⟨(⟨d.fst, d.snd, d.adj⟩ : OrientedEdge K).toSimplex,
          (⟨d.fst, d.snd, d.adj⟩ : OrientedEdge K).mem_edges⟩)).sum) by
    exact h p.val.darts
  intro l
  induction l with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [orientedEdge_symm_neg, ih]
    ring

-- Extending a path by an edge adds the edge contribution
theorem pathIntegral_concat_edge (K : SimplicialComplex) (f : Cochain K 1)
    {v w x : K.vertexSet} (p : Path K v w) (h : (oneSkeleton K).Adj w x)
    (hx : x ∉ p.val.support) :
    ∃ newPath : Path K v x,
      pathIntegral K f newPath = pathIntegral K f p +
        (if w.val < x.val then 1 else -1) * f ⟨{w.val, x.val}, ⟨h.2, Finset.card_pair h.1⟩⟩ := by
  -- The new path is p.concat h
  have h_isPath : (p.val.concat h).IsPath := p.property.concat hx h
  use ⟨p.val.concat h, h_isPath⟩
  unfold pathIntegral cochainWalkSum walkToOrientedEdges
  simp only [SimpleGraph.Walk.darts_concat, List.map_concat, List.sum_concat,
             OrientedEdge.sign, OrientedEdge.toSimplex]

/-! ## Well-Defined on Forests -/

theorem pathIntegral_well_defined (K : SimplicialComplex) (hK : OneConnected K)
    (f : Cochain K 1) {v w : K.vertexSet} (p q : Path K v w) :
    pathIntegral K f p = pathIntegral K f q := by
  rw [acyclic_path_unique K hK v w p q]

-- In a connected graph, paths exist between any two vertices
-- Uses Walk.toPath to convert any walk to a path
theorem pathBetween_exists (K : SimplicialComplex) {v w : K.vertexSet}
    (h : (oneSkeleton K).Reachable v w) : Nonempty (Path K v w) :=
  ⟨h.some.toPath⟩

noncomputable def pathBetween (K : SimplicialComplex) {v w : K.vertexSet}
    (h : (oneSkeleton K).Reachable v w) : Path K v w :=
  Classical.choice (pathBetween_exists K h)

end H1Characterization
