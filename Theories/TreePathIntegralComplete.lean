/-
# Complete Tree Path Integral Theory

Rigorous path integral machinery for proving H¹ = 0 on trees.

## Main Results

1. `pathIntegral_append` - Path concatenation is additive
2. `pathIntegral_cons` - Single edge adds signed contribution  
3. `tree_adjacent_paths` - Adjacent vertices: one path extends the other
4. `cocycle_path_difference_proof` - The key difference theorem

Targets: Mathlib 4.27.0 / Lean 4.27.0

SORRIES: 0
AXIOMS: 0

Author: Tenured Cohomology Foundations
Date: January 2026
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace TreePathIntegralComplete

open Finset BigOperators SimpleGraph

/-! ## Section 1: Simplicial Complex Definitions -/

abbrev Coeff := ℚ
abbrev Vertex := ℕ
abbrev Simplex := Finset Vertex

structure SimplicialComplex where
  simplices : Set Simplex
  has_vertices : ∀ s ∈ simplices, ∀ v ∈ s, ({v} : Simplex) ∈ simplices
  down_closed : ∀ s ∈ simplices, ∀ i : Fin s.card,
    s.erase ((s.sort (· ≤ ·)).get ⟨i.val, by rw [Finset.length_sort]; exact i.isLt⟩) ∈ simplices

namespace SimplicialComplex
def vertexSet (K : SimplicialComplex) : Set Vertex := { v | ({v} : Simplex) ∈ K.simplices }
def ksimplices (K : SimplicialComplex) (k : ℕ) : Set Simplex := { s ∈ K.simplices | s.card = k + 1 }
end SimplicialComplex

/-! ## Section 2: One-Skeleton -/

def oneSkeleton (K : SimplicialComplex) : SimpleGraph K.vertexSet where
  Adj v w := v.val ≠ w.val ∧ ({v.val, w.val} : Simplex) ∈ K.simplices
  symm := by intro v w ⟨h, e⟩; exact ⟨h.symm, by convert e using 1; ext; simp; tauto⟩
  loopless := by intro v ⟨h, _⟩; exact h rfl

def OneConnected (K : SimplicialComplex) : Prop := (oneSkeleton K).IsAcyclic
def IsConnected (K : SimplicialComplex) : Prop := (oneSkeleton K).Connected
def IsTree (K : SimplicialComplex) : Prop := IsConnected K ∧ OneConnected K

/-! ## Section 3: Cochains -/

def Cochain (K : SimplicialComplex) (k : ℕ) := { s // s ∈ K.ksimplices k } → Coeff

def sign (n : ℕ) : Coeff := if n % 2 = 0 then 1 else -1

/-! ## Section 4: Oriented Edges -/

structure OrientedEdge (K : SimplicialComplex) where
  src : K.vertexSet
  tgt : K.vertexSet
  adj : (oneSkeleton K).Adj src tgt

namespace OrientedEdge
variable {K : SimplicialComplex}

def toSimplex (e : OrientedEdge K) : Simplex := {e.src.val, e.tgt.val}

theorem mem_ksimplices (e : OrientedEdge K) : e.toSimplex ∈ K.ksimplices 1 :=
  ⟨e.adj.2, Finset.card_pair e.adj.1⟩

def sign (e : OrientedEdge K) : Coeff := if e.src.val < e.tgt.val then 1 else -1

theorem sign_symm (e : OrientedEdge K) :
    OrientedEdge.sign ⟨e.tgt, e.src, e.adj.symm⟩ = -e.sign := by
  simp only [OrientedEdge.sign]
  have hne := e.adj.1
  by_cases h : e.src.val < e.tgt.val
  · have : ¬(e.tgt.val < e.src.val) := not_lt.mpr (le_of_lt h)
    simp [h, this]
  · push_neg at h
    have hlt : e.tgt.val < e.src.val := lt_of_le_of_ne h (Ne.symm hne)
    simp [hlt, not_lt.mpr (le_of_lt hlt)]

end OrientedEdge

/-! ## Section 5: Walk to Oriented Edges -/

def walkToOrientedEdges (K : SimplicialComplex) {v w : K.vertexSet}
    (p : (oneSkeleton K).Walk v w) : List (OrientedEdge K) :=
  p.darts.map fun d => ⟨d.fst, d.snd, d.adj⟩

theorem walkToOrientedEdges_nil (K : SimplicialComplex) (v : K.vertexSet) :
    walkToOrientedEdges K (Walk.nil : (oneSkeleton K).Walk v v) = [] := rfl

theorem walkToOrientedEdges_cons (K : SimplicialComplex) {u v w : K.vertexSet}
    (h : (oneSkeleton K).Adj u v) (p : (oneSkeleton K).Walk v w) :
    walkToOrientedEdges K (Walk.cons h p) = ⟨u, v, h⟩ :: walkToOrientedEdges K p := by
  simp [walkToOrientedEdges, Walk.darts_cons]

theorem walkToOrientedEdges_append (K : SimplicialComplex) {u v w : K.vertexSet}
    (p : (oneSkeleton K).Walk u v) (q : (oneSkeleton K).Walk v w) :
    walkToOrientedEdges K (p.append q) = walkToOrientedEdges K p ++ walkToOrientedEdges K q := by
  simp [walkToOrientedEdges, Walk.darts_append]

/-! ## Section 6: Path Integral -/

def pathIntegral (K : SimplicialComplex) (f : Cochain K 1) {v w : K.vertexSet}
    (p : (oneSkeleton K).Walk v w) : Coeff :=
  ((walkToOrientedEdges K p).map fun e => e.sign * f ⟨e.toSimplex, e.mem_ksimplices⟩).sum

/-! ## Section 7: Path Integral Properties -/

/-- Nil walk has zero integral -/
theorem pathIntegral_nil (K : SimplicialComplex) (f : Cochain K 1) (v : K.vertexSet) :
    pathIntegral K f (Walk.nil : (oneSkeleton K).Walk v v) = 0 := by
  simp [pathIntegral, walkToOrientedEdges_nil]

/-- Cons adds single edge contribution -/
theorem pathIntegral_cons (K : SimplicialComplex) (f : Cochain K 1) {u v w : K.vertexSet}
    (h : (oneSkeleton K).Adj u v) (p : (oneSkeleton K).Walk v w) :
    pathIntegral K f (Walk.cons h p) = 
      (if u.val < v.val then 1 else -1) * f ⟨{u.val, v.val}, ⟨h.2, Finset.card_pair h.1⟩⟩ + 
      pathIntegral K f p := by
  simp only [pathIntegral, walkToOrientedEdges_cons, List.map_cons, List.sum_cons]
  simp only [OrientedEdge.sign, OrientedEdge.toSimplex]

/-- Append is additive (KEY LEMMA) -/
theorem pathIntegral_append (K : SimplicialComplex) (f : Cochain K 1) {u v w : K.vertexSet}
    (p : (oneSkeleton K).Walk u v) (q : (oneSkeleton K).Walk v w) :
    pathIntegral K f (p.append q) = pathIntegral K f p + pathIntegral K f q := by
  simp only [pathIntegral, walkToOrientedEdges_append, List.map_append, List.sum_append]

/-- Concat adds edge at end -/
theorem pathIntegral_concat (K : SimplicialComplex) (f : Cochain K 1) {u v w : K.vertexSet}
    (p : (oneSkeleton K).Walk u v) (h : (oneSkeleton K).Adj v w) :
    pathIntegral K f (p.concat h) = pathIntegral K f p + 
      (if v.val < w.val then 1 else -1) * f ⟨{v.val, w.val}, ⟨h.2, Finset.card_pair h.1⟩⟩ := by
  rw [Walk.concat_eq_append, pathIntegral_append, pathIntegral_cons, pathIntegral_nil, add_zero]

/-! ## Section 8: Path Uniqueness -/

theorem acyclic_path_unique (K : SimplicialComplex) (hK : OneConnected K)
    (v w : K.vertexSet) (p q : (oneSkeleton K).Path v w) : p = q :=
  hK.path_unique p q

theorem pathIntegral_well_defined (K : SimplicialComplex) (hK : OneConnected K)
    (f : Cochain K 1) {v w : K.vertexSet} (p q : (oneSkeleton K).Path v w) :
    pathIntegral K f p.val = pathIntegral K f q.val := by
  rw [acyclic_path_unique K hK v w p q]

/-! ## Section 9: Tree Paths -/

theorem connected_reachable (K : SimplicialComplex) (hconn : IsConnected K)
    (u v : K.vertexSet) : (oneSkeleton K).Reachable u v := hconn u v

noncomputable def treePath (K : SimplicialComplex) (htree : IsTree K)
    (root v : K.vertexSet) : (oneSkeleton K).Path root v :=
  (connected_reachable K htree.1 root v).somePath.toPath

/-! ## Section 10: Forest Path Exclusive -/

/-- In acyclic graph, adjacent vertices: one not on path to other -/
theorem forest_path_exclusive (K : SimplicialComplex) (hK : OneConnected K)
    (root a b : K.vertexSet) (h_adj : (oneSkeleton K).Adj a b)
    (h_reach_a : (oneSkeleton K).Reachable root a)
    (h_reach_b : (oneSkeleton K).Reachable root b) :
    b ∉ h_reach_a.somePath.toPath.val.support ∨ 
    a ∉ h_reach_b.somePath.toPath.val.support := by
  by_contra h; push_neg at h
  exact hK.ne_mem_support_of_support_of_adj_of_isPath
    h_reach_a.somePath.toPath.property
    h_reach_b.somePath.toPath.property
    h_adj h.1 h.2

/-! ## Section 11: Tree Adjacent Paths -/

/-- For adjacent a,b in tree, paths from root satisfy:
    path_b = path_a.concat(a→b) OR path_a = path_b.concat(b→a) -/
theorem tree_adjacent_paths (K : SimplicialComplex) (htree : IsTree K)
    (root a b : K.vertexSet) (h_adj : (oneSkeleton K).Adj a b) :
    let path_a := treePath K htree root a
    let path_b := treePath K htree root b
    (∃ hx : b ∉ path_a.val.support, 
      path_b = ⟨path_a.val.concat h_adj, path_a.property.concat hx h_adj⟩) ∨
    (∃ hx : a ∉ path_b.val.support,
      path_a = ⟨path_b.val.concat h_adj.symm, path_b.property.concat hx h_adj.symm⟩) := by
  have h_reach_a := connected_reachable K htree.1 root a
  have h_reach_b := connected_reachable K htree.1 root b
  rcases forest_path_exclusive K htree.2 root a b h_adj h_reach_a h_reach_b with hb_not | ha_not
  · -- b ∉ path_a.support
    left
    use hb_not
    -- path_b is the unique path, and path_a.concat h_adj is also a path to b
    have h_concat_path : (path_a.val.concat h_adj).IsPath := path_a.property.concat hb_not h_adj
    exact acyclic_path_unique K htree.2 root b 
      (treePath K htree root b) ⟨path_a.val.concat h_adj, h_concat_path⟩
  · -- a ∉ path_b.support
    right
    use ha_not
    have h_concat_path : (path_b.val.concat h_adj.symm).IsPath := 
      path_b.property.concat ha_not h_adj.symm
    exact acyclic_path_unique K htree.2 root a
      (treePath K htree root a) ⟨path_b.val.concat h_adj.symm, h_concat_path⟩
  where
    path_a := treePath K htree root a
    path_b := treePath K htree root b

/-! ## Section 12: Main Path Difference Theorem -/

/-- KEY THEOREM: Path integral difference equals signed edge value -/
theorem cocycle_path_difference_proof (K : SimplicialComplex) (htree : IsTree K)
    (f : Cochain K 1) (root a b : K.vertexSet) (h_adj : (oneSkeleton K).Adj a b) :
    pathIntegral K f (treePath K htree root b).val - 
    pathIntegral K f (treePath K htree root a).val =
      (if a.val < b.val then 1 else -1) * 
        f ⟨{a.val, b.val}, ⟨h_adj.2, Finset.card_pair h_adj.1⟩⟩ := by
  rcases tree_adjacent_paths K htree root a b h_adj with ⟨hb_not, h_eq_b⟩ | ⟨ha_not, h_eq_a⟩
  · -- path_b = path_a.concat(a→b)
    calc pathIntegral K f (treePath K htree root b).val - pathIntegral K f (treePath K htree root a).val
      = pathIntegral K f (path_a.val.concat h_adj) - pathIntegral K f path_a.val := by
          rw [h_eq_b]
    _ = (pathIntegral K f path_a.val + (if a.val < b.val then 1 else -1) * 
          f ⟨{a.val, b.val}, _⟩) - pathIntegral K f path_a.val := by
          rw [pathIntegral_concat]
    _ = (if a.val < b.val then 1 else -1) * f ⟨{a.val, b.val}, _⟩ := by ring
  · -- path_a = path_b.concat(b→a)
    calc pathIntegral K f (treePath K htree root b).val - pathIntegral K f (treePath K htree root a).val
      = pathIntegral K f path_b.val - pathIntegral K f (path_b.val.concat h_adj.symm) := by
          rw [h_eq_a]
    _ = pathIntegral K f path_b.val - (pathIntegral K f path_b.val + 
          (if b.val < a.val then 1 else -1) * f ⟨{b.val, a.val}, _⟩) := by
          rw [pathIntegral_concat]
    _ = -((if b.val < a.val then 1 else -1) * f ⟨{b.val, a.val}, _⟩) := by ring
    _ = (if a.val < b.val then 1 else -1) * f ⟨{a.val, b.val}, _⟩ := by
          have hne := h_adj.1
          have h_pair : ({b.val, a.val} : Simplex) = {a.val, b.val} := Finset.pair_comm _ _
          have h_edge_eq : (⟨{b.val, a.val}, _⟩ : {s // s ∈ K.ksimplices 1}) = 
                          ⟨{a.val, b.val}, ⟨h_adj.2, Finset.card_pair h_adj.1⟩⟩ := 
            Subtype.ext h_pair
          rw [h_edge_eq]
          by_cases hab : a.val < b.val
          · have hnba : ¬(b.val < a.val) := not_lt.mpr (le_of_lt hab)
            simp [hab, hnba]
          · push_neg at hab
            have hba : b.val < a.val := lt_of_le_of_ne hab (Ne.symm hne)
            simp [hba, not_lt.mpr (le_of_lt hba)]
  where
    path_a := treePath K htree root a
    path_b := treePath K htree root b

/-! ## Summary -/

#check pathIntegral_nil
#check pathIntegral_cons
#check pathIntegral_append         -- Key: concatenation is additive
#check pathIntegral_concat
#check pathIntegral_well_defined
#check forest_path_exclusive
#check tree_adjacent_paths         -- Key: adjacent paths differ by one edge
#check cocycle_path_difference_proof  -- Main theorem

end TreePathIntegralComplete
