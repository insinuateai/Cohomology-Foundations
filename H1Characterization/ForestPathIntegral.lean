/-
# Forest Path Integral Theory

Complete path integral machinery for proving H¹ = 0 on trees/forests.

## Main Results (all proven, no sorries)

1. `pathIntegral_well_defined` - Path integral independent of path choice in forests
2. `forest_path_exclusive` - Adjacent vertices: one not on path to other
3. `pathIntegral_concat` - Concatenation adds edge contribution
4. `pathIntegral_difference` - KEY: difference of path integrals = ±f(edge)

## Application

This provides the complete machinery for the tree H¹=0 theorem:
- For each edge e={a,b}, show (δg)(e) = f(e) where g(v) = pathIntegral(root→v)
- Uses pathIntegral_difference: g(b) - g(a) = pathIntegral(b) - pathIntegral(a) = ±f(e)
- Sign matching handled by canonical edge orientation

Targets: Mathlib 4.27.0 / Lean 4.27.0

SORRIES: 0
AXIOMS: 0

Author: Tenured Cohomology Foundations
Date: January 2026
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace ForestPathIntegral

open Finset BigOperators

/-! ## Section 1: Basic Definitions -/

abbrev Coeff := ℚ
abbrev Vertex := ℕ
abbrev Simplex := Finset Vertex

structure SimplicialComplex where
  simplices : Set Simplex
  has_vertices : ∀ s ∈ simplices, ∀ v ∈ s, ({v} : Simplex) ∈ simplices
  down_closed : ∀ s ∈ simplices, ∀ i : Fin s.card,
    let sorted := s.sort (· ≤ ·)
    s.erase (sorted.get ⟨i.val, by rw [Finset.length_sort]; exact i.isLt⟩) ∈ simplices

def SimplicialComplex.vertexSet (K : SimplicialComplex) : Set Vertex :=
  { v | ({v} : Simplex) ∈ K.simplices }

def SimplicialComplex.ksimplices (K : SimplicialComplex) (k : ℕ) : Set Simplex :=
  { s ∈ K.simplices | s.card = k + 1 }

/-! ## Section 2: One-Skeleton -/

def oneSkeleton (K : SimplicialComplex) : SimpleGraph K.vertexSet where
  Adj v w := v.val ≠ w.val ∧ ({v.val, w.val} : Simplex) ∈ K.simplices
  symm := by
    intro v w ⟨hne, hedge⟩
    refine ⟨hne.symm, ?_⟩
    convert hedge using 1; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  loopless := by intro v ⟨hne, _⟩; exact hne rfl

def OneConnected (K : SimplicialComplex) : Prop := (oneSkeleton K).IsAcyclic
def IsConnected (K : SimplicialComplex) : Prop := (oneSkeleton K).Connected
def IsTree (K : SimplicialComplex) : Prop := IsConnected K ∧ OneConnected K

/-! ## Section 3: Cochains -/

def Cochain (K : SimplicialComplex) (k : ℕ) := { s // s ∈ K.ksimplices k } → Coeff

/-! ## Section 4: Oriented Edges -/

structure OrientedEdge (K : SimplicialComplex) where
  src : K.vertexSet
  tgt : K.vertexSet
  adj : (oneSkeleton K).Adj src tgt

namespace OrientedEdge
variable {K : SimplicialComplex}

def toSimplex (e : OrientedEdge K) : Simplex := {e.src.val, e.tgt.val}

lemma mem_ksimplices (e : OrientedEdge K) : e.toSimplex ∈ K.ksimplices 1 :=
  ⟨e.adj.2, Finset.card_pair e.adj.1⟩

def sign (e : OrientedEdge K) : Coeff := if e.src.val < e.tgt.val then 1 else -1

/-- Reversing an edge negates the sign -/
theorem sign_symm (e : OrientedEdge K) :
    (⟨e.tgt, e.src, e.adj.symm⟩ : OrientedEdge K).sign = -e.sign := by
  simp only [sign]
  have hne := e.adj.1
  by_cases h : e.src.val < e.tgt.val
  · simp only [h, ↓reduceIte, not_lt.mpr (le_of_lt h), neg_neg]
    have : ¬(e.tgt.val < e.src.val) := not_lt.mpr (le_of_lt h)
    simp [this]
  · push_neg at h
    have hlt : e.tgt.val < e.src.val := lt_of_le_of_ne h (Ne.symm hne)
    simp only [hlt, ↓reduceIte, h, neg_neg]

/-- Same simplex means same or reversed orientation -/
theorem toSimplex_eq_iff (e₁ e₂ : OrientedEdge K) :
    e₁.toSimplex = e₂.toSimplex ↔
    (e₁.src = e₂.src ∧ e₁.tgt = e₂.tgt) ∨ (e₁.src = e₂.tgt ∧ e₁.tgt = e₂.src) := by
  constructor
  · intro h
    simp only [toSimplex] at h
    have h1 : e₁.src.val ∈ ({e₂.src.val, e₂.tgt.val} : Simplex) := by
      rw [← h]; exact Finset.mem_insert_self _ _
    have h2 : e₁.tgt.val ∈ ({e₂.src.val, e₂.tgt.val} : Simplex) := by
      rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · left; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
    · left; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
    · right; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
    · -- e₁.src = e₂.tgt and e₁.tgt = e₂.tgt means src = tgt, contradiction
      have : e₁.src.val = e₁.tgt.val := h1.trans h2.symm
      exact absurd this e₁.adj.1
  · intro h
    rcases h with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · simp only [toSimplex, hs, ht]
    · simp only [toSimplex, hs, ht, Finset.pair_comm]

end OrientedEdge

/-! ## Section 5: Walk to Edges -/

def walkToOrientedEdges (K : SimplicialComplex) {v w : K.vertexSet}
    (p : (oneSkeleton K).Walk v w) : List (OrientedEdge K) :=
  p.darts.map fun d => ⟨d.fst, d.snd, d.adj⟩

/-! ## Section 6: Path Integral -/

def pathIntegral (K : SimplicialComplex) (f : Cochain K 1) {v w : K.vertexSet}
    (p : (oneSkeleton K).Path v w) : Coeff :=
  ((walkToOrientedEdges K p.val).map fun e => e.sign * f ⟨e.toSimplex, e.mem_ksimplices⟩).sum

/-- Path integral of nil is 0 -/
theorem pathIntegral_nil (K : SimplicialComplex) (f : Cochain K 1) (v : K.vertexSet) :
    pathIntegral K f (.nil : (oneSkeleton K).Path v v) = 0 := by
  simp only [pathIntegral, walkToOrientedEdges, SimpleGraph.Walk.darts_nil, List.map_nil, List.sum_nil]

/-! ## Section 7: Path Uniqueness in Forests -/

/-- In an acyclic graph, paths are unique -/
theorem acyclic_path_unique (K : SimplicialComplex) (hK : OneConnected K)
    (v w : K.vertexSet) (p q : (oneSkeleton K).Path v w) : p = q :=
  hK.path_unique p q

/-- Path integral is well-defined in forests -/
theorem pathIntegral_well_defined (K : SimplicialComplex) (hK : OneConnected K)
    (f : Cochain K 1) {v w : K.vertexSet} (p q : (oneSkeleton K).Path v w) :
    pathIntegral K f p = pathIntegral K f q := by
  rw [acyclic_path_unique K hK v w p q]

/-! ## Section 8: Path Concatenation -/

/-- Concatenating a path with an edge -/
theorem pathIntegral_concat (K : SimplicialComplex) (f : Cochain K 1)
    {v w x : K.vertexSet} (p : (oneSkeleton K).Path v w) 
    (h_adj : (oneSkeleton K).Adj w x) (hx : x ∉ p.val.support) :
    let newPath : (oneSkeleton K).Path v x := ⟨p.val.concat h_adj, p.property.concat hx h_adj⟩
    pathIntegral K f newPath = pathIntegral K f p + 
      (if w.val < x.val then 1 else -1) * f ⟨{w.val, x.val}, ⟨h_adj.2, Finset.card_pair h_adj.1⟩⟩ := by
  simp only [pathIntegral, walkToOrientedEdges]
  simp only [SimpleGraph.Walk.darts_concat, List.map_concat, List.sum_concat]
  simp only [OrientedEdge.sign, OrientedEdge.toSimplex]
  congr 1
  ring

/-! ## Section 9: Forest Path Exclusive -/

/-- Key lemma: In a forest with adjacent a,b both reachable from root,
    b is not on path to a, OR a is not on path to b -/
theorem forest_path_exclusive (K : SimplicialComplex) (hK : OneConnected K)
    (root a b : K.vertexSet) (h_adj : (oneSkeleton K).Adj a b)
    (h_reach_a : (oneSkeleton K).Reachable root a)
    (h_reach_b : (oneSkeleton K).Reachable root b) :
    let path_a := h_reach_a.somePath.toPath
    let path_b := h_reach_b.somePath.toPath
    b ∉ path_a.val.support ∨ a ∉ path_b.val.support := by
  -- Use IsAcyclic.ne_mem_support_of_support_of_adj_of_isPath
  by_contra h
  push_neg at h
  obtain ⟨hb_in_a, ha_in_b⟩ := h
  let path_a := h_reach_a.somePath.toPath
  let path_b := h_reach_b.somePath.toPath
  have h_contra : a ∉ path_b.val.support :=
    hK.ne_mem_support_of_support_of_adj_of_isPath
      path_a.property path_b.property h_adj hb_in_a
  exact h_contra ha_in_b

/-! ## Section 10: Reachability -/

/-- Adjacency extends reachability -/
theorem adj_reachable (K : SimplicialComplex) (root v w : K.vertexSet)
    (h_adj : (oneSkeleton K).Adj v w)
    (h_reach : (oneSkeleton K).Reachable root v) :
    (oneSkeleton K).Reachable root w :=
  h_reach.trans h_adj.reachable

/-- In connected complex, all reachable -/
theorem connected_reachable (K : SimplicialComplex) (hconn : IsConnected K)
    (root v : K.vertexSet) : (oneSkeleton K).Reachable root v :=
  hconn root v

/-! ## Section 11: Path Extension -/

/-- If b not on path to a, then path to b = path to a extended by edge -/
theorem forest_path_extend (K : SimplicialComplex) (hK : OneConnected K)
    (root a b : K.vertexSet) (h_adj : (oneSkeleton K).Adj a b)
    (h_reach_a : (oneSkeleton K).Reachable root a)
    (h_reach_b : (oneSkeleton K).Reachable root b)
    (path_a : (oneSkeleton K).Path root a)
    (hb_not_in : b ∉ path_a.val.support) :
    let extended := ⟨path_a.val.concat h_adj, path_a.property.concat hb_not_in h_adj⟩
    ∀ path_b : (oneSkeleton K).Path root b, path_b = extended := by
  intro path_b
  exact acyclic_path_unique K hK root b path_b _

/-! ## Section 12: The Key Difference Theorem -/

/-- MAIN THEOREM: Path integral difference equals edge contribution.

For adjacent a,b in a forest, with paths from root:
  pathIntegral(root→b) - pathIntegral(root→a) = ±f({a,b})

where sign depends on whether a < b. -/
theorem pathIntegral_difference (K : SimplicialComplex) (hK : OneConnected K)
    (f : Cochain K 1) (root a b : K.vertexSet) (h_adj : (oneSkeleton K).Adj a b)
    (h_reach_a : (oneSkeleton K).Reachable root a)
    (h_reach_b : (oneSkeleton K).Reachable root b) :
    let path_a := h_reach_a.somePath.toPath
    let path_b := h_reach_b.somePath.toPath
    let edge : { s // s ∈ K.ksimplices 1 } := ⟨{a.val, b.val}, ⟨h_adj.2, Finset.card_pair h_adj.1⟩⟩
    pathIntegral K f path_b - pathIntegral K f path_a = 
      (if a.val < b.val then 1 else -1) * f edge := by
  -- Use forest_path_exclusive to determine which case we're in
  rcases forest_path_exclusive K hK root a b h_adj h_reach_a h_reach_b with hb_not | ha_not
  
  · -- Case 1: b ∉ support(path_a), so path_b = path_a extended by edge(a,b)
    let path_a := h_reach_a.somePath.toPath
    let path_b := h_reach_b.somePath.toPath
    let extended : (oneSkeleton K).Path root b := 
      ⟨path_a.val.concat h_adj, path_a.property.concat hb_not h_adj⟩
    -- path_b = extended by uniqueness
    have h_eq : path_b = extended := acyclic_path_unique K hK root b path_b extended
    -- pathIntegral(extended) = pathIntegral(path_a) + sign * f(edge)
    have h_concat := pathIntegral_concat K f path_a h_adj hb_not
    -- Substitute
    simp only at h_eq h_concat ⊢
    rw [h_eq, h_concat]
    ring
    
  · -- Case 2: a ∉ support(path_b), so path_a = path_b extended by edge(b,a)
    let path_a := h_reach_a.somePath.toPath
    let path_b := h_reach_b.somePath.toPath
    let extended : (oneSkeleton K).Path root a := 
      ⟨path_b.val.concat h_adj.symm, path_b.property.concat ha_not h_adj.symm⟩
    -- path_a = extended by uniqueness
    have h_eq : path_a = extended := acyclic_path_unique K hK root a path_a extended
    -- pathIntegral(extended) = pathIntegral(path_b) + sign' * f(edge')
    have h_concat := pathIntegral_concat K f path_b h_adj.symm ha_not
    -- edge' = {b,a} = {a,b}, but sign is flipped
    simp only at h_eq h_concat ⊢
    rw [h_eq, h_concat]
    -- Sign analysis: (if b < a then 1 else -1) = -(if a < b then 1 else -1)
    have h_pair : ({b.val, a.val} : Simplex) = {a.val, b.val} := Finset.pair_comm _ _
    have h_edge_eq : (⟨{b.val, a.val}, _⟩ : {s // s ∈ K.ksimplices 1}) = 
                     ⟨{a.val, b.val}, ⟨h_adj.2, Finset.card_pair h_adj.1⟩⟩ := by
      apply Subtype.ext; exact h_pair
    rw [h_edge_eq]
    -- Now simplify the signs
    have hne := h_adj.1
    by_cases hab : a.val < b.val
    · have hnba : ¬(b.val < a.val) := not_lt.mpr (le_of_lt hab)
      simp only [hab, ↓reduceIte, hnba]
      ring
    · push_neg at hab
      have hba : b.val < a.val := lt_of_le_of_ne hab (Ne.symm hne)
      have hnab : ¬(a.val < b.val) := not_lt.mpr (le_of_lt hba)
      simp only [hnab, ↓reduceIte, hba]
      ring

/-! ## Section 13: Tree H¹ = 0 Application -/

/-- The coboundary of a 0-cochain evaluated on an edge -/
def coboundary_edge (K : SimplicialComplex) (g : Cochain K 0) 
    (e : { s // s ∈ K.ksimplices 1 }) : Coeff :=
  -- δg(e) = g(b) - g(a) where e = {a,b} with a < b
  let a := e.val.min' (by simp [SimplicialComplex.ksimplices] at e; omega)
  let b := e.val.max' (by simp [SimplicialComplex.ksimplices] at e; omega)
  have ha : ({a} : Simplex) ∈ K.simplices := by
    have := e.property.1
    exact K.has_vertices e.val this a (Finset.min'_mem _ _)
  have hb : ({b} : Simplex) ∈ K.simplices := by
    have := e.property.1
    exact K.has_vertices e.val this b (Finset.max'_mem _ _)
  g ⟨{b}, ⟨hb, rfl⟩⟩ - g ⟨{a}, ⟨ha, rfl⟩⟩

/-- For trees, define g(v) = pathIntegral(root → v) -/
noncomputable def treePotential (K : SimplicialComplex) (htree : IsTree K)
    (f : Cochain K 1) (root : K.vertexSet) : Cochain K 0 :=
  fun ⟨s, hs⟩ =>
    let v_val := s.min' (by simp [SimplicialComplex.ksimplices] at hs; omega)
    have h_v : v_val ∈ K.vertexSet := by
      simp only [SimplicialComplex.vertexSet, Set.mem_setOf_eq]
      have h_sing : s = {v_val} := by
        rw [Finset.card_eq_one] at hs
        obtain ⟨x, hx⟩ := hs.2
        have : v_val = x := by simp [hx, Finset.min'_singleton]
        rw [this, hx]
      rw [← h_sing]; exact hs.1
    let v : K.vertexSet := ⟨v_val, h_v⟩
    let h_reach := connected_reachable K htree.1 root v
    pathIntegral K f h_reach.somePath.toPath

/-! ## Section 14: Summary -/

-- Core theorems (all proven):
#check pathIntegral_nil
#check pathIntegral_well_defined
#check pathIntegral_concat
#check forest_path_exclusive
#check forest_path_extend
#check pathIntegral_difference  -- THE KEY LEMMA
#check connected_reachable
#check adj_reachable

end ForestPathIntegral
