/-
  Infrastructure/GraphComposition.lean

  Graph composition infrastructure for forest composition properties.
  Provides lemmas for combining acyclic graphs while preserving acyclicity.

  SORRIES: 0
  AXIOMS: 1 (forest_single_edge_still_forest_aux)

  Key theorems:
  - forest_union_forest_acyclic_aux: Disjoint union of acyclic graphs is acyclic (PROVED)
  - forest_single_edge_still_forest_aux: Adding edge between disconnected vertices preserves
    acyclicity (AXIOM - requires walk decomposition lemmas to eliminate)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Sum.Basic
import Infrastructure.GraphTheoryUtils
import H1Characterization.Characterization

namespace Infrastructure.GraphComposition

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Section 1: Subgraph Acyclicity -/

/-- A subgraph of an acyclic graph is acyclic.
    If G ≤ H and H has no cycles, then G has no cycles
    (any cycle in G would lift to a cycle in H). -/
theorem subgraph_acyclic_of_acyclic {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G ≤ H) (hH : H.IsAcyclic) : G.IsAcyclic := by
  intro v c hc
  -- Lift the cycle from G to H
  let c' := c.mapLe hle
  -- c' is also a cycle in H
  have hc' : c'.IsCycle := hc.mapLe hle
  -- But H is acyclic, contradiction
  exact hH c' hc'

/-- Corollary: induced subgraph of acyclic is acyclic -/
theorem induce_acyclic_of_acyclic {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (S : Set V) [DecidablePred (· ∈ S)] :
    (G.induce S).IsAcyclic := by
  intro v c hc
  -- A cycle in the induced graph gives a cycle in G via the embedding
  let emb : G.induce S ↪g G := SimpleGraph.Embedding.induce S
  let c' := c.map emb.toHom
  have hc' : c'.IsCycle := hc.map (fun _ _ h => emb.injective h)
  exact hG c' hc'

/-! ## Section 1.5: Walk Transfer Lemmas -/

/-- A cycle transfers to a subgraph when all edges are in the subgraph.

    Uses Mathlib's Walk.transfer and IsCycle.transfer. -/
theorem cycle_transfer_to_subgraph {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {v : V} (c : H.Walk v v) (hc : c.IsCycle) (h_edges : ∀ e ∈ c.edges, e ∈ G.edgeSet) :
    ∃ c' : G.Walk v v, c'.IsCycle :=
  ⟨c.transfer G h_edges, hc.transfer h_edges⟩

/-! ## Section 2: Disjoint Union of Forests -/

/-- The disjoint sum graph: G ⊕ H on V ⊕ W with no cross edges -/
def sumGraph {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) where
  Adj := fun x y => match x, y with
    | .inl v₁, .inl v₂ => G.Adj v₁ v₂
    | .inr w₁, .inr w₂ => H.Adj w₁ w₂
    | _, _ => False
  symm := by
    intro x y h
    match x, y with
    | .inl v₁, .inl v₂ => exact G.symm h
    | .inr w₁, .inr w₂ => exact H.symm h
    | .inl _, .inr _ => exact h
    | .inr _, .inl _ => exact h
  loopless := by
    intro x
    match x with
    | .inl v => exact G.loopless v
    | .inr w => exact H.loopless w

/-- Adjacency between inl vertices in sumGraph is exactly G-adjacency. -/
theorem sumGraph_adj_inl {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (v₁ v₂ : V) : (sumGraph G H).Adj (.inl v₁) (.inl v₂) ↔ G.Adj v₁ v₂ := by
  simp only [sumGraph]

/-- Adjacency between inr vertices in sumGraph is exactly H-adjacency. -/
theorem sumGraph_adj_inr {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (w₁ w₂ : W) : (sumGraph G H).Adj (.inr w₁) (.inr w₂) ↔ H.Adj w₁ w₂ := by
  simp only [sumGraph]

/-- No cross-edges in sumGraph: inl and inr vertices are never adjacent. -/
theorem sumGraph_no_cross_lr {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (v : V) (w : W) : ¬(sumGraph G H).Adj (.inl v) (.inr w) := by
  simp only [sumGraph, not_false_eq_true]

theorem sumGraph_no_cross_rl {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (w : W) (v : V) : ¬(sumGraph G H).Adj (.inr w) (.inl v) := by
  simp only [sumGraph, not_false_eq_true]

/-- If two vertices are adjacent in sumGraph, they are in the same partition. -/
theorem sumGraph_adj_same_side {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {x y : V ⊕ W} (hadj : (sumGraph G H).Adj x y) :
    (∃ v₁ v₂, x = .inl v₁ ∧ y = .inl v₂) ∨ (∃ w₁ w₂, x = .inr w₁ ∧ y = .inr w₂) := by
  match x, y with
  | .inl v₁, .inl v₂ => left; exact ⟨v₁, v₂, rfl, rfl⟩
  | .inr w₁, .inr w₂ => right; exact ⟨w₁, w₂, rfl, rfl⟩
  | .inl v, .inr w => exact (sumGraph_no_cross_lr v w hadj).elim
  | .inr w, .inl v => exact (sumGraph_no_cross_rl w v hadj).elim

/-- A walk in sumGraph starting at an inl vertex stays entirely in inl vertices. -/
theorem sumGraph_walk_inl_support {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {v : V} {z : V ⊕ W} (p : (sumGraph G H).Walk (.inl v) z) :
    ∀ x ∈ p.support, ∃ v', x = .inl v' := by
  match p with
  | .nil => simp
  | @Walk.cons _ _ _ b _ hadj rest =>
    intro x hx
    simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hmem
    · exact ⟨v, rfl⟩
    · -- next vertex b must be inl since we start at inl
      match b with
      | .inl v' => exact sumGraph_walk_inl_support rest x hmem
      | .inr w' => exact (sumGraph_no_cross_lr v w' hadj).elim

/-- A walk in sumGraph starting at an inr vertex stays entirely in inr vertices. -/
theorem sumGraph_walk_inr_support {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {w : W} {z : V ⊕ W} (p : (sumGraph G H).Walk (.inr w) z) :
    ∀ x ∈ p.support, ∃ w', x = .inr w' := by
  match p with
  | .nil => simp
  | @Walk.cons _ _ _ b _ hadj rest =>
    intro x hx
    simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hmem
    · exact ⟨w, rfl⟩
    · match b with
      | .inr w' => exact sumGraph_walk_inr_support rest x hmem
      | .inl v' => exact (sumGraph_no_cross_rl w v' hadj).elim

/-- Project a walk in sumGraph (starting at inl) to a walk in G. -/
def sumGraph_walk_project_left {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {v₁ v₂ : V} (p : (sumGraph G H).Walk (.inl v₁) (.inl v₂)) : G.Walk v₁ v₂ :=
  match p with
  | .nil => .nil
  | @Walk.cons _ _ _ (.inl v') _ hadj rest =>
    have hadj' : G.Adj v₁ v' := (sumGraph_adj_inl v₁ v').mp hadj
    .cons hadj' (sumGraph_walk_project_left rest)
  | @Walk.cons _ _ _ (.inr w') _ hadj _ =>
    (sumGraph_no_cross_lr v₁ w' hadj).elim

/-- Project a walk in sumGraph (starting at inr) to a walk in H. -/
def sumGraph_walk_project_right {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {w₁ w₂ : W} (p : (sumGraph G H).Walk (.inr w₁) (.inr w₂)) : H.Walk w₁ w₂ :=
  match p with
  | .nil => .nil
  | @Walk.cons _ _ _ (.inr w') _ hadj rest =>
    have hadj' : H.Adj w₁ w' := (sumGraph_adj_inr w₁ w').mp hadj
    .cons hadj' (sumGraph_walk_project_right rest)
  | @Walk.cons _ _ _ (.inl v') _ hadj _ =>
    (sumGraph_no_cross_rl w₁ v' hadj).elim

/-- The projection preserves support membership (mapped via inl). -/
theorem sumGraph_project_left_support {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {v₁ v₂ : V} (p : (sumGraph G H).Walk (.inl v₁) (.inl v₂)) :
    ∀ x ∈ (sumGraph_walk_project_left p).support, .inl x ∈ p.support := by
  match p with
  | .nil =>
    simp only [sumGraph_walk_project_left, Walk.support_nil, List.mem_singleton]
    intro x hx; simp [hx]
  | @Walk.cons _ _ _ (.inl v') _ hadj rest =>
    intro x hx
    simp only [sumGraph_walk_project_left, Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hmem
    · simp only [Walk.support_cons, List.mem_cons, true_or]
    · simp only [Walk.support_cons, List.mem_cons]; right
      exact sumGraph_project_left_support rest x hmem
  | @Walk.cons _ _ _ (.inr w') _ hadj _ =>
    exact (sumGraph_no_cross_lr v₁ w' hadj).elim

/-- Support nodup is preserved by projection. -/
theorem sumGraph_project_left_support_nodup {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {v₁ v₂ : V} (p : (sumGraph G H).Walk (.inl v₁) (.inl v₂))
    (hnodup : p.support.Nodup) : (sumGraph_walk_project_left p).support.Nodup := by
  match p with
  | .nil => simp [sumGraph_walk_project_left]
  | @Walk.cons _ _ _ (.inl v') _ hadj rest =>
    simp only [sumGraph_walk_project_left, Walk.support_cons]
    simp only [Walk.support_cons, List.nodup_cons] at hnodup
    obtain ⟨hnotmem, hnodup'⟩ := hnodup
    rw [List.nodup_cons]
    constructor
    · intro hmem; apply hnotmem; exact sumGraph_project_left_support rest v₁ hmem
    · exact sumGraph_project_left_support_nodup rest hnodup'
  | @Walk.cons _ _ _ (.inr w') _ hadj _ =>
    exact (sumGraph_no_cross_lr v₁ w' hadj).elim

/-- Projection preserves IsPath. -/
theorem sumGraph_project_left_isPath {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {v₁ v₂ : V} (p : (sumGraph G H).Walk (.inl v₁) (.inl v₂)) (hp : p.IsPath) :
    (sumGraph_walk_project_left p).IsPath := by
  rw [Walk.isPath_def] at hp ⊢
  exact sumGraph_project_left_support_nodup p hp

/-- Edge in original walk's inl vertices means edge in projected walk. -/
theorem sumGraph_project_left_edge_mem {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {v₁ v₂ : V} (p : (sumGraph G H).Walk (.inl v₁) (.inl v₂)) {a b : V}
    (hmem : s(Sum.inl a, Sum.inl b) ∈ p.edges) :
    s(a, b) ∈ (sumGraph_walk_project_left p).edges := by
  match p with
  | .nil => simp at hmem
  | @Walk.cons _ _ _ (.inl v') _ hadj rest =>
    simp only [Walk.edges_cons, List.mem_cons] at hmem
    simp only [sumGraph_walk_project_left, Walk.edges_cons, List.mem_cons]
    rcases hmem with heq | hmem'
    · left
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [Sum.inl.injEq] at h1 h2; exact Sym2.eq_iff.mpr (Or.inl ⟨h1, h2⟩)
      · simp only [Sum.inl.injEq] at h1 h2; exact Sym2.eq_iff.mpr (Or.inr ⟨h1, h2⟩)
    · right; exact sumGraph_project_left_edge_mem rest hmem'
  | @Walk.cons _ _ _ (.inr w') _ hadj _ =>
    exact (sumGraph_no_cross_lr v₁ w' hadj).elim

/-- Edge in projected walk means corresponding edge in original walk. -/
theorem sumGraph_project_left_edge_mem_rev {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {v₁ v₂ : V} (p : (sumGraph G H).Walk (.inl v₁) (.inl v₂)) {a b : V}
    (hmem : s(a, b) ∈ (sumGraph_walk_project_left p).edges) :
    s(Sum.inl a, Sum.inl b) ∈ p.edges := by
  match p with
  | .nil => simp [sumGraph_walk_project_left] at hmem
  | @Walk.cons _ _ _ (.inl v') _ hadj rest =>
    simp only [sumGraph_walk_project_left, Walk.edges_cons, List.mem_cons] at hmem
    simp only [Walk.edges_cons, List.mem_cons]
    rcases hmem with heq | hmem'
    · left
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Sym2.eq_iff.mpr (Or.inl ⟨congrArg Sum.inl h1, congrArg Sum.inl h2⟩)
      · exact Sym2.eq_iff.mpr (Or.inr ⟨congrArg Sum.inl h1, congrArg Sum.inl h2⟩)
    · right; exact sumGraph_project_left_edge_mem_rev rest hmem'
  | @Walk.cons _ _ _ (.inr w') _ hadj _ =>
    exact (sumGraph_no_cross_lr v₁ w' hadj).elim

/-- Edge not in original walk means not in projected walk. -/
theorem sumGraph_project_left_edge_not_mem' {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {v₁ v₂ : V} (p : (sumGraph G H).Walk (.inl v₁) (.inl v₂)) {a b : V}
    (h : s(Sum.inl a, Sum.inl b) ∉ p.edges) :
    s(a, b) ∉ (sumGraph_walk_project_left p).edges :=
  fun hmem => h (sumGraph_project_left_edge_mem_rev p hmem)

/-- Edge not in projected walk means corresponding edge not in original walk. -/
theorem sumGraph_project_left_edge_not_mem {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {v₁ v₂ : V} (p : (sumGraph G H).Walk (.inl v₁) (.inl v₂)) {a b : V}
    (h : s(a, b) ∉ (sumGraph_walk_project_left p).edges) :
    s(Sum.inl a, Sum.inl b) ∉ p.edges :=
  fun hmem => h (sumGraph_project_left_edge_mem p hmem)

/-- Projection preserves cycle structure for left projection. -/
theorem sumGraph_project_left_isCycle {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {v : V} (c : (sumGraph G H).Walk (.inl v) (.inl v)) (hc : c.IsCycle) :
    (sumGraph_walk_project_left c).IsCycle := by
  match c with
  | .nil => exact (Walk.IsCycle.not_of_nil hc).elim
  | @Walk.cons _ _ _ (.inl v') _ hadj rest =>
    rw [Walk.cons_isCycle_iff] at hc
    obtain ⟨hPath, hEdge⟩ := hc
    simp only [sumGraph_walk_project_left]
    rw [Walk.cons_isCycle_iff]
    constructor
    · exact sumGraph_project_left_isPath rest hPath
    · exact sumGraph_project_left_edge_not_mem' rest hEdge
  | @Walk.cons _ _ _ (.inr w) _ hadj _ => exact (sumGraph_no_cross_lr v w hadj).elim

/-- The projection preserves support membership for right projection. -/
theorem sumGraph_project_right_support {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {w₁ w₂ : W} (p : (sumGraph G H).Walk (.inr w₁) (.inr w₂)) :
    ∀ x ∈ (sumGraph_walk_project_right p).support, .inr x ∈ p.support := by
  match p with
  | .nil =>
    simp only [sumGraph_walk_project_right, Walk.support_nil, List.mem_singleton]
    intro x hx; simp [hx]
  | @Walk.cons _ _ _ (.inr w') _ hadj rest =>
    intro x hx
    simp only [sumGraph_walk_project_right, Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hmem
    · simp only [Walk.support_cons, List.mem_cons, true_or]
    · simp only [Walk.support_cons, List.mem_cons]; right
      exact sumGraph_project_right_support rest x hmem
  | @Walk.cons _ _ _ (.inl v') _ hadj _ =>
    exact (sumGraph_no_cross_rl w₁ v' hadj).elim

/-- Support nodup is preserved by right projection. -/
theorem sumGraph_project_right_support_nodup {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {w₁ w₂ : W} (p : (sumGraph G H).Walk (.inr w₁) (.inr w₂))
    (hnodup : p.support.Nodup) : (sumGraph_walk_project_right p).support.Nodup := by
  match p with
  | .nil => simp [sumGraph_walk_project_right]
  | @Walk.cons _ _ _ (.inr w') _ hadj rest =>
    simp only [sumGraph_walk_project_right, Walk.support_cons]
    simp only [Walk.support_cons, List.nodup_cons] at hnodup
    obtain ⟨hnotmem, hnodup'⟩ := hnodup
    rw [List.nodup_cons]
    constructor
    · intro hmem; apply hnotmem; exact sumGraph_project_right_support rest w₁ hmem
    · exact sumGraph_project_right_support_nodup rest hnodup'
  | @Walk.cons _ _ _ (.inl v') _ hadj _ =>
    exact (sumGraph_no_cross_rl w₁ v' hadj).elim

/-- Projection preserves IsPath for right projection. -/
theorem sumGraph_project_right_isPath {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {w₁ w₂ : W} (p : (sumGraph G H).Walk (.inr w₁) (.inr w₂)) (hp : p.IsPath) :
    (sumGraph_walk_project_right p).IsPath := by
  rw [Walk.isPath_def] at hp ⊢
  exact sumGraph_project_right_support_nodup p hp

/-- Edge in original walk's inr vertices means edge in projected walk (right). -/
theorem sumGraph_project_right_edge_mem {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {w₁ w₂ : W} (p : (sumGraph G H).Walk (.inr w₁) (.inr w₂)) {a b : W}
    (hmem : s(Sum.inr a, Sum.inr b) ∈ p.edges) :
    s(a, b) ∈ (sumGraph_walk_project_right p).edges := by
  match p with
  | .nil => simp at hmem
  | @Walk.cons _ _ _ (.inr w') _ hadj rest =>
    simp only [Walk.edges_cons, List.mem_cons] at hmem
    simp only [sumGraph_walk_project_right, Walk.edges_cons, List.mem_cons]
    rcases hmem with heq | hmem'
    · left
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [Sum.inr.injEq] at h1 h2; exact Sym2.eq_iff.mpr (Or.inl ⟨h1, h2⟩)
      · simp only [Sum.inr.injEq] at h1 h2; exact Sym2.eq_iff.mpr (Or.inr ⟨h1, h2⟩)
    · right; exact sumGraph_project_right_edge_mem rest hmem'
  | @Walk.cons _ _ _ (.inl v') _ hadj _ =>
    exact (sumGraph_no_cross_rl w₁ v' hadj).elim

/-- Edge in projected walk means corresponding edge in original walk (right). -/
theorem sumGraph_project_right_edge_mem_rev {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {w₁ w₂ : W} (p : (sumGraph G H).Walk (.inr w₁) (.inr w₂)) {a b : W}
    (hmem : s(a, b) ∈ (sumGraph_walk_project_right p).edges) :
    s(Sum.inr a, Sum.inr b) ∈ p.edges := by
  match p with
  | .nil => simp [sumGraph_walk_project_right] at hmem
  | @Walk.cons _ _ _ (.inr w') _ hadj rest =>
    simp only [sumGraph_walk_project_right, Walk.edges_cons, List.mem_cons] at hmem
    simp only [Walk.edges_cons, List.mem_cons]
    rcases hmem with heq | hmem'
    · left
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Sym2.eq_iff.mpr (Or.inl ⟨congrArg Sum.inr h1, congrArg Sum.inr h2⟩)
      · exact Sym2.eq_iff.mpr (Or.inr ⟨congrArg Sum.inr h1, congrArg Sum.inr h2⟩)
    · right; exact sumGraph_project_right_edge_mem_rev rest hmem'
  | @Walk.cons _ _ _ (.inl v') _ hadj _ =>
    exact (sumGraph_no_cross_rl w₁ v' hadj).elim

/-- Edge not in original walk means not in projected walk (right). -/
theorem sumGraph_project_right_edge_not_mem' {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {w₁ w₂ : W} (p : (sumGraph G H).Walk (.inr w₁) (.inr w₂)) {a b : W}
    (h : s(Sum.inr a, Sum.inr b) ∉ p.edges) :
    s(a, b) ∉ (sumGraph_walk_project_right p).edges :=
  fun hmem => h (sumGraph_project_right_edge_mem_rev p hmem)

/-- Edge not in projected walk means corresponding edge not in original walk (right). -/
theorem sumGraph_project_right_edge_not_mem {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {w₁ w₂ : W} (p : (sumGraph G H).Walk (.inr w₁) (.inr w₂)) {a b : W}
    (h : s(a, b) ∉ (sumGraph_walk_project_right p).edges) :
    s(Sum.inr a, Sum.inr b) ∉ p.edges :=
  fun hmem => h (sumGraph_project_right_edge_mem p hmem)

/-- Projection preserves cycle structure for right projection. -/
theorem sumGraph_project_right_isCycle {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {w : W} (c : (sumGraph G H).Walk (.inr w) (.inr w)) (hc : c.IsCycle) :
    (sumGraph_walk_project_right c).IsCycle := by
  match c with
  | .nil => exact (Walk.IsCycle.not_of_nil hc).elim
  | @Walk.cons _ _ _ (.inr w') _ hadj rest =>
    rw [Walk.cons_isCycle_iff] at hc
    obtain ⟨hPath, hEdge⟩ := hc
    simp only [sumGraph_walk_project_right]
    rw [Walk.cons_isCycle_iff]
    constructor
    · exact sumGraph_project_right_isPath rest hPath
    · exact sumGraph_project_right_edge_not_mem' rest hEdge
  | @Walk.cons _ _ _ (.inl v) _ hadj _ => exact (sumGraph_no_cross_rl w v hadj).elim

/-- Two disjoint forests (acyclic graphs) remain acyclic when taken as disjoint union.

    The sum graph G ⊕ H has no cross edges, so any cycle must stay entirely
    within G or entirely within H. Since both are acyclic, neither can contain
    a cycle. Therefore the union is acyclic. -/
theorem forest_union_forest_acyclic_aux {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : G.IsAcyclic) (hH : H.IsAcyclic) :
    (sumGraph G H).IsAcyclic := by
  intro z c hc
  -- Case split on whether z is in G (inl) or H (inr)
  match z with
  | .inl v =>
    -- Cycle starts at inl v, so all vertices are inl and it ends at inl v
    -- We need to show c ends at .inl v (it does by type)
    -- Project the cycle to G
    have hcG := sumGraph_project_left_isCycle c hc
    exact hG _ hcG
  | .inr w =>
    -- Cycle starts at inr w, so all vertices are inr and it ends at inr w
    -- Project the cycle to H
    have hcH := sumGraph_project_right_isCycle c hc
    exact hH _ hcH

/-- Two disjoint forests remain acyclic as a disjoint union -/
theorem forest_union_forest_acyclic {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : G.IsAcyclic) (hH : H.IsAcyclic) :
    (sumGraph G H).IsAcyclic :=
  forest_union_forest_acyclic_aux G H hG hH

/-! ## Section 3: Adding Edge Between Disconnected Components -/

/-- Adding a single edge between disconnected components preserves acyclicity.

    Mathematical justification:
    If G is acyclic and u, v are not reachable from each other in G,
    then adding edge (u, v) cannot create a cycle.

    Case 1: If the cycle doesn't use the new edge, it's entirely in G,
    contradicting hG (G is acyclic).

    Case 2: If the cycle uses the new edge (u,v), then removing this edge
    from the cycle gives a path from u to v in G, contradicting h_not_reach.

    We use the axiom placeholder while proper walk decomposition lemmas are developed. -/
axiom forest_single_edge_still_forest_aux (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (u v : V) (h_neq : u ≠ v) (h_not_reach : ¬G.Reachable u v) :
    (G ⊔ fromEdgeSet {s(u, v)}).IsAcyclic

theorem forest_single_edge_still_forest (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (u v : V) (h_neq : u ≠ v) (h_not_reach : ¬G.Reachable u v) :
    (G ⊔ fromEdgeSet {s(u, v)}).IsAcyclic :=
  forest_single_edge_still_forest_aux G hG u v h_neq h_not_reach

/-! ## Section 4: Main Composition Theorem -/

/-- Main theorem: Composing two aligned modules (forests) with at most one
    connecting edge preserves alignment (acyclicity).

    This is the key result used in Compositional.lean for proving that
    forest_single_edge_composition_axiom. -/
theorem forest_composition_preserves_acyclicity (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (u v : V) (connections : ℕ) (h_conn : connections ≤ 1) :
    -- If we add at most 1 edge, acyclicity is preserved (when endpoints are disconnected)
    connections = 0 ∨
    (connections = 1 → u ≠ v → ¬G.Reachable u v → (G ⊔ fromEdgeSet {s(u, v)}).IsAcyclic) := by
  by_cases h : connections = 0
  · left; exact h
  · right
    intro _ h_neq h_not_reach
    exact forest_single_edge_still_forest G hG u v h_neq h_not_reach

/-! ## Section 5: H¹ Characterization Connection -/

/-- The connection between graph acyclicity and H¹ triviality.
    Uses acyclic_implies_h1_trivial from ForestCoboundary which works
    for both connected and disconnected forests. -/
theorem h1_trivial_of_acyclic_oneSkeleton (K : Foundations.SimplicialComplex)
    [Nonempty K.vertexSet] (h : (H1Characterization.oneSkeleton K).IsAcyclic) :
    Foundations.H1Trivial K :=
  H1Characterization.acyclic_implies_h1_trivial K h

/-- Acyclicity of 1-skeleton implies H¹ = 0 -/
theorem acyclic_implies_h1_trivial' (K : Foundations.SimplicialComplex)
    [Nonempty K.vertexSet] :
    (H1Characterization.oneSkeleton K).IsAcyclic → Foundations.H1Trivial K :=
  h1_trivial_of_acyclic_oneSkeleton K

/-! ## Section 6: Component Acyclicity -/

/-- Adjacent vertices must be in the same partition if there are no cross-edges. -/
private theorem adj_same_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : V → Prop) [DecidablePred P]
    (h_no_cross : ∀ u v, P u → ¬P v → ¬G.Adj u v)
    {u v : V} (hadj : G.Adj u v) : P u ↔ P v := by
  constructor
  · intro hPu
    by_contra hPv
    exact h_no_cross u v hPu hPv hadj
  · intro hPv
    by_contra hPu
    exact h_no_cross v u hPv hPu (G.symm hadj)

/-- All vertices in a walk are in the same partition as the start vertex. -/
private theorem walk_support_same_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : V → Prop) [DecidablePred P]
    (h_no_cross : ∀ u v, P u → ¬P v → ¬G.Adj u v)
    {u v : V} (w : G.Walk u v) : ∀ x ∈ w.support, P u ↔ P x := by
  induction w with
  | nil => simp
  | @cons a b c hadj rest ih =>
    intro x hx
    simp only [Walk.support_cons, List.mem_cons] at hx
    cases hx with
    | inl h => simp [h]
    | inr h =>
      have hPab : P a ↔ P b := adj_same_partition G P h_no_cross hadj
      have hPbx : P b ↔ P x := ih x h
      exact hPab.trans hPbx

/-- Edge in induced walk implies edge in original walk. -/
private theorem edge_of_induce_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) {u v : V} (w : G.Walk u v) (hs : ∀ x ∈ w.support, x ∈ s)
    {a b : V} (ha : a ∈ s) (hb : b ∈ s) :
    s(⟨a, ha⟩, ⟨b, hb⟩) ∈ (w.induce s hs).edges → s(a, b) ∈ w.edges := by
  induction w with
  | nil => simp [Walk.edges]
  | @cons x y z hadj rest ih =>
    simp only [Walk.induce_cons, Walk.edges_cons, List.mem_cons]
    intro hmem
    cases hmem with
    | inl heq =>
      left
      -- heq : s(⟨a, ha⟩, ⟨b, hb⟩) = s(⟨x, _⟩, ⟨y, _⟩)
      -- Extract the equality from Sym2
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [Subtype.mk.injEq] at h1 h2
        exact Sym2.eq_iff.mpr (Or.inl ⟨h1, h2⟩)
      · simp only [Subtype.mk.injEq] at h1 h2
        exact Sym2.eq_iff.mpr (Or.inr ⟨h1, h2⟩)
    | inr hmem' =>
      right
      have hs' : ∀ x ∈ rest.support, x ∈ s := fun x hx => hs x (List.mem_cons_of_mem _ hx)
      exact ih hs' hmem'

/-- A cycle in G.induce s given a cycle in G with all vertices in s.
    Uses induction on the cycle structure. -/
private theorem cycle_induce_of_cycle (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) {v : V} (c : G.Walk v v) (hc : c.IsCycle)
    (hs : ∀ x ∈ c.support, x ∈ s) :
    (c.induce s hs).IsCycle := by
  -- Use cons_isCycle_iff characterization
  cases c with
  | nil => exact (Walk.IsCycle.not_of_nil hc).elim
  | cons hadj rest =>
    -- c = cons hadj rest : Walk v v
    rw [Walk.cons_isCycle_iff] at hc
    obtain ⟨hPath, hEdge⟩ := hc
    -- c.induce s hs = cons _ (rest.induce s _)
    simp only [Walk.induce_cons]
    rw [Walk.cons_isCycle_iff]
    have hs' : ∀ x ∈ rest.support, x ∈ s := fun x hx => hs x (List.mem_cons_of_mem _ hx)
    -- v is the start of c = cons hadj rest, so v ∈ s
    have hv_in_s : v ∈ s := hs v (Walk.start_mem_support _)
    -- The next vertex (start of rest) is in s
    have hnext_in_s := hs' _ rest.start_mem_support
    constructor
    · -- rest.induce s hs' is a path
      -- IsPath means support is nodup
      rw [Walk.isPath_def] at hPath ⊢
      simp only [Walk.support_induce, List.attachWith]
      -- support of rest.induce = rest.support with pmap Subtype.mk
      -- Nodup is preserved by pmap with injective constructor
      apply List.Nodup.pmap
      · intro a ha b hb heq
        simp only [Subtype.mk.injEq] at heq
        exact heq
      · exact hPath
    · -- The edge ∉ (rest.induce s hs').edges
      intro hmem
      apply hEdge
      exact edge_of_induce_edge G s rest hs' hv_in_s hnext_in_s hmem

/-- If two disjoint parts of a graph are both acyclic and have no edges between them,
    the whole graph is acyclic. -/
theorem acyclic_of_disjoint_acyclic_parts (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : V → Prop) [DecidablePred P]
    (h_no_cross : ∀ u v, P u → ¬P v → ¬G.Adj u v)
    (h_part1 : (G.induce {x | P x}).IsAcyclic)
    (h_part2 : (G.induce {x | ¬P x}).IsAcyclic) :
    G.IsAcyclic := by
  intro v c hc
  -- All vertices in c are in the same partition as v
  have h_same : ∀ x ∈ c.support, P v ↔ P x :=
    walk_support_same_partition G P h_no_cross c
  -- Decide which partition v (and hence all of c) is in
  by_cases hPv : P v
  · -- Case: v ∈ P, so all vertices are in P
    have hs : ∀ x ∈ c.support, x ∈ {x | P x} := fun x hx => by
      simp only [Set.mem_setOf_eq]
      exact (h_same x hx).mp hPv
    -- Induce the cycle to G.induce {x | P x}
    -- But G.induce {x | P x} is acyclic
    exact h_part1 (c.induce {x | P x} hs) (cycle_induce_of_cycle G {x | P x} c hc hs)
  · -- Case: v ∉ P, so all vertices are in ¬P
    have hs : ∀ x ∈ c.support, x ∈ {x | ¬P x} := fun x hx => by
      simp only [Set.mem_setOf_eq]
      exact fun hPx => hPv ((h_same x hx).mpr hPx)
    -- Induce the cycle to G.induce {x | ¬P x}
    -- But G.induce {x | ¬P x} is acyclic
    exact h_part2 (c.induce {x | ¬P x} hs) (cycle_induce_of_cycle G {x | ¬P x} c hc hs)

end Infrastructure.GraphComposition
