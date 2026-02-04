/-
  Infrastructure/WalkDecomposition.lean

  Walk decomposition lemmas for cycle analysis and path rerouting.
  Provides infrastructure for proving graph theory axioms.

  Key results:
  - mem_support_takeUntil_or_dropUntil: Any vertex in walk is in prefix or suffix
  - mem_edges_takeUntil_or_dropUntil: Any edge in walk is in prefix or suffix
  - cycle_other_path_avoids_edge: In any cycle using edge {u,v}, the "long way around" avoids it
  - forest_single_edge_still_forest: Adding edge between disconnected vertices preserves acyclicity

  SORRIES: 0
  AXIOMS: 0
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

namespace Infrastructure.WalkDecomposition

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-! ## Section 1: Core Support Decomposition

The key insight is that Mathlib provides `Walk.take_spec`:
  (p.takeUntil u h).append (p.dropUntil u h) = p

From this we can derive support and edge decomposition properties.
-/

/-- Support decomposition: vertex in original walk is in takeUntil or dropUntil.
    Derived from Walk.take_spec and mem_support_append_iff. -/
theorem mem_support_takeUntil_or_dropUntil {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (u : V) (hu : u ∈ p.support) (v : V)
    (hv : v ∈ p.support) :
    v ∈ (p.takeUntil u hu).support ∨ v ∈ (p.dropUntil u hu).support := by
  have key := Walk.take_spec p hu
  rw [← key, Walk.mem_support_append_iff] at hv
  exact hv

/-- Edge decomposition: edge in original walk is in takeUntil or dropUntil.
    Derived from Walk.take_spec via edges_append. -/
theorem mem_edges_takeUntil_or_dropUntil {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (u : V) (hu : u ∈ p.support) (e : Sym2 V)
    (he : e ∈ p.edges) :
    e ∈ (p.takeUntil u hu).edges ∨ e ∈ (p.dropUntil u hu).edges := by
  have key := Walk.take_spec p hu
  have : e ∈ ((p.takeUntil u hu).append (p.dropUntil u hu)).edges := by rw [key]; exact he
  rw [Walk.edges_append] at this
  exact List.mem_append.mp this

/-! ## Section 2: Helper Lemmas -/

/-- Helper: if a walk uses edge e, at least one of the takeUntil prefixes doesn't use e.
    This is the core lemma for cycle decomposition. -/
lemma takeUntil_first_endpoint_no_edge (G : SimpleGraph V)
    {a b u v : V} (p : G.Walk a b) (hp : s(u,v) ∈ p.edges)
    (hu : u ∈ p.support) (hv : v ∈ p.support) (hne : u ≠ v) :
    s(u,v) ∉ (p.takeUntil u hu).edges ∨ s(u,v) ∉ (p.takeUntil v hv).edges := by
  -- Compare lengths: whichever vertex appears first has prefix without edge
  by_cases h : (p.takeUntil u hu).length ≤ (p.takeUntil v hv).length
  · left
    intro h_in
    have hv_in_prefix := Walk.snd_mem_support_of_mem_edges _ h_in
    -- v in prefix to u means length(takeUntil v) < length(takeUntil u)
    have h_lt := Walk.length_takeUntil_lt hv_in_prefix hne.symm
    simp only [Walk.takeUntil_takeUntil] at h_lt
    omega
  · right
    push_neg at h
    intro h_in
    have hu_in_prefix := Walk.fst_mem_support_of_mem_edges _ h_in
    -- u in prefix to v means length(takeUntil u) < length(takeUntil v)
    have h_lt := Walk.length_takeUntil_lt hu_in_prefix hne
    simp only [Walk.takeUntil_takeUntil] at h_lt
    omega

/-! ## Section 3: Cycle Edge Analysis -/

/-- In any cycle using edge {u,v}, there is a path from u to v that avoids {u,v}.
    This is "the long way around" the cycle. -/
theorem cycle_other_path_avoids_edge (G : SimpleGraph V)
    {a : V} (c : G.Walk a a) (hc : c.IsCycle) {u v : V}
    (he : s(u,v) ∈ c.edges) (hne : u ≠ v) :
    ∃ p : G.Walk u v, s(u,v) ∉ p.edges := by
  -- Both u and v are in the cycle support
  have hu : u ∈ c.support := Walk.fst_mem_support_of_mem_edges c he
  have hv : v ∈ c.support := Walk.snd_mem_support_of_mem_edges c he
  -- Use takeUntil_first_endpoint_no_edge: one of the prefixes avoids the edge
  rcases takeUntil_first_endpoint_no_edge G c he hu hv hne with h_pu | h_pv
  · -- Prefix to u doesn't use edge s(u,v)
    let c' := c.reverse
    have he' : s(u,v) ∈ c'.edges := by
      rw [Walk.edges_reverse]
      exact List.mem_reverse.mpr he
    have hu' : u ∈ c'.support := by
      rw [Walk.support_reverse]
      exact List.mem_reverse.mpr hu
    have hv' : v ∈ c'.support := by
      rw [Walk.support_reverse]
      exact List.mem_reverse.mpr hv
    rcases takeUntil_first_endpoint_no_edge G c' he' hu' hv' hne with h_pu' | h_pv'
    · -- c'.takeUntil u doesn't use edge
      by_cases hvcheck : s(u,v) ∈ (c.takeUntil v hv).edges
      · -- c.takeUntil v contains the edge, so c.dropUntil v doesn't (by nodup)
        have hnodup : c.edges.Nodup := hc.edges_nodup
        have key := Walk.take_spec c hv
        have hnodup' : ((c.takeUntil v hv).edges ++ (c.dropUntil v hv).edges).Nodup := by
          rw [← Walk.edges_append, key]; exact hnodup
        have hdisj := List.Nodup.disjoint hnodup'
        have hnotdrop : s(u,v) ∉ (c.dropUntil v hv).edges := hdisj hvcheck

        -- Construct path: (c.takeUntil u).reverse ++ (c.dropUntil v).reverse
        let p1 := (c.takeUntil u hu).reverse  -- u → a
        let p2 := (c.dropUntil v hv).reverse  -- a → v
        use p1.append p2
        rw [Walk.edges_append]
        intro hmem
        rcases List.mem_append.mp hmem with h1 | h2
        · rw [Walk.edges_reverse] at h1
          exact h_pu (List.mem_reverse.mp h1)
        · rw [Walk.edges_reverse] at h2
          exact hnotdrop (List.mem_reverse.mp h2)
      · -- c.takeUntil v does NOT contain the edge
        let p1 := (c.takeUntil u hu).reverse  -- u → a
        let p2 := c.takeUntil v hv  -- a → v
        use p1.append p2
        rw [Walk.edges_append]
        intro hmem
        rcases List.mem_append.mp hmem with h1 | h2
        · rw [Walk.edges_reverse] at h1
          exact h_pu (List.mem_reverse.mp h1)
        · exact hvcheck h2
    · -- c'.takeUntil v doesn't use edge
      let p1 := (c.takeUntil u hu).reverse  -- u → a
      let p2 := c'.takeUntil v hv'  -- a → v (in reverse cycle)
      use p1.append p2
      rw [Walk.edges_append]
      intro hmem
      rcases List.mem_append.mp hmem with h1 | h2
      · rw [Walk.edges_reverse] at h1
        exact h_pu (List.mem_reverse.mp h1)
      · exact h_pv' h2
  · -- Prefix to v doesn't use edge s(u,v)
    let c' := c.reverse
    have he' : s(u,v) ∈ c'.edges := by
      rw [Walk.edges_reverse]
      exact List.mem_reverse.mpr he
    have hu' : u ∈ c'.support := by
      rw [Walk.support_reverse]
      exact List.mem_reverse.mpr hu
    have hv' : v ∈ c'.support := by
      rw [Walk.support_reverse]
      exact List.mem_reverse.mpr hv
    rcases takeUntil_first_endpoint_no_edge G c' he' hu' hv' hne with h_pu' | h_pv'
    · -- c'.takeUntil u doesn't use edge
      let p1 := (c'.takeUntil u hu').reverse  -- u → a
      let p2 := c.takeUntil v hv  -- a → v
      use p1.append p2
      rw [Walk.edges_append]
      intro hmem
      rcases List.mem_append.mp hmem with h1 | h2
      · rw [Walk.edges_reverse] at h1
        exact h_pu' (List.mem_reverse.mp h1)
      · exact h_pv h2
    · -- c'.takeUntil v doesn't use edge - use edge partition on c for u
      have hedge_u := mem_edges_takeUntil_or_dropUntil c u hu (s(u,v)) he
      rcases hedge_u with htake_u | hdrop_u
      · -- s(u,v) ∈ (c.takeUntil u).edges, so not in dropUntil (by nodup)
        have hnodup : c.edges.Nodup := hc.edges_nodup
        have key := Walk.take_spec c hu
        have hnodup' : ((c.takeUntil u hu).edges ++ (c.dropUntil u hu).edges).Nodup := by
          rw [← Walk.edges_append, key]; exact hnodup
        have hdisj := List.Nodup.disjoint hnodup'
        have hnotdrop_u : s(u,v) ∉ (c.dropUntil u hu).edges := hdisj htake_u

        let p1 := c.dropUntil u hu  -- u → a
        let p2 := c.takeUntil v hv  -- a → v
        use p1.append p2
        rw [Walk.edges_append]
        intro hmem
        rcases List.mem_append.mp hmem with h1 | h2
        · exact hnotdrop_u h1
        · exact h_pv h2
      · -- s(u,v) ∈ (c.dropUntil u).edges, so not in takeUntil (by nodup)
        have hnodup : c.edges.Nodup := hc.edges_nodup
        have key := Walk.take_spec c hu
        have hnodup' : ((c.takeUntil u hu).edges ++ (c.dropUntil u hu).edges).Nodup := by
          rw [← Walk.edges_append, key]; exact hnodup
        have hdisj := List.Nodup.disjoint hnodup'
        have hnottake_u : s(u,v) ∉ (c.takeUntil u hu).edges := hdisj.symm hdrop_u

        let p1 := (c.takeUntil u hu).reverse  -- u → a
        let p2 := c.takeUntil v hv  -- a → v
        use p1.append p2
        rw [Walk.edges_append]
        intro hmem
        rcases List.mem_append.mp hmem with h1 | h2
        · rw [Walk.edges_reverse] at h1
          exact hnottake_u (List.mem_reverse.mp h1)
        · exact h_pv h2

/-! ## Section 4: Forest Single Edge Theorem -/

/-- Adjacency in G ⊔ fromEdgeSet {e} -/
lemma adj_sup_fromEdgeSet (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) (u v : V) :
    (G ⊔ fromEdgeSet {e}).Adj u v ↔ G.Adj u v ∨ (s(u,v) = e ∧ u ≠ v) := by
  simp only [sup_adj, fromEdgeSet_adj, Set.mem_singleton_iff]

/-- Adding edge between disconnected vertices preserves acyclicity.

    ELIMINATES: forest_single_edge_still_forest_aux (GraphComposition.lean:445)

    If G is acyclic and u, v are not reachable from each other in G,
    then adding edge (u, v) cannot create a cycle.

    Proof: Suppose cycle c exists in G ⊔ {(u,v)}.
    - If c doesn't use the new edge: transfer to G, contradiction with hG.
    - If c uses the new edge: the "other path" in c gives G-reachability u↔v,
      contradicting h_not_reach. -/
theorem forest_single_edge_still_forest (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (u v : V) (h_neq : u ≠ v) (h_not_reach : ¬G.Reachable u v) :
    (G ⊔ fromEdgeSet {s(u, v)}).IsAcyclic := by
  let G' := G ⊔ fromEdgeSet {s(u, v)}
  intro w c hc
  by_cases h_uses_edge : s(u,v) ∈ c.edges
  · -- Case: Cycle uses the new edge s(u,v)
    have hu : u ∈ c.support := Walk.fst_mem_support_of_mem_edges c h_uses_edge
    have hv : v ∈ c.support := Walk.snd_mem_support_of_mem_edges c h_uses_edge
    obtain ⟨p, hp⟩ := cycle_other_path_avoids_edge G' c hc h_uses_edge h_neq
    have hp_in_G : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
      intro e he
      have he_in_G' : e ∈ G'.edgeSet := p.edges_subset_edgeSet he
      simp only [G'] at he_in_G'
      rcases Sym2.mk_surjective e with ⟨⟨x, y⟩, hxy⟩
      rw [← hxy, mem_edgeSet] at he_in_G' ⊢
      rw [adj_sup_fromEdgeSet] at he_in_G'
      rcases he_in_G' with hG_adj | ⟨heq, _⟩
      · exact hG_adj
      · exfalso
        have heq' : s(u,v) = e := heq.symm.trans hxy
        have : s(u,v) ∈ p.edges := heq' ▸ he
        exact hp this
    let p_G := p.transfer G hp_in_G
    have h_reach : G.Reachable u v := ⟨p_G⟩
    exact h_not_reach h_reach
  · -- Case: Cycle doesn't use the new edge
    have hc_in_G : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
      intro e he
      have he_in_G' : e ∈ G'.edgeSet := c.edges_subset_edgeSet he
      simp only [G'] at he_in_G'
      rcases Sym2.mk_surjective e with ⟨⟨x, y⟩, hxy⟩
      rw [← hxy, mem_edgeSet] at he_in_G' ⊢
      rw [adj_sup_fromEdgeSet] at he_in_G'
      rcases he_in_G' with hG_adj | ⟨heq, _⟩
      · exact hG_adj
      · exfalso
        have heq' : s(u,v) = e := heq.symm.trans hxy
        have : s(u,v) ∈ c.edges := heq' ▸ he
        exact h_uses_edge this
    let c_G := c.transfer G hc_in_G
    have hc_G : c_G.IsCycle := hc.transfer hc_in_G
    exact hG c_G hc_G

/-! ## Section 5: Corollaries -/

/-- Deleting an edge from an acyclic graph preserves acyclicity -/
theorem deleteEdges_isAcyclic (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set (Sym2 V)) (hG : G.IsAcyclic) : (G.deleteEdges s).IsAcyclic := by
  intro v c hc
  let c' := c.mapLe (deleteEdges_le s)
  have hc' : c'.IsCycle := hc.mapLe _
  exact hG c' hc'

end Infrastructure.WalkDecomposition
