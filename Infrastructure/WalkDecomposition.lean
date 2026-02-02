/-
  Infrastructure/WalkDecomposition.lean

  Walk decomposition lemmas for cycle analysis and path rerouting.
  Provides infrastructure for proving graph theory axioms.

  Key results:
  - support_takeUntil_append_dropUntil: Decompose walk support at any vertex
  - mem_support_takeUntil_or_dropUntil: Any vertex in walk is in prefix or suffix
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

/-! ## Section 1: Core Support Decomposition -/

/-- Helper: if a walk uses edge e, at least one of the takeUntil prefixes doesn't use e.
    This is imported from TreeGraphInfra but included here for completeness. -/
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

/-- Edges in takeUntil are a subset of the original walk's edges -/
lemma edges_takeUntil_subset (G : SimpleGraph V)
    {a b : V} (p : G.Walk a b) (u : V) (hu : u ∈ p.support) :
    ∀ e ∈ (p.takeUntil u hu).edges, e ∈ p.edges := by
  intro e he
  have h := Walk.edges_takeUntil_subset p u hu
  exact h he

/-- Edges in dropUntil are a subset of the original walk's edges -/
lemma edges_dropUntil_subset (G : SimpleGraph V)
    {a b : V} (p : G.Walk a b) (u : V) (hu : u ∈ p.support) :
    ∀ e ∈ (p.dropUntil u hu).edges, e ∈ p.edges := by
  intro e he
  have h := Walk.edges_dropUntil_subset p u hu
  exact h he

/-- Any vertex in walk support is in takeUntil support or dropUntil support -/
theorem mem_support_takeUntil_or_dropUntil (G : SimpleGraph V)
    {a b : V} (p : G.Walk a b) (u : V) (hu : u ∈ p.support) (v : V)
    (hv : v ∈ p.support) :
    v ∈ (p.takeUntil u hu).support ∨ v ∈ (p.dropUntil u hu).support := by
  -- Use the fact that support of takeUntil ++ dropUntil covers all of p.support
  have key := Walk.support_takeUntil_append_support_dropUntil p u hu
  -- v ∈ p.support means v ∈ (takeUntil).support ++ (dropUntil).support
  rw [key] at hv
  exact List.mem_append.mp hv

/-- Any edge in walk is in takeUntil or dropUntil -/
theorem mem_edges_takeUntil_or_dropUntil (G : SimpleGraph V)
    {a b : V} (p : G.Walk a b) (u : V) (hu : u ∈ p.support) (e : Sym2 V)
    (he : e ∈ p.edges) :
    e ∈ (p.takeUntil u hu).edges ∨ e ∈ (p.dropUntil u hu).edges := by
  have key := Walk.edges_takeUntil_append_edges_dropUntil p u hu
  rw [key] at he
  exact List.mem_append.mp he

/-! ## Section 2: Cycle Edge Analysis -/

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
    -- We want path from u to v. Use: c = (takeUntil u) ++ (dropUntil u)
    -- dropUntil u goes from u to a (end of cycle)
    -- The cycle is closed, so a = a, and we can compose walks
    -- Strategy: Use the "other direction" around the cycle
    -- c.reverse is a cycle from a to a in reverse
    -- It contains the same edge s(u,v)
    let c' := c.reverse
    have hc' : c'.IsCycle := hc.reverse
    have he' : s(u,v) ∈ c'.edges := by
      rw [Walk.edges_reverse]
      exact List.mem_reverse.mpr he
    have hu' : u ∈ c'.support := by
      rw [Walk.support_reverse]
      exact List.mem_reverse.mpr hu
    have hv' : v ∈ c'.support := by
      rw [Walk.support_reverse]
      exact List.mem_reverse.mpr hv
    -- In the reverse cycle, check which prefix avoids the edge
    rcases takeUntil_first_endpoint_no_edge G c' he' hu' hv' hne with h_pu' | h_pv'
    · -- c'.takeUntil u doesn't use edge
      -- c' goes from a to a (reversed), so c'.takeUntil u goes from a to u
      -- We need u to v. Use c'.dropUntil u which goes from u to a
      -- Then reverse it? No, let's think differently.
      -- Actually we want: a path from u to v not using the edge
      -- c.dropUntil u goes from u to a (end of c)
      -- Since c is a closed walk a→a, we can compose:
      -- c.dropUntil u: u → a
      -- We need u → v. Let's use c.dropUntil v which goes from v → a
      -- and then c.takeUntil v which goes from a → v
      -- Hmm, this is getting complicated. Let's use a cleaner approach.

      -- The walk (c.dropUntil u).append (c.takeUntil u) goes from u back to u
      -- around the "other way" of the cycle
      -- We can then takeUntil v on this combined walk

      -- Actually, simplest: (c'.takeUntil v).reverse gives a path from v to a
      -- and (c'.dropUntil v) gives a path from v to a
      -- Hmm no.

      -- Let me try: c'.takeUntil v goes from a to v (in reversed cycle)
      -- If we reverse that, we get a path from v to a
      -- c.takeUntil u goes from a to u
      -- So: (c'.takeUntil v).reverse.append (c.takeUntil u) goes v → a → u
      -- Then reverse to get u → a → v, but that's not what we want either.

      -- Cleaner: c.dropUntil u goes from u to a. c.takeUntil v goes from a to v.
      -- Compose: c.dropUntil u ++ c.takeUntil v goes from u to v
      -- But wait, c.dropUntil u ends at a, and c.takeUntil v starts at a.
      -- Perfect! (c.dropUntil u).append (c.takeUntil v) : Walk u v
      -- Does this avoid s(u,v)? Need to check.

      -- Actually c.dropUntil u might contain the edge. Let's think again.
      -- We know: c.takeUntil u does NOT contain s(u,v) (from h_pu)
      -- And: c'.takeUntil u does NOT contain s(u,v) (from h_pu')

      -- c' = c.reverse
      -- c'.takeUntil u is a walk in the reversed graph from a to u
      -- (c'.takeUntil u).reverse is a walk from u to a
      -- This walk doesn't contain s(u,v) (edge is symmetric)

      -- Similarly from h_pu: c.takeUntil u (from a to u) doesn't contain s(u,v)

      -- c.dropUntil u goes from u to a (end of c)
      -- c.dropUntil v goes from v to a

      -- By edge decomposition: s(u,v) ∈ c.takeUntil u ∨ s(u,v) ∈ c.dropUntil u
      -- Since s(u,v) ∉ c.takeUntil u (h_pu), we have s(u,v) ∈ c.dropUntil u
      -- So c.dropUntil u contains the edge.

      -- Similarly for v: s(u,v) ∈ c.takeUntil v ∨ s(u,v) ∈ c.dropUntil v

      -- Let's use the reverse cycle more directly.
      -- (c.dropUntil v).reverse goes from a to v
      -- (c'.takeUntil u).reverse = (c.reverse.takeUntil u).reverse goes from u to a
      -- No wait, that's back to a.

      -- OK let me just construct this directly:
      -- Path 1: c.takeUntil v goes from a to v, may or may not contain edge
      -- Path 2: c.dropUntil v goes from v to a, may or may not contain edge
      -- Path 3: c.takeUntil u goes from a to u, does NOT contain edge (h_pu)
      -- Path 4: c.dropUntil u goes from u to a, may contain edge

      -- We want u to v. Options:
      -- (c.dropUntil u).append(c.takeUntil v) : u → a → v
      --   Edges = edges(dropUntil u) ++ edges(takeUntil v)
      --   s(u,v) is in one of these (by edge partition), but we need to know which.

      -- From h_pu: s(u,v) ∉ edges(takeUntil u)
      -- By partition: s(u,v) ∈ edges(takeUntil u) ∨ s(u,v) ∈ edges(dropUntil u)
      -- Therefore: s(u,v) ∈ edges(dropUntil u)

      -- From h_pu' (applied to c'): s(u,v) ∉ edges(c'.takeUntil u)
      -- c'.takeUntil u is the walk in c.reverse from a to u
      -- Note: edges(c'.takeUntil u) corresponds to edges in the reversed direction

      -- This is getting complicated. Let me try a direct construction.

      -- Simple approach: Since one of the two "halves" of the cycle avoids the edge,
      -- we can extract the path. Let's use Walk.getVert and construct explicitly.

      -- Even simpler: use the existing lemmas about cycle structure.
      -- A cycle with n ≥ 3 vertices has the property that for any edge (u,v),
      -- removing that edge leaves a path from u to v.

      -- The cleanest proof: use c.toDeleteEdges for the edge s(u,v)
      -- No wait, that's circular.

      -- Let me just provide the witness directly using the cycle structure.
      -- Since c is a cycle containing edge s(u,v), and cycles have length ≥ 3,
      -- the complement of this edge in the cycle is a path from u to v.

      -- For now, use: (c.takeUntil v) when it doesn't contain the edge,
      -- or construct using dropUntil and reverse.

      -- I'll check if c.takeUntil v avoids the edge
      by_cases hvcheck : s(u,v) ∈ (c.takeUntil v hv).edges
      · -- c.takeUntil v contains the edge
        -- By partition, c.dropUntil v does NOT contain the edge (well, need to verify)
        -- Actually partition says edge is in one OR the other, not XOR.
        -- But for a simple cycle (no repeated edges), it's in exactly one.
        -- Since hc.IsCycle, edges are nodup, so XOR holds.
        have hedge_partition := mem_edges_takeUntil_or_dropUntil G c v hv (s(u,v)) he
        -- hedge_partition : s(u,v) ∈ (c.takeUntil v hv).edges ∨ s(u,v) ∈ (c.dropUntil v hv).edges

        -- For cycles, edges don't repeat. So if it's in takeUntil, it's not in dropUntil.
        have hnodup : c.edges.Nodup := hc.edges_nodup
        have htake_sub : (c.takeUntil v hv).edges ⊆ c.edges := fun e he' => edges_takeUntil_subset G c v hv e he'
        have hdrop_sub : (c.dropUntil v hv).edges ⊆ c.edges := fun e he' => edges_dropUntil_subset G c v hv e he'

        -- Use: if takeUntil and dropUntil partition edges and edges are nodup,
        -- then edge in takeUntil means not in dropUntil
        have key := Walk.edges_takeUntil_append_edges_dropUntil c v hv
        have hnodup' : ((c.takeUntil v hv).edges ++ (c.dropUntil v hv).edges).Nodup := by
          rw [← key]; exact hnodup
        have hdisj := List.Nodup.disjoint_of_append hnodup'
        have hnotdrop : s(u,v) ∉ (c.dropUntil v hv).edges := List.Disjoint.not_mem_right hdisj hvcheck

        -- c.dropUntil v goes from v to a
        -- (c.dropUntil v).reverse goes from a to v
        -- c.takeUntil u goes from a to u (and doesn't contain edge by h_pu)
        -- So: (c.takeUntil u).reverse.append (c.dropUntil v).reverse
        --   goes from u to a to v? No, reverse of takeUntil goes from u to a.

        -- (c.takeUntil u).reverse : Walk u a
        -- (c.dropUntil v).reverse : Walk a v
        -- Their append: (c.takeUntil u).reverse.append (c.dropUntil v).reverse : Walk u v
        -- Wait, that requires endpoint matching. takeUntil u ends at u, reverse starts at u.
        -- (c.takeUntil u hu).reverse starts at u, ends at a
        -- (c.dropUntil v hv).reverse starts at a, ends at v
        -- So append: starts at u, ends at v. Perfect!

        let p1 := (c.takeUntil u hu).reverse -- u → a
        let p2 := (c.dropUntil v hv).reverse -- a → v
        have hend : p1.getFinish = p2.getStart := rfl -- both are a
        let p := p1.append p2
        use p
        -- Show s(u,v) ∉ p.edges
        rw [Walk.edges_append]
        intro hmem
        rcases List.mem_append.mp hmem with h1 | h2
        · -- s(u,v) in p1.edges = (c.takeUntil u).reverse.edges
          rw [Walk.edges_reverse] at h1
          have := List.mem_reverse.mp h1
          exact h_pu this
        · -- s(u,v) in p2.edges = (c.dropUntil v).reverse.edges
          rw [Walk.edges_reverse] at h2
          have := List.mem_reverse.mp h2
          exact hnotdrop this
      · -- c.takeUntil v does NOT contain the edge
        -- We can use c.takeUntil v to get from a to v
        -- and (c.takeUntil u).reverse to get from u to a
        -- Compose: u → a → v
        let p1 := (c.takeUntil u hu).reverse -- u → a
        let p2 := c.takeUntil v hv -- a → v
        let p := p1.append p2
        use p
        rw [Walk.edges_append]
        intro hmem
        rcases List.mem_append.mp hmem with h1 | h2
        · rw [Walk.edges_reverse] at h1
          exact h_pu (List.mem_reverse.mp h1)
        · exact hvcheck h2
    · -- c'.takeUntil v doesn't use edge
      -- (c'.takeUntil v).reverse goes from v to a in the original graph
      -- c.takeUntil u goes from a to u (doesn't use edge by h_pu)
      -- Compose appropriately

      -- c'.takeUntil v goes from a to v (in reversed cycle c')
      -- (c'.takeUntil v).reverse goes from v to a
      -- We want u to v.

      -- Option: (c.takeUntil u).reverse goes from u to a
      --         (c'.takeUntil v) goes from a to v (but in graph G, edges are same)
      -- Actually c' is a walk in G (same graph, just reversed direction)
      -- So (c'.takeUntil v) is a valid G.Walk from a to v

      -- (c.takeUntil u).reverse : Walk u a
      -- (c'.takeUntil v) : Walk a v (this is c.reverse.takeUntil v)
      -- Append: Walk u v

      -- Check edges:
      -- (c.takeUntil u).reverse.edges doesn't contain s(u,v) (by h_pu, reversing preserves this)
      -- (c'.takeUntil v).edges doesn't contain s(u,v) (by h_pv')

      let p1 := (c.takeUntil u hu).reverse -- u → a
      let p2 := c'.takeUntil v hv' -- a → v
      let p := p1.append p2
      use p
      rw [Walk.edges_append]
      intro hmem
      rcases List.mem_append.mp hmem with h1 | h2
      · rw [Walk.edges_reverse] at h1
        exact h_pu (List.mem_reverse.mp h1)
      · exact h_pv' h2

  · -- Prefix to v doesn't use edge s(u,v)
    -- c.takeUntil v goes from a to v, doesn't contain edge
    -- We need u to v.

    -- Use reverse cycle c' = c.reverse
    let c' := c.reverse
    have hc' : c'.IsCycle := hc.reverse
    have he' : s(u,v) ∈ c'.edges := by
      rw [Walk.edges_reverse]
      exact List.mem_reverse.mpr he
    have hu' : u ∈ c'.support := by
      rw [Walk.support_reverse]
      exact List.mem_reverse.mpr hu
    have hv' : v ∈ c'.support := by
      rw [Walk.support_reverse]
      exact List.mem_reverse.mpr hv

    -- c'.takeUntil u goes from a to u (in reversed cycle)
    -- Check if it avoids the edge
    rcases takeUntil_first_endpoint_no_edge G c' he' hu' hv' hne with h_pu' | h_pv'
    · -- c'.takeUntil u doesn't use edge
      -- (c'.takeUntil u) : Walk a u
      -- (c.takeUntil v).reverse : Walk v a
      -- We want u to v.
      -- (c'.takeUntil u).reverse : Walk u a
      -- (c.takeUntil v) : Walk a v
      -- Compose: u → a → v

      let p1 := (c'.takeUntil u hu').reverse -- u → a
      let p2 := c.takeUntil v hv -- a → v
      let p := p1.append p2
      use p
      rw [Walk.edges_append]
      intro hmem
      rcases List.mem_append.mp hmem with h1 | h2
      · rw [Walk.edges_reverse] at h1
        exact h_pu' (List.mem_reverse.mp h1)
      · exact h_pv h2

    · -- c'.takeUntil v doesn't use edge
      -- This together with h_pv (c.takeUntil v doesn't use edge) gives us two paths
      -- that avoid the edge. We can use either.

      -- (c'.takeUntil u) may contain the edge, so use c'.takeUntil v approach
      -- (c'.takeUntil v) : Walk a v, doesn't use edge
      -- (c.takeUntil v).reverse : Walk v a, doesn't use edge

      -- We need u to v. Let's check c'.dropUntil u
      -- By edge partition in c': s(u,v) ∈ takeUntil u ∨ dropUntil u
      -- If takeUntil u doesn't have it... wait, we're in the case where
      -- we DON'T know about takeUntil u (that's the h_pu' case we're not in)

      -- In this branch: h_pv' says c'.takeUntil v doesn't use edge
      -- and h_pv says c.takeUntil v doesn't use edge

      -- c'.dropUntil v : Walk v a (in reversed cycle)
      -- c.dropUntil v : Walk v a (in original cycle)

      -- Let's use partition on c for u:
      have hedge_u := mem_edges_takeUntil_or_dropUntil G c u hu (s(u,v)) he
      rcases hedge_u with htake_u | hdrop_u
      · -- s(u,v) ∈ (c.takeUntil u).edges
        -- Then s(u,v) ∉ (c.dropUntil u).edges (by nodup)
        have hnodup : c.edges.Nodup := hc.edges_nodup
        have key := Walk.edges_takeUntil_append_edges_dropUntil c u hu
        have hnodup' : ((c.takeUntil u hu).edges ++ (c.dropUntil u hu).edges).Nodup := by
          rw [← key]; exact hnodup
        have hdisj := List.Nodup.disjoint_of_append hnodup'
        have hnotdrop_u : s(u,v) ∉ (c.dropUntil u hu).edges := List.Disjoint.not_mem_right hdisj htake_u

        -- c.dropUntil u : Walk u a, doesn't use edge
        -- c.takeUntil v : Walk a v, doesn't use edge (h_pv)
        -- Compose: u → a → v
        let p1 := c.dropUntil u hu -- u → a
        let p2 := c.takeUntil v hv -- a → v
        let p := p1.append p2
        use p
        rw [Walk.edges_append]
        intro hmem
        rcases List.mem_append.mp hmem with h1 | h2
        · exact hnotdrop_u h1
        · exact h_pv h2

      · -- s(u,v) ∈ (c.dropUntil u).edges
        -- Then s(u,v) ∉ (c.takeUntil u).edges (by nodup)
        have hnodup : c.edges.Nodup := hc.edges_nodup
        have key := Walk.edges_takeUntil_append_edges_dropUntil c u hu
        have hnodup' : ((c.takeUntil u hu).edges ++ (c.dropUntil u hu).edges).Nodup := by
          rw [← key]; exact hnodup
        have hdisj := List.Nodup.disjoint_of_append hnodup'
        have hnottake_u : s(u,v) ∉ (c.takeUntil u hu).edges := List.Disjoint.not_mem_left hdisj hdrop_u

        -- c.takeUntil u : Walk a u, doesn't use edge
        -- (c.takeUntil u).reverse : Walk u a
        -- c.takeUntil v : Walk a v, doesn't use edge (h_pv)
        -- Compose: u → a → v
        let p1 := (c.takeUntil u hu).reverse -- u → a
        let p2 := c.takeUntil v hv -- a → v
        let p := p1.append p2
        use p
        rw [Walk.edges_append]
        intro hmem
        rcases List.mem_append.mp hmem with h1 | h2
        · rw [Walk.edges_reverse] at h1
          exact hnottake_u (List.mem_reverse.mp h1)
        · exact h_pv h2

/-! ## Section 3: Forest Single Edge Theorem -/

/-- Helper: convert Reachable proof when graphs are definitionally equal via cast -/
private def reachable_cast' {G1 G2 : SimpleGraph V} (heq : G1 = G2)
    {a b : V} (h : G1.Reachable a b) : G2.Reachable a b := heq ▸ h

/-- Walk in G can be lifted to G ⊔ H when G ≤ G ⊔ H -/
lemma walk_lift_sup (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    {a b : V} (p : G.Walk a b) : (G ⊔ H).Walk a b :=
  p.mapLe le_sup_left

/-- Adjacency in G ⊔ fromEdgeSet {e} -/
lemma adj_sup_fromEdgeSet (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) (u v : V) :
    (G ⊔ fromEdgeSet {e}).Adj u v ↔ G.Adj u v ∨ (s(u,v) = e ∧ u ≠ v) := by
  simp only [sup_adj, fromEdgeSet_adj, Set.mem_singleton_iff]
  constructor
  · intro h
    rcases h with hG | ⟨he, hne⟩
    · left; exact hG
    · right; exact ⟨he, hne⟩
  · intro h
    rcases h with hG | ⟨he, hne⟩
    · left; exact hG
    · right; exact ⟨he, hne⟩

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
  intro w c hc
  -- c is a cycle in G' = G ⊔ fromEdgeSet {s(u,v)}
  set G' := G ⊔ fromEdgeSet {s(u, v)} with hG'
  -- Check if c uses the new edge
  by_cases h_uses_edge : s(u,v) ∈ c.edges
  · -- Case: Cycle uses the new edge s(u,v)
    -- Both u and v are in the cycle
    have hu : u ∈ c.support := Walk.fst_mem_support_of_mem_edges c h_uses_edge
    have hv : v ∈ c.support := Walk.snd_mem_support_of_mem_edges c h_uses_edge
    -- By cycle_other_path_avoids_edge, there's a path u → v avoiding s(u,v)
    obtain ⟨p, hp⟩ := cycle_other_path_avoids_edge G' c hc h_uses_edge h_neq
    -- This path p is in G' but avoids the new edge, so it's actually in G
    -- Convert p to a G-walk
    have hp_in_G : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
      intro e he
      -- e is an edge of p, which is a walk in G'
      have he_in_G' : e ∈ G'.edgeSet := p.edges_subset_edgeSet he
      -- e ∈ G'.edgeSet means G'.Adj on the endpoints
      -- G'.Adj = G.Adj ∨ (e = s(u,v) ∧ endpoints ≠)
      -- Since e ≠ s(u,v) (because hp says s(u,v) ∉ p.edges), we have e ∈ G.edgeSet
      rcases Sym2.mk_surjective e with ⟨⟨a, b⟩, hab⟩
      rw [← hab] at he_in_G' he hp ⊢
      simp only [mem_edgeSet] at he_in_G' ⊢
      rw [adj_sup_fromEdgeSet] at he_in_G'
      rcases he_in_G' with hG_adj | ⟨heq, _⟩
      · exact hG_adj
      · -- s(a,b) = s(u,v), but s(u,v) ∉ p.edges (hp), and s(a,b) ∈ p.edges (he)
        rw [hab] at he
        rw [heq] at he
        exact absurd he hp
    -- Transfer p to G
    let p_G := p.transfer G hp_in_G
    -- p_G is a G-walk from u to v
    have h_reach : G.Reachable u v := ⟨p_G⟩
    exact h_not_reach h_reach
  · -- Case: Cycle doesn't use the new edge
    -- All edges of c are in G, so c transfers to G
    have hc_in_G : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
      intro e he
      have he_in_G' : e ∈ G'.edgeSet := c.edges_subset_edgeSet he
      rcases Sym2.mk_surjective e with ⟨⟨a, b⟩, hab⟩
      rw [← hab] at he_in_G' he h_uses_edge ⊢
      simp only [mem_edgeSet] at he_in_G' ⊢
      rw [adj_sup_fromEdgeSet] at he_in_G'
      rcases he_in_G' with hG_adj | ⟨heq, _⟩
      · exact hG_adj
      · rw [hab, heq] at he
        exact absurd he h_uses_edge
    -- Transfer c to G
    let c_G := c.transfer G hc_in_G
    have hc_G : c_G.IsCycle := hc.transfer hc_in_G
    -- But G is acyclic, contradiction
    exact hG c_G hc_G

/-! ## Section 4: Corollaries and Applications -/

/-- Deleting an edge from an acyclic graph preserves acyclicity -/
theorem deleteEdges_isAcyclic (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set (Sym2 V)) (hG : G.IsAcyclic) : (G.deleteEdges s).IsAcyclic := by
  intro v c hc
  -- Any cycle in G.deleteEdges s would lift to a cycle in G
  let c' := c.mapLe (deleteEdges_le s)
  have hc' : c'.IsCycle := hc.mapLe _
  exact hG c' hc'

end Infrastructure.WalkDecomposition
