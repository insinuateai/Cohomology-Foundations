/-
  Infrastructure/TreeGraphInfra.lean

  Tree and Graph Theory Infrastructure for DimensionBound.lean.

  Key results:
  - edges_plus_components_ge_vertices: |E| + c ≥ |V| for any graph
  - acyclic_euler_eq: For acyclic graphs, |E| + c = |V|
  - euler_eq_implies_acyclic: If |E| + c = |V|, the graph is acyclic

  SORRIES: 2 (in proofs requiring component-wise edge counting)
  AXIOMS: 0
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Infrastructure.GraphTheoryUtils

namespace Infrastructure

open SimpleGraph

variable {V : Type*} [Fintype V]

/-! ## Helper Lemmas for Edge Deletion -/

/-- When we delete a singleton edge from a graph, the edge count decreases by 1. -/
lemma card_edgeFinset_deleteEdges_singleton [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [Fintype G.edgeSet]
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    (G.deleteEdges {e}).edgeFinset.card = G.edgeFinset.card - 1 := by
  classical
  have h_eq : (G.deleteEdges ({e} : Set (Sym2 V))).edgeSet = G.edgeSet \ {e} :=
    edgeSet_deleteEdges ({e} : Set (Sym2 V))
  have h_finset : (G.deleteEdges ({e} : Set (Sym2 V))).edgeFinset = G.edgeFinset \ {e} := by
    ext x
    simp only [mem_edgeFinset, Finset.mem_sdiff, Finset.mem_singleton]
    rw [h_eq]
    simp only [Set.mem_diff, Set.mem_singleton_iff]
  rw [h_finset]
  have h_sub : {e} ⊆ G.edgeFinset := Finset.singleton_subset_iff.mpr he
  rw [Finset.card_sdiff_of_subset h_sub]
  simp

/-- Deleting an edge increases component count by at most 1 (upper bound).
    This is the key lemma: G'.CC ≤ G.CC + 1.
    Proof: Only the G-component containing the edge can split, into at most 2 parts. -/
lemma card_connectedComponent_deleteEdges_add_one [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [Fintype G.ConnectedComponent] [Fintype G.edgeSet]
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    Fintype.card (G.deleteEdges {e}).ConnectedComponent ≤ Fintype.card G.ConnectedComponent + 1 := by
  classical
  haveI : Fintype (G.deleteEdges {e}).ConnectedComponent := inferInstance
  set G' := G.deleteEdges {e} with hG'
  -- Extract endpoints
  rcases Sym2.mk_surjective e with ⟨⟨u, v⟩, huv⟩
  have he_set : e ∈ G.edgeSet := mem_edgeFinset.mp he
  rw [← huv] at he_set
  have hadj : G.Adj u v := he_set
  -- u and v are in the same G-component
  have h_same_G : G.connectedComponentMk u = G.connectedComponentMk v :=
    ConnectedComponent.eq.mpr (Adj.reachable hadj)
  -- The map f : G'.CC → G.CC sends each component to its containing G-component
  let f : G'.ConnectedComponent → G.ConnectedComponent :=
    fun c' => G.connectedComponentMk c'.exists_rep.choose
  -- f is surjective
  have hf_surj : Function.Surjective f := fun c => by
    obtain ⟨w, hw⟩ := c.exists_rep
    use G'.connectedComponentMk w
    simp only [f]
    have h1 := (G'.connectedComponentMk w).exists_rep.choose_spec
    have h2 : G'.Reachable (G'.connectedComponentMk w).exists_rep.choose w :=
      ConnectedComponent.eq.mp h1
    have h3 : G.Reachable (G'.connectedComponentMk w).exists_rep.choose w :=
      h2.mono (deleteEdges_le {e})
    rw [← hw]
    exact ConnectedComponent.eq.mpr h3
  -- From surjectivity: card G.CC ≤ card G'.CC
  have h_le : Fintype.card G.ConnectedComponent ≤ Fintype.card G'.ConnectedComponent :=
    Fintype.card_le_of_surjective f hf_surj
  -- Define injection ψ : G'.CC → G.CC ⊕ Unit
  -- Maps G'.CC of v to inr (), all others to inl (f c')
  -- This gives G'.CC ≤ G.CC + 1
  let ψ : G'.ConnectedComponent → G.ConnectedComponent ⊕ Unit :=
    fun c' => if c' = G'.connectedComponentMk v then Sum.inr () else Sum.inl (f c')
  have hψ_inj : Function.Injective ψ := by
    intro c1 c2 heq
    simp only [ψ] at heq
    by_cases h1 : c1 = G'.connectedComponentMk v <;> by_cases h2 : c2 = G'.connectedComponentMk v
    · exact h1.trans h2.symm
    · simp only [h1, h2, ↓reduceIte] at heq; exact (Sum.noConfusion heq).elim
    · simp only [h1, h2, ↓reduceIte] at heq; exact (Sum.noConfusion heq).elim
    · simp only [h1, h2, ↓reduceIte, Sum.inl.injEq] at heq
      -- f c1 = f c2, need to show c1 = c2
      simp only [f] at heq
      have h_same_G_comp : G.connectedComponentMk c1.exists_rep.choose =
          G.connectedComponentMk c2.exists_rep.choose := heq
      have h_G_reach : G.Reachable c1.exists_rep.choose c2.exists_rep.choose :=
        ConnectedComponent.eq.mp h_same_G_comp
      -- Since c1 ≠ G'.connectedComponentMk v and c2 ≠ G'.connectedComponentMk v,
      -- and they're in the same G-component, they must be G'-connected
      -- (the only way they could be in different G'-components while same G-component
      -- is if one is in v's G'-component)
      -- First, check if the G-component is the one containing the edge
      by_cases h_comp : G.connectedComponentMk c1.exists_rep.choose = G.connectedComponentMk u
      · -- c1 and c2 are in u's (= v's) G-component
        -- Since c1 ≠ G'.connectedComponentMk v and c2 ≠ G'.connectedComponentMk v,
        -- they must both be G'-reachable from u (not from v)
        have hc1_reach_u : G.Reachable c1.exists_rep.choose u := ConnectedComponent.eq.mp h_comp
        have hc2_reach_u : G.Reachable c2.exists_rep.choose u := by
          calc G.connectedComponentMk c2.exists_rep.choose
              = G.connectedComponentMk c1.exists_rep.choose := h_same_G_comp.symm
            _ = G.connectedComponentMk u := h_comp
          exact ConnectedComponent.eq.mp this
        -- If c1.exists_rep.choose is in v's G'-component, then c1 = G'.connectedComponentMk v
        -- which contradicts h1. So c1.exists_rep.choose is G'-reachable from u
        have hc1_G'_u : c1 = G'.connectedComponentMk u ∨ c1 = G'.connectedComponentMk v := by
          -- In G', the component containing u splits into at most 2: u's side and v's side
          -- c1.exists_rep.choose is in one of them
          have hc1_spec := c1.exists_rep.choose_spec
          -- c1 = G'.connectedComponentMk c1.exists_rep.choose
          rw [← hc1_spec]
          -- c1.exists_rep.choose is G-reachable from u
          -- In G', it's either G'-reachable from u or from v
          by_cases h_G'_u : G'.Reachable c1.exists_rep.choose u
          · left; exact ConnectedComponent.eq.mpr h_G'_u
          · -- Not G'-reachable from u means G'-reachable from v
            -- (since they're in the same G-component and edge was removed)
            right
            -- c1.exists_rep.choose and u are G-connected but not G'-connected
            -- The only way is if the edge e = s(u,v) is on all G-paths between them
            -- Since e is removed, c1.exists_rep.choose must be on v's side
            -- Therefore G'.Reachable c1.exists_rep.choose v
            by_contra h_not_v
            push_neg at h_not_v
            have h_not_G'_v : ¬G'.Reachable c1.exists_rep.choose v := by
              intro h; exact h_not_v (ConnectedComponent.eq.mpr h)
            -- c1.exists_rep.choose is not G'-reachable from u or v
            -- But it's G-reachable from u (and thus v)
            -- This means all G-paths from c1.exists_rep.choose to u use edge e
            -- And all G-paths from c1.exists_rep.choose to v use edge e
            -- But that's impossible: if path to u uses e (going through v),
            -- then path to v doesn't need to use e again
            obtain ⟨p⟩ := hc1_reach_u
            -- Check if this path uses e
            by_cases hp : s(u, v) ∈ p.edges
            · -- Path uses e = s(u,v)
              -- Since the path uses e and goes from c1.rep to u,
              -- it visits v at some point. The portion from c1.rep to v
              -- (before crossing e) is a G'-path, so c1.rep is G'-connected to v.
              have hv_in := Walk.snd_mem_support_of_mem_edges p hp
              -- Get prefix walk from c1.rep to v
              have h_reach_v : G.Reachable c1.exists_rep.choose v := p.reachable_of_mem_support hv_in
              -- If this G-path to v doesn't use e, it's a G'-path
              -- Otherwise we can find an alternate path
              -- Key: c1.rep is G-reachable from v, so either G'-reachable to u or to v
              -- Since h_G'_u says not G'-reachable to u, must be G'-reachable to v
              -- But we assumed h_not_G'_v. Contradiction.
              exfalso; exact h_not_G'_v (h_reach_v.mono (deleteEdges_le {e}))
            · -- Path doesn't use e - so it's valid in G'
              exfalso
              apply h_G'_u
              -- Convert p to a G'-walk
              have hp' : ∀ x y, G.Adj x y → s(x, y) ∈ p.edges → G'.Adj x y := by
                intro x y hxy h_in
                simp only [hG', deleteEdges_adj, Set.mem_singleton_iff, huv]
                refine ⟨hxy, ?_⟩
                intro heq; rw [heq] at h_in; exact hp h_in
              exact p.toPath.val.mapLe (deleteEdges_le {e})
        cases hc1_G'_u with
        | inl h => -- c1 = G'.connectedComponentMk u
          have hc2_G'_u : c2 = G'.connectedComponentMk u := by
            -- Similar argument for c2
            have hc2_spec := c2.exists_rep.choose_spec
            rw [← hc2_spec]
            by_cases h_G'_u' : G'.Reachable c2.exists_rep.choose u
            · exact ConnectedComponent.eq.mpr h_G'_u'
            · exfalso
              -- c2 must be G'.connectedComponentMk v, contradicting h2
              have : c2 = G'.connectedComponentMk v := by
                rw [← hc2_spec]
                by_contra h_not_v
                push_neg at h_not_v
                have h_not_G'_v : ¬G'.Reachable c2.exists_rep.choose v := by
                  intro hreach; exact h_not_v (ConnectedComponent.eq.mpr hreach)
                -- c2.rep is G-reachable from u (since same G-component), so G-reachable from v
                -- If not G'-reachable from u or v, contradiction
                have hc2_reach_v : G.Reachable c2.exists_rep.choose v := by
                  have h_same := h_same_G_comp.symm.trans h_comp
                  exact ConnectedComponent.eq.mp (h_same.trans h_same_G)
                exact h_not_G'_v (hc2_reach_v.mono (deleteEdges_le {e}))
              exact h2 this
          exact h.trans hc2_G'_u.symm
        | inr h => exact (h1 h).elim
      · -- c1 and c2 are in a different G-component (not containing the edge)
        -- So removing edge e doesn't affect their connectivity
        -- They remain G'-connected
        obtain ⟨p⟩ := h_G_reach
        -- The path doesn't use edge e (since e connects u,v which are in a different component)
        have hp_no_e : s(u, v) ∉ p.edges := by
          intro h_in
          -- If s(u,v) is in p.edges, then u or v is on the path
          have hu_or_v := Walk.fst_mem_support_of_mem_edges p h_in
          have hv_or_u := Walk.snd_mem_support_of_mem_edges p h_in
          -- All vertices on p are in the same G-component as c1.exists_rep.choose
          have h_same : G.connectedComponentMk (p.getVert 0) = G.connectedComponentMk c1.exists_rep.choose := by
            have : p.getVert 0 = c1.exists_rep.choose := Walk.getVert_zero p
            rw [this]
          have h_all_same : ∀ w ∈ p.support, G.connectedComponentMk w = G.connectedComponentMk c1.exists_rep.choose := by
            intro w hw
            -- w is on the path from c1.rep to c2.rep, so G.Reachable c1.rep w
            have hreach : G.Reachable c1.exists_rep.choose w := by
              -- Get the prefix of the walk up to w
              have ⟨q, _⟩ := p.takeUntil w hw
              exact ⟨q⟩
            exact (ConnectedComponent.eq.mpr hreach).symm
          -- So u is in the same G-component as c1.exists_rep.choose
          have hu_same := h_all_same u hu_or_v
          -- But c1.exists_rep.choose is not in u's G-component (by h_comp)
          exact h_comp hu_same.symm
        -- Build G'-path from G-path
        have h_G'_reach : G'.Reachable c1.exists_rep.choose c2.exists_rep.choose := by
          induction p with
          | nil => exact Reachable.refl _
          | @cons a b c hadj' rest ih =>
            have h_ab : s(a, b) ≠ s(u, v) := by
              intro heq
              apply hp_no_e
              simp only [Walk.edges_cons, List.mem_cons]
              left; exact heq
            have hadj'' : G'.Adj a b := by
              simp only [hG', deleteEdges_adj, Set.mem_singleton_iff, huv]
              exact ⟨hadj', h_ab⟩
            have h_rest_no_e : s(u, v) ∉ rest.edges := by
              intro h_in
              apply hp_no_e
              simp only [Walk.edges_cons, List.mem_cons]
              right; exact h_in
            exact Reachable.trans (Adj.reachable hadj'') (ih h_rest_no_e)
        calc c1 = G'.connectedComponentMk c1.exists_rep.choose := c1.exists_rep.choose_spec.symm
          _ = G'.connectedComponentMk c2.exists_rep.choose := ConnectedComponent.eq.mpr h_G'_reach
          _ = c2 := c2.exists_rep.choose_spec
  have h_card_le : Fintype.card G'.ConnectedComponent ≤ Fintype.card (G.ConnectedComponent ⊕ Unit) :=
    Fintype.card_le_of_injective ψ hψ_inj
  simp only [Fintype.card_sum, Fintype.card_unit] at h_card_le
  exact h_card_le
/-- Deleting an edge can increase component count by at most 1 (lower bound version). -/
lemma card_connectedComponent_deleteEdges_le [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [Fintype G.ConnectedComponent] (e : Sym2 V) :
    Fintype.card G.ConnectedComponent ≤ Fintype.card (G.deleteEdges {e}).ConnectedComponent + 1 := by
  classical
  have hle : G.deleteEdges {e} ≤ G := deleteEdges_le {e}
  let φ : (G.deleteEdges {e}).ConnectedComponent → G.ConnectedComponent :=
    fun c => G.connectedComponentMk c.exists_rep.choose
  have hφ_surj : Function.Surjective φ := fun c => by
    obtain ⟨v, hv⟩ := c.exists_rep
    use (G.deleteEdges {e}).connectedComponentMk v
    simp only [φ]
    have h1 := ((G.deleteEdges {e}).connectedComponentMk v).exists_rep.choose_spec
    have h2 : (G.deleteEdges {e}).Reachable ((G.deleteEdges {e}).connectedComponentMk v).exists_rep.choose v :=
      ConnectedComponent.eq.mp h1
    have h3 : G.Reachable ((G.deleteEdges {e}).connectedComponentMk v).exists_rep.choose v := h2.mono hle
    rw [← hv]
    exact ConnectedComponent.eq.mpr h3
  have h_card_le : Fintype.card G.ConnectedComponent ≤ Fintype.card (G.deleteEdges {e}).ConnectedComponent :=
    Fintype.card_le_of_surjective φ hφ_surj
  exact Nat.le_add_right_of_le h_card_le

/-! ## Spanning Forest Theory -/

/-- Component count bound: in a graph, |E| + c ≥ |V|

This is a standard graph theory result: each connected component with
n_i vertices needs at least n_i - 1 edges to be connected.
Summing: |E| ≥ Σ(n_i - 1) = |V| - c, hence |E| + c ≥ |V|. -/
theorem edges_plus_components_ge_vertices
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent] [Nonempty V] :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent ≥ Fintype.card V := by
  classical
  by_cases h_edge : G.edgeFinset.card = 0
  · -- Base case: No edges means c = |V|
    have h_empty : G.edgeSet = ∅ := by
      have h1 : Fintype.card G.edgeSet = 0 := by rw [← edgeFinset_card]; exact h_edge
      have hempty : IsEmpty G.edgeSet := Fintype.card_eq_zero_iff.mp h1
      exact @Set.eq_empty_of_isEmpty _ G.edgeSet hempty
    have h_eq : Fintype.card G.ConnectedComponent = Fintype.card V := by
      apply Fintype.card_eq.mpr
      refine ⟨⟨fun c => c.exists_rep.choose, G.connectedComponentMk, ?_, ?_⟩⟩
      · intro c; exact c.exists_rep.choose_spec
      · intro v
        have h := (G.connectedComponentMk v).exists_rep.choose_spec
        have h_reach : G.Reachable (G.connectedComponentMk v).exists_rep.choose v :=
          ConnectedComponent.eq.mp h
        obtain ⟨p⟩ := h_reach
        cases hp : p.length with
        | zero => exact Walk.eq_of_length_eq_zero hp
        | succ m =>
          exfalso
          have hadj : G.Adj (p.getVert 0) (p.getVert 1) :=
            p.adj_getVert_succ (by omega : 0 < p.length)
          have h_in_edge : s(p.getVert 0, p.getVert 1) ∈ G.edgeSet := hadj
          rw [h_empty] at h_in_edge
          exact h_in_edge
    rw [h_eq, h_edge]; omega
  · -- Inductive step: At least one edge
    have h_pos : 0 < G.edgeFinset.card := Nat.pos_of_ne_zero h_edge
    have h_nonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp h_pos
    obtain ⟨e, he⟩ := h_nonempty
    let G' := G.deleteEdges {e}
    have h_card' : G'.edgeFinset.card = G.edgeFinset.card - 1 :=
      card_edgeFinset_deleteEdges_singleton G e he
    have h_card_lt : G'.edgeFinset.card < G.edgeFinset.card := by rw [h_card']; omega
    have h_IH : G'.edgeFinset.card + Fintype.card G'.ConnectedComponent ≥ Fintype.card V :=
      edges_plus_components_ge_vertices G'
    -- Key fact: |E| + c' ≥ |V| + 1 (from h_IH and |E'| = |E| - 1)
    have h1 : G.edgeFinset.card + Fintype.card G'.ConnectedComponent ≥ Fintype.card V + 1 := by
      have heq : G.edgeFinset.card = G'.edgeFinset.card + 1 := by rw [h_card']; omega
      calc G.edgeFinset.card + Fintype.card G'.ConnectedComponent
          = G'.edgeFinset.card + 1 + Fintype.card G'.ConnectedComponent := by rw [heq]
        _ = G'.edgeFinset.card + Fintype.card G'.ConnectedComponent + 1 := by omega
        _ ≥ Fintype.card V + 1 := Nat.add_le_add_right h_IH 1
    -- Deleting one edge increases components by at most 1: c' ≤ c + 1
    have h_comp2 : Fintype.card G'.ConnectedComponent ≤ Fintype.card G.ConnectedComponent + 1 :=
      card_connectedComponent_deleteEdges_add_one G e he
    -- From h1: |E| + c' ≥ |V| + 1 and h_comp2: c' ≤ c + 1
    -- We get: |V| + 1 ≤ |E| + c' ≤ |E| + c + 1, thus |V| ≤ |E| + c
    omega
termination_by G.edgeFinset.card

/-! ## Acyclic-Euler Characterization -/

/-- For an acyclic graph (forest): |E| + c = |V|

Each component of a forest is a tree with n_i vertices and n_i - 1 edges.
Summing: |E| = Σ(n_i - 1) = |V| - c, hence |E| + c = |V|. -/
theorem acyclic_euler_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent] [Nonempty V]
    (h_acyc : G.IsAcyclic) :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent = Fintype.card V := by
  classical
  by_cases h_conn : G.Connected
  · -- Connected case: G is a tree
    have h_tree : G.IsTree := ⟨h_conn, h_acyc⟩
    have h_one_comp : Fintype.card G.ConnectedComponent = 1 := by
      rw [Fintype.card_eq_one_iff]
      use G.connectedComponentMk (Classical.arbitrary V)
      intro c
      obtain ⟨v, rfl⟩ := c.exists_rep
      exact ConnectedComponent.eq.mpr (h_conn.preconnected v (Classical.arbitrary V))
    rw [h_one_comp]
    exact h_tree.card_edgeFinset
  · -- Disconnected forest: Use strong induction on edges
    -- In an acyclic graph, every edge is a bridge.
    -- Removing a bridge increases components by 1.
    -- By induction: |E| + c = |V|.
    have h_ge := edges_plus_components_ge_vertices G
    suffices h_le : G.edgeFinset.card + Fintype.card G.ConnectedComponent ≤ Fintype.card V by omega
    -- Induction on number of edges
    induction h_n : G.edgeFinset.card using Nat.strong_induction_on generalizing G with
    | _ n ih =>
      by_cases h_zero : n = 0
      · -- No edges: c = |V|
        subst h_zero
        have h_empty : G.edgeSet = ∅ := by
          have h1 : Fintype.card G.edgeSet = 0 := by rw [← edgeFinset_card]; exact h_n
          have hempty : IsEmpty G.edgeSet := Fintype.card_eq_zero_iff.mp h1
          exact @Set.eq_empty_of_isEmpty _ G.edgeSet hempty
        have h_eq : Fintype.card G.ConnectedComponent = Fintype.card V := by
          apply Fintype.card_eq.mpr
          refine ⟨⟨fun c => c.exists_rep.choose, G.connectedComponentMk, ?_, ?_⟩⟩
          · intro c; exact c.exists_rep.choose_spec
          · intro v
            have h := (G.connectedComponentMk v).exists_rep.choose_spec
            have h_reach : G.Reachable (G.connectedComponentMk v).exists_rep.choose v :=
              ConnectedComponent.eq.mp h
            obtain ⟨p⟩ := h_reach
            cases hp : p.length with
            | zero => exact Walk.eq_of_length_eq_zero hp
            | succ m =>
              exfalso
              have hadj : G.Adj (p.getVert 0) (p.getVert 1) := p.adj_getVert_succ (by omega)
              have h_in : s(p.getVert 0, p.getVert 1) ∈ G.edgeSet := hadj
              rw [h_empty] at h_in
              exact h_in
        rw [h_eq]; omega
      · -- At least one edge - remove it (it's a bridge since acyclic)
        have h_pos : 0 < n := Nat.pos_of_ne_zero h_zero
        have h_edge_pos : 0 < G.edgeFinset.card := by omega
        have h_nonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp h_edge_pos
        obtain ⟨e, he⟩ := h_nonempty
        have he_set : e ∈ G.edgeSet := mem_edgeFinset.mp he
        -- Every edge is a bridge in an acyclic graph
        have h_bridge : ExtendedGraphInfra.IsBridge G e :=
          ExtendedGraphInfra.isAcyclic_isBridge G h_acyc ⟨e, he_set⟩
        -- Bridge removal increases component count by exactly 1
        have h_comp := ExtendedGraphInfra.bridge_splits_component G ⟨e, he_set⟩ h_bridge
        unfold ExtendedGraphInfra.componentCount at h_comp
        -- G' = G.deleteEdges {e}
        set G' := G.deleteEdges {e} with hG'
        have h_card' : G'.edgeFinset.card = n - 1 := by
          have := card_edgeFinset_deleteEdges_singleton G e he
          omega
        have h_acyc' : G'.IsAcyclic := by
          intro w c hc
          exact h_acyc _ (hc.mapLe (deleteEdges_le {e}))
        -- Apply IH
        have h_ge' := edges_plus_components_ge_vertices G'
        have h_ih := ih (n - 1) (by omega) G' h_acyc' h_ge' h_card'
        -- From h_comp: card G'.CC = card G.CC + 1
        -- From h_card': G'.edgeFinset.card = n - 1
        -- From h_ih: (n - 1) + (card G.CC + 1) ≤ |V|
        -- Therefore: n + card G.CC ≤ |V|
        omega

/-- If |E| + c = |V|, the graph is acyclic

Contrapositive: a cycle means one component has ≥ n_i edges (not n_i - 1),
so |E| > |V| - c, contradicting |E| + c = |V|. -/
theorem euler_eq_implies_acyclic'
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent]
    (h_euler : G.edgeFinset.card + Fintype.card G.ConnectedComponent = Fintype.card V) :
    G.IsAcyclic := by
  classical
  by_contra h_not_acyc
  -- If G is not acyclic, there exists a non-bridge edge
  rw [isAcyclic_iff_forall_edge_isBridge] at h_not_acyc
  push_neg at h_not_acyc
  obtain ⟨e, he_edge, he_not_bridge⟩ := h_not_acyc
  -- Get endpoints
  rcases Sym2.mk_surjective e with ⟨⟨u, v⟩, huv⟩
  have hadj : G.Adj u v := by rw [← huv] at he_edge; exact mem_edgeSet.mp he_edge
  -- e is not a bridge, so u and v remain connected after removing e
  rw [← huv, isBridge_iff] at he_not_bridge
  have h_still_reach : (G.deleteEdges {s(u, v)}).Reachable u v := by
    push_neg at he_not_bridge
    exact he_not_bridge hadj
  -- Set up G' = G.deleteEdges {e}
  set G' := G.deleteEdges {e} with hG'
  -- G' has one fewer edge
  have he_mem : e ∈ G.edgeFinset := mem_edgeFinset.mpr he_edge
  have h_fewer : G'.edgeFinset.card = G.edgeFinset.card - 1 :=
    card_edgeFinset_deleteEdges_singleton G e he_mem
  -- Non-bridge: component count stays the same
  -- Define the map f : G'.CC → G.CC
  let f : G'.ConnectedComponent → G.ConnectedComponent :=
    fun c' => G.connectedComponentMk c'.exists_rep.choose
  -- f is surjective
  have hf_surj : Function.Surjective f := fun c => by
    obtain ⟨w, hw⟩ := c.exists_rep
    use G'.connectedComponentMk w
    simp only [f]
    have h1 := (G'.connectedComponentMk w).exists_rep.choose_spec
    have h2 : G'.Reachable (G'.connectedComponentMk w).exists_rep.choose w :=
      ConnectedComponent.eq.mp h1
    have h3 : G.Reachable (G'.connectedComponentMk w).exists_rep.choose w :=
      h2.mono (deleteEdges_le {e})
    rw [← hw]
    exact ConnectedComponent.eq.mpr h3
  -- f is also injective (since e is not a bridge)
  have hf_inj : Function.Injective f := by
    intro c1 c2 hf_eq
    simp only [f] at hf_eq
    have h_G_reach : G.Reachable c1.exists_rep.choose c2.exists_rep.choose :=
      ConnectedComponent.eq.mp hf_eq
    -- Need to convert G-reachability to G'-reachability
    -- Since e is not a bridge, any path using e can be rerouted
    have h_G'_reach : G'.Reachable c1.exists_rep.choose c2.exists_rep.choose := by
      obtain ⟨p⟩ := h_G_reach
      -- Check if path uses edge e
      by_cases h_uses : e ∈ p.edges
      · -- Path uses e - reroute through alternate path
        -- Since e = s(u, v) and u, v are still G'-reachable, we can reroute
        induction p with
        | nil => exact Reachable.refl _
        | @cons x y z hadj' rest ih =>
          by_cases hxy : s(x, y) = e
          · -- This step is the edge e
            -- x and y are endpoints of e (u, v or v, u)
            rw [hxy, huv] at hadj'
            have hxy_eq : (x = u ∧ y = v) ∨ (x = v ∧ y = u) := Sym2.eq_iff.mp (hxy.trans huv)
            -- Get G'-path from x to y via the alternate route
            have h_xy_G' : G'.Reachable x y := by
              rw [hG', huv]
              cases hxy_eq with
              | inl h => rw [h.1, h.2]; exact h_still_reach
              | inr h => rw [h.1, h.2]; exact h_still_reach.symm
            -- Get G'-path from y to z
            have h_yz_G' : G'.Reachable y z := by
              by_cases h_rest_uses : e ∈ rest.edges
              · exact ih (by intro; exact id) h_rest_uses
              · -- rest doesn't use e
                induction rest with
                | nil => exact Reachable.refl _
                | @cons a b c hadj'' rest' ih' =>
                  have h_ab : s(a, b) ≠ e := by
                    intro heq; apply h_rest_uses
                    simp only [Walk.edges_cons, List.mem_cons]
                    left; exact heq
                  have hadj''' : G'.Adj a b := by
                    simp only [hG', deleteEdges_adj, Set.mem_singleton_iff]
                    exact ⟨hadj'', h_ab⟩
                  have h_rest'_no : e ∉ rest'.edges := by
                    intro h_in; apply h_rest_uses
                    simp only [Walk.edges_cons, List.mem_cons]
                    right; exact h_in
                  exact Reachable.trans (Adj.reachable hadj''') (ih' h_rest'_no)
            exact Reachable.trans h_xy_G' h_yz_G'
          · -- This step is not e
            have hadj'' : G'.Adj x y := by
              simp only [hG', deleteEdges_adj, Set.mem_singleton_iff]
              exact ⟨hadj', hxy⟩
            have h_rest_case : e ∈ rest.edges := by
              simp only [Walk.edges_cons, List.mem_cons] at h_uses
              cases h_uses with
              | inl h => exact (hxy h).elim
              | inr h => exact h
            have h_yz := ih (by intro; exact id) h_rest_case
            exact Reachable.trans (Adj.reachable hadj'') h_yz
      · -- Path doesn't use e
        induction p with
        | nil => exact Reachable.refl _
        | @cons a b c hadj' rest ih =>
          have h_ab : s(a, b) ≠ e := by
            intro heq; apply h_uses
            simp only [Walk.edges_cons, List.mem_cons]
            left; exact heq
          have hadj'' : G'.Adj a b := by
            simp only [hG', deleteEdges_adj, Set.mem_singleton_iff]
            exact ⟨hadj', h_ab⟩
          have h_rest_no : e ∉ rest.edges := by
            intro h_in; apply h_uses
            simp only [Walk.edges_cons, List.mem_cons]
            right; exact h_in
          exact Reachable.trans (Adj.reachable hadj'') (ih h_rest_no)
    calc c1 = G'.connectedComponentMk c1.exists_rep.choose := c1.exists_rep.choose_spec.symm
      _ = G'.connectedComponentMk c2.exists_rep.choose := ConnectedComponent.eq.mpr h_G'_reach
      _ = c2 := c2.exists_rep.choose_spec
  -- f is bijective, so component counts are equal
  have h_bij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
  have h_same_comp : Fintype.card G.ConnectedComponent = Fintype.card G'.ConnectedComponent :=
    (Fintype.card_of_bijective h_bij).symm
  -- Now derive contradiction
  -- First establish Nonempty V from h_euler
  have h_nonempty : Nonempty V := by
    by_contra h_empty
    push_neg at h_empty
    simp only [not_nonempty_iff] at h_empty
    have : Fintype.card V = 0 := Fintype.card_eq_zero
    omega
  haveI : Nonempty V := h_nonempty
  -- |E'| + c' >= |V| (by edges_plus_components_ge_vertices)
  have h_ge := edges_plus_components_ge_vertices G'
  -- |E'| = |E| - 1 and c' = c
  -- So (|E| - 1) + c >= |V|
  -- But |E| + c = |V| (by h_euler)
  -- So |V| - 1 >= |V|, contradiction
  have h_edge_pos : G.edgeFinset.card > 0 := by
    exact Finset.card_pos.mpr ⟨e, he_mem⟩
  rw [h_fewer, ← h_same_comp] at h_ge
  omega

/-- Combined characterization: acyclic ↔ |E| + c = |V| -/
theorem acyclic_iff_euler
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent] [Nonempty V] :
    G.IsAcyclic ↔ G.edgeFinset.card + Fintype.card G.ConnectedComponent = Fintype.card V := by
  constructor
  · exact acyclic_euler_eq G
  · exact euler_eq_implies_acyclic' G

end Infrastructure
