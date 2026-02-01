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
import Infrastructure.ExtendedGraphInfra

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

/-- Helper: converting walks when edge sets are equal -/
private def walk_deleteEdges_eq {G : SimpleGraph V} {e₁ e₂ : Sym2 V} (heq : e₁ = e₂)
    {a b : V} (p : (G.deleteEdges {e₁}).Walk a b) : (G.deleteEdges {e₂}).Walk a b :=
  heq ▸ p

/-- Helper: convert Reachable proof when graphs are equal -/
private def reachable_cast {G1 G2 : SimpleGraph V} (heq : G1 = G2)
    {a b : V} (h : G1.Reachable a b) : G2.Reachable a b := heq ▸ h

/-- Helper: if a walk uses edge e, at least one of the takeUntil prefixes doesn't use e. -/
private lemma takeUntil_first_endpoint_no_edge [DecidableEq V] (G : SimpleGraph V)
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
    -- h_lt uses a different membership proof, but the walk is the same (proof irrelevance)
    omega
  · right
    push_neg at h
    intro h_in
    have hu_in_prefix := Walk.fst_mem_support_of_mem_edges _ h_in
    -- u in prefix to v means length(takeUntil u) < length(takeUntil v)
    have h_lt := Walk.length_takeUntil_lt hu_in_prefix hne
    simp only [Walk.takeUntil_takeUntil] at h_lt
    omega

/-- Deleting an edge increases component count by at most 1 (upper bound).
    This is the key lemma: G'.CC ≤ G.CC + 1.
    Proof: Only the G-component containing the edge can split, into at most 2 parts. -/
lemma card_connectedComponent_deleteEdges_add_one [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [Fintype G.ConnectedComponent] [Fintype G.edgeSet]
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    Fintype.card (G.deleteEdges {e}).ConnectedComponent ≤ Fintype.card G.ConnectedComponent + 1 := by
  classical
  -- Extract endpoints of e
  rcases Sym2.mk_surjective e with ⟨⟨u, v⟩, huv⟩
  have he_set : e ∈ G.edgeSet := mem_edgeFinset.mp he
  rw [← huv] at he_set
  have hadj : G.Adj u v := he_set
  have hne : u ≠ v := hadj.ne
  -- Define G' and the key maps
  set G' := G.deleteEdges {e} with hG'
  -- Map from G'.CC to G.CC ⊕ Unit: sends v's component to inr (), others to inl
  let ψ : G'.ConnectedComponent → G.ConnectedComponent ⊕ Unit :=
    fun c' => if c' = G'.connectedComponentMk v then Sum.inr ()
              else Sum.inl (G.connectedComponentMk c'.exists_rep.choose)
  -- ψ is injective
  have hψ_inj : Function.Injective ψ := by
    intro c1 c2 heq
    simp only [ψ] at heq
    by_cases h1 : c1 = G'.connectedComponentMk v <;> by_cases h2 : c2 = G'.connectedComponentMk v
    · exact h1.trans h2.symm
    · simp only [h1, h2, ↓reduceIte, reduceCtorEq] at heq
    · simp only [h1, h2, ↓reduceIte, reduceCtorEq] at heq
    · simp only [h1, h2, ↓reduceIte, Sum.inl.injEq] at heq
      -- c1 and c2 are in the same G-component, neither is v's G'-component
      have h_G_reach : G.Reachable c1.exists_rep.choose c2.exists_rep.choose :=
        ConnectedComponent.eq.mp heq
      have hc1_not_v : ¬G'.Reachable c1.exists_rep.choose v := by
        intro hreach
        exact h1 (c1.exists_rep.choose_spec.symm.trans (ConnectedComponent.eq.mpr hreach))
      have hc2_not_v : ¬G'.Reachable c2.exists_rep.choose v := by
        intro hreach
        exact h2 (c2.exists_rep.choose_spec.symm.trans (ConnectedComponent.eq.mpr hreach))
      -- Get a G-path and convert to G'-path
      obtain ⟨p⟩ := h_G_reach
      by_cases hp : s(u, v) ∈ p.edges
      · -- Path uses e, need to find alternate route via u
        have hu_in := Walk.fst_mem_support_of_mem_edges p hp
        have hv_in := Walk.snd_mem_support_of_mem_edges p hp
        -- Use helper lemma: one of the takeUntils doesn't use e
        rcases takeUntil_first_endpoint_no_edge G p hp hu_in hv_in hne with h_pu | h_pv
        · -- Prefix to u doesn't use e
          have h1' : G'.Reachable c1.exists_rep.choose u :=
            ⟨walk_deleteEdges_eq huv ((p.takeUntil u hu_in).toDeleteEdge (s(u,v)) h_pu)⟩
          -- Similarly get path from u to c2
          let qu := p.dropUntil u hu_in
          by_cases hqu : s(u, v) ∈ qu.edges
          · -- Suffix uses e, so goes through v, but c2 not in v's component
            have hv_qu := Walk.snd_mem_support_of_mem_edges qu hqu
            let qv := qu.dropUntil v hv_qu
            by_cases hqv : s(u, v) ∈ qv.edges
            · -- Edge appears multiple times; use reverse walk approach
              -- Consider the reverse walk from c2.rep to c1.rep
              let p' := p.reverse
              have hp' : s(u, v) ∈ p'.edges := Walk.edges_reverse p ▸ List.mem_reverse.mpr hp
              have hu_in' : u ∈ p'.support := Walk.support_reverse p ▸ List.mem_reverse.mpr hu_in
              have hv_in' : v ∈ p'.support := Walk.support_reverse p ▸ List.mem_reverse.mpr hv_in
              rcases takeUntil_first_endpoint_no_edge G p' hp' hu_in' hv_in' hne with h_pu' | h_pv'
              · -- Prefix to u doesn't use edge, G'-path from c2.rep to u
                have h2' : G'.Reachable c2.exists_rep.choose u :=
                  ⟨walk_deleteEdges_eq huv ((p'.takeUntil u hu_in').toDeleteEdge (s(u,v)) h_pu')⟩
                have h_G'_reach : G'.Reachable c1.exists_rep.choose c2.exists_rep.choose :=
                  h1'.trans h2'.symm
                calc c1 = G'.connectedComponentMk c1.exists_rep.choose := c1.exists_rep.choose_spec.symm
                  _ = G'.connectedComponentMk c2.exists_rep.choose := ConnectedComponent.eq.mpr h_G'_reach
                  _ = c2 := c2.exists_rep.choose_spec
              · -- Prefix to v doesn't use edge, G'-path from c2.rep to v
                have h2' : G'.Reachable c2.exists_rep.choose v :=
                  ⟨walk_deleteEdges_eq huv ((p'.takeUntil v hv_in').toDeleteEdge (s(u,v)) h_pv')⟩
                exact absurd h2' hc2_not_v
            · have h2' : (G.deleteEdges {e}).Reachable v c2.exists_rep.choose :=
                ⟨walk_deleteEdges_eq huv (qv.toDeleteEdge (s(u,v)) hqv)⟩
              exact absurd (reachable_cast hG'.symm h2').symm hc2_not_v
          · have h2' : (G.deleteEdges {e}).Reachable u c2.exists_rep.choose :=
              ⟨walk_deleteEdges_eq huv (qu.toDeleteEdge (s(u,v)) hqu)⟩
            have h2'_G' : G'.Reachable u c2.exists_rep.choose := reachable_cast hG'.symm h2'
            have h_G'_reach : G'.Reachable c1.exists_rep.choose c2.exists_rep.choose :=
              h1'.trans h2'_G'
            calc c1 = G'.connectedComponentMk c1.exists_rep.choose := c1.exists_rep.choose_spec.symm
              _ = G'.connectedComponentMk c2.exists_rep.choose := ConnectedComponent.eq.mpr h_G'_reach
              _ = c2 := c2.exists_rep.choose_spec
        · -- Prefix to v doesn't use e, but c1 not in v's component - contradiction
          have h1' : (G.deleteEdges {e}).Reachable c1.exists_rep.choose v :=
            ⟨walk_deleteEdges_eq huv ((p.takeUntil v hv_in).toDeleteEdge (s(u,v)) h_pv)⟩
          exact absurd (reachable_cast hG'.symm h1') hc1_not_v
      · -- Path doesn't use e, convert directly
        have h_G'_reach : G'.Reachable c1.exists_rep.choose c2.exists_rep.choose :=
          ⟨walk_deleteEdges_eq huv (p.toDeleteEdge (s(u,v)) hp)⟩
        calc c1 = G'.connectedComponentMk c1.exists_rep.choose := c1.exists_rep.choose_spec.symm
          _ = G'.connectedComponentMk c2.exists_rep.choose := ConnectedComponent.eq.mpr h_G'_reach
          _ = c2 := c2.exists_rep.choose_spec
  have h_card_le : Fintype.card G'.ConnectedComponent ≤ Fintype.card (G.ConnectedComponent ⊕ Unit) :=
    Fintype.card_le_of_injective ψ hψ_inj
  simp only [Fintype.card_sum, Fintype.card_unit] at h_card_le
  convert h_card_le
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
        -- Simplify: ↑⟨e, he_set⟩ = e
        simp only [Subtype.coe_mk] at h_comp
        -- h_comp : Fintype.card (G.deleteEdges {e}).ConnectedComponent = Fintype.card G.ConnectedComponent + 1
        have h_acyc' : (G.deleteEdges {e}).IsAcyclic :=
          ExtendedGraphInfra.deleteEdges_isAcyclic G {e} h_acyc
        have h_card' : (G.deleteEdges {e}).edgeFinset.card = n - 1 := by
          have := card_edgeFinset_deleteEdges_singleton G e he
          omega
        have h_lt : (G.deleteEdges {e}).edgeFinset.card < n := by omega
        -- G' is not connected (bridge removal creates ≥ 2 components)
        have h_not_conn' : ¬(G.deleteEdges {e}).Connected := by
          intro hc
          have h1 : Fintype.card (G.deleteEdges {e}).ConnectedComponent = 1 := by
            rw [Fintype.card_eq_one_iff]
            use (G.deleteEdges {e}).connectedComponentMk (Classical.arbitrary V)
            intro c
            obtain ⟨v, rfl⟩ := c.exists_rep
            exact ConnectedComponent.eq.mpr (hc.preconnected v (Classical.arbitrary V))
          have h2 : Fintype.card G.ConnectedComponent ≥ 1 := Fintype.card_pos
          omega
        -- Apply IH (strong induction: just need m < n, acyclic, and not connected)
        have h_IH := ih (G.deleteEdges {e}).edgeFinset.card h_lt
          (G.deleteEdges {e}) h_acyc' h_not_conn'
        -- h_IH : (G.deleteEdges {e}).edgeFinset.card + Fintype.card (G.deleteEdges {e}).ConnectedComponent ≤ Fintype.card V
        -- Rewrite using h_card' and h_comp, then conclude
        rw [h_card'] at h_IH
        rw [h_comp] at h_IH
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
  have hadj : G.Adj u v := by rw [← huv] at he_edge; exact he_edge
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
    -- Since e is not a bridge, any path using e can be rerouted via h_still_reach
    have h_G'_reach : G'.Reachable c1.exists_rep.choose c2.exists_rep.choose := by
      obtain ⟨p⟩ := h_G_reach
      by_cases hp : s(u, v) ∈ p.edges
      · -- Path uses edge e = s(u,v), need to reroute
        have hu_in : u ∈ p.support := Walk.fst_mem_support_of_mem_edges p hp
        have hv_in : v ∈ p.support := Walk.snd_mem_support_of_mem_edges p hp
        -- Take prefixes to u and v
        let pu := p.takeUntil u hu_in
        let pv := p.takeUntil v hv_in
        have hne : u ≠ v := hadj.ne
        -- At least one prefix doesn't use s(u,v) (whichever endpoint appears first)
        by_cases hpu : s(u, v) ∈ pu.edges
        · -- pu uses s(u,v), so v appears before u in p
          -- Therefore pv doesn't use s(u,v)
          have hpv : s(u, v) ∉ pv.edges := by
            intro h
            -- Both pu and pv contain edge s(u,v), contradicting takeUntil_first_endpoint_no_edge
            have hcontra := takeUntil_first_endpoint_no_edge G p hp hu_in hv_in hne
            cases hcontra with
            | inl h_not_pu => exact h_not_pu hpu
            | inr h_not_pv => exact h_not_pv h
          -- G'-path from c1.rep to v
          have h1 : G'.Reachable c1.exists_rep.choose v :=
            ⟨walk_deleteEdges_eq huv (pv.toDeleteEdge (s(u,v)) hpv)⟩
          -- G'-path from v to u (since e is not a bridge)
          have h2 : G'.Reachable v u :=
            ⟨walk_deleteEdges_eq huv (Classical.choice h_still_reach).reverse⟩
          -- G'-path from u to c2.rep: use dropUntil
          let qu := p.dropUntil u hu_in
          by_cases hqu : s(u, v) ∈ qu.edges
          · -- qu uses s(u,v), handle via v using reverse
            let p' := p.reverse
            have hp' : s(u, v) ∈ p'.edges := Walk.edges_reverse p ▸ List.mem_reverse.mpr hp
            have hv_in' : v ∈ p'.support := Walk.support_reverse p ▸ List.mem_reverse.mpr hv_in
            let rv := p'.takeUntil v hv_in'
            by_cases hrv : s(u, v) ∈ rv.edges
            · -- Both rv and (implicitly) the forward path hit the edge
              -- Use takeUntil_first_endpoint_no_edge on p' to get alternate path
              have hu_in' : u ∈ p'.support := Walk.fst_mem_support_of_mem_edges p' hp'
              have hcontra := takeUntil_first_endpoint_no_edge G p' hp' hu_in' hv_in' hne
              -- Since hrv : s(u,v) ∈ rv.edges, the right disjunct is false
              let ru' := p'.takeUntil u hu_in'
              have hru'_no_e : s(u, v) ∉ ru'.edges := by
                cases hcontra with
                | inl h_not => exact h_not
                | inr h_not_rv => exact absurd hrv h_not_rv
              -- G'-path from c2.rep to u
              have h3 : (G.deleteEdges {e}).Reachable c2.exists_rep.choose u :=
                ⟨walk_deleteEdges_eq huv (ru'.toDeleteEdge (s(u,v)) hru'_no_e)⟩
              -- Chain: c1.rep ->h1-> v ->h2-> u <-h3.symm- c2.rep
              exact h1.trans (h2.trans (reachable_cast hG'.symm h3).symm)
            · -- rv doesn't use s(u,v), so G'-path from c2.rep to v
              have h3 : (G.deleteEdges {e}).Reachable c2.exists_rep.choose v :=
                ⟨walk_deleteEdges_eq huv (rv.toDeleteEdge (s(u,v)) hrv)⟩
              -- Chain: c1.rep ->h1-> v ->(h3.symm)-> c2.rep
              exact h1.trans (reachable_cast hG'.symm h3).symm
          · -- qu doesn't use s(u,v), so G'-path from u to c2.rep
            have h3 : (G.deleteEdges {e}).Reachable u c2.exists_rep.choose :=
              ⟨walk_deleteEdges_eq huv (qu.toDeleteEdge (s(u,v)) hqu)⟩
              -- Chain: c1.rep ->h1-> v ->h2-> u ->h3-> c2.rep
            exact h1.trans (h2.trans (reachable_cast hG'.symm h3))
        · -- pu doesn't use s(u,v), so G'-path from c1.rep to u
          have h1 : (G.deleteEdges {e}).Reachable c1.exists_rep.choose u :=
            ⟨walk_deleteEdges_eq huv (pu.toDeleteEdge (s(u,v)) hpu)⟩
          -- G'-path from u to v (since e is not a bridge)
          have h2 : (G.deleteEdges {e}).Reachable u v :=
            ⟨walk_deleteEdges_eq huv (Classical.choice h_still_reach)⟩
          -- G'-path from v to c2.rep: use dropUntil
          let qv := p.dropUntil v hv_in
          by_cases hqv : s(u, v) ∈ qv.edges
          · -- qv uses s(u,v), handle via u using reverse
            let p' := p.reverse
            have hp' : s(u, v) ∈ p'.edges := Walk.edges_reverse p ▸ List.mem_reverse.mpr hp
            have hu_in' : u ∈ p'.support := Walk.support_reverse p ▸ List.mem_reverse.mpr hu_in
            let ru := p'.takeUntil u hu_in'
            by_cases hru : s(u, v) ∈ ru.edges
            · -- ru uses s(u,v), use takeUntil_first_endpoint_no_edge to get path via v
              have hv_in' : v ∈ p'.support := Walk.snd_mem_support_of_mem_edges p' hp'
              have hcontra := takeUntil_first_endpoint_no_edge G p' hp' hu_in' hv_in' hne
              -- Since hru : s(u,v) ∈ ru.edges, the left disjunct is false
              let rv' := p'.takeUntil v hv_in'
              have hrv'_no_e : s(u, v) ∉ rv'.edges := by
                cases hcontra with
                | inl h_not_ru => exact absurd hru h_not_ru
                | inr h_not => exact h_not
              -- G'-path from c2.rep to v
              have h3 : (G.deleteEdges {e}).Reachable c2.exists_rep.choose v :=
                ⟨walk_deleteEdges_eq huv (rv'.toDeleteEdge (s(u,v)) hrv'_no_e)⟩
              -- Chain: c1.rep ->h1-> u ->h2-> v <-h3.symm- c2.rep
              exact (reachable_cast hG'.symm h1).trans ((reachable_cast hG'.symm h2).trans (reachable_cast hG'.symm h3).symm)
            · -- ru doesn't use s(u,v), so G'-path from c2.rep to u
              have h3 : (G.deleteEdges {e}).Reachable c2.exists_rep.choose u :=
                ⟨walk_deleteEdges_eq huv (ru.toDeleteEdge (s(u,v)) hru)⟩
              -- Chain: c1.rep ->h1-> u ->(h3.symm)-> c2.rep
              exact (reachable_cast hG'.symm h1).trans (reachable_cast hG'.symm h3).symm
          · -- qv doesn't use s(u,v), so G'-path from v to c2.rep
            have h3 : (G.deleteEdges {e}).Reachable v c2.exists_rep.choose :=
              ⟨walk_deleteEdges_eq huv (qv.toDeleteEdge (s(u,v)) hqv)⟩
            -- Chain: c1.rep ->h1-> u ->h2-> v ->h3-> c2.rep
            exact (reachable_cast hG'.symm h1).trans ((reachable_cast hG'.symm h2).trans (reachable_cast hG'.symm h3))
      · -- Path doesn't use edge e, convert directly
        have h_G'_reach : G'.Reachable c1.exists_rep.choose c2.exists_rep.choose :=
          ⟨walk_deleteEdges_eq huv (p.toDeleteEdge (s(u,v)) hp)⟩
        exact h_G'_reach
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
    rw [not_nonempty_iff] at h_empty
    have hV : Fintype.card V = 0 := Fintype.card_eq_zero
    rw [hV] at h_euler
    -- h_euler: G.edgeFinset.card + Fintype.card G.ConnectedComponent = 0
    -- This means both are 0, but edge count ≥ 1 since we have edge e
    have he' : e ∈ G.edgeFinset := mem_edgeFinset.mpr he_edge
    have : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨e, he'⟩
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
