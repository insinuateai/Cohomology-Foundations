/-
# Extended Graph Infrastructure for Cohomology

Extends Infrastructure/GraphTheoryUtils.lean with additional proven lemmas
for TreeGraphInfra.lean and the H¹ characterization theorems.

Targets: Mathlib 4.27.0 / Lean 4.27.0

## What This Provides

1. Empty graph component characterization (PROVEN)
2. Edge removal machinery (PROVEN)
3. Walk monotonicity and lifting (PROVEN)
4. Subgraph acyclicity preservation (PROVEN)
5. Reachability lemmas (PROVEN)
6. Bridge detection and characterization (PROVEN)
7. Component count bounds (PARTIAL - key lemma stated)

SORRIES: 0
AXIOMS: 0 (bridge_splits_component_aux now proven)

Author: Tenured Cohomology Foundations
Date: January 2026
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

namespace ExtendedGraphInfra

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Section 1: Definitions -/

/-- Edge count using edgeFinset -/
noncomputable def edgeCount (G : SimpleGraph V) [Fintype G.edgeSet] : ℕ :=
  G.edgeFinset.card

/-- Component count -/
noncomputable def componentCount (G : SimpleGraph V) [Fintype G.ConnectedComponent] : ℕ :=
  Fintype.card G.ConnectedComponent

/-- Vertex count -/
def vertexCount : ℕ := Fintype.card V

/-! ## Section 2: Empty Graph - FULLY PROVEN -/

/-- In the empty graph, v and w in same component iff v = w -/
theorem bot_connectedComponent_eq_iff (v w : V) :
    (⊥ : SimpleGraph V).connectedComponentMk v = (⊥ : SimpleGraph V).connectedComponentMk w ↔ v = w := by
  constructor
  · intro h
    rw [ConnectedComponent.eq] at h
    obtain ⟨p⟩ := h
    cases p with
    | nil => rfl
    | cons hadj _ => exact absurd hadj (by simp [SimpleGraph.bot_adj])
  · intro h; rw [h]

/-- Empty graph: components biject with vertices -/
theorem bot_components_bijective :
    Function.Bijective (⊥ : SimpleGraph V).connectedComponentMk := by
  constructor
  · -- Injective
    intro v w h
    exact (bot_connectedComponent_eq_iff v w).mp h
  · -- Surjective
    intro c
    obtain ⟨v, rfl⟩ := c.exists_rep
    exact ⟨v, rfl⟩

/-- Empty graph: component count = vertex count -/
theorem bot_componentCount [Fintype (⊥ : SimpleGraph V).ConnectedComponent] :
    componentCount (⊥ : SimpleGraph V) = vertexCount (V := V) := by
  unfold componentCount vertexCount
  have e : V ≃ (⊥ : SimpleGraph V).ConnectedComponent :=
    Equiv.ofBijective (⊥ : SimpleGraph V).connectedComponentMk bot_components_bijective
  exact (Fintype.card_congr e).symm

/-- Empty graph has 0 edges -/
theorem bot_edgeCount [Fintype (⊥ : SimpleGraph V).edgeSet] :
    edgeCount (⊥ : SimpleGraph V) = 0 := by
  unfold edgeCount
  have : (⊥ : SimpleGraph V).edgeFinset = ∅ := by
    ext e
    simp only [mem_edgeFinset, edgeSet_bot, Set.mem_empty_iff_false]
    simp
  rw [this, Finset.card_empty]

/-- Empty graph: |E| + c = |V| -/
theorem bot_euler [Fintype (⊥ : SimpleGraph V).edgeSet]
    [Fintype (⊥ : SimpleGraph V).ConnectedComponent] :
    edgeCount (⊥ : SimpleGraph V) + componentCount (⊥ : SimpleGraph V) = vertexCount (V := V) := by
  rw [bot_edgeCount, bot_componentCount, zero_add]

/-! ## Section 3: Connected Graph - FULLY PROVEN -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Connected graph has exactly 1 component -/
theorem connected_componentCount_eq_one [Fintype G.ConnectedComponent] (h : G.Connected) :
    componentCount G = 1 := by
  unfold componentCount
  have hne : Nonempty V := h.nonempty
  rw [Fintype.card_eq_one_iff]
  use G.connectedComponentMk (Classical.arbitrary V)
  intro c
  obtain ⟨v, rfl⟩ := c.exists_rep
  exact ConnectedComponent.eq.mpr (h.preconnected v _)

/-- Tree: |E| + 1 = |V| -/
theorem tree_edgeCount [Fintype G.edgeSet] [Nonempty V] (h : G.IsTree) :
    edgeCount G + 1 = vertexCount (V := V) := by
  unfold edgeCount vertexCount
  exact h.card_edgeFinset

/-- Tree satisfies |E| + c = |V| (since c = 1) -/
theorem tree_euler [Fintype G.edgeSet] [Fintype G.ConnectedComponent] [Nonempty V]
    (h : G.IsTree) :
    edgeCount G + componentCount G = vertexCount (V := V) := by
  have h1 := tree_edgeCount G h
  have h2 := connected_componentCount_eq_one G h.1
  omega

/-! ## Section 4: Edge Removal - FULLY PROVEN -/

/-- edgeFinset of deleteEdges is the set difference -/
theorem deleteEdges_edgeFinset_eq (s : Set (Sym2 V)) [Fintype G.edgeSet]
    [Fintype (G.deleteEdges s).edgeSet] [DecidablePred (· ∈ s)] :
    (G.deleteEdges s).edgeFinset = G.edgeFinset.filter (· ∉ s) := by
  ext e
  simp only [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_diff, Finset.mem_filter]

/-- Removing a single edge: edgeFinset is erase -/
theorem deleteEdges_singleton_edgeFinset (e : Sym2 V) [Fintype G.edgeSet]
    [Fintype (G.deleteEdges {e}).edgeSet] (he : e ∈ G.edgeSet) :
    (G.deleteEdges {e}).edgeFinset = G.edgeFinset.erase e := by
  ext e'
  simp only [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_erase]
  tauto

/-- Removing edge decreases count by 1 -/
theorem deleteEdges_singleton_card (e : Sym2 V) [Fintype G.edgeSet]
    [Fintype (G.deleteEdges {e}).edgeSet] (he : e ∈ G.edgeSet) :
    (G.deleteEdges {e}).edgeFinset.card + 1 = G.edgeFinset.card := by
  have h1 : e ∈ G.edgeFinset := mem_edgeFinset.mpr he
  rw [deleteEdges_singleton_edgeFinset G e he, Finset.card_erase_of_mem h1]
  have hpos : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨e, h1⟩
  omega

/-- Edge removal strictly decreases edge count -/
theorem deleteEdges_singleton_card_lt (e : Sym2 V) [Fintype G.edgeSet]
    [Fintype (G.deleteEdges {e}).edgeSet] (he : e ∈ G.edgeSet) :
    (G.deleteEdges {e}).edgeFinset.card < G.edgeFinset.card := by
  have h := deleteEdges_singleton_card G e he
  omega

/-! ## Section 5: Monotonicity - FULLY PROVEN -/

/-- deleteEdges gives subgraph -/
theorem deleteEdges_le (s : Set (Sym2 V)) : G.deleteEdges s ≤ G := by
  intro v w h
  exact h.1

/-- Adjacency lifts from subgraph to supergraph -/
theorem adj_of_le {H : SimpleGraph V} (hle : G ≤ H) {v w : V} (h : G.Adj v w) :
    H.Adj v w := hle h

/-- Reachability lifts from subgraph to supergraph -/
theorem reachable_of_le {H : SimpleGraph V} (hle : G ≤ H) {v w : V}
    (h : G.Reachable v w) : H.Reachable v w := by
  obtain ⟨p⟩ := h
  exact ⟨p.mapLe hle⟩

/-- Connected lifts from subgraph to supergraph -/
theorem connected_of_le {H : SimpleGraph V} (hle : G ≤ H) (h : G.Connected) :
    H.Connected := by
  haveI : Nonempty V := h.nonempty
  exact Connected.mk (fun v w => reachable_of_le G hle (h v w))

/-! ## Section 6: Acyclicity Preservation - FULLY PROVEN -/

/-- Subgraph of acyclic is acyclic -/
theorem isAcyclic_of_le {H : SimpleGraph V} (hle : G ≤ H) (hH : H.IsAcyclic) :
    G.IsAcyclic := by
  intro v p hp
  exact hH (p.mapLe hle) (hp.mapLe hle)

/-- deleteEdges preserves acyclicity -/
theorem deleteEdges_isAcyclic (s : Set (Sym2 V)) (h : G.IsAcyclic) :
    (G.deleteEdges s).IsAcyclic := by
  have hle : G.deleteEdges s ≤ G := deleteEdges_le G s
  intro v p hp
  exact h (p.mapLe hle) (hp.mapLe hle)

/-! ## Section 7: Reachability - FULLY PROVEN -/

/-- Same component iff reachable -/
theorem connectedComponent_eq_iff_reachable (v w : V) :
    G.connectedComponentMk v = G.connectedComponentMk w ↔ G.Reachable v w :=
  ConnectedComponent.eq

/-- In connected graph, all pairs reachable -/
theorem connected_reachable (h : G.Connected) (v w : V) : G.Reachable v w :=
  h v w

/-- In tree, all pairs reachable -/
theorem tree_reachable (h : G.IsTree) (v w : V) : G.Reachable v w :=
  h.1 v w

/-! ## Section 8: Bridge Definition - FULLY PROVEN -/

/-- An edge is a bridge if removing it disconnects its endpoints -/
def IsBridge (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ ∃ v w, s(v, w) = e ∧ ¬(G.deleteEdges {e}).Reachable v w

/-- Equivalent: edge e with endpoints v, w is a bridge iff removing disconnects them -/
theorem isBridge_iff (v w : V) (h_adj : G.Adj v w) :
    IsBridge G s(v, w) ↔ ¬(G.deleteEdges {s(v, w)}).Reachable v w := by
  unfold IsBridge
  constructor
  · intro ⟨_, v', w', he, hr⟩
    -- he : s(v', w') = s(v, w)
    have hvw : (v' = v ∧ w' = w) ∨ (v' = w ∧ w' = v) := Sym2.eq_iff.mp he
    cases hvw with
    | inl h =>
      obtain ⟨hv, hw⟩ := h
      subst hv hw
      exact hr
    | inr h =>
      obtain ⟨hv, hw⟩ := h
      subst hv hw
      exact fun hr' => hr (hr'.symm)
  · intro h
    exact ⟨G.mem_edgeSet.mpr h_adj, v, w, rfl, h⟩

/-- In acyclic graph, every edge is a bridge -/
theorem isAcyclic_isBridge (h_acyc : G.IsAcyclic) (e : G.edgeSet) :
    IsBridge G e.val := by
  -- Get endpoints of the edge
  have ⟨v, w, hvw⟩ : ∃ v w, s(v, w) = e.val := Sym2.ind (fun v w => ⟨v, w, rfl⟩) e.val
  refine ⟨e.property, v, w, hvw, ?_⟩
  -- Use Mathlib's isAcyclic_iff_forall_edge_isBridge
  have h_mathlib_bridge : G.IsBridge e.val := isAcyclic_iff_forall_edge_isBridge.mp h_acyc e.property
  -- Extract the non-reachability from Mathlib's IsBridge
  obtain ⟨_, h_not_reach⟩ := h_mathlib_bridge
  rw [← hvw] at h_not_reach ⊢
  simp only [Sym2.lift_mk] at h_not_reach
  -- h_not_reach : ¬(G \ fromEdgeSet {s(v, w)}).Reachable v w
  -- Need to show: ¬(G.deleteEdges {s(v, w)}).Reachable v w
  intro h_reach
  apply h_not_reach
  -- Show (G \ fromEdgeSet {s(v, w)}).Reachable v w from (G.deleteEdges {s(v, w)}).Reachable v w
  have h_le : G.deleteEdges {s(v, w)} ≤ G \ fromEdgeSet {s(v, w)} := by
    intro u v' huv
    rw [deleteEdges_adj] at huv
    rw [sdiff_adj]
    constructor
    · exact huv.1
    · intro h_from
      simp only [Set.mem_singleton_iff] at huv
      exact huv.2 h_from.1
  obtain ⟨p⟩ := h_reach
  exact ⟨p.mapLe h_le⟩

/-! ## Section 9: Component Splitting -/

/-- Convert a G-walk to a G'-walk when all edges are in G'.edgeSet -/
private theorem walk_to_G'_reachable {G : SimpleGraph V} [DecidableRel G.Adj]
    {G' : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (h_edges : ∀ e ∈ p.edges, e ∈ G'.edgeSet) : G'.Reachable u v := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons a b c hadj_ab p' ih =>
    have h_ab_G' : G'.Adj a b := by
      have he : s(a, b) ∈ (Walk.cons hadj_ab p').edges := by
        simp only [Walk.edges_cons, List.mem_cons, true_or]
      exact h_edges s(a, b) he
    have h_rest : ∀ e ∈ p'.edges, e ∈ G'.edgeSet := by
      intro e he
      apply h_edges
      simp only [Walk.edges_cons, List.mem_cons]; right; exact he
    exact h_ab_G'.reachable.trans (ih h_rest)

/-- Every vertex in v's G-component is G'-reachable from v or w after removing an edge e = {v,w}.
    This is the key lemma for showing the fiber over v's G-component has exactly 2 elements.
    Also used by PathDecompositionComplete for G04/G05 proofs. -/
theorem vertex_in_v_or_w_component (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (v w : V) (hvw : s(v, w) = e) (hadj : G.Adj v w) (u : V)
    (hu : G.connectedComponentMk u = G.connectedComponentMk v) :
    let G' := G.deleteEdges ({e} : Set (Sym2 V))
    G'.connectedComponentMk u = G'.connectedComponentMk v ∨
    G'.connectedComponentMk u = G'.connectedComponentMk w := by
  classical
  intro G'
  have h_reach : G.Reachable u v := ConnectedComponent.eq.mp hu
  -- Get a path from u to v using the skill document pattern
  let p : G.Path u v := (Classical.choice h_reach).toPath
  have hne : v ≠ w := G.ne_of_adj hadj
  -- Either the path uses edge {v,w} or not
  by_cases h_uses : s(v, w) ∈ p.val.edges
  · -- Path uses the edge, so it goes through w at some point
    -- After removing the edge, u is connected to w (via the part before crossing)
    right
    have hw_in := Walk.snd_mem_support_of_mem_edges p.val h_uses
    -- Get the prefix from u to w
    let q := p.val.takeUntil w hw_in
    -- Key insight: v ∉ (takeUntil w).support because:
    -- 1. p is a simple path ending at v
    -- 2. takeUntil w stops at first occurrence of w
    -- 3. By endpoint_notMem_support_takeUntil, v ∉ q.support
    have hv_not_in_q : v ∉ q.support :=
      Walk.endpoint_notMem_support_takeUntil p.property hw_in hne
    -- Therefore {v,w} ∉ q.edges (since if it were, v would be in q.support)
    have hq_edges : ∀ e' ∈ q.edges, e' ≠ e := by
      intro e' he' heq
      -- heq : e' = e and hvw : s(v,w) = e, so e' = s(v,w)
      rw [heq.trans hvw.symm] at he'
      have hv_in : v ∈ q.support := Walk.fst_mem_support_of_mem_edges q he'
      exact hv_not_in_q hv_in
    -- Now convert q to a G'-walk
    have h_q_in_G' : ∀ e' ∈ q.edges, e' ∈ G'.edgeSet := by
      intro e' he'
      rw [edgeSet_deleteEdges, Set.mem_diff]
      exact ⟨Walk.edges_subset_edgeSet q he', hq_edges e' he'⟩
    have h_G'_reach_w : G'.Reachable u w := walk_to_G'_reachable q h_q_in_G'
    exact ConnectedComponent.eq.mpr h_G'_reach_w
  · -- Path doesn't use edge {v,w}, so it's valid in G'
    left
    have h_edges_ok : ∀ e' ∈ p.val.edges, e' ∈ G'.edgeSet := by
      intro e' he'
      rw [edgeSet_deleteEdges, Set.mem_diff]
      refine ⟨Walk.edges_subset_edgeSet p.val he', ?_⟩
      intro hmem
      -- hmem : e' ∈ {e} means e' = e
      rw [Set.mem_singleton_iff] at hmem
      -- hmem : e' = e and hvw : s(v,w) = e, so e' = s(v,w)
      rw [hmem.trans hvw.symm] at he'
      exact h_uses he'
    have h_G'_reach : G'.Reachable u v := walk_to_G'_reachable p.val h_edges_ok
    exact ConnectedComponent.eq.mpr h_G'_reach

/-- Deleting an edge increases component count by at most 1.
    Proof: Define injection ψ : G'.CC → G.CC ⊕ Unit that maps v's G'-component to inr ()
    and everything else to inl(f(c)). -/
theorem deleteEdges_componentCount_le (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.ConnectedComponent] (e : Sym2 V) (he : e ∈ G.edgeSet)
    [inst : Fintype (G.deleteEdges ({e} : Set (Sym2 V))).ConnectedComponent] :
    componentCount (G.deleteEdges ({e} : Set (Sym2 V))) ≤ componentCount G + 1 := by
  classical
  unfold componentCount
  -- Use abbreviation G' but keep the instance explicit
  let G' := G.deleteEdges ({e} : Set (Sym2 V))
  -- Extract endpoints
  rcases Sym2.mk_surjective e with ⟨⟨v, w⟩, hvw⟩
  have hadj : G.Adj v w := by rw [← hvw] at he; exact he
  -- Define map f : G'.CC → G.CC
  let f : G'.ConnectedComponent → G.ConnectedComponent :=
    fun c => G.connectedComponentMk c.exists_rep.choose
  -- Define injection ψ : G'.CC → G.CC ⊕ Unit
  let ψ : G'.ConnectedComponent → G.ConnectedComponent ⊕ Unit :=
    fun c' => if c' = G'.connectedComponentMk v then Sum.inr () else Sum.inl (f c')
  have hψ_inj : Function.Injective ψ := by
    intro c1 c2 heq
    simp only [ψ] at heq
    by_cases h1 : c1 = G'.connectedComponentMk v <;> by_cases h2 : c2 = G'.connectedComponentMk v
    · exact h1.trans h2.symm
    · simp only [h1, h2, ↓reduceIte, reduceCtorEq] at heq
    · simp only [h1, h2, ↓reduceIte, reduceCtorEq] at heq
    · simp only [h1, h2, ↓reduceIte, Sum.inl.injEq] at heq
      simp only [f] at heq
      have h_same : G.connectedComponentMk c1.exists_rep.choose =
          G.connectedComponentMk c2.exists_rep.choose := heq
      have h_G_reach : G.Reachable c1.exists_rep.choose c2.exists_rep.choose :=
        ConnectedComponent.eq.mp h_same
      -- Check if they're in the component containing the edge
      by_cases h_comp : G.connectedComponentMk c1.exists_rep.choose = G.connectedComponentMk v
      · -- Both c1.rep and c2.rep are in v's G-component
        -- By vertex_in_v_or_w_component, each is in G'.comp(v) or G'.comp(w)
        -- Since c1 ≠ G'.comp(v) and c2 ≠ G'.comp(v), both must be G'.comp(w)
        have hc1_vw := vertex_in_v_or_w_component G e v w hvw hadj c1.exists_rep.choose h_comp
        have h2_comp : G.connectedComponentMk c2.exists_rep.choose = G.connectedComponentMk v :=
          h_same.symm.trans h_comp
        have hc2_vw := vertex_in_v_or_w_component G e v w hvw hadj c2.exists_rep.choose h2_comp
        -- c1.exists_rep.choose_spec : G'.connectedComponentMk c1.rep = c1
        have h1_eq := c1.exists_rep.choose_spec
        have h2_eq := c2.exists_rep.choose_spec
        -- From hc1_vw and h1 ≠ G'.comp(v):
        cases hc1_vw with
        | inl hc1_v =>
          have hc1_eq : c1 = G'.connectedComponentMk v := h1_eq.symm.trans hc1_v
          exact (h1 hc1_eq).elim
        | inr hc1_w =>
          cases hc2_vw with
          | inl hc2_v =>
            have hc2_eq : c2 = G'.connectedComponentMk v := h2_eq.symm.trans hc2_v
            exact (h2 hc2_eq).elim
          | inr hc2_w =>
            calc c1 = G'.connectedComponentMk c1.exists_rep.choose := h1_eq.symm
              _ = G'.connectedComponentMk w := hc1_w
              _ = G'.connectedComponentMk c2.exists_rep.choose := hc2_w.symm
              _ = c2 := h2_eq
      · -- Not in v's G-component
        obtain ⟨p⟩ := h_G_reach
        have hp_no_e : e ∉ p.edges := by
          intro h_in
          rw [← hvw] at h_in
          have hv_in := Walk.fst_mem_support_of_mem_edges p h_in
          have h_reach_v : G.Reachable c1.exists_rep.choose v := ⟨p.takeUntil v hv_in⟩
          exact h_comp (ConnectedComponent.eq.mpr h_reach_v)
        have h_G'_reach : G'.Reachable c1.exists_rep.choose c2.exists_rep.choose := by
          have h_edges_ok : ∀ e' ∈ p.edges, e' ∈ G'.edgeSet := by
            intro e' he'
            rw [edgeSet_deleteEdges, Set.mem_diff]
            refine ⟨Walk.edges_subset_edgeSet p he', ?_⟩
            intro heq
            rw [heq] at he'
            exact hp_no_e he'
          exact walk_to_G'_reachable p h_edges_ok
        calc c1 = G'.connectedComponentMk c1.exists_rep.choose := c1.exists_rep.choose_spec.symm
          _ = G'.connectedComponentMk c2.exists_rep.choose := ConnectedComponent.eq.mpr h_G'_reach
          _ = c2 := c2.exists_rep.choose_spec
  -- G' is definitionally G.deleteEdges {e}, so use the explicit instance
  have h_card : @Fintype.card G'.ConnectedComponent inst ≤ Fintype.card (G.ConnectedComponent ⊕ Unit) :=
    Fintype.card_le_of_injective ψ hψ_inj
  simp only [Fintype.card_sum, Fintype.card_unit] at h_card
  exact h_card

/-- Bridge removal increases component count by exactly 1.

    Proof structure:
    1. Map f : G'.CC → G.CC is surjective (gives |G.CC| ≤ |G'.CC|)
    2. f(comp_v) = f(comp_w) but comp_v ≠ comp_w (bridge splits)
    3. So |G.CC| < |G'.CC|
    4. Combined with upper bound |G'.CC| ≤ |G.CC| + 1, get equality -/
theorem bridge_splits_component_aux (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.ConnectedComponent]
    (e : G.edgeSet)
    [inst : Fintype (G.deleteEdges ({e.val} : Set (Sym2 V))).ConnectedComponent]
    (h_bridge : IsBridge G e.val) :
    componentCount (G.deleteEdges ({e.val} : Set (Sym2 V))) = componentCount G + 1 := by
  classical
  unfold componentCount
  -- Use abbreviation G' but keep the instance explicit
  let G' := G.deleteEdges ({e.val} : Set (Sym2 V))
  -- Extract bridge endpoints from IsBridge
  obtain ⟨he_edge, v, w, hvw, h_not_reach⟩ := h_bridge
  have hadj : G.Adj v w := by rw [← hvw] at he_edge; exact he_edge
  -- Key facts about v and w
  have h_same_G : G.connectedComponentMk v = G.connectedComponentMk w :=
    ConnectedComponent.eq.mpr (Adj.reachable hadj)
  have h_diff_G' : G'.connectedComponentMk v ≠ G'.connectedComponentMk w := by
    intro heq
    rw [ConnectedComponent.eq] at heq
    exact h_not_reach heq
  -- Define map f : G'.CC → G.CC
  let f : G'.ConnectedComponent → G.ConnectedComponent :=
    fun c => G.connectedComponentMk c.exists_rep.choose
  -- f is surjective (gives lower bound |G.CC| ≤ |G'.CC|)
  have hf_surj : Function.Surjective f := fun c => by
    obtain ⟨u, hu⟩ := c.exists_rep
    use G'.connectedComponentMk u
    simp only [f]
    have h1 := (G'.connectedComponentMk u).exists_rep.choose_spec
    have h2 : G'.Reachable (G'.connectedComponentMk u).exists_rep.choose u :=
      ConnectedComponent.eq.mp h1
    have h3 : G.Reachable (G'.connectedComponentMk u).exists_rep.choose u :=
      h2.mono (deleteEdges_le G ({e.val} : Set (Sym2 V)))
    rw [← hu]
    exact ConnectedComponent.eq.mpr h3
  have h_le : Fintype.card G.ConnectedComponent ≤ @Fintype.card G'.ConnectedComponent inst :=
    Fintype.card_le_of_surjective f hf_surj
  -- f maps both v and w's G'-components to the same G-component
  have hf_vw : f (G'.connectedComponentMk v) = f (G'.connectedComponentMk w) := by
    simp only [f]
    have hv := (G'.connectedComponentMk v).exists_rep.choose_spec
    have hw := (G'.connectedComponentMk w).exists_rep.choose_spec
    have hv_reach : G.Reachable (G'.connectedComponentMk v).exists_rep.choose v :=
      (ConnectedComponent.eq.mp hv).mono (deleteEdges_le G _)
    have hw_reach : G.Reachable (G'.connectedComponentMk w).exists_rep.choose w :=
      (ConnectedComponent.eq.mp hw).mono (deleteEdges_le G _)
    calc G.connectedComponentMk (G'.connectedComponentMk v).exists_rep.choose
        = G.connectedComponentMk v := ConnectedComponent.eq.mpr hv_reach
      _ = G.connectedComponentMk w := h_same_G
      _ = G.connectedComponentMk (G'.connectedComponentMk w).exists_rep.choose :=
          (ConnectedComponent.eq.mpr hw_reach).symm
  -- f is not injective: comp_v ≠ comp_w but f(comp_v) = f(comp_w)
  -- So |G.CC| < |G'.CC|
  have h_strict : Fintype.card G.ConnectedComponent < @Fintype.card G'.ConnectedComponent inst := by
    by_contra h_not_lt
    push_neg at h_not_lt
    have h_eq : @Fintype.card G'.ConnectedComponent inst = Fintype.card G.ConnectedComponent :=
      le_antisymm h_not_lt h_le
    have h_bij : Function.Bijective f := by
      rw [Fintype.bijective_iff_surjective_and_card]
      exact ⟨hf_surj, h_eq⟩
    -- f is bijective but maps distinct elements to same value - contradiction
    exact h_diff_G' (h_bij.1 hf_vw)
  -- Upper bound: |G'.CC| ≤ |G.CC| + 1
  have h_upper : @Fintype.card G'.ConnectedComponent inst ≤ Fintype.card G.ConnectedComponent + 1 := by
    have := deleteEdges_componentCount_le G e.val e.property
    simp only [componentCount] at this
    exact this
  -- Combine: |G'.CC| = |G.CC| + 1
  -- h_strict : card G.CC < card G'.CC means card G.CC + 1 ≤ card G'.CC
  -- h_upper : card G'.CC ≤ card G.CC + 1
  -- Therefore card G'.CC = card G.CC + 1 by antisymmetry
  exact Nat.le_antisymm h_upper (Nat.succ_le_of_lt h_strict)

/-- Removing a bridge increases component count by 1.
    This is the key lemma for forest_euler.

    Proof idea: The bridge e = {v,w} connects v's component to w's component.
    After removal, they become separate components.
    All other components unchanged.
    Net effect: +1 component.

    Requires Mathlib's ConnectedComponent.lift and related API. -/
theorem bridge_splits_component [Fintype G.ConnectedComponent]
    (e : G.edgeSet)
    [Fintype (G.deleteEdges ({e.val} : Set (Sym2 V))).ConnectedComponent]
    (h_bridge : IsBridge G e.val) :
    componentCount (G.deleteEdges ({e.val} : Set (Sym2 V))) = componentCount G + 1 :=
  bridge_splits_component_aux V G e h_bridge

/-! ## Section 10: Positive Component Count - FULLY PROVEN -/

/-- Non-empty vertex set implies positive component count -/
theorem componentCount_pos [Nonempty V] [Fintype G.ConnectedComponent] :
    0 < componentCount G := by
  unfold componentCount
  have ⟨v⟩ : Nonempty V := inferInstance
  have : Nonempty G.ConnectedComponent := ⟨G.connectedComponentMk v⟩
  exact Fintype.card_pos

/-! ## Section 11: Path Uniqueness in Trees - FULLY PROVEN -/

/-- In acyclic graph, paths are unique -/
theorem isAcyclic_path_unique (h : G.IsAcyclic) (v w : V)
    (p q : G.Path v w) : p = q :=
  h.path_unique p q

/-! ## Section 12: Summary -/

-- Fully proven (0 sorry):
#check bot_connectedComponent_eq_iff
#check bot_components_bijective
#check bot_componentCount
#check bot_edgeCount
#check bot_euler
#check connected_componentCount_eq_one
#check tree_edgeCount
#check tree_euler
#check deleteEdges_edgeFinset_eq
#check deleteEdges_singleton_edgeFinset
#check deleteEdges_singleton_card
#check deleteEdges_singleton_card_lt
#check deleteEdges_le
#check adj_of_le
#check reachable_of_le
#check connected_of_le
#check isAcyclic_of_le
#check deleteEdges_isAcyclic
#check connectedComponent_eq_iff_reachable
#check connected_reachable
#check tree_reachable
#check isBridge_iff
#check isAcyclic_isBridge  -- NOW PROVEN
#check componentCount_pos
#check isAcyclic_path_unique

-- NOW FULLY PROVEN (was axiom):
#check bridge_splits_component

/-! ## Section 11: G06 Bridge Component Cardinality Wrapper -/

/-- Alternative bridge definition matching BridgeComponentTheory -/
def IsBridge' (G : SimpleGraph V) (v w : V) : Prop :=
  G.Adj v w ∧ ¬(G.deleteEdges {s(v, w)}).Reachable v w

/-- THEOREM G06: Bridge removal increases component count by 1.

    Wrapper around bridge_splits_component_aux with vertex-based signature
    matching the axiom in BridgeComponentTheory.lean.
-/
theorem bridge_component_cardinality_proven (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.ConnectedComponent]
    (v w : V)
    [Fintype (G.deleteEdges {s(v, w)}).ConnectedComponent]
    (hb : IsBridge' G v w) :
    Fintype.card (G.deleteEdges {s(v, w)}).ConnectedComponent =
    Fintype.card G.ConnectedComponent + 1 := by
  -- Convert to edge-set form for bridge_splits_component_aux
  have he : s(v, w) ∈ G.edgeSet := hb.1
  let e : G.edgeSet := ⟨s(v, w), he⟩
  -- Show the sets are equal for instance resolution
  have h_sets_eq : ({s(v, w)} : Set (Sym2 V)) = {e.val} := rfl
  have h_bridge : IsBridge G e.val := by
    constructor
    · exact he
    · use v, w
      exact ⟨rfl, hb.2⟩
  -- Use the existing theorem with the correct instance
  have key := @bridge_splits_component_aux V _ _ G _ _ e (by rw [← h_sets_eq]; infer_instance) h_bridge
  simp only [componentCount] at key
  convert key using 2

#check bridge_component_cardinality_proven  -- G06: PROVEN

end ExtendedGraphInfra
