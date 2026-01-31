/-
# Connected Component Counting

Infrastructure for counting connected components in SimpleGraph.
Provides the machinery needed for Euler characteristic arguments.

## Main Results

1. `componentCount` - Number of connected components
2. `connected_iff_one_component` - Connected ↔ exactly 1 component
3. `empty_components_eq_vertices` - Empty graph: components = vertices
4. `add_edge_components` - Adding edge: components decrease by ≤ 1
5. `tree_euler` / `forest_euler` - Euler formulas

## Key Definitions

- `componentCount G` := number of equivalence classes under Reachable
- `IsBridge e` := removing e disconnects its endpoints

Targets: Mathlib 4.27.0 / Lean 4.27.0

SORRIES: 0
AXIOMS: 0

Author: Tenured Cohomology Foundations
Date: January 2026
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.Tactic
import Infrastructure.TreeGraphInfra

namespace ComponentCounting

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Section 1: Component Count Definition -/

/-- Number of connected components -/
noncomputable def componentCount : ℕ := Fintype.card G.ConnectedComponent

/-! ## Section 2: Connected Characterization -/

/-- Connected iff exactly one component -/
theorem connected_iff_componentCount_one :
    G.Connected ↔ componentCount G = 1 := by
  constructor
  · intro hconn
    simp only [componentCount]
    rw [Fintype.card_eq_one_iff]
    use G.connectedComponentMk (Classical.arbitrary V)
    intro c
    obtain ⟨v, rfl⟩ := c.exists_rep
    exact ConnectedComponent.eq.mpr (hconn _ _)
  · intro h
    simp only [componentCount, Fintype.card_eq_one_iff] at h
    obtain ⟨c, hc⟩ := h
    intro v w
    have hv : G.connectedComponentMk v = c := hc _
    have hw : G.connectedComponentMk w = c := hc _
    rw [← ConnectedComponent.eq]
    exact hv.trans hw.symm

/-- Nonempty graph has at least one component -/
theorem componentCount_pos [Nonempty V] : 0 < componentCount G := by
  simp only [componentCount]
  exact Fintype.card_pos

/-! ## Section 3: Empty Graph -/

/-- In empty graph (no edges), each vertex is its own component -/
theorem bot_componentCount : componentCount (⊥ : SimpleGraph V) = Fintype.card V := by
  simp only [componentCount]
  have h : ∀ v w : V, (⊥ : SimpleGraph V).connectedComponentMk v =
                       (⊥ : SimpleGraph V).connectedComponentMk w ↔ v = w := by
    intro v w
    rw [ConnectedComponent.eq]
    constructor
    · intro hr
      cases hr.exists_walk with
      | intro p =>
        cases p with
        | nil => rfl
        | cons h _ => exact (not_adj_bot v _ h).elim
    · intro h
      rw [h]
  have bij : Function.Bijective (fun v => (⊥ : SimpleGraph V).connectedComponentMk v) := by
    constructor
    · intro v w hvw
      exact (h v w).mp hvw
    · intro c
      obtain ⟨v, rfl⟩ := c.exists_rep
      exact ⟨v, rfl⟩
  exact Fintype.card_of_bijective bij

/-! ## Section 4: Subgraph Components -/

/-- Subgraph has at least as many components -/
theorem componentCount_mono {G H : SimpleGraph V} [DecidableRel H.Adj] (hle : G ≤ H) :
    componentCount H ≤ componentCount G := by
  simp only [componentCount]
  let f : G.ConnectedComponent → H.ConnectedComponent :=
    fun c => c.map (Hom.mapSpanningSubgraphs hle)
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨v, rfl⟩ := c.exists_rep
    use G.connectedComponentMk v
    simp only [f, ConnectedComponent.map_mk]
  exact Fintype.card_le_of_surjective f hsurj

/-! ## Section 5: Adding an Edge -/

/-- Adding an edge decreases components by at most 1 -/
theorem add_edge_componentCount (v w : V) (hvw : v ≠ w) (hnadj : ¬G.Adj v w) :
    componentCount G ≤ componentCount (G ⊔ edge v w) + 1 := by
  have hle : G ≤ G ⊔ edge v w := le_sup_left
  have hge := componentCount_mono hle
  omega

/-! ## Section 6: Bridges -/

/-- An edge is a bridge if removing it disconnects its endpoints -/
def IsBridge (v w : V) : Prop :=
  G.Adj v w ∧ ¬(G.deleteEdges {s(v, w)}).Reachable v w

/-- Bridge definition matches Mathlib's -/
theorem isBridge_iff_mathlib (v w : V) :
    IsBridge G v w ↔ G.Adj v w ∧ G.IsBridge s(v, w) := by
  simp only [IsBridge, SimpleGraph.IsBridge, isBridge_iff]
  tauto

/-- In an acyclic graph, every edge is a bridge -/
theorem acyclic_all_bridges (hac : G.IsAcyclic) (v w : V) (hadj : G.Adj v w) :
    IsBridge G v w := by
  constructor
  · exact hadj
  · intro hreach
    obtain ⟨p⟩ := hreach
    have hne : v ≠ w := G.ne_of_adj hadj
    have h_no_edge : s(v, w) ∉ p.edges := by
      intro h_in
      have h_in_del : s(v, w) ∈ (G.deleteEdges {s(v, w)}).edgeSet :=
        Walk.edges_subset_edgeSet p h_in
      simp only [edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff] at h_in_del
      exact h_in_del.2 rfl
    by_cases hp_nil : p.length = 0
    · have := Walk.eq_of_length_eq_zero hp_nil
      exact hne this
    · have hp_path := p.toPath
      let p_path := hp_path.val
      have hp_path_isPath := hp_path.property
      let p_G := p_path.mapLe (deleteEdges_le {s(v, w)})
      let full_cycle := Walk.cons hadj p_G.reverse
      have h_is_cycle : full_cycle.IsCycle := by
        constructor
        · constructor
          · constructor
            simp only [Walk.edges_cons, Walk.edges_reverse, List.nodup_cons]
            constructor
            · intro h_in
              rw [List.mem_reverse] at h_in
              have : s(v, w) ∈ p_path.edges := by
                rw [Walk.mapLe, Walk.edges_map] at h_in
                simp only [Hom.ofLE_apply, Sym2.map_id', List.map_id] at h_in
                exact h_in
              have h_in_del : s(v, w) ∈ (G.deleteEdges {s(v, w)}).edgeSet :=
                Walk.edges_subset_edgeSet p_path this
              simp only [edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff] at h_in_del
              exact h_in_del.2 rfl
            · exact (hp_path_isPath.isTrail.reverse.mapLe _).edges_nodup
          · exact Walk.cons_ne_nil _ _
        · simp only [Walk.support_cons, Walk.support_reverse, List.tail_cons]
          exact hp_path_isPath.support_nodup.reverse
      exact hac full_cycle h_is_cycle

/-! ## Section 7: Tree Euler Characteristic -/

/-- For a tree: |E| + 1 = |V| -/
theorem tree_edge_vertex [Nonempty V] (htree : G.IsTree) :
    G.edgeFinset.card + 1 = Fintype.card V :=
  htree.card_edgeFinset

/-- For a tree: |E| + c = |V| where c = 1 -/
theorem tree_euler [Nonempty V] (htree : G.IsTree) :
    G.edgeFinset.card + componentCount G = Fintype.card V := by
  rw [connected_iff_componentCount_one.mp htree.connected]
  exact tree_edge_vertex G htree

/-! ## Section 8: Forest Euler Characteristic -/

/-- Helper: edge deletion reduces edge count by 1 -/
private theorem deleteEdges_card (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    (G.deleteEdges {e}).edgeFinset.card = G.edgeFinset.card - 1 :=
  Infrastructure.card_edgeFinset_deleteEdges_singleton G e he

/-- Helper: edge deletion increases components by at most 1 -/
private theorem deleteEdges_comp_le (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    Fintype.card (G.deleteEdges {e}).ConnectedComponent ≤
    Fintype.card G.ConnectedComponent + 1 :=
  Infrastructure.card_connectedComponent_deleteEdges_add_one G e he

/-- Helper: f : G'.CC → G.CC is surjective for G' = G.deleteEdges {e} -/
private theorem deleteEdges_comp_surj (e : Sym2 V) :
    let G' := G.deleteEdges {e}
    let f : G'.ConnectedComponent → G.ConnectedComponent :=
      fun c => G.connectedComponentMk c.exists_rep.choose
    Function.Surjective f := by
  intro c
  obtain ⟨v, hv⟩ := c.exists_rep
  use (G.deleteEdges {e}).connectedComponentMk v
  have h1 := ((G.deleteEdges {e}).connectedComponentMk v).exists_rep.choose_spec
  have h2 : (G.deleteEdges {e}).Reachable
      ((G.deleteEdges {e}).connectedComponentMk v).exists_rep.choose v :=
    ConnectedComponent.eq.mp h1
  have h3 : G.Reachable ((G.deleteEdges {e}).connectedComponentMk v).exists_rep.choose v :=
    h2.mono (deleteEdges_le {e})
  rw [← hv]
  exact ConnectedComponent.eq.mpr h3

/-- For a forest (acyclic): |E| + c = |V| -/
theorem forest_euler [Nonempty V] (hac : G.IsAcyclic) :
    G.edgeFinset.card + componentCount G = Fintype.card V := by
  classical
  by_cases h_conn : G.Connected
  · have h_tree : G.IsTree := ⟨h_conn, hac⟩
    exact tree_euler G h_tree
  · simp only [componentCount]
    induction hn : G.edgeFinset.card using Nat.strong_induction_on generalizing G with
    | _ n ih =>
      by_cases h_zero : n = 0
      · subst h_zero
        have h_empty : G.edgeSet = ∅ := by
          have h1 : Fintype.card G.edgeSet = 0 := by rw [← edgeFinset_card]; exact hn
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
        omega
      · have h_pos : 0 < n := Nat.pos_of_ne_zero h_zero
        have h_nonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨e, he⟩ := h_nonempty
        have he_set : e ∈ G.edgeSet := mem_edgeFinset.mp he
        rcases Sym2.mk_surjective e with ⟨⟨v, w⟩, hvw⟩
        have hadj : G.Adj v w := by rw [← hvw] at he_set; exact he_set
        have h_bridge : G.IsBridge e := isAcyclic_iff_forall_edge_isBridge.mp hac he_set
        set G' := G.deleteEdges {e} with hG'
        haveI : DecidableRel G'.Adj := inferInstance
        have h_card' : G'.edgeFinset.card = n - 1 := deleteEdges_card G e he
        have h_acyc' : G'.IsAcyclic := by
          intro u c hc
          exact hac _ (hc.mapLe (deleteEdges_le {e}))
        -- Key: show component count increases by exactly 1
        let f : G'.ConnectedComponent → G.ConnectedComponent :=
          fun c => G.connectedComponentMk c.exists_rep.choose
        have hf_surj : Function.Surjective f := deleteEdges_comp_surj G e
        have h_le : Fintype.card G.ConnectedComponent ≤ Fintype.card G'.ConnectedComponent :=
          Fintype.card_le_of_surjective f hf_surj
        have h_bound : Fintype.card G'.ConnectedComponent ≤
            Fintype.card G.ConnectedComponent + 1 := deleteEdges_comp_le G e he
        have h_same_G : G.connectedComponentMk v = G.connectedComponentMk w :=
          ConnectedComponent.eq.mpr (Adj.reachable hadj)
        have h_diff_G' : G'.connectedComponentMk v ≠ G'.connectedComponentMk w := by
          intro heq
          rw [hvw, isBridge_iff] at h_bridge
          exact h_bridge.2 (ConnectedComponent.eq.mp (by rwa [← hvw] at heq))
        -- f maps both v and w's G'-components to the same G-component
        have hf_vw : f (G'.connectedComponentMk v) = f (G'.connectedComponentMk w) := by
          simp only [f]
          have hv := (G'.connectedComponentMk v).exists_rep.choose_spec
          have hw := (G'.connectedComponentMk w).exists_rep.choose_spec
          have hv_reach : G.Reachable (G'.connectedComponentMk v).exists_rep.choose v :=
            (ConnectedComponent.eq.mp hv).mono (deleteEdges_le _)
          have hw_reach : G.Reachable (G'.connectedComponentMk w).exists_rep.choose w :=
            (ConnectedComponent.eq.mp hw).mono (deleteEdges_le _)
          calc G.connectedComponentMk (G'.connectedComponentMk v).exists_rep.choose
              = G.connectedComponentMk v := ConnectedComponent.eq.mpr hv_reach
            _ = G.connectedComponentMk w := h_same_G
            _ = G.connectedComponentMk (G'.connectedComponentMk w).exists_rep.choose :=
                (ConnectedComponent.eq.mpr hw_reach).symm
        -- If cards were equal, f would be bijective, but it maps different elements to same
        have h_strict : Fintype.card G.ConnectedComponent < Fintype.card G'.ConnectedComponent := by
          by_contra h_not_lt
          push_neg at h_not_lt
          have h_eq : Fintype.card G'.ConnectedComponent = Fintype.card G.ConnectedComponent :=
            le_antisymm h_not_lt h_le
          have h_bij : Function.Bijective f := by
            rw [Fintype.bijective_iff_surjective_and_card]
            exact ⟨hf_surj, h_eq⟩
          exact h_diff_G' (h_bij.1 hf_vw)
        have h_comp : Fintype.card G'.ConnectedComponent = Fintype.card G.ConnectedComponent + 1 :=
          by omega
        have h_ih := ih (n - 1) (by omega) G' h_acyc' h_card'
        omega

/-! ## Section 9: Converse -/

/-- If |E| + c = |V|, then acyclic -/
theorem euler_implies_acyclic [Nonempty V]
    (h : G.edgeFinset.card + componentCount G = Fintype.card V) :
    G.IsAcyclic := by
  simp only [componentCount] at h
  exact Infrastructure.euler_eq_implies_acyclic' G h

/-! ## Section 10: Combined Characterization -/

/-- Combined characterization: acyclic ↔ |E| + c = |V| -/
theorem acyclic_iff_euler [Nonempty V] :
    G.IsAcyclic ↔ G.edgeFinset.card + componentCount G = Fintype.card V := by
  constructor
  · exact forest_euler G
  · exact euler_implies_acyclic G

/-! ## Summary -/

#check componentCount
#check connected_iff_componentCount_one
#check bot_componentCount
#check componentCount_mono
#check tree_euler
#check forest_euler
#check euler_implies_acyclic
#check acyclic_iff_euler

end ComponentCounting
