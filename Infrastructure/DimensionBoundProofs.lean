/-
# Dimension Bound Proofs

Proves the h1_dim_components_bound axiom from DimensionBound.lean.

## Main Result

The axiom states that for a simplicial complex K:
  |E| + |C| ≤ (n-1)(n-2)/2 + n

where:
- |E| = number of edges in the 1-skeleton
- |C| = number of connected components
- n = number of vertices

## Mathematical Insight

The key observation is:
1. For a spanning forest: |E| = n - |C|, so |E| + |C| = n
2. Each additional edge (beyond spanning forest) contributes +1 to |E| but at most -1 to |C|
3. Maximum occurs at complete graph: |E| = n(n-1)/2, |C| = 1
4. Complete graph gives: |E| + |C| = n(n-1)/2 + 1 = (n² - n + 2)/2
5. This equals: (n-1)(n-2)/2 + n

AXIOMS ELIMINATED: 1
- h1_dim_components_bound (DimensionBound.lean:308)

SORRIES: 0
AXIOMS: 0 (disconnected_graph_edge_component_bound now proven via ComponentEdgeCounting)

Author: Infrastructure Team
Date: February 2026
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Infrastructure.TreeGraphInfra
import Infrastructure.ComponentEdgeCounting

namespace Infrastructure.DimensionBoundProofs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Graph Theory Lemmas -/

/-- For any graph on n vertices with |C| components, we have |E| ≥ n - |C| edges
    (spanning forest edges). Any additional edges create cycles. -/
theorem edges_ge_spanning_forest (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent] (hne : Nonempty V) :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent ≥ Fintype.card V :=
  -- Reuse the proven theorem from TreeGraphInfra
  @Infrastructure.edges_plus_components_ge_vertices V _ G _ _ _ hne

/-- The cycle rank (first Betti number) of a graph equals |E| - n + |C| -/
theorem cycle_rank_formula (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent] (hne : Nonempty V) :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent ≥ Fintype.card V :=
  edges_ge_spanning_forest G hne

/-- For a complete graph, |E| = n(n-1)/2 and |C| = 1 -/
theorem complete_graph_edges (n : ℕ) (_hn : n > 0) :
    (⊤ : SimpleGraph (Fin n)).edgeFinset.card = n * (n - 1) / 2 := by
  -- The complete graph on n vertices has n(n-1)/2 edges = n choose 2
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp [Nat.choose_two_right]

/-- Complete graph is connected (has exactly 1 component) when n > 0 -/
theorem complete_graph_connected (n : ℕ) (hn : n > 0) :
    Fintype.card (⊤ : SimpleGraph (Fin n)).ConnectedComponent = 1 := by
  -- Complete graph with n > 0 vertices is connected
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hconn : (⊤ : SimpleGraph (Fin n)).Connected := SimpleGraph.connected_top
  exact ExtendedGraphInfra.connected_componentCount_eq_one _ hconn

/-! ## Disconnected Graph Bound -/

/-- Vertices in different components are not adjacent. -/
lemma diff_components_not_adj (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
    (h : G.connectedComponentMk u ≠ G.connectedComponentMk v) : ¬G.Adj u v := by
  intro hadj
  have hreach : G.Reachable u v := hadj.reachable
  have hsame : G.connectedComponentMk u = G.connectedComponentMk v :=
    SimpleGraph.ConnectedComponent.eq.mpr hreach
  exact h hsame

/-- Disconnected graph has at least 2 components. -/
lemma disconnected_components_ge_two (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.ConnectedComponent]
    (h_disconn : ¬G.Connected) (hne : Nonempty V) :
    Fintype.card G.ConnectedComponent ≥ 2 := by
  classical
  -- Connected requires both Preconnected and Nonempty V
  -- Since we have hne : Nonempty V, ¬Connected implies ¬Preconnected
  have h_not_preconn : ¬G.Preconnected := by
    intro hp
    exact h_disconn { preconnected := hp, nonempty := hne }
  -- Preconnected means ∀ u v, Reachable u v
  -- ¬Preconnected means ∃ u v, ¬Reachable u v
  unfold SimpleGraph.Preconnected at h_not_preconn
  push_neg at h_not_preconn
  obtain ⟨u, v, h_not_reach⟩ := h_not_preconn
  -- u and v are in different components
  have h_diff : G.connectedComponentMk u ≠ G.connectedComponentMk v := by
    intro heq
    have hreach := SimpleGraph.ConnectedComponent.eq.mp heq
    exact h_not_reach hreach
  -- So we have at least 2 distinct components
  have h_two : ({G.connectedComponentMk u, G.connectedComponentMk v} : Finset _).card = 2 :=
    Finset.card_pair h_diff
  calc Fintype.card G.ConnectedComponent
      ≥ ({G.connectedComponentMk u, G.connectedComponentMk v} : Finset _).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = 2 := h_two

/-- Non-edges between component representatives.
    If c1 ≠ c2 are components with reps v1 v2, then {v1, v2} is NOT an edge of G. -/
lemma component_reps_not_adjacent (G : SimpleGraph V) [DecidableRel G.Adj]
    (c1 c2 : G.ConnectedComponent) (h_diff : c1 ≠ c2)
    (v1 : V) (hv1 : G.connectedComponentMk v1 = c1)
    (v2 : V) (hv2 : G.connectedComponentMk v2 = c2) :
    ¬G.Adj v1 v2 := by
  have h_comp_diff : G.connectedComponentMk v1 ≠ G.connectedComponentMk v2 := by
    rw [hv1, hv2]; exact h_diff
  exact diff_components_not_adj G v1 v2 h_comp_diff

/-- For a disconnected graph, there exists at least one "missing" edge:
    an edge in ⊤ but not in G. This shows e < n(n-1)/2. -/
lemma disconnected_has_missing_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (h_disconn : ¬G.Connected) (hne : Nonempty V) :
    ∃ edge : Sym2 V, edge ∈ (⊤ : SimpleGraph V).edgeSet ∧ edge ∉ G.edgeSet := by
  classical
  have hc_ge_2 := disconnected_components_ge_two G h_disconn hne
  -- Get two distinct components
  have h_exists_diff : ∃ c1 c2 : G.ConnectedComponent, c1 ≠ c2 := by
    by_contra h_all_eq
    push_neg at h_all_eq
    have h_c_le_1 : Fintype.card G.ConnectedComponent ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr ⟨h_all_eq⟩
    omega
  obtain ⟨c1, c2, h_c1_ne_c2⟩ := h_exists_diff
  obtain ⟨v1, hv1⟩ := c1.exists_rep
  obtain ⟨v2, hv2⟩ := c2.exists_rep
  have hv_ne : v1 ≠ v2 := by
    intro heq; subst heq; rw [hv1] at hv2; exact h_c1_ne_c2 hv2
  use s(v1, v2)
  constructor
  · simp [SimpleGraph.edgeSet_top, hv_ne]
  · intro h_in
    have hadj : G.Adj v1 v2 := h_in
    have h_same := SimpleGraph.ConnectedComponent.eq.mpr hadj.reachable
    simp only [SimpleGraph.connectedComponentMk] at h_same
    rw [hv1, hv2] at h_same
    exact h_c1_ne_c2 h_same

/-- For a disconnected graph, the edge count is strictly less than the complete graph. -/
lemma disconnected_edges_lt_complete (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (h_disconn : ¬G.Connected) (hne : Nonempty V) :
    G.edgeFinset.card < (⊤ : SimpleGraph V).edgeFinset.card := by
  classical
  obtain ⟨e, h_in_top, h_not_in_G⟩ := disconnected_has_missing_edge G h_disconn hne
  have h_subset : G.edgeFinset ⊆ (⊤ : SimpleGraph V).edgeFinset := by
    intro x hx
    simp only [SimpleGraph.mem_edgeFinset] at hx ⊢
    rw [SimpleGraph.edgeSet_top, Sym2.diagSet_compl_eq_setOf_not_isDiag, Set.mem_setOf_eq]
    exact G.not_isDiag_of_mem_edgeSet hx
  have h_ssubset : G.edgeFinset ⊂ (⊤ : SimpleGraph V).edgeFinset := by
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · exact h_subset
    · intro heq
      have : e ∈ G.edgeFinset := by
        rw [heq]
        simp only [SimpleGraph.mem_edgeFinset]
        exact h_in_top
      simp only [SimpleGraph.mem_edgeFinset] at this
      exact h_not_in_G this
  exact Finset.card_lt_card h_ssubset

/-- For a disconnected graph, e ≤ n(n-1)/2 - 1. -/
lemma disconnected_edges_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (h_disconn : ¬G.Connected) (hne : Nonempty V) :
    G.edgeFinset.card + 1 ≤ Fintype.card V * (Fintype.card V - 1) / 2 := by
  have h_lt := disconnected_edges_lt_complete G h_disconn hne
  have h_complete : (⊤ : SimpleGraph V).edgeFinset.card = Fintype.card V * (Fintype.card V - 1) / 2 := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    simp [Nat.choose_two_right]
  omega

/--
For a disconnected graph with c ≥ 2 components, e + c ≤ n(n-1)/2 + 1.

PROVEN: Uses the infrastructure from ComponentEdgeCounting.lean which proves
this bound for ALL graphs (connected or disconnected) via:
1. Partition edges by connected component
2. Local bound: component with k vertices has ≤ k(k-1)/2 edges
3. Convexity: sum Σ k_i(k_i-1)/2 maximized when c-1 components are singletons
4. Maximum = (n-c+1)(n-c)/2, achieved when largest component has n-c+1 vertices

The bound is tight: complete graph achieves e + c = n(n-1)/2 + 1.
-/
theorem disconnected_graph_edge_component_bound (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (_h_disconn : ¬G.Connected)
    (_h_edge : G.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) / 2) :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent ≤ Fintype.card V * (Fintype.card V - 1) / 2 + 1 :=
  ComponentEdgeCounting.edges_plus_components_le G

/-! ## Main Theorem -/

/--
The key algebraic identity:
n(n-1)/2 + 1 = (n-1)(n-2)/2 + n

Proof:
LHS = n(n-1)/2 + 1 = (n² - n)/2 + 1 = (n² - n + 2)/2
RHS = (n-1)(n-2)/2 + n = (n² - 3n + 2)/2 + n = (n² - 3n + 2 + 2n)/2 = (n² - n + 2)/2
-/
theorem dimension_bound_identity (n : ℕ) (hn : n ≥ 1) :
    n * (n - 1) / 2 + 1 ≤ (n - 1) * (n - 2) / 2 + n := by
  -- Both sides are equal for n ≥ 1:
  -- n(n-1)/2 + 1 = (n-1)(n-2)/2 + n = (n² - n + 2)/2
  --
  -- Key algebraic fact: n(n-1) + 2 = (n-1)(n-2) + 2n
  -- Proof: n² - n + 2 = n² - 3n + 2 + 2n ✓

  match n, hn with
  | 1, _ => simp
  | n + 2, _ =>
    -- For n ≥ 2: LHS = (n+2)(n+1)/2 + 1, RHS = (n+1)n/2 + (n+2)
    -- These are equal.
    simp only [Nat.add_sub_cancel, Nat.succ_sub_one]
    -- Goal: (n + 2) * (n + 1) / 2 + 1 ≤ (n + 1) * n / 2 + (n + 2)
    -- Use: (n+2)(n+1) = n(n+1) + 2(n+1), so (n+2)(n+1)/2 = n(n+1)/2 + (n+1)
    have hdiv : n * (n + 1) / 2 + (n + 1) + 1 = n * (n + 1) / 2 + (n + 2) := by omega
    have hkey : (n + 2) * (n + 1) / 2 = n * (n + 1) / 2 + (n + 1) := by
      have h_eq : (n + 2) * (n + 1) = 2 * (n + 1) + n * (n + 1) := by ring
      have h_even : 2 ∣ n * (n + 1) := Nat.even_mul_succ_self n |>.two_dvd
      have h_div2 : 2 * (n + 1) / 2 = n + 1 := Nat.mul_div_cancel_left (n + 1) (by norm_num)
      have h_split : (2 * (n + 1) + n * (n + 1)) / 2 = 2 * (n + 1) / 2 + n * (n + 1) / 2 :=
        Nat.add_div_of_dvd_left h_even
      calc (n + 2) * (n + 1) / 2
          = (2 * (n + 1) + n * (n + 1)) / 2 := by rw [h_eq]
        _ = 2 * (n + 1) / 2 + n * (n + 1) / 2 := h_split
        _ = (n + 1) + n * (n + 1) / 2 := by rw [h_div2]
        _ = n * (n + 1) / 2 + (n + 1) := by ring
    rw [hkey, mul_comm n (n + 1)]
    omega

/--
MAIN THEOREM: For any graph, |E| + |C| ≤ (n-1)(n-2)/2 + n

This proves h1_dim_components_bound.

Proof strategy:
1. If graph is connected (c = 1): e + 1 ≤ n(n-1)/2 + 1 directly from h_edge
2. If graph is disconnected (c ≥ 2): complete graph maximizes e + c

Mathematical insight: The sum |E| + |C| is maximized by the complete graph because:
- Adding an edge within a component: |E| increases by 1, |C| unchanged → sum +1
- Adding an edge between components: |E| increases by 1, |C| decreases by 1 → sum unchanged
Thus starting from isolated vertices (sum = n) and adding all edges within one
component (complete graph) maximizes the sum at n(n-1)/2 + 1.
-/
theorem h1_dim_components_bound_proven (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (h_edge : G.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) / 2) :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent
      ≤ (Fintype.card V - 1) * (Fintype.card V - 2) / 2 + Fintype.card V := by
  classical
  let n := Fintype.card V
  let e := G.edgeFinset.card
  let c := Fintype.card G.ConnectedComponent

  -- The key bound: e + c ≤ n(n-1)/2 + 1
  -- This follows from the fact that the complete graph maximizes e + c.
  -- For connected graphs: c = 1, so e + c = e + 1 ≤ n(n-1)/2 + 1.
  -- For disconnected graphs with c ≥ 2 components:
  --   The max edges with c components is achieved by putting all vertices
  --   in one component (except c-1 isolated vertices), giving:
  --   max_e = (n-c+1)(n-c)/2, and max(e+c) = (n-c+1)(n-c)/2 + c
  --   This is maximized at c=1 (the connected/complete case).

  -- Handle n = 0 case separately (empty graph)
  by_cases hn : n = 0
  · -- n = 0: empty vertex set means e = 0, c = 0, result is trivial
    have hV_empty : IsEmpty V := Fintype.card_eq_zero_iff.mp hn
    -- Edge set is empty when vertex set is empty
    have he : e = 0 := by
      have hempty : G.edgeSet = ∅ := by
        -- V is empty, so Sym2 V is empty, hence any subset is empty
        haveI : IsEmpty (Sym2 V) := inferInstance
        exact Set.eq_empty_of_isEmpty G.edgeSet
      simp only [e, SimpleGraph.edgeFinset, hempty, Set.toFinset_empty, Finset.card_empty]
    -- Component set is empty when vertex set is empty
    have hc : c = 0 := @Fintype.card_eq_zero _ _ ⟨fun cc => hV_empty.false cc.exists_rep.choose⟩
    -- LHS = 0 + 0 = 0, RHS ≥ 0
    show e + c ≤ _
    rw [he, hc]
    exact Nat.zero_le _

  · -- n ≥ 1 case: use the algebraic identity
    have hn1 : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
    calc e + c ≤ n * (n - 1) / 2 + 1 := by
          -- Split on whether graph is connected
          by_cases hconn : G.Connected
          · -- Connected case: c = 1, so e + 1 ≤ n(n-1)/2 + 1 follows from h_edge
            have hc1 : c = 1 := ExtendedGraphInfra.connected_componentCount_eq_one G hconn
            calc e + c = e + 1 := by rw [hc1]
              _ ≤ n * (n - 1) / 2 + 1 := Nat.add_le_add_right h_edge 1
          · -- Disconnected case: c ≥ 2
            -- Use the axiom for disconnected graphs
            exact disconnected_graph_edge_component_bound V G hconn h_edge
      _ ≤ (n - 1) * (n - 2) / 2 + n := dimension_bound_identity n hn1

end Infrastructure.DimensionBoundProofs
