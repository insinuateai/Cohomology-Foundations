/-
COBOUND: Multi-Agent Coordination Framework
Module: MultiAgent/NerveComplex.lean
Batch: FOUNDATION - Critical Bridge Infrastructure
Created: January 2026

PURPOSE:
This module provides the CRITICAL BRIDGE between AgentNetwork and SimplicialComplex,
enabling bridge axioms to be converted from axioms to proven theorems.

MATHEMATICAL FOUNDATION:
The nerve complex N(G) of a graph G has:
- Vertices = nodes of G
- k-simplices = (k+1)-cliques in G

For agent networks:
- Vertices = agents (via Agent.id)
- Edges = compatible pairs

KEY THEOREM:
  AgentNetwork.isForest N → H1Trivial (nerveComplex N)

QUALITY STANDARDS:
- Axioms: 0 (all theorems fully proven)
- Sorries: 0

DEPENDENCIES:
- Foundations.Cohomology (H1Trivial)
- H1Characterization.Characterization (h1_trivial_iff_oneConnected)
- MultiAgent.AgentNetworks (AgentNetwork, isForest)
-/

import Foundations.Cohomology
import H1Characterization.Characterization
import MultiAgent.AgentNetworks
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace MultiAgent

open Foundations
open H1Characterization

/-! # Section 1: Agent to Vertex Mapping

Convert between Agent and Vertex (ℕ) types.
-/

/-- Convert an agent to a vertex using its ID -/
def agentToVertex (a : Agent) : Vertex := a.id

/-- Convert a vertex back to an agent -/
def vertexToAgent (v : Vertex) : Agent := Agent.mk v

/-- Round-trip: agent → vertex → agent = identity -/
theorem vertexToAgent_agentToVertex (a : Agent) :
    vertexToAgent (agentToVertex a) = a := by
  cases a
  rfl

/-- Round-trip: vertex → agent → vertex = identity -/
theorem agentToVertex_vertexToAgent (v : Vertex) :
    agentToVertex (vertexToAgent v) = v := rfl

/-- The mapping is injective -/
theorem agentToVertex_injective : Function.Injective agentToVertex := by
  intro a b h
  simp only [agentToVertex] at h
  exact Agent.id_inj a b h

/-! # Section 2: Nerve Complex Construction

Build a SimplicialComplex from an AgentNetwork.
The nerve complex has:
- 0-simplices: individual agents (as vertices via their ID)
- 1-simplices: compatible pairs
-/

/-- The set of vertices in the nerve complex (agent IDs) -/
def nerveVertices (N : AgentNetwork) : Set Vertex :=
  { v | ∃ a ∈ N.agents, a.id = v }

/-- The simplices of the nerve complex -/
def nerveSimplices (N : AgentNetwork) : Set Simplex :=
  { s : Simplex |
    -- Empty simplex is always included
    s = ∅ ∨
    -- Non-empty simplices: all vertices are agents, and all distinct pairs are compatible
    (s.Nonempty ∧
     (∀ v ∈ s, ∃ a ∈ N.agents, a.id = v) ∧
     (∀ v w, v ∈ s → w ∈ s → v ≠ w →
        ∃ a b, a ∈ N.agents ∧ b ∈ N.agents ∧ a.id = v ∧ b.id = w ∧ N.compatible a b)) }

/-- The nerve complex of an agent network -/
def nerveComplex (N : AgentNetwork) : SimplicialComplex where
  simplices := nerveSimplices N
  has_vertices := by
    intro s hs v hv
    simp only [nerveSimplices, Set.mem_setOf_eq] at hs ⊢
    rcases hs with rfl | ⟨_, hAgents, _⟩
    · exact (Finset.notMem_empty v hv).elim
    · -- The singleton {v} is in the nerve
      right
      constructor
      · exact ⟨v, Finset.mem_singleton_self v⟩
      constructor
      · intro w hw
        simp only [Simplex.vertex, Finset.mem_singleton] at hw
        rw [hw]
        exact hAgents v hv
      · intro w1 w2 hw1 hw2 hne
        simp only [Simplex.vertex, Finset.mem_singleton] at hw1 hw2
        rw [hw1, hw2] at hne
        exact (hne rfl).elim
  down_closed := by
    intro s hs i
    simp only [nerveSimplices, Set.mem_setOf_eq] at hs ⊢
    rcases hs with rfl | ⟨hne, hAgents, hCompat⟩
    · exact i.elim0  -- Empty simplex has no faces
    · -- Face of a clique is a clique
      by_cases hface : (Simplex.face s i) = ∅
      · left; exact hface
      · right
        constructor
        · exact Finset.nonempty_iff_ne_empty.mpr hface
        constructor
        · intro v hv
          have hv_in_s := Simplex.face_subset s i hv
          exact hAgents v hv_in_s
        · intro v w hv hw hvw
          have hv_in_s := Simplex.face_subset s i hv
          have hw_in_s := Simplex.face_subset s i hw
          exact hCompat v w hv_in_s hw_in_s hvw

/-! # Section 3: Nerve Complex Properties -/

/-- Singleton simplices are in the nerve for any agent -/
theorem nerve_has_agent_vertices (N : AgentNetwork) (a : Agent) (ha : a ∈ N.agents) :
    ({a.id} : Simplex) ∈ (nerveComplex N).simplices := by
  simp only [nerveComplex, nerveSimplices, Set.mem_setOf_eq]
  right
  constructor
  · exact ⟨a.id, Finset.mem_singleton_self _⟩
  constructor
  · intro v hv
    simp only [Finset.mem_singleton] at hv
    rw [hv]
    exact ⟨a, ha, rfl⟩
  · intro v w hv hw hvw
    simp only [Finset.mem_singleton] at hv hw
    rw [hv, hw] at hvw
    exact (hvw rfl).elim

/-- An edge exists in the nerve iff the corresponding agents are compatible -/
theorem nerveComplex_edge_iff (N : AgentNetwork) (a b : Agent)
    (ha : a ∈ N.agents) (hb : b ∈ N.agents) (hab : a ≠ b) :
    ({a.id, b.id} : Simplex) ∈ (nerveComplex N).simplices ↔ N.compatible a b := by
  simp only [nerveComplex, nerveSimplices, Set.mem_setOf_eq]
  constructor
  · intro h
    rcases h with habs | ⟨_, _, hCompat⟩
    · -- Empty case: {a.id, b.id} = ∅ is false
      have : a.id ∈ ({a.id, b.id} : Simplex) := Finset.mem_insert_self _ _
      rw [habs] at this
      exact (Finset.notMem_empty _ this).elim
    · -- Use hCompat
      have haid : a.id ∈ ({a.id, b.id} : Simplex) := Finset.mem_insert_self _ _
      have hbid : b.id ∈ ({a.id, b.id} : Simplex) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hne : a.id ≠ b.id := by
        intro h; apply hab; exact Agent.id_inj a b h
      obtain ⟨a', b', _, _, ha'id, hb'id, hcomp⟩ := hCompat a.id b.id haid hbid hne
      -- a' = a and b' = b by injectivity
      have ha_eq : a' = a := Agent.id_inj a' a ha'id
      have hb_eq : b' = b := Agent.id_inj b' b hb'id
      rw [ha_eq, hb_eq] at hcomp
      exact hcomp
  · intro hcomp
    right
    constructor
    · exact ⟨a.id, Finset.mem_insert_self _ _⟩
    constructor
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact ⟨a, ha, rfl⟩
      · exact ⟨b, hb, rfl⟩
    · intro v w hv hw hvw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
      rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
      · exact (hvw rfl).elim
      · exact ⟨a, b, ha, hb, rfl, rfl, hcomp⟩
      · exact ⟨b, a, hb, ha, rfl, rfl, N.compatible_symm a b hcomp⟩
      · exact (hvw rfl).elim

/-! # Section 4: Compatibility Graph

The compatibility graph of an agent network as a SimpleGraph.
-/

/-- The compatibility graph of an agent network as a SimpleGraph -/
def compatibilityGraph (N : AgentNetwork) : SimpleGraph N.agents where
  Adj a b := N.compatible a.val b.val
  symm := by
    intro a b h
    exact N.compatible_symm a.val b.val h
  loopless := by
    intro a h
    exact N.compatible_irrefl a.val h

/-- A network is acyclic in the graph-theoretic sense -/
def AgentNetwork.isAcyclic (N : AgentNetwork) : Prop :=
  (compatibilityGraph N).IsAcyclic

/-! # Section 5: Forest → H¹ = 0 Bridge

The main bridge theorem showing that forest networks have trivial first cohomology.
-/

/-- Forest networks have no compatible pairs.
    Key insight: isForest = isTrivial = card ≤ 1. -/
theorem forest_no_compatible_in_nerve (N : AgentNetwork) (hf : N.isForest) :
    ∀ a b, a ∈ N.agents → b ∈ N.agents → ¬N.compatible a b := by
  intro a b ha hb hcomp
  simp only [AgentNetwork.isForest, AgentNetwork.isTrivial] at hf
  have heq : a = b := Finset.card_le_one.mp hf a ha b hb
  rw [heq] at hcomp
  exact N.compatible_irrefl b hcomp

/-- Forest networks have no edges in their nerve complex (all simplices have card ≤ 1). -/
theorem forest_no_edges_in_nerve (N : AgentNetwork) (hf : N.isForest) :
    ∀ s ∈ (nerveComplex N).simplices, s.card ≤ 1 := by
  intro s hs
  simp only [nerveComplex, nerveSimplices, Set.mem_setOf_eq] at hs
  rcases hs with rfl | ⟨hne, hAgents, hCompat⟩
  · -- Empty simplex
    simp only [Finset.card_empty, Nat.zero_le]
  · -- Non-empty simplex: show it can't have 2+ vertices
    by_contra h
    push_neg at h
    -- If card ≥ 2, there exist distinct v, w in s
    have hge2 : s.card ≥ 2 := h
    have hgt1 : 1 < s.card := by omega
    obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.mp hgt1
    -- Those agents would be compatible
    obtain ⟨a', b', ha', hb', _, _, hcomp⟩ := hCompat v w hv hw hvw
    -- But forest means no compatible pairs
    have hno := forest_no_compatible_in_nerve N hf a' b' ha' hb'
    exact hno hcomp

/-- The nerve complex of a forest has no 1-simplices. -/
theorem nerve_forest_ksimplices_one_empty (N : AgentNetwork) (hf : N.isForest) :
    (nerveComplex N).ksimplices 1 = ∅ := by
  ext s
  simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro ⟨hs_mem, hs_card⟩
  have h := forest_no_edges_in_nerve N hf s hs_mem
  -- hs_card says s.card = 1 + 1 = 2, but h says s.card ≤ 1
  omega

/-- MAIN THEOREM: Forest structure implies trivial first cohomology.

This is the KEY BRIDGE theorem.

Mathematical content:
- Forest (trivial network) = card ≤ 1 = no distinct agents
- No distinct agents = no compatible pairs
- No compatible pairs = no 1-simplices in nerve complex
- No 1-simplices = H¹ = 0 (trivially, no 1-cochains)

The proof chain:
  N.isForest
    → no compatible pairs (forest_no_compatible_in_nerve)
    → no 1-simplices in nerveComplex N (nerve_forest_ksimplices_one_empty)
    → H1Trivial (nerveComplex N) (h1_trivial_of_no_edges)
-/
theorem forest_implies_h1_trivial_nerve (N : AgentNetwork) :
    N.isForest → H1Trivial (nerveComplex N) := by
  intro hf
  apply h1_trivial_of_no_edges
  exact nerve_forest_ksimplices_one_empty N hf

/-- Forest (simplified) implies acyclic in the compatibility graph -/
theorem isForest_implies_isAcyclic (N : AgentNetwork) (hf : N.isForest) :
    N.isAcyclic := by
  -- isForest = isTrivial = agents.card ≤ 1
  simp only [AgentNetwork.isForest, AgentNetwork.isTrivial] at hf
  simp only [AgentNetwork.isAcyclic, SimpleGraph.IsAcyclic]
  intro v p hp
  -- Trivial case: at most 1 agent, so no cycles possible
  by_cases hc : N.agents.card = 0
  · -- No agents at all - v can't exist
    have hempty : N.agents = ∅ := Finset.card_eq_zero.mp hc
    have hv : v.val ∈ N.agents := v.property
    simp only [hempty, Finset.notMem_empty] at hv
  · -- Exactly 1 agent (since card ≤ 1 and card ≠ 0)
    have hone : N.agents.card = 1 := Nat.le_antisymm hf (Nat.one_le_iff_ne_zero.mpr hc)
    -- With 1 agent, the graph has 1 vertex and no edges (by irreflexivity)
    have h_no_adj : ∀ (a b : N.agents), ¬(compatibilityGraph N).Adj a b := by
      intro a b hadj
      have ha_eq_b : a = b := Subtype.ext (Finset.card_le_one.mp hf a.val a.property b.val b.property)
      rw [ha_eq_b] at hadj
      exact (compatibilityGraph N).loopless b hadj
    -- A cycle needs at least one edge, but we have none
    cases p with
    | nil => exact hp.1.2 rfl  -- ne_nil violated
    | cons hadj _ => exact h_no_adj _ _ hadj

/-! # Section 6: Graph-Theoretic Forest Definition

A more general definition that captures acyclic compatibility graphs.
-/

/-- Graph-theoretic forest: compatibility graph is acyclic.
    This is the proper mathematical definition of forest. -/
def AgentNetwork.isGraphForest (N : AgentNetwork) : Prop :=
  (compatibilityGraph N).IsAcyclic

/-- The simplified isForest implies the graph-theoretic isGraphForest.
    This shows our restricted definition is a special case. -/
theorem isForest_implies_isGraphForest (N : AgentNetwork) :
    N.isForest → N.isGraphForest :=
  isForest_implies_isAcyclic N

/-! # Section 7: Derived Bridge Theorems

These theorems provide convenient forms of the main bridge.
-/

/-- Trivial networks have H¹ = 0 -/
theorem trivial_h1_trivial (N : AgentNetwork) (htriv : N.isTrivial) :
    H1Trivial (nerveComplex N) := by
  apply forest_implies_h1_trivial_nerve
  exact htriv

/-- Empty networks have H¹ = 0 -/
theorem empty_h1_trivial : H1Trivial (nerveComplex AgentNetwork.empty) := by
  apply trivial_h1_trivial
  exact AgentNetwork.isTrivial_of_isEmpty _ AgentNetwork.empty_isEmpty

/-- Singleton networks have H¹ = 0 -/
theorem singleton_h1_trivial (a : Agent) :
    H1Trivial (nerveComplex (AgentNetwork.singleton a)) := by
  apply trivial_h1_trivial
  exact AgentNetwork.singleton_isTrivial a

/-- Fully incompatible trivial networks have H¹ = 0 -/
theorem fullyIncompatible_trivial_h1_trivial (N : AgentNetwork)
    (htriv : N.isTrivial) (_hinc : N.fullyIncompatible) :
    H1Trivial (nerveComplex N) := by
  apply trivial_h1_trivial
  exact htriv

/-- If H¹ ≠ 0, the network is not a forest (contrapositive) -/
theorem h1_nontrivial_implies_not_forest (N : AgentNetwork)
    (h : ¬H1Trivial (nerveComplex N)) :
    ¬N.isForest := by
  intro hf
  exact h (forest_implies_h1_trivial_nerve N hf)

/-! # Section 8: Summary

## Proven Theorems
- Section 1 (Mapping): 4 theorems
- Section 2 (Construction): 1 definition with full proofs
- Section 3 (Properties): 2 theorems
- Section 4 (Compatibility Graph): 2 definitions
- Section 5 (Main Bridge): 4 theorems including the main bridge
- Section 6 (Graph Forest): 2 definitions/theorems
- Section 7 (Derived): 5 theorems

## Definitions
- agentToVertex, vertexToAgent
- nerveVertices, nerveSimplices, nerveComplex
- compatibilityGraph
- AgentNetwork.isAcyclic, AgentNetwork.isGraphForest

## Quality
- Axioms: 0
- Sorries: 0

This module provides the foundation for bridging agent network properties
to cohomological statements.
-/

end MultiAgent
