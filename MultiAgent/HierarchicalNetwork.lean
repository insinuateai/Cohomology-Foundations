/-
COBOUND: Multi-Agent Coordination Framework
Module: MultiAgent/HierarchicalNetwork.lean
Created: January 2026

Hierarchical Networks: Agent Value Systems + Tree Authority

Combines:
- TreeAuth: The authority structure (who reports to whom)
- ValueSystem: Agent perspectives/preferences

The key insight: When agents are organized in a tree authority structure,
and direct reports are compatible, H¹ = 0 is guaranteed.

QUALITY STANDARDS:
- Axioms: 0
- Sorries: Minimal
- Core structures: COMPLETE
-/

import MultiAgent.TreeAuthority
import Perspective.ValueSystem

namespace MultiAgent

open Perspective (ValueSystem)

/-! # Hierarchical Network

A hierarchical network combines:
1. A set of agents with value systems (perspectives)
2. A tree authority structure defining supervision relationships
3. A compatibility threshold epsilon

The key property is `wellFormed`: direct reports must be compatible.
-/

/-- A hierarchical agent network with tree authority.

Combines agent value systems with a tree-shaped authority structure.
The `wellFormed` condition ensures direct reports can reconcile. -/
structure HierarchicalNetwork (S : Type*) [Fintype S] [DecidableEq S] where
  /-- Number of agents -/
  numAgents : ℕ
  /-- Positive number of agents -/
  numAgents_pos : 0 < numAgents
  /-- Value system for each agent -/
  systems : Fin numAgents → ValueSystem S
  /-- Tree authority structure -/
  authority : TreeAuth numAgents
  /-- Compatibility threshold -/
  epsilon : ℚ
  /-- Threshold is positive -/
  epsilon_pos : epsilon > 0

variable {S : Type*} [Fintype S] [DecidableEq S]

namespace HierarchicalNetwork

/-! ## Basic Definitions -/

/-- An agent directly reports to another -/
def directReport (H : HierarchicalNetwork S) (subordinate supervisor : Fin H.numAgents) : Prop :=
  H.authority.parent subordinate = some supervisor

/-- Two agents are compatible: they can reconcile on some situation -/
def compatible (H : HierarchicalNetwork S) (i j : Fin H.numAgents) : Prop :=
  ∃ s : S, |((H.systems i).values s) - ((H.systems j).values s)| ≤ 2 * H.epsilon

/-- The network is well-formed if all direct reports are compatible.
    This is the key condition for H¹ = 0. -/
def wellFormed (H : HierarchicalNetwork S) : Prop :=
  ∀ i j, H.directReport i j → H.compatible i j

/-! ## Convenience Accessors -/

/-- The root agent (ultimate authority) -/
def root (H : HierarchicalNetwork S) : Fin H.numAgents := H.authority.root

/-- Get the value system for an agent -/
def agentSystem (H : HierarchicalNetwork S) (i : Fin H.numAgents) : ValueSystem S :=
  H.systems i

/-- Get the parent (supervisor) of an agent, if any -/
def supervisor (H : HierarchicalNetwork S) (i : Fin H.numAgents) : Option (Fin H.numAgents) :=
  H.authority.parent i

/-- Get children (direct reports) of an agent -/
def directReports (H : HierarchicalNetwork S) (i : Fin H.numAgents) : List (Fin H.numAgents) :=
  H.authority.children i

/-! ## Compatibility Properties -/

/-- Compatible is symmetric -/
theorem compatible_symm (H : HierarchicalNetwork S) (i j : Fin H.numAgents) :
    H.compatible i j ↔ H.compatible j i := by
  unfold compatible
  constructor
  · intro ⟨s, hs⟩
    exact ⟨s, by rwa [abs_sub_comm]⟩
  · intro ⟨s, hs⟩
    exact ⟨s, by rwa [abs_sub_comm]⟩

/-- Every agent is compatible with itself -/
theorem compatible_refl (H : HierarchicalNetwork S) [Nonempty S] (i : Fin H.numAgents) :
    H.compatible i i := by
  simp only [compatible]
  use Classical.arbitrary S
  simp only [sub_self, abs_zero]
  apply le_of_lt
  have hpos := H.epsilon_pos
  have : H.epsilon + H.epsilon = 2 * H.epsilon := by ring
  rw [← this]
  exact add_pos hpos hpos

/-! ## Authority Chain Properties -/

/-- Root has no supervisor -/
theorem root_no_supervisor (H : HierarchicalNetwork S) :
    H.supervisor H.root = none := H.authority.root_no_parent

/-- Non-root agents have supervisors -/
theorem nonroot_has_supervisor (H : HierarchicalNetwork S) (i : Fin H.numAgents)
    (hi : i ≠ H.root) : (H.supervisor i).isSome :=
  H.authority.nonroot_has_parent i hi

/-- The authority chain from any agent to root -/
def chainToRoot (H : HierarchicalNetwork S) (i : Fin H.numAgents) : List (Fin H.numAgents) :=
  H.authority.pathToRoot i

/-! ## Edge Set for Simplicial Complex -/

/-- Edges in the hierarchy: (subordinate, supervisor) pairs -/
def edges (H : HierarchicalNetwork S) : List (Fin H.numAgents × Fin H.numAgents) :=
  H.authority.edges

/-- In a well-formed network, every edge connects compatible agents -/
theorem edges_compatible (H : HierarchicalNetwork S) (hwf : H.wellFormed)
    (e : Fin H.numAgents × Fin H.numAgents) (he : e ∈ H.edges) :
    H.compatible e.1 e.2 := by
  -- he tells us (e.1, e.2) is in the edge list, meaning e.1's parent is e.2
  have hdr : H.directReport e.1 e.2 := by
    simp only [edges, directReport, TreeAuth.edges] at he ⊢
    simp only [List.mem_filterMap, List.mem_finRange] at he
    obtain ⟨i, _, hi⟩ := he
    cases hp : H.authority.parent i with
    | none => simp [hp] at hi
    | some p =>
      simp [hp] at hi
      have heq : (i, p) = e := hi
      rw [← heq]
      exact hp
  exact hwf e.1 e.2 hdr

/-! ## Depth and Distance -/

/-- Depth of an agent in the hierarchy (distance from root) -/
def depth (H : HierarchicalNetwork S) (i : Fin H.numAgents) : ℕ :=
  H.authority.depth i

/-- Root has depth 0 -/
theorem depth_root (H : HierarchicalNetwork S) : H.depth H.root = 0 :=
  H.authority.depth_root H.numAgents_pos

/-! ## Well-formedness Implies Path Compatibility -/

/-- In a well-formed hierarchy, any path of direct reports has cumulative compatibility.
    This is the key to constructing alignment witnesses. -/
theorem path_compatible (H : HierarchicalNetwork S) (hwf : H.wellFormed)
    (i : Fin H.numAgents) (k : ℕ) (hk : k ≤ H.depth i) :
    ∃ path : List (Fin H.numAgents),
      path.length = k + 1 ∧
      path.head? = some i ∧
      (∀ m (hm : m + 1 < path.length),
        H.compatible (path.get ⟨m, Nat.lt_of_succ_lt hm⟩) (path.get ⟨m + 1, hm⟩)) := by
  -- The path to root provides such a sequence
  -- Proof requires: (1) pathToRoot length = depth + 1
  --                 (2) adjacent elements in pathToRoot are parent-child pairs
  -- Both require additional infrastructure theorems
  sorry

end HierarchicalNetwork

/-! ## Conversion to Value Systems Array -/

/-- Extract the array of value systems from a hierarchical network -/
def hierarchyToValueSystems (H : HierarchicalNetwork S) : Fin H.numAgents → Perspective.ValueSystem S :=
  H.systems

end MultiAgent
