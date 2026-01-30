# Self-Contained Prompt 2: acyclic_euler_eq (disconnected case)

## Goal
Prove that for an acyclic graph (forest): `|E| + c = |V|` where c = number of connected components.

The connected case is already handled - we need the **disconnected forest** case.

## Mathlib Version
v4.27.0 (Lean 4)

## Required Imports
```lean
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
```

## Context: What's Already Proved
```lean
-- From GraphTheoryUtils.lean (already complete):
theorem has_cycle_iff_not_acyclic (G : SimpleGraph V) :
    (∃ v : V, ∃ p : G.Walk v v, p.IsCycle) ↔ ¬G.IsAcyclic

-- Already proved in same file:
theorem edges_plus_components_ge_vertices
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent] [Nonempty V] :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent ≥ Fintype.card V
```

## Statement to Prove
```lean
theorem acyclic_euler_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent] [Nonempty V]
    (h_acyc : G.IsAcyclic) :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent = Fintype.card V := by
  by_cases h_conn : G.Connected
  · -- Connected case: G is a tree (already handled)
    have h_tree : G.IsTree := ⟨h_conn, h_acyc⟩
    have h_one_comp : Fintype.card G.ConnectedComponent = 1 := by
      rw [Fintype.card_eq_one_iff]
      use G.connectedComponentMk (Classical.arbitrary V)
      intro c
      obtain ⟨v, rfl⟩ := c.exists_rep
      exact ConnectedComponent.eq.mpr (h_conn.preconnected v (Classical.arbitrary V))
    rw [h_one_comp]
    exact h_tree.card_edgeFinset
  · -- Disconnected forest: NEEDS PROOF
    sorry
```

## Mathematical Background
For a disconnected forest:
1. Each connected component is a tree (by `IsAcyclic.isTree_connectedComponent`)
2. For a tree: `|E_i| + 1 = |V_i|` (Mathlib's `IsTree.card_edgeFinset`)
3. Edges partition by component: `|E| = Σ|E_i|`
4. Vertices partition by component: `|V| = Σ|V_i|`
5. Therefore: `|E| + c = Σ|E_i| + c = Σ(|V_i| - 1) + c = |V| - c + c = |V|`

## Suggested Proof Strategy

**Approach 1: Strong induction on edges**
- Base (|E| = 0): c = |V|, so |E| + c = |V| ✓
- Step: Pick any edge e (it's a bridge since forest). Remove it.
  - G' is still acyclic
  - G' has one more component (bridge removal splits)
  - By IH: |E'| + c' = |V|, i.e., (|E|-1) + (c+1) = |V|
  - So |E| + c = |V| ✓

**Approach 2: Use both inequalities**
- We have `|E| + c ≥ |V|` from `edges_plus_components_ge_vertices`
- Prove `|E| + c ≤ |V|` for forests (each tree has exactly |V_i| - 1 edges)
- Together: `|E| + c = |V|`

## Key Mathlib Lemmas
```lean
-- Each component of a forest is a tree
IsAcyclic.isTree_connectedComponent : G.IsAcyclic → ∀ c, c.toSimpleGraph.IsTree

-- Tree edge count
IsTree.card_edgeFinset : G.IsTree → G.edgeFinset.card + 1 = Fintype.card V

-- Bridge characterization for acyclic graphs
isAcyclic_iff_forall_edge_isBridge : G.IsAcyclic ↔
    (∀ e ∈ G.edgeSet, G.IsBridge e) ∧ (∀ e ∈ G.edgeSet, G.IsBridge e)

-- Edge deletion
SimpleGraph.deleteEdges : SimpleGraph V → Set (Sym2 V) → SimpleGraph V

-- Connectivity and components
ConnectedComponent.eq : connectedComponentMk u = connectedComponentMk v ↔ Reachable u v
```

## Tactics to Prefer
- `omega` for natural number arithmetic
- `Nat.strong_induction_on` for strong induction
- `by_cases` for case analysis
- `calc` for equation chains

## Output Format
Provide a complete proof for the `sorry` in the disconnected case. The proof should:
1. Compile with Mathlib v4.27.0
2. Not introduce any axioms
3. Use only the lemmas available in the imports listed above

## Known Pitfalls
- When removing a bridge edge, proving that component count increases by exactly 1 requires careful argument about reachability
- The map from G-components to G'-components needs to track that exactly one component splits
- `decide_eq_false`/`decide_eq_true` instead of `decide_False`/`decide_True`
