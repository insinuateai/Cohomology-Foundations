# Self-Contained Prompt 3: euler_eq_implies_acyclic'

## Goal
Prove the converse of the Euler formula: if `|E| + c = |V|`, then the graph is acyclic.

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

## Context: Available Lemmas
```lean
-- From GraphTheoryUtils.lean:
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
theorem euler_eq_implies_acyclic'
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent]
    (h_euler : G.edgeFinset.card + Fintype.card G.ConnectedComponent = Fintype.card V) :
    G.IsAcyclic := by
  by_contra h_not_acyc
  have h_cycle := (has_cycle_iff_not_acyclic G).mpr h_not_acyc
  obtain ⟨v, p, hp⟩ := h_cycle
  -- We have a cycle. Need to derive contradiction with h_euler.
  --
  -- Key insight: A graph with a cycle has |E| + c > |V|
  -- because the cyclic component has "extra" edges beyond what a tree needs.
  --
  -- Specifically: in the component containing the cycle,
  -- we can remove one cycle edge without disconnecting the component.
  -- This shows that component has ≥ |V_i| edges (not |V_i| - 1 like a tree).
  -- So |E| ≥ (|V| - c) + 1, giving |E| + c ≥ |V| + 1 > |V|.
  -- But h_euler says |E| + c = |V|. Contradiction.
  sorry
```

## Mathematical Background
**Contrapositive approach:**
- If G has a cycle, then G is not acyclic
- A cycle means there exists a non-bridge edge (removing it keeps the component connected)
- In a graph where every edge is a bridge: `|E| + c = |V|` (each edge removal increases c by 1)
- In a graph with a non-bridge edge: `|E| + c > |V|` (removing that edge doesn't increase c)

**Direct approach:**
- A cycle on k vertices uses k edges (not k-1 like a tree)
- The component containing the cycle has at least one "extra" edge
- So `|E| ≥ |V| - c + 1`, meaning `|E| + c ≥ |V| + 1`
- This contradicts `|E| + c = |V|`

## Suggested Proof Strategy

1. **Get the cycle and its properties:**
   ```lean
   have h_3le : 3 ≤ p.length := hp.three_le_length
   ```

2. **Show there's a non-bridge edge:**
   ```lean
   -- From cycle_has_nonbridge or manual construction
   have ⟨e, he, h_not_bridge⟩ : ∃ e ∈ G.edgeSet, ¬G.IsBridge e
   ```

3. **Remove the non-bridge edge:**
   ```lean
   let G' := G.deleteEdges {e}
   -- G' has same number of components (non-bridge removal)
   have h_same_comp : Fintype.card G'.ConnectedComponent = Fintype.card G.ConnectedComponent
   -- G' has one fewer edge
   have h_fewer : G'.edgeFinset.card = G.edgeFinset.card - 1
   ```

4. **Apply the inequality to G':**
   ```lean
   have h_ge : G'.edgeFinset.card + Fintype.card G'.ConnectedComponent ≥ Fintype.card V
   -- Substituting: (|E| - 1) + c ≥ |V|
   -- But h_euler says |E| + c = |V|
   -- So |E| - 1 + c ≥ |E| + c, i.e., -1 ≥ 0. Contradiction!
   ```

## Key Mathlib Lemmas
```lean
-- Cycle properties
Walk.IsCycle.three_le_length : p.IsCycle → 3 ≤ p.length
Walk.IsCycle.support_nodup : p.IsCycle → p.support.tail.Nodup

-- Bridge characterization
IsBridge : Sym2 V → Prop
IsBridge_iff : G.IsBridge s(u,v) ↔ s(u,v) ∈ G.edgeSet ∧ ¬(G.deleteEdges {s(u,v)}).Reachable u v
isAcyclic_iff_forall_edge_isBridge : G.IsAcyclic ↔ ∀ e ∈ G.edgeSet, G.IsBridge e

-- Edge deletion preserves structure
deleteEdges_le : G.deleteEdges s ≤ G
deleteEdges_edgeSet : (G.deleteEdges s).edgeSet = G.edgeSet \ s

-- Finset operations
Finset.card_erase_of_mem : a ∈ s → (s.erase a).card = s.card - 1
```

## Helper Lemma You May Need
```lean
/-- A graph with a cycle has at least one non-bridge edge -/
theorem cycle_has_nonbridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_cycle : ∃ v : V, ∃ p : G.Walk v v, p.IsCycle) :
    ∃ e ∈ G.edgeSet, ¬G.IsBridge e := by
  by_contra h_all_bridge
  push_neg at h_all_bridge
  have h_acyc : G.IsAcyclic := isAcyclic_iff_forall_edge_isBridge.mpr ⟨h_all_bridge, h_all_bridge⟩
  obtain ⟨v, p, hp⟩ := h_cycle
  exact h_acyc p hp
```

## Output Format
Provide a complete proof replacing the `sorry`. The proof should:
1. Compile with Mathlib v4.27.0
2. Use only the imports listed
3. May define helper lemmas if needed (like `cycle_has_nonbridge` above)

## Known Pitfalls
- Proving that removing a non-bridge preserves component count requires showing reachability is maintained
- The key step is `Fintype.card_eq.mpr` with an equivalence showing components biject
- Use `omega` for the final arithmetic contradiction
- `↓reduceIte` may be needed for if-then-else simplification
