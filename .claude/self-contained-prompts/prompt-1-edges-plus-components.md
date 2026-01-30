# Self-Contained Prompt 1: edges_plus_components_ge_vertices

## Goal
Prove that for any finite simple graph: `|E| + c ≥ |V|` where c = number of connected components.

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

## Partial Proof (base case done, inductive step needed)
```lean
theorem edges_plus_components_ge_vertices
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Fintype G.ConnectedComponent] [Nonempty V] :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent ≥ Fintype.card V := by
  by_cases h_edge : G.edgeFinset.card = 0
  · -- Base case: No edges means c = |V| (COMPLETE)
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
        | succ n =>
          exfalso
          have hadj : G.Adj (p.getVert 0) (p.getVert 1) := p.adj_getVert_succ (by omega)
          have h_in_edge : s(p.getVert 0, p.getVert 1) ∈ G.edgeSet := mem_edgeSet.mpr hadj
          rw [h_empty] at h_in_edge
          exact h_in_edge
    rw [h_eq, h_edge]; omega
  · -- Inductive step: At least one edge (NEEDS PROOF)
    sorry
```

## Mathematical Background
Each connected component with n_i vertices needs at least n_i - 1 edges to be connected.
Summing over all components: |E| ≥ Σ(n_i - 1) = |V| - c
Therefore: |E| + c ≥ |V|

## Suggested Proof Strategy
**Strong induction on |E|:**

1. **Base case (|E| = 0):**
   - No edges means each vertex is its own component
   - So c = |V|, hence |E| + c = 0 + |V| = |V| ✓
   - Key: Show the map `V → G.ConnectedComponent` via `connectedComponentMk` is bijective when |E| = 0

2. **Inductive step (|E| = n + 1):**
   - Pick any edge e = {u, v}
   - Define G' = G.deleteEdges {s(u,v)}
   - G' has n edges
   - By IH: G'.edgeFinset.card + Fintype.card G'.ConnectedComponent ≥ Fintype.card V
   - Two cases for the removed edge:
     - **Bridge:** Removing it increases components by 1, so c' = c + 1
       - Then: n + (c + 1) ≥ |V|, so (n+1) + c ≥ |V| ✓
     - **Not a bridge:** Removing it keeps same component count, so c' = c
       - Then: n + c ≥ |V|, so (n+1) + c > |V| ✓

## Key Mathlib Lemmas to Use
```lean
-- Edge deletion
SimpleGraph.deleteEdges : SimpleGraph V → Set (Sym2 V) → SimpleGraph V
SimpleGraph.deleteEdges_edgeSet : (G.deleteEdges s).edgeSet = G.edgeSet \ s

-- Component connectivity
ConnectedComponent.eq : G.connectedComponentMk u = G.connectedComponentMk v ↔ G.Reachable u v
ConnectedComponent.exists_rep : ∀ c : G.ConnectedComponent, ∃ v, G.connectedComponentMk v = c

-- Bridge characterization
SimpleGraph.IsBridge : Sym2 V → Prop
SimpleGraph.isBridge_iff : G.IsBridge e ↔ e ∈ G.edgeSet ∧ ¬(G.deleteEdges {e}).Reachable u v
  -- where e = s(u, v)

-- Walk/reachability
Walk.eq_of_length_eq_zero : p.length = 0 → u = v
Walk.adj_getVert_succ : 0 < p.length → G.Adj (p.getVert i) (p.getVert (i+1))
```

## Tactics to Prefer
- `omega` for natural number arithmetic
- `by_cases` for case splits on decidable propositions
- `Fintype.card_eq.mpr ⟨equiv⟩` for cardinality arguments
- `Finset.card_eq_zero` / `Finset.card_pos` for empty/nonempty edge sets

## Output Format
Please provide a complete Lean 4 proof that compiles with Mathlib v4.27.0. Include any helper lemmas needed. The proof should replace the `sorry` in the theorem statement above.

## Known Pitfalls (from this codebase)
- `decide_False`/`decide_True` don't exist in this Mathlib version - use `decide_eq_false`/`decide_eq_true`
- After `simp` changes goal structure, explicit `rfl` may be needed
- `↓reduceIte` is needed to simplify `if true = true then ... else ...`
