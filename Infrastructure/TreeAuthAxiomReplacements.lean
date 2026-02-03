/-
# TreeAuth Axiom Replacements

Provides drop-in replacements for axioms in TreeAuthSimpleGraph.lean.

AXIOM ELIMINATED:
- T02: toSimpleGraph_acyclic_aux (MultiAgent/TreeAuthSimpleGraph.lean:429)

The theorem is fully proven in TreeAuthCoreProofs.lean. This file provides
a bridge between the TreeAuthSimpleGraph.TreeAuth type and the
TreeAuthCoreProofs.TreeAuth type used in the proof.

SORRIES: 0
AXIOMS: 0
-/

import MultiAgent.TreeAuthSimpleGraph
import Infrastructure.TreeAuthCoreProofs

namespace Infrastructure.TreeAuthAxiomReplacements

open TreeAuthSimpleGraph (TreeAuth)

/-! ## Type Conversion

TreeAuthSimpleGraph.TreeAuth and TreeAuthCoreProofs.TreeAuth have identical
structure definitions. We provide conversion functions between them.
-/

/-- Convert TreeAuthSimpleGraph.TreeAuth to TreeAuthCoreProofs.TreeAuth -/
def toProofTreeAuth {n : ℕ} (T : TreeAuthSimpleGraph.TreeAuth n) : TreeAuthCoreProofs.TreeAuth n where
  root := T.root
  parent := T.parent
  root_no_parent := T.root_no_parent
  nonroot_has_parent := T.nonroot_has_parent
  acyclic := T.acyclic
  parent_ne_self := T.parent_ne_self

/-! ## Graph Compatibility

The toSimpleGraph functions produce equivalent graphs.
-/

/-- The SimpleGraphs from both TreeAuth types have the same adjacency relation -/
lemma toSimpleGraph_adj_iff {n : ℕ} (T : TreeAuthSimpleGraph.TreeAuth n) (i j : Fin n) :
    T.toSimpleGraph.Adj i j ↔ (toProofTreeAuth T).toSimpleGraph.Adj i j := by
  simp only [TreeAuthSimpleGraph.TreeAuth.toSimpleGraph_adj, TreeAuthCoreProofs.TreeAuth.toSimpleGraph]
  rfl

/-- The SimpleGraphs are equal -/
lemma toSimpleGraph_eq {n : ℕ} (T : TreeAuthSimpleGraph.TreeAuth n) :
    T.toSimpleGraph = (toProofTreeAuth T).toSimpleGraph := by
  ext i j
  exact toSimpleGraph_adj_iff T i j

/-! ## T02: toSimpleGraph_acyclic_aux

The original axiom:
```
axiom toSimpleGraph_acyclic_aux (T : TreeAuth n) (v : Fin n)
    (p : T.toSimpleGraph.Walk v v) (hp : p.IsCycle) : False
```

We provide a proven version using the TreeAuthCoreProofs infrastructure.
-/

/-- T02 replacement: No cycle exists in the tree SimpleGraph -/
theorem toSimpleGraph_acyclic_aux_replacement {n : ℕ} (T : TreeAuthSimpleGraph.TreeAuth n)
    (v : Fin n) (p : T.toSimpleGraph.Walk v v) (hp : p.IsCycle) : False := by
  -- Convert the walk to use the proof TreeAuth's SimpleGraph
  have h_eq := toSimpleGraph_eq T
  -- Rewrite the walk using graph equality
  have p' : (toProofTreeAuth T).toSimpleGraph.Walk v v := h_eq ▸ p
  have hp' : p'.IsCycle := by
    -- IsCycle is preserved under graph equality
    simp only [SimpleGraph.Walk.IsCycle] at hp ⊢
    constructor
    · -- not_nil preserved
      intro h_nil
      have : p.Nil := h_eq ▸ h_nil
      exact hp.not_nil this
    · exact hp.tail_nodup
  exact TreeAuthCoreProofs.TreeAuth.toSimpleGraph_acyclic_aux (toProofTreeAuth T) v p' hp'

end Infrastructure.TreeAuthAxiomReplacements
