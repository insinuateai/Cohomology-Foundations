# Skill Document

> Update at end of each session. **Keep under 100 lines** - compress when needed.

## Tactics

| Situation | Use |
|-----------|-----|
| Nat arithmetic | `omega` |
| Ring equations | `ring` |
| Sum cancellation | `Finset.sum_involution` |

## Pitfalls

- `subst x` with `h : x = i` replaces ALL `i` with `x`, breaking references to `i`. Use `subst i` (direction matters) or work with `rw`
- `decide_False`/`decide_True` don't exist. Use `decide_eq_false (h : ¬P)` and `decide_eq_true (h : P)`
- `List.length_filterMap` doesn't exist in this Mathlib version
- After `simp` changes goal structure, explicit `rfl` may be needed
- `↓reduceIte` is needed to simplify `if true = true then ... else ...`

### Mathlib 4.27.0 API Changes
- **Reachable**: No `.somePath.toPath` - use `reachableToPath h := (Classical.choice h).toPath`
- **Sum.noConfusion**: No `.elim` field - use direct contradiction or `reduceCtorEq`
- **Walk**: No `.reachable_of_mem_support` - use `.takeUntil` to construct prefix walk
- **Walk induction**: `induction p with` may fail with "Invalid target" - use `sorry` or case-by-case
- **SimpleGraph.mem_edgeSet**: No `.mp` - membership works directly without projection
- **IsTree**: No `.connected` field - use `.1` for tuple access (IsTree = Connected ∧ IsAcyclic)
- **Connected**: Use `Connected.mk` with Preconnected first, Nonempty as instance
- **IsAcyclic**: Definition is `∀ ⦃v⦄ (c : Walk v v), ¬c.IsCycle` - pass walk then cycle proof
- **Fintype.card_of_bijective**: Use `Fintype.card_congr (Equiv.ofBijective _ proof)`
- **Set notation `{e}`**: May need explicit type `({e} : Set (Sym2 V))` in some contexts
- **⟨...⟩ notation**: Can fail on And/Exists - use explicit `And.intro` or `Exists.intro`
- **deleteEdges_edgeSet vs edgeSet_deleteEdges**: Use `edgeSet_deleteEdges` for `(G.deleteEdges s).edgeSet`
- **Sym2.eq_iff.mp**: Returns `(a = a' ∧ b = b') ∨ (a = b' ∧ b = a')` - check direction of equality
- **Sym2 endpoints**: Use `Sym2.ind (fun v w => ⟨v, w, rfl⟩) e` to get `∃ v w, s(v,w) = e`
- **IsBridge**: Mathlib uses `G \ fromEdgeSet {e}`, code may use `G.deleteEdges {e}` - prove they're equivalent

## Patterns

- For `by_cases` on decidable props with `decide`, prove `decide P = true/false` explicitly:
  ```lean
  have hdec : decide (i ≠ j) = false := decide_eq_false (not_not.mpr h)
  simp only [hdec, Bool.false_eq_true, ↓reduceIte]
  ```
- `congrArg some h` to lift `h : a = b` to `some a = some b`

## Graph Theory Infrastructure

| Mathlib Lemma | Use |
|---------------|-----|
| `IsTree.card_edgeFinset` | Tree on n vertices has n-1 edges |
| `IsAcyclic.isTree_connectedComponent` | Each component of forest is tree |
| `isAcyclic_iff_forall_edge_isBridge` | Acyclic ↔ all edges are bridges |
| `iUnion_connectedComponentSupp` | Components partition vertex set |
| `Walk.toDeleteEdge e p hp` | Convert `G.Walk` to `(G.deleteEdges {e}).Walk` when `hp : e ∉ p.edges` |
| `Walk.toDeleteEdges s p hp` | Convert walk when `hp : ∀ e ∈ p.edges, e ∉ s` |
| `Walk.edges_subset_edgeSet` | `e ∈ p.edges → e ∈ G.edgeSet` |
| `Reachable.mono hle h` | If `G ≤ G'` and `G.Reachable u v` then `G'.Reachable u v` |
| `deleteEdges_le {e}` | `G.deleteEdges {e} ≤ G` (for `mapLe`) |

**Walk→DeleteEdges pattern** (prove `e ∉ p.edges` by contradiction):
```lean
have hp_no_e : e ∉ p.edges := by
  intro h_in
  have := Walk.edges_subset_edgeSet p h_in  -- e ∈ (G.deleteEdges {e}).edgeSet
  simp only [edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff] at this
  exact this.2 rfl
exact ⟨p.toDeleteEdge e hp_no_e⟩  -- G'-reachability
```

**Component-wise summing** (e.g., Σ|E_i| = |E|) requires `Setoid.IsPartition.ncard_eq_finsum` pattern.

## Axiom Elimination Patterns

**Walk Transfer Pattern** (transfer walk to subgraph when edges present):
```lean
def walk_transfer {G H} (p : G.Walk u v) (h : ∀ e ∈ p.edges, e ∈ H.edgeSet) : H.Walk u v := by
  induction p with
  | nil => exact Walk.nil
  | @cons x y z hadj rest ih =>
    have h_xy : s(x,y) ∈ H.edgeSet := h _ (by simp [Walk.edges_cons])
    exact Walk.cons (mem_edgeSet.mp h_xy) (ih (fun e he => h e (by simp [he])))
```

**Cycle Transfer Theorem**: `walk_transfer` preserves edges/support/IsTrail/IsCycle.

**Partition Walk Pattern** (walks stay in partition when no cross edges):
```lean
theorem walk_stays_in_part (p : G.Walk u v) (P : V → Prop)
    (h_no_cross : ∀ a b, P a → ¬P b → ¬G.Adj a b) (hu : P u) :
    ∀ x ∈ p.support, P x := by induction p ...
```

## Session Log

<!-- Newest first -->
- 2026-02-02: **AxiomSolver.lean created** - Comprehensive axiom elimination file with: (1) cycle_transfer_to_subgraph_theorem (fully proven), (2) forest_single_edge_still_forest_theorem (1 sorry), (3) acyclic_of_disjoint_acyclic_parts_theorem (2 sorries), (4) forest_union_forest_acyclic_theorem (3 sorries). Key infrastructure: walk_transfer, walk_transfer_isCycle, walk_stays_in_part, acyclic_implies_bridge all fully proven.
- 2026-01-31: **Full Build Success** - Build completes with 3174 jobs. TreeGraphInfra.lean has 6 sorries for Walk→deleteEdges conversions. Key finding: use `Walk.toDeleteEdge` with proof `e ∉ p.edges` (see pattern above).
- 2026-01-31: Fixed Mathlib 4.27.0 compatibility across 8+ files. Key API changes documented above. TreeH1Trivial.lean compiles (2 sorries). ConnectedCocycleLemma.lean complete (0 sorries). DoubleSquaredZero.lean complete (sum_involution pattern).
- 2026-01-30: TreeGraphInfra.lean added. TreeAuthority.lean `pathBetween_head/last` fixed. `alignment_computable` fixed.
