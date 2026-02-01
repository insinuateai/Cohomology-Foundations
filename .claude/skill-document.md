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
- **set vs let for Fintype**: `set G' := expr with hG'` creates different Fintype instance than parameter. Use `let G' := expr` and explicitly reference instance: `@Fintype.card G'.ConnectedComponent inst`
- **endpoint_notMem_support_takeUntil**: Use to prove `v ∉ (p.takeUntil w hw).support` for simple paths ending at v
- **▸ operator fails for Reachable**: `hG'.symm ▸ h` fails with "failed to compute motive". Use helper: `def reachable_cast (heq : G1 = G2) (h : G1.Reachable a b) : G2.Reachable a b := heq ▸ h`
- **absurd for False→goal**: When deriving goal from contradiction, use `exact absurd hReach hNotReach` not `exact hNotReach hReach`
- **Fintype instance mismatch**: When `convert` leaves goal `Fintype.card X = Fintype.card X` with different instances, use `simp only [Fintype.card_eq_nat_card]` to normalize both sides to `Nat.card` (instance-independent)

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

## Session Log

<!-- Newest first -->
- 2026-02-01: **ForestEulerFormula.lean COMPLETE (0 sorries, 0 axioms)** - Eliminated 2 TEMP axioms (`component_injection_technical`, `path_reroute_around_edge`) by importing `Infrastructure.TreeGraphInfra`. Key fix: use `Fintype.card_eq_nat_card` to resolve Fintype instance mismatches when `convert` leaves cardinality equality goals with different instances.
- 2026-02-01: **TreeGraphInfra.lean COMPLETE (0 sorries)** - Fixed all 7 sorries for Euler formula. Key patterns: (1) `Walk.length_takeUntil_lt h hne` proves prefix length < walk length, (2) `takeUntil_first_endpoint_no_edge`: if edge in walk, one of takeUntil u/v doesn't contain it, (3) For repeated edge traversal: use reverse walk + takeUntil_first_endpoint_no_edge, (4) Strong induction IH: just pass `(G', h_acyc', h_not_conn')` - no edge count equality needed, (5) Use `simp only [Subtype.coe_mk]` to unify `{↑⟨e, he_set⟩}` with `{e}` before omega.
- 2026-01-31: **bridge_splits_component_aux COMPLETE** - Axiom eliminated. Key fixes: (1) Use `let` not `set` for `G'` to preserve Fintype instance, (2) Use `endpoint_notMem_support_takeUntil` for path edge analysis, (3) Use `Nat.le_antisymm h_upper (Nat.succ_le_of_lt h_strict)` instead of omega for Fintype card equality. Proof: surjective f gives lower bound, non-injectivity from bridge gives strict, upper bound from injection to G.CC⊕Unit.
- 2026-01-31: **Full Build Success** - Build completes with 3174 jobs. TreeGraphInfra.lean has 6 sorries for Walk→deleteEdges conversions. Key finding: use `Walk.toDeleteEdge` with proof `e ∉ p.edges` (see pattern above).
- 2026-01-31: Fixed Mathlib 4.27.0 compatibility across 8+ files. Key API changes documented above. TreeH1Trivial.lean compiles (2 sorries). ConnectedCocycleLemma.lean complete (0 sorries). DoubleSquaredZero.lean complete (sum_involution pattern).
- 2026-01-30: TreeGraphInfra.lean added. TreeAuthority.lean `pathBetween_head/last` fixed. `alignment_computable` fixed.
