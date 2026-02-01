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
- After `simp` changes goal structure, explicit `rfl` may be needed. When simp with `List.mem_cons` reduces membership to `True ∨ _`, use `simp only [..., true_or]` rather than `exact Or.inl rfl`
- `↓reduceIte` is needed to simplify `if true = true then ... else ...`

### Mathlib 4.27.0 API Changes
- **Reachable**: No `.somePath.toPath` - use `reachableToPath h := (Classical.choice h).toPath`
- **Sum.noConfusion**: No `.elim` field - use direct contradiction or `reduceCtorEq`
- **Walk**: No `.reachable_of_mem_support` - use `.takeUntil` to construct prefix walk
- **Walk induction**: `induction p with` may fail with "Invalid target: Index in target's type is not a variable" when walk endpoints are Sum types like `Sum.inl v`. Use `match p with` pattern matching instead. For defining recursive functions, use explicit patterns: `@Walk.cons _ _ _ (.inl v') _ hadj rest`
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
| `Walk.transfer H hp` | Transfer walk to H when `hp : ∀ e ∈ p.edges, e ∈ H.edgeSet` |
| `IsCycle.transfer hc hp` | Transfer cycle to H (preserves IsCycle) |
| `Walk.induce s hs` | Walk in `G.induce s` when `hs : ∀ x ∈ p.support, x ∈ s` |
| `cons_isCycle_iff` | `(cons h p).IsCycle ↔ p.IsPath ∧ s(u,v) ∉ p.edges` |
| `List.Nodup.pmap f _ nodup` | Preserve Nodup through pmap with injective f |
| `Walk.edges_subset_edgeSet` | `e ∈ p.edges → e ∈ G.edgeSet` |
| `Reachable.mono hle h` | If `G ≤ G'` and `G.Reachable u v` then `G'.Reachable u v` |

## Build Speed

- **tmpfs (RAM disk)**: `make tmpfs-mount` → 12.8x faster builds (3m7s → 14.6s). Auto-save: `make tmpfs-autosave`
- **After deleting .lean files**: Kill stale workers with `pkill -f "lean --worker.*DeletedFileName"` or reload VSCode window
- **Fast build**: `make fast` or `lake build --old` (uses cached oleans, ~2s)
- **Mathlib cache**: `lake exe cache get` (downloads pre-built oleans, ~2min)
- **Clean project only**: `make clean` (preserves Mathlib cache)
- **Clean all**: `make clean-all` (SLOW - rebuilds Mathlib!)
- **Linter disabled**: lakefile.toml disables unusedVariables, unnecessarySeqFocus, etc.
- **Lake parallelism**: Automatic in Lake 5.0.0 (no `-j` flag needed)

## Session Log

<!-- Newest first -->
- 2026-02-01: **sumGraph projection lemmas** - For walks in `sumGraph G H` (disjoint union on `V ⊕ W`), need pattern match on next vertex: `@Walk.cons _ _ _ (.inl v') _ hadj rest`. Use `.elim` on `sumGraph_no_cross_lr` for impossible cases. Edge lemmas need BOTH directions: `sumGraph_project_left_edge_mem` (original→projected) AND `sumGraph_project_left_edge_mem_rev` (projected→original) for contrapositive proofs. Axioms: 89→88.
- 2026-02-01: **GraphComposition axiom elimination** - Eliminated 2 axioms: `cycle_transfer_to_subgraph_aux` (use `Walk.transfer`+`IsCycle.transfer`), `acyclic_of_disjoint_acyclic_parts_aux` (use `Walk.induce`+partition argument). Key: `cases c with | nil => ... | cons hadj rest => ...` for walk induction; access next vertex via `hs' _ rest.start_mem_support`. Axioms remaining: 89.
- 2026-02-01: **Build optimization** - tmpfs RAM disk (12.8x speedup). Cleanup: deleted 9 root files (70 sorries), fixed comments. State: 0 sorries, 91→89 axioms.
- 2026-02-01: **H1Characterization/ & Perspective/ CLEAN** - Main theorem `h1_trivial_iff_oneConnected` complete. `acyclic_implies_h1_trivial` via per-component root selection.
- 2026-01-31: **Full Build Success** - Mathlib 4.27.0 compatibility complete.
