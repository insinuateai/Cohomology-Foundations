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
- 2026-02-02: **Game Theory axioms eliminated (3)** - Created `Infrastructure/GameTheoryProofs.lean`. Proved: `supermodular_of_convex` (induction on |T\S|, apply IH to S'=insert i S), `marginal_sum_telescope` (sum over {j<k} telescopes), `convex_marginal_sum_ge` (induction on |S|, max element is S-predecessor). Updated CoalitionGameCore.lean (2 axioms→0), GameTheoryBridge.lean (1→0). Pattern: use `Finset.max'` for max element, `sPredecessors S m = S.erase m` when m is max. Axioms: 73→70.
- 2026-02-01: **cycleIndicator_is_cocycle axiom eliminated** - Added `hasNoFilledTriangles K` hypothesis to forward direction of main theorem. Key insight: the axiom is FALSE for complexes with filled 2-simplices (counterexample: filled triangle gives δf ≠ 0). For hollow complexes, use proven `cycleIndicator_is_cocycle_hollow` (via `cochain_one_is_cocycle_of_no_2simplices`). Pattern: when eliminating axioms by adding hypotheses, use direct theorems (`oneConnected_implies_h1_trivial`) for backward direction instead of iff rewrites (avoids needing hypothesis for unused direction). Files updated: CycleCochain/Definitions.lean, Characterization.lean, SmallGraphs.lean, LinearComplexity.lean, ConflictLocalization.lean, ConflictResolution.lean, AgentCoordination.lean, IncrementalUpdates.lean, HierarchicalAlignment.lean, DimensionBound.lean. Axioms: 72→71.
- 2026-02-01: **Axiom signature mismatch analysis** - AxiomElimination.lean theorems with same names as source file axioms may have DIFFERENT signatures: (1) `forms_cycle_from_global_failure` in AxiomElim returns cocycle existence, source returns pairwise agreement; (2) `fairness_loss_bounded` in AxiomElim has h_total/h_valid hypotheses, source is unconditional; (3) `h1_trivial_implies_fair_allocation` in AxiomElim just unfolds H1Trivial definition, source proves ∃ fair allocation. Pitfall: Same-named declarations across files aren't necessarily duplicates - always compare full signatures before attempting elimination.
- 2026-02-01: **Deleted 7 unused axioms** - Removed `potential_has_nash`, `h1_local_global_gap`, `convex_implies_superadditive`, `convex_nonempty_core`, `core_h1_relation`, `convex_h1_zero`, `h1_pos_ic_obstruction` from MultiAgent/. Pitfall: docstrings before axioms sometimes extend upward; deleting just the axiom+immediate docstring can leave orphaned comment blocks causing "unterminated comment" errors.
- 2026-02-01: **TreeAuthDepthTheory 4 axioms → 0** - Refactored depth to `Nat.find` (cleaner than fuel), pathToRoot to well-founded recursion (`termination_by T.depth i`). Proved: `depth_parent`, `pathToRoot_last_is_root`, `pathToRoot_consecutive`, `pathToRoot_unique_induction`, `walk_adjacent_extraction`. Two sorries remain: `depth_bounded` (pigeonhole), `no_cycle_via_depth_aux` (minimum depth argument needs careful case analysis). Patterns: `conv_lhs => unfold f` prevents simp loops on recursive defs; `induction' hd : expr using Nat.strong_induction_on with d ih generalizing vars` for strong induction.
- 2026-02-01: **envy_free_implies_proportional_identical_ax eliminated** - `Perspective/EnvyFreeness.lean`: Envy-free ⇒ all values equal ⇒ each ≥ average. Key: `div_le_div_of_nonneg_right` needs `0 ≤ n` not `n > 0`, use `le_of_lt`. Axioms: 72→71.
- 2026-02-01: **simple_graph_edge_bound axiom eliminated** - `Perspective/DimensionBound.lean`: replaced axiom with proof using `SimpleGraph.card_edgeFinset_le_card_choose_two` + `Nat.choose_two_right`. Pattern: graph edge bounds often have Mathlib lemmas in `Combinatorics/SimpleGraph/Finite.lean`.
- 2026-02-01: **Axiom triage** - Best targets for elimination: (1) `Theories/TreeAuthDepthTheory.lean` (4 axioms, Mathlib-only imports, self-contained), (2) `Infrastructure/GraphComposition.lean` (1 axiom). Total: ~88 axioms across 44 files. Priority factors: self-containment > feasibility (graph theory easier than spectral) > impact count.
- 2026-02-01: **sumGraph projection lemmas** - For walks in `sumGraph G H` (disjoint union on `V ⊕ W`), need pattern match on next vertex: `@Walk.cons _ _ _ (.inl v') _ hadj rest`. Use `.elim` on `sumGraph_no_cross_lr` for impossible cases. Edge lemmas need BOTH directions: `sumGraph_project_left_edge_mem` (original→projected) AND `sumGraph_project_left_edge_mem_rev` (projected→original) for contrapositive proofs. Axioms: 89→88.
- 2026-02-01: **GraphComposition axiom elimination** - Eliminated 2 axioms: `cycle_transfer_to_subgraph_aux` (use `Walk.transfer`+`IsCycle.transfer`), `acyclic_of_disjoint_acyclic_parts_aux` (use `Walk.induce`+partition argument). Key: `cases c with | nil => ... | cons hadj rest => ...` for walk induction; access next vertex via `hs' _ rest.start_mem_support`. Axioms remaining: 89.
- 2026-02-01: **Build optimization** - tmpfs RAM disk (12.8x speedup). Cleanup: deleted 9 root files (70 sorries), fixed comments. State: 0 sorries, 91→89 axioms.
- 2026-02-01: **H1Characterization/ & Perspective/ CLEAN** - Main theorem `h1_trivial_iff_oneConnected` complete. `acyclic_implies_h1_trivial` via per-component root selection.
- 2026-01-31: **Full Build Success** - Mathlib 4.27.0 compatibility complete.
