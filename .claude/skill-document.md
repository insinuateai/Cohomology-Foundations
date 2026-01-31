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

**Component-wise summing** (e.g., Σ|E_i| = |E|) requires `Setoid.IsPartition.ncard_eq_finsum` pattern.

## Session Log

<!-- Newest first -->
- 2026-01-31: Completed `bridge_splits_component` in ExtendedGraphInfra.lean. Key technique: define surjective map f : G'.CC → G.CC, show bridge endpoints are same in G but different in G', derive card G'.CC = card G.CC + 1 via bijection contradiction. File now has 0 sorries.
- 2026-01-31: DoubleSquaredZero.lean - Implemented self-contained δ² = 0 proof using sign-reversing involution on index pairs. Key pattern: `Finset.sum_involution` with involution τ(i,j) = (j, i-1) when j < i, else (j+1, i).
- 2026-01-30: TreeGraphInfra.lean - Added graph theory infrastructure for DimensionBound. 3 sorries remain requiring component-wise reasoning (edges_plus_components_ge_vertices, acyclic_euler_eq disconnected, euler_eq_implies_acyclic'). Build succeeds.
- 2026-01-30: Fixed broken `pathBetween_head`/`pathBetween_last` in TreeAuthority.lean (Mathlib API changes). `path_compatible` needs missing infrastructure (pathToRoot length, adjacent elements are parent-child)
- 2026-01-30: Fixed 2 sorries in `alignment_computable` using existing `pathBetween_head`/`pathBetween_last` theorems
