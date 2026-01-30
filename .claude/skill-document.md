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

## Session Log

<!-- Newest first -->
- 2026-01-30: Fixed broken `pathBetween_head`/`pathBetween_last` in TreeAuthority.lean (Mathlib API changes). `path_compatible` needs missing infrastructure (pathToRoot length, adjacent elements are parent-child)
- 2026-01-30: Fixed 2 sorries in `alignment_computable` using existing `pathBetween_head`/`pathBetween_last` theorems
