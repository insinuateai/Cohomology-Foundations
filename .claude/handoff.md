# Agent Handoff Document

> Overwritten each session. Previous versions in git history.
> Read CLAUDE.md and skill-document.md first, then this file.

## Session Metadata

- **Date**: 2026-02-02
- **Primary goal**: Fix `acyclic_periodic_orbit_equiv` sorry and eliminate axioms
- **User intent**: Understand and fix the "incorrect for root case" sorry at TreeAuthCoreProofs.lean:486

## What Was Accomplished

### Completed
- [x] Fixed `acyclic_periodic_orbit_equiv` theorem statement (was mathematically false)
- [x] Removed sorry from TreeAuthCoreProofs.lean:486
- [x] Created bridging lemmas to connect local TreeAuth to TreeAuthCoreProofs.TreeAuth
- [x] Eliminated X28 and X29 axioms from HierarchicalNetworkComplete.lean
- [x] Updated axiom-registry.md with eliminations

### Key Changes

| File | Change |
|------|--------|
| `Infrastructure/TreeAuthCoreProofs.lean:472` | Fixed theorem: added `i ≠ T.root →` to RHS |
| `Infrastructure/TreeAuthCoreProofs.lean:486` | Removed sorry (proof now complete) |
| `Theories/HierarchicalNetworkComplete.lean:117-131` | Added bridging lemmas |
| `Theories/HierarchicalNetworkComplete.lean:248-274` | Replaced axiom with proven theorem |

### Axiom Status

- **Before**: 68 axioms
- **After**: 66 axioms
- **Eliminated**: X28 (`acyclic_periodic_orbit_equiv`), X29 (`pathToRoot_consecutive_adjacent`)

## Current State

### Sorries (3 total - reduced from 4)
| File | Line | Issue |
|------|------|-------|
| `Infrastructure/TreeAuthCoreProofs.lean` | 551 | `toSimpleGraph_acyclic_aux` - minimum-depth cycle argument |
| `Theories/TreeAuthDepthTheory.lean` | 127 | `depth_bounded` - pigeonhole for depth bound |
| `Theories/TreeAuthDepthTheory.lean` | 408 | `no_cycle_via_depth_aux` |

### Key Insight from This Session

**When an axiom's statement is mathematically false, fix the statement rather than trying to prove the unprovable.**

The original `acyclic_periodic_orbit_equiv` claimed:
```
(∀ i, ∃ k, parentOrRoot^[k] i = T.root) ↔ ∀ i, ∀ k > 0, parentOrRoot^[k] i ≠ i
```

But the RHS is FALSE for the root node because `parentOrRoot root = root` (root is a fixed point). The corrected statement adds `i ≠ T.root →` to the RHS.

### Bridging Pattern for TreeAuth

When HierarchicalNetworkComplete.lean has its own local `TreeAuth` type but needs to use theorems from TreeAuthCoreProofs.lean:

```lean
-- Convert function values
lemma parentOrRoot_eq_core (T : TreeAuth n) (i : Fin n) :
    T.parentOrRoot i = T.toCore.parentOrRoot i

-- Convert iterations
lemma parentOrRoot_iterate_eq_core (T : TreeAuth n) (i : Fin n) (k : ℕ) :
    T.parentOrRoot^[k] i = T.toCore.parentOrRoot^[k] i

-- Root unchanged
lemma root_eq_core (T : TreeAuth n) : T.root = T.toCore.root
```

## Recommended Next Steps

### High Value
1. **X27** (`compose_path_reaches_root`) - Last axiom in HierarchicalNetworkComplete.lean
2. **T01-T05** - Tree authority depth axioms (TreeAuthDepthTheory.lean)

### Remaining Sorries
3. Fix `toSimpleGraph_acyclic_aux` (TreeAuthCoreProofs.lean:551) - needs minimum-depth argument
4. Fix `depth_bounded` (TreeAuthDepthTheory.lean:127) - needs pigeonhole
