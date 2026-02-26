# Cohomology-Foundations

Lean 4 formalization of cohomology theory with applications to multi-agent coordination and AI alignment.

## Codebase Statistics

| Metric | Value |
|--------|-------|
| Total `.lean` files | 150 |
| Sorries | 0 |
| Axioms | 18 (in auxiliary modules; all core theorems are axiom-free) |

## Module Structure

| Directory | Files | Purpose |
|-----------|-------|---------|
| `Foundations/` | 9 | Simplices, cochains, coboundary (δ²=0), cohomology |
| `Infrastructure/` | 54 | Axiom elimination, graph utilities |
| `H1Characterization/` | 11 | Forest ⟺ H¹=0 theorems |
| `MultiAgent/` | 29 | Game theory + cohomology |
| `Perspective/` | 47 | Barriers, repair, fairness, critical points |

## Key Results

- **δ²=0** (`delta_squared_zero`): The coboundary operator squares to zero — axiom-free
- **H¹ characterization** (`h1_trivial_iff_oneConnected`): H¹(K)=0 ⟺ K is a forest — axiom-free
- **Impossibility** (`no_universal_reconciler_strong`): No universal reconciler exists — axiom-free
- **Tree authority** (`tree_authority_h1_trivial`): Tree-structured authority implies H¹=0 — axiom-free

## Axiom Status

All 18 remaining axioms are confined to auxiliary application modules in `Perspective/` (Morse theory, attractor basins, optimal repair, etc.) and do not appear in the transitive dependency chain of any core theorem.