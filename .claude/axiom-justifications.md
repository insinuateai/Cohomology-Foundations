# Axiom Justification Appendix

> Publication-ready citations for external mathematical results.
> Last updated: 2026-02-04

## Summary

| Category | Count | Status |
|----------|-------|--------|
| External Math (KEEP) | 13 | Requires Mathlib extensions or external theory |
| Has Replacement | ~28 | Proven in Infrastructure/ |
| Pending | ~7 | Provable, no replacement yet |
| **Total in Codebase** | **48** | |

---

## KEEP: Cited External Results

### Spectral Graph Theory (5 axioms)

| Axiom | File | Citation |
|-------|------|----------|
| `vertexDegreeAx` | SpectralGap.lean | Standard graph theory (axiomatized to avoid decidability overhead) |
| `laplacianExists` | SpectralGap.lean | Chung, *Spectral Graph Theory* (1997), Ch. 1; L = D - A construction |
| `laplacianEigenvalues` | SpectralGap.lean | Spectral theorem for symmetric matrices |
| `eigenvalues_nonneg` | SpectralGap.lean | Chung (1997), Lemma 1.7; vᵀLv = Σ(vᵢ-vⱼ)² ≥ 0 |
| `spectral_gap_bounded_aux` | SpectralGap.lean | Fiedler (1973); Mohar (1991) |

### Persistent Homology & Stability (2 axioms)

| Axiom | File | Citation |
|-------|------|----------|
| `stability_of_h1_trivial_aux` | Stability.lean | Cohen-Steiner et al., "Stability of Persistence Diagrams" (2007) |
| `measurement_robustness_aux` | Stability.lean | Lipschitz stability of topological invariants |

### Higher Cohomology H² (2 axioms)

| Axiom | File | Citation |
|-------|------|----------|
| `filled_tetrahedron_coboundary` | H2Characterization.lean | Tetrahedron is contractible ⟹ H² = 0 |
| `hollow_tetrahedron_h2_nontrivial_ax` | H2Characterization.lean | Hollow tetrahedron has H² ≠ 0 |

---

## KEEP: Structural Assumptions

### StrategicGame.actions_nonempty

**Why unprovable**: The `StrategicGame` type defines `actions : Agent → Finset ℕ` which allows empty sets. The type explicitly permits counterexamples.

**Elimination would require**: Refactoring to use dependent types or a `WellFormedGame` wrapper.

---

## KEEP: Mathematically False Statements

These axioms are false for complexes with multiple independent cycles. They hold for single-cycle complexes but are stated without this restriction.

### remove_edge_from_single_cycle_aux'

**What it claims**: Removing any maximal edge makes H¹ = 0.

**Counterexample**: A complex with two disjoint hollow triangles. Removing an edge from one leaves the other cycle intact.

### fill_triangle_h1_trivial_aux'

**What it claims**: Adding any triangle makes H¹ = 0.

**Counterexample**: Same - filling one triangle doesn't kill cycles in other triangles.

### resolution_edge_exists_maximal_aux

**What it claims**: If H¹ ≠ 0, there exists a maximal edge whose removal makes H¹ = 0.

**Counterexample**: Two disjoint hollow triangles have no edge appearing in both cycles.

---

## References

1. Chung, F. R. K. (1997). *Spectral Graph Theory*. CBMS Regional Conference Series in Mathematics, 92. American Mathematical Society.

2. Cohen-Steiner, D., Edelsbrunner, H., & Harer, J. (2007). Stability of persistence diagrams. *Discrete & Computational Geometry*, 37(1), 103-120.

3. Fiedler, M. (1973). Algebraic connectivity of graphs. *Czechoslovak Mathematical Journal*, 23(2), 298-305.

4. Godsil, C., & Royle, G. F. (2001). *Algebraic Graph Theory*. Graduate Texts in Mathematics, 207. Springer.

5. Mohar, B. (1991). The Laplacian spectrum of graphs. *Graph Theory, Combinatorics, and Applications*, 2, 871-898.

---

## Notes

- Spectral axioms require ~100+ theorems to eliminate (characteristic polynomial, algebraic closure, sorting)
- Stability axioms require persistent homology formalization not in Mathlib
- Multi-cycle false axioms could be fixed by adding `dim H¹(K) = 1` hypothesis, but this requires refactoring the entire conflict resolution pipeline
