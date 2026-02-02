# Axiom Justification Appendix

> Publication-ready citations for external mathematical results.
> 15 axioms require external theory not yet in Mathlib.

## Summary

| Category | Count | Status |
|----------|-------|--------|
| External Math (cited) | 15 | KEEP - requires Mathlib extensions |
| Elimination Targets | 59 | Provable from current Mathlib |
| **Total** | **74** | |

## Cited External Results

### Spectral Graph Theory (5 axioms)

| Axiom | File | Citation |
|-------|------|----------|
| `vertexDegreeAx` | SpectralGap.lean:84 | Standard graph theory (axiomatized to avoid decidability overhead) |
| `laplacianExists` | SpectralGap.lean:135 | Chung, *Spectral Graph Theory* (1997), Ch. 1; L = D - A construction |
| `laplacianEigenvalues` | SpectralGap.lean:181 | Spectral theorem for symmetric matrices; requires algebraic closure |
| `eigenvalues_nonneg` | SpectralGap.lean:215 | Chung (1997), Lemma 1.7; vᵀLv = Σ(vᵢ-vⱼ)² ≥ 0 implies λᵢ ≥ 0 |
| `spectral_gap_bounded_aux` | SpectralGap.lean:551 | Fiedler (1973); Mohar (1991); bounds via path/complete graphs |

### Persistent Homology & Stability (2 axioms)

| Axiom | File | Citation |
|-------|------|----------|
| `stability_of_h1_trivial_aux` | Stability.lean:104 | Cohen-Steiner et al., "Stability of Persistence Diagrams" (2007) |
| `measurement_robustness_aux` | Stability.lean:113 | Lipschitz stability of topological invariants under perturbation |

### Bifurcation Theory (2 axioms)

| Axiom | File | Citation |
|-------|------|----------|
| `safety_margin_aux` | Bifurcation.lean:170 | Standard bifurcation theory; continuity near regular values |
| `bifurcation_catastrophic_aux` | Bifurcation.lean:240 | Thom, *Structural Stability and Morphogenesis* (1972) |

### Dynamical Systems (1 axiom)

| Axiom | File | Citation |
|-------|------|----------|
| `negative_lyapunov_stable_ax` | FairnessDynamics.lean:273 | Lyapunov stability theorem; Khalil, *Nonlinear Systems* (2002) |

### Higher Cohomology H² (5 axioms)

| Axiom | File | Citation |
|-------|------|----------|
| `h2_small_complex_aux` | H2Characterization.lean:74 | Simplicial cohomology; H²=0 for ≤3 vertices by dimension |
| `filled_tetrahedron_coboundary` | H2Characterization.lean:81 | Tetrahedron is contractible ⟹ H² = 0 |
| `hollow_tetrahedron_no_primitive` | H2Characterization.lean:87 | Hollow tetrahedron has H² ≅ ℚ; standard counterexample |
| `h1_h2_trivial_grand_coalition_aux` | CoalitionH2.lean:84 | Coalition obstruction theory via H² |
| `h1_trivial_h2_nontrivial_obstruction_aux` | CoalitionH2.lean:107 | H² creates scaling obstruction from triples to grand coalition |

## References

1. Chung, F. R. K. (1997). *Spectral Graph Theory*. CBMS Regional Conference Series in Mathematics, 92. American Mathematical Society.

2. Cohen-Steiner, D., Edelsbrunner, H., & Harer, J. (2007). Stability of persistence diagrams. *Discrete & Computational Geometry*, 37(1), 103-120.

3. Fiedler, M. (1973). Algebraic connectivity of graphs. *Czechoslovak Mathematical Journal*, 23(2), 298-305.

4. Godsil, C., & Royle, G. F. (2001). *Algebraic Graph Theory*. Graduate Texts in Mathematics, 207. Springer.

5. Khalil, H. K. (2002). *Nonlinear Systems* (3rd ed.). Prentice Hall.

6. Mohar, B. (1991). The Laplacian spectrum of graphs. *Graph Theory, Combinatorics, and Applications*, 2, 871-898.

7. Thom, R. (1972). *Structural Stability and Morphogenesis*. W.A. Benjamin.

## Notes

- H² axioms are marked TEMP in source with target date 2026-02-07; may become eliminable
- Spectral axioms require ~100+ theorems to eliminate (characteristic polynomial, algebraic closure, sorting)
- Stability axioms require persistent homology formalization not in Mathlib
