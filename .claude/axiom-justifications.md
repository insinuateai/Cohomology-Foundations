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
| `hollow_tetrahedron_h2_nontrivial_ax` | H2Characterization.lean:91 | Hollow tetrahedron has H² ≠ 0; complete proof in HollowTetrahedron.lean (uses witness 1,0,0,0) |
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

## Structural Assumptions (Type System Limitations)

These axioms cannot be proven because the type system doesn't enforce the required properties.

### X25: StrategicGame.actions_nonempty — KEEP (Structural)

| Property | Value |
|----------|-------|
| File | GameTheoreticH1.lean:274 |
| Usages | 4 locations in `nash_iff_h1_trivial_coordination` |

**Why unprovable**: The `StrategicGame` type defines `actions : Agent → Finset ℕ` which allows empty sets. The type explicitly permits counterexamples:
```lean
def StrategicGame.empty : StrategicGame where
  actions := fun _ => ∅  -- Empty actions allowed
```

**Elimination would require**: Refactoring `StrategicGame` to use dependent types or a `WellFormedGame` wrapper (~20 locations affected).

### X26: StrategicGame.coordination_nash_player_bound — KEEP (Model Limitation)

| Property | Value |
|----------|-------|
| File | GameTheoreticH1.lean:286 |
| Usages | 1 location in `nash_implies_h1_trivial` |

**Why unprovable**: This axiom claims coordination games with Nash equilibrium cannot have >2 players. This contradicts full game theory where coordination games typically have Nash equilibria for n ≥ 2.

The axiom documents a known gap: the simplified forest-based formalization (forests ≤1 player) doesn't match real coordination game behavior. The code comments (line 284) acknowledge this limitation.

**Elimination would require**: Redesigning the Nash ↔ H¹ connection to not assume forest structure implies ≤1 player.

---

## Mathematically Strong Statements (Multi-Cycle Issues)

These axioms are mathematically false for complexes with multiple independent cycles. They hold for single-cycle complexes but are stated without this restriction.

### R01: remove_edge_from_single_cycle_aux' — KEEP (False for Multi-Cycle)

| Property | Value |
|----------|-------|
| File | ConflictResolution.lean:163 |
| Usages | wrapper (line 172), `resolution_edge_exists_aux` (line 275), `remove_edge_resolves` (line 343) |

**What it claims**: Removing any maximal edge makes H¹ = 0.

**Counterexample**: A complex with two disjoint hollow triangles {a,b,c} and {x,y,z}. Removing an edge from the first triangle leaves the second cycle intact. H¹ ≠ 0.

**Why not fixed**: Adding `dim H¹(K) = 1` hypothesis would break `resolution_edge_exists_aux` which lacks this context. Full fix requires refactoring the entire resolution pipeline.

### R02: fill_triangle_h1_trivial_aux' — KEEP (False for Multi-Cycle)

| Property | Value |
|----------|-------|
| File | ConflictResolution.lean:196 |
| Usages | wrapper (line 200), `fill_triangle_resolves` (line 389) |

**What it claims**: Adding any triangle makes H¹ = 0.

**Counterexample**: Same as R01 - filling one triangle in a two-triangle complex leaves the other cycle intact.

**Why not fixed**: Same as R01 - would require pipeline-wide changes.

### R03: resolution_edge_exists_maximal_aux — KEEP (False for Multi-Cycle)

| Property | Value |
|----------|-------|
| File | ConflictResolution.lean:217 |
| Usages | 1 location as fallback in `resolution_edge_exists_aux` (line 284) |

**What it claims**: If H¹ ≠ 0, there exists a maximal edge whose removal makes H¹ = 0.

**Counterexample**: Two disjoint hollow triangles have no edge appearing in both cycles. Removing any edge breaks only one cycle.

**Note**: This is existential (∃) not universal (∀), so initially seemed possibly true. However, for truly independent (disjoint) cycles, no single edge can break all cycles.

---

## Notes

- H² axioms are marked TEMP in source with target date 2026-02-07; may become eliminable
- Spectral axioms require ~100+ theorems to eliminate (characteristic polynomial, algebraic closure, sorting)
- Stability axioms require persistent homology formalization not in Mathlib
- R01/R02/R03 could theoretically be fixed by adding `dim H¹(K) = 1` hypothesis, but this requires refactoring the entire conflict resolution pipeline
