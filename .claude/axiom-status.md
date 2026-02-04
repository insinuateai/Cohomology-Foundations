# Axiom Status (Quick Reference)

> For full details, see `axiom-registry.md`
> Last updated: 2026-02-04 (session 2)

| Status | Count | Description |
|--------|-------|-------------|
| **In Codebase** | **41** | Total axiom declarations |
| KEEP | 19 | External math, structural, mathematically false |
| TAUTOLOGICAL | ~18 | Infrastructure proofs with wrong H1Trivial |
| PENDING | 0 | All analyzed - moved to KEEP or TAUTOLOGICAL |
| **ELIMINATED** | 2 | See RECENTLY ELIMINATED below |

## KEEP (Don't Attempt - 19 total)

| Category | Axioms |
|----------|--------|
| Structural (1) | `StrategicGame.actions_nonempty` |
| Math False (7) | `remove_edge_*`, `fill_triangle_*`, `resolution_edge_*`, `large_disagreement_breaks_alignment_aux`, `general_acyclic_composition_axiom_aux`, `escape_time_finite_ax`, `forest_single_edge_composition_axiom_aux` |
| Spectral (5) | `vertexDegreeAx`, `laplacianExists`, `laplacianEigenvalues`, `eigenvalues_nonneg`, `spectral_gap_bounded_aux` |
| Persistent Homology (4) | `stability_of_h1_trivial_aux` (×2 duplicates), `measurement_robustness_aux` (×2 duplicates) |
| H² Theory (2) | `filled_tetrahedron_coboundary`, `hollow_tetrahedron_h2_nontrivial_ax` |

## PENDING (0 Elimination Targets)

All PENDING axioms have been analyzed. Remaining axioms are either:
- **KEEP**: Mathematically false, external dependencies, or structural
- **TAUTOLOGICAL**: Need full infrastructure rewrite (beyond scope)

## RECENTLY ELIMINATED

| Axiom | Replacement | Method |
|-------|-------------|--------|
| `escape_time_monotone_ax` | `escape_time_monotone_proven` | Proved using `Int.floor_le_floor` + `Int.toNat_le` |
| `escape_time_bounded_ax` | `escape_time_bounded_proven` | Proved using `div_le_div_of_nonneg_right` + floor monotonicity |

## Recently Moved to KEEP

- `large_disagreement_breaks_alignment_aux` - Counterexample: 2 disagreeing agents = forest (H¹=0)
- `general_acyclic_composition_axiom_aux` - `interfaceIsAcyclic=True` makes it false
- `escape_time_finite_ax` - Counterexample: misalignment=1000, tolerance=1 gives escapeTime=1001 > 1000
- `forest_single_edge_composition_axiom_aux` - Interface connections ≠ valueComplex edges; K₂,₂ counterexample possible

## HAS REPLACEMENT (Axiom exists, proof available)

Most axioms in Perspective/ and MultiAgent/ have proven replacements in Infrastructure/*Proofs.lean files. See `axiom-registry.md` for the full mapping.

Key examples:
- `saddle_has_escape_ax` → CriticalPointsProofs.lean
- `negative_lyapunov_stable_ax` → LyapunovProofs.lean
- `h1_trivial_implies_fair_allocation` → FairnessAllocationProofs.lean

## Update Protocol

When eliminating an axiom:
1. Verify signature matches EXACTLY
2. Create `*_proven` theorem in Infrastructure/
3. Update `axiom-registry.md`
4. Run `make axiom-count`
