# Axiom Status (Quick Reference)

> For full details, see `axiom-registry.md`
> Last updated: 2026-02-06 (session 30)

| Status | Count | Description |
|--------|-------|-------------|
| **In Codebase** | **18** | Total axiom declarations |
| All in `Perspective/` | 18 | Auxiliary application modules only |
| **SORRIES** | 0 | All sorries eliminated |

## Location Summary

| File | Count |
|------|-------|
| `Perspective/CriticalPoints.lean` | 6 |
| `Perspective/Curvature.lean` | 3 |
| `Perspective/DimensionBound.lean` | 3 |
| `Perspective/AttractorBasins.lean` | 2 |
| `Perspective/AgentCoordination.lean` | 1 |
| `Perspective/Barrier.lean` | 1 |
| `Perspective/OptimalRepair.lean` | 1 |
| `Perspective/Persistence.lean` | 1 |
| **Total** | **18** |

## Core Theorem Status

All four core theorems are **axiom-free** (verified by import chain analysis):

| Theorem | File | Status |
|---------|------|--------|
| `delta_squared_zero` | `Foundations/DoubleSquaredZero.lean` | AXIOM-FREE |
| `h1_trivial_iff_oneConnected` | `H1Characterization/Characterization.lean` | AXIOM-FREE |
| `no_universal_reconciler_strong` | `Perspective/ImpossibilityStrong.lean` | AXIOM-FREE |
| `tree_authority_h1_trivial` | `MultiAgent/TreeAuthorityH1.lean` | AXIOM-FREE |

## Remaining Axiom Categories

| Category | Count | Why Not Proven |
|----------|-------|----------------|
| Morse / critical point theory | 6 | Requires discrete Morse theory |
| Riemannian geometry (curvature) | 3 | Requires continuous analysis |
| Graph component counting | 3 | Requires detailed component lemmas |
| Dynamical systems | 2 | Requires attractor/basin theory |
| Hub / coordination topology | 1 | Requires hub-leaf reduction |
| Structural resolution | 1 | Requires barrier theory |
| Repair convergence | 1 | Requires convergence analysis |
| Persistence diagrams | 1 | Requires persistence homology |

## Update Protocol

When eliminating an axiom:
1. Verify signature matches EXACTLY
2. Create `*_proven` theorem in `Infrastructure/`
3. Update `axiom-registry.md`
4. Run `make axiom-count`
