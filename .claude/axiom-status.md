# Axiom Status (Quick Reference)

> For full signatures, see `axiom-signatures.md`

| Status | Count | Description |
|--------|-------|-------------|
| ELIMINATED | 13 | G01-G06, C03, C04, X03, X04, X28, X29, F07 |
| KEEP | ~25 | Structural assumptions, external math, multi-cycle issues |
| ELIMINATE | ~34 | Provable from current Mathlib |

## Priority Targets

### Tree Authority (Sorries block these)
| ID | Axiom | Blocker |
|----|-------|---------|
| T01-T05 | Depth/acyclicity proofs | TreeAuthCoreProofs sorries |
| T06-T07 | Path compatibility | TreeAuthority build errors |

### Fairness (Blocked by CompleteComplexH1)
| ID | Axiom | Status |
|----|-------|--------|
| F01 | h1_trivial_implies_fair_allocation | Blocked |
| F02 | fair_allocation_implies_h1_trivial | Blocked |

### KEEP (Don't Attempt)
| ID | Why |
|----|-----|
| R01-R03 | Mathematically false for multi-cycle |
| X25-X26 | Structural (type allows violations) |
| K01-K15 | External math (spectral, H2, dynamics) |

## Recently Eliminated

| Date | IDs | Method |
|------|-----|--------|
| 2026-02-02 | G01-G06 | WalkDecomposition, PathDecomposition, ExtendedGraphInfra |
| 2026-02-02 | C03, C04, X03, X04 | CriticalPointsCore, CompleteComplexH1 |
| 2026-02-02 | X28, X29, F07 | TreeAuthCoreProofs, FairnessH1Proofs |

## Update Protocol

When eliminating an axiom:
1. Verify signature matches EXACTLY
2. Update this file
3. Update `axiom-signatures.md` if signature documented
4. Run `make axiom-count`
