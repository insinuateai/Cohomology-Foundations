# Active Axiom Targets

> For completed/blocked details, see `next-5-targets-archive.md`.

## Current Blockers (Fix First)

| Blocker | Location | Sorries | Unlocks |
|---------|----------|---------|---------|
| TreeAuthCoreProofs | :582, :486 | 2 | T01-T05 |
| CompleteComplexH1 | :coboundary_edge | 2 | F01, F02 |
| TreeAuthorityAcyclicity | multiple | 3 | T04, T05 |
| TreeAuthDepthTheory | :127, :408 | 2 | depth proofs |
| TreeAuthority.lean | build errors | 0 | T06, T07, X27 |

## Priority Order

1. **Fix sorries** (12 total) - These block more axiom eliminations than new files can provide
2. **Fix TreeAuthority.lean** build errors - Unlocks path compatibility axioms
3. **ComponentCountingComplete.lean** - C05, X22, X23 (can proceed independently)

## Quick Reference

| Status | Axioms |
|--------|--------|
| **ELIMINATED** | G01-G06, C03, C04, X03, X04, X28, X29, F07 (13 total) |
| **BLOCKED** | T01-T07, F01, F02, X27 |
| **KEEP** | R01-R03 (math false), X25-X26 (structural), K01-K15 (external) |
| **PENDING** | C01, C02, C05, C06, X01-X24 (various) |

## Verification

After any elimination:
```bash
lake build
make axiom-count
grep -r "sorry" --include="*.lean" | wc -l
```
