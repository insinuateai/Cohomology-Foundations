# Cohomology Foundations

Lean4 formalization of cohomology theory with applications to multi-agent coordination and AI alignment.

## Session Protocol

**START:** Read `.claude/skill-document.md` for patterns and pitfalls.

**END:** Update `.claude/skill-document.md` with learnings (pitfalls discovered, tactics that worked, anti-patterns to avoid). If >100 lines, compress: consolidate similar entries, remove stale info, prune verbose examples.

## Goals

- **0 sorries** - All proofs must be complete, no placeholders
- **0 axioms** - Prove everything from Mathlib foundations

## Quick Reference

- **Build:** `lake build`
- **Coefficients:** `Coeff := ℚ`
- **Key insight:** H¹ = 0 ⟺ forest ⟺ reconcilable

## Structure

| Directory | Purpose |
|-----------|---------|
| `Foundations/` | Simplices, cochains, coboundary (δ² = 0), cohomology |
| `Infrastructure/` | Axiom elimination, graph utilities |
| `H1Characterization/` | Forest ⟺ H¹=0 theorems |
| `MultiAgent/` | Game theory + cohomology |
| `Perspective/` | Barriers, repair, fairness |
