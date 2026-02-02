# Cohomology Foundations

Lean4 formalization of cohomology theory with applications to multi-agent coordination and AI alignment.

## Session Protocol

**START:**
1. Read `.claude/skill-document.md` for patterns and pitfalls
2. Read `.claude/handoff.md` for previous session state (if exists)
3. If working on axiom elimination, check `.claude/axiom-registry.md` and `.claude/axiom-justifications.md`

**END:**
1. Update `.claude/skill-document.md` with learnings (if >100 lines, compress)
2. Write `.claude/handoff.md` with session summary (overwrites previous)
3. If axiom status changed, update `.claude/axiom-registry.md`
4. Run `make axiom-count` to verify progress

## Goals

- **0 sorries** - All proofs must be complete, no placeholders
- **0 axioms** - Prove everything from Mathlib foundations

## Context Efficiency

- **Complex proofs:** Prioritize understanding over speed—load full dependency chains
- **Simple fixes:** Keep context minimal, use targeted file reads
- **Exploration:** Use focused searches (specific files/functions) before broad sweeps

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
