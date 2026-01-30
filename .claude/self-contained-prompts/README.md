# Self-Contained Prompts for Graph Theory Sorries

These prompts are designed to be used in a **fresh Claude session** without needing the full codebase.

## Target File
`Infrastructure/TreeGraphInfra.lean` - 3 sorries

## Prompts

| # | File | Theorem | Dependency |
|---|------|---------|------------|
| 1 | `prompt-1-edges-plus-components.md` | `edges_plus_components_ge_vertices` | None (base) |
| 2 | `prompt-2-acyclic-euler-eq.md` | `acyclic_euler_eq` (disconnected case) | Uses #1 |
| 3 | `prompt-3-euler-implies-acyclic.md` | `euler_eq_implies_acyclic'` | Uses #1 |

## Recommended Order
Complete them in order 1 → 2 → 3 since #2 and #3 can use #1.

## How to Use

1. **Copy the full prompt text** into a new Claude chat
2. **Ask Claude to generate** the complete Lean 4 proof
3. **Test locally** with `lake build` before committing
4. **If it fails**, paste the error back to Claude for debugging

## What's Included in Each Prompt

- Exact theorem statement
- Required Mathlib imports (v4.27.0)
- Mathematical background
- Suggested proof strategy
- Key Mathlib lemmas to use
- Known pitfalls from this codebase

## Success Probability

~70-80% for prompt 1 (pure graph theory, base case already done)
~60-70% for prompts 2-3 (depend on component counting infrastructure)

Main risk: Mathlib v4.27.0 API may differ from Claude's training data. If a suggested lemma doesn't exist, search Mathlib docs.

## After Completing These

The remaining sorries in the codebase involve project-specific types (`Cochain`, `SimplicialComplex`, etc.) and **cannot** be solved with self-contained prompts. Those will need:
- Minimal context documents (type definitions only)
- Or working in a session with codebase visibility
