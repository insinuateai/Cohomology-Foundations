# Cohomology Foundations

Lean4 formalization of cohomology theory with applications to multi-agent coordination and AI alignment.

## Quick Start (Choose One)

| Task Type | Load Only |
|-----------|-----------|
| **Axiom elimination** | `handoff.md` only |
| **Sorry fixing** | `handoff.md` → target file |
| **New feature** | `skill-document.md` (pitfalls section) |
| **Exploration** | Skip `.claude/` entirely |
| **Deep proof work** | Also load `.claude/memory/advanced-math.md` |

## Session Protocol

**START:**
1. Status auto-displays (sorries, axioms, doc size) via hook
2. Pick Quick Start path above (don't load everything)
3. For axiom work: check `axiom-registry.md` and `axiom-justifications.md`

**END:**
1. Update `.claude/skill-document.md` with learnings (if >100 lines, compress)
2. Write `.claude/handoff.md` with session summary (overwrites previous)
3. If axiom status changed, update `.claude/axiom-registry.md`
4. Run `make axiom-count` to verify progress

## iPad Session Patterns

**Short session (< 30 min)**:
- Pick ONE sorry or ONE axiom
- Focus on single file
- Write handoff before timeout

**Medium session (30-60 min)**:
- Fix sorry chain in one module
- OR eliminate 1-2 related axioms
- Update skill-document with new patterns

**Deep session (60+ min)**:
- New infrastructure file
- Multi-file refactor
- Full dependency chain analysis

## Checkpoint Protocol

**During multi-step proof:**
1. After each lemma: add `- [CHECKPOINT] lemma_name done, next: other_lemma` to handoff.md
2. If blocked: add `- [BLOCKED] reason` with what's been tried
3. Resume from checkpoint if session ends mid-proof

**In code (for complex proofs):**
```lean
-- CHECKPOINT: proved base case
-- TODO: inductive step needs walk decomposition
```

## Goals

- **0 sorries** - All proofs must be complete, no placeholders
- **0 axioms** - Prove everything from Mathlib foundations

## Proof Level Hierarchy

Changes must move **UP**, never **DOWN**:

| Level | Name | Description | Status |
|-------|------|-------------|--------|
| **6** | Full constructive | Pure tactic proof, no assumptions | THE GOAL |
| **5** | Proven chain | All dependencies also Level 5/6 | GOOD |
| **4** | Proven + minimal axioms | 1-2 documented standard axioms | ACCEPTABLE |
| **3** | Weak proxy | Proves partial/weaker statement | DO NOT CREATE |
| **2** | Honest axiom | Full statement, assumed true | ACCEPTABLE |
| **1** | Trivialized | Vacuous, circular, or too strong | NEVER DO THIS |
| **0** | sorry | No proof at all | STARTING POINT |

**THE RULE:** Level 2 (honest axiom) is BETTER than Level 1 or 3.

If you can't prove something fully → LEAVE IT AS AN AXIOM (Level 2).

### Invalid Changes (Level goes DOWN)

```lean
-- BAD: axiom foo : H1Trivial K  →  theorem foo : True := trivial
-- BAD: axiom foo : H1Trivial K  →  theorem foo : (0:ℚ) ≤ 0 := le_rfl
-- BAD: def isAligned := <meaningful>  →  def isAligned := True
```

## Mathematical Semantics

| Term | Meaning | NOT the same as |
|------|---------|-----------------|
| `H1Trivial K` | First cohomology trivial (forest) | `True` |
| `ValueAligned systems ε` | Pairwise bounded disagreement | `True` |
| `OneConnected K` | 1-skeleton is acyclic | `True` |
| `IsCocycle f` | δf = 0 | `True` |

## Core Types

| Type | Definition | Mathematical Meaning |
|------|------------|---------------------|
| `Coeff` | `ℚ` | Rational coefficients |
| `Vertex` | `ℕ` | Abstract vertex/agent index |
| `Simplex` | `Finset Vertex` | Set of vertices (dim = card - 1) |
| `SimplicialComplex` | `Set Simplex` + closure axioms | Down-closed simplex collection |
| `Cochain K k` | `ksimplices k → Coeff` | Function assigning rationals to k-simplices |
| `IsCocycle K k f` | `δ K k f = 0` | Kernel of coboundary (closed forms) |
| `IsCoboundary K k f` | `∃ g, δ g = f` | Image of coboundary (exact forms) |
| `H1Trivial K` | `∀ f, IsCocycle → IsCoboundary` | H¹(K) = 0 (every 1-cocycle is exact) |
| `OneConnected K` | `(oneSkeleton K).IsAcyclic` | 1-skeleton is a forest |
| `ValueSystem S` | `S → ℚ` | Agent preference function |
| `ValueAligned systems ε` | `∀ i j s, \|vᵢ(s) - vⱼ(s)\| ≤ 2ε` | Pairwise bounded disagreement |

## Mathlib Foundations

| Our Type | Mathlib Base | Key Lemmas |
|----------|--------------|------------|
| `Simplex` | `Finset` | `card_eq_two`, `card_eq_one`, `min'_mem` |
| `SimplicialComplex` | `Set` | membership predicates |
| `Cochain` algebra | `AddCommGroup` | pointwise ops |
| `δ` (coboundary) | alternating sum | `Finset.sum_involution` for δ²=0 |
| `OneConnected` | `SimpleGraph.IsAcyclic` | `path_unique`, `IsTree` |
| `ValueAligned` | `abs` on `ℚ` | `abs_sub_le` |

## Context Efficiency

- **Complex proofs:** Prioritize understanding over speed—load full dependency chains
- **Simple fixes:** Keep context minimal, use targeted file reads
- **Exploration:** Use focused searches (specific files/functions) before broad sweeps

## Quick Reference

- **Build:** `lake build`
- **Session status:** `.claude/hooks/session-status.sh` (sorries, axioms, doc size)
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
