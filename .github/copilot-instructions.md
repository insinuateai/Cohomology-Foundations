# Copilot Instructions for Cohomology-Foundations

> **CRITICAL**: Read this ENTIRE file before making any changes to this codebase.

## PROOF LEVEL HIERARCHY

This codebase follows a strict proof quality hierarchy. **Changes must move UP, never DOWN.**

```
LEVEL 6: Full constructive proof                    ← THE GOAL
         No assumptions. Pure tactic proof. Compiles.
         "We KNOW this is true because Lean checked every step."

LEVEL 5: Theorem proven from other proven theorems
         All dependencies are also Level 5 or 6.
         "True, and the entire chain is verified."

LEVEL 4: Theorem proven from proven lemmas + 1-2 minimal axioms
         The axioms are tight, documented, mathematically standard.
         "True, modulo Euler's formula for forests."

LEVEL 3: Weak constructive proof (proxy)           ← DO NOT CREATE THESE
         Proves something real but not the full statement.
         One direction, inequality, specific case.
         "We proved half of it from scratch."

LEVEL 2: Honest axiom                              ← ACCEPTABLE FOR UNPROVEN ITEMS
         States the full theorem as assumed-true.
         Documented, referenced, no proof.
         "We assert this is true. Diestel page 14."

LEVEL 1: Trivialized axiom / assumption baking     ← NEVER DO THIS
         Axiom that's too strong, circular, or vacuous.
         "We assumed what we wanted to prove."

LEVEL 0: sorry
         Literally nothing. A hole.
         "We haven't even tried."
```

### THE GOLDEN RULE

**Level 2 (honest axiom) is BETTER than Level 1 or 3.**

Never "upgrade" an honest axiom to a trivialized theorem. If you can't prove something fully (Level 5/6), LEAVE IT AS AN AXIOM (Level 2).

---

## CRITICAL CONSTRAINTS (MUST NOT VIOLATE)

### Build Verification
- `lake build` MUST pass before any commit
- No introducing import cycles
- No breaking existing compiling code

### Axiom Handling Rules
- NEVER replace `axiom X : P` with `theorem X : True`
- NEVER replace meaningful conclusions with tautologies like `(0:ℚ) ≤ 0`
- NEVER make definitions vacuously true (e.g., `isAligned := True`)
- If you can't prove an axiom properly, **LEAVE IT AS AN AXIOM**
- Axiom elimination must preserve semantic meaning

### Import Rules
- Check for import cycles before adding new imports
- Use existing transitive imports when possible

---

## VALID vs INVALID AXIOM ELIMINATION

### VALID (Level 2 → Level 5/6):
```lean
-- BEFORE: axiom foo : H1Trivial K
-- AFTER: theorem foo : H1Trivial K := by
--   exact someProvenLemma K h
-- RESULT: Same statement, now proven. Level went UP. ✓
```

### INVALID (Level 2 → Level 1 - DESTROYS MEANING):
```lean
-- BEFORE: axiom foo : H1Trivial K
-- AFTER: theorem foo : True := trivial
-- RESULT: Changed the statement! Now proves nothing. Level went DOWN. ✗
```

### INVALID (Level 2 → Level 3 - SEMANTIC WEAKENING):
```lean
-- BEFORE: axiom foo : H1Trivial K
-- AFTER: theorem foo : (0 : ℚ) ≤ 0 := le_rfl
-- RESULT: Proves something trivial, not the original claim. Level went DOWN. ✗
```

### INVALID (Level 2 → Level 1 - VACUOUS DEFINITION):
```lean
-- BEFORE: def isAligned (M : Module) : Prop := <meaningful definition>
-- AFTER: def isAligned (M : Module) : Prop := True
-- RESULT: Everything is now "aligned". Theorems become vacuous. Level went DOWN. ✗
```

---

## MATHEMATICAL SEMANTICS TO PRESERVE

These terms have SPECIFIC meanings. They are NOT interchangeable with `True`:

| Term | Meaning |
|------|---------|
| `H1Trivial K` | First cohomology group is trivial (forest property) |
| `ValueAligned systems ε` | Pairwise bounded disagreement between value systems |
| `OneConnected K` | 1-skeleton graph is acyclic |
| `IsCocycle f` | f satisfies the cocycle condition (δf = 0) |
| `IsCoboundary f` | f is in the image of the coboundary operator |

---

## PRE-COMMIT CHECKLIST

Before committing ANY changes:

1. **Run `lake build`** - must succeed with no errors
2. **Run `make axiom-count`** - document any changes in axiom count
3. **Check imports** - verify no import cycles introduced
4. **Verify semantics** - if changing axiom → theorem, verify the theorem proves the SAME statement

---

## EXISTING DOCUMENTATION

Consult these files for additional context:

| File | Purpose |
|------|---------|
| `CLAUDE.md` | Project structure, session protocols |
| `.claude/skill-document.md` | Lean 4 pitfalls and API quirks |
| `.claude/axiom-registry.md` | Full axiom inventory with status |
| `.claude/axiom-justifications.md` | Why certain axioms are marked KEEP |

---

## SUMMARY

1. **Move proofs UP the hierarchy** (toward Level 6), never DOWN
2. **Level 2 (honest axiom) > Level 1 or 3** (trivialized/weakened)
3. **If you can't prove it fully, leave it as an axiom**
4. **Always run `lake build` before committing**
5. **Never change the TYPE of a theorem** - only change the proof
