# Lean 4 H1 Characterization Knowledge Base

## Overview
Documents patterns, errors, and strategies for proving H1 = 0 iff OneConnected.

---
Added: 2026-01-24
Source: singleEdge_oneConnected_axiom, hollowTriangle_not_oneConnected_axiom

### Pattern: Cycle Contradiction in Finite Graphs

**Name:** Finite Graph Acyclicity via Edge Counting
**Use when:** Proving a graph with few edges has no cycles

**Code:**
```lean
cases p with
| nil => exact hne_nil rfl
| cons h p' =>
  cases p' with
  | nil => exact hne_vw (congrArg Subtype.val heq)
  | cons h' p'' =>
    -- Both edges must be same (only one edge exists), violates IsTrail
    have h_same_edge : Sym2.mk v w = Sym2.mk w _ := by ...
    rw [SimpleGraph.Walk.isTrail_def, List.nodup_cons] at htrail
    exact htrail.1 (by rw [<- h_same_edge]; exact List.mem_cons_self _ _)
```

---
### Pattern: IsCycle Construction

**Name:** Explicit Cycle Construction for SimpleGraph
**Use when:** Proving a graph has a cycle

**Code:**
```lean
have h01 : (oneSkeleton K).Adj v0 v1 := ⟨hne01, hedge01⟩
let w := Walk.cons h01 (Walk.cons h12 (Walk.cons h20 Walk.nil))
constructor
· constructor  -- IsCircuit = IsTrail + ne_nil
  · constructor  -- IsTrail: edges.Nodup
  · exact fun h => Walk.noConfusion h
· -- support_nodup
```

---
### Pattern: Vertex Extraction from Edge Equality

**Name:** Finset Pair Membership Transport
**Use when:** Extracting vertices from {a, b} = {v, w}

**Code:**
```lean
have hv_mem : v ∈ ({a, b} : Finset N) := by
  have : v ∈ ({v, w} : Finset N) := Finset.mem_insert_self _ _
  rw [heq] at this; exact this
simp only [Finset.mem_insert, Finset.mem_singleton] at hv_mem hw_mem
rcases hv_mem with rfl | rfl <;> rcases hw_mem with rfl | rfl
```

---
### Error: native_decide for Concrete Inequalities

**Message:** `decide` fails on `(0 : N) ≠ 1`
**Fix:** Use `native_decide`

```lean
have hne01 : (0 : Vertex) ≠ 1 := by native_decide
```

---
### Error: Walk.noConfusion for ne_nil

**Message:** Type mismatch proving `¬p.Nil`
**Fix:** Use `Walk.noConfusion`

```lean
exact fun h => SimpleGraph.Walk.noConfusion h
```

---
### Strategy: Oriented Edge Sign Cases

**For:** Properties about oriented edges with sign adjustments
**Approach:** Case split on `src < tgt`

```lean
by_cases hslt : oe.src.val < oe.tgt.val
· -- sign = 1: src = a, tgt = b
· -- sign = -1: tgt = a, src = b, use ring for cancellation
```
