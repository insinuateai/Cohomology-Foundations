# Lean 4 Patterns & Fixes

## Quick Reference

### Decidability
```lean
have hne : (0 : N) ≠ 1 := by native_decide  -- not `decide` for concrete types
```

### Walk/Cycle Proofs
```lean
-- ne_nil for walks
exact fun h => SimpleGraph.Walk.noConfusion h

-- IsCycle construction
let w := Walk.cons h01 (Walk.cons h12 (Walk.cons h20 Walk.nil))
constructor
· constructor; · constructor; · exact fun h => Walk.noConfusion h  -- IsCircuit
· -- support_nodup
```

### Finset Operations
```lean
-- Extract from {a,b} = {v,w}
have hv_mem : v ∈ ({a, b} : Finset N) := by
  have : v ∈ ({v, w} : Finset N) := Finset.mem_insert_self _ _
  rw [heq] at this; exact this
simp only [Finset.mem_insert, Finset.mem_singleton] at hv_mem
rcases hv_mem with rfl | rfl <;> rcases hw_mem with rfl | rfl

-- Sum over Fin 2
have h_univ : (Finset.univ : Finset (Fin s.card)) = {i0, i1} := by ...
rw [Finset.sum_pair h_ne_idx]

-- Sum non-negativity
apply Finset.sum_nonneg; intro i _; exact abs_nonneg _
```

### Sorted Finset Pairs
```lean
have h_sort : ({a, b} : Finset ℕ).sort (· ≤ ·) = [a, b] := by
  have h_ne : a ∉ ({b} : Finset ℕ) := by simp [ne_of_lt hab]
  have h_insert : ({a, b} : Finset ℕ) = insert a {b} := by ext x; simp [or_comm]
  rw [h_insert, Finset.sort_insert (r := (· ≤ ·))]
  · simp only [Finset.sort_singleton]
  · intro x hx; simp at hx; rw [hx]; exact le_of_lt hab
  · exact h_ne
```

### Oriented Edge Signs
```lean
by_cases hslt : oe.src.val < oe.tgt.val
· -- sign = 1
· -- sign = -1, use ring for cancellation
```

### Type Conversions
```lean
-- ℚ = 0 → ℕ = 0 for omega
have h_zero : (n : ℚ) = 0 := ...
have h_nat : n = 0 := Nat.cast_injective h_zero
omega
```

### countP Patterns
```lean
-- Uniqueness from countP = 1
lemma countP_eq_one_unique (hcount : l.countP p = 1) (x y : α) 
    (hx : x ∈ l) (hy : y ∈ l) (hpx : p x) (hpy : p y) : x = y

-- Refined predicate
lemma countP_eq_one_of_refines (hp_one : l.countP p = 1) 
    (hqp : ∀ x, q x → p x) (x : α) (hx : x ∈ l) (hqx : q x) : l.countP q = 1
```

### Structure Definitions
```lean
-- Explicit type params for methods
def ModuleInterface.isCompatible {M₁ M₂ : AlignmentModule S} (I : ModuleInterface M₁ M₂) : Prop := ...

-- Pair iteration (no destructuring)
∀ p ∈ I.connections, |(M₁.systems p.1).values s - (M₂.systems p.2).values s| ≤ ...

-- Use function application, not dot notation for defs
h_compat : ModuleInterface.isCompatible I  -- NOT I.isCompatible
```

### Triangle Inequality (L1)
```lean
calc (Finset.univ.sum fun i => |p i - r i|)
    = ... |p i - q i + (q i - r i)| := by ring_nf
  _ ≤ ... (|p i - q i| + |q i - r i|) := by apply Finset.sum_le_sum; exact abs_add_le _ _
  _ = ... + ... := by rw [← Finset.sum_add_distrib]
```

### Graph Connectivity
```lean
-- Acyclicity: single edge graph has no cycles (any closed walk repeats edges)
cases p with
| nil => exact hne_nil rfl
| cons h p' => cases p' with
  | nil => exact hne_vw (congrArg Subtype.val heq)
  | cons h' p'' => -- both edges same, violates IsTrail
```

### Simplex Face Operations
```lean
-- Coboundary on edge {a,b}: (δg)(e) = g({b}) - g({a})
-- face 0 = {b}, face 1 = {a} when sorted
```

### Common Imports
```lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Topology.SimplicialComplex
```

## Error Quick Fixes

| Error | Fix |
|-------|-----|
| `decide` fails on concrete ≠ | Use `native_decide` |
| `Walk.noConfusion` type mismatch | Pattern: `fun h => Walk.noConfusion h` |
| Sym2 edge equality | Case split on both orderings |
| `Invalid field 'foo'` on def | Use `Namespace.foo x` not `x.foo` |
| `toList` noncomputable | Use `Finset.sum` directly |
| omega fails on ℚ | Convert via `Nat.cast_injective` |
