# Cohomology-Foundations Knowledge Base

This file documents error→fix pairs, tactic patterns, and proof strategies discovered while working on this codebase.

---
Added: 2026-01-24 12:00
Source: coboundary_edge_formula / ForestCoboundary.lean

### Error: Fin Type Mismatch in Sums

**Message:** `type mismatch: Fin e.val.card vs Fin 2`

**Context:** When the coboundary definition sums over `Fin s.val.card` but you need to use `Fin.sum_univ_two` which requires syntactic `Fin 2`.

**Fix:** Use `finCongr` to create a type equivalence, then `Finset.sum_equiv` to transport the sum.

**Code:**
```lean
-- Given: hcard : e.val.card = 2
-- Goal: rewrite sum over Fin e.val.card to sum over Fin 2

have h_sum_eq : ∑ i : Fin e.val.card, f i = ∑ j : Fin 2, f (finCongr hcard.symm j) := by
  refine (Finset.sum_equiv (finCongr hcard.symm) ?_ ?_).symm
  · intro j; simp only [Finset.mem_univ, implies_true]
  · intro j _; simp only [finCongr_apply, Fin.coe_cast]

rw [h_sum_eq, Fin.sum_univ_two]
```

---
Added: 2026-01-24 12:00
Source: coboundary_edge_formula / ForestCoboundary.lean

### Pattern: finCongr + sum_equiv

**Name:** Fin Type Transport for Sums
**Use when:** You have a sum over `Fin n` where `n` is computed (e.g., `e.val.card`) but need to apply lemmas that require a specific literal type like `Fin 2`.

**Key Lemmas:**
- `finCongr : (h : n = m) → Fin n ≃ Fin m` (from `Mathlib.Logic.Equiv.Fin`)
- `finCongr_apply : (finCongr h i).val = i.val`
- `finCongr_symm : (finCongr h).symm = finCongr h.symm`
- `Finset.sum_equiv` (from `Mathlib.Algebra.BigOperators.Group.Finset`)
- `Fin.sum_univ_two` (from `Mathlib.Algebra.BigOperators.Fin`)

**Code:**
```lean
-- Working pattern from Foundations/Coboundary.lean:584-587
refine Finset.sum_equiv (finCongr h_card) ?_ ?_
· intro j; simp only [Finset.mem_univ, implies_true]
· intro j _; simp only [termFn, finCongr_apply, Fin.coe_cast]
```

---
Added: 2026-01-24 12:00
Source: coboundary_edge_formula / ForestCoboundary.lean

### Pattern: Edge Decomposition for 1-Simplices

**Name:** Decompose 1-simplex into ordered pair
**Use when:** You need to work with a 1-simplex as `{a, b}` with `a < b`.

**Code:**
```lean
-- Given: e : { s : Simplex // s ∈ K.ksimplices 1 }
have hcard : e.val.card = 2 := e.property.2
rw [Finset.card_eq_two] at hcard
obtain ⟨a', b', hab_ne, hab_eq⟩ := hcard
-- hab_ne : a' ≠ b', hab_eq : e.val = {a', b'}

-- Establish ordering via trichotomy
rcases Nat.lt_trichotomy a' b' with hab' | hab' | hab'
· -- Case a' < b': use a = a', b = b'
  ...
· -- Case a' = b': contradicts hab_ne
  exact absurd hab' hab_ne
· -- Case a' > b': use a = b', b = a', swap with Finset.pair_comm
  ...
```

---
Added: 2026-01-24 12:00
Source: coboundary_edge_formula / ForestCoboundary.lean

### Pattern: Sort Computation for 2-element Finset

**Name:** Compute sort of {a, b} when a < b
**Use when:** You need to prove what `Finset.sort (· ≤ ·)` produces for a pair.

**Code:**
```lean
-- Given: a' < b', need to show (e.val).sort (· ≤ ·) = [a', b']
have h_sort : (e.val).sort (· ≤ ·) = [a', b'] := by
  rw [hab_eq]  -- e.val = {a', b'}
  have h_ne : a' ∉ ({b'} : Finset Vertex) := by simp [ne_of_lt hab']
  have h_insert : ({a', b'} : Finset Vertex) = insert a' {b'} := by
    ext x; simp [Finset.mem_insert, Finset.mem_singleton, or_comm]
  rw [h_insert, Finset.sort_insert (r := (· ≤ ·))]
  · simp only [Finset.sort_singleton]
  · intro x hx
    simp only [Finset.mem_singleton] at hx
    rw [hx]; exact le_of_lt hab'
  · exact h_ne
```

---
Added: 2026-01-24 12:00
Source: coboundary_edge_formula / ForestCoboundary.lean

### Pattern: Face Computation for Edges

**Name:** Compute face of 1-simplex
**Use when:** You need to show `e.val.face ⟨0, _⟩ = {larger}` and `e.val.face ⟨1, _⟩ = {smaller}`.

**Code:**
```lean
-- Given: h_sort : (e.val).sort (· ≤ ·) = [a', b'] (where a' < b')
-- Face 0 removes first element of sorted list (a'), leaving {b'}
have h_face0 : e.val.face ⟨0, by rw [hcard2]; omega⟩ = {b'} := by
  simp only [Simplex.face, h_sort, List.get_eq_getElem, List.getElem_cons_zero]
  ext x
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro ⟨hne, hx⟩
    rw [hab_eq] at hx; simp at hx
    rcases hx with rfl | rfl
    · exact absurd rfl hne
    · rfl
  · intro rfl
    rw [hab_eq]
    exact ⟨ne_of_gt hab', by simp⟩

-- Face 1 removes second element of sorted list (b'), leaving {a'}
have h_face1 : e.val.face ⟨1, by rw [hcard2]; omega⟩ = {a'} := by
  simp only [Simplex.face, h_sort, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
  ext x
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro ⟨hne, hx⟩
    rw [hab_eq] at hx; simp at hx
    rcases hx with rfl | rfl
    · rfl
    · exact absurd rfl hne
  · intro rfl
    rw [hab_eq]
    exact ⟨ne_of_lt hab', by simp⟩
```

---
Added: 2026-01-24 12:00
Source: coboundary_edge_formula / ForestCoboundary.lean

### Error: subst fails on computed expressions

**Message:** `subst tactic failed, hypothesis 'h' is not a variable`

**Context:** Attempting `subst hab_eq` where `hab_eq : e.val = {a', b'}` - the LHS is a computed expression, not a simple variable.

**Fix:** Don't use `subst` for computed expressions. Instead:
1. Use `rw [hab_eq]` to substitute directly
2. Or restructure the proof to avoid needing substitution

---
Added: 2026-01-24 12:00
Source: General Mathlib 4.16+

### Strategy: Dependent Type Handling in Fin Sums

**For:** Proofs involving sums over `Fin n` where `n` is not a literal

**Approach:**
1. **Never assume `Fin n` equals `Fin m`** even when `n = m` is provable - they are distinct types
2. **Use `finCongr`** to create an explicit equivalence from the equality proof
3. **Use `Finset.sum_equiv`** to transport sums across the equivalence
4. **Use `finCongr_apply` and `Fin.coe_cast`** to simplify terms after transport
5. **Only then** apply lemmas like `Fin.sum_univ_two` that require specific literal types

**Why standard approaches fail:**
- `subst` only works on variable equalities, not computed expressions
- `conv => rw [...]` can't rewrite inside type-dependent sums
- Direct `Fintype.sum_equiv` often has inference issues with dependent proofs
