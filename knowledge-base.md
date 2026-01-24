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

---
Added: 2026-01-24
Source: oriented_edge_coboundary proof

### Pattern: Coboundary on 1-Simplex (Edge)

**Name:** Edge Coboundary via Face Decomposition
**Use when:** Computing (δg)(e) for a 0-cochain g on a 1-simplex e

**Mathematical Content:**
For edge {a, b} with a < b (sorted), coboundary sums over Fin 2:
- face 0 = erase element at position 0 = {b}
- face 1 = erase element at position 1 = {a}
- (δg)(e) = sign(0)*g({b}) + sign(1)*g({a}) = g({b}) - g({a})

**Code:**
```lean
-- Define Fin 2 indices
have h_idx0 : (0 : ℕ) < s.card := by rw [hcard]; omega
have h_idx1 : (1 : ℕ) < s.card := by rw [hcard]; omega
let i0 : Fin s.card := ⟨0, h_idx0⟩
let i1 : Fin s.card := ⟨1, h_idx1⟩

-- Expand sum to two terms
have h_univ : (Finset.univ : Finset (Fin s.card)) = {i0, i1} := by ...
rw [Finset.sum_pair h_ne_idx]
simp only [sign_zero, sign_one, one_mul, neg_one_mul]
```

**Key Lemmas:**
- `Finset.sort_insert` for computing sorted list of {a, b}
- `Simplex.face` removes i-th vertex in sorted order
- `Finset.sum_pair` to expand sum over Fin 2

---
### Pattern: Sorted List of Two-Element Finset

**Name:** Finset.sort_insert for Pairs
**Use when:** Computing sorted list of {a, b} with a < b

**Code:**
```lean
have h_sort : ({a, b} : Finset ℕ).sort (· ≤ ·) = [a, b] := by
  have h_ne : a ∉ ({b} : Finset ℕ) := by simp [ne_of_lt hab]
  have h_insert : ({a, b} : Finset ℕ) = insert a {b} := by
    ext x; simp [Finset.mem_insert, Finset.mem_singleton, or_comm]
  rw [h_insert, Finset.sort_insert (r := (· ≤ ·))]
  · simp only [Finset.sort_singleton]
  · intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]; exact le_of_lt hab
  · exact h_ne
```

---
Added: 2026-01-24
Source: cycleIndicator_not_coboundary proof

### Pattern: Non-Coboundary via Walk Sum Contradiction

**Name:** Cycle Indicator Not Coboundary
**Use when:** Proving a cochain on a cycle is not a coboundary

**Mathematical Content:**
If `f = δg` for some `g`, then the walk sum of `f` around any closed walk equals 0 (coboundaries telescope). But the cycle indicator on a cycle has walk sum = cycle length ≥ 3. Contradiction.

**Code:**
```lean
theorem not_coboundary ... : ¬IsCoboundary K 1 f := by
  intro ⟨g, hg⟩
  -- Compute walk sum two ways:
  have h1 : cochainWalkSum K f C = C.length := ...
  have h2 : cochainWalkSum K (δ K 0 g) C = 0 := coboundary_walk_sum_zero K g C
  -- hg : δ K 0 g = f, so substitute into h2
  rw [hg] at h2
  -- Derive length = 0
  have h_zero : (C.length : ℚ) = 0 := h1.symm.trans h2
  have h_len_zero : C.length = 0 := Nat.cast_injective h_zero
  -- But cycles have length ≥ 3
  have h_len : C.length ≥ 3 := hC.three_le_length
  omega
```

**Key Lemmas:**
- `coboundary_walk_sum_zero`: Walk sum of coboundary on closed walk = 0
- `IsCycle.three_le_length`: Cycles have at least 3 edges
- `Nat.cast_injective`: Convert `(n : ℚ) = 0` to `n = 0`

---
### Technique: Nat.cast_injective for omega

**Name:** Converting Rational Equality to Natural for omega
**Use when:** You have `(n : ℚ) = 0` but need `n = 0` for omega

**Code:**
```lean
have h_zero : (C.length : ℚ) = 0 := h1.symm.trans h2
have h_len_zero : C.length = 0 := Nat.cast_injective h_zero
omega  -- Now works with h_len_zero and h_len : C.length ≥ 3
```

**Note:** `omega` works with ℕ and ℤ but not ℚ. Use `Nat.cast_injective` to bridge.

---
Added: 2026-01-24
Source: cycleIndicator_self_contribution proof

### Pattern: Trail Edge Uniqueness

**Name:** Using countP = 1 for Uniqueness in Trails
**Use when:** Proving properties about unique edges in a trail/cycle

**Mathematical Content:**
In a trail (walk with no repeated edges), each undirected edge appears exactly once. This means `countP (fun d' => d'.edge = d.edge) = 1` for any dart `d` in the trail. This uniqueness can be used to prove that any dart with the same edge must be identical.

**Code:**
```lean
-- Get trail uniqueness
have hedge_unique : C.darts.countP (fun d' => d'.edge = d.edge) = 1 :=
  trail_dart_edge_unique' C htrail d hd

-- Any dart with same edge must equal d
have same_edge_implies_eq : ∀ d' ∈ C.darts, d'.edge = d.edge → d' = d := by
  intro d' hd' hedge
  exact countP_eq_one_unique hedge_unique d' d hd' hd
    (by simp only [decide_eq_true_eq]; exact hedge)
    (by simp only [decide_eq_true_eq])
```

**Key Lemma:**
```lean
private lemma countP_eq_one_unique {α : Type*} {l : List α} {p : α → Bool}
    (hcount : l.countP p = 1) (x y : α) (hx : x ∈ l) (hy : y ∈ l)
    (hpx : p x = true) (hpy : p y = true) : x = y
```

---
### Pattern: Refining countP Predicates

**Name:** countP = 1 for Refined Predicate
**Use when:** You know countP = 1 for a weaker predicate and need to prove it for a stronger one

**Mathematical Content:**
If `countP p = 1` and predicate `q` implies `p`, and you have an element satisfying `q`, then `countP q = 1` (since `countP q ≤ countP p = 1` and `countP q ≥ 1`).

**Code:**
```lean
private lemma countP_eq_one_of_refines {α : Type*} {l : List α} {p q : α → Bool}
    (hp_one : l.countP p = 1) (hqp : ∀ x, q x = true → p x = true)
    (x : α) (hx : x ∈ l) (hqx : q x = true) : l.countP q = 1 := by
  have hle : l.countP q ≤ l.countP p := countP_le_of_imp l hqp
  have hge : 1 ≤ l.countP q := countP_pos_of_mem x hx hqx
  omega
```

**Use Case:**
- Have: `countP (edge equality) = 1` from trail uniqueness
- Want: `countP (same simplex ∧ positive orientation) = 1`
- Strategy: Show same simplex implies edge equality, then apply refines lemma

---
### Pattern: Sym2 Edge Equality via Dart Fields

**Name:** dart_edge_eq_iff for Undirected Edge Matching
**Use when:** Converting between Sym2 edge equality and vertex field equality

**Code:**
```lean
private lemma dart_edge_eq_iff (d1 d2 : (oneSkeleton K).Dart) :
    d1.edge = d2.edge ↔
    (d1.fst = d2.fst ∧ d1.snd = d2.snd) ∨ (d1.fst = d2.snd ∧ d1.snd = d2.fst) := by
  rw [SimpleGraph.Dart.edge, SimpleGraph.Dart.edge, Sym2.mk_eq_mk_iff]
  -- Then handle Prod.ext_iff and Prod.fst_swap/snd_swap
```

**Note:** `Sym2.mk_eq_mk_iff` gives `Sym2.mk a b = Sym2.mk c d ↔ (a,b) = (c,d) ∨ (a,b) = (d,c)`

---
### Pattern: List Sum Equals Length When All Elements Are 1

**Name:** sum_eq_length_of_all_one
**Use when:** Proving sum of a list equals its length when all elements are 1

**Code:**
```lean
private lemma sum_eq_length_of_all_one {l : List ℚ} (h : ∀ x ∈ l, x = 1) : l.sum = l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have ha : a = 1 := h a (List.Mem.head as)
    have has : ∀ x ∈ as, x = 1 := fun x hx => h x (List.Mem.tail a hx)
    rw [ha, ih has]
    ring
```

**Note:** Use `List.Mem.head` and `List.Mem.tail` for membership in cons lists (Lean 4 style).

---
### Error: List.mem_cons_self Syntax in Lean 4

**Message:** `Function expected at List.mem_cons_self`
**Cause:** In Lean 4, `List.mem_cons_self a as` is a proof term, not a function

**Wrong:**
```lean
h a (List.mem_cons_self a as)  -- Treating as function
```

**Fix:**
```lean
h a (List.Mem.head as)  -- Use List.Mem.head
-- or
h a (by exact List.mem_cons_self a as)
```

---
### Error: List.length_eq_zero.mp Not Found

**Message:** `Unknown constant 'List.length_eq_zero.mp'`
**Fix:** Use `List.eq_nil_of_length_eq_zero` instead

**Wrong:**
```lean
have hzs : zs = [] := List.length_eq_zero.mp hcount
```

**Fix:**
```lean
have hzs : zs = [] := List.eq_nil_of_length_eq_zero hcount
```
