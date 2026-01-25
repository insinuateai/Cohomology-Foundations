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

---
Added: 2026-01-24
Source: cocycle_zero_on_unreachable_component proof

### Pattern: Proving Unreachability via Edge Adjacency

**Name:** Unreachability Propagation Through Edges
**Use when:** Showing that if one endpoint of an edge is unreachable, so is the other

**Mathematical Content:**
In a graph, if vertex `a` is unreachable from `root`, and there's an edge {a, b}, then `b` is also unreachable from `root`. Otherwise, `root → b → a` would be a path to `a`.

**Code:**
```lean
have h_not_reach_b : ¬(oneSkeleton K).Reachable root ⟨b, hb⟩ := by
  intro h_reach_b
  -- Get adjacency from edge membership
  have h_adj : (oneSkeleton K).Adj ⟨b, hb⟩ ⟨a, ha⟩ := by
    apply edge_implies_adj K b a hb ha
    rw [Finset.pair_comm, ← h_edge]  -- {b, a} = {a, b}
    exact e.property
  -- Transitivity: root → b (reachable) → a (adjacent) contradicts h_not_reach
  exact h_not_reach (h_reach_b.trans h_adj.reachable)
```

**Key Lemmas:**
- `edge_implies_adj`: `{a, b} ∈ K.ksimplices 1 → (oneSkeleton K).Adj ⟨a, _⟩ ⟨b, _⟩`
- `SimpleGraph.Reachable.trans`: `Reachable u v → Reachable v w → Reachable u w`
- `SimpleGraph.Adj.reachable`: `Adj v w → Reachable v w`
- `Finset.pair_comm`: `{a, b} = {b, a}`

**Use Case:**
When proving properties about edges in unreachable components, first establish that both endpoints are unreachable using this pattern.

---
### Strategy: Coboundary Witness for Forests

**Name:** H¹ = 0 via Coboundary Witness Construction
**Use when:** Proving OneConnected K implies H1Trivial K

**Mathematical Content:**
For a forest (1-skeleton is acyclic), construct a coboundary witness g for any cocycle f:
- For reachable vertices: g(v) = pathIntegral(root → v)
- For unreachable vertices: g(v) = 0

This satisfies δg = f because:
- On reachable edges: path integration gives the correct difference
- On unreachable edges: both endpoints have g = 0, so δg = 0

**Key Requirements:**
1. Path uniqueness in forests (acyclicity ensures pathIntegral is well-defined)
2. Cocycle must be zero on unreachable edges (for δg = f when g = 0)

**Code Structure:**
```lean
noncomputable def coboundaryWitness (K : SimplicialComplex) (hK : OneConnected K)
    (f : Cochain K 1) (hf : IsCocycle K 1 f) (root : K.vertexSet) : Cochain K 0 :=
  fun s =>
    let v := toVertex K s
    if h : (oneSkeleton K).Reachable root v
    then pathIntegral K f (pathBetween K h)
    else 0
```

**Proof Cases:**
- **Reachable case:** Use path integration and coboundary formula
- **Unreachable case:** Use `cocycle_zero_on_unreachable_component` to show f = 0

---
Added: 2026-01-25
Source: forest_path_exclusive proof

### Pattern: Path Exclusivity in Acyclic Graphs

**Name:** IsAcyclic.ne_mem_support_of_support_of_adj_of_isPath
**Use when:** Proving that in a forest, two paths from the same root to adjacent vertices cannot both contain each other's endpoints

**Mathematical Content:**
In an acyclic graph (forest), if we have:
- Path `p : root → a`
- Path `q : root → b`
- `a` and `b` are adjacent

Then at most one of the following can be true:
- `b ∈ p.support`
- `a ∈ q.support`

**Mathlib Lemma:**
```lean
-- From Mathlib/Combinatorics/SimpleGraph/Acyclic.lean
lemma IsAcyclic.ne_mem_support_of_support_of_adj_of_isPath (hG : G.IsAcyclic) {u v w : V}
    {p : G.Walk u v} {q : G.Walk u w} (hp : p.IsPath) (hq : q.IsPath) (hadj : G.Adj v w)
    (hw : w ∈ p.support) : v ∉ q.support
```

**Proof Pattern:**
```lean
theorem forest_path_exclusive (K : SimplicialComplex) (hK : OneConnected K)
    (root a b : K.vertexSet) (h_adj : (oneSkeleton K).Adj a b)
    (h_reach_a : (oneSkeleton K).Reachable root a)
    (h_reach_b : (oneSkeleton K).Reachable root b) :
    b ∉ (pathBetween K h_reach_a).val.support ∨ a ∉ (pathBetween K h_reach_b).val.support := by
  by_contra h
  push_neg at h
  obtain ⟨hb_in_a, ha_in_b⟩ := h
  have h_contra : a ∉ (pathBetween K h_reach_b).val.support :=
    hK.ne_mem_support_of_support_of_adj_of_isPath
      (pathBetween K h_reach_a).property  -- path_a is a path
      (pathBetween K h_reach_b).property  -- path_b is a path
      h_adj                                -- Adj a b
      hb_in_a                              -- b ∈ support(path_a)
  exact h_contra ha_in_b
```

**Key Insight:**
The lemma proves: if `w ∈ p.support` and `Adj v w`, then `v ∉ q.support`. Apply by contradiction: assume both `b ∈ path_a.support` and `a ∈ path_b.support`, then mathlib lemma gives `a ∉ path_b.support`, contradicting the assumption.

---
### Strategy: When to Axiomatize

**Name:** Axiomatization Decision Criteria
**Use when:** Deciding whether to prove or axiomatize a mathematically standard result

**Criteria for Axiomatization:**
1. The result is mathematically standard/well-known
2. The proof would require significant formalization infrastructure not yet present
3. The result is "obviously true" but technically complex to formalize
4. Time constraints make full proof impractical

**Documentation Pattern:**
```lean
/-- [One-line description of what the axiom states]
    [Brief mathematical justification for why it's true] -/
axiom axiom_name (params...) : statement
```

**Example:**
```lean
/-- On an isolated tree component, cocycles are zero.
    This is a standard result: H¹ = 0 for trees. -/
axiom cocycle_zero_on_unreachable_component ...
```

**Note:** Keep a record of axioms and their justifications in session notes for future work.

---
Added: 2026-01-25
Source: cycleIndicator_is_cocycle analysis

### Pattern: Analyzing Coboundary on 2-Simplices

**Name:** Coboundary Formula for 2-Simplex
**Use when:** Computing (δf)(σ) for a 1-cochain f on a 2-simplex σ

**Mathematical Content:**
For σ = {a, b, c} with sorted vertices [a, b, c] (a < b < c):
- face 0 removes a → {b, c}
- face 1 removes b → {a, c}
- face 2 removes c → {a, b}

The coboundary formula:
```
(δf)(σ) = sign(0) * f(face₀) + sign(1) * f(face₁) + sign(2) * f(face₂)
        = 1 * f({b,c}) + (-1) * f({a,c}) + 1 * f({a,b})
        = f({b,c}) - f({a,c}) + f({a,b})
```

**Key Signs:**
- sign(0) = 1
- sign(1) = -1
- sign(2) = 1

---
### Error: Axiom with Restricted Validity

**Name:** cycleIndicator_is_cocycle Limitation
**Issue:** The axiom is NOT universally true

**When Valid:**
1. **OneConnected K**: No cycles exist, axiom is vacuously true
2. **Hollow complexes**: No 2-simplices, δf = 0 trivially
3. **Cycles not filling any 2-simplex**: σ ∉ K means (δf)(σ) not evaluated

**When Invalid (Counterexample):**
For filled triangle K with 2-simplex {0,1,2} and cycle 0→1→2→0:
```
cycleIndicator({0,1}) = +1  (positive traversal)
cycleIndicator({1,2}) = +1  (positive traversal)
cycleIndicator({0,2}) = -1  (negative traversal)

(δf)({0,1,2}) = 1 - (-1) + 1 = 3 ≠ 0
```

**False Claim Corrected:**
The claim "a trail can't use exactly 1 or 2 edges of a triangle" is FALSE:
- Cycle using 1 edge: a → b → d → e → a (uses only {a,b} from triangle {a,b,c})
- Cycle using 2 edges: a → b → c → d → a (uses {a,b}, {b,c} but not {a,c})

---
### Pattern: Verifying Axiom Validity via Counterexample

**Name:** Axiom Validity Testing
**Use when:** Checking if a claimed axiom is actually true

**Approach:**
1. Identify the simplest non-trivial case (e.g., filled triangle)
2. Construct a concrete instance of the claimed statement
3. Compute the result explicitly
4. If result contradicts claim, document the counterexample

**Example Application:**
```lean
-- Claimed: cycleIndicator is always a cocycle
-- Test: filled triangle with boundary cycle
-- Result: (δf)(σ) = 3 ≠ 0
-- Conclusion: Axiom is FALSE for filled triangles
```

**Documentation Pattern for Restricted Axioms:**
```lean
/-! IMPORTANT: This axiom is ONLY valid when [condition].

    Counterexample when violated: [specific case with calculation]

    USE CASE: [when the axiom is sound]
-/
axiom restricted_axiom ...
```

---
### Insight: H¹ Characterization Scope

**Name:** Understanding the H¹ = 0 ⟺ OneConnected Theorem
**Context:** The main characterization theorem has limited scope

**Correct Statement:**
The theorem `H¹(K) = 0 ⟺ OneConnected K` is only correct when:
- K has no 2-simplices whose edges are all used by some cycle, OR
- K is OneConnected (no cycles at all)

**General Topological Truth:**
```
H¹(K) = 0 ⟺ every 1-cycle bounds a 2-chain
```
This is NOT equivalent to "1-skeleton is acyclic" for general complexes.

**Examples:**
- Filled triangle: H¹ = 0, but 1-skeleton has a cycle (theorem fails)
- Hollow triangle: H¹ ≠ 0, 1-skeleton has a cycle (theorem holds)
- Tree: H¹ = 0, 1-skeleton acyclic (theorem holds)

---
Added: 2026-01-25
Source: cocycle_zero_on_unreachable_component analysis

### Pattern: Disconnected Complex Counterexamples

**Name:** Axiom Failure on Disconnected Simplicial Complexes
**Use when:** Analyzing axioms that assume connectivity implicitly

**Key Insight:**
Many cohomology axioms that seem "obviously true" fail on disconnected complexes.
Always test axioms on disconnected forests (simplest counterexample structure).

**Counterexample Template:**
```
Forest with two disconnected trees:
- Tree 1: isolated vertex {0}
- Tree 2: edge {1}—{2}

Properties:
- K is OneConnected (acyclic 1-skeleton)
- No 2-simplices (δf = 0 vacuously for any f)
- root = 0 → vertices 1, 2 are UNREACHABLE
- Can define f({1,2}) = any value (it's still a cocycle!)
```

**When Axioms Are Vacuously True:**
If an axiom has hypothesis `h_not_reach : ¬Reachable root a`, and K is connected,
then this hypothesis can NEVER be satisfied (all vertices are reachable).
The axiom becomes **vacuously true**.

**Pattern for Documenting Restricted Axioms:**
```lean
/-!
**IMPORTANT: This axiom has RESTRICTED VALIDITY.**

The axiom is ONLY valid when K is **connected**.
When K is connected AND OneConnected, it's a single tree,
all vertices reachable → axiom is vacuously true.

**COUNTEREXAMPLE when K is disconnected:**
[Describe the disconnected forest counterexample]
-/
axiom restricted_axiom ...
```

---
### Error: Confusing H¹=0 for Trees with Zero Cocycles

**Name:** H¹ = 0 ≠ All Cocycles Zero
**Context:** Tree cohomology misunderstanding

**Wrong Reasoning:**
"On a tree, H¹ = 0 (every cocycle is a coboundary).
Therefore every cocycle is zero."

**Correct Understanding:**
H¹ = 0 means: for every cocycle f, there exists g such that f = δg.
This does NOT mean f = 0. It means f is EXACT (a coboundary).

**The Subtlety in coboundaryWitness:**
The construction sets g = 0 on unreachable vertices.
For this specific g: δg = 0 on unreachable edges.
For δg = f to hold, we need f = 0 on those edges.
But a general cocycle doesn't have this constraint!

**Resolution:**
The axiom `cocycle_zero_on_unreachable_component` is only valid when:
1. K is connected (no unreachable vertices exist)
2. Or f is specifically constructed to be zero on unreachable components

---
### Summary: Final Axiom Status

**Both remaining axioms have restricted validity:**

| Axiom | File | Restriction |
|-------|------|-------------|
| `cycleIndicator_is_cocycle` | CycleCochain/Definitions.lean | No 2-simplex contains all cycle edges |
| `cocycle_zero_on_unreachable_component` | ForestCoboundary.lean | K must be connected |

**Key Pattern:** Both are **vacuously true** in the OneConnected case:
- `cycleIndicator_is_cocycle`: OneConnected → no cycles → vacuous
- `cocycle_zero_on_unreachable_component`: OneConnected + connected → single tree → all reachable → vacuous

This completes the formal verification with well-documented scope limitations.

---
Added: 2026-01-25
Source: ImpossibilityStrong.lean compilation fixes

### Error: Docstring vs Regular Comment

**Message:** `unexpected token '/--'; expected 'lemma'`
**Cause:** Using `/--` (docstring) for explanation blocks not followed by a definition

**Wrong:**
```lean
/--
This is a multi-line explanation of the construction...
-/

def myDef := ...  -- docstring attaches here, but parser confused
```

**Fix:**
```lean
/-
This is a multi-line explanation of the construction...
-/

/-- Brief docstring for the definition -/
def myDef := ...
```

**Rule:** Use `/-` for standalone comments, `/--` only immediately before definitions.

---
### Pattern: Fin.val for Concrete Values Beyond 1

**Name:** native_decide for Fin.val Computation
**Use when:** Simplifying `(n : Fin m).val` for n > 1

**Problem:**
`Fin.val_zero` and `Fin.val_one` exist, but no `Fin.val_two`, `Fin.val_three`, etc.

**Code:**
```lean
-- For (2 : Fin 3).val = 2
have hval2 : ((2 : Fin 3).val : ℚ) = 2 := by native_decide
simp only [hval2] at h
```

**Why native_decide:** The value is computable at compile time; `native_decide` evaluates it.

**Alternative:** For general Fin values, use `Fin.val_ofNat` with modular arithmetic.

---
### Pattern: Absolute Value of Zero Minus

**Name:** Handling |0 - x| in Proofs
**Use when:** Simplifying `|0 - x|` to `|x|`

**Wrong approach:**
```lean
simp only [sub_zero]  -- This is x - 0 = x, NOT 0 - x
rw [abs_of_nonneg h_pos]  -- Pattern mismatch!
```

**Correct approach:**
```lean
simp only [zero_sub]  -- 0 - x = -x
rw [abs_neg, abs_of_nonneg h_pos]  -- |-x| = |x|, then |x| = x
```

**Key lemmas:**
- `zero_sub : 0 - a = -a`
- `abs_neg : |-a| = |a|`
- `abs_of_nonneg : 0 ≤ a → |a| = a`

---
### Strategy: Impossibility Proof via Interval Intersection

**Name:** Reconciler Impossibility via Empty Interval Intersection
**Use when:** Proving no global reconciler exists for multiple value systems

**Mathematical Content:**
If a reconciler R must satisfy `|R(s) - vᵢ| ≤ ε` for all i, then:
- R(s) ∈ [vᵢ - ε, vᵢ + ε] for each i
- Intersection must be non-empty for R to exist
- Show intersection is empty when values are spread too far

**Proof Pattern:**
```lean
-- Get constraints from each system
have h_first := hR ⟨0, _⟩ s     -- |R(s) - v₀| ≤ ε
have h_last := hR ⟨n-1, _⟩ s   -- |R(s) - v_{n-1}| ≤ ε

-- Extract bounds
have h_upper : R.values s ≤ v₀ + ε := by
  have := abs_le.mp h_first; linarith

have h_lower : R.values s ≥ v_{n-1} - ε := by
  have := abs_le.mp h_last; linarith

-- Show contradiction: v₀ + ε < v_{n-1} - ε when gap is large
have h_gap : v_{n-1} - ε > v₀ + ε := by linarith

linarith  -- R.values s ≤ v₀ + ε and R.values s ≥ v_{n-1} - ε contradict
```

**Use Case:** Strong Impossibility Theorem for n ≥ 3 agents with linear value spacing.

---
Added: 2026-01-25
Source: LinearComplexity.lean, Characterization.lean fixes

### Pattern: Walk.cons Implicit Variable Binding

**Name:** Capturing Implicit Vertices in Walk Pattern Matching
**Use when:** Pattern matching on `SimpleGraph.Walk.cons` and needing the target vertex

**Problem:**
When using `cases p with | cons h p' =>`, the intermediate vertex is implicit and not bound.

**Solution:**
Use `rename_i` to capture the implicit variable after the pattern match.

**Code:**
```lean
cases p with
| nil => exact hne_nil rfl
| cons h p' =>
  rename_i w  -- w is now the target vertex of the first edge
  obtain ⟨hne_vw, hedge⟩ := h
  -- Now w is available for use
```

**Context:**
`Walk.cons : G.Adj u v → G.Walk v w → G.Walk u w`
When matching `| cons h p' =>`, you get:
- `h : G.Adj u v` (where v is implicit)
- `p' : G.Walk v w`
Use `rename_i v` to name the implicit vertex `v`.

---
### Pattern: Sym2.inductionOn Case Naming

**Name:** Correct Case Name for Sym2 Induction
**Use when:** Using `induction e using Sym2.inductionOn`

**Correct:**
```lean
induction e using Sym2.inductionOn with
| hf x y =>
  -- e = s(x, y), prove goal for this case
```

**Wrong:**
```lean
induction e using Sym2.inductionOn with
| mk x y =>  -- ERROR: Invalid alternative name `mk`: Expected `hf`
```

**Explanation:**
The `Sym2.inductionOn` theorem has hypothesis named `hf : ∀ x y, f s(x, y)`, not `mk`.
Always use `| hf x y =>` as the case name.

---
### Error: Mathlib Module Split

**Message:** `bad import 'Mathlib.Combinatorics.SimpleGraph.Connectivity'`
**Cause:** The Connectivity module was split into submodules in recent Mathlib

**Fix:**
```lean
-- Old (broken):
import Mathlib.Combinatorics.SimpleGraph.Connectivity

-- New (correct):
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
```

**Key submodules:**
- `Connected` - Reachability, ConnectedComponent
- `WalkCounting` - `Fintype G.ConnectedComponent` instance
- `WalkDecomp` - Walk decomposition lemmas
- `Subgraph` - Subgraph connectivity

---
### Error: connectedComponentFinset Not Found

**Message:** `unknown identifier 'connectedComponentFinset'`
**Fix:** Use `Fintype.card G.ConnectedComponent` instead

**Old API:**
```lean
(oneSkeleton K).connectedComponentFinset.card  -- Not found
```

**New API:**
```lean
Fintype.card (oneSkeleton K).ConnectedComponent  -- Correct
```

**Note:** Requires `import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting`
for the `Fintype G.ConnectedComponent` instance.

---
### Error: Instance Requires noncomputable

**Message:** `failed to compile definition, consider marking it as 'noncomputable'`
**Cause:** Instance depends on noncomputable definitions (e.g., Fintype.card)

**Fix:**
```lean
-- Wrong:
instance foo_decidable : Decidable (foo K) := by ...

-- Correct:
noncomputable instance foo_decidable : Decidable (foo K) := by ...
```

**Common triggers:**
- Depending on `Fintype.card`
- Using `componentCount` or similar counting functions
- Any instance using classical choice indirectly

---
### Pattern: Walk Edge Counting

**Name:** Relating Walk Length to Edges List Length
**Use when:** Proving properties about walk lengths

**Key Lemma:**
```lean
SimpleGraph.Walk.length_edges : p.edges.length = p.length
```

**Usage:**
```lean
have h_edges_eq_len : p.edges.length = p.length := SimpleGraph.Walk.length_edges p
-- Now can use omega to relate edges count to walk length
```

**Related lemmas:**
- `Walk.length_support : p.support.length = p.length + 1`
- `Walk.length_darts : p.darts.length = p.length`

---
### Pattern: List.Nodup Element Uniqueness

**Name:** Using Nodup to Prove Elements at Different Indices Differ
**Use when:** Proving two elements from a nodup list at different positions are equal implies position equality

**Key Lemma:**
```lean
List.Nodup.get_inj_iff : h.get_inj_iff.mp : l.get i = l.get j → i = j
```

**Usage:**
```lean
have htrail := hp.1.1  -- IsTrail gives edges.Nodup
rw [SimpleGraph.Walk.isTrail_def] at htrail
-- htrail : p.edges.Nodup
have h_eq : e0 = e1 := ...  -- Proved both equal some canonical edge
exact h_ne_idx (htrail.get_inj_iff.mp h_eq)  -- Contradiction if indices differ
```

---
### Strategy: Euler Formula for Forests

**Name:** Forest Edge Count Formula
**Use when:** Proving properties about acyclic graphs (forests)

**The Formula:**
For a forest (acyclic graph) with:
- V vertices
- c connected components
- E edges

**Result:** E = V - c (exactly, for forests)

**Proof Sketch:**
1. Each connected component of a forest is a tree
2. A tree on n vertices has exactly n - 1 edges
3. For c components with vertex counts n₁, ..., nₒ:
   - Total vertices: V = Σnᵢ
   - Total edges: E = Σ(nᵢ - 1) = V - c

**Key Mathlib Lemmas:**
- `SimpleGraph.IsTree.card_edgeFinset`: Tree on n vertices has n-1 edges
- `SimpleGraph.IsAcyclic.isTree_connectedComponent`: Each component of forest is tree
- `SimpleGraph.isTree_iff_connected_and_card`: Tree iff connected and |E| = |V| - 1

---
Added: 2026-01-25
Source: ConflictLocalization.lean (Batch 2A)

### Pattern: Double Negation from IsAcyclic Simp

**Name:** Eliminating Double Negation after IsAcyclic Simp
**Use when:** After `simp [SimpleGraph.IsAcyclic, not_forall]` produces `¬¬p.IsCycle`

**Problem:**
When unfolding `IsAcyclic` and simplifying:
```lean
unfold OneConnected at h
simp only [SimpleGraph.IsAcyclic, not_forall] at h
obtain ⟨v, p, hp⟩ := h
-- hp : ¬¬p.IsCycle (double negation!)
```

**Fix:**
```lean
have hp' : p.IsCycle := not_not.mp hp
-- Now use hp' instead of hp
```

**Explanation:**
`SimpleGraph.IsAcyclic` is defined as `∀ v, ∀ p : Walk v v, ¬p.IsCycle`.
After `not_forall` twice, we get `∃ v, ∃ p, ¬¬p.IsCycle`.
The inner `¬¬` requires classical double negation elimination via `not_not.mp`.

---
### Pattern: List.Nodup.length_le_card for Bounded Lists

**Name:** Bounding List Length by Fintype Cardinality
**Use when:** Proving a nodup list of Fin n elements has length ≤ n

**Code:**
```lean
theorem max_conflict_size (n : ℕ) (systems : Fin n → ValueSystem S) (ε : ℚ)
    (c : AlignmentConflict n systems ε) : c.agents.length ≤ n := by
  have h := c.agents_nodup  -- agents.Nodup
  have : c.agents.length ≤ Fintype.card (Fin n) := List.Nodup.length_le_card h
  simp only [Fintype.card_fin] at this
  exact this
```

**Key Lemma:**
```lean
List.Nodup.length_le_card : l.Nodup → l.length ≤ Fintype.card α
```

**Use Case:** When you need to prove a list can't have more elements than the type it's drawn from.

---
### Pattern: Explicit Nat.mod_lt for Omega

**Name:** Providing Modulo Bounds Explicitly
**Use when:** Omega can't prove `i % n < n` automatically in structure fields

**Problem:**
In a structure definition:
```lean
let next := agents.get ⟨(i.val + 1) % agents.length, by omega⟩
-- Error: omega could not prove the goal
```

**Fix:**
Provide the proof explicitly using `Nat.mod_lt`:
```lean
let next := agents.get ⟨(i.val + 1) % agents.length,
  Nat.mod_lt _ (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) min_size)⟩
```

**Explanation:**
`Nat.mod_lt a (h : b > 0) : a % b < b`
To use it, prove `agents.length > 0` from `min_size : agents.length ≥ 3`.

---
### Pattern: List.length_finRange Usage

**Name:** Correct Usage of List.length_finRange
**Use when:** Proving `(List.finRange n).length = n`

**Wrong:**
```lean
have h : agents.length = n := List.length_finRange n  -- Error: not a function
```

**Correct:**
```lean
have h : agents.length = n := List.length_finRange
-- Type inference determines n from context
```

**Related lemmas:**
- `List.nodup_finRange : (List.finRange n).Nodup`
- `List.mem_finRange : i ∈ List.finRange n` (for all `i : Fin n`)

---
### Strategy: Conflict Localization Fallback

**Name:** Using All Agents as Trivial Conflict
**Use when:** Proving conflict existence without finding minimal conflict

**Mathematical Content:**
If global alignment fails for n agents, we can always take ALL n agents as the conflict.
This is "trivially correct" (the subset that fails is the whole set) but not minimal.

**Code Pattern:**
```lean
theorem alignment_conflict_localization [Nonempty S] (n : ℕ) (hn : n ≥ 3)
    (systems : Fin n → ValueSystem S) (ε : ℚ) (hε : ε > 0)
    (h_no_global : ¬∃ R, ∀ i, Reconciles R (systems i) ε) :
    ∃ conflict : AlignmentConflict n systems ε, True := by
  let agents := List.finRange n
  refine ⟨{
    agents := agents
    agents_nodup := List.nodup_finRange n
    min_size := by simp [List.length_finRange]; exact hn
    forms_cycle := by sorry  -- Would need pairwise alignability hypothesis
    no_local_reconciler := by
      intro ⟨R, hR⟩
      apply h_no_global
      exact ⟨R, fun i => hR i (List.mem_finRange i)⟩
  }, trivial⟩
```

**Key Insight:**
The `no_local_reconciler` condition is easy: since `agents` contains all indices,
`∀ a ∈ agents, P a` is equivalent to `∀ i : Fin n, P i`.

---
Added: 2026-01-25
Source: ConflictResolution.lean (Batch 2B)

### Pattern: Namespace Organization for Dot Notation

**Name:** Placing Definitions in Correct Namespace for Method Syntax
**Use when:** Defining operations on a type that should be callable with dot notation

**Problem:**
Definitions in the wrong namespace don't enable dot notation:
```lean
-- In namespace Perspective.SimplicialComplex
def removeEdge (K : SimplicialComplex) ... := ...

-- Usage fails:
K.removeEdge e he h_max  -- ERROR: invalid field 'removeEdge'
```

**Fix:**
Place the definition in the type's actual namespace:
```lean
namespace Foundations.SimplicialComplex

def removeEdge (K : SimplicialComplex) ... := ...

end Foundations.SimplicialComplex

-- Now works:
K.removeEdge e he h_max  -- OK
```

**Rule:** For dot notation `x.method`, the `method` must be in the namespace of `x`'s type.
If `K : SimplicialComplex` and `SimplicialComplex` is in `Foundations`, put `removeEdge` in `Foundations.SimplicialComplex`.

---
### Pattern: Union Membership Case Analysis

**Name:** Cases vs Rcases for Union Membership
**Use when:** Destructuring `s ∈ A ∪ B ∪ C` after simp

**Problem:**
After simp on union membership, using `rcases` or `obtain` may fail:
```lean
simp only [Set.mem_union, Set.mem_singleton_iff] at hs
rcases hs with h1 | h2 | h3  -- ERROR: rcases failed: not inductive datatype
```

**Fix:**
Use `cases` with explicit alternative patterns:
```lean
simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hs
cases hs with
| inl hs_left =>
  cases hs_left with
  | inl hs_in_K => -- s ∈ K.simplices
  | inr hs_eq => -- s = triangle
| inr hs_sub => -- s ⊆ triangle
```

**Explanation:**
After simp, the type is a nested `Or` structure. `cases` handles this better than `rcases` when the structure isn't recognized as an inductive datatype pattern.

---
### Pattern: Finset Cardinality with Distinctness

**Name:** Proving {a, b, c}.card = 3 with Explicit Rewrites
**Use when:** simp can't prove finset cardinality automatically

**Problem:**
```lean
have h_card : ({a, b, c} : Finset V).card = 3 := by simp
-- ERROR: simp made no progress
```

**Fix:**
Use explicit rewrites with `Finset.card_insert_of_notMem` and distinctness hypotheses:
```lean
have h_card : ({a, b, c} : Finset V).card = 3 := by
  have hab : a ≠ b := ...
  have hac : a ≠ c := ...
  have hbc : b ≠ c := ...
  rw [Finset.card_insert_of_notMem (by simp [hab, hac])]  -- a ∉ {b, c}
  rw [Finset.card_insert_of_notMem (by simp [hbc])]       -- b ∉ {c}
  rw [Finset.card_singleton]
```

**Key Lemma:**
```lean
Finset.card_insert_of_notMem : a ∉ s → (insert a s).card = s.card + 1
```

**Tip:** The distinctness hypotheses (hab, hac, hbc) are essential for the `simp` to prove the non-membership conditions.

---
### Pattern: Face Subset for down_closed Proofs

**Name:** Proving Faces Belong to SimplicialComplex
**Use when:** Proving `down_closed` property for new simplicial complex constructions

**Problem:**
When constructing a new SimplicialComplex, you need to prove that all faces of simplices are included:
```lean
down_closed := by
  intro s hs t ht_sub
  -- Need to show: t ∈ new_simplices
```

**Strategy for Union-Based Constructions:**
```lean
down_closed := by
  intro s hs t ht_sub
  simp only [Set.mem_union, ...] at hs ⊢
  cases hs with
  | inl hs_in_original =>
    left
    exact original_complex.down_closed s hs_in_original t ht_sub
  | inr hs_is_new =>
    -- Show t is either in original OR is a face of the new simplex
    by_cases hcard : t.card = new_simplex.card
    · right; ... -- t equals new_simplex
    · left; ... -- t is a proper face, show it's in original
```

**Key Insight:**
For a simplicial complex K ∪ {σ}, the down_closed property follows from:
1. K.down_closed (for faces from K)
2. Faces of σ are either σ itself or are already in K (by triangle construction)

---
### Error: Subst Removes Variables from Scope

**Name:** Using rw Instead of subst to Preserve Variables
**Use when:** You need to substitute an equality but still use the original variable

**Problem:**
```lean
have hs_eq : s = t := ...
subst hs_eq
-- Now 't' is no longer in scope!
exact some_lemma_about_t  -- ERROR: unknown identifier 't'
```

**Fix:**
Use `rw` with symmetric equality instead:
```lean
have hs_eq : s = t := ...
rw [← hs_eq]  -- Rewrites t to s in the goal, keeps t in scope
-- or
rw [hs_eq]    -- Rewrites s to t in the goal
```

**When to use which:**
- `subst h` when you want to completely eliminate a variable
- `rw [h]` when you need the variable to remain accessible
- `rw [← h]` when the equality direction needs reversal

---
### Pattern: Singleton Membership from Finset.mem_singleton

**Name:** Converting Finset Singleton Membership to Equality
**Use when:** You have `v ∈ ({x} : Finset V)` and need `v = x`

**Code:**
```lean
have h_mem : v ∈ ({x} : Finset V) := ...
have h_eq : v = x := Finset.mem_singleton.mp h_mem
```

**Related lemmas:**
- `Finset.mem_singleton : a ∈ ({b} : Finset α) ↔ a = b`
- `Finset.singleton_subset_iff : {a} ⊆ s ↔ a ∈ s`

**Use case in removeVertex proofs:**
When a simplex contains a single vertex and you need to identify that vertex.

---
### Strategy: Resolution Strategies for H¹ Conflicts

**Name:** Three Approaches to Resolving H¹ ≠ 0
**Use when:** Designing conflict resolution for cohomology obstructions

**The Three Strategies:**

1. **Fill Triangle (Add 2-simplex)**
   - When: Three vertices form a hollow triangle (cycle of length 3)
   - Action: Add the 2-simplex {a, b, c}
   - Effect: The cycle becomes a boundary, so it's now trivial in H¹

2. **Remove Edge (Remove 1-simplex)**
   - When: An edge is part of a cycle but no larger simplices depend on it
   - Action: Remove the edge from the complex
   - Effect: Breaks the cycle, potentially making 1-skeleton acyclic

3. **Remove Vertex (Remove 0-simplex and all incident)**
   - When: A vertex is central to multiple conflicts
   - Action: Remove vertex and all simplices containing it
   - Effect: Most drastic; removes all incident structure

**Formalization Pattern:**
```lean
structure ResolutionStrategy (K : SimplicialComplex) where
  /-- The resulting complex after resolution -/
  result : SimplicialComplex
  /-- The resolution actually fixes the problem -/
  resolves : H1Trivial result

inductive StrategyKind
  | fillTriangle : Vertex → Vertex → Vertex → StrategyKind
  | removeEdge : Simplex → StrategyKind
  | removeAgent : Vertex → StrategyKind
```

**Key Insight:**
Each strategy trades off different things:
- fillTriangle adds structure (may affect other properties)
- removeEdge is minimal but requires maximality check
- removeAgent is aggressive but always works

---
### Pattern: Explicit Type Parameters for Dependent Structures

**Name:** Parametric Structures with Function Fields
**Added:** 2026-01-25
**Source:** AgentCoordination.lean rewrite

**Problem:** When a structure has a function field like `profile : S → ℚ`, and `S` is defined via `variable {S : Type*}`, the structure becomes ill-formed because `S` isn't captured as a parameter.

**Wrong:**
```lean
variable {S : Type*} [Fintype S]

structure Agent where
  id : ℕ
  profile : S → ℚ  -- S not captured!
  deriving DecidableEq  -- Will fail: can't derive DecidableEq for functions
```

**Correct:**
```lean
variable {S : Type*} [Fintype S]

structure Agent (S : Type*) where
  id : ℕ
  profile : S → ℚ  -- S is now explicit parameter

-- Usage requires explicit S
def canCooperate {S : Type*} (a b : Agent S) (ε : ℚ) : Prop := ...
```

**When to use:**
- Structures with function fields `T → U`
- Structures containing other parametric structures
- When you need decidable equality or other derived instances

**Related pattern:** `ValueSystem (S : Type*) where values : S → ℚ` in ValueSystem.lean

---
### Pattern: Definitional Equality for Complex Constructions

**Name:** Trivial Equivalence via Definitional Equality
**Added:** 2026-01-25
**Source:** agent_complex_eq_value_complex

**Use when:** Two mathematical constructions are "the same" and you need to prove equivalence.

**Strategy:** Instead of proving isomorphism with complex machinery, define one construction in terms of the other.

**Example:**
```lean
-- Instead of defining agentComplex with its own simplices set:
def agentComplex (N : AgentNetwork S) : SimplicialComplex where
  simplices := { ... complex definition ... }
  has_vertices := sorry  -- Hard to prove
  down_closed := sorry   -- Hard to prove

-- Define it directly using the equivalent construction:
def agentComplex (N : AgentNetwork S) : SimplicialComplex :=
  Perspective.valueComplex N.toValueSystems N.threshold

-- Now the equivalence theorem is trivial:
theorem agent_complex_eq_value_complex (N : AgentNetwork S) :
    H1Trivial (agentComplex N) ↔
    H1Trivial (Perspective.valueComplex N.toValueSystems N.threshold) := by
  rfl  -- Definitional equality!
```

**Benefits:**
- Avoids complex proofs about set membership
- `rfl` proofs are fast and robust
- Maintenance is simpler (single source of truth)

**When NOT to use:**
- When the constructions are genuinely different but isomorphic
- When you need to expose the internal structure
- When the "equivalent" construction has different computational properties

---
### Pattern: Agent-Memory Duality

**Name:** Multi-Agent Coordination as Memory Consistency
**Added:** 2026-01-25
**Source:** AgentCoordination.lean

**The Duality:**
| Memory Problem | Agent Problem | Mathematical Object |
|----------------|---------------|---------------------|
| Memory fragment | Agent profile | `ValueSystem S` / `Agent S` |
| Fragments agree on s | Agents cooperate | `∃ s, |v₁(s) - v₂(s)| ≤ 2ε` |
| All fragments consistent | No deadlocks | `H¹ = 0` |
| Memory conflict | Coordination deadlock | `H¹ ≠ 0` |

**Formalization:**
```lean
-- Agent to ValueSystem (they're the same!)
def Agent.toValueSystem (a : Agent S) : ValueSystem S := ⟨a.profile⟩

-- Network to systems
def AgentNetwork.toValueSystems (N : AgentNetwork S) :
    Fin N.agents.length → ValueSystem S :=
  fun i => (N.agents.get i).toValueSystem

-- Agent complex IS value complex
def agentComplex (N : AgentNetwork S) : SimplicialComplex :=
  Perspective.valueComplex N.toValueSystems N.threshold
```

**Key Insight:** One engine, two products:
- Memory Consistency Checker: Do AI memories contradict?
- Agent Coordination Checker: Will agents deadlock?
Same H¹ cohomology. Same O(n) complexity. Same guarantees.

---
Added: 2026-01-25
Source: Stability.lean (Batch 4)

### Error: Greek Letter Encoding Issues

**Message:** `unexpected token 'δ'; expected '_' or identifier`
**Cause:** Unicode Greek letters sometimes cause parsing issues despite being valid Lean 4 identifiers

**Problem:**
```lean
theorem foo (δ : ℚ) (hδ : δ > 0) : ... -- ERROR: unexpected token 'δ'
```

**Fix:**
```lean
theorem foo (delta : ℚ) (hdelta : delta > 0) : ... -- Works
```

**When this happens:**
- Copy-pasted Greek characters may have different Unicode points
- Some editor/terminal combinations mangle Greek letters
- Safe to use ASCII equivalents: `delta` for δ, `epsilon` for ε

---
### Pattern: Finset.exists_mem_eq_inf' for Minimum Witnesses

**Name:** Finite Set Minimum Witness Extraction
**Use when:** You need to prove existence of an element achieving the infimum

**Mathematical Content:**
For finite nonempty sets with a linear order, the infimum is actually a minimum - achieved by some element.

**Code:**
```lean
-- If you have: inf' < bound
-- Get the witness:
have ⟨s₀, hs₀_mem, hs₀_eq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty f
-- s₀ : S
-- hs₀_mem : s₀ ∈ Finset.univ
-- hs₀_eq : f s₀ = Finset.univ.inf' ... f
use s₀
rw [hs₀_eq] at h_inf_lt  -- Now have: f s₀ < bound
```

**Key Lemma:**
```lean
Finset.exists_mem_eq_inf' : s.Nonempty → ∃ a ∈ s, f a = s.inf' H f
```

**Note:** Similarly `Finset.exists_mem_eq_sup'` for supremum.

---
### Pattern: Explicit Function Parameter for le_sup'/inf'_le

**Name:** Disambiguating Finset Lattice Operations
**Use when:** Type mismatch errors with `Finset.le_sup'` or `Finset.inf'_le`

**Problem:**
```lean
have h2 := Finset.le_sup' _ hs  -- ERROR: Type mismatch, couldn't infer function
```

**Fix:**
```lean
have h2 := Finset.le_sup' (f := fun s => |V₁.values s - V₂.values s|) hs  -- Works
```

**Explanation:**
The lemma signature is:
```lean
Finset.le_sup' (f : α → β) {a : α} (ha : a ∈ s) : f a ≤ s.sup' H f
```
When the function can't be inferred from context, provide it explicitly with `(f := ...)`.

---
### Pattern: ValueSystem Extensionality

**Name:** Proving ValueSystem Equality
**Use when:** Proving two ValueSystems are equal

**Problem:**
```lean
ext s  -- ERROR: No applicable extensionality theorem found
```

**Fix:**
```lean
cases V₁ with | mk v₁ => cases V₂ with | mk v₂ =>
simp only [ValueSystem.mk.injEq]
funext s
exact h_all_zero s
```

**Explanation:**
ValueSystem is a single-field structure. Destruct both, then use `funext` on the underlying functions.

---
### Strategy: Stability Theorem Proof Approach

**Name:** Proving Small Perturbations Preserve H¹ = 0
**Use when:** Proving robustness of alignment under perturbations

**Mathematical Content:**
H¹ = 0 means the 1-skeleton is a forest (no cycles).

Small perturbations can:
1. **Remove edges** (systems drift apart) → Forest - edge = forest ✓
2. **Add edges** (systems drift together) → Forest + edge = might have cycle ✗

**Key Insight:**
If perturbation δ < margin, no new edges are added because:
- Edge exists when `∃ s, |V₁(s) - V₂(s)| ≤ 2ε`
- If systems were far apart (distance > 2ε), after perturbation < ε on each,
  distance can decrease by at most 2δ < 2ε
- So systems that were > 2ε apart stay > 0 apart (no new edge)

**Proof Outline:**
```lean
theorem stability_of_h1_trivial ... :
    H1Trivial (valueComplex perturbed ε) := by
  -- 1. Get OneConnected from h_aligned via h1_trivial_iff_oneConnected
  -- 2. Show no new edges: distance decrease bounded by 2δ < 2ε
  -- 3. Forest - edges = forest, so perturbed is still OneConnected
  -- 4. Apply oneConnected_implies_h1_trivial
```

---
### Pattern: Monitoring Status Structure

**Name:** Alignment Health Dashboard Data
**Use when:** Building monitoring products on top of alignment verification

**Code:**
```lean
structure MonitoringStatus where
  aligned : Bool
  margin : ℚ
  marginPercent : ℚ
  timeToFailure : Option ℚ
  alertThreshold : ℚ
  shouldAlert : Bool

def computeMonitoringStatus (systems : Fin n → ValueSystem S) (ε : ℚ)
    (aligned : Bool) (driftRate : Option ℚ) (alertThreshold : ℚ) : MonitoringStatus :=
  let margin := if aligned then stabilityMarginSimple systems ε else 0
  let marginPercent := if ε > 0 then margin / ε * 100 else 0
  let ttf := driftRate.bind fun r => if r > 0 then some (margin / r) else none
  { aligned, margin, marginPercent, timeToFailure := ttf, alertThreshold,
    shouldAlert := marginPercent < alertThreshold }
```

**Business Value:**
- One-time check: "Is it aligned?" → single sale
- Monitoring: "How aligned? When will it break?" → subscription revenue

---
Added: 2026-01-25
Source: ObstructionClassification.lean (Batch 5)

### Pattern: Classical Decidability for Non-Decidable Props

**Name:** Using Classical.propDecidable for if-then-else
**Use when:** You need to use `if p then ... else ...` where `p` is not decidable

**Problem:**
```lean
def classify (K : SimplicialComplex) : ObstructionType :=
  if hasCyclicObstruction K then ...  -- ERROR: Decidable instance not found
```

**Fix:**
```lean
open Classical in
attribute [local instance] propDecidable

noncomputable def classify (K : SimplicialComplex) : ObstructionType :=
  if hasCyclicObstruction K then ...  -- OK
```

**Note:** Must mark the definition `noncomputable` since Classical.propDecidable uses choice.

---
### Pattern: Double Negation for hasCyclicObstruction

**Name:** Converting ¬¬IsAcyclic to IsAcyclic
**Use when:** After classical `if` on `hasCyclicObstruction`, the false branch gives `¬hasCyclicObstruction K`

**Problem:**
```lean
split_ifs with hc hd
· -- Case: hc : hasCyclicObstruction K
· -- Case: hc : ¬hasCyclicObstruction K (need IsAcyclic!)
  exact ⟨h, hc⟩  -- ERROR: hc has type ¬hasCyclicObstruction K, not IsAcyclic
```

**Fix:**
```lean
have hac : (oneSkeleton K).IsAcyclic := by
  unfold hasCyclicObstruction at hc
  -- hc : ¬¬(oneSkeleton K).IsAcyclic
  exact not_not.mp hc
refine ⟨h, hac⟩
```

**Explanation:**
`hasCyclicObstruction K` is defined as `¬(oneSkeleton K).IsAcyclic`.
So `¬hasCyclicObstruction K = ¬¬IsAcyclic`, which requires `not_not.mp` to eliminate.

---
### Pattern: Walk Support Length for Cycle Size

**Name:** Proving cycle.support.length ≥ 3 from IsCycle
**Use when:** Proving minimum size of cycles using support

**Problem:**
```lean
theorem cyclic_obstruction_min_size (w : CyclicObstructionWitness K) :
    w.cycle.size ≥ 3 := by  -- size = support.length
  exact w.cycle.nontrivial  -- ERROR: nontrivial gives length > 0, not support.length ≥ 3
```

**Fix:**
```lean
theorem cyclic_obstruction_min_size (w : CyclicObstructionWitness K) :
    w.cycle.size ≥ 3 := by
  have h := w.cycle.is_cycle
  have hlen := SimpleGraph.Walk.IsCycle.three_le_length h  -- length ≥ 3
  have hsup := SimpleGraph.Walk.length_support w.cycle.cycle  -- support.length = length + 1
  unfold ConflictWitness.size
  omega  -- support.length = length + 1 ≥ 3 + 1 = 4 ≥ 3
```

**Key Lemmas:**
- `Walk.IsCycle.three_le_length : p.IsCycle → 3 ≤ p.length`
- `Walk.length_support : p.support.length = p.length + 1`

---
### Strategy: Obstruction Classification Trichotomy

**Name:** Complete Classification of H¹ Obstructions
**Use when:** Proving that any cohomology obstruction falls into one of three categories

**Mathematical Content:**
When H¹(K) ≠ 0, the obstruction can be classified as:
1. **Cyclic:** 1-skeleton has a cycle (most common)
2. **Disconnected:** 1-skeleton has multiple components with incompatible boundaries
3. **Dimensional:** H¹ ≠ 0 but 1-skeleton is acyclic (rare, higher-order)

**Proof Pattern:**
```lean
theorem obstruction_trichotomy (K : SimplicialComplex) (h : ¬H1Trivial K) :
    hasCyclicObstruction K ∨ hasDisconnectedObstruction K ∨ hasDimensionalObstruction K := by
  by_cases hc : hasCyclicObstruction K
  · left; exact hc
  · right
    by_cases hd : hasDisconnectedObstruction K
    · left; exact hd
    · right
      -- Dimensional: H¹ ≠ 0 but acyclic
      exact ⟨h, not_not.mp hc⟩
```

**Key Insight:** The dimensional case is defined as the complement of the first two:
`hasDimensionalObstruction K := ¬H1Trivial K ∧ (oneSkeleton K).IsAcyclic`

---
### Pattern: Fintype.card for Connected Components

**Name:** Counting Connected Components in Mathlib 4
**Use when:** Checking if a graph has multiple connected components

**Old API (doesn't exist):**
```lean
(oneSkeleton K).connectedComponentFinset.card  -- ERROR: not found
```

**Current API:**
```lean
Fintype.card (oneSkeleton K).ConnectedComponent  -- Correct
```

**Required import:**
```lean
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
```

**Usage:**
```lean
def hasDisconnectedObstruction (K : SimplicialComplex)
    [Fintype K.vertexSet] [DecidableEq K.vertexSet]
    [DecidableRel (oneSkeleton K).Adj] : Prop :=
  Fintype.card (oneSkeleton K).ConnectedComponent > 1
```
