# Axiom Elimination Plan: Two High-Impact Infrastructure Files

> **Goal**: Eliminate ~18-23 axioms by creating two infrastructure files that can be developed in parallel.

## Summary

| File | Axioms Eliminated | Difficulty | Dependencies |
|------|-------------------|------------|--------------|
| `Infrastructure/WalkDecomposition.lean` | 10-15 | Medium | None |
| `Infrastructure/CompleteComplexH1.lean` | 5-8 | Medium | None |
| **Combined Total** | **15-23** | | Can parallelize |

---

# File 1: `Infrastructure/WalkDecomposition.lean`

## Purpose

Provides Walk decomposition lemmas missing from Mathlib 4.27.0. The key missing lemma `Walk.support_takeUntil_append_dropUntil` blocks 6+ graph theory axioms. A working pattern already exists in `TreeGraphInfra.lean:60-82`.

## Axioms Eliminated

### Direct Eliminations (10 axioms)

| ID | Axiom | File:Line |
|----|-------|-----------|
| G01 | `forest_single_edge_still_forest_aux` | GraphComposition.lean:445 |
| G04 | `bridge_path_decomposition` | BridgeComponentTheory.lean:171 |
| G05 | `non_v_component_path_avoids_bridge` | BridgeComponentTheory.lean:177 |
| G06 | `bridge_component_cardinality` | BridgeComponentTheory.lean:183 |
| T02 | `toSimpleGraph_acyclic_aux` | TreeAuthSimpleGraph.lean:429 |
| T05 | `hierarchyComplex_acyclic_aux` | TreeAuthH1.lean:232 |
| R01 | `remove_edge_from_single_cycle_aux'` | ConflictResolution.lean:163 |
| X15 | `forest_single_edge_composition_axiom_aux` | Compositional.lean:149 |
| X16 | `general_acyclic_composition_axiom_aux` | Compositional.lean:244 |
| X29 | `pathToRoot_consecutive_adjacent` | HierarchicalNetworkComplete.lean:188 |

### Cascade Eliminations (5-8 more with additional work)

| ID | Axiom | Depends On |
|----|-------|------------|
| T03 | `path_to_root_unique_aux` | T02 + path uniqueness |
| T04 | `no_cycle_bookkeeping` | T02 + cycle structure |
| T06 | `alignment_path_compatible` | T02 + compatibility |
| T07 | `path_compatible_aux` | T02 + depth bounds |
| R02 | `fill_triangle_h1_trivial_aux'` | R01 + coboundary |

## File Structure

```lean
/-
  Infrastructure/WalkDecomposition.lean

  Walk decomposition lemmas for cycle analysis and path rerouting.
  Eliminates graph theory axioms G01, G04-G06, R01, T02.

  SORRIES: 0
  AXIOMS: 0
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import CohomologyFoundations.Infrastructure.TreeGraphInfra

namespace Infrastructure.WalkDecomposition

variable {V : Type*} [DecidableEq V] [Fintype V]
```

## Section 1: Core Support Decomposition

### Lemma 1.1: `support_takeUntil_append_dropUntil`
```lean
/-- Decompose walk support at any vertex -/
theorem support_takeUntil_append_dropUntil {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (u : V) (hu : u ∈ p.support) :
    p.support = (p.takeUntil u hu).support ++ (p.dropUntil u hu).support.tail
```

**Proof Strategy**:
- Use `Walk.support_append`
- Handle junction vertex u appearing at end of takeUntil and start of dropUntil
- Key: `dropUntil.support.tail` avoids double-counting

### Lemma 1.2: `mem_support_takeUntil_or_dropUntil`
```lean
/-- Any vertex in walk is in prefix or suffix -/
theorem mem_support_takeUntil_or_dropUntil {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (u : V) (hu : u ∈ p.support) (v : V)
    (hv : v ∈ p.support) :
    v ∈ (p.takeUntil u hu).support ∨ v ∈ (p.dropUntil u hu).support
```

### Lemma 1.3: `mem_edges_takeUntil_or_dropUntil`
```lean
/-- Any edge in walk is in prefix or suffix -/
theorem mem_edges_takeUntil_or_dropUntil {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (u : V) (hu : u ∈ p.support) (e : Sym2 V)
    (he : e ∈ p.edges) :
    e ∈ (p.takeUntil u hu).edges ∨ e ∈ (p.dropUntil u hu).edges
```

---

## Section 2: Cycle Edge Analysis

### Lemma 2.1: `takeUntil_first_endpoint_no_edge`
```lean
/-- Already proven in TreeGraphInfra.lean:60-82 - import and re-export -/
theorem takeUntil_first_endpoint_no_edge (G : SimpleGraph V)
    {a b u v : V} (p : G.Walk a b) (hp : s(u,v) ∈ p.edges)
    (hu : u ∈ p.support) (hv : v ∈ p.support) (hne : u ≠ v) :
    s(u,v) ∉ (p.takeUntil u hu).edges ∨ s(u,v) ∉ (p.takeUntil v hv).edges
```

**Source**: TreeGraphInfra.lean lines 60-82 (already proven!)

### Lemma 2.2: `cycle_other_path_avoids_edge`
```lean
/-- In any cycle using edge {u,v}, the "long way around" avoids that edge -/
theorem cycle_other_path_avoids_edge {G : SimpleGraph V}
    {a : V} (c : G.Walk a a) (hc : c.IsCycle) {u v : V}
    (he : s(u,v) ∈ c.edges) (hne : u ≠ v) :
    ∃ p : G.Walk u v, s(u,v) ∉ p.edges ∧ p.IsPath
```

**Proof Strategy**:
1. Both u,v in cycle support (from `fst/snd_mem_support_of_mem_edges`)
2. Use `takeUntil_first_endpoint_no_edge` - one prefix avoids the edge
3. Combine with dropUntil to construct the other path

---

## Section 3: Forest Single Edge (G01 Elimination)

### Theorem 3.1: `forest_single_edge_still_forest`
```lean
/-- ELIMINATES: forest_single_edge_still_forest_aux (GraphComposition.lean:445)
    Adding an edge between disconnected vertices preserves acyclicity -/
theorem forest_single_edge_still_forest {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (u v : V) (h_neq : u ≠ v) (h_not_reach : ¬G.Reachable u v) :
    (G ⊔ fromEdgeSet {s(u, v)}).IsAcyclic
```

**Proof Strategy**:
```
1. Suppose cycle c exists in G ⊔ {(u,v)}
2. Case 1: Cycle uses new edge
   → Extract G-path u→v via cycle_other_path_avoids_edge
   → Contradicts h_not_reach
3. Case 2: Cycle avoids new edge
   → Transfer to G
   → Contradicts hG
```

---

## Section 4: Bridge Path Decomposition (G04-G06)

### Theorem 4.1: `bridge_path_decomposition`
```lean
/-- ELIMINATES: bridge_path_decomposition (BridgeComponentTheory.lean:171) -/
theorem bridge_path_decomposition {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V} (h_bridge : G.IsBridge s(v,w)) {u : V} (hr : G.Reachable u v) :
    (G.deleteEdges {s(v,w)}).Reachable u v ∨ (G.deleteEdges {s(v,w)}).Reachable u w
```

### Theorem 4.2: `non_v_component_path_avoids_bridge`
```lean
/-- ELIMINATES: non_v_component_path_avoids_bridge (BridgeComponentTheory.lean:177) -/
theorem non_v_component_path_avoids_bridge {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V} (h_bridge : G.IsBridge s(v,w))
    (h_comp : (G.deleteEdges {s(v,w)}).Reachable u w)
    (h_not_v : ¬(G.deleteEdges {s(v,w)}).Reachable u v) :
    ∀ p : G.Walk u v, s(v,w) ∈ p.edges
```

### Theorem 4.3: `bridge_component_cardinality`
```lean
/-- ELIMINATES: bridge_component_cardinality (BridgeComponentTheory.lean:183) -/
theorem bridge_component_cardinality {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V} (h_bridge : G.IsBridge s(v,w)) :
    Fintype.card (G.deleteEdges {s(v,w)}).ConnectedComponent + 1 =
    Fintype.card G.ConnectedComponent + 1
```

---

## Section 5: Tree Cycle Contradiction (T02)

### Theorem 5.1: `tree_cycle_min_depth_contradiction`
```lean
/-- ELIMINATES: toSimpleGraph_acyclic_aux (TreeAuthSimpleGraph.lean:429) -/
theorem tree_cycle_min_depth_contradiction {n : ℕ}
    (T : TreeAuth n) (v : Fin n) (p : T.toSimpleGraph.Walk v v) (hp : p.IsCycle) :
    False
```

**Proof Strategy** (from TreeAuthCoreProofs.lean:563-582):
```
1. Find minimum depth vertex m in cycle support via Finset.argmin
2. m has two cycle neighbors (prev, next) both at depth ≥ depth(m)
3. By adjacent_depth, both have depth = depth(m) + 1
4. So m is parent of both → unique parent contradiction
5. Or: path prev→next through m vs avoiding m violates path uniqueness
```

---

## Dependency Graph

```
support_takeUntil_append_dropUntil (NEW)
    │
    ├── mem_support_takeUntil_or_dropUntil (NEW)
    │       │
    │       └── mem_edges_takeUntil_or_dropUntil (NEW)
    │               │
    │               ├── cycle_other_path_avoids_edge (NEW)
    │               │       │
    │               │       ├── forest_single_edge_still_forest → G01 ✓
    │               │       │       │
    │               │       │       ├── X15 ✓
    │               │       │       └── X16 ✓
    │               │       │
    │               │       └── remove_edge_from_single_cycle → R01 ✓
    │               │
    │               └── bridge_path_decomposition → G04 ✓
    │                       │
    │                       ├── non_v_component_path_avoids → G05 ✓
    │                       └── bridge_component_cardinality → G06 ✓
    │
    └── takeUntil_first_endpoint_no_edge (EXISTS in TreeGraphInfra)
            │
            └── tree_cycle_min_depth_contradiction → T02 ✓
                    │
                    └── hierarchyComplex_acyclic → T05 ✓
```

---

## Critical Source Files

| File | Lines | Content |
|------|-------|---------|
| `Infrastructure/TreeGraphInfra.lean` | 60-82 | Pattern for `takeUntil_first_endpoint_no_edge` |
| `Infrastructure/GraphComposition.lean` | 445 | G01 axiom location |
| `Theories/BridgeComponentTheory.lean` | 171-199 | G04-G06 axiom locations |
| `MultiAgent/TreeAuthSimpleGraph.lean` | 429 | T02 axiom location |
| `Infrastructure/TreeAuthCoreProofs.lean` | 563-582 | Min-depth cycle strategy |

---

# File 2: `Infrastructure/CompleteComplexH1.lean`

## Purpose

Implements the **Root Vertex Method** - a standard algebraic topology result proving that complete simplicial complexes have H¹ = 0. This is the shared mathematical foundation for cohomology core axioms, fairness axioms, and curvature axioms.

## The Core Mathematical Insight

For any **complete simplicial complex** K (where all vertices pairwise connected):

1. **Pick root vertex** r = vertex 0
2. **Define witness 0-cochain**: g({r}) = 0, g({v}) = f({r, v}) for v ≠ r
3. **Verify δg = f** using the **cocycle condition on triangles**

For any edge {a, b} with a < b:
- **Case a = r**: (δg)({r,b}) = g({b}) - g({r}) = f({r,b}) - 0 = f({r,b}) ✓
- **Case r < a < b**: Triangle {r, a, b} exists (complete complex)
  - Cocycle condition: f({a,b}) - f({r,b}) + f({r,a}) = 0
  - Therefore: f({a,b}) = f({r,b}) - f({r,a}) = g({b}) - g({a}) = (δg)({a,b}) ✓

This proves: **Every 1-cocycle is a 1-coboundary** → **H¹ = 0**

## Axioms Eliminated

### Direct Eliminations (5 axioms)

| ID | Axiom | File:Line |
|----|-------|-----------|
| C02 | `minimal_conflict_exists_aux` | ConflictLocalization.lean:182 |
| C03 | `complete_complex_coboundary_aux'` | AlignmentEquivalence.lean:928 |
| F01 | `h1_trivial_implies_fair_allocation` | FairnessFoundations.lean:184 |
| F02 | `fair_allocation_implies_h1_trivial` | FairnessFoundations.lean:195 |
| X12 | `h1_trivial_implies_bounded_disagreement_ax` | Curvature.lean:187 |

### Cascade Eliminations (2-3 more)

| ID | Axiom | Depends On |
|----|-------|------------|
| C01 | `forms_cycle_from_global_failure` | Already proven in AxiomElimination.lean |
| X13 | `barrier_implies_high_curvature_ax` | Via X12 + contrapositive |
| X14 | `low_curvature_implies_no_barrier_ax` | Via X12 + metric bounds |

## File Structure

```lean
/-
  Infrastructure/CompleteComplexH1.lean

  Root vertex method for proving H¹ = 0 on complete simplicial complexes.
  Eliminates cohomology core axioms C01, C02, C03 and enables F01, F02.

  SORRIES: 0
  AXIOMS: 0
-/

import Mathlib.Data.Finset.Basic
import CohomologyFoundations.Foundations.Cohomology
import CohomologyFoundations.Foundations.Coboundary
import CohomologyFoundations.H1Characterization.CycleCochain.Definitions

namespace Infrastructure.CompleteComplexH1

open SimplicialComplex Cochain

variable {V : Type*} [DecidableEq V] [Fintype V]
```

---

## Section 1: Complete Complex Membership Lemmas

### Lemma 1.1: `vertex_in_complete_complex`
```lean
/-- In a complete complex, every vertex is a 0-simplex -/
theorem vertex_in_complete_complex {K : SimplicialComplex}
    (h_complete : ∀ v w : K.vertexSet, v ≠ w → {v.val, w.val} ∈ K.simplices)
    (v : K.vertexSet) :
    {v.val} ∈ K.ksimplices 0
```

### Lemma 1.2: `edge_in_complete_complex`
```lean
/-- In a complete complex, every pair forms a 1-simplex -/
theorem edge_in_complete_complex {K : SimplicialComplex}
    (h_complete : ∀ v w : K.vertexSet, v ≠ w → {v.val, w.val} ∈ K.simplices)
    (v w : K.vertexSet) (hvw : v ≠ w) :
    {v.val, w.val} ∈ K.ksimplices 1
```

### Lemma 1.3: `triangle_in_complete_complex`
```lean
/-- In a complete complex, every triple forms a 2-simplex -/
theorem triangle_in_complete_complex {K : SimplicialComplex}
    (h_complete : ∀ v w : K.vertexSet, v ≠ w → {v.val, w.val} ∈ K.simplices)
    (h_filled : ∀ a b c : K.vertexSet, a ≠ b → b ≠ c → a ≠ c →
      {a.val, b.val, c.val} ∈ K.simplices)
    (a b c : K.vertexSet) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    {a.val, b.val, c.val} ∈ K.ksimplices 2
```

---

## Section 2: Cocycle Condition on Triangles

### Lemma 2.1: `cocycle_triangle_condition`
```lean
/-- The cocycle condition applied to a triangle {a, b, c} with a < b < c:
    f({b,c}) - f({a,c}) + f({a,b}) = 0 -/
theorem cocycle_triangle_condition {K : SimplicialComplex}
    (f : Cochain K 1) (hf : IsCocycle K 1 f)
    {a b c : Vertex} (ha : {a} ∈ K.ksimplices 0) (hb : {b} ∈ K.ksimplices 0)
    (hc : {c} ∈ K.ksimplices 0)
    (hab : a < b) (hbc : b < c)
    (h_tri : {a, b, c} ∈ K.ksimplices 2) :
    f ⟨{b, c}, edge_in_K⟩ - f ⟨{a, c}, edge_in_K⟩ + f ⟨{a, b}, edge_in_K⟩ = 0
```

### Lemma 2.2: `cocycle_rearranged`
```lean
/-- Rearranged cocycle condition: f({b,c}) = f({a,c}) - f({a,b}) -/
theorem cocycle_rearranged {K : SimplicialComplex}
    (f : Cochain K 1) (hf : IsCocycle K 1 f)
    {a b c : Vertex} (h_tri : {a, b, c} ∈ K.ksimplices 2) (hab : a < b) (hbc : b < c) :
    f ⟨{b, c}, _⟩ = f ⟨{a, c}, _⟩ - f ⟨{a, b}, _⟩
```

---

## Section 3: Root Vertex Witness Construction

### Definition 3.1: `rootVertexWitness`
```lean
/-- The root vertex witness: g(v) = f({root, v}) for v ≠ root, g(root) = 0 -/
noncomputable def rootVertexWitness {K : SimplicialComplex}
    (f : Cochain K 1) (root : K.vertexSet)
    (h_complete : ∀ v : K.vertexSet, v ≠ root → {root.val, v.val} ∈ K.simplices) :
    Cochain K 0 :=
  fun s =>
    let v := s.val.min' (by simp [Finset.card_eq_one.mp s.2.2])
    if hv : v = root.val then 0
    else f ⟨{root.val, v}, h_complete ⟨v, vertex_mem⟩ (by simp [hv])⟩
```

### Theorem 3.2: `rootVertexWitness_is_primitive` (THE KEY THEOREM)
```lean
/-- The root vertex witness satisfies δg = f -/
theorem rootVertexWitness_is_primitive {K : SimplicialComplex}
    (f : Cochain K 1) (hf : IsCocycle K 1 f)
    (root : K.vertexSet)
    (h_complete : ∀ v w : K.vertexSet, v ≠ w → {v.val, w.val} ∈ K.simplices)
    (h_filled : ∀ a b c : K.vertexSet, a ≠ b → b ≠ c → a ≠ c →
      {a.val, b.val, c.val} ∈ K.simplices) :
    δ K 0 (rootVertexWitness f root (fun v hv => h_complete root v hv.symm)) = f
```

**Proof Strategy** (50-80 lines):
```
1. Apply funext - prove equal on all 1-simplices {a, b}
2. Unfold δ and rootVertexWitness definitions
3. Case split on relationship of a, b to root:

   Case a = root (WLOG a < b):
     (δg)({root, b}) = g({b}) - g({root})
                     = f({root, b}) - 0
                     = f({root, b}) ✓

   Case b = root (WLOG a < b):
     (δg)({a, root}) = g({root}) - g({a})
                     = 0 - f({root, a})
                     = -f({root, a})
                     = f({a, root})  (by edge symmetry)
                     ✓

   Case root < a < b:
     Triangle {root, a, b} exists (h_filled)
     (δg)({a, b}) = g({b}) - g({a})
                  = f({root, b}) - f({root, a})
                  = f({a, b})  (by cocycle_rearranged on {root, a, b})
                  ✓

   Case a < root < b:
     Similar using triangle {a, root, b}

   Case a < b < root:
     Similar using triangle {a, b, root}
```

---

## Section 4: Main Theorem - Complete Complex H¹ = 0

### Theorem 4.1: `complete_complex_h1_trivial`
```lean
/-- ELIMINATES: complete_complex_coboundary_aux' (C03)
    A complete simplicial complex has H¹ = 0 -/
theorem complete_complex_h1_trivial {K : SimplicialComplex}
    (h_complete : ∀ v w : K.vertexSet, v ≠ w → {v.val, w.val} ∈ K.simplices)
    (h_filled : ∀ a b c : K.vertexSet, a ≠ b → b ≠ c → a ≠ c →
      {a.val, b.val, c.val} ∈ K.simplices)
    (h_nonempty : K.vertexSet.Nonempty) :
    H1Trivial K
```

**Proof** (10 lines):
```lean
  intro f hf
  obtain ⟨root, hroot⟩ := h_nonempty
  exact ⟨rootVertexWitness f ⟨root, hroot⟩ _,
         rootVertexWitness_is_primitive f hf _ h_complete h_filled⟩
```

---

## Section 5: Application to Value Complex (C03 Elimination)

### Theorem 5.1: `valueComplex_complete_h1_trivial`
```lean
/-- ELIMINATES: complete_complex_coboundary_aux' (AlignmentEquivalence.lean:928)
    When all pairs of systems agree within 2ε, the value complex has H¹ = 0 -/
theorem valueComplex_complete_h1_trivial {S : Type*} [Fintype S] [DecidableEq S]
    {n : ℕ} [NeZero n] (systems : Fin n → ValueSystem S) (ε : ℚ)
    (h_complete : ∀ (i j : Fin n), i < j →
      ∃ s : S, |(systems i).values s - (systems j).values s| ≤ 2 * ε) :
    H1Trivial (valueComplex systems ε)
```

---

## Section 6: Minimal Conflict Existence (C02 Elimination)

### Theorem 6.1: `minimal_conflict_exists`
```lean
/-- ELIMINATES: minimal_conflict_exists_aux (ConflictLocalization.lean:182)
    Every conflict contains a minimal sub-conflict -/
theorem minimal_conflict_exists {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {n : ℕ} (systems : Fin n → ValueSystem S) (ε : ℚ) (hε : ε > 0)
    (c : AlignmentConflict n systems ε) :
    ∃ c' : AlignmentConflict n systems ε,
      (∀ a ∈ c'.agents, a ∈ c.agents) ∧ c'.isMinimal
```

**Proof Strategy** (30 lines):
```
1. Well-founded induction on |c.agents|
2. Base case: |c.agents| = 0 → contradiction (empty set can't be conflict)
3. Inductive case:
   - If c is already minimal, done (c' = c)
   - Otherwise ∃ agent a such that c.agents \ {a} is still a conflict
   - Apply IH to smaller conflict
4. Termination: |c'.agents| < |c.agents| strictly decreases
```

---

## Section 7: Fairness H¹ Bridge (F01, F02 Elimination)

### Theorem 7.1: `fair_allocation_implies_h1_trivial`
```lean
/-- ELIMINATES: fair_allocation_implies_h1_trivial (F02)
    If a fair allocation exists, the fairness complex is complete → H¹ = 0 -/
theorem fair_allocation_implies_h1_trivial {n : ℕ} [NeZero n]
    (profile : FairnessProfile n)
    (alloc : Fin n → ℚ)
    (h : isGloballyFair profile alloc) :
    FairnessH1Trivial profile
```

**Proof** (15 lines):
```
1. isGloballyFair means ∀ i, (profile i).isFair alloc
2. Therefore for ANY subset σ of agents, canSatisfyAgents profile σ (use same alloc)
3. fairnessComplex profile is complete (all simplices present)
4. Apply complete_complex_h1_trivial
```

### Theorem 7.2: `h1_trivial_implies_fair_allocation`
```lean
/-- ELIMINATES: h1_trivial_implies_fair_allocation (F01)
    If H¹ = 0 on fairness complex, a fair allocation exists -/
theorem h1_trivial_implies_fair_allocation {n : ℕ} [NeZero n]
    (profile : FairnessProfile n)
    (h : FairnessH1Trivial profile) :
    ∃ alloc : Fin n → ℚ, isGloballyFair profile alloc
```

**Proof Strategy** (40-60 lines):
```
1. H1Trivial (fairnessComplex profile) means every cocycle is coboundary
2. Construct "constraint satisfaction" cocycle:
   - For each edge {i,j}, assign value based on constraint compatibility
3. H¹ = 0 means this cocycle has a primitive g
4. Use g to construct the witness allocation:
   - alloc(i) derived from g({i}) values
5. Verify isGloballyFair by construction
```

---

## Dependency Graph

```
complete_complex_h1_trivial (Theorem 4.1) ← THE CORE
    │
    ├── rootVertexWitness_is_primitive (Theorem 3.2)
    │       │
    │       ├── cocycle_rearranged (Lemma 2.2)
    │       │       └── cocycle_triangle_condition (Lemma 2.1)
    │       │
    │       └── rootVertexWitness (Definition 3.1)
    │
    ├── valueComplex_complete_h1_trivial → C03 ✓
    │
    ├── fair_allocation_implies_h1_trivial → F02 ✓
    │       └── h1_trivial_implies_fair_allocation → F01 ✓
    │
    └── h1_trivial_implies_bounded_disagreement → X12 ✓
            ├── barrier_implies_high_curvature → X13 ✓
            └── low_curvature_implies_no_barrier → X14 ✓

minimal_conflict_exists → C02 ✓ (independent, well-founded induction)
```

---

## Critical Source Files

| File | Lines | Content |
|------|-------|---------|
| `AlignmentEquivalence.lean` | 939-1002 | Root vertex proof outline (mathematical) |
| `Foundations/Cohomology.lean` | 13-51 | IsCocycle, IsCoboundary, H1Trivial definitions |
| `Foundations/Coboundary.lean` | 549-773 | δ² = 0, oriented boundary formulas |
| `CycleCochain/Definitions.lean` | 172-315 | oriented_edge_coboundary |
| `FairnessFoundations.lean` | 138-199 | fairnessComplex, F01, F02 axioms |
| `ConflictLocalization.lean` | 43-186 | C01, C02 axioms |

---

# Verification Plan

After creating both files:

1. **Build WalkDecomposition**:
   ```bash
   lake build Infrastructure.WalkDecomposition
   ```

2. **Build CompleteComplexH1**:
   ```bash
   lake build Infrastructure.CompleteComplexH1
   ```

3. **Update axiom references** in:
   - GraphComposition.lean (G01)
   - BridgeComponentTheory.lean (G04-G06)
   - TreeAuthSimpleGraph.lean (T02)
   - AlignmentEquivalence.lean (C03)
   - FairnessFoundations.lean (F01, F02)
   - ConflictLocalization.lean (C02)

4. **Verify axiom count**:
   ```bash
   make axiom-count
   ```

5. **Expected reduction**: 59 → ~36-41 axioms (18-23 eliminated)

---

# Axiom Landscape Summary

| Category | Before | After Both Files |
|----------|--------|------------------|
| Graph Theory (G01-G06) | 6 | **0** |
| Tree Authority (T01-T07) | 7 | **~2** |
| Cohomology Core (C01-C03) | 3 | **0** |
| Fairness (F01-F02) | 2 | **0** |
| Conflict Resolution (R01-R02) | 2 | **~1** |
| Curvature (X12-X14) | 3 | **~1** |
| Compositional (X15-X17) | 3 | **0** |
| **Total Eliminable** | ~59 | **~36-41** |
