# Next 5 Infrastructure Files to Create

> Target: Eliminate ~24 axioms by creating new infrastructure files (following the WalkDecomposition.lean model)
> Last updated: 2026-02-02

## Summary

| # | File to Create | Axioms Eliminated | Difficulty | Dependencies |
|---|----------------|-------------------|------------|--------------|
| 1 | `Infrastructure/DepthTheoryComplete.lean` | 6 | MEDIUM | None |
| 2 | `Infrastructure/SimplicialGraphBridge.lean` | 6 | MEDIUM-HIGH | None |
| 3 | `Infrastructure/PathDecompositionComplete.lean` | 5 | LOW | WalkDecomposition.lean |
| 4 | `Infrastructure/ComponentCountingComplete.lean` | 4 | MEDIUM | ExtendedGraphInfra.lean |
| 5 | `Infrastructure/FairnessH1Bridge.lean` | 3 | LOW | Cohomology definitions |

**Total: 24 axioms**

---

## 1. Infrastructure/DepthTheoryComplete.lean

**Purpose:** Centralize tree depth recursion, iteration chains, and well-foundedness proofs.

### Theorems to Prove

```lean
-- Core depth properties via Nat.find
theorem stepsToRoot_spec (T : TreeAuth n) (i : Fin n) :
    T.parentOrRoot^[T.stepsToRoot i] i = T.root

theorem stepsToRoot_min (T : TreeAuth n) (i : Fin n) (k : ℕ) :
    (T.parentOrRoot^[k] i = T.root) → T.stepsToRoot i ≤ k

-- Depth increment property
theorem depth_parent_relation (T : TreeAuth n) (i p : Fin n)
    (hp : T.parent i = some p) : T.stepsToRoot i = T.stepsToRoot p + 1

-- Cycle impossibility via minimum vertex
theorem no_cycle_via_depth (T : TreeAuth n) (v : Fin n)
    (p : T.toSimpleGraph.Walk v v) (hp : p.IsCycle) : False

-- Periodic orbit equivalence
theorem periodic_orbit_iff_reaches_root (T : TreeAuth n) :
    (∀ i, ∃ k, T.parentOrRoot^[k] i = T.root) ↔
    ∀ i, i ≠ T.root → ∀ k > 0, T.parentOrRoot^[k] i ≠ i

-- Path uniqueness
theorem path_to_root_unique (T : TreeAuth n) (i : Fin n) (p : List (Fin n))
    (h_head : p.head? = some i) (h_last : p.getLast? = some T.root)
    (h_chain : ∀ j k, j + 1 < p.length → p.get? j = some k →
      T.parent k = p.get? (j + 1) ∨ k = T.root) :
    p = T.pathToRoot i
```

### Axioms Eliminated

| ID | Axiom | Source File | Line |
|----|-------|-------------|------|
| T01 | `depth_parent_fuel_analysis` | MultiAgent/TreeAuthSimpleGraph.lean | 94 |
| T02 | `toSimpleGraph_acyclic_aux` | MultiAgent/TreeAuthSimpleGraph.lean | 429 |
| T03 | `path_to_root_unique_aux` | MultiAgent/TreeAuthorityAcyclicity.lean | 43 |
| T04 | `no_cycle_bookkeeping` | MultiAgent/TreeAuthorityAcyclicity.lean | 454 |
| T05 | `hierarchyComplex_acyclic_aux` | MultiAgent/TreeAuthorityH1.lean | 232 |
| X28 | `acyclic_periodic_orbit_equiv` | Theories/HierarchicalNetworkComplete.lean | 182 |

### Proof Strategy

All proofs use the same pattern:
1. Depth decreases strictly toward root (each parent step reduces depth by 1)
2. Cycles are impossible because minimum-depth vertex in a cycle has no valid predecessor
3. Use `Nat.find` minimality: if `parentOrRoot^[k] i = root`, then `stepsToRoot i ≤ k`
4. Strong induction on depth handles all cases

### Existing Infrastructure

- `TreeAuthCoreProofs.lean`: `stepsToRoot` definition, `depth_eq_stepsToRoot`
- `TreeAuthSimpleGraph.lean`: `adjacent_depth`, `walk_step_depth_change`

---

## 2. Infrastructure/SimplicialGraphBridge.lean

**Purpose:** Formalize bijection between simplicial complex 1-simplices and SimpleGraph edges.

### Theorems to Prove

```lean
-- Core bijection
theorem ksimplices_one_to_edges_bijection (K : SimplicialComplex)
    [Fintype K.vertexSet] :
    ∃ (φ : K.ksimplices 1 ≃ (oneSkeleton K).edgeFinset),
      ∀ s : K.ksimplices 1, (φ s : Sym2 K.vertexSet) = Simplex.toSym2 s.val

-- Euler formula (forward)
theorem acyclic_implies_euler (K : SimplicialComplex)
    [Fintype K.vertexSet] [Fintype (K.ksimplices 1)]
    [DecidableEq K.vertexSet] [DecidableRel (oneSkeleton K).Adj]
    (h : OneConnected K) : EulerForestCondition K

-- Euler formula (reverse)
theorem euler_implies_acyclic (K : SimplicialComplex)
    [Fintype K.vertexSet] [Fintype (K.ksimplices 1)]
    [DecidableEq K.vertexSet] [DecidableRel (oneSkeleton K).Adj]
    [Nonempty K.vertexSet]
    (h : EulerForestCondition K) : OneConnected K

-- Complete complex H¹ structure
theorem complete_complex_coboundary_exists (K : SimplicialComplex)
    [Nonempty K.vertexSet]
    (f : Cochain K 1) (hf : IsCocycle K 1 f) :
    ∃ g : Cochain K 0, ∀ {u v : K.vertexSet}, f {u, v} = g ⟨v⟩ - g ⟨u⟩

-- Edge removal preserves acyclicity
theorem remove_edge_from_single_cycle (K : SimplicialComplex)
    [Nonempty K.vertexSet]
    (e : K.ksimplices 1) (h_in_cycle : e ∈ minimalCycleEdges K) :
    H1Trivial (K.removeEdge e)

-- Triangle filling kills cycles
theorem fill_triangle_h1_trivial (K : SimplicialComplex)
    [Nonempty K.vertexSet]
    (t : Finset K.vertexSet) (ht : t.card = 3) (h_boundary : boundaryInK K t) :
    H1Trivial (K.addSimplex t)
```

### Axioms Eliminated

| ID | Axiom | Source File | Line |
|----|-------|-------------|------|
| G02 | `acyclic_implies_euler` | H1Characterization/LinearComplexity.lean | 123 |
| G03 | `euler_implies_acyclic` | H1Characterization/LinearComplexity.lean | 143 |
| R01 | `remove_edge_from_single_cycle_aux'` | Perspective/ConflictResolution.lean | 163 |
| R02 | `fill_triangle_h1_trivial_aux'` | Perspective/ConflictResolution.lean | 196 |
| R03 | `resolution_edge_exists_maximal_aux` | Perspective/ConflictResolution.lean | 217 |
| C03 | `complete_complex_coboundary_aux'` | Perspective/AlignmentEquivalence.lean | 928 |

### Proof Strategy

1. **Bijection**: 1-simplices `{u,v}` correspond exactly to edges `s(u,v)` in the 1-skeleton
2. **Euler formula**: Forest with c components on V vertices has V-c edges; sum over components using `IsTree.card_edgeFinset`
3. **Complete complex**: Pick root vertex, define `g(v) = f({root, v})`; coboundary property from cocycle condition
4. **Triangle filling**: Added 2-simplex makes the boundary 1-cycle exact (becomes a coboundary)

### Existing Infrastructure

- `OneSkeleton.lean`: `oneSkeleton` definition, `edge_gives_adj`
- `GraphTheoryUtils.lean`: `tree_euler_formula`, `forest_iff_euler`
- Mathlib: `IsTree.card_edgeFinset`

---

## 3. Infrastructure/PathDecompositionComplete.lean

**Purpose:** Extend WalkDecomposition.lean with bridge-based path splitting and hierarchical path compatibility.

### Theorems to Prove

```lean
-- Bridge path decomposition
theorem bridge_path_decomposition (G : SimpleGraph V) (v w : V)
    (hb : IsBridge' G v w) (u : V) (hr : G.Reachable u v) :
    (G.deleteEdges {s(v, w)}).Reachable u v ∨
    (G.deleteEdges {s(v, w)}).Reachable u w

-- Component separation via bridge
theorem non_v_component_path_avoids_bridge (G : SimpleGraph V) (v w : V)
    (hb : IsBridge' G v w)
    (u : V) (hu : G.connectedComponentMk u ≠ G.connectedComponentMk v)
    (u' : V) (hu' : G.Reachable u' u)
    (hn : ¬(G.deleteEdges {s(v, w)}).Reachable u' u) : False

-- Path compatibility in hierarchical network
theorem alignment_path_compatible {S : Type*} [Fintype S] [DecidableEq S]
    (H : HierarchicalNetwork S) (hwf : H.wellFormed) (i j : Fin H.numAgents)
    (k : ℕ) (hk : k + 1 < (H.authority.pathBetween i j).length) :
    H.compatible ((H.authority.pathBetween i j).get ⟨k, Nat.lt_of_succ_lt hk⟩)
                 ((H.authority.pathBetween i j).get ⟨k + 1, hk⟩)

-- Path existence in hierarchy
theorem path_compatible_aux {S : Type*} [Fintype S] [DecidableEq S]
    (H : HierarchicalNetwork S) (hwf : H.wellFormed)
    (i : Fin H.numAgents) (k : ℕ) (hk : k ≤ H.depth i) :
    ∃ path : List (Fin H.numAgents),
      path.length = k + 1 ∧
      path.head? = some i ∧
      (∀ m (hm : m + 1 < path.length),
        H.compatible (path.get ⟨m, Nat.lt_of_succ_lt hm⟩)
                     (path.get ⟨m + 1, hm⟩))

-- Composed path reaches root
theorem compose_path_reaches_root (H1 H2 : HierarchicalNetwork S)
    (b : Boundary H1 H2) (hn1 : 0 < H1.numAgents)
    (i : Fin (compositeSize H1 H2)) :
    ∃ k, (fun j => (compositeParent H1 H2 b j).getD
                   (compositeRoot H1 H2 hn1))^[k] i = compositeRoot H1 H2 hn1
```

### Axioms Eliminated

| ID | Axiom | Source File | Line |
|----|-------|-------------|------|
| G04 | `bridge_path_decomposition` | Theories/BridgeComponentTheory.lean | 171 |
| G05 | `non_v_component_path_avoids_bridge` | Theories/BridgeComponentTheory.lean | 177 |
| T06 | `alignment_path_compatible` | MultiAgent/TreeAuthorityH1.lean | 314 |
| T07 | `path_compatible_aux` | MultiAgent/HierarchicalNetwork.lean | 169 |
| X27 | `compose_path_reaches_root` | Theories/HierarchicalNetworkComplete.lean | 136 |

### Proof Strategy

1. **G04**: Use `Walk.takeUntil` - path either avoids bridge entirely (reaches v) or crosses it (reaches w first)
2. **G05**: Contradiction - if u not in v's component, path from u' to u cannot require bridge
3. **T06/T07**: Adjacent elements in `pathBetween` are parent-child; `wellFormed` ensures compatible
4. **X27**: H1 agents reach H1.root; H2 agents reach H2.root then bridge to H1

### Existing Infrastructure

- `WalkDecomposition.lean`: `takeUntil`, `dropUntil`, `mem_support_takeUntil_or_dropUntil`
- `ExtendedGraphInfra.lean`: `vertex_in_v_or_w_component` (lines 292-346) - **already proves G04/G05 logic**

---

## 4. Infrastructure/ComponentCountingComplete.lean

**Purpose:** Centralize Fintype cardinality arguments for graph components.

### Theorems to Prove

```lean
-- Bridge splits exactly one component into two
theorem bridge_component_cardinality (G : SimpleGraph V) (v w : V)
    (hb : IsBridge' G v w)
    (h_fiber_vw : ∀ c : (G.deleteEdges {s(v, w)}).ConnectedComponent,
        componentMap (deleteEdges_le G {s(v, w)}) c = G.connectedComponentMk v →
        c = (G.deleteEdges {s(v, w)}).connectedComponentMk v ∨
        c = (G.deleteEdges {s(v, w)}).connectedComponentMk w)
    (h_fiber_other : ∀ c : G.ConnectedComponent, c ≠ G.connectedComponentMk v →
        ∃! c' : (G.deleteEdges {s(v, w)}).ConnectedComponent,
          componentMap (deleteEdges_le G {s(v, w)}) c' = c)
    (hsurj : Function.Surjective (componentMap (deleteEdges_le G {s(v, w)})))
    (hdiff : (G.deleteEdges {s(v, w)}).connectedComponentMk v ≠
             (G.deleteEdges {s(v, w)}).connectedComponentMk w)
    (hsame : componentMap (deleteEdges_le G {s(v, w)})
               ((G.deleteEdges {s(v, w)}).connectedComponentMk v) =
             componentMap (deleteEdges_le G {s(v, w)})
               ((G.deleteEdges {s(v, w)}).connectedComponentMk w)) :
    Fintype.card (G.deleteEdges {s(v, w)}).ConnectedComponent =
    Fintype.card G.ConnectedComponent + 1

-- H¹ dimension bound via components
theorem h1_dim_components_bound (K : SimplicialComplex)
    [Fintype K.vertexSet] [DecidableRel (oneSkeleton K).Adj] :
    dim_H1 K ≤ edgeCount K - vertexCount K + componentCount K

-- Subtree partition
theorem subtree_partition_aux (H : HierarchicalNetwork S) (j : Fin H.numAgents) :
    ∃ (sub : Subtree H H.root), j ∈ sub.agents

-- Composite hierarchy acyclicity
theorem compose_acyclic_h2_aux (H1 H2 : HierarchicalNetwork S) (b : Bridge H1 H2)
    (h1_acyc : H1.authority.toSimpleGraph.IsAcyclic)
    (h2_acyc : H2.authority.toSimpleGraph.IsAcyclic) :
    (compose H1 H2 b).authority.toSimpleGraph.IsAcyclic
```

### Axioms Eliminated

| ID | Axiom | Source File | Line |
|----|-------|-------------|------|
| G06 | `bridge_component_cardinality` | Theories/BridgeComponentTheory.lean | 183 |
| C05 | `h1_dim_components_bound` | Perspective/DimensionBound.lean | 308 |
| X22 | `subtree_partition_aux` | MultiAgent/TreeComposition.lean | 50 |
| X23 | `compose_acyclic_h2_aux` | MultiAgent/TreeComposition.lean | 88 |

### Proof Strategy

1. **G06**: Already proven as `bridge_splits_component_aux` in ExtendedGraphInfra.lean:440 - adapt signature
2. **C05**: β₁(G) = |E| - |V| + c; apply standard bounds
3. **X22**: Every j lies on some path to root, so j ∈ subtree containing that path
4. **X23**: Composed tree has no cycles because H1 and H2 are acyclic and bridge connects roots

### Existing Infrastructure

- `ExtendedGraphInfra.lean`: `bridge_splits_component_aux` (line 440) - **already proves G06**
- Mathlib: `Fintype.card` lemmas, `ConnectedComponent` API

---

## 5. Infrastructure/FairnessH1Bridge.lean

**Purpose:** Connect H¹ triviality to fairness allocation existence.

### Theorems to Prove

```lean
-- H¹ triviality implies fair allocation exists
theorem h1_trivial_implies_fair_allocation {S : Type*} [Fintype S] [DecidableEq S]
    {n : ℕ} [NeZero n] (systems : Fin n → ValueSystem S) (ε : ℚ) (hε : ε > 0)
    (h : H1Trivial (valueComplex systems ε)) :
    ∃ R : ValueSystem S, ∀ k : Fin n, Reconciles R (systems k) ε

-- Fair allocation implies H¹ triviality
theorem fair_allocation_implies_h1_trivial {S : Type*} [Fintype S] [DecidableEq S]
    {n : ℕ} [NeZero n] (systems : Fin n → ValueSystem S) (ε : ℚ) (hε : ε > 0)
    (R : ValueSystem S) (h : ∀ k : Fin n, Reconciles R (systems k) ε) :
    H1Trivial (valueComplex systems ε)

-- Optimal Lipschitz constant achieves fairness
theorem optimal_lipschitz_achieves {n : ℕ} [NeZero n]
    (metric : SimilarityMetric n) (treatment : Allocation n) :
    isLipschitzFair metric (optimalLipschitz metric treatment) treatment
```

### Axioms Eliminated

| ID | Axiom | Source File | Line |
|----|-------|-------------|------|
| F01 | `h1_trivial_implies_fair_allocation` | Perspective/FairnessFoundations.lean | 184 |
| F02 | `fair_allocation_implies_h1_trivial` | Perspective/FairnessFoundations.lean | 195 |
| F07 | `optimal_lipschitz_achieves` | Perspective/IndividualFairness.lean | 212 |

### Proof Strategy

1. **F01**: H¹=0 means every 1-cocycle is a coboundary. The cobounding 0-cochain gives the reconciling value system R
2. **F02**: The reconciling R defines a 0-cochain whose coboundary equals any cocycle (showing all cocycles are exact)
3. **F07**: `optimalLipschitz` is defined as a supremum; continuity/compactness ensures achievability

### Existing Infrastructure

- `Foundations/Cohomology.lean`: `H1Trivial`, `IsCocycle`, `IsCoboundary` definitions
- `Perspective/FairnessFoundations.lean`: `valueComplex`, `Reconciles` definitions

---

## Verification Checklist

After creating each file:

- [ ] `lake build` passes with no new errors
- [ ] `make axiom-count` shows expected reduction
- [ ] `grep -r "sorry" --include="*.lean" | wc -l` unchanged or decreased
- [ ] Update `.claude/axiom-registry.md` with eliminations
- [ ] Update `.claude/handoff.md` with session progress

---

## Registry Updates Needed

These "axioms" are already proven (remove from registry):

| ID | Name | Status |
|----|------|--------|
| T01 | `depth_parent_fuel_analysis` | PROVEN at TreeAuthSimpleGraph.lean:271 |
| F04 | `convex_marginal_sum_ge` | PROVEN at GameTheoryBridge.lean:193 |
| F05 | `supermodular_of_convex` | PROVEN at CoalitionGameCore.lean:61 |
| F06 | `marginal_sum_telescope_aux` | PROVEN as `coalition_sum_telescope` |
