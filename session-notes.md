# Session Notes - H1 Characterization Proofs

---
## Session: 2026-01-24 (oriented_edge_coboundary)

**Theorem:** oriented_edge_coboundary
**File:** H1Characterization/CycleCochain/Definitions.lean:116-259
**Status:** COMPLETED - axiom replaced with proof

### Work Done
Replaced the `oriented_edge_coboundary` axiom with a complete 144-line proof. The theorem states:
```lean
oe.sign * (δ K 0 g) ⟨oe.toSimplex, oe.mem_edges⟩ = g (vertex0Simplex K oe.tgt) - g (vertex0Simplex K oe.src)
```

### Proof Strategy
1. **Case split** on `oe.src.val < oe.tgt.val` vs `oe.tgt.val < oe.src.val`
   - Equality ruled out by `oe.adj.1` (src ≠ tgt)

2. **For each case:**
   - Compute sorted list using `Finset.sort_insert`
   - Show `face 0` and `face 1` via `Simplex.face` definition
   - Prove face membership in `K.ksimplices 0`
   - Establish equality with `vertex0Simplex` via `Subtype.ext`
   - Unfold coboundary, expand sum over `Fin 2` using `Finset.sum_pair`
   - Apply `sign_zero = 1`, `sign_one = -1`
   - Close with `ring`

### Import Constraint
Could not use `coboundary_edge_formula` from ForestCoboundary.lean due to circular import:
- ForestCoboundary → PathIntegral → Definitions
- So Definitions cannot import ForestCoboundary

Solution: Wrote self-contained proof computing faces directly from coboundary definition.

### Patterns Added to Knowledge Base
- Edge Coboundary via Face Decomposition
- Sorted List of Two-Element Finset

### Pre-existing Error
Found pre-existing error in `cycleIndicator_sum_length` (lines 322-327) with `List.map_eq_replicate_iff.mpr` - unrelated to this change.

### Axiom Count Update
Updated header comment: AXIOMS reduced from 4 to 3.

### Time Spent
~30 minutes

---
## Session: 2026-01-24 (Continuation)

**Theorem:** singleEdge_oneConnected_axiom + review of remaining work
**File:** H1Characterization/Characterization.lean
**Status:** Completed (singleEdge), review of remaining items done

### Work Done
This session was a continuation from a previous context. The `singleEdge_oneConnected_axiom` was completed (converted from axiom to theorem with ~180 lines of proof). The session reviewed remaining work: 3 sorries in ForestCoboundary.lean and 5 axioms in CycleCochain/Definitions.lean.

### Errors Encountered
| Error | Fix | Added to KB? |
|-------|-----|--------------|
| native_decide needed for 0 ≠ 1 | Use native_decide not decide | Yes |
| Walk.noConfusion for ne_nil | Use noConfusion not direct pattern | Yes |
| Sym2.eq_iff for edge equality | Case split on both orderings | Yes |

### Patterns Used

- IsCycle Construction (from hollowTriangle proof)
- Finset Pair Membership Transport
- Case analysis on walk structure (nil vs cons)

### Remaining Work
| Line | Type | Statement | Suggested Approach |
|------|------|-----------|-------------------|
| ForestCoboundary.lean:375 | sorry | pathIntegral_difference_on_edge | Use path uniqueness in forests |
| ForestCoboundary.lean:424 | sorry | cocycle_zero_on_unreachable_component | Show unreachable component is isolated tree |
| ForestCoboundary.lean:477 | sorry | coboundaryWitness_works (reachable case) | Use pathIntegral_difference_on_edge |
| Definitions.lean:90 | axiom | cycleIndicator_is_cocycle | Keep as axiom (topological fact) |
| Definitions.lean:116 | theorem | oriented_edge_coboundary | COMPLETED (2026-01-24) |
| Definitions.lean:138 | axiom | cycleIndicator_self_contribution | Prove using trail edges_nodup |
| Definitions.lean:322 | theorem | cycleIndicator_sum_length | PRE-EXISTING ERROR (List.map_eq_replicate_iff issue) |
| Definitions.lean:344 | theorem | cycleIndicator_not_coboundary | COMPLETED (2026-01-24) |
| Characterization.lean:163 | axiom | (was singleEdge_oneConnected_axiom) | COMPLETED |

### Dependencies
- cycleIndicator_self_contribution → cycleIndicator_sum_length (sequential)
- pathIntegral_difference_on_edge → coboundaryWitness_works (sequential)

### Key Insight
For singleEdge acyclicity: any closed walk in a 2-vertex, 1-edge graph must traverse the single edge at least twice to return, violating IsTrail (edges.Nodup). Pattern-match on walk structure and show duplicate edge membership.

### Time Spent
~20 minutes (mostly reviewing continuation context and verifying build)

---
## Session: 2026-01-24 (cycleIndicator_not_coboundary)

**Theorem:** cycleIndicator_not_coboundary
**File:** H1Characterization/CycleCochain/Definitions.lean:344-359
**Status:** COMPLETED - axiom replaced with proof

### Work Done
Replaced the `cycleIndicator_not_coboundary` axiom with a 15-line proof. The theorem states:
```lean
¬IsCoboundary K 1 (cycleIndicator K C)
```

### Proof Strategy
1. **Assume** `cycleIndicator K C = δ K 0 g` for some `g` (via `IsCoboundary`)
2. **Compute** walk sum two ways:
   - `cycleIndicator_sum_length`: `cochainWalkSum K (cycleIndicator K C) C = C.length`
   - `coboundary_walk_sum_zero`: `cochainWalkSum K (δ K 0 g) C = 0`
3. **Substitute** `hg` into the coboundary walk sum
4. **Derive** `(C.length : ℚ) = 0` by transitivity (`h1.symm.trans h2`)
5. **Convert** to `C.length = 0` via `Nat.cast_injective`
6. **Contradict** with `hC.three_le_length` (cycles have length ≥ 3)
7. **Close** with `omega`

### Key Technique
Used `Nat.cast_injective` to convert `(n : ℚ) = 0` to `n = 0` for omega compatibility.

### Note on IsCoboundary
The `IsCoboundary` definition gives `hg : δ K 0 g = cycleIndicator K C` (coboundary equals the cochain), so rewrite into the coboundary walk sum `h2`, not `h1`.

### Axiom Count Update
Updated header comment: AXIOMS reduced from 3 to 2.

### Pre-existing Error
The `cycleIndicator_sum_length` theorem (lines 322-327) still has a pre-existing error with `List.map_eq_replicate_iff.mpr` - this blocks the build but is unrelated to this change.

---
## Session: 2026-01-24 (cycleIndicator_self_contribution)

**Theorem:** cycleIndicator_self_contribution
**File:** H1Characterization/CycleCochain/Definitions.lean:418-514
**Status:** COMPLETED - axiom replaced with proof

### Work Done
Replaced the `cycleIndicator_self_contribution` axiom with a ~100-line proof. The theorem states:
```lean
∀ oe ∈ walkToOrientedEdges K C,
  oe.sign * cycleIndicator K C ⟨oe.toSimplex, oe.mem_edges⟩ = 1
```

Also fixed the pre-existing error in `cycleIndicator_sum_length` by rewriting it to avoid `List.map_eq_replicate_iff.mpr`.

### Proof Strategy
1. **Get the dart** `d` corresponding to the oriented edge `oe`
2. **Extract trail uniqueness**: Use `trail_dart_edge_unique'` to show exactly one dart has the same edge
3. **Prove `same_edge_implies_eq`**: Any dart with the same edge must equal `d` (via `countP_eq_one_unique`)
4. **Case split** on `d.fst.val < d.snd.val`:
   - **Positive case (src < tgt)**: sign = 1, countPositive = 1, countNegative = 0
   - **Negative case (tgt < src)**: sign = -1, countPositive = 0, countNegative = 1
5. **For counting proofs**:
   - Use `countP_eq_one_of_refines`: if countP for weaker predicate (edge equality) = 1,
     and our stronger predicate (same simplex + orientation) implies it,
     and `d` satisfies the stronger predicate, then stronger count = 1
   - Use `List.countP_eq_zero.mpr` for the zero cases
6. **Final computation**: `1 * 1 = 1` or `(-1) * (-1) = 1` via `ring`

### Helper Lemmas Added
- `countP_eq_one_unique`: If countP = 1, any two satisfying elements are equal
- `countP_le_of_imp`: countP for stronger predicate ≤ countP for weaker
- `countP_pos_of_mem`: countP ≥ 1 when an element satisfies the predicate
- `countP_eq_one_of_refines`: Combines above to prove countP = 1 for refined predicate
- `sum_eq_length_of_all_one`: If all list elements are 1, sum = length

### cycleIndicator_sum_length Fix
Rewrote proof to avoid non-existent `List.map_eq_replicate_iff`:
- Created `sum_eq_length_of_all_one` helper
- Used it to show sum of all-1 list equals length
- Build now succeeds

### Axiom Count Update
Updated header comment: AXIOMS reduced from 2 to 1.
Only remaining axiom: `cycleIndicator_is_cocycle` (standard topological fact).

### Key Insight
The core insight is using trail uniqueness: `IsTrail` means each undirected edge appears exactly once in the walk. Combined with knowing which orientation the dart `d` has, we can prove exactly one of countPositive/countNegative equals 1 and the other equals 0.

---
## Session: 2026-01-24 (cocycle_zero_on_unreachable_component)

**Theorem:** cocycle_zero_on_unreachable_component
**File:** H1Characterization/ForestCoboundary.lean:398-445
**Status:** PARTIAL - Step 1 complete, Step 2 needs further work

### Work Done
Made progress on the `cocycle_zero_on_unreachable_component` theorem which states:
```lean
theorem cocycle_zero_on_unreachable_component (K : SimplicialComplex) (hK : OneConnected K)
    (f : Cochain K 1) (hf : IsCocycle K 1 f) (root : K.vertexSet)
    (e : { s : Simplex // s ∈ K.ksimplices 1 })
    (a b : Vertex) (ha : a ∈ K.vertexSet) (hb : b ∈ K.vertexSet)
    (h_edge : e.val = {a, b})
    (h_not_reach : ¬(oneSkeleton K).Reachable root ⟨a, ha⟩) :
    f e = 0
```

### Proof Strategy (Partially Implemented)

**Step 1 (COMPLETE):** Show b is also unreachable from root
```lean
have h_not_reach_b : ¬(oneSkeleton K).Reachable root ⟨b, hb⟩ := by
  intro h_reach_b
  have h_adj : (oneSkeleton K).Adj ⟨b, hb⟩ ⟨a, ha⟩ := by
    apply edge_implies_adj K b a hb ha
    rw [Finset.pair_comm, ← h_edge]
    exact e.property
  exact h_not_reach (h_reach_b.trans h_adj.reachable)
```

**Step 2 (SORRY):** Show f(e) = 0 on the isolated tree component
- The unreachable component is a tree (acyclic subgraph)
- On a tree, H¹ = 0 (every cocycle is a coboundary)
- The coboundary witness uses g = 0 on unreachable vertices
- For δg = f to hold, f must be 0 on unreachable edges

### Mathematical Analysis
The proof requires showing that on an isolated tree component, a cocycle must be zero when the coboundary witness construction sets g = 0 on all unreachable vertices.

Key insight: The theorem is used in `coboundaryWitness_works` where:
- For reachable edges: δg = f via path integration
- For unreachable edges: δg = 0 (since g = 0 on both endpoints), so we need f = 0

### Pattern Used
**Reachability Transitivity via Adjacency:**
```lean
have h_adj : (oneSkeleton K).Adj ⟨b, hb⟩ ⟨a, ha⟩ := by
  apply edge_implies_adj K b a hb ha
  rw [Finset.pair_comm, ← h_edge]
  exact e.property
exact h_not_reach (h_reach_b.trans h_adj.reachable)
```

### Dependencies
- `edge_implies_adj`: edge membership implies adjacency in 1-skeleton
- `SimpleGraph.Reachable.trans`: transitivity of reachability
- `SimpleGraph.Adj.reachable`: adjacency implies reachability

### Remaining Work
The final step requires either:
1. Completing `pathIntegral_difference_on_edge` (also has sorry)
2. Finding an alternative proof strategy for the tree cohomology argument
3. Possibly restructuring `coboundaryWitness` to handle unreachable components differently

### Notes
- The theorem is essential for `coboundaryWitness_works` and `oneConnected_implies_h1_trivial`
- Build succeeds with 3 sorries in ForestCoboundary.lean (lines 342, 398, 522)
