# Axiom Signatures (Full Reference)

> Load only when you need exact signature details. For quick status, see `axiom-status.md`.

---

## ELIMINATED Axioms

### G01: forest_single_edge_still_forest_aux
```lean
-- ELIMINATED 2026-02-02 via Infrastructure/WalkDecomposition.lean
theorem forest_single_edge_still_forest (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (u v : V) (h_neq : u ≠ v) (h_not_reach : ¬G.Reachable u v) :
    (G ⊔ fromEdgeSet {s(u, v)}).IsAcyclic
```

### G02-G03: Euler Formula
```lean
-- ELIMINATED via SimplicialGraphBridge.lean
theorem acyclic_implies_euler (K : SimplicialComplex) (h : OneConnected K) : EulerForestCondition K
theorem euler_implies_acyclic (K : SimplicialComplex) (h : EulerForestCondition K) : OneConnected K
```

### C03: complete_complex_coboundary_aux'
```lean
-- ELIMINATED via CompleteComplexH1.lean (moved valueComplex to ValueComplex.lean)
theorem complete_complex_coboundary_aux' {S' : Type*} [Fintype S'] [DecidableEq S']
    {n : ℕ} (systems : Fin n → ValueSystem S') (ε : ℚ)
    (f : Cochain (valueComplex systems ε) 1)
    (hf : IsCocycle (valueComplex systems ε) 1 f)
    (h_complete : ∀ (i j : ℕ) (hi : i < n) (hj : j < n), i < j →
      ∃ s : S', |(systems ⟨i, hi⟩).values s - (systems ⟨j, hj⟩).values s| ≤ 2 * ε) :
    IsCoboundary (valueComplex systems ε) 1 f
```

### X28: acyclic_periodic_orbit_equiv
```lean
-- ELIMINATED via TreeAuthCoreProofs.lean
-- Original was UNPROVABLE (RHS false for root). Fixed by adding i ≠ T.root:
theorem acyclic_periodic_orbit_equiv (T : TreeAuth n) :
    (∀ i, ∃ k, T.parentOrRoot^[k] i = T.root) ↔
    ∀ i, i ≠ T.root → ∀ k > 0, T.parentOrRoot^[k] i ≠ i
```

---

## KEEP Axioms (With Reasons)

### R01-R03: Conflict Resolution (MATHEMATICALLY FALSE)
```lean
-- R01: FALSE for multi-cycle complexes (counterexample: two disjoint hollow triangles)
axiom remove_edge_from_single_cycle_aux' (K : SimplicialComplex) (e : K.ksimplices 1)
    (h_in_cycle : e ∈ minimalCycleEdges K) : H1Trivial (K.removeEdge e)

-- R02: FALSE - filling one triangle doesn't kill cycles in other triangles
axiom fill_triangle_h1_trivial_aux' (K : SimplicialComplex) (t : Finset K.vertexSet)
    (ht : t.card = 3) (h_boundary : boundaryInK K t) : H1Trivial (K.addSimplex t)

-- R03: FALSE - no single edge appears in both independent cycles
axiom resolution_edge_exists_maximal_aux (K : SimplicialComplex) : ∃ e, e ∈ minimalCycleEdges K
```

### X25-X26: Strategic Games (STRUCTURAL)
```lean
-- X25: UNPROVABLE - StrategicGame type allows actions : Agent → Finset ℕ to be empty
axiom StrategicGame.actions_nonempty (G : StrategicGame) (a : G.Agent) : (G.actions a).Nonempty

-- X26: MATHEMATICALLY FALSE in full game theory (coordination games can have Nash with >2 players)
axiom StrategicGame.coordination_nash_player_bound (G : StrategicGame) ...
```

### K01-K15: External Math (KEEP)
- K01-K05: Spectral theory (requires eigenvalue machinery)
- K06-K10: Stability/dynamics (Lyapunov, bifurcation)
- K11-K15: H2 characterization (higher cohomology)

---

## PENDING Axioms (Signatures for Reference)

### T01: depth_parent_fuel_analysis
```lean
axiom depth_parent_fuel_analysis (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) :
    T.depth i = T.depth p + 1
```
**Approach**: Unfold `Nat.find` definition, use `hp` to show parent chain is one shorter.

### C01: forms_cycle_from_global_failure
```lean
axiom forms_cycle_from_global_failure {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {n : ℕ} (systems : Fin n → ValueSystem S) (ε : ℚ) (_hε : ε > 0) (i : Fin n) (j : Fin n)
    (_h_no_global : ¬∃ R : ValueSystem S, ∀ k : Fin n, Reconciles R (systems k) ε) :
    ∃ s : S, |(systems i).values s - (systems j).values s| ≤ 2 * ε
```
**WARNING**: Different signature in AxiomElimination.lean!

### F01-F02: Fairness ↔ H¹
```lean
axiom h1_trivial_implies_fair_allocation {S : Type*} [Fintype S] [DecidableEq S]
    {n : ℕ} [NeZero n] (systems : Fin n → ValueSystem S) (ε : ℚ) (hε : ε > 0)
    (h : H1Trivial (valueComplex systems ε)) :
    ∃ R : ValueSystem S, ∀ k : Fin n, Reconciles R (systems k) ε

axiom fair_allocation_implies_h1_trivial {S : Type*} [Fintype S] [DecidableEq S]
    {n : ℕ} [NeZero n] (systems : Fin n → ValueSystem S) (ε : ℚ) (hε : ε > 0)
    (R : ValueSystem S) (h : ∀ k : Fin n, Reconciles R (systems k) ε) :
    H1Trivial (valueComplex systems ε)
```
**Blocked by**: CompleteComplexH1.lean sorries

---

## Signature Mismatch Warning

Same-named declarations may have DIFFERENT signatures:

| Name | Location | Returns |
|------|----------|---------|
| `forms_cycle_from_global_failure` | ConflictLocalization.lean | Pairwise ε-agreement |
| `forms_cycle_from_global_failure` | AxiomElimination.lean | Cocycle existence |

Always check source file signature before elimination attempts.
