# Axiom Signatures (Reference)

> Load only when you need exact signature details.
> For quick status, see `axiom-status.md`.
> Last updated: 2026-02-04

---

## KEEP Axioms (Signatures)

### Conflict Resolution (Mathematically False)
```lean
-- R01: FALSE for multi-cycle complexes
axiom remove_edge_from_single_cycle_aux' (K : SimplicialComplex) (e : K.ksimplices 1)
    (h_in_cycle : e ∈ minimalCycleEdges K) : H1Trivial (K.removeEdge e)

-- R02: FALSE - filling one triangle doesn't kill other cycles
axiom fill_triangle_h1_trivial_aux' (K : SimplicialComplex) (t : Finset K.vertexSet)
    (ht : t.card = 3) (h_boundary : boundaryInK K t) : H1Trivial (K.addSimplex t)

-- R03: FALSE - no single edge in both independent cycles
axiom resolution_edge_exists_maximal_aux (K : SimplicialComplex) : ∃ e, e ∈ minimalCycleEdges K
```

### Strategic Games (Structural)
```lean
-- X25: UNPROVABLE - type allows empty action sets
axiom StrategicGame.actions_nonempty (G : StrategicGame) (a : G.Agent) : (G.actions a).Nonempty
```

### Spectral Theory (External Math)
```lean
axiom vertexDegreeAx (K : SimplicialComplex) (v : K.vertexSet) : ℕ
axiom laplacianExists (K : SimplicialComplex) [Fintype K.vertexSet] : Laplacian K
axiom laplacianEigenvalues (K : SimplicialComplex) [Fintype K.vertexSet] : ...
axiom eigenvalues_nonneg (K : SimplicialComplex) [Fintype K.vertexSet] : ...
axiom spectral_gap_bounded_aux (K : SimplicialComplex) [Fintype K.vertexSet] : ...
```

### Persistent Homology (External Math)
```lean
axiom stability_of_h1_trivial_aux {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {n : ℕ} (systems : Fin n → ValueSystem S) (ε δ : ℚ) (hε : ε > 0) (hδ : δ > 0)
    (h : H1Trivial (valueComplex systems ε)) : H1Trivial (valueComplex systems (ε + δ))

axiom measurement_robustness_aux {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {n : ℕ} (systems : Fin n → ValueSystem S) (ε : ℚ) (hε : ε > 0)
    (h : H1Trivial (valueComplex systems ε)) : ∃ δ > 0, ...
```

### H² Theory (External Math)
```lean
axiom filled_tetrahedron_coboundary (K : SimplicialComplex) ... : IsCoboundary K 2 f
axiom hollow_tetrahedron_h2_nontrivial_ax (K : SimplicialComplex) ... : ¬H2Trivial K
```

---

## PENDING Axioms (Signatures)

### Escape Time
```lean
axiom escape_time_finite_ax {n : ℕ} [NeZero n]
    (dynamics : FairnessDynamics n) (a : Allocation n)
    (h_obstruction : ¬isEquilibrium a) : ∃ k, isEquilibrium (dynamics.step^[k] a)

axiom escape_time_monotone_ax {n : ℕ} [NeZero n]
    (dynamics : FairnessDynamics n) : ...

axiom escape_time_bounded_ax {n : ℕ} [NeZero n]
    (dynamics : FairnessDynamics n) : ...
```

### Compositional
```lean
axiom forest_single_edge_composition_axiom_aux (M₁ M₂ : AlignmentModule S) : ...
axiom general_acyclic_composition_axiom_aux (M₁ M₂ : AlignmentModule S) : ...
axiom large_disagreement_breaks_alignment_aux (M₁ M₂ : AlignmentModule S) : ...
```

---

## HAS REPLACEMENT (Common Signatures)

### Fairness
```lean
-- Has replacement in FairnessAllocationProofs.lean
axiom h1_trivial_implies_fair_allocation {S : Type*} [Fintype S] [DecidableEq S]
    {n : ℕ} [NeZero n] (systems : Fin n → ValueSystem S) (ε : ℚ) (hε : ε > 0)
    (h : H1Trivial (valueComplex systems ε)) :
    ∃ R : ValueSystem S, ∀ k : Fin n, Reconciles R (systems k) ε
```

### Critical Points
```lean
-- Has replacement in CriticalPointsProofs.lean
axiom saddle_has_escape_ax {n : ℕ} (hn : n ≥ 2)
    (saddle : AlignmentLandscape n → Prop)
    (h_saddle : saddle landscape) :
    ∃ direction, EscapeDirection landscape saddle direction
```

---

## Signature Mismatch Warning

Same-named declarations may have DIFFERENT signatures:

| Name | Location | Returns |
|------|----------|---------|
| `forms_cycle_from_global_failure` | ConflictLocalization.lean | Pairwise ε-agreement |
| `forms_cycle_from_global_failure` | AxiomElimination.lean | Cocycle existence |

Always check source file signature before elimination attempts.
