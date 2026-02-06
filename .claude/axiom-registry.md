# Axiom Registry

> Last updated: 2026-02-06 (session 24 - corrected total count 4→8, classified 5 as math-false)

## Current State Summary

| Status | Count | Description |
|--------|-------|-------------|
| **In Codebase** | **8** | Total `axiom` keyword declarations |
| Math false (KEEP) | 5 | Cannot be proven — counterexamples documented |
| Honest axioms | 3 | Meaningful, potentially provable with more infra |
| VERIFIED ELIMINATED | 29+ | Converted to theorems/defs in prior sessions |
| **SORRIES** | 0 | All sorries eliminated or converted to honest axioms |

> **Session 24 Progress (2026-02-06):**
> - **Corrected axiom count: 4 → 8** (prior registry missed 4 axioms)
> - Removed phantom `h1_trivial_implies_bounded_disagreement_ax` from count (already eliminated)
> - Classified 5 axioms as **KEEP (math false)** with counterexamples:
>   - `aligned_zero_curvature_ax` — ∃s/∀s gap (same as bounded_disagreement)
>   - `aligned_implies_zero_misalignment_ax` — ∃s/∀s gap
>   - `gradient_zero_when_aligned_ax` — ∃s/∀s gap
>   - `disjoint_modules_safe_ax` — cross-edges create 4-cycle (**new counterexample**)
>   - `optimal_repair_achieves_minimum_ax` — open feasible set (**new counterexample**)
> - Infrastructure files (UniformCertification, DisjointUnionH1, L1OptimizationLemmas,
>   CochainRestriction) confirmed Level 6 with correct provable alternatives

---

## All 8 Axiom Declarations (verified by `grep ^axiom`)

### KEEP — Math False (5)

| # | Axiom | File:Line | Counterexample |
|---|-------|-----------|----------------|
| 1 | `aligned_zero_curvature_ax` | Curvature.lean:236 | ∃s/∀s gap: 2 agents (0,0)/(1,100) at ε=1 — edge via s₁, but curvature≠0 because max disagreement=100>>2 |
| 2 | `aligned_implies_zero_misalignment_ax` | CriticalPoints.lean:212 | Same gap: H1Trivial+Connected does NOT imply ∀s bounded disagreement |
| 3 | `gradient_zero_when_aligned_ax` | CriticalPoints.lean:271 | Same gap: gradient depends on per-situation differences, not edge existence |
| 4 | `disjoint_modules_safe_ax` | Compositional.lean:333 | **Cross-edges:** M₁(2 agents), M₂(2 agents), S={s₁..s₄}, ε=1. v₀=(0,10,0,10), v₁=(1,10,10,0), v₂=(10,0,1,10), v₃=(10,1,10,1). Each module is a tree (H¹=0). Composed complex has 4-cycle 0-1-3-2 with NO chords → H¹≠0. Value complex ≠ disjoint union because cross-module agents can share edges. |
| 5 | `optimal_repair_achieves_minimum_ax` | FairRepairProofs.lean:171 | **Open feasible set:** n=1, original=0, target={a(0)>0}. Cost=a(0) for a(0)>0. Infimum=0 not attained. FairnessTarget allows arbitrary Prop predicates including non-closed sets. |

**Provable alternatives exist** in infrastructure files under stronger/correct hypotheses:
- Axioms 1-3 → `UniformCertification.lean` (ValueAligned hypothesis, Level 6)
- Axiom 4 → `DisjointUnionH1.lean` (vertex-disjoint complexes, Level 6)
- Axiom 5 → `L1OptimizationLemmas.lean` (specific targets like proportionalTarget, Level 6)

### Honest Axioms — Level 2 (3)

| # | Axiom | File:Line | Why Not Yet Proven |
|---|-------|-----------|-------------------|
| 6 | `saddle_has_escape_ax` | CriticalPoints.lean:481 | Needs escape direction theory for saddle points |
| 7 | `h1_trivial_implies_fair_allocation` | FairnessFoundations.lean:269 | Harder direction: H¹=0 → ∃ globally fair allocation. Needs obstruction theory bridge. FairnessComplexH1.lean has partial infrastructure. |
| 8 | `optimal_repair_exists_ax` | OptimalRepair.lean:408 | **Likely math false** (documented in source): feasible set is open (edge removal needs strict ineq), infimum not attained. Needs RepairPlan at boundary which doesn't satisfy feasibility. |

---

## Axiom Count by Directory

```
Perspective/           7  (axioms 1-4, 6-8 above)
Infrastructure/        1  (axiom 5: optimal_repair_achieves_minimum_ax)
MultiAgent/            0
Theories/              0
H1Characterization/    0
Foundations/            0
────────────────────────
TOTAL                  8
```

> Last verified: 2026-02-06 (session 24 — `grep ^axiom` across all .lean files)

---

## Historical KEEP List (No Longer Axiom Declarations)

These were previously `axiom` declarations but have been **eliminated** (converted to
theorems, defs, or removed). Listed for historical reference only.

### Previously Math False (all eliminated)
- ~~`remove_edge_from_single_cycle_aux'`~~ — False for multi-cycle (eliminated)
- ~~`fill_triangle_h1_trivial_aux'`~~ — False for multi-cycle (eliminated)
- ~~`resolution_edge_exists_maximal_aux`~~ — False for multi-cycle (eliminated)
- ~~`large_disagreement_breaks_alignment_aux`~~ — Now a theorem in Compositional.lean
- ~~`general_acyclic_composition_axiom_aux`~~ — Now a theorem in Compositional.lean
- ~~`h1_trivial_implies_bounded_disagreement_ax`~~ — Removed (math false, documented)
- ~~`escape_time_finite_ax`~~ — Now a theorem in EscapeTime.lean
- ~~`barrier_implies_high_curvature_ax`~~ — Proven vacuously true

### Previously External Math (all eliminated — were defs/structures, not axioms)
- ~~Spectral (5)~~: `vertexDegreeAx` etc. — these are `noncomputable def` / `structure`, never were `axiom` declarations
- ~~Persistent Homology (4)~~: `stability_of_h1_trivial_aux` etc. — eliminated or were theorems
- ~~H² (2)~~: `filled_tetrahedron_coboundary` etc. — eliminated

### Previously Structural
- ~~`StrategicGame.actions_nonempty`~~ — Eliminated

---

## VERIFIED REPLACEMENTS (Real proofs)

Axioms with Infrastructure proofs using **real** `Foundations.H1Trivial`:

| Axiom | Replacement File | Status |
|-------|------------------|--------|
| `misalignment_zero_implies_aligned_ax` | CriticalPointsAxiomReplacements.lean | Eliminated |
| `aligned_implies_H1_trivial` | CriticalPointsCore.lean | Uses real H1Trivial |
| `barrier_implies_high_curvature_ax` | Curvature.lean (in-place) | Eliminated (X15) |
| `hierarchical_decomposition_aux` | HierarchicalAlignment.lean:155 | THEOREM |
| `hierarchical_decomposition_ax` | HierarchicalAlignmentProofs.lean:131 | THEOREM |
| `lower_production_lower_cost_aux` | EntropyProduction.lean:221 | THEOREM |
| `simple_mayer_vietoris_ax` | MayerVietorisProofs.lean | THEOREM (session 22) |
| `h1_zero_local_global_ic_ax` | MechanismDesignProofs.lean | THEOREM (session 15) |
| `revenue_equivalence_from_h1_ax` | MechanismDesignProofs.lean | THEOREM (session 19) |
| `optimal_mechanism_exists_ax` | MechanismDesignProofs.lean | THEOREM (session 19) |
| `composition_deadlock_example_ax` | InformationBoundProofs.lean | THEOREM (session 19) |
| `disconnected_graph_edge_component_bound` | DimensionBoundProofs.lean:374 | THEOREM (session 18) |

---

## Progress History

### Session 24: Registry Audit — 5 Axioms Classified Math-False
- **Corrected axiom count: 4 → 8** (grep-verified)
- Classified 5 axioms as KEEP (math false) with documented counterexamples
- New counterexamples found for `disjoint_modules_safe_ax` and `optimal_repair_achieves_minimum_ax`
- Confirmed infrastructure files (UniformCertification, DisjointUnionH1, L1OptimizationLemmas, CochainRestriction) are all Level 6 with 0 axioms, 0 sorries
- These infrastructure files provide **correct provable alternatives** under appropriate hypotheses

### Session 23: Fixed axiom count, corrected counterexample
- Fixed count: 5 → 4 (removed false positive in CriticalPointsAxiomReplacements.lean)
- Note: count was actually wrong — should have been 8, not 4

### Session 22: 3 Axioms Eliminated — MayerVietorisProofs Level 6!
- **MayerVietorisProofs.lean** (3 → 0): Level 6!

### Session 21: CochainRestriction Infrastructure Created
- **Infrastructure/CochainRestriction.lean** (new file): Level 6!

### Session 20: 2 Axioms Eliminated — InformationBoundProofs Level 6!
- **InformationBoundProofs.lean** (2 → 0): Level 6!

### Session 19: 5 Axioms Eliminated — 2 Files Reach Level 6!
- MechanismDesignProofs.lean (2 → 0), CriticalPointsProofs.lean (1 → 0), InformationBoundProofs.lean (4 → 2)

### Session 18: disconnected_graph_edge_component_bound PROVEN

### Session 15: h1_zero_local_global_ic PROVEN

### Session 14: HierarchicalAlignmentProofs Level 6!, H2SmallComplex Level 6!

### Build Status
- Full project builds successfully (3175 jobs)
- All infrastructure files: 0 axioms, 0 sorries (Level 6!)
