# Perspective Level‑6 Lemma Backlog

> Purpose: enumerate **new lemmas** needed to eliminate remaining Perspective/ axioms and reach Level 6 without weakening statements.

## Scope
Only axioms without verified replacements are listed here. For axioms with replacements in Infrastructure/, see [.claude/axiom-registry.md](axiom-registry.md).

---

## 1) Compositional.lean (3 axioms)

### Axiom: `forest_single_edge_composition_axiom_aux`
**Location:** [Perspective/Compositional.lean](../Perspective/Compositional.lean)

**Needed lemmas (new):**
1. **`forest_union_single_edge_is_forest`**
   - **Statement (sketch):** If $G_1$ and $G_2$ are forests and $e$ is an edge joining distinct components, then $G_1 \cup G_2 \cup \{e\}$ is acyclic.
   - **Target file:** Infrastructure/GraphComposition.lean (or new Infrastructure/ForestComposition.lean)

2. **`valueComplex_forest_implies_H1Trivial`**
   - **Statement (sketch):** If the 1‑skeleton of `valueComplex` is acyclic, then `H1Trivial` holds.
   - **Target file:** Infrastructure/CompleteComplexH1.lean or Infrastructure/TreeAcyclicityComplete.lean

3. **`composition_single_edge_preserves_forest`**
   - **Statement (sketch):** The 1‑skeleton of `composeModules M₁ M₂ I` is the union of the internal forests plus at most one interface edge when `I.connections.length ≤ 1`.
   - **Target file:** Infrastructure/GraphComposition.lean

---

### Axiom: `general_acyclic_composition_axiom_aux`
**Location:** [Perspective/Compositional.lean](../Perspective/Compositional.lean)

**Needed lemmas (new):**
1. **`interfaceIsAcyclic_correct`**
   - **Statement (sketch):** Replace the current placeholder `interfaceIsAcyclic := True` with a graph‑theoretic acyclicity predicate for the combined interface graph.
   - **Target file:** Perspective/Compositional.lean (definition refactor) + Infrastructure/GraphTheoryUtils.lean

2. **`forest_union_acyclic_interface_is_forest`**
   - **Statement (sketch):** If $G_1$ and $G_2$ are forests and the interface graph is acyclic relative to the union, then the full union is acyclic.
   - **Target file:** Infrastructure/GraphComposition.lean

3. **`composition_preserves_H1Trivial_under_acyclic_interface`**
   - **Statement (sketch):** Use previous lemmas to prove `H1Trivial` of the composed module.
   - **Target file:** Infrastructure/GraphComposition.lean

---

### Axiom: `large_disagreement_breaks_alignment_aux`
**Location:** [Perspective/Compositional.lean](../Perspective/Compositional.lean)

**Needed lemmas (new):**
1. **`missing_edge_creates_nontrivial_cycle`**
   - **Statement (sketch):** In a value complex, if an interface edge is missing due to disagreement $> 2\varepsilon$ while alternative paths exist, then a nontrivial 1‑cycle exists.
   - **Target file:** Infrastructure/ConflictLocalizationProofs.lean or new Infrastructure/ValueComplexCycles.lean

2. **`disagreement_implies_edge_absent`**
   - **Statement (sketch):** If disagreement $> 2\varepsilon$, then the corresponding edge is absent in `valueComplex`.
   - **Target file:** Foundations/ValueComplex.lean or Infrastructure/CohomologyInfra.lean

3. **`nontrivial_cycle_implies_not_H1Trivial`**
   - **Statement (sketch):** Existence of a nontrivial cycle implies `¬H1Trivial`.
   - **Target file:** H1Characterization/Characterization.lean

---

## 2) EscapeTime.lean (3 axioms)

### Axiom: `escape_time_finite_ax`
**Location:** [Perspective/EscapeTime.lean](../Perspective/EscapeTime.lean)

**Needed lemmas (new):**
1. **`escapeTime_def_bounded`**
   - **Statement (sketch):** For positive `epsilon` and `tolerance`, `escapeTime` is bounded by a computable function of `misalignment` and `convergenceRate`.
   - **Target file:** Infrastructure/PathCompatibilityProofs.lean or new Infrastructure/EscapeTimeProofs.lean

2. **`misalignment_bounded_for_alignable`**
   - **Statement (sketch):** If an aligned system exists, then misalignment of any system is finite/bounded.
   - **Target file:** Infrastructure/StabilityProofs.lean

---

### Axiom: `escape_time_monotone_ax`
**Location:** [Perspective/EscapeTime.lean](../Perspective/EscapeTime.lean)

**Needed lemmas (new):**
1. **`rat_div_toNat_monotone`**
   - **Statement (sketch):** Monotonicity of `(ratio.num / ratio.den).toNat` under `tol1 ≤ tol2`.
   - **Target file:** Infrastructure/MathlibExtensions/RatNatLemmas.lean (new)

2. **`escapeTime_monotone_tolerance`**
   - **Statement (sketch):** If `tol1 ≤ tol2`, then `escapeTime ... tol2 ≤ escapeTime ... tol1`.
   - **Target file:** Infrastructure/EscapeTimeProofs.lean (new)

---

### Axiom: `escape_time_bounded_ax`
**Location:** [Perspective/EscapeTime.lean](../Perspective/EscapeTime.lean)

**Needed lemmas (new):**
1. **`escapeTime_le_worstCase`**
   - **Statement (sketch):** If `misalignment ≤ maxMis`, then `escapeTime ≤ worstCaseEscapeTime maxMis`.
   - **Target file:** Infrastructure/EscapeTimeProofs.lean (new)

2. **`rat_floor_bound`**
   - **Statement (sketch):** Basic bounding lemmas for `Rat` floor/`toNat` operations.
   - **Target file:** Infrastructure/MathlibExtensions/RatNatLemmas.lean (new)

---

## 3) AgentCoordination.lean (1 axiom)

### Axiom: `composition_deadlock_example_aux`
**Location:** [Perspective/AgentCoordination.lean](../Perspective/AgentCoordination.lean)

**Needed lemmas (new):**
1. **`hollow_triangle_network_exists`**
   - **Statement (sketch):** Construct explicit `AgentNetwork` with three agents forming a hollow triangle; show its `valueComplex` has nontrivial H¹.
   - **Target file:** Infrastructure/SmallGraphsFixed.lean or Infrastructure/SmallComplexH2.lean

2. **`two_networks_individually_H1Trivial`**
   - **Statement (sketch):** Build $N_1$ (single agent) and $N_2$ (two agents) with `H1Trivial` in their value complexes.
   - **Target file:** Infrastructure/SmallGraphsFixed.lean

3. **`compose_creates_cycle`**
   - **Statement (sketch):** Composing the above yields a hollow triangle with `¬H1Trivial`.
   - **Target file:** Infrastructure/SmallComplexH2.lean

---

## Notes
- Do **not** weaken any statements or redefine meaningful predicates as `True`.
- These lemmas should be introduced as theorems (Level 6 proofs) or kept as Level 2 axioms if a full proof is not yet achievable.
- After any code changes: run `lake build`, update `.claude/axiom-registry.md`, and run `make axiom-count`.

---

# Appendix A: Hardest Axioms → Detailed Lemma Plans

This section expands the hardest remaining axioms with concrete lemma chains and
infrastructure to build (or import) to reach Level 6 without weakening.

## A1) FairnessFoundations: `h1_trivial_implies_fair_allocation`
**Problem:** Needs a full H¹ obstruction‑vanishing → global allocation argument.

**Required new machinery (suggested files):**
- Foundations/Cohomology.lean (extend coboundary API)
- Infrastructure/FairnessComplexH1.lean (formalize extension steps)

**Lemma chain (detailed):**
1. **`fairnessComplex_complete_from_pairwise`**
   - If every pair of agents is jointly satisfiable, then the 1‑skeleton is complete.
2. **`cocycle_on_complete_graph_is_coboundary`**
   - Root‑vertex method for complete graphs (already used elsewhere, formalize for fairnessComplex).
3. **`local_consistency_triangle`**
   - Triangles enforce cocycle consistency for local allocations.
4. **`extend_allocation_by_induction`**
   - Induct on simplex size to extend a partial allocation to full set when H¹=0.
5. **`global_allocation_exists`**
   - Build `alloc : Fin n → ℚ` using `canSatisfyAgents` witness and the extension lemma.

**Notes:** Infrastructure/FairnessComplexH1.lean currently has a placeholder `True`.
Replace with the full chain above once coboundary lemmas are available.

---

## A2) Curvature: `barrier_implies_high_curvature_ax`, `low_curvature_implies_no_barrier_ax`
**Problem:** Needs curvature/obstruction equivalence on valueComplex.

**Required machinery:**
- Infrastructure/CurvatureProofs.lean (strengthen with explicit cycle ↔ curvature link)
- H1Characterization/Characterization.lean (cycle ↔ nontrivial H¹)

**Lemma chain:**
1. **`barrier_def_equiv_cycle`**: barrier ⇔ existence of a nontrivial cycle in 1‑skeleton.
2. **`cycle_implies_high_curvature`**: any nontrivial cycle yields ≥1 pair with curvature > c.
3. **`low_curvature_implies_acyclic`**: if all pairwise curvatures ≤ c, graph is acyclic.
4. **`acyclic_implies_no_barrier`**: H¹ trivial ⇒ no barrier.

---

## A3) EscapeTime: `escape_time_finite_ax`, `escape_time_monotone_ax`, `escape_time_bounded_ax`
**Problem:** Needs rational arithmetic + monotonicity of toNat on ratios.

**Required machinery:**
- Infrastructure/MathlibExtensions/RatNatLemmas.lean (new)
- Infrastructure/EscapeTimeProofs.lean (new)

**Lemma chain:**
1. **`rat_div_toNat_monotone`**: if a≤b (a,b≥0), then ⌊a⌋≤⌊b⌋ for Rat.toNat.
2. **`ratio_monotone_in_tol`**: tol1≤tol2 ⇒ (initial/tol2)≤(initial/tol1).
3. **`escapeTime_monotone_tolerance`**: combine 1–2 with `escapeTime` definition.
4. **`escapeTime_le_worstCase`**: if misalignment≤maxMis, then escapeTime ≤ worstCaseEscapeTime.
5. **`escapeTime_finite`**: bounded ratio ⇒ finite escapeTime (<1000) using 4.

---

## A4) Compositional: interface acyclicity and disagreement
**Problem:** placeholder `interfaceIsAcyclic := True` blocks real proofs.

**Required machinery:**
- Infrastructure/GraphComposition.lean (new or extend existing)
- Infrastructure/GraphTheoryUtils.lean (acyclicity for unions)

**Lemma chain:**
1. **`interface_graph_union`**: define union graph of internal edges + interface edges.
2. **`acyclic_union_of_forests`**: union of two forests plus acyclic interface is acyclic.
3. **`interface_single_edge_acyclic`**: connections.length ≤ 1 ⇒ interface graph acyclic.
4. **`disagreement_edge_absent`**: large disagreement ⇒ edge missing in valueComplex.
5. **`missing_edge_nontrivial_cycle`**: alternative path + missing edge ⇒ nontrivial cycle.

---

## A5) AgentCoordination: `composition_deadlock_example_aux`
**Problem:** needs explicit hollow‑triangle construction.

**Required machinery:**
- Infrastructure/SmallGraphsFixed.lean (explicit finite example)
- Infrastructure/SmallComplexH2.lean (H¹ nontrivial for hollow triangle)

**Lemma chain:**
1. **`hollow_triangle_network`**: explicit 3‑agent network with pairwise agreements.
2. **`pairwise_H1Trivial_components`**: N₁, N₂ individually have H¹ = 0.
3. **`compose_creates_cycle`**: composition yields hollow triangle with H¹ ≠ 0.

---

## A6) SpectralGap axioms (external)
**Problem:** requires full linear algebra and spectral theorem.

**Required machinery:**
- Mathlib linear algebra: symmetric matrices, spectral theorem.
- Graph Laplacian formalization.

**Lemma chain:**
1. **`laplacian_is_symmetric`**
2. **`quadratic_form_nonneg`**
3. **`eigenvalues_nonneg`**
4. **`λ₂_bounds`**

**Note:** these are listed as KEEP in the registry. Only attempt if Mathlib
infrastructure is adopted across the codebase.

---

# Appendix B: Repository‑Wide Missing Lemmas (Level‑6 Completion)

This section lists remaining axioms outside Perspective/ and the lemma/machinery
needed to upgrade them to Level 6. For axioms marked KEEP in the registry,
the required machinery is noted; otherwise, use existing Infrastructure proofs.

## B1) MultiAgent/

### `StrategicGame.actions_nonempty` (KEEP: structural)
**Needed machinery:** re‑design `StrategicGame` to enforce nonempty action sets in the type.
**Note:** This is a model/definition change, not a lemma.

### `StrategicGame.coordination_nash_player_bound`
**Missing lemmas:**
1. **`nash_equilibrium_exists_for_finite_game`** (mathlib game theory)
2. **`coordination_bound_from_equilibrium`** (bridge lemma connecting Nash to H¹)

### `h1_zero_local_global_ic` (MechanismDesign.lean)
**Existing replacement:** `Infrastructure.MechanismDesignProofs.h1_zero_local_global_ic_proven`
**Missing step:** bridge lemma/wiring in MultiAgent/MechanismDesign.lean (no new math).

### `compose_acyclic_h2_aux` (TreeComposition.lean)
**Missing lemmas:**
1. **`tree_composition_preserves_H2_trivial`**
2. **`acyclic_h2_characterization`** (H² for tree‑like complexes)
**Required machinery:** H² cochain/coboundary infrastructure.

### CoalitionH2 axioms
- `h1_h2_trivial_grand_coalition_aux`
- `h1_trivial_h2_nontrivial_obstruction_aux`
- `four_agent_h2_forward`
- `four_agent_h2_backward`

**Existing replacements:** `Infrastructure.CoalitionH2Proofs.*` for forward/backward and grand coalition.
**Missing step:** bridge lemmas in MultiAgent/CoalitionH2.lean to use the proven theorems.
**For `h1_trivial_h2_nontrivial_obstruction_aux`:** missing H² obstruction machinery (not yet proven).

### `nontrivial_compatible_has_gap` (GlobalLocalDuality.lean)
**Missing lemmas:**
1. **`compatible_cycle_implies_gap`** (link compatibility graph to duality gap)
2. **`gap_implies_obstruction`** (cohomological duality lemma)

---

## B2) Theories/

### H2Characterization.lean
- `filled_tetrahedron_coboundary`
- `hollow_tetrahedron_h2_nontrivial_ax`

**Missing machinery:**
1. **Full H² cochain/coboundary API** for simplicial complexes
2. **`tetrahedron_coboundary`**: explicit 2‑cochain witness for filled tetrahedron
3. **`hollow_tetrahedron_nontrivial_H2`**: nontrivial 2‑cocycle not a coboundary

---

## B3) Infrastructure/

### `stability_of_h1_trivial_aux` (AxiomElimination.lean)
**KEEP (external math):** requires persistent homology stability theorem.
**Missing machinery:** interleaving distance, persistence modules, stability theorem.

### `misalignment_zero_implies_aligned_ax` (CriticalPointsAxiomReplacements.lean)
**Existing replacement:** use the proven lemma in Infrastructure/CriticalPointsProofs.lean.
**Missing step:** remove axiom and replace with local proof (no new math).

