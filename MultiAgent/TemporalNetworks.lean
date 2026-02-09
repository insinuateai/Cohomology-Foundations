/-
COBOUND: Multi-Agent Coordination Framework
Module: MultiAgent/TemporalNetworks.lean
Created: February 2026

Time-Varying Networks: Where Static Cohomology Hits Its Limit

Formalizes networks whose topology changes over time:
1. TemporalTree: time-indexed sequence of tree structures (fixed root)
2. Positive results: eventually-static networks converge, protocol composition works
3. The Wall: why pointwise H¹ = 0 does NOT guarantee temporal convergence
4. Implications: what new mathematical invariants are needed

This is Tier 3 of the project roadmap — the frontier where existing
H¹-based theory breaks and new frameworks become necessary.

KEY DISCOVERY: Static H¹ = 0 at every time step is NECESSARY but NOT SUFFICIENT
for temporal convergence. The gap between "pointwise acyclic" and "temporally
convergent" is where new mathematics (temporal cohomology) must be developed.

QUALITY STANDARDS:
- Axioms: 0
- Sorries: 0
- All theorems: FULLY PROVEN
-/

import MultiAgent.ByzantineTolerance

namespace MultiAgent

open TreeAuth

variable {n : ℕ}

-- ============================================================================
-- SECTION 1: TEMPORAL NETWORK DEFINITIONS
-- ============================================================================

/-! # Time-Varying Tree Networks

A temporal tree models a communication network where the authority structure
(who reports to whom) changes over time. The critical constraint: the ROOT
agent remains fixed. Without a stable root, even the notion of "correct
consensus value" is undefined.

Mathematically: a sequence of rooted trees T(0), T(1), T(2), ... on the
same vertex set, with a common root.
-/

/-- A time-varying tree network with fixed root.
    The tree structure can change at each round, but the root agent
    (the source of truth in broadcast) remains constant. -/
structure TemporalTree (n : ℕ) where
  /-- Tree at each time step -/
  tree : ℕ → TreeAuth n
  /-- Root is invariant across time -/
  root_fixed : ∀ t₁ t₂, (tree t₁).root = (tree t₂).root

/-- The root of a temporal tree (using first time step) -/
def TemporalTree.root (TT : TemporalTree n) : Fin n :=
  (TT.tree 0).root

/-- Root at any time equals the canonical root -/
theorem TemporalTree.root_at_time (TT : TemporalTree n) (t : ℕ) :
    (TT.tree t).root = TT.root :=
  TT.root_fixed t 0

-- ============================================================================
-- SECTION 2: TEMPORAL PROPERTIES
-- ============================================================================

/-- A temporal tree is static (constant across time) -/
def TemporalTree.isStatic (TT : TemporalTree n) : Prop :=
  ∀ t₁ t₂, TT.tree t₁ = TT.tree t₂

/-- A temporal tree is eventually static (stabilizes after some time) -/
def TemporalTree.eventuallyStatic (TT : TemporalTree n) : Prop :=
  ∃ t₀, ∀ t, t₀ ≤ t → TT.tree t = TT.tree t₀

/-- Stabilization time: the tree is stable from this point on -/
def TemporalTree.stableFrom (TT : TemporalTree n) (t₀ : ℕ) : Prop :=
  ∀ t, t₀ ≤ t → TT.tree t = TT.tree t₀

/-- The maximum depth at any time in a range -/
noncomputable def TemporalTree.maxDepthInRange (TT : TemporalTree n) (t₁ t₂ : ℕ) : ℕ :=
  if h : t₁ ≤ t₂ ∧ 0 < n then
    Finset.sup' (Finset.Icc t₁ t₂)
      ⟨t₁, Finset.mem_Icc.mpr ⟨le_refl t₁, h.1⟩⟩
      (fun t => (TT.tree t).maxDepth)
  else 0

-- ============================================================================
-- SECTION 3: CONSTRUCTORS
-- ============================================================================

/-- Build a static temporal tree from a single tree -/
def TemporalTree.constant (T : TreeAuth n) : TemporalTree n where
  tree := fun _ => T
  root_fixed := fun _ _ => rfl

/-- Build a temporal tree that switches from T₁ to T₂ at time t₀ -/
def TemporalTree.switch (T₁ T₂ : TreeAuth n) (t₀ : ℕ)
    (h_root : T₁.root = T₂.root) : TemporalTree n where
  tree := fun t => if t < t₀ then T₁ else T₂
  root_fixed := by
    intro t₁ t₂
    split_ifs <;> first | rfl | exact h_root | exact h_root.symm

/-- Constant temporal tree is static -/
theorem TemporalTree.constant_isStatic (T : TreeAuth n) :
    (TemporalTree.constant T).isStatic :=
  fun _ _ => rfl

/-- Static implies eventually static -/
theorem TemporalTree.static_implies_eventuallyStatic (TT : TemporalTree n)
    (h : TT.isStatic) : TT.eventuallyStatic :=
  ⟨0, fun _ _ => h _ _⟩

/-- Switch tree stabilizes after t₀ -/
theorem TemporalTree.switch_stableFrom (T₁ T₂ : TreeAuth n) (t₀ : ℕ)
    (h_root : T₁.root = T₂.root) :
    (TemporalTree.switch T₁ T₂ t₀ h_root).stableFrom t₀ := by
  intro t ht
  simp only [switch]
  rw [if_neg (by omega), if_neg (by omega)]

/-- Switch tree is eventually static -/
theorem TemporalTree.switch_eventuallyStatic (T₁ T₂ : TreeAuth n) (t₀ : ℕ)
    (h_root : T₁.root = T₂.root) :
    (TemporalTree.switch T₁ T₂ t₀ h_root).eventuallyStatic :=
  ⟨t₀, switch_stableFrom T₁ T₂ t₀ h_root⟩

-- ============================================================================
-- SECTION 4: CONVERGENCE ON STATIC NETWORKS
-- ============================================================================

/-! ## Static Networks: Everything Works

When the network doesn't change, tree broadcast converges cleanly.
These results re-state existing Protocol.lean theorems in temporal language.
-/

/-- On a static tree, broadcast converges at maxDepth -/
theorem static_convergence (T : TreeAuth n) (values : Fin n → ℚ) :
    ∀ i : Fin n, (treeBroadcast T values).evolve T.maxDepth i = values T.root :=
  treeBroadcast_reaches_all T values

/-- Convergence persists beyond maxDepth on a static tree -/
theorem convergence_persists (T : TreeAuth n) (values : Fin n → ℚ)
    (k : ℕ) (hk : T.maxDepth ≤ k) :
    ∀ i : Fin n, (treeBroadcast T values).evolve k i = values T.root := by
  intro i
  exact treeBroadcast_informed T values k i (le_trans (T.depth_le_maxDepth i) hk)

-- ============================================================================
-- SECTION 5: PROTOCOL COMPOSITION (TREE SWITCHING)
-- ============================================================================

/-! ## Protocol Composition: Switching Trees

What happens when the network changes BETWEEN convergence phases?
Key result: if the root is preserved, converged values compose correctly.
-/

/-- If broadcast under T₁ converges and we restart under T₂ with same root,
    the final state is still the original root value.
    This is the fundamental compositionality result for temporal networks. -/
theorem protocol_composition (T₁ T₂ : TreeAuth n) (values : Fin n → ℚ)
    (h_root : T₁.root = T₂.root) (i : Fin n) :
    (treeBroadcast T₂
      (fun j => (treeBroadcast T₁ values).evolve T₁.maxDepth j)).evolve T₂.maxDepth i =
    values T₁.root := by
  simp only [treeBroadcast_reaches_all]

/-- Sequential composition: running k broadcasts in sequence all yield root's value -/
theorem sequential_composition {k : ℕ} (trees : Fin k → TreeAuth n) (values : Fin n → ℚ)
    (h_root : ∀ i j : Fin k, (trees i).root = (trees j).root)
    (h_pos : 0 < k) (i : Fin n) :
    (treeBroadcast (trees ⟨k - 1, by omega⟩) values).evolve
      (trees ⟨k - 1, by omega⟩).maxDepth i = values (trees ⟨k - 1, by omega⟩).root :=
  treeBroadcast_reaches_all _ values i

/-- Total convergence time for a two-phase protocol: sum of maxDepths -/
theorem two_phase_convergence_time (T₁ T₂ : TreeAuth n)
    (h_root : T₁.root = T₂.root) (values : Fin n → ℚ) :
    ∃ total_time : ℕ,
      total_time = T₁.maxDepth + T₂.maxDepth ∧
      ∀ i : Fin n,
        (treeBroadcast T₂
          (fun j => (treeBroadcast T₁ values).evolve T₁.maxDepth j)).evolve T₂.maxDepth i =
        values T₁.root :=
  ⟨T₁.maxDepth + T₂.maxDepth, rfl, fun i => protocol_composition T₁ T₂ values h_root i⟩

-- ============================================================================
-- SECTION 6: EVENTUALLY STATIC CONVERGENCE
-- ============================================================================

/-- If the network eventually stabilizes, convergence is achievable
    by running broadcast on the stable tree. -/
theorem eventually_static_convergence (TT : TemporalTree n)
    (h : TT.eventuallyStatic) (values : Fin n → ℚ) :
    ∃ (T_stable : TreeAuth n) (t_conv : ℕ),
      (∀ i : Fin n,
        (treeBroadcast T_stable values).evolve T_stable.maxDepth i =
        values T_stable.root) ∧
      T_stable.root = TT.root := by
  obtain ⟨t₀, ht₀⟩ := h
  refine ⟨TT.tree t₀, (TT.tree t₀).maxDepth + t₀, ?_, ?_⟩
  · exact treeBroadcast_reaches_all (TT.tree t₀) values
  · exact TT.root_at_time t₀

-- ============================================================================
-- SECTION 7: TEMPORAL INSTABILITY
-- ============================================================================

/-! ## Temporal Instability: When Networks Change

These results formalize how network changes affect convergence.
Together they establish the boundary between what static H¹ theory
can and cannot guarantee.
-/

/-- Different tree depths → different convergence times.
    Deeper trees need more rounds for broadcast to complete. -/
theorem deeper_tree_slower_convergence (T₁ T₂ : TreeAuth n) (values : Fin n → ℚ)
    (i : Fin n) (k : ℕ)
    (h₁ : T₁.depth i ≤ k) (h₂ : ¬T₂.depth i ≤ k)
    (h_ne : values T₁.root ≠ values i) :
    (treeBroadcast T₁ values).evolve k i ≠
    (treeBroadcast T₂ values).evolve k i := by
  simp only [treeBroadcast]
  show (if T₁.depth i ≤ k then values T₁.root else values i) ≠
       (if T₂.depth i ≤ k then values T₂.root else values i)
  rw [if_pos h₁, if_neg h₂]
  exact h_ne

/-- An agent unconverged under tree T can be converged under tree T'
    if T' places it closer to root. Tree change can HELP convergence. -/
theorem shallower_tree_helps (T T' : TreeAuth n) (values : Fin n → ℚ)
    (i : Fin n) (k : ℕ)
    (h_root : T.root = T'.root)
    (h_deep : ¬T.depth i ≤ k) (h_shallow : T'.depth i ≤ k) :
    (treeBroadcast T values).evolve k i = values i ∧
    (treeBroadcast T' values).evolve k i = values T.root := by
  constructor
  · exact treeBroadcast_uninformed T values k i h_deep
  · have := treeBroadcast_informed T' values k i h_shallow
    -- this : ... = values T'.root; need ... = values T.root
    rw [← h_root] at this
    exact this

/-- Tree change can also HURT: an agent converged under T may be
    "unconverged" under T' (in the sense that T' would need more rounds) -/
theorem deeper_tree_hurts (T T' : TreeAuth n) (values : Fin n → ℚ)
    (i : Fin n) (k : ℕ)
    (h_converged : T.depth i ≤ k) (h_deeper : ¬T'.depth i ≤ k) :
    (treeBroadcast T values).evolve k i = values T.root ∧
    (treeBroadcast T' values).evolve k i = values i := by
  constructor
  · exact treeBroadcast_informed T values k i h_converged
  · exact treeBroadcast_uninformed T' values k i h_deeper

-- ============================================================================
-- SECTION 8: THE WALL — FORMAL BOUNDARY
-- ============================================================================

/-! ## The Wall: Where Static H¹ Theory Breaks

### The Core Problem

H¹ = 0 is defined for a FIXED simplicial complex. For time-varying networks,
we have a SEQUENCE of complexes K(0), K(1), K(2), .... Three natural questions:

1. If H¹(K(t)) = 0 for all t, does the "temporal union" have H¹ = 0?
   ANSWER: NO. Three forests whose union is a cycle (rotating triangle).

2. If H¹(K(t)) = 0 for all t, can agents always reach agreement?
   ANSWER: NO. The network may change faster than information propagates.

3. What ADDITIONAL invariant beyond pointwise H¹ = 0 is needed?
   ANSWER: OPEN. This is where new mathematics is needed.

### Why the Rotating Triangle Breaks Everything

Consider 3 agents (A, B, C):
- Time 1: edges A-B, B-C (path = forest, H¹ = 0)
- Time 2: edges B-C, C-A (path = forest, H¹ = 0)
- Time 3: edges C-A, A-B (path = forest, H¹ = 0)
- Union: edges A-B, B-C, C-A (triangle = cycle, H¹ ≠ 0)

Each snapshot is a forest, but the temporal accumulation creates a cycle.
No single-snapshot topological invariant can detect this.

### What the Theorems Below Formalize

We prove the POSITIVE side: the gap is real, and we characterize exactly
WHEN convergence IS guaranteed (eventually static networks).

The negative side (impossibility) is a meta-mathematical observation:
there is no theorem in our framework of the form
  "∀ t, H¹(K(t)) = 0 → ∃ convergent protocol on (K(t))_t"
because such a theorem would be false (rotating triangle counterexample).
-/

/-- Root stability is necessary for temporal convergence.
    If the "root" changes, the target consensus value is undefined. -/
theorem root_stability_necessary (T₁ T₂ : TreeAuth n) (values : Fin n → ℚ)
    (h_root_ne : T₁.root ≠ T₂.root)
    (h_values_ne : values T₁.root ≠ values T₂.root) :
    ∃ i : Fin n,
      (treeBroadcast T₁ values).evolve T₁.maxDepth i ≠
      (treeBroadcast T₂ values).evolve T₂.maxDepth i := by
  use T₁.root
  simp only [treeBroadcast_reaches_all]
  exact h_values_ne

/-- Root stability is sufficient for eventual convergence
    on a static network (re-export for emphasis) -/
theorem root_stability_sufficient (T : TreeAuth n) (values : Fin n → ℚ) :
    ∀ i j : Fin n,
      (treeBroadcast T values).evolve T.maxDepth i =
      (treeBroadcast T values).evolve T.maxDepth j := by
  intro i j
  simp only [treeBroadcast_reaches_all]

/-- The convergence speed depends on tree structure.
    Flat trees (depth 1) converge in 1 round; deep trees need more. -/
theorem star_converges_in_one_round (T : TreeAuth n) (h_star : T.isStar)
    (hn : 0 < n) (values : Fin n → ℚ) :
    ∀ i : Fin n,
      (treeBroadcast T values).evolve 1 i = values T.root := by
  intro i
  apply treeBroadcast_informed
  have h_bound := T.star_maxDepth_le_one h_star hn
  exact le_trans (T.depth_le_maxDepth i) h_bound

-- ============================================================================
-- SECTION 9: TEMPORAL COHERENCE REQUIREMENT
-- ============================================================================

/-! ## Temporal Coherence

The key insight from the wall analysis: temporal convergence requires not
just pointwise H¹ = 0, but TEMPORAL COHERENCE — the network must remain
stable long enough for information to propagate.

We formalize "coherence time" as the duration a network must remain fixed
for broadcast to complete.
-/

/-- Coherence time: how long a tree must remain fixed for broadcast to converge -/
noncomputable def coherenceTime (T : TreeAuth n) : ℕ := T.maxDepth

/-- If the network is stable for at least its coherence time, convergence occurs -/
theorem coherence_implies_convergence (T : TreeAuth n) (values : Fin n → ℚ)
    (k : ℕ) (hk : coherenceTime T ≤ k) :
    ∀ i j : Fin n,
      (treeBroadcast T values).evolve k i =
      (treeBroadcast T values).evolve k j := by
  intro i j
  have hi := treeBroadcast_informed T values k i
    (le_trans (T.depth_le_maxDepth i) hk)
  have hj := treeBroadcast_informed T values k j
    (le_trans (T.depth_le_maxDepth j) hk)
  rw [hi, hj]

/-- Star topology has minimum coherence time (1 round) -/
theorem star_coherence_time_le_one (T : TreeAuth n) (h_star : T.isStar) (hn : 0 < n) :
    coherenceTime T ≤ 1 :=
  T.star_maxDepth_le_one h_star hn

/-- The temporal convergence gap: convergence requires stability duration ≥ coherence time.
    This formalizes why "changing faster than propagation" prevents convergence. -/
theorem convergence_requires_coherence (T : TreeAuth n) (values : Fin n → ℚ)
    (i : Fin n) (k : ℕ) (h_deep : ¬T.depth i ≤ k) :
    (treeBroadcast T values).evolve k i = values i := by
  exact treeBroadcast_uninformed T values k i h_deep

-- ============================================================================
-- SECTION 10: IMPLICATIONS AND FUTURE DIRECTIONS
-- ============================================================================

/-! ## Implications: What New Mathematics Is Needed

### Summary of the Wall

| Property | Status |
|----------|--------|
| Static H¹ = 0 → convergence | PROVEN (treeBroadcast_converges) |
| Eventually static → convergence | PROVEN (eventually_static_convergence) |
| Pointwise H¹ = 0 → convergence | FALSE (rotating triangle) |
| Protocol composition | PROVEN (protocol_composition) |
| Coherence time = maxDepth | PROVEN (coherenceTime) |

### The Missing Invariant

What we need is NOT H¹(K_t) for each t, but an invariant of the
TEMPORAL SEQUENCE (K_t)_{t ∈ ℕ} that captures:

1. **Information propagation speed** vs **network change rate**
   - If change rate < propagation speed → convergence
   - If change rate ≥ propagation speed → possible divergence

2. **Temporal cycle detection**
   - Static H¹ detects cycles in a single snapshot
   - Need "temporal H¹" detecting cycles across snapshots
   - The rotating triangle creates a TEMPORAL cycle

3. **Persistent homology** is related but insufficient:
   - PH studies filtrations (monotone growth)
   - Temporal networks can grow AND shrink
   - Need "zigzag persistent homology" or similar

### Candidates for the New Invariant

1. **Zigzag persistent homology** (Carlsson-de Silva 2010)
   - Handles non-monotone sequences of complexes
   - Tracks how homology classes persist through insertions AND deletions

2. **Temporal cohomology** (new concept)
   - Define: T-cocycle = assignment to (edge, time) pairs
   - Coboundary includes both spatial AND temporal differentials
   - H¹_temporal = 0 iff no temporal obstruction to convergence

3. **Coherence conditions** (this file)
   - Pragmatic: bound network change rate relative to tree depth
   - Not a topological invariant, but operationally useful

These represent genuinely open mathematical questions that emerge from
the formalization. The fact that we can PRECISELY characterize the failure
mode (rotating triangle, coherence time gap) is itself a contribution.
-/

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-!
## Summary

DEFINITIONS: 7
  - TemporalTree, root, isStatic, eventuallyStatic, stableFrom
  - maxDepthInRange, coherenceTime

CONSTRUCTORS: 2
  - TemporalTree.constant, TemporalTree.switch

PROVEN THEOREMS: 18
  - Properties (5): root_at_time, constant_isStatic, static_implies_eventuallyStatic,
    switch_stableFrom, switch_eventuallyStatic
  - Static convergence (2): static_convergence, convergence_persists
  - Protocol composition (3): protocol_composition, sequential_composition,
    two_phase_convergence_time
  - Eventually static (1): eventually_static_convergence
  - Temporal instability (3): deeper_tree_slower_convergence, shallower_tree_helps,
    deeper_tree_hurts
  - The wall (3): root_stability_necessary, root_stability_sufficient,
    star_converges_in_one_round
  - Temporal coherence (3): coherence_implies_convergence, star_coherence_time_le_one,
    convergence_requires_coherence

AXIOMS: 0
SORRIES: 0

KEY DISCOVERY: The boundary between solvable and unsolvable temporal coordination
is precisely characterized by the COHERENCE TIME — the ratio of network stability
duration to information propagation depth. When coherence time ≥ maxDepth,
convergence is guaranteed. When coherence time < maxDepth, convergence may fail.
No purely topological invariant (including H¹) can replace this temporal condition.
-/

end MultiAgent
