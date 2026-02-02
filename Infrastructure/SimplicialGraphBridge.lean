/-
# Simplicial Complex ↔ SimpleGraph Bridge

Bridges between SimplicialComplex 1-simplices and SimpleGraph edges to enable
using ForestEulerFormula proofs for cohomology axiom elimination.

## Main Results

1. `ksimplex_one_gives_skeleton_edge` - 1-simplices give skeleton edges
2. `skeleton_edge_gives_ksimplex_one` - Skeleton edges give 1-simplices
3. `edge_count_eq_ksimplex_count` - Edge count equals 1-simplex count
4. `acyclic_implies_euler_proven` - G02: Forest implies Euler condition
5. `euler_implies_acyclic_proven` - G03: Euler condition implies forest

## Axioms Eliminated

- G02: acyclic_implies_euler (LinearComplexity.lean)
- G03: euler_implies_acyclic (LinearComplexity.lean)

SORRIES: 1
AXIOMS: 0

Author: Infrastructure Team
Date: February 2026
-/

import H1Characterization.OneSkeleton
import H1Characterization.OneConnected
import H1Characterization.ForestEulerFormula
import Foundations.Cohomology
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace Infrastructure.SimplicialGraphBridge

open Foundations (SimplicialComplex Simplex Vertex Cochain IsCocycle IsCoboundary H1Trivial)
open H1Characterization (oneSkeleton OneConnected oneSkeleton_adj_iff)

variable {K : SimplicialComplex}

/-! ## Section 1: 1-Simplex and Edge Correspondence -/

/-- A 1-simplex (edge in simplicial complex) gives an edge in the 1-skeleton -/
theorem ksimplex_one_gives_skeleton_edge [Fintype K.vertexSet]
    (e : K.ksimplices 1) :
    ∃ (v w : K.vertexSet), v ≠ w ∧ (oneSkeleton K).Adj v w ∧
      e.val = ({v.val, w.val} : Finset Vertex) := by
  obtain ⟨s, hs_mem, hs_card⟩ := e
  obtain ⟨a, b, hab, hs_eq⟩ := Finset.card_eq_two.mp hs_card
  have ha_in_s : a ∈ s := by rw [hs_eq]; exact Finset.mem_insert_self a {b}
  have hb_in_s : b ∈ s := by rw [hs_eq]; simp
  have ha_vert := Foundations.SimplicialComplex.vertex_of_mem_simplex K s hs_mem a ha_in_s
  have hb_vert := Foundations.SimplicialComplex.vertex_of_mem_simplex K s hs_mem b hb_in_s
  use ⟨a, ha_vert⟩, ⟨b, hb_vert⟩
  refine ⟨?_, ?_, hs_eq⟩
  · simp only [ne_eq, Subtype.mk.injEq]; exact hab
  · rw [oneSkeleton_adj_iff]
    exact ⟨hab, by rw [← hs_eq]; exact hs_mem⟩

/-- An edge in the 1-skeleton gives a 1-simplex -/
theorem skeleton_edge_gives_ksimplex_one [Fintype K.vertexSet]
    (v w : K.vertexSet) (hadj : (oneSkeleton K).Adj v w) :
    ({v.val, w.val} : Finset Vertex) ∈ K.ksimplices 1 := by
  rw [oneSkeleton_adj_iff] at hadj
  exact ⟨hadj.2, Finset.card_pair hadj.1⟩

/-- The 1-simplices correspond exactly to edges of the 1-skeleton -/
theorem edge_mem_ksimplices_iff [Fintype K.vertexSet]
    (v w : K.vertexSet) (hne : v ≠ w) :
    ({v.val, w.val} : Finset Vertex) ∈ K.ksimplices 1 ↔
    (oneSkeleton K).Adj v w := by
  constructor
  · intro ⟨hmem, _⟩
    rw [oneSkeleton_adj_iff]
    exact ⟨fun h => hne (Subtype.ext h), hmem⟩
  · exact skeleton_edge_gives_ksimplex_one v w

/-! ## Section 2: Counting Arguments -/

/-- A 2-element finset can be written as {min', max'} -/
private lemma finset_two_eq_minmax (s : Finset Vertex) (hs : s.card = 2) :
    s = {s.min' (Finset.card_pos.mp (by omega)), s.max' (Finset.card_pos.mp (by omega))} := by
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hab : s.min' hne ≠ s.max' hne := by
    intro h
    have hcard_le : s.card ≤ 1 := by
      rw [← Finset.card_singleton (s.min' hne)]; apply Finset.card_le_card
      intro x hx; simp only [Finset.mem_singleton]
      have hle := Finset.min'_le s x hx
      have hge := Finset.le_max' s x hx
      have hge' : x ≤ s.min' hne := h ▸ hge
      exact le_antisymm hge' hle
    omega
  obtain ⟨x, y, _, hs_xy⟩ := Finset.card_eq_two.mp hs
  have ha_mem : s.min' hne ∈ ({x, y} : Finset Vertex) := hs_xy ▸ Finset.min'_mem s hne
  have hb_mem : s.max' hne ∈ ({x, y} : Finset Vertex) := hs_xy ▸ Finset.max'_mem s hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem hb_mem
  rcases ha_mem with ha_x | ha_y <;> rcases hb_mem with hb_x | hb_y
  · rw [ha_x, hb_x] at hab; exact absurd rfl hab
  · calc s = {x, y} := hs_xy
      _ = {s.min' hne, s.max' hne} := by rw [ha_x, hb_y]
  · calc s = {x, y} := hs_xy
      _ = {y, x} := Finset.pair_comm x y
      _ = {s.min' hne, s.max' hne} := by rw [ha_y, hb_x]
  · rw [ha_y, hb_y] at hab; exact absurd rfl hab

/-- Edge count in 1-skeleton equals 1-simplex count.

    Each 1-simplex {v,w} corresponds to exactly one edge s(v,w) in the 1-skeleton.
    The bijection follows directly from `ksimplex_one_gives_skeleton_edge` and
    `skeleton_edge_gives_ksimplex_one`. -/
theorem edge_count_eq_ksimplex_count [Fintype K.vertexSet]
    [DecidableEq K.vertexSet] [DecidableRel (oneSkeleton K).Adj]
    [Fintype (K.ksimplices 1)] [Fintype (oneSkeleton K).edgeSet] :
    (oneSkeleton K).edgeFinset.card = Fintype.card (K.ksimplices 1) := by
  rw [SimpleGraph.edgeFinset_card]
  apply Nat.le_antisymm
  -- Direction 1: |edgeSet| ≤ |ksimplices 1|
  · -- Use Sym2.lift to map edges to finsets
    let toFinset : Sym2 K.vertexSet → Finset Vertex :=
      Sym2.lift ⟨fun v w => ({v.val, w.val} : Finset Vertex), fun _ _ => Finset.pair_comm _ _⟩
    apply Fintype.card_le_of_injective
      (fun ⟨e, he⟩ => ⟨toFinset e, by
        -- Use Sym2.ind to eliminate into Prop
        refine Sym2.ind (fun v w hmem => ?_) e he
        show ({v.val, w.val} : Finset Vertex) ∈ K.ksimplices 1
        exact skeleton_edge_gives_ksimplex_one v w (hmem)⟩)
    intro ⟨e1, he1⟩ ⟨e2, he2⟩ hfeq
    simp only [Subtype.mk.injEq] at hfeq ⊢
    -- Both edges map to the same finset, show they are equal
    revert hfeq he1 he2
    refine Sym2.ind (fun v1 w1 => ?_) e1
    refine Sym2.ind (fun v2 w2 => ?_) e2
    intro hmem1 hmem2 hfeq
    show s(v1, w1) = s(v2, w2)
    change ({v1.val, w1.val} : Finset Vertex) = {v2.val, w2.val} at hfeq
    simp only [SimpleGraph.mem_edgeSet] at hmem1 hmem2
    rw [oneSkeleton_adj_iff] at hmem1 hmem2
    have hne1 : v1.val ≠ w1.val := fun h => hmem1.1 h
    have hne2 : v2.val ≠ w2.val := fun h => hmem2.1 h
    -- {v1.val, w1.val} = {v2.val, w2.val} with both pairs distinct
    have hcard : ({v1.val, w1.val} : Finset Vertex).card = 2 := Finset.card_pair hne1
    obtain ⟨a, b, hab, hset1⟩ := Finset.card_eq_two.mp hcard
    have hset2 : ({v2.val, w2.val} : Finset Vertex) = {a, b} := by rw [← hfeq, hset1]
    have h1a : v1.val ∈ ({a, b} : Finset Vertex) := by rw [← hset1]; simp
    have h1b : w1.val ∈ ({a, b} : Finset Vertex) := by rw [← hset1]; simp
    have h2a : v2.val ∈ ({a, b} : Finset Vertex) := by rw [← hset2]; simp
    have h2b : w2.val ∈ ({a, b} : Finset Vertex) := by rw [← hset2]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1a h1b h2a h2b
    have ha_vert : a ∈ K.vertexSet :=
      Foundations.SimplicialComplex.vertex_of_mem_simplex K _ hmem1.2 a (by rw [hset1]; simp)
    have hb_vert : b ∈ K.vertexSet :=
      Foundations.SimplicialComplex.vertex_of_mem_simplex K _ hmem1.2 b (by rw [hset1]; simp)
    have he1_eq : s(v1, w1) = s(⟨a, ha_vert⟩, ⟨b, hb_vert⟩) := by
      rw [Sym2.eq_iff]
      rcases h1a with h1a' | h1a' <;> rcases h1b with h1b' | h1b'
      · exfalso; exact hne1 (h1a'.trans h1b'.symm)
      · left; exact ⟨Subtype.ext h1a', Subtype.ext h1b'⟩
      · right; exact ⟨Subtype.ext h1a', Subtype.ext h1b'⟩
      · exfalso; exact hne1 (h1a'.trans h1b'.symm)
    have he2_eq : s(v2, w2) = s(⟨a, ha_vert⟩, ⟨b, hb_vert⟩) := by
      rw [Sym2.eq_iff]
      rcases h2a with h2a' | h2a' <;> rcases h2b with h2b' | h2b'
      · exfalso; exact hne2 (h2a'.trans h2b'.symm)
      · left; exact ⟨Subtype.ext h2a', Subtype.ext h2b'⟩
      · right; exact ⟨Subtype.ext h2a', Subtype.ext h2b'⟩
      · exfalso; exact hne2 (h2a'.trans h2b'.symm)
    rw [he1_eq, he2_eq]
  -- Direction 2: |ksimplices 1| ≤ |edgeSet|
  · apply Fintype.card_le_of_injective
      (fun ⟨s, hs_mem, hs_card⟩ =>
        have hne : s.Nonempty := Finset.card_pos.mp (by omega)
        have hab : s.min' hne ≠ s.max' hne := by
          intro heq
          have hcard_le : s.card ≤ 1 := by
            rw [← Finset.card_singleton (s.min' hne)]; apply Finset.card_le_card
            intro x hx; simp only [Finset.mem_singleton]
            have hle := Finset.min'_le s x hx
            have hge := Finset.le_max' s x hx
            have hge' : x ≤ s.min' hne := heq ▸ hge
            exact le_antisymm hge' hle
          omega
        have ha_vert := Foundations.SimplicialComplex.vertex_of_mem_simplex K s hs_mem
          (s.min' hne) (Finset.min'_mem s hne)
        have hb_vert := Foundations.SimplicialComplex.vertex_of_mem_simplex K s hs_mem
          (s.max' hne) (Finset.max'_mem s hne)
        have hs_eq := finset_two_eq_minmax s hs_card
        ⟨Sym2.mk (⟨s.min' hne, ha_vert⟩, ⟨s.max' hne, hb_vert⟩), by
          rw [SimpleGraph.mem_edgeSet, oneSkeleton_adj_iff]
          exact ⟨hab, hs_eq ▸ hs_mem⟩⟩)
    intro ⟨s1, hs1_mem, hs1_card⟩ ⟨s2, hs2_mem, hs2_card⟩ hgeq
    simp only [Subtype.mk.injEq] at hgeq ⊢
    have hne1 : s1.Nonempty := Finset.card_pos.mp (by omega)
    have hne2 : s2.Nonempty := Finset.card_pos.mp (by omega)
    have hfinset_eq : ({s1.min' hne1, s1.max' hne1} : Finset Vertex) =
                      ({s2.min' hne2, s2.max' hne2} : Finset Vertex) := by
      have h := congrArg (Sym2.lift ⟨fun (v w : K.vertexSet) => ({v.val, w.val} : Finset Vertex),
        fun _ _ => Finset.pair_comm _ _⟩) hgeq
      simp only [Sym2.lift_mk] at h
      exact h
    have hs1_eq := finset_two_eq_minmax s1 hs1_card
    have hs2_eq := finset_two_eq_minmax s2 hs2_card
    rw [hs1_eq, hs2_eq, hfinset_eq]

/-! ## Section 3: Euler Formula Bridge

We use the proven theorems from ForestEulerFormula.lean:
- `SimpleGraph.acyclic_euler_eq` : acyclic → |E| + |C| = |V|
- `SimpleGraph.euler_eq_implies_acyclic` : |E| + |C| = |V| → acyclic
-/

/-- For a forest (acyclic graph), |E| + |C| = |V| -/
theorem forest_euler_equality [Fintype K.vertexSet] [DecidableEq K.vertexSet]
    [DecidableRel (oneSkeleton K).Adj] [Fintype (oneSkeleton K).edgeSet]
    [Fintype (oneSkeleton K).ConnectedComponent] [Nonempty K.vertexSet]
    (h_acyc : (oneSkeleton K).IsAcyclic) :
    (oneSkeleton K).edgeFinset.card + Fintype.card (oneSkeleton K).ConnectedComponent
    = Fintype.card K.vertexSet :=
  SimpleGraph.acyclic_euler_eq (oneSkeleton K) h_acyc

/-- For a forest (acyclic graph), edges ≤ vertices - components -/
theorem forest_euler_inequality [Fintype K.vertexSet] [DecidableEq K.vertexSet]
    [DecidableRel (oneSkeleton K).Adj] [Fintype (oneSkeleton K).edgeSet]
    [Fintype (oneSkeleton K).ConnectedComponent] [Nonempty K.vertexSet]
    (h_acyc : (oneSkeleton K).IsAcyclic) :
    (oneSkeleton K).edgeFinset.card ≤
    Fintype.card K.vertexSet - Fintype.card (oneSkeleton K).ConnectedComponent := by
  have h_eq := forest_euler_equality h_acyc
  omega

/-- G02: OneConnected (acyclic 1-skeleton) implies Euler forest condition -/
theorem acyclic_implies_euler_proven [Fintype K.vertexSet] [DecidableEq K.vertexSet]
    [DecidableRel (oneSkeleton K).Adj] [Fintype (K.ksimplices 1)]
    [Fintype (oneSkeleton K).edgeSet] [Fintype (oneSkeleton K).ConnectedComponent]
    [Nonempty K.vertexSet]
    (h : OneConnected K) :
    Fintype.card (K.ksimplices 1) ≤
    Fintype.card K.vertexSet - Fintype.card (oneSkeleton K).ConnectedComponent := by
  have h_acyc : (oneSkeleton K).IsAcyclic := h
  have h_eq := @edge_count_eq_ksimplex_count K _ _ _ _ _
  rw [← h_eq]
  exact forest_euler_inequality h_acyc

/-- G03: Euler condition implies OneConnected (acyclic 1-skeleton) -/
theorem euler_implies_acyclic_proven [Fintype K.vertexSet] [DecidableEq K.vertexSet]
    [DecidableRel (oneSkeleton K).Adj] [Fintype (K.ksimplices 1)]
    [Fintype (oneSkeleton K).edgeSet] [Fintype (oneSkeleton K).ConnectedComponent]
    [Nonempty K.vertexSet]
    (h : Fintype.card (K.ksimplices 1) ≤
         Fintype.card K.vertexSet - Fintype.card (oneSkeleton K).ConnectedComponent) :
    OneConnected K := by
  have h_eq := @edge_count_eq_ksimplex_count K _ _ _ _ _
  -- Convert ksimplices bound to edgeFinset bound
  have h' : (oneSkeleton K).edgeFinset.card ≤
      Fintype.card K.vertexSet - Fintype.card (oneSkeleton K).ConnectedComponent := by
    rw [h_eq]; exact h
  -- Use ForestEulerFormula's euler_eq_implies_acyclic
  -- The condition |E| ≤ |V| - |C| combined with |E| + |C| ≥ |V| gives |E| + |C| = |V|
  have h_ge := SimpleGraph.edges_plus_components_ge_vertices (oneSkeleton K)
  -- h_ge : E + C ≥ V
  -- h' : E ≤ V - C, which means E + C ≤ V (when C ≤ V)
  have h_euler : (oneSkeleton K).edgeFinset.card +
      Fintype.card (oneSkeleton K).ConnectedComponent = Fintype.card K.vertexSet := by
    -- From h' : E ≤ V - C and h_ge : E + C ≥ V
    -- We need E + C = V
    have hCV : Fintype.card (oneSkeleton K).ConnectedComponent ≤ Fintype.card K.vertexSet := by
      -- Every vertex has a connected component, so |C| ≤ |V|
      have : Function.Surjective (oneSkeleton K).connectedComponentMk := fun c =>
        ⟨c.exists_rep.choose, c.exists_rep.choose_spec⟩
      exact Fintype.card_le_of_surjective _ this
    -- Now E ≤ V - C implies E + C ≤ V (since C ≤ V means V - C + C = V)
    have h_le : (oneSkeleton K).edgeFinset.card + Fintype.card (oneSkeleton K).ConnectedComponent
        ≤ Fintype.card K.vertexSet := by
      calc (oneSkeleton K).edgeFinset.card + Fintype.card (oneSkeleton K).ConnectedComponent
          ≤ (Fintype.card K.vertexSet - Fintype.card (oneSkeleton K).ConnectedComponent)
            + Fintype.card (oneSkeleton K).ConnectedComponent := Nat.add_le_add_right h' _
        _ = Fintype.card K.vertexSet := Nat.sub_add_cancel hCV
    omega
  exact SimpleGraph.euler_eq_implies_acyclic (oneSkeleton K) h_euler

/-! ## Section 4: Summary -/

#check ksimplex_one_gives_skeleton_edge
#check skeleton_edge_gives_ksimplex_one
#check edge_mem_ksimplices_iff
#check edge_count_eq_ksimplex_count
#check acyclic_implies_euler_proven
#check euler_implies_acyclic_proven

end Infrastructure.SimplicialGraphBridge
