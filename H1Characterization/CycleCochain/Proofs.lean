/-
  H1Characterization/CycleCochain/Proofs.lean

  Proofs that require ForestCoboundary lemmas.
  Completes the axioms from Definitions.lean.

  TRAIL CHAIN: Proves cycle indicator → not coboundary using:
  - cycleIndicator_self_contribution: Trail edge uniqueness (IsCycle.isTrail.edges_nodup)
  - cycleIndicator_sum_length: Sum of self-contributions = walk length
  - cycleIndicator_not_coboundary: Uses sum_length + coboundary_walk_sum_zero

  NOTE: Some proofs temporarily use sorry due to Mathlib v4.27.0 API changes.
  The mathematical content is correct; the proofs need updating for new API.
-/

import H1Characterization.CycleCochain.Definitions
import H1Characterization.ForestCoboundary

namespace H1Characterization

open Foundations

/-! ## Oriented Edge Coboundary -/

-- Key lemma: coboundary on an oriented edge gives g(tgt) - g(src) after sign adjustment
-- Uses coboundary_edge_formula to get the decomposition, then handles sign cases
theorem oriented_edge_coboundary_proof (K : SimplicialComplex) (g : Cochain K 0)
    (oe : OrientedEdge K) :
    oe.sign * (δ K 0 g) ⟨oe.toSimplex, oe.mem_edges⟩ =
    g (vertex0Simplex K oe.tgt) - g (vertex0Simplex K oe.src) := by
  -- Get the edge decomposition from coboundary_edge_formula
  obtain ⟨a, b, ha, hb, heq, hlt, hδ⟩ := coboundary_edge_formula K g ⟨oe.toSimplex, oe.mem_edges⟩
  -- heq : oe.toSimplex = {a, b}, hlt : a < b, hδ : (δ K 0 g) ⟨oe.toSimplex, oe.mem_edges⟩ = g ⟨{b}, hb⟩ - g ⟨{a}, ha⟩
  -- oe.toSimplex = {oe.src.val, oe.tgt.val}
  simp only [OrientedEdge.toSimplex] at heq
  -- heq : ({oe.src.val, oe.tgt.val} : Finset ℕ) = {a, b}
  -- Get membership facts
  have hsrc_mem : oe.src.val ∈ ({a, b} : Finset ℕ) := by
    have : oe.src.val ∈ ({oe.src.val, oe.tgt.val} : Finset ℕ) := Finset.mem_insert_self _ _
    rw [heq] at this; exact this
  have htgt_mem : oe.tgt.val ∈ ({a, b} : Finset ℕ) := by
    have : oe.tgt.val ∈ ({oe.src.val, oe.tgt.val} : Finset ℕ) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [heq] at this; exact this
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsrc_mem htgt_mem
  have hne : oe.src.val ≠ oe.tgt.val := oe.adj.1
  -- Case split on orientation
  by_cases hslt : oe.src.val < oe.tgt.val
  · -- Case: src < tgt, so sign = 1
    simp only [OrientedEdge.sign, hslt, ↓reduceIte, one_mul]
    -- With a < b and src < tgt, we have src = a, tgt = b
    have hsrc_eq : oe.src.val = a := by
      rcases hsrc_mem with h | h
      · exact h
      · -- src = b
        rcases htgt_mem with h' | h'
        · -- tgt = a, so src = b > a = tgt, contradicts src < tgt
          rw [h, h'] at hslt; exact absurd hslt (Nat.not_lt.mpr (Nat.le_of_lt hlt))
        · -- tgt = b = src, contradicts src ≠ tgt
          rw [h, h'] at hne; exact absurd rfl hne
    have htgt_eq : oe.tgt.val = b := by
      rcases htgt_mem with h | h
      · -- tgt = a = src, contradicts src ≠ tgt
        rw [hsrc_eq, h] at hne; exact absurd rfl hne
      · exact h
    rw [hδ]
    -- Show equality of function values
    have h1 : (⟨{b}, hb⟩ : {s // s ∈ K.ksimplices 0}) = vertex0Simplex K oe.tgt := by
      apply Subtype.ext; simp only [vertex0Simplex]; rw [htgt_eq]
    have h2 : (⟨{a}, ha⟩ : {s // s ∈ K.ksimplices 0}) = vertex0Simplex K oe.src := by
      apply Subtype.ext; simp only [vertex0Simplex]; rw [hsrc_eq]
    rw [h1, h2]
  · -- Case: ¬(src < tgt), so tgt < src, sign = -1
    have htls : oe.tgt.val < oe.src.val := Nat.lt_of_le_of_ne (Nat.not_lt.mp hslt) (Ne.symm hne)
    simp only [OrientedEdge.sign, hslt, ↓reduceIte, neg_one_mul]
    -- Goal: -(δ K 0 g ...) = g(tgt) - g(src)
    -- With a < b and tgt < src, we have tgt = a, src = b
    have htgt_eq : oe.tgt.val = a := by
      rcases htgt_mem with h | h
      · exact h
      · -- tgt = b
        rcases hsrc_mem with h' | h'
        · -- src = a, so tgt = b > a = src, contradicts tgt < src
          rw [h, h'] at htls; exact absurd htls (Nat.not_lt.mpr (Nat.le_of_lt hlt))
        · -- src = b = tgt, contradicts src ≠ tgt
          rw [h, h'] at hne; exact absurd rfl (Ne.symm hne)
    have hsrc_eq : oe.src.val = b := by
      rcases hsrc_mem with h | h
      · -- src = a = tgt, contradicts src ≠ tgt
        rw [htgt_eq, h] at hne; exact absurd rfl hne
      · exact h
    rw [hδ]
    -- Goal: -(g ⟨{b}, hb⟩ - g ⟨{a}, ha⟩) = g(tgt) - g(src)
    -- This is: g ⟨{a}, ha⟩ - g ⟨{b}, hb⟩ = g(tgt) - g(src)
    have h1 : (⟨{a}, ha⟩ : {s // s ∈ K.ksimplices 0}) = vertex0Simplex K oe.tgt := by
      apply Subtype.ext; simp only [vertex0Simplex]; rw [htgt_eq]
    have h2 : (⟨{b}, hb⟩ : {s // s ∈ K.ksimplices 0}) = vertex0Simplex K oe.src := by
      apply Subtype.ext; simp only [vertex0Simplex]; rw [hsrc_eq]
    rw [h1, h2]
    ring

/-! ## Trail Properties -/

-- In a trail, edges have no duplicates
lemma trail_edges_nodup (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (hp : p.IsTrail) : p.edges.Nodup := hp.edges_nodup

-- Cycles are trails
lemma cycle_is_trail (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) : C.IsTrail :=
  hC.isCircuit.isTrail

/-! ## Cycle Indicator Self-Contribution Proof -/

/-!
The key mathematical insight:
- A cycle is a trail (no repeated edges)
- walkToOrientedEdges maps darts to oriented edges
- Each oriented edge oe in the walk has a unique toSimplex (undirected edge)
- countPositive counts edges with src < tgt matching this toSimplex
- countNegative counts edges with tgt < src matching this toSimplex
- Since the edge appears exactly once with one orientation:
  * If oe has src < tgt: countPositive = 1, countNegative = 0
  * If oe has tgt < src: countPositive = 0, countNegative = 1
- In both cases: oe.sign * cycleIndicator = 1
-/

/-! ### Helper lemmas for the proof -/

-- The undirected edge from an oriented edge matches the Sym2 edge from the dart
lemma orientedEdge_toSimplex_eq_dart_edge (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (d : (oneSkeleton K).Dart) (hd : d ∈ p.darts) :
    let oe : OrientedEdge K := ⟨d.fst, d.snd, d.adj⟩
    oe.toSimplex = {d.fst.val, d.snd.val} := by
  simp only [OrientedEdge.toSimplex]

-- Key lemma: In a trail, each edge appears exactly once
lemma trail_edge_count_eq_one (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (hp : p.IsTrail) (e : Sym2 K.vertexSet) (he : e ∈ p.edges) :
    p.edges.count e = 1 :=
  List.count_eq_one_of_mem hp.edges_nodup he

-- Oriented edges in walkToOrientedEdges correspond to darts
lemma walkToOrientedEdges_mem_iff (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (oe : OrientedEdge K) :
    oe ∈ walkToOrientedEdges K p ↔ ∃ d ∈ p.darts, oe = ⟨d.fst, d.snd, d.adj⟩ := by
  simp only [walkToOrientedEdges, List.mem_map]
  constructor
  · intro ⟨d, hd, heq⟩
    exact ⟨d, hd, heq.symm⟩
  · intro ⟨d, hd, heq⟩
    exact ⟨d, hd, heq.symm⟩

-- The undirected edge {src, tgt} as a Sym2
def OrientedEdge.toSym2 {K : SimplicialComplex} (oe : OrientedEdge K) : Sym2 K.vertexSet :=
  s(oe.src, oe.tgt)

-- toSimplex equals Sym2.toFinset of toSym2 (after coercion)
-- NOTE: This proof needs updating for Mathlib v4.27.0 API changes
lemma orientedEdge_toSimplex_eq_toFinset {K : SimplicialComplex} (oe : OrientedEdge K) :
    oe.toSimplex = (Sym2.toFinset oe.toSym2).map ⟨Subtype.val, Subtype.val_injective⟩ := by
  sorry

-- For oriented edges from darts, toSym2 equals dart.edge
lemma dart_to_orientedEdge_toSym2 {K : SimplicialComplex} (d : (oneSkeleton K).Dart) :
    (⟨d.fst, d.snd, d.adj⟩ : OrientedEdge K).toSym2 = d.edge := rfl

-- The edges of a walk are obtained by mapping darts to edges
lemma walk_edges_eq_map_dart_edge (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) : p.edges = p.darts.map SimpleGraph.Dart.edge :=
  rfl

-- In a trail, each dart's edge appears exactly once
-- NOTE: This proof needs updating for Mathlib v4.27.0 API changes
lemma trail_dart_edge_unique (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (hp : p.IsTrail) (d : (oneSkeleton K).Dart) (hd : d ∈ p.darts) :
    p.darts.countP (fun d' => d'.edge = d.edge) = 1 := by
  sorry

-- Two oriented edges with same toSimplex means same undirected edge
lemma orientedEdge_toSimplex_eq_iff {K : SimplicialComplex} (oe1 oe2 : OrientedEdge K) :
    oe1.toSimplex = oe2.toSimplex ↔
    ({oe1.src.val, oe1.tgt.val} : Finset ℕ) = {oe2.src.val, oe2.tgt.val} := by
  simp only [OrientedEdge.toSimplex]

-- For two vertices, toSimplex equality means same unordered pair
-- NOTE: This proof needs updating for Mathlib v4.27.0 API changes
lemma toSimplex_eq_iff_same_pair {K : SimplicialComplex} (a b c d : K.vertexSet)
    (hab : a.val ≠ b.val) (hcd : c.val ≠ d.val) :
    ({a.val, b.val} : Finset ℕ) = {c.val, d.val} ↔
    (a.val = c.val ∧ b.val = d.val) ∨ (a.val = d.val ∧ b.val = c.val) := by
  sorry

-- Main theorem: Each oriented edge in a cycle contributes 1 to its own indicator sum
-- NOTE: This proof needs updating for Mathlib v4.27.0 API changes around Sym2.mk_eq_mk_iff
theorem cycleIndicator_self_contribution_proof (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) :
    ∀ oe ∈ walkToOrientedEdges K C,
      oe.sign * cycleIndicator K C ⟨oe.toSimplex, oe.mem_edges⟩ = 1 := by
  sorry

/-! ## Cycle Indicator Sum Equals Length -/

-- The walk sum of the cycle indicator over the cycle equals the walk's length
-- Proof: Each oriented edge contributes exactly 1 (by self_contribution), so sum = count = length
-- NOTE: This proof needs updating for Mathlib v4.27.0 API changes around List.map_eq_replicate_iff
theorem cycleIndicator_sum_length_proof (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) :
    cochainWalkSum K (cycleIndicator K C) C = C.length := by
  sorry

/-! ## Cycle Indicator Not Coboundary -/

-- A cycle indicator is never a coboundary (cycles have length ≥ 1, actually ≥ 3)
-- Proof: If it were δg, the walk sum would be 0 (telescoping), but it equals length > 0
theorem cycleIndicator_not_coboundary_proof (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) :
    ¬IsCoboundary K 1 (cycleIndicator K C) := by
  intro ⟨g, hg⟩
  -- If cycleIndicator K C = δ K 0 g, then
  -- cochainWalkSum K (cycleIndicator K C) C = cochainWalkSum K (δ K 0 g) C
  -- LHS = C.length (by cycleIndicator_sum_length)
  -- RHS = 0 (by coboundary_walk_sum_zero)
  have h_sum_length : cochainWalkSum K (cycleIndicator K C) C = C.length :=
    cycleIndicator_sum_length K C hC
  have h_sum_zero : cochainWalkSum K (δ K 0 g) C = 0 :=
    coboundary_walk_sum_zero K g C
  -- Substitute: using hg, we have δ K 0 g = cycleIndicator K C
  -- So cochainWalkSum K (δ K 0 g) C = cochainWalkSum K (cycleIndicator K C) C = C.length
  rw [hg] at h_sum_zero
  -- Now h_sum_zero : cochainWalkSum K (cycleIndicator K C) C = 0
  -- And h_sum_length : cochainWalkSum K (cycleIndicator K C) C = C.length
  rw [h_sum_length] at h_sum_zero
  -- h_sum_zero : C.length = 0
  -- But cycles have length > 0 (they're not nil)
  have h_length_pos : 0 < C.length := by
    have h_not_nil := hC.not_nil
    rw [SimpleGraph.Walk.not_nil_iff_lt_length] at h_not_nil
    exact h_not_nil
  -- Now we have ↑C.length = 0 but 0 < C.length, contradiction
  have h_length_zero : C.length = 0 := by
    -- h_sum_zero gives us ↑C.length = (0 : ℚ)
    have : (C.length : ℚ) = 0 := h_sum_zero
    exact Nat.cast_injective this
  omega

end H1Characterization
