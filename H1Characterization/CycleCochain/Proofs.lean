/-
  H1Characterization/CycleCochain/Proofs.lean

  Proofs that require ForestCoboundary lemmas.
  Completes the axioms from Definitions.lean.

  TRAIL CHAIN: Proves cycle indicator → not coboundary using:
  - cycleIndicator_self_contribution: Trail edge uniqueness (IsCycle.isTrail.edges_nodup)
  - cycleIndicator_sum_length: Sum of self-contributions = walk length
  - cycleIndicator_not_coboundary: Uses sum_length + coboundary_walk_sum_zero
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
    (oe.toSimplex : Finset ℕ) = (Sym2.toFinset d.edge : Finset ℕ) := by
  simp only [OrientedEdge.toSimplex, SimpleGraph.Dart.edge, Sym2.toFinset_mk]
  rfl

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
def OrientedEdge.toSym2 (oe : OrientedEdge K) : Sym2 K.vertexSet :=
  s(oe.src, oe.tgt)

-- toSimplex equals Sym2.toFinset of toSym2 (after coercion)
lemma orientedEdge_toSimplex_eq_toFinset (oe : OrientedEdge K) :
    (oe.toSimplex : Finset ℕ) = (Sym2.toFinset (oe.toSym2)).map (↑) := by
  simp only [OrientedEdge.toSimplex, OrientedEdge.toSym2, Sym2.toFinset_mk]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro h
    rcases h with rfl | rfl
    · exact ⟨oe.src, Or.inl rfl, rfl⟩
    · exact ⟨oe.tgt, Or.inr rfl, rfl⟩
  · intro ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl <;> simp

-- For oriented edges from darts, toSym2 equals dart.edge
lemma dart_to_orientedEdge_toSym2 (d : (oneSkeleton K).Dart) :
    (⟨d.fst, d.snd, d.adj⟩ : OrientedEdge K).toSym2 = d.edge := by
  simp only [OrientedEdge.toSym2, SimpleGraph.Dart.edge, Sym2.mk_eq_mk]
  left; rfl

-- The edges of a walk are obtained by mapping darts to edges
lemma walk_edges_eq_map_dart_edge (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) : p.edges = p.darts.map SimpleGraph.Dart.edge :=
  rfl

-- In a trail, each dart's edge appears exactly once
lemma trail_dart_edge_unique (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (hp : p.IsTrail) (d : (oneSkeleton K).Dart) (hd : d ∈ p.darts) :
    p.darts.countP (fun d' => d'.edge = d.edge) = 1 := by
  -- Since edges.Nodup and edges = darts.map edge, and d.edge ∈ edges
  have he : d.edge ∈ p.edges := List.mem_map_of_mem _ hd
  have hcount : p.edges.count d.edge = 1 := trail_edge_count_eq_one K p hp d.edge he
  -- count in edges equals countP in darts for matching edges
  have : p.edges.count d.edge = p.darts.countP (fun d' => d'.edge = d.edge) := by
    rw [walk_edges_eq_map_dart_edge]
    rw [List.count_map]
  rw [this] at hcount
  exact hcount

-- Two oriented edges with same toSimplex means same undirected edge
lemma orientedEdge_toSimplex_eq_iff (oe1 oe2 : OrientedEdge K) :
    oe1.toSimplex = oe2.toSimplex ↔
    ({oe1.src.val, oe1.tgt.val} : Finset ℕ) = {oe2.src.val, oe2.tgt.val} := by
  simp only [OrientedEdge.toSimplex]

-- For two vertices, toSimplex equality means same unordered pair
lemma toSimplex_eq_iff_same_pair (a b c d : K.vertexSet) (hab : a.val ≠ b.val) (hcd : c.val ≠ d.val) :
    ({a.val, b.val} : Finset ℕ) = {c.val, d.val} ↔
    (a.val = c.val ∧ b.val = d.val) ∨ (a.val = d.val ∧ b.val = c.val) := by
  constructor
  · intro heq
    have ha : a.val ∈ ({c.val, d.val} : Finset ℕ) := by
      rw [← heq]; exact Finset.mem_insert_self _ _
    have hb : b.val ∈ ({c.val, d.val} : Finset ℕ) := by
      rw [← heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl
    · rcases hb with h | h
      · exact absurd h.symm hab
      · left; exact ⟨rfl, h⟩
    · rcases hb with h | h
      · right; exact ⟨rfl, h⟩
      · exact absurd h.symm hab
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Finset.pair_comm _ _

-- Main theorem: Each oriented edge in a cycle contributes 1 to its own indicator sum
theorem cycleIndicator_self_contribution_proof (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) :
    ∀ oe ∈ walkToOrientedEdges K C,
      oe.sign * cycleIndicator K C ⟨oe.toSimplex, oe.mem_edges⟩ = 1 := by
  intro oe hoe
  -- oe comes from some dart d in C.darts
  rw [walkToOrientedEdges_mem_iff] at hoe
  obtain ⟨d, hd, rfl⟩ := hoe
  -- Let's call this oriented edge oe_d for clarity
  set oe_d : OrientedEdge K := ⟨d.fst, d.snd, d.adj⟩ with hoe_d
  -- C is a trail, so each undirected edge appears exactly once
  have htrail : C.IsTrail := hC.isCircuit.isTrail
  -- The edge d.edge appears exactly once in C.edges
  have hedge_unique : C.darts.countP (fun d' => d'.edge = d.edge) = 1 :=
    trail_dart_edge_unique K C htrail d hd
  -- We need to show: oe_d.sign * cycleIndicator K C ⟨oe_d.toSimplex, oe_d.mem_edges⟩ = 1
  -- cycleIndicator = countPositive - countNegative
  simp only [cycleIndicator]
  -- Case split on whether src < tgt
  by_cases hslt : d.fst.val < d.snd.val
  · -- Case: src < tgt, so sign = 1
    have hsign : oe_d.sign = 1 := by simp only [OrientedEdge.sign, hslt, ↓reduceIte]
    rw [hsign, one_mul]
    -- Need to show: countPositive = 1, countNegative = 0
    -- So cycleIndicator = 1 - 0 = 1
    have hpos : countPositive K C ⟨oe_d.toSimplex, oe_d.mem_edges⟩ = 1 := by
      simp only [countPositive, walkToOrientedEdges]
      -- Count edges with matching toSimplex and src < tgt
      -- The only such edge is oe_d itself (since edges are unique in a trail)
      rw [List.countP_map]
      -- We need: countP (fun d' => (oe from d').toSimplex = oe_d.toSimplex ∧ d'.fst.val < d'.snd.val) = 1
      -- This equals the number of darts with the same undirected edge and positive orientation
      -- Since the trail has each edge once, and d has src < tgt, count = 1
      have : C.darts.countP (fun d' => (⟨d'.fst, d'.snd, d'.adj⟩ : OrientedEdge K).toSimplex =
             oe_d.toSimplex ∧ d'.fst.val < d'.snd.val) =
             C.darts.countP (fun d' => d'.edge = d.edge ∧ d'.fst.val < d'.snd.val) := by
        apply List.countP_congr
        intro d' _
        constructor
        · intro ⟨heq, hlt⟩
          constructor
          · -- toSimplex equality implies edge equality
            simp only [OrientedEdge.toSimplex] at heq
            simp only [SimpleGraph.Dart.edge, Sym2.mk_eq_mk]
            have hne : d'.fst.val ≠ d'.snd.val := d'.adj.1
            have hne' : d.fst.val ≠ d.snd.val := d.adj.1
            rw [toSimplex_eq_iff_same_pair _ _ _ _ hne hne'] at heq
            rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · left
              ext <;> [exact Subtype.ext h1; exact Subtype.ext h2]
            · right
              ext <;> [exact Subtype.ext h1; exact Subtype.ext h2]
          · exact hlt
        · intro ⟨heq, hlt⟩
          constructor
          · -- edge equality implies toSimplex equality
            simp only [OrientedEdge.toSimplex]
            simp only [SimpleGraph.Dart.edge, Sym2.mk_eq_mk] at heq
            rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · simp only [h1, h2]
            · rw [Finset.pair_comm]; simp only [h1, h2]
          · exact hlt
      rw [this]
      -- Now count darts with d'.edge = d.edge ∧ d'.fst < d'.snd
      -- Since trail has unique edges, and d is the only dart with d.edge, count = 1 if d.fst < d.snd
      -- We have hslt : d.fst.val < d.snd.val
      have hcount_split : C.darts.countP (fun d' => d'.edge = d.edge ∧ d'.fst.val < d'.snd.val) +
                          C.darts.countP (fun d' => d'.edge = d.edge ∧ d'.snd.val < d'.fst.val) =
                          C.darts.countP (fun d' => d'.edge = d.edge) := by
        rw [← List.countP_add_countP_compl (fun d' => d'.fst.val < d'.snd.val)
            (C.darts.filter (fun d' => d'.edge = d.edge))]
        simp only [List.countP_filter]
        congr 1
        · apply List.countP_congr; intro d' _; simp [and_comm]
        · apply List.countP_congr
          intro d' _
          simp only [Bool.not_eq_true, decide_eq_false_iff_not, not_lt]
          constructor
          · intro ⟨heq, hle⟩
            constructor
            · exact heq
            · have hne : d'.fst.val ≠ d'.snd.val := d'.adj.1
              exact Nat.lt_of_le_of_ne hle (Ne.symm hne)
          · intro ⟨heq, hlt⟩
            exact ⟨heq, Nat.le_of_lt hlt⟩
      rw [hedge_unique] at hcount_split
      -- The negative count must be 0 since d has src < tgt and is unique
      have hneg_zero : C.darts.countP (fun d' => d'.edge = d.edge ∧ d'.snd.val < d'.fst.val) = 0 := by
        apply List.countP_eq_zero.mpr
        intro d' hd'
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
        intro heq
        -- d'.edge = d.edge and d' ∈ C.darts
        -- Since trail has unique edges, d' = d or d' = d.symm
        -- But d.symm is not in C.darts (simple graph, darts are oriented)
        -- Actually, in a trail edges are unique, so if d'.edge = d.edge then d' = d
        have : C.darts.countP (fun d'' => d''.edge = d.edge) = 1 := hedge_unique
        -- d and d' both satisfy the predicate
        have hd_sat : d.edge = d.edge := rfl
        have hd'_sat : d'.edge = d.edge := heq
        -- If d ≠ d' then count ≥ 2, contradiction
        by_contra hlt
        have hne_sym : d' ≠ d := by
          intro heq'
          rw [heq'] at hlt
          exact (Nat.lt_irrefl _) (Nat.lt_of_lt_of_le hlt (Nat.le_of_lt hslt))
        -- d'.edge = d.edge means {d'.fst, d'.snd} = {d.fst, d.snd}
        -- With d'.snd < d'.fst and d.fst < d.snd, we must have d'.fst = d.snd and d'.snd = d.fst
        simp only [SimpleGraph.Dart.edge, Sym2.mk_eq_mk] at heq
        rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · -- d'.fst = d.fst, d'.snd = d.snd
          have : d' = d := SimpleGraph.Dart.ext _ _ (Prod.ext h1 h2)
          exact hne_sym this
        · -- d'.fst = d.snd, d'.snd = d.fst
          -- Then d'.snd.val = d.fst.val < d.snd.val = d'.fst.val
          have : d'.snd.val < d'.fst.val := by
            calc d'.snd.val = d.fst.val := congrArg Subtype.val h2
            _ < d.snd.val := hslt
            _ = d'.fst.val := (congrArg Subtype.val h1).symm
          exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le this (Nat.le_of_lt hlt))
      omega
    have hneg : countNegative K C ⟨oe_d.toSimplex, oe_d.mem_edges⟩ = 0 := by
      simp only [countNegative, walkToOrientedEdges]
      rw [List.countP_map]
      have : C.darts.countP (fun d' => (⟨d'.fst, d'.snd, d'.adj⟩ : OrientedEdge K).toSimplex =
             oe_d.toSimplex ∧ d'.snd.val < d'.fst.val) =
             C.darts.countP (fun d' => d'.edge = d.edge ∧ d'.snd.val < d'.fst.val) := by
        apply List.countP_congr
        intro d' _
        constructor
        · intro ⟨heq, hlt⟩
          constructor
          · simp only [OrientedEdge.toSimplex] at heq
            simp only [SimpleGraph.Dart.edge, Sym2.mk_eq_mk]
            have hne : d'.fst.val ≠ d'.snd.val := d'.adj.1
            have hne' : d.fst.val ≠ d.snd.val := d.adj.1
            rw [toSimplex_eq_iff_same_pair _ _ _ _ hne hne'] at heq
            rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · left; ext <;> [exact Subtype.ext h1; exact Subtype.ext h2]
            · right; ext <;> [exact Subtype.ext h1; exact Subtype.ext h2]
          · exact hlt
        · intro ⟨heq, hlt⟩
          constructor
          · simp only [OrientedEdge.toSimplex]
            simp only [SimpleGraph.Dart.edge, Sym2.mk_eq_mk] at heq
            rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · simp only [h1, h2]
            · rw [Finset.pair_comm]; simp only [h1, h2]
          · exact hlt
      rw [this]
      apply List.countP_eq_zero.mpr
      intro d' hd'
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
      intro heq
      simp only [SimpleGraph.Dart.edge, Sym2.mk_eq_mk] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- d' = d
        have : d' = d := SimpleGraph.Dart.ext _ _ (Prod.ext h1 h2)
        rw [this]
        exact Nat.le_of_lt hslt
      · -- d'.fst = d.snd, d'.snd = d.fst
        -- d'.snd.val = d.fst.val < d.snd.val = d'.fst.val
        have hlt' : d'.snd.val < d'.fst.val := by
          calc d'.snd.val = d.fst.val := congrArg Subtype.val h2
          _ < d.snd.val := hslt
          _ = d'.fst.val := (congrArg Subtype.val h1).symm
        exact Nat.le_of_lt hlt'
    simp only [hpos, hneg, Nat.cast_one, Nat.cast_zero, sub_zero]

  · -- Case: ¬(src < tgt), so tgt < src, sign = -1
    have hne : d.fst.val ≠ d.snd.val := d.adj.1
    have htls : d.snd.val < d.fst.val := Nat.lt_of_le_of_ne (Nat.not_lt.mp hslt) (Ne.symm hne)
    have hsign : oe_d.sign = -1 := by simp only [OrientedEdge.sign, hslt, ↓reduceIte]
    rw [hsign]
    -- Need to show: (-1) * (countPositive - countNegative) = 1
    -- i.e., countNegative - countPositive = 1
    -- i.e., countPositive = 0, countNegative = 1
    have hpos : countPositive K C ⟨oe_d.toSimplex, oe_d.mem_edges⟩ = 0 := by
      simp only [countPositive, walkToOrientedEdges]
      rw [List.countP_map]
      have : C.darts.countP (fun d' => (⟨d'.fst, d'.snd, d'.adj⟩ : OrientedEdge K).toSimplex =
             oe_d.toSimplex ∧ d'.fst.val < d'.snd.val) =
             C.darts.countP (fun d' => d'.edge = d.edge ∧ d'.fst.val < d'.snd.val) := by
        apply List.countP_congr
        intro d' _
        constructor
        · intro ⟨heq, hlt⟩
          constructor
          · simp only [OrientedEdge.toSimplex] at heq
            simp only [SimpleGraph.Dart.edge, Sym2.mk_eq_mk]
            have hne' : d'.fst.val ≠ d'.snd.val := d'.adj.1
            rw [toSimplex_eq_iff_same_pair _ _ _ _ hne' hne] at heq
            rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · left; ext <;> [exact Subtype.ext h1; exact Subtype.ext h2]
            · right; ext <;> [exact Subtype.ext h1; exact Subtype.ext h2]
          · exact hlt
        · intro ⟨heq, hlt⟩
          constructor
          · simp only [OrientedEdge.toSimplex]
            simp only [SimpleGraph.Dart.edge, Sym2.mk_eq_mk] at heq
            rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · simp only [h1, h2]
            · rw [Finset.pair_comm]; simp only [h1, h2]
          · exact hlt
      rw [this]
      apply List.countP_eq_zero.mpr
      intro d' hd'
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
      intro heq
      simp only [SimpleGraph.Dart.edge, Sym2.mk_eq_mk] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- d' = d
        have : d' = d := SimpleGraph.Dart.ext _ _ (Prod.ext h1 h2)
        rw [this]
        exact Nat.le_of_lt htls
      · -- d'.fst = d.snd, d'.snd = d.fst
        -- d'.fst.val = d.snd.val < d.fst.val = d'.snd.val
        have hlt' : d'.fst.val < d'.snd.val := by
          calc d'.fst.val = d.snd.val := congrArg Subtype.val h1
          _ < d.fst.val := htls
          _ = d'.snd.val := (congrArg Subtype.val h2).symm
        exact Nat.le_of_lt hlt'
    have hneg : countNegative K C ⟨oe_d.toSimplex, oe_d.mem_edges⟩ = 1 := by
      simp only [countNegative, walkToOrientedEdges]
      rw [List.countP_map]
      have : C.darts.countP (fun d' => (⟨d'.fst, d'.snd, d'.adj⟩ : OrientedEdge K).toSimplex =
             oe_d.toSimplex ∧ d'.snd.val < d'.fst.val) =
             C.darts.countP (fun d' => d'.edge = d.edge ∧ d'.snd.val < d'.fst.val) := by
        apply List.countP_congr
        intro d' _
        constructor
        · intro ⟨heq, hlt⟩
          constructor
          · simp only [OrientedEdge.toSimplex] at heq
            simp only [SimpleGraph.Dart.edge, Sym2.mk_eq_mk]
            have hne' : d'.fst.val ≠ d'.snd.val := d'.adj.1
            rw [toSimplex_eq_iff_same_pair _ _ _ _ hne' hne] at heq
            rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · left; ext <;> [exact Subtype.ext h1; exact Subtype.ext h2]
            · right; ext <;> [exact Subtype.ext h1; exact Subtype.ext h2]
          · exact hlt
        · intro ⟨heq, hlt⟩
          constructor
          · simp only [OrientedEdge.toSimplex]
            simp only [SimpleGraph.Dart.edge, Sym2.mk_eq_mk] at heq
            rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · simp only [h1, h2]
            · rw [Finset.pair_comm]; simp only [h1, h2]
          · exact hlt
      rw [this]
      -- Count darts with d'.edge = d.edge and d'.snd < d'.fst
      have hcount_split : C.darts.countP (fun d' => d'.edge = d.edge ∧ d'.fst.val < d'.snd.val) +
                          C.darts.countP (fun d' => d'.edge = d.edge ∧ d'.snd.val < d'.fst.val) =
                          C.darts.countP (fun d' => d'.edge = d.edge) := by
        rw [← List.countP_add_countP_compl (fun d' => d'.fst.val < d'.snd.val)
            (C.darts.filter (fun d' => d'.edge = d.edge))]
        simp only [List.countP_filter]
        congr 1
        · apply List.countP_congr; intro d' _; simp [and_comm]
        · apply List.countP_congr
          intro d' _
          simp only [Bool.not_eq_true, decide_eq_false_iff_not, not_lt]
          constructor
          · intro ⟨heq, hle⟩
            constructor
            · exact heq
            · have hne' : d'.fst.val ≠ d'.snd.val := d'.adj.1
              exact Nat.lt_of_le_of_ne hle (Ne.symm hne')
          · intro ⟨heq, hlt⟩
            exact ⟨heq, Nat.le_of_lt hlt⟩
      rw [hedge_unique] at hcount_split
      have hpos_zero : C.darts.countP (fun d' => d'.edge = d.edge ∧ d'.fst.val < d'.snd.val) = 0 := by
        apply List.countP_eq_zero.mpr
        intro d' hd'
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
        intro heq
        simp only [SimpleGraph.Dart.edge, Sym2.mk_eq_mk] at heq
        rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · -- d' = d
          have : d' = d := SimpleGraph.Dart.ext _ _ (Prod.ext h1 h2)
          rw [this]
          exact Nat.le_of_lt htls
        · -- d'.fst = d.snd, d'.snd = d.fst
          have hlt' : d'.fst.val < d'.snd.val := by
            calc d'.fst.val = d.snd.val := congrArg Subtype.val h1
            _ < d.fst.val := htls
            _ = d'.snd.val := (congrArg Subtype.val h2).symm
          exact Nat.le_of_lt hlt'
      omega
    simp only [hpos, hneg, Nat.cast_zero, Nat.cast_one, zero_sub, neg_neg]

/-! ## Cycle Indicator Sum Equals Length -/

-- The walk sum of the cycle indicator over the cycle equals the walk's length
-- Proof: Each oriented edge contributes exactly 1 (by self_contribution), so sum = count = length
theorem cycleIndicator_sum_length_proof (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) :
    cochainWalkSum K (cycleIndicator K C) C = C.length := by
  -- Unfold cochainWalkSum to get the sum over oriented edges
  simp only [cochainWalkSum]
  -- Each term in the sum equals 1 by cycleIndicator_self_contribution_proof
  have h_all_one : ∀ oe ∈ walkToOrientedEdges K C,
      oe.sign * cycleIndicator K C ⟨oe.toSimplex, oe.mem_edges⟩ = 1 :=
    cycleIndicator_self_contribution_proof K C hC
  -- The sum of 1s equals the length of the list
  rw [List.map_eq_replicate_iff.mpr ⟨1, ?_⟩]
  · -- Sum of replicate n 1 = n
    simp only [List.sum_replicate, smul_eq_mul, mul_one]
    -- walkToOrientedEdges K C has the same length as C.darts
    simp only [walkToOrientedEdges, List.length_map]
    -- C.darts.length = C.length by SimpleGraph.Walk.length_darts
    exact C.length_darts.symm
  · exact h_all_one

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
