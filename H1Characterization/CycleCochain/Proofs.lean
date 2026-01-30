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
theorem oriented_edge_coboundary_proof (K : SimplicialComplex) (g : Cochain K 0)
    (oe : OrientedEdge K) :
    oe.sign * (δ K 0 g) ⟨oe.toSimplex, oe.mem_edges⟩ =
    g (vertex0Simplex K oe.tgt) - g (vertex0Simplex K oe.src) := by
  obtain ⟨a, b, ha, hb, heq, hlt, hδ⟩ := coboundary_edge_formula K g ⟨oe.toSimplex, oe.mem_edges⟩
  simp only [OrientedEdge.toSimplex] at heq
  have hsrc_mem : oe.src.val ∈ ({a, b} : Finset ℕ) := by
    have : oe.src.val ∈ ({oe.src.val, oe.tgt.val} : Finset ℕ) := Finset.mem_insert_self _ _
    rw [heq] at this; exact this
  have htgt_mem : oe.tgt.val ∈ ({a, b} : Finset ℕ) := by
    have : oe.tgt.val ∈ ({oe.src.val, oe.tgt.val} : Finset ℕ) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [heq] at this; exact this
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsrc_mem htgt_mem
  have hne : oe.src.val ≠ oe.tgt.val := oe.adj.1
  by_cases hslt : oe.src.val < oe.tgt.val
  · simp only [OrientedEdge.sign, hslt, ↓reduceIte, one_mul]
    have hsrc_eq : oe.src.val = a := by
      rcases hsrc_mem with h | h
      · exact h
      · rcases htgt_mem with h' | h'
        · rw [h, h'] at hslt; exact absurd hslt (Nat.not_lt.mpr (Nat.le_of_lt hlt))
        · rw [h, h'] at hne; exact absurd rfl hne
    have htgt_eq : oe.tgt.val = b := by
      rcases htgt_mem with h | h
      · rw [hsrc_eq, h] at hne; exact absurd rfl hne
      · exact h
    rw [hδ]
    have h1 : (⟨{b}, hb⟩ : {s // s ∈ K.ksimplices 0}) = vertex0Simplex K oe.tgt := by
      apply Subtype.ext; simp only [vertex0Simplex]; rw [htgt_eq]
    have h2 : (⟨{a}, ha⟩ : {s // s ∈ K.ksimplices 0}) = vertex0Simplex K oe.src := by
      apply Subtype.ext; simp only [vertex0Simplex]; rw [hsrc_eq]
    rw [h1, h2]
  · have htls : oe.tgt.val < oe.src.val := Nat.lt_of_le_of_ne (Nat.not_lt.mp hslt) (Ne.symm hne)
    simp only [OrientedEdge.sign, hslt, ↓reduceIte, neg_one_mul]
    have htgt_eq : oe.tgt.val = a := by
      rcases htgt_mem with h | h
      · exact h
      · rcases hsrc_mem with h' | h'
        · rw [h, h'] at htls; exact absurd htls (Nat.not_lt.mpr (Nat.le_of_lt hlt))
        · rw [h, h'] at hne; exact absurd rfl (Ne.symm hne)
    have hsrc_eq : oe.src.val = b := by
      rcases hsrc_mem with h | h
      · rw [htgt_eq, h] at hne; exact absurd rfl hne
      · exact h
    rw [hδ]
    have h1 : (⟨{a}, ha⟩ : {s // s ∈ K.ksimplices 0}) = vertex0Simplex K oe.tgt := by
      apply Subtype.ext; simp only [vertex0Simplex]; rw [htgt_eq]
    have h2 : (⟨{b}, hb⟩ : {s // s ∈ K.ksimplices 0}) = vertex0Simplex K oe.src := by
      apply Subtype.ext; simp only [vertex0Simplex]; rw [hsrc_eq]
    rw [h1, h2]
    ring

/-! ## Trail Properties -/

lemma trail_edges_nodup (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (hp : p.IsTrail) : p.edges.Nodup := hp.edges_nodup

lemma cycle_is_trail (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) : C.IsTrail :=
  hC.isCircuit.isTrail

/-! ## Cycle Indicator Self-Contribution Proof -/

lemma trail_edge_count_eq_one (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (hp : p.IsTrail) (e : Sym2 K.vertexSet) (he : e ∈ p.edges) :
    p.edges.count e = 1 :=
  List.count_eq_one_of_mem hp.edges_nodup he

lemma walkToOrientedEdges_mem_iff (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (oe : OrientedEdge K) :
    oe ∈ walkToOrientedEdges K p ↔ ∃ d ∈ p.darts, oe = ⟨d.fst, d.snd, d.adj⟩ := by
  simp only [walkToOrientedEdges, List.mem_map]
  constructor
  · intro ⟨d, hd, heq⟩; exact ⟨d, hd, heq.symm⟩
  · intro ⟨d, hd, heq⟩; exact ⟨d, hd, heq.symm⟩

/-! ## Helper Lemmas for Self-Contribution Proof -/

-- Convert count in mapped list to countP
private lemma count_map_eq_countP' {α β : Type*} [DecidableEq β] (f : α → β) (l : List α) (b : β) :
    (l.map f).count b = l.countP (fun a => f a = b) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.count_cons, List.countP_cons, ih, beq_iff_eq, decide_eq_true_eq]

-- In a trail, each dart's edge appears exactly once
private lemma trail_dart_edge_unique' (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (hp : p.IsTrail) (d : (oneSkeleton K).Dart) (hd : d ∈ p.darts) :
    p.darts.countP (fun d' => d'.edge = d.edge) = 1 := by
  have he : d.edge ∈ p.edges := List.mem_map.mpr ⟨d, hd, rfl⟩
  have hcount : p.edges.count d.edge = 1 := List.count_eq_one_of_mem hp.edges_nodup he
  simp only [SimpleGraph.Walk.edges] at hcount
  rw [count_map_eq_countP'] at hcount
  exact hcount

-- toSimplex equality means same unordered pair
private lemma toSimplex_eq_iff_same_pair' (K : SimplicialComplex) (a b c d : K.vertexSet)
    (hab : a.val ≠ b.val) (_hcd : c.val ≠ d.val) :
    ({a.val, b.val} : Finset ℕ) = {c.val, d.val} ↔
    (a.val = c.val ∧ b.val = d.val) ∨ (a.val = d.val ∧ b.val = c.val) := by
  constructor
  · intro heq
    have ha : a.val ∈ ({c.val, d.val} : Finset ℕ) := by
      rw [← heq]; exact Finset.mem_insert_self _ _
    have hb : b.val ∈ ({c.val, d.val} : Finset ℕ) := by
      rw [← heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha_eq | ha_eq
    · rcases hb with hb_eq | hb_eq
      · rw [ha_eq, hb_eq] at hab; exact absurd rfl hab
      · left; exact ⟨ha_eq, hb_eq⟩
    · rcases hb with hb_eq | hb_eq
      · right; exact ⟨ha_eq, hb_eq⟩
      · rw [ha_eq, hb_eq] at hab; exact absurd rfl hab
  · intro h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simp only [ha, hb]
    · rw [Finset.pair_comm]; simp only [ha, hb]

-- Sym2 equality for edges
private lemma dart_edge_eq_iff' (K : SimplicialComplex) (d1 d2 : (oneSkeleton K).Dart) :
    d1.edge = d2.edge ↔
    (d1.fst = d2.fst ∧ d1.snd = d2.snd) ∨ (d1.fst = d2.snd ∧ d1.snd = d2.fst) := by
  rw [SimpleGraph.Dart.edge, SimpleGraph.Dart.edge, Sym2.mk_eq_mk_iff]
  constructor
  · intro h
    rcases h with heq | heq
    · left; exact Prod.ext_iff.mp heq
    · right
      have h1 : d1.fst = d2.snd := congrArg Prod.fst heq
      have h2 : d1.snd = d2.fst := congrArg Prod.snd heq
      exact ⟨h1, h2⟩
  · intro h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact Prod.ext h1 h2
    · right; exact Prod.ext h1 h2

-- If countP = 1, any two elements satisfying predicate are equal
private lemma countP_eq_one_unique' {α : Type*} {l : List α} {p : α → Bool}
    (hcount : l.countP p = 1) (x y : α) (hx : x ∈ l) (hy : y ∈ l)
    (hpx : p x = true) (hpy : p y = true) : x = y := by
  rw [List.countP_eq_length_filter] at hcount
  have hx_filt : x ∈ l.filter p := List.mem_filter.mpr ⟨hx, hpx⟩
  have hy_filt : y ∈ l.filter p := List.mem_filter.mpr ⟨hy, hpy⟩
  cases hf : l.filter p with
  | nil =>
    simp only [hf, List.length_nil] at hcount
    omega  -- 0 = 1 is false
  | cons z zs =>
    simp only [hf, List.length_cons] at hcount
    have hzs : zs = [] := List.eq_nil_of_length_eq_zero (Nat.succ_injective hcount)
    rw [hf, hzs] at hx_filt hy_filt
    simp only [List.mem_singleton] at hx_filt hy_filt
    exact hx_filt.trans hy_filt.symm

-- countP q ≤ countP p when q implies p
private lemma countP_le_of_imp' {α : Type*} (l : List α) {p q : α → Bool}
    (hqp : ∀ x, q x = true → p x = true) : l.countP q ≤ l.countP p := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.countP_cons]
    by_cases hqa : q a = true
    · have hpa : p a = true := hqp a hqa
      simp only [hqa, hpa, ite_true]
      exact Nat.add_le_add_right ih 1
    · simp only [Bool.not_eq_true] at hqa
      simp only [hqa]
      by_cases hpa : p a = true
      · simp only [hpa, ite_true]
        calc as.countP q ≤ as.countP p := ih
          _ ≤ as.countP p + 1 := Nat.le_add_right _ _
      · simp only [Bool.not_eq_true] at hpa
        simp only [hpa]
        exact ih

-- countP ≥ 1 when element in list satisfies predicate
private lemma countP_pos_of_mem' {α : Type*} {l : List α} {p : α → Bool}
    (x : α) (hx : x ∈ l) (hpx : p x = true) : 1 ≤ l.countP p := by
  induction l with
  | nil => simp at hx
  | cons a as ih =>
    simp only [List.countP_cons]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxas
    · simp only [hpx, ↓reduceIte]; omega
    · have := ih hxas; omega

-- If countP p l = 1 and q implies p, and unique element satisfies q, then countP q l = 1
private lemma countP_eq_one_of_refines' {α : Type*} {l : List α} {p q : α → Bool}
    (hp_one : l.countP p = 1) (hqp : ∀ x, q x = true → p x = true)
    (x : α) (hx : x ∈ l) (hqx : q x = true) : l.countP q = 1 := by
  have hle : l.countP q ≤ l.countP p := countP_le_of_imp' l hqp
  have hge : 1 ≤ l.countP q := countP_pos_of_mem' x hx hqx
  omega

-- Main theorem: Each oriented edge in a cycle contributes 1 to its own indicator sum
-- The proof relies on: in a trail, each undirected edge appears exactly once
-- So for an oriented edge with a given direction, either:
-- - If src < tgt: countPositive = 1, countNegative = 0, so sign(1) * (1-0) = 1
-- - If tgt < src: countPositive = 0, countNegative = 1, so sign(-1) * (0-1) = 1
theorem cycleIndicator_self_contribution_proof (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) :
    ∀ oe ∈ walkToOrientedEdges K C,
      oe.sign * cycleIndicator K C ⟨oe.toSimplex, oe.mem_edges⟩ = 1 := by
  intro oe hoe
  rw [walkToOrientedEdges_mem_iff] at hoe
  obtain ⟨d, hd, rfl⟩ := hoe
  have htrail : C.IsTrail := hC.isCircuit.isTrail
  have he : d.edge ∈ C.edges := by
    simp only [SimpleGraph.Walk.edges]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  have _hedge_count : C.edges.count d.edge = 1 := trail_edge_count_eq_one K C htrail d.edge he
  simp only [cycleIndicator]
  let oe_d : OrientedEdge K := ⟨d.fst, d.snd, d.adj⟩
  by_cases hslt : d.fst.val < d.snd.val
  · -- Case: src < tgt, so sign = 1
    have hsign : oe_d.sign = 1 := if_pos hslt
    rw [hsign, one_mul]
    -- Trail uniqueness: exactly one dart has this edge
    have hedge_unique : C.darts.countP (fun d' => d'.edge = d.edge) = 1 :=
      trail_dart_edge_unique' K C htrail d hd
    -- Any dart with same edge must be d
    have same_edge_implies_eq : ∀ d' ∈ C.darts, d'.edge = d.edge → d' = d := by
      intro d' hd' hedge
      exact countP_eq_one_unique' hedge_unique d' d hd' hd
        (by simp only [decide_eq_true_eq]; exact hedge)
        (by simp only [decide_eq_true_eq])
    have hpos : countPositive K C ⟨oe_d.toSimplex, oe_d.mem_edges⟩ = 1 := by
      simp only [countPositive, walkToOrientedEdges, List.countP_map]
      apply countP_eq_one_of_refines' hedge_unique
      · intro d' hq
        simp only [Function.comp_apply, decide_eq_true_eq] at hq ⊢
        obtain ⟨hsimplex, _⟩ := hq
        rw [dart_edge_eq_iff' K]
        simp only [OrientedEdge.toSimplex] at hsimplex
        rw [toSimplex_eq_iff_same_pair' K _ _ _ _ d'.adj.1 d.adj.1] at hsimplex
        rcases hsimplex with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
        · right; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact hd
      · simp only [Function.comp_apply, decide_eq_true_eq, OrientedEdge.toSimplex]
        exact ⟨rfl, hslt⟩
    have hneg : countNegative K C ⟨oe_d.toSimplex, oe_d.mem_edges⟩ = 0 := by
      simp only [countNegative, walkToOrientedEdges, List.countP_map]
      apply List.countP_eq_zero.mpr; intro d' hd'
      simp only [Function.comp_apply, decide_eq_true_eq, not_and, not_lt]
      intro heq
      simp only [OrientedEdge.toSimplex] at heq
      have hedge : d'.edge = d.edge := by
        rw [dart_edge_eq_iff' K]
        rw [toSimplex_eq_iff_same_pair' K _ _ _ _ d'.adj.1 d.adj.1] at heq
        rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
        · right; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
      have heq_d := same_edge_implies_eq d' hd' hedge
      rw [heq_d]; exact Nat.le_of_lt hslt
    rw [hpos, hneg]; norm_num
  · -- Case: ¬(src < tgt), so tgt < src, sign = -1
    have hne : d.fst.val ≠ d.snd.val := d.adj.1
    have htls : d.snd.val < d.fst.val := Nat.lt_of_le_of_ne (Nat.not_lt.mp hslt) (Ne.symm hne)
    have hsign : oe_d.sign = -1 := if_neg hslt
    rw [hsign]
    -- Trail uniqueness: exactly one dart has this edge
    have hedge_unique : C.darts.countP (fun d' => d'.edge = d.edge) = 1 :=
      trail_dart_edge_unique' K C htrail d hd
    -- Any dart with same edge must be d
    have same_edge_implies_eq : ∀ d' ∈ C.darts, d'.edge = d.edge → d' = d := by
      intro d' hd' hedge
      exact countP_eq_one_unique' hedge_unique d' d hd' hd
        (by simp only [decide_eq_true_eq]; exact hedge)
        (by simp only [decide_eq_true_eq])
    have hpos : countPositive K C ⟨oe_d.toSimplex, oe_d.mem_edges⟩ = 0 := by
      simp only [countPositive, walkToOrientedEdges, List.countP_map]
      apply List.countP_eq_zero.mpr; intro d' hd'
      simp only [Function.comp_apply, decide_eq_true_eq, not_and, not_lt]
      intro heq
      simp only [OrientedEdge.toSimplex] at heq
      have hedge : d'.edge = d.edge := by
        rw [dart_edge_eq_iff' K]
        rw [toSimplex_eq_iff_same_pair' K _ _ _ _ d'.adj.1 hne] at heq
        rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
        · right; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
      have heq_d := same_edge_implies_eq d' hd' hedge
      rw [heq_d]; exact Nat.le_of_lt htls
    have hneg : countNegative K C ⟨oe_d.toSimplex, oe_d.mem_edges⟩ = 1 := by
      simp only [countNegative, walkToOrientedEdges, List.countP_map]
      apply countP_eq_one_of_refines' hedge_unique
      · intro d' hq
        simp only [Function.comp_apply, decide_eq_true_eq] at hq ⊢
        obtain ⟨hsimplex, _⟩ := hq
        rw [dart_edge_eq_iff' K]
        simp only [OrientedEdge.toSimplex] at hsimplex
        rw [toSimplex_eq_iff_same_pair' K _ _ _ _ d'.adj.1 hne] at hsimplex
        rcases hsimplex with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
        · right; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact hd
      · simp only [Function.comp_apply, decide_eq_true_eq, OrientedEdge.toSimplex]
        exact ⟨rfl, htls⟩
    rw [hpos, hneg]; norm_num

/-! ## Cycle Indicator Sum Equals Length -/

theorem cycleIndicator_sum_length_proof (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) :
    cochainWalkSum K (cycleIndicator K C) C = C.length := by
  simp only [cochainWalkSum]
  have h_all_one : ∀ oe ∈ walkToOrientedEdges K C,
      oe.sign * cycleIndicator K C ⟨oe.toSimplex, oe.mem_edges⟩ = 1 :=
    cycleIndicator_self_contribution_proof K C hC
  have h_map_ones : (walkToOrientedEdges K C).map
      (fun oe => oe.sign * cycleIndicator K C ⟨oe.toSimplex, oe.mem_edges⟩) =
      List.replicate (walkToOrientedEdges K C).length 1 := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_replicate]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_replicate]
      apply h_all_one
      have h1' : i < (walkToOrientedEdges K C).length := by
        simp only [List.length_map] at h1; exact h1
      exact List.getElem_mem h1'
  rw [h_map_ones]
  simp only [List.sum_replicate]
  simp only [walkToOrientedEdges, List.length_map]
  simp only [nsmul_eq_mul, mul_one]
  norm_cast
  exact C.length_darts

/-! ## Cycle Indicator Not Coboundary -/

theorem cycleIndicator_not_coboundary_proof (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) :
    ¬IsCoboundary K 1 (cycleIndicator K C) := by
  intro ⟨g, hg⟩
  have h_sum_length : cochainWalkSum K (cycleIndicator K C) C = C.length :=
    cycleIndicator_sum_length K C hC
  have h_sum_zero : cochainWalkSum K (δ K 0 g) C = 0 :=
    coboundary_walk_sum_zero K g C
  rw [hg] at h_sum_zero
  rw [h_sum_length] at h_sum_zero
  have h_length_pos : 0 < C.length := by
    have h_not_nil := hC.not_nil
    rw [SimpleGraph.Walk.not_nil_iff_lt_length] at h_not_nil
    exact h_not_nil
  have h_length_zero : C.length = 0 := by
    have : (C.length : ℚ) = 0 := h_sum_zero
    exact Nat.cast_injective this
  omega

end H1Characterization
