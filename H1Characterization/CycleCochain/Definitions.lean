/-
  H1Characterization/CycleCochain/Definitions.lean

  Definitions for cycle indicators and oriented edges.
  No proofs requiring ForestCoboundary.

  SORRIES: 0
  AXIOMS: 0 (axiom eliminated by requiring hasNoFilledTriangles hypothesis)

  KEY THEOREMS:
    ✓ cochain_one_is_cocycle_of_no_2simplices: ANY 1-cochain is a cocycle when no 2-simplices
    ✓ cycleIndicator_is_cocycle_hollow: Cycle indicator is cocycle for hollow complexes
    ✓ cycleIndicator_is_cocycle_oneConnected: Vacuously true (no cycles in OneConnected)
    ✓ cycle_implies_h1_nontrivial: Requires hasNoFilledTriangles hypothesis
    ✓ h1_trivial_implies_oneConnected: Requires hasNoFilledTriangles hypothesis

  NOTE: The cycleIndicator cocycle property is NOT universally true for complexes
  with filled 2-simplices. The main theorem now requires hasNoFilledTriangles K.
-/

import H1Characterization.OneConnected

namespace H1Characterization

open Foundations
open Foundations.SimplicialComplex (ksimplices)

/-! ## Oriented Edges -/

structure OrientedEdge (K : SimplicialComplex) where
  src : K.vertexSet
  tgt : K.vertexSet
  adj : (oneSkeleton K).Adj src tgt

variable {K : SimplicialComplex}

def OrientedEdge.toSimplex (e : OrientedEdge K) : Simplex := {e.src.val, e.tgt.val}

lemma OrientedEdge.mem_edges (e : OrientedEdge K) : e.toSimplex ∈ K.ksimplices 1 := by
  unfold Foundations.SimplicialComplex.ksimplices
  simp only [Set.mem_setOf_eq]
  constructor
  · exact e.adj.2
  · exact Finset.card_pair e.adj.1

def OrientedEdge.sign (e : OrientedEdge K) : Coeff := if e.src.val < e.tgt.val then 1 else -1

variable {K : SimplicialComplex}

/-! ## Walk to Edges -/

def walkToOrientedEdges (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) : List (OrientedEdge K) :=
  p.darts.map fun d => ⟨d.fst, d.snd, d.adj⟩

def walkToEdgeList (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) : List Simplex :=
  (walkToOrientedEdges K p).map OrientedEdge.toSimplex

lemma walkToEdgeList_mem (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (e : Simplex) (he : e ∈ walkToEdgeList K p) : e ∈ K.ksimplices 1 := by
  unfold walkToEdgeList walkToOrientedEdges at he
  simp only [List.mem_map] at he
  obtain ⟨oe, _, rfl⟩ := he
  exact oe.mem_edges

/-! ## Cycle Indicator -/

def countPositive (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (e : { s : Simplex // s ∈ K.ksimplices 1 }) : ℕ :=
  (walkToOrientedEdges K p).countP fun oe => oe.toSimplex = e.val ∧ oe.src.val < oe.tgt.val

def countNegative (K : SimplicialComplex) {v w : K.vertexSet}
    (p : Walk K v w) (e : { s : Simplex // s ∈ K.ksimplices 1 }) : ℕ :=
  (walkToOrientedEdges K p).countP fun oe => oe.toSimplex = e.val ∧ oe.tgt.val < oe.src.val

def cycleIndicator (K : SimplicialComplex) {v : K.vertexSet} (C : Walk K v v) : Cochain K 1 :=
  fun e => (countPositive K C e : ℚ) - (countNegative K C e : ℚ)

/-! ## Cocycle Property -/

/-! ### General Theorem: Cocycles when no 2-simplices exist

    When K has no 2-simplices, ANY 1-cochain is automatically a cocycle.
    Reason: δ¹ maps C¹(K) → C²(K), which is a function space from an empty domain
    when K.ksimplices 2 = ∅. Functions from empty types are unique (by extensionality).
-/

/-- Any 1-cochain is a cocycle when the complex has no 2-simplices.

    This is a general fact: when K.ksimplices 2 = ∅, the coboundary operator δ¹
    maps to Cochain K 2, which is a function from an empty type. By function
    extensionality, δ¹(f) = 0 for any f. -/
theorem cochain_one_is_cocycle_of_no_2simplices (K : SimplicialComplex)
    (f : Cochain K 1) (h : K.ksimplices 2 = ∅) :
    IsCocycle K 1 f := by
  unfold IsCocycle
  -- δ K 1 f : Cochain K 2 = {s // s ∈ K.ksimplices 2} → Coeff
  -- Since K.ksimplices 2 = ∅, this is a function from an empty type
  funext σ
  -- σ : {s // s ∈ K.ksimplices (1 + 1)}, but K.ksimplices 2 = ∅
  exfalso
  have : σ.val ∈ K.ksimplices 2 := by
    show σ.val ∈ K.ksimplices (1 + 1)
    exact σ.property
  simp only [h] at this
  exact this

/-! ## Cocycle Property for Cycle Indicators

    The cycle indicator is a cocycle when:
    - ✓ PROVEN for complexes with no 2-simplices (see cochain_one_is_cocycle_of_no_2simplices)
    - ✓ PROVEN for OneConnected complexes (vacuously true, no cycles exist)

    NOTE: NOT universally true for complexes with filled simplices!
    COUNTEREXAMPLE: For a filled triangle {0,1,2} with cycle 0→1→2→0:
      - cycleIndicator({0,1}) = +1, cycleIndicator({1,2}) = +1, cycleIndicator({0,2}) = -1
      - (δf)({0,1,2}) = 1 - (-1) + 1 = 3 ≠ 0 (NOT a cocycle!)

    The H¹ characterization theory requires the `hasNoFilledTriangles` hypothesis.
-/

/-- A simplicial complex has no filled 2-simplices (only hollow triangles at most). -/
def hasNoFilledTriangles (K : SimplicialComplex) : Prop :=
  K.ksimplices 2 = ∅

/-- PROVEN VERSION: cycleIndicator is a cocycle when K has no 2-simplices.

    This follows from the general theorem cochain_one_is_cocycle_of_no_2simplices.
    When there are no 2-simplices, ANY 1-cochain is a cocycle. -/
theorem cycleIndicator_is_cocycle_hollow (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (_hC : C.IsCycle) (hK : hasNoFilledTriangles K) :
    IsCocycle K 1 (cycleIndicator K C) :=
  cochain_one_is_cocycle_of_no_2simplices K (cycleIndicator K C) hK

/-- PROVEN VERSION: This is vacuously true for OneConnected complexes.

    OneConnected K means the 1-skeleton has no cycles. If we have a cycle C,
    this contradicts OneConnected. The result follows from False (ex falso quodlibet). -/
theorem cycleIndicator_is_cocycle_oneConnected (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) (hK : OneConnected K) :
    IsCocycle K 1 (cycleIndicator K C) := by
  -- OneConnected means no cycles, but we have a cycle C - contradiction!
  exfalso
  rw [oneConnected_iff_no_cycles] at hK
  exact hK v C hC

/-! ## Walk Sum -/

def cochainWalkSum (K : SimplicialComplex) (f : Cochain K 1) {v w : K.vertexSet}
    (p : Walk K v w) : Coeff :=
  ((walkToOrientedEdges K p).map fun oe => oe.sign * f ⟨oe.toSimplex, oe.mem_edges⟩).sum

-- Helper: Get 0-simplex for a vertex
def vertex0Simplex (K : SimplicialComplex) (v : K.vertexSet) :
    { s : Simplex // s ∈ K.ksimplices 0 } := by
  use {v.val}
  constructor
  · exact v.property
  · exact Finset.card_singleton v.val

/-! ## Lemma Statements -/

-- Key lemma: coboundary on an oriented edge
-- Mathematical content:
-- For a 2-element simplex {a, b} with a < b:
--   (δg)(e) = sign(0)*g(face_0) + sign(1)*g(face_1) = g({b}) - g({a})
-- For oriented edge (src→tgt):
--   If src < tgt: sign = 1, e = {src, tgt}, so (δg)(e) = g({tgt}) - g({src})
--   If tgt < src: sign = -1, e = {tgt, src}, so (δg)(e) = g({src}) - g({tgt})
--   Either way: sign * (δg)(e) = g({tgt}) - g({src})
theorem oriented_edge_coboundary (K : SimplicialComplex) (g : Cochain K 0)
    (oe : OrientedEdge K) :
    oe.sign * (δ K 0 g) ⟨oe.toSimplex, oe.mem_edges⟩ =
    g (vertex0Simplex K oe.tgt) - g (vertex0Simplex K oe.src) := by
  -- The edge has cardinality 2 and vertices src ≠ tgt
  have hcard : oe.toSimplex.card = 2 := oe.mem_edges.2
  have hne : oe.src.val ≠ oe.tgt.val := oe.adj.1
  -- Define indices for the two faces
  have h_idx0 : (0 : ℕ) < oe.toSimplex.card := by rw [hcard]; omega
  have h_idx1 : (1 : ℕ) < oe.toSimplex.card := by rw [hcard]; omega
  let i0 : Fin oe.toSimplex.card := ⟨0, h_idx0⟩
  let i1 : Fin oe.toSimplex.card := ⟨1, h_idx1⟩
  -- The universe of Fin 2 is {i0, i1}
  have h_univ : (Finset.univ : Finset (Fin oe.toSimplex.card)) = {i0, i1} := by
    ext i; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    have hi : i.val < 2 := by rw [← hcard]; exact i.isLt
    rcases i with ⟨n, hn⟩
    rcases n with _ | n; · left; rfl
    rcases n with _ | n; · right; rfl
    omega
  have h_ne_idx : i0 ≠ i1 := by intro h; have : (0 : ℕ) = 1 := congrArg Fin.val h; omega
  -- Case split on the ordering of src and tgt
  by_cases hslt : oe.src.val < oe.tgt.val
  · -- Case: src < tgt, so sign = 1
    -- Sorted list is [src, tgt], so face 0 = {tgt}, face 1 = {src}
    have h_sort : oe.toSimplex.sort (· ≤ ·) = [oe.src.val, oe.tgt.val] := by
      simp only [OrientedEdge.toSimplex]
      have h_ne' : oe.src.val ∉ ({oe.tgt.val} : Finset ℕ) := by simp [ne_of_lt hslt]
      have h_insert : ({oe.src.val, oe.tgt.val} : Finset ℕ) = insert oe.src.val {oe.tgt.val} := by
        ext x; simp [Finset.mem_insert, Finset.mem_singleton]
      rw [h_insert, Finset.sort_insert (r := (· ≤ ·))]
      · simp only [Finset.sort_singleton]
      · intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]; exact le_of_lt hslt
      · exact h_ne'
    have h_face0 : oe.toSimplex.face i0 = {oe.tgt.val} := by
      simp only [Simplex.face, h_sort, List.get_eq_getElem]
      ext x; simp only [Finset.mem_erase, Finset.mem_singleton]
      constructor
      · intro ⟨hne', hx⟩
        simp only [OrientedEdge.toSimplex] at hx
        simp at hx; rcases hx with rfl | rfl
        · exact absurd rfl hne'
        · rfl
      · intro rfl; simp only [OrientedEdge.toSimplex]
        exact ⟨ne_of_gt hslt, by simp⟩
    have h_face1 : oe.toSimplex.face i1 = {oe.src.val} := by
      simp only [Simplex.face, h_sort, List.get_eq_getElem]
      ext x; simp only [Finset.mem_erase, Finset.mem_singleton]
      constructor
      · intro ⟨hne', hx⟩
        simp only [OrientedEdge.toSimplex] at hx
        simp at hx; rcases hx with rfl | rfl
        · rfl
        · exact absurd rfl hne'
      · intro rfl; simp only [OrientedEdge.toSimplex]
        exact ⟨ne_of_lt hslt, by simp⟩
    -- Face membership proofs
    have h_face0_mem : oe.toSimplex.face i0 ∈ K.ksimplices 0 := by
      rw [h_face0]
      exact ⟨oe.tgt.property, Finset.card_singleton _⟩
    have h_face1_mem : oe.toSimplex.face i1 ∈ K.ksimplices 0 := by
      rw [h_face1]
      exact ⟨oe.src.property, Finset.card_singleton _⟩
    -- Subtype equalities
    have h_eq_tgt : (⟨oe.toSimplex.face i0, h_face0_mem⟩ : {s // s ∈ K.ksimplices 0}) =
        vertex0Simplex K oe.tgt := Subtype.ext h_face0
    have h_eq_src : (⟨oe.toSimplex.face i1, h_face1_mem⟩ : {s // s ∈ K.ksimplices 0}) =
        vertex0Simplex K oe.src := Subtype.ext h_face1
    -- Now compute the coboundary
    simp only [OrientedEdge.sign, hslt, ↓reduceIte, one_mul, coboundary]
    rw [show (Finset.univ : Finset (Fin oe.toSimplex.card)) = {i0, i1} from h_univ]
    rw [Finset.sum_pair h_ne_idx]
    -- Simplify the signs
    have hi0 : i0.val = 0 := rfl
    have hi1 : i1.val = 1 := rfl
    simp only [hi0, hi1, sign_zero, sign_one, one_mul, neg_one_mul]
    -- Use proof irrelevance for the subtype membership
    have h1 : g ⟨oe.toSimplex.face i0, _⟩ = g ⟨oe.toSimplex.face i0, h_face0_mem⟩ := rfl
    have h2 : g ⟨oe.toSimplex.face i1, _⟩ = g ⟨oe.toSimplex.face i1, h_face1_mem⟩ := rfl
    rw [h1, h2, h_eq_tgt, h_eq_src]
    ring
  · -- Case: ¬(src < tgt), so tgt < src (since src ≠ tgt), sign = -1
    have htls : oe.tgt.val < oe.src.val := Nat.lt_of_le_of_ne (Nat.not_lt.mp hslt) (Ne.symm hne)
    -- Sorted list is [tgt, src], so face 0 = {src}, face 1 = {tgt}
    have h_sort : oe.toSimplex.sort (· ≤ ·) = [oe.tgt.val, oe.src.val] := by
      simp only [OrientedEdge.toSimplex]
      have h_ne' : oe.tgt.val ∉ ({oe.src.val} : Finset ℕ) := by simp [ne_of_lt htls]
      have h_insert : ({oe.src.val, oe.tgt.val} : Finset ℕ) = insert oe.tgt.val {oe.src.val} := by
        ext x; simp [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h; rcases h with rfl | rfl <;> [right; left] <;> rfl
        · intro h; rcases h with rfl | rfl <;> [right; left] <;> rfl
      rw [h_insert, Finset.sort_insert (r := (· ≤ ·))]
      · simp only [Finset.sort_singleton]
      · intro x hx; simp only [Finset.mem_singleton] at hx; rw [hx]; exact le_of_lt htls
      · exact h_ne'
    have h_face0 : oe.toSimplex.face i0 = {oe.src.val} := by
      simp only [Simplex.face, h_sort, List.get_eq_getElem]
      ext x; simp only [Finset.mem_erase, Finset.mem_singleton]
      constructor
      · intro ⟨hne', hx⟩
        simp only [OrientedEdge.toSimplex] at hx
        simp at hx; rcases hx with rfl | rfl
        · rfl
        · exact absurd rfl hne'
      · intro rfl; simp only [OrientedEdge.toSimplex]
        exact ⟨ne_of_gt htls, by simp⟩
    have h_face1 : oe.toSimplex.face i1 = {oe.tgt.val} := by
      simp only [Simplex.face, h_sort, List.get_eq_getElem]
      ext x; simp only [Finset.mem_erase, Finset.mem_singleton]
      constructor
      · intro ⟨hne', hx⟩
        simp only [OrientedEdge.toSimplex] at hx
        simp at hx; rcases hx with rfl | rfl
        · exact absurd rfl hne'
        · rfl
      · intro rfl; simp only [OrientedEdge.toSimplex]
        exact ⟨ne_of_lt htls, by simp⟩
    -- Face membership proofs
    have h_face0_mem : oe.toSimplex.face i0 ∈ K.ksimplices 0 := by
      rw [h_face0]
      exact ⟨oe.src.property, Finset.card_singleton _⟩
    have h_face1_mem : oe.toSimplex.face i1 ∈ K.ksimplices 0 := by
      rw [h_face1]
      exact ⟨oe.tgt.property, Finset.card_singleton _⟩
    -- Subtype equalities
    have h_eq_src : (⟨oe.toSimplex.face i0, h_face0_mem⟩ : {s // s ∈ K.ksimplices 0}) =
        vertex0Simplex K oe.src := Subtype.ext h_face0
    have h_eq_tgt : (⟨oe.toSimplex.face i1, h_face1_mem⟩ : {s // s ∈ K.ksimplices 0}) =
        vertex0Simplex K oe.tgt := Subtype.ext h_face1
    -- Now compute the coboundary
    simp only [OrientedEdge.sign, hslt, ↓reduceIte, neg_one_mul, coboundary]
    rw [show (Finset.univ : Finset (Fin oe.toSimplex.card)) = {i0, i1} from h_univ]
    rw [Finset.sum_pair h_ne_idx]
    -- Simplify the signs
    have hi0 : i0.val = 0 := rfl
    have hi1 : i1.val = 1 := rfl
    simp only [hi0, hi1, sign_zero, sign_one, one_mul, neg_one_mul]
    -- Use proof irrelevance for the subtype membership
    have h1 : g ⟨oe.toSimplex.face i0, _⟩ = g ⟨oe.toSimplex.face i0, h_face0_mem⟩ := rfl
    have h2 : g ⟨oe.toSimplex.face i1, _⟩ = g ⟨oe.toSimplex.face i1, h_face1_mem⟩ := rfl
    rw [h1, h2, h_eq_src, h_eq_tgt]
    ring

/-! ## TRAIL CHAIN: 3 axioms using trail edge uniqueness -/

/-!
Helper lemma: each edge in a trail contributes 1 to its own indicator sum.

Mathematical content:
- IsCycle implies IsTrail (via IsCircuit)
- IsTrail means edges.Nodup (no repeated undirected edges)
- For an oriented edge oe in the walk:
  - The undirected edge {src, tgt} appears exactly once in the walk
  - If src < tgt: countPositive = 1, countNegative = 0, so cycleIndicator = 1
    Therefore oe.sign * cycleIndicator = 1 * 1 = 1
  - If tgt < src: countPositive = 0, countNegative = 1, so cycleIndicator = -1
    Therefore oe.sign * cycleIndicator = (-1) * (-1) = 1
- Either way, oe.sign * cycleIndicator = 1
-/
-- Helper: walkToOrientedEdges membership relates to darts
private lemma walkToOrientedEdges_mem_iff' {v w : K.vertexSet}
    (p : Walk K v w) (oe : OrientedEdge K) :
    oe ∈ walkToOrientedEdges K p ↔ ∃ d ∈ p.darts, oe = ⟨d.fst, d.snd, d.adj⟩ := by
  simp only [walkToOrientedEdges, List.mem_map]
  constructor
  · intro ⟨d, hd, heq⟩; exact ⟨d, hd, heq.symm⟩
  · intro ⟨d, hd, heq⟩; exact ⟨d, hd, heq.symm⟩

-- Helper: count in mapped list = countP
private lemma count_map_eq_countP {α β : Type*} [DecidableEq β] (f : α → β) (l : List α) (b : β) :
    (l.map f).count b = l.countP (fun a => f a = b) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.count_cons, List.countP_cons, ih, beq_iff_eq, decide_eq_true_eq]

-- Helper: In a trail, each dart's edge appears exactly once
private lemma trail_dart_edge_unique' {v w : K.vertexSet}
    (p : Walk K v w) (hp : p.IsTrail) (d : (oneSkeleton K).Dart) (hd : d ∈ p.darts) :
    p.darts.countP (fun d' => d'.edge = d.edge) = 1 := by
  have he : d.edge ∈ p.edges := List.mem_map.mpr ⟨d, hd, rfl⟩
  have hcount : p.edges.count d.edge = 1 := List.count_eq_one_of_mem hp.edges_nodup he
  simp only [SimpleGraph.Walk.edges] at hcount
  rw [count_map_eq_countP] at hcount
  exact hcount

-- Helper: toSimplex equality means same unordered pair
private lemma toSimplex_eq_iff_same_pair' (a b c d : K.vertexSet)
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
      · -- a = c, b = c, so a = b, contradicts hab
        rw [ha_eq, hb_eq] at hab; exact absurd rfl hab
      · left; exact ⟨ha_eq, hb_eq⟩
    · rcases hb with hb_eq | hb_eq
      · right; exact ⟨ha_eq, hb_eq⟩
      · -- a = d, b = d, so a = b, contradicts hab
        rw [ha_eq, hb_eq] at hab; exact absurd rfl hab
  · intro h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simp only [ha, hb]
    · rw [Finset.pair_comm]; simp only [ha, hb]

-- Helper: Sym2 equality for edges
private lemma dart_edge_eq_iff (d1 d2 : (oneSkeleton K).Dart) :
    d1.edge = d2.edge ↔
    (d1.fst = d2.fst ∧ d1.snd = d2.snd) ∨ (d1.fst = d2.snd ∧ d1.snd = d2.fst) := by
  rw [SimpleGraph.Dart.edge, SimpleGraph.Dart.edge, Sym2.mk_eq_mk_iff]
  constructor
  · intro h
    rcases h with heq | heq
    · left; exact Prod.ext_iff.mp heq
    · right
      have h1 : d1.fst = d2.snd := by
        have := congrArg Prod.fst heq
        simp only [Prod.fst_swap] at this
        exact this
      have h2 : d1.snd = d2.fst := by
        have := congrArg Prod.snd heq
        simp only [Prod.snd_swap] at this
        exact this
      exact ⟨h1, h2⟩
  · intro h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact Prod.ext h1 h2
    · right
      apply Prod.ext
      · simp only [Prod.fst_swap]; exact h1
      · simp only [Prod.snd_swap]; exact h2

-- Helper: If countP = 1, any two elements satisfying predicate are equal
private lemma countP_eq_one_unique {α : Type*} {l : List α} {p : α → Bool}
    (hcount : l.countP p = 1) (x y : α) (hx : x ∈ l) (hy : y ∈ l)
    (hpx : p x = true) (hpy : p y = true) : x = y := by
  -- Convert to filter
  rw [List.countP_eq_length_filter] at hcount
  have hx_filt : x ∈ l.filter p := List.mem_filter.mpr ⟨hx, hpx⟩
  have hy_filt : y ∈ l.filter p := List.mem_filter.mpr ⟨hy, hpy⟩
  -- In a singleton list, all elements are equal
  cases hf : l.filter p with
  | nil =>
    simp only [hf, List.length_nil] at hcount
    omega  -- 0 = 1 is false
  | cons z zs =>
    simp only [hf, List.length_cons] at hcount
    have hzs : zs = [] := by
      have h : zs.length = 0 := Nat.succ_injective hcount
      exact List.eq_nil_of_length_eq_zero h
    rw [hf, hzs] at hx_filt hy_filt
    simp only [List.mem_singleton] at hx_filt hy_filt
    exact hx_filt.trans hy_filt.symm

-- Helper: countP q ≤ countP p when q implies p
private lemma countP_le_of_imp {α : Type*} (l : List α) {p q : α → Bool}
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

-- Helper: countP ≥ 1 when element in list satisfies predicate
private lemma countP_pos_of_mem {α : Type*} {l : List α} {p : α → Bool}
    (x : α) (hx : x ∈ l) (hpx : p x = true) : 1 ≤ l.countP p := by
  induction l with
  | nil => simp at hx
  | cons a as ih =>
    simp only [List.countP_cons]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxas
    · simp only [hpx, ↓reduceIte]; omega
    · have := ih hxas; omega

-- Helper: If countP p l = 1 and q implies p, and unique element satisfies q, then countP q l = 1
private lemma countP_eq_one_of_refines {α : Type*} {l : List α} {p q : α → Bool}
    (hp_one : l.countP p = 1) (hqp : ∀ x, q x = true → p x = true)
    (x : α) (hx : x ∈ l) (hqx : q x = true) : l.countP q = 1 := by
  have hle : l.countP q ≤ l.countP p := countP_le_of_imp l hqp
  have hge : 1 ≤ l.countP q := countP_pos_of_mem x hx hqx
  omega

theorem cycleIndicator_self_contribution (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) :
    ∀ oe ∈ walkToOrientedEdges K C,
      oe.sign * cycleIndicator K C ⟨oe.toSimplex, oe.mem_edges⟩ = 1 := by
  intro oe hoe
  -- oe comes from some dart d in C.darts
  rw [walkToOrientedEdges_mem_iff'] at hoe
  obtain ⟨d, hd, rfl⟩ := hoe
  set oe_d : OrientedEdge K := ⟨d.fst, d.snd, d.adj⟩ with hoe_d
  -- C is a trail, so each undirected edge appears exactly once
  have htrail : C.IsTrail := hC.isCircuit.isTrail
  have _hedge_unique : C.darts.countP (fun d' => d'.edge = d.edge) = 1 :=
    trail_dart_edge_unique' C htrail d hd
  -- Unfold cycleIndicator
  simp only [cycleIndicator]
  -- Key: trail_dart_edge_unique' says exactly 1 dart has the same edge
  have hedge_unique := trail_dart_edge_unique' C htrail d hd
  -- Any dart d' with same edge must be d (since count = 1)
  have same_edge_implies_eq : ∀ d' ∈ C.darts, d'.edge = d.edge → d' = d := by
    intro d' hd' hedge
    exact countP_eq_one_unique hedge_unique d' d hd' hd
      (by simp only [decide_eq_true_eq]; exact hedge)
      (by simp only [decide_eq_true_eq])
  -- Case split on whether src < tgt
  by_cases hslt : d.fst.val < d.snd.val
  · -- Case: src < tgt, so sign = 1
    -- countPositive = 1, countNegative = 0, cycleIndicator = 1
    have hsign : oe_d.sign = 1 := if_pos hslt
    rw [hsign, one_mul]
    have hpos : countPositive K C ⟨oe_d.toSimplex, oe_d.mem_edges⟩ = 1 := by
      simp only [countPositive, walkToOrientedEdges, List.countP_map]
      -- Use countP_eq_one_of_refines: positive predicate implies edge equality
      apply countP_eq_one_of_refines hedge_unique
      · -- same simplex implies same edge
        intro d' hq
        simp only [Function.comp_apply, decide_eq_true_eq] at hq ⊢
        obtain ⟨hsimplex, _⟩ := hq
        rw [dart_edge_eq_iff]
        simp only [OrientedEdge.toSimplex] at hsimplex
        rw [toSimplex_eq_iff_same_pair' _ _ _ _ d'.adj.1 d.adj.1] at hsimplex
        rcases hsimplex with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
        · right; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact hd
      · -- d satisfies the positive predicate
        simp only [Function.comp_apply, decide_eq_true_eq, OrientedEdge.toSimplex]
        exact ⟨rfl, hslt⟩
    have hneg : countNegative K C ⟨oe_d.toSimplex, oe_d.mem_edges⟩ = 0 := by
      simp only [countNegative, walkToOrientedEdges, List.countP_map]
      apply List.countP_eq_zero.mpr; intro d' hd'
      simp only [Function.comp_apply, decide_eq_true_eq, not_and, not_lt]
      intro heq
      simp only [OrientedEdge.toSimplex] at heq
      have hedge : d'.edge = d.edge := by
        rw [dart_edge_eq_iff]
        rw [toSimplex_eq_iff_same_pair' _ _ _ _ d'.adj.1 d.adj.1] at heq
        rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
        · right; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
      have heq_d := same_edge_implies_eq d' hd' hedge
      rw [heq_d]; exact Nat.le_of_lt hslt
    simp only [hpos, hneg, Nat.cast_one, Nat.cast_zero, sub_zero]

  · -- Case: ¬(src < tgt), so tgt < src, sign = -1
    have hne : d.fst.val ≠ d.snd.val := d.adj.1
    have htls : d.snd.val < d.fst.val := Nat.lt_of_le_of_ne (Nat.not_lt.mp hslt) (Ne.symm hne)
    have hsign : oe_d.sign = -1 := if_neg hslt
    rw [hsign]
    have hpos : countPositive K C ⟨oe_d.toSimplex, oe_d.mem_edges⟩ = 0 := by
      simp only [countPositive, walkToOrientedEdges, List.countP_map]
      apply List.countP_eq_zero.mpr; intro d' hd'
      simp only [Function.comp_apply, decide_eq_true_eq, not_and, not_lt]
      intro heq
      simp only [OrientedEdge.toSimplex] at heq
      have hedge : d'.edge = d.edge := by
        rw [dart_edge_eq_iff]
        rw [toSimplex_eq_iff_same_pair' _ _ _ _ d'.adj.1 hne] at heq
        rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
        · right; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
      have heq_d := same_edge_implies_eq d' hd' hedge
      rw [heq_d]; exact Nat.le_of_lt htls
    have hneg : countNegative K C ⟨oe_d.toSimplex, oe_d.mem_edges⟩ = 1 := by
      simp only [countNegative, walkToOrientedEdges, List.countP_map]
      -- Use countP_eq_one_of_refines: negative predicate implies edge equality
      apply countP_eq_one_of_refines hedge_unique
      · -- same simplex implies same edge
        intro d' hq
        simp only [Function.comp_apply, decide_eq_true_eq] at hq ⊢
        obtain ⟨hsimplex, _⟩ := hq
        rw [dart_edge_eq_iff]
        simp only [OrientedEdge.toSimplex] at hsimplex
        rw [toSimplex_eq_iff_same_pair' _ _ _ _ d'.adj.1 hne] at hsimplex
        rcases hsimplex with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
        · right; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact hd
      · -- d satisfies the negative predicate
        simp only [Function.comp_apply, decide_eq_true_eq, OrientedEdge.toSimplex]
        exact ⟨rfl, htls⟩
    simp only [hpos, hneg, Nat.cast_zero, Nat.cast_one, zero_sub]
    ring

/-! ## Derived Theorems -/

-- General telescoping property for any walk
-- Proof: By induction. Each edge contribution is g(tgt) - g(src), and these telescope.
theorem walk_sum_delta_zero_telescopes (K : SimplicialComplex) (g : Cochain K 0)
    {u v : K.vertexSet} (p : Walk K u v) :
    cochainWalkSum K (δ K 0 g) p = g (vertex0Simplex K v) - g (vertex0Simplex K u) := by
  induction p with
  | nil =>
    -- Empty walk: sum = 0 = g(u) - g(u)
    simp only [cochainWalkSum, walkToOrientedEdges, SimpleGraph.Walk.darts_nil,
               List.map_nil, List.sum_nil, sub_self]
  | cons hadj p' ih =>
    -- Walk from u to y to v via edge (u,y) then walk p' from y to v
    simp only [cochainWalkSum, walkToOrientedEdges, SimpleGraph.Walk.darts_cons,
               List.map_cons, List.sum_cons]
    -- First edge contribution: oriented_edge_coboundary gives g(y) - g(u)
    -- Rest of walk: by IH, gives g(v) - g(y)
    -- Total: (g(y) - g(u)) + (g(v) - g(y)) = g(v) - g(u)
    have h_edge := oriented_edge_coboundary K g ⟨_, _, hadj⟩
    rw [h_edge]
    -- The inductive hypothesis rewrites the rest of the walk sum
    simp only [cochainWalkSum, walkToOrientedEdges] at ih
    rw [ih]
    ring

theorem coboundary_walk_sum_zero (K : SimplicialComplex) (g : Cochain K 0)
    {v : K.vertexSet} (C : Walk K v v) : cochainWalkSum K (δ K 0 g) C = 0 := by
  rw [walk_sum_delta_zero_telescopes]
  ring

/-!
Each edge in the cycle contributes 1 to its own indicator sum.

Mathematical content:
- cochainWalkSum K (cycleIndicator K C) C = Σ (oe.sign * cycleIndicator(oe.toSimplex))
- By cycleIndicator_self_contribution, each term equals 1
- Therefore the sum = number of terms = number of darts = C.length
-/
-- Helper: If all elements of a list are 1, the sum equals the length
private lemma sum_eq_length_of_all_one {l : List ℚ} (h : ∀ x ∈ l, x = 1) : l.sum = l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have ha : a = 1 := h a (List.Mem.head as)
    have has : ∀ x ∈ as, x = 1 := fun x hx => h x (List.Mem.tail a hx)
    rw [ha, ih has]
    ring

theorem cycleIndicator_sum_length (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) : cochainWalkSum K (cycleIndicator K C) C = C.length := by
  simp only [cochainWalkSum]
  have h_all_one : ∀ oe ∈ walkToOrientedEdges K C,
      oe.sign * cycleIndicator K C ⟨oe.toSimplex, oe.mem_edges⟩ = 1 :=
    cycleIndicator_self_contribution K C hC
  -- The mapped list has all elements = 1
  have h_map_all_one : ∀ x ∈ (walkToOrientedEdges K C).map
      (fun oe => oe.sign * cycleIndicator K C ⟨oe.toSimplex, oe.mem_edges⟩), x = 1 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨oe, hoe, rfl⟩ := hx
    exact h_all_one oe hoe
  rw [sum_eq_length_of_all_one h_map_all_one]
  simp only [List.length_map, walkToOrientedEdges, List.length_map]
  rw [C.length_darts]

/-! ## Not Coboundary -/

/-!
A cycle indicator is never a coboundary (since cycles have length ≥ 3).

Mathematical content:
- If cycleIndicator K C = δ K 0 g for some g, then:
- cochainWalkSum K (cycleIndicator K C) C = cochainWalkSum K (δ K 0 g) C
- LHS = C.length (by cycleIndicator_sum_length)
- RHS = 0 (by coboundary_walk_sum_zero, since the walk is a cycle v → v)
- So C.length = 0, but cycles have length ≥ 3 (at least 3 edges), contradiction.
-/
theorem cycleIndicator_not_coboundary (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) : ¬IsCoboundary K 1 (cycleIndicator K C) := by
  intro ⟨g, hg⟩
  -- Compute the walk sum two ways:
  have h1 : cochainWalkSum K (cycleIndicator K C) C = C.length := cycleIndicator_sum_length K C hC
  have h2 : cochainWalkSum K (δ K 0 g) C = 0 := coboundary_walk_sum_zero K g C
  -- hg : δ K 0 g = cycleIndicator K C, so substitute into h2
  rw [hg] at h2
  -- Now h1 : ... = C.length and h2 : ... = 0, so C.length = 0
  have h_zero : (C.length : ℚ) = 0 := h1.symm.trans h2
  -- Convert from ℚ to ℕ: (n : ℚ) = 0 ↔ n = 0
  have h_len_zero : C.length = 0 := Nat.cast_injective h_zero
  -- But cycles have length ≥ 3
  have h_len : C.length ≥ 3 := hC.three_le_length
  omega

/-! ## Main Forward Lemmas -/

theorem cycle_implies_h1_nontrivial (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) (hK : hasNoFilledTriangles K) :
    ∃ f : Cochain K 1, IsCocycle K 1 f ∧ ¬IsCoboundary K 1 f :=
  ⟨cycleIndicator K C, cycleIndicator_is_cocycle_hollow K C hC hK, cycleIndicator_not_coboundary K C hC⟩

theorem h1_trivial_implies_oneConnected (K : SimplicialComplex) (hK : hasNoFilledTriangles K)
    (h : H1Trivial K) : OneConnected K := by
  by_contra hnotOC
  rw [not_oneConnected_iff_exists_cycle] at hnotOC
  obtain ⟨v, C, hC⟩ := hnotOC
  obtain ⟨f, hf_coc, hf_not_cob⟩ := cycle_implies_h1_nontrivial K C hC hK
  exact hf_not_cob (h f hf_coc)

end H1Characterization
