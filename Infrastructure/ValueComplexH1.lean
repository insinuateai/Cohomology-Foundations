/-
# ValueComplex to H1Trivial Bridge Infrastructure

Bridge lemmas connecting `valueComplex` (agent-based) to `Foundations.H1Trivial` (cohomology).

## Main Results

1. `valueComplex_vertexSet_nonempty` - Vertices exist when n ≥ 1
2. `valueComplex_hasNoFilledTriangles` - ValueComplex has no 2-simplices when n < 3
3. `disagreement_exceeds_threshold_implies_no_edge` - Large disagreement → no edge
4. `valueComplex_oneSkeleton_acyclic_implies_H1Trivial` - Acyclic 1-skeleton → H¹ = 0

SORRIES: 0
AXIOMS: 0

Author: Infrastructure Team
Date: February 2026
-/

import Foundations.Cohomology
import Perspective.ValueComplex
import H1Characterization.Characterization
import H1Characterization.ForestCoboundary
import Infrastructure.CompleteComplexH1

namespace Infrastructure.ValueComplexH1

open Foundations (Cochain IsCocycle IsCoboundary H1Trivial coboundary Simplex SimplicialComplex Coeff)
open Foundations.SimplicialComplex (ksimplices vertexSet)
open Perspective (ValueSystem valueComplex)
open H1Characterization (OneConnected oneSkeleton hasNoFilledTriangles acyclic_implies_h1_trivial)

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## Section 1: Vertex Set Nonempty -/

/-- A vertex {v} is in the valueComplex vertex set when v < n -/
theorem valueComplex_vertex_in_vertexSet {n : ℕ} (systems : Fin n → ValueSystem S) (ε : ℚ)
    (v : ℕ) (hv : v < n) :
    v ∈ (valueComplex systems ε).vertexSet := by
  rw [Foundations.SimplicialComplex.mem_vertexSet_iff]
  simp only [Foundations.Simplex.vertex]
  exact Infrastructure.CompleteComplexH1.valueComplex_vertex_mem systems ε v hv

/-- The valueComplex has nonempty vertex set when n ≥ 1 -/
instance valueComplex_vertexSet_nonempty {n : ℕ} [NeZero n]
    (systems : Fin n → ValueSystem S) (ε : ℚ) :
    Nonempty (valueComplex systems ε).vertexSet := by
  have h0 : 0 < n := NeZero.pos n
  exact ⟨⟨0, valueComplex_vertex_in_vertexSet systems ε 0 h0⟩⟩

/-! ## Section 2: Edge Existence Lemmas -/

/-- An edge {a,b} is NOT in valueComplex when all disagreements exceed 2ε -/
theorem disagreement_exceeds_threshold_implies_no_edge {n : ℕ}
    (systems : Fin n → ValueSystem S) (ε : ℚ) [Nonempty S]
    (a b : ℕ) (ha : a < n) (hb : b < n) (hab : a < b)
    (h_disagree : ∀ s : S, |(systems ⟨a, ha⟩).values s - (systems ⟨b, hb⟩).values s| > 2 * ε) :
    ({a, b} : Simplex) ∉ (valueComplex systems ε).simplices := by
  intro h_in
  simp only [valueComplex, Set.mem_setOf_eq] at h_in
  obtain ⟨_, h_agree⟩ := h_in
  -- h_agree says for all pairs, there exists s with |diff| ≤ 2ε
  -- Apply it to a, b
  have h_ab_agree := h_agree a b (by simp) (by simp) hab ha hb
  obtain ⟨s, hs⟩ := h_ab_agree
  -- hs : |(systems ⟨a, ha⟩).values s - (systems ⟨b, hb⟩).values s| ≤ 2 * ε
  -- h_disagree s : |(systems ⟨a, ha⟩).values s - (systems ⟨b, hb⟩).values s| > 2 * ε
  have := h_disagree s
  linarith

/-- An edge {a,b} is in valueComplex iff there exists s with |diff| ≤ 2ε -/
theorem valueComplex_edge_mem_iff {n : ℕ}
    (systems : Fin n → ValueSystem S) (ε : ℚ)
    (a b : ℕ) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    ({a, b} : Simplex) ∈ (valueComplex systems ε).simplices ↔
    ∃ s : S, |(systems ⟨a, ha⟩).values s - (systems ⟨b, hb⟩).values s| ≤ 2 * ε := by
  constructor
  · intro h_in
    simp only [valueComplex, Set.mem_setOf_eq] at h_in
    obtain ⟨_, h_agree⟩ := h_in
    -- Need to handle both cases: a < b and b < a
    cases Nat.lt_or_gt_of_ne hab with
    | inl h_lt => exact h_agree a b (by simp) (by simp) h_lt ha hb
    | inr h_gt =>
      have h_swap := h_agree b a (by simp) (by simp) h_gt hb ha
      obtain ⟨s, hs⟩ := h_swap
      use s
      rw [abs_sub_comm]
      exact hs
  · intro ⟨s, hs⟩
    simp only [valueComplex, Set.mem_setOf_eq]
    constructor
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> assumption
    · intro i j hi hj hij hi_lt hj_lt
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      -- Use the given s to satisfy the agreement condition for any pair
      use s
      -- hi : i = a ∨ i = b, hj : j = a ∨ j = b
      rcases hi with hi_a | hi_b <;> rcases hj with hj_a | hj_b
      · -- i = a, j = a: contradicts hij
        omega
      · -- i = a, j = b
        subst hi_a hj_b
        exact hs
      · -- i = b, j = a
        subst hi_b hj_a
        rw [abs_sub_comm]
        exact hs
      · -- i = b, j = b: contradicts hij
        omega

/-! ## Section 3: HasNoFilledTriangles for Small Complexes -/

/-- ValueComplex has no 2-simplices when n < 3 (too few vertices for triangles) -/
theorem valueComplex_hasNoFilledTriangles_of_lt_three {n : ℕ}
    (systems : Fin n → ValueSystem S) (ε : ℚ) (hn : n < 3) :
    hasNoFilledTriangles (valueComplex systems ε) := by
  -- hasNoFilledTriangles means ksimplices 2 = ∅
  simp only [hasNoFilledTriangles]
  ext σ
  simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
             not_and]
  intro h_in h_card
  -- σ ∈ valueComplex.simplices means all vertices < n
  simp only [valueComplex, Set.mem_setOf_eq] at h_in
  -- σ.card = 3 but all vertices must be < n < 3, and they must be distinct
  have ⟨a, b, c, hab, hac, hbc, heq⟩ := Finset.card_eq_three.mp h_card
  rw [heq] at h_in
  have ha_lt := h_in.1 a (by simp)
  have hb_lt := h_in.1 b (by simp)
  have hc_lt := h_in.1 c (by simp)
  -- n < 3 means n ∈ {0, 1, 2}. We can't have 3 distinct values all < n.
  interval_cases n
  · -- n = 0: no naturals < 0
    exact Nat.not_lt_zero a ha_lt
  · -- n = 1: only 0 < 1, so a = b = c = 0, contradicting distinctness
    have ha0 : a = 0 := Nat.lt_one_iff.mp ha_lt
    have hb0 : b = 0 := Nat.lt_one_iff.mp hb_lt
    exact hab (ha0.trans hb0.symm)
  · -- n = 2: only 0, 1 < 2, can't have 3 distinct values all different
    -- a, b, c ∈ {0, 1} but they must be distinct (hab, hac, hbc)
    interval_cases a <;> interval_cases b <;> interval_cases c <;>
      first | exact hab rfl | exact hac rfl | exact hbc rfl

/-! ## Section 4: The Key Bridge Lemma -/

/-- **THE KEY LEMMA**: If valueComplex has acyclic 1-skeleton, then H¹ = 0.

This uses the general theorem `acyclic_implies_h1_trivial` from H1Characterization.
Note: This does NOT require hasNoFilledTriangles - that's only needed for the
converse direction (H¹=0 → acyclic).
-/
theorem valueComplex_oneSkeleton_acyclic_implies_H1Trivial {n : ℕ} [NeZero n]
    (systems : Fin n → ValueSystem S) (ε : ℚ)
    (hacyclic : (oneSkeleton (valueComplex systems ε)).IsAcyclic) :
    H1Trivial (valueComplex systems ε) := by
  have _ := valueComplex_vertexSet_nonempty systems ε
  exact acyclic_implies_h1_trivial (valueComplex systems ε) hacyclic

/-! ## Section 5: Additional Useful Lemmas -/

/-- The 1-skeleton of valueComplex is acyclic iff it's a forest (no cycles) -/
theorem valueComplex_acyclic_iff_no_cycles {n : ℕ} [NeZero n]
    (systems : Fin n → ValueSystem S) (ε : ℚ) :
    (oneSkeleton (valueComplex systems ε)).IsAcyclic ↔
    ∀ v : (valueComplex systems ε).vertexSet,
      ∀ p : (oneSkeleton (valueComplex systems ε)).Walk v v, ¬p.IsCycle := Iff.rfl

/-- Complete valueComplex (all edges exist) has trivial H¹.
    This follows from `complete_complex_coboundary_proven`. -/
theorem valueComplex_complete_H1Trivial {n : ℕ} (hn : n ≥ 1)
    (systems : Fin n → ValueSystem S) (ε : ℚ)
    (h_complete : ∀ (i j : ℕ) (hi : i < n) (hj : j < n), i < j →
      ∃ s : S, |(systems ⟨i, hi⟩).values s - (systems ⟨j, hj⟩).values s| ≤ 2 * ε) :
    H1Trivial (valueComplex systems ε) := by
  intro f hf
  exact Infrastructure.CompleteComplexH1.complete_complex_coboundary_proven hn systems ε f hf h_complete

end Infrastructure.ValueComplexH1
