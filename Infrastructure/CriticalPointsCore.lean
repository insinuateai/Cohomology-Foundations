/-
# Critical Points Core Proofs

Proves axioms X03, X04, C04 related to misalignment and alignment conditions.

AXIOMS ELIMINATED:
- X03: misalignment_zero_implies_aligned_ax (CriticalPoints.lean:98)
- X04: uniform_misalignment_zero_ax (CriticalPoints.lean:276)
- C04: aligned_implies_H1_trivial (OptimalRepair.lean:156)

NOTE: X04 as stated has no epsilon constraint, but is mathematically false for ε < 0.
All callers use ε > 0, so we prove the constrained version.

SORRIES: 0
AXIOMS: 0
-/

import Perspective.CriticalPoints
import Perspective.AlignmentEquivalence

namespace Infrastructure.CriticalPointsCore

open Foundations (SimplicialComplex H1Trivial)
open Perspective (ValueSystem valueComplex)
open CriticalPoints (misalignment)

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## X04: Uniform values have zero misalignment -/

/--
THEOREM: If all agents have identical values, misalignment is zero.

Proof: All differences are 0, so max(0, 0 - 2ε) = 0 (when ε ≥ 0), and sum of 0s = 0.

NOTE: The original axiom has no ε constraint but is false for ε < 0.
All callers have ε > 0, so this constrained version suffices.
-/
theorem uniform_misalignment_zero_proven {n : ℕ} (epsilon : ℚ) (hε : epsilon ≥ 0) [Nonempty S]
    (baseVal : S → ℚ) :
    misalignment (fun _ : Fin n => (⟨baseVal⟩ : ValueSystem S)) epsilon = 0 := by
  unfold misalignment
  apply Finset.sum_eq_zero
  intro ij _
  split_ifs with h_lt
  · -- Case ij.1 < ij.2: show the squared excess is 0
    -- All systems have identical values, so difference is 0
    have h_diff_zero : ∀ s : S, |(⟨baseVal⟩ : ValueSystem S).values s -
        (⟨baseVal⟩ : ValueSystem S).values s| = 0 := by
      intro s
      simp only [sub_self, abs_zero]
    -- The sup of zeros is zero
    let f := fun s => |(⟨baseVal⟩ : ValueSystem S).values s -
                       (⟨baseVal⟩ : ValueSystem S).values s|
    have h_sup_zero : Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩ f = 0 := by
      apply le_antisymm
      · apply Finset.sup'_le
        intro s _
        simp only [f]
        rw [h_diff_zero s]
      · have h_arb : Classical.arbitrary S ∈ Finset.univ := Finset.mem_univ _
        have h_f_arb : f (Classical.arbitrary S) = 0 := by simp only [f, sub_self, abs_zero]
        rw [← h_f_arb]
        exact Finset.le_sup' f h_arb
    simp only [f] at h_sup_zero
    simp only [h_sup_zero]
    -- max(0, 0 - 2ε) = max(0, -2ε) = 0 for ε ≥ 0
    have h_neg : -2 * epsilon ≤ 0 := by linarith
    have h_max_zero : max 0 (0 - 2 * epsilon) = 0 := by
      have : (0 : ℚ) - 2 * epsilon = -2 * epsilon := by ring
      rw [this]
      exact max_eq_left h_neg
    rw [h_max_zero]
    ring
  · rfl

/-! ## X03: Zero misalignment implies aligned -/

/--
Helper: Zero misalignment implies all pairwise max disagreements are ≤ 2ε.
-/
lemma misalignment_zero_implies_pairwise_bounded {n : ℕ}
    (systems : Fin n → ValueSystem S) (epsilon : ℚ) [Nonempty S]
    (h_zero : misalignment systems epsilon = 0) :
    ∀ i j : Fin n, i < j →
      Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
        (fun s => |(systems i).values s - (systems j).values s|) ≤ 2 * epsilon := by
  intro i j hij
  -- From h_zero, the sum of non-negative terms is 0
  unfold misalignment at h_zero
  -- Each term is non-negative (squared non-negative values)
  have h_nonneg : ∀ x ∈ Finset.univ, (0 : ℚ) ≤
      (if (x : Fin n × Fin n).1 < x.2 then
        let maxDisagree := Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
          fun s => |(systems x.1).values s - (systems x.2).values s|
        let excess := max 0 (maxDisagree - 2 * epsilon)
        excess * excess
      else 0) := by
    intro x _
    split_ifs
    · exact mul_self_nonneg _
    · linarith
  -- Sum is 0 and each term is ≥ 0, so each term is 0
  have h_eq := Finset.sum_eq_zero_iff_of_nonneg h_nonneg
  have h_all_zero := h_eq.mp h_zero
  -- Get the specific term for (i, j)
  have h_ij_zero := h_all_zero (i, j) (Finset.mem_univ _)
  simp only [hij, ↓reduceIte] at h_ij_zero
  -- (excess * excess = 0) → excess = 0
  have h_excess_zero : max 0 (Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
      (fun s => |(systems i).values s - (systems j).values s|) - 2 * epsilon) = 0 := by
    have h_sq := mul_self_eq_zero.mp h_ij_zero
    exact h_sq
  -- max 0 x = 0 → x ≤ 0
  have h_le_zero : Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
      (fun s => |(systems i).values s - (systems j).values s|) - 2 * epsilon ≤ 0 := by
    by_cases h : Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
        (fun s => |(systems i).values s - (systems j).values s|) - 2 * epsilon ≤ 0
    · exact h
    · push_neg at h
      have := max_eq_right_of_lt h
      rw [this] at h_excess_zero
      linarith
  linarith

/--
THEOREM: Zero misalignment implies H¹ is trivial.

Proof:
1. misalignment = 0 → each (max(0, maxDisagree - 2ε))² = 0
2. → maxDisagree ≤ 2ε for each pair
3. → for each pair, ∃ s with |diff| ≤ 2ε (the sup achieves the bound)
4. → valueComplex is complete (all edges exist)
5. → H¹ = 0 by h1_trivial_of_complete_complex
-/
theorem misalignment_zero_implies_aligned_proven {n : ℕ} (hn : n ≥ 1)
    (systems : Fin n → ValueSystem S) (epsilon : ℚ) (hε : epsilon > 0)
    [Nonempty S] :
    misalignment systems epsilon = 0 →
    H1Trivial (valueComplex systems epsilon) := by
  intro h_zero
  -- Get pairwise bounds
  have h_bounded := misalignment_zero_implies_pairwise_bounded systems epsilon h_zero
  -- For each pair i < j, the sup ≤ 2ε means ∃ s with |diff| ≤ 2ε
  -- In fact, ALL s have |diff| ≤ 2ε since sup ≤ 2ε
  have h_complete : ∀ (i j : ℕ) (hi : i < n) (hj : j < n), i < j →
      ∃ s : S, |(systems ⟨i, hi⟩).values s - (systems ⟨j, hj⟩).values s| ≤ 2 * epsilon := by
    intro i j hi hj hij
    -- Use any s; the bound holds because sup ≤ 2ε
    obtain ⟨s⟩ := ‹Nonempty S›
    use s
    have h_sup := h_bounded ⟨i, hi⟩ ⟨j, hj⟩ (by simp only [Fin.mk_lt_mk]; exact hij)
    -- |diff| ≤ sup ≤ 2ε
    have h_le_sup : |(systems ⟨i, hi⟩).values s - (systems ⟨j, hj⟩).values s| ≤
        Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
          (fun s' => |(systems ⟨i, hi⟩).values s' - (systems ⟨j, hj⟩).values s'|) :=
      Finset.le_sup' (fun s' => |(systems ⟨i, hi⟩).values s' - (systems ⟨j, hj⟩).values s'|)
        (Finset.mem_univ s)
    linarith
  -- Apply the complete complex theorem
  by_cases hn2 : n ≥ 2
  · exact Perspective.h1_trivial_of_complete_complex hn2 systems epsilon hε h_complete
  · -- n = 1 case: only one vertex, no edges, H¹ trivially 0
    have hn1 : n = 1 := by omega
    intro f _hf
    -- f is a 1-cochain on a complex with at most 1 vertex
    -- There are no 1-simplices (edges need 2 vertices)
    use fun _ => 0
    funext ⟨e, he⟩
    -- e must be a 1-simplex (edge with 2 elements)
    simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at he
    -- e has card 2, but all elements must be < n = 1, impossible
    obtain ⟨h_in, h_card⟩ := he
    simp only [valueComplex, Set.mem_setOf_eq] at h_in
    -- e has at least 2 elements (card = 2), and all are < 1
    -- This is a contradiction
    have h_vertices := h_in.1
    -- e.card = 2 means e has at least 2 elements
    have h_two := Finset.one_lt_card.mp (by rw [h_card]; norm_num : 1 < e.card)
    obtain ⟨a, ha, b, hb, hab⟩ := h_two
    have ha' := h_vertices a ha
    have hb' := h_vertices b hb
    -- a < 1 and b < 1 means a = b = 0, contradicting a ≠ b
    subst hn1
    have ha0 : a = 0 := Nat.lt_one_iff.mp ha'
    have hb0 : b = 0 := Nat.lt_one_iff.mp hb'
    exact False.elim (hab (ha0.trans hb0.symm))

/-! ## C04: Aligned implies H¹ trivial -/

/--
THEOREM: If all pairwise differences are bounded by 2ε, then H¹ is trivial.

This is a direct application of the complete complex theorem.
-/
theorem aligned_implies_H1_trivial_proven {n : ℕ} (systems : Fin n → ValueSystem S)
    (epsilon : ℚ) (hε : epsilon > 0) [Nonempty S]
    (h_aligned : ∀ i j : Fin n, ∀ s : S,
      |(systems i).values s - (systems j).values s| ≤ 2 * epsilon) :
    Foundations.H1Trivial (valueComplex systems epsilon) := by
  by_cases hn : n ≥ 2
  · -- For n ≥ 2, use the complete complex theorem
    have h_complete : ∀ (i j : ℕ) (hi : i < n) (hj : j < n), i < j →
        ∃ s : S, |(systems ⟨i, hi⟩).values s - (systems ⟨j, hj⟩).values s| ≤ 2 * epsilon := by
      intro i j hi hj _
      obtain ⟨s⟩ := ‹Nonempty S›
      use s
      exact h_aligned ⟨i, hi⟩ ⟨j, hj⟩ s
    exact Perspective.h1_trivial_of_complete_complex hn systems epsilon hε h_complete
  · -- For n < 2, the complex has ≤ 1 vertex, so no 1-simplices
    push_neg at hn
    intro f _hf
    use fun _ => 0
    funext ⟨e, he⟩
    simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] at he
    simp only [valueComplex, Set.mem_setOf_eq] at he
    -- e has card 2 but all vertices < n < 2, impossible
    obtain ⟨⟨h_vertices, _⟩, h_card⟩ := he
    have h_two := Finset.one_lt_card.mp (by rw [h_card]; norm_num : 1 < e.card)
    obtain ⟨a, ha, b, hb, hab⟩ := h_two
    have ha' := h_vertices a ha
    have hb' := h_vertices b hb
    -- a < n and b < n with n < 2, so a, b ∈ {0, 1} but n ≤ 1 means a, b < 1 or just < 2
    -- Since n < 2, we have n ≤ 1, so a < n ≤ 1 and b < n ≤ 1
    have hn' : n ≤ 1 := Nat.lt_succ_iff.mp hn
    have ha0 : a = 0 := Nat.lt_one_iff.mp (Nat.lt_of_lt_of_le ha' hn')
    have hb0 : b = 0 := Nat.lt_one_iff.mp (Nat.lt_of_lt_of_le hb' hn')
    exact False.elim (hab (ha0.trans hb0.symm))

end Infrastructure.CriticalPointsCore
