/-
# Uniform Certification Infrastructure

This file provides provable alternatives to axioms that require the
existential-to-universal gap to be bridged.

The core issue with axioms like `aligned_zero_curvature_ax`:
- Edge condition (valueComplex): ∃ s, |v_i(s) - v_j(s)| ≤ 2ε
- Axiom needs: ∀ s, |v_i(s) - v_j(s)| ≤ 2ε

We provide lemmas under stronger conditions:
1. `ValueAligned` - the ∀s bound holds directly
2. `UniformlyCertified` - all pairs agree on the SAME situation

AXIOMS ELIMINATED: 0
SORRIES: 0
-/

import Perspective.Curvature
import Perspective.CriticalPoints
import Perspective.AlignmentEquivalence

namespace UniformCertification

open Foundations (SimplicialComplex H1Trivial)
open Perspective (ValueSystem valueComplex ValueAligned)
open Curvature (pairwiseCurvature)
open CriticalPoints (misalignment misalignmentGradient gradientNorm)
open H1Characterization (oneSkeleton)

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## Part 1: Uniform Certification Definition -/

/--
A system has uniform certification if all pairs agree on the SAME situation.
This is stronger than the edge condition (which only requires existence).
-/
def UniformlyCertified {n : ℕ} (systems : Fin n → ValueSystem S) (ε : ℚ) : Prop :=
  ∃ s₀ : S, ∀ i j : Fin n, |(systems i).values s₀ - (systems j).values s₀| ≤ 2 * ε

/--
Uniform certification implies all edges exist in the value complex.
-/
theorem uniformly_certified_implies_edges {n : ℕ} (systems : Fin n → ValueSystem S)
    (ε : ℚ) (h_unif : UniformlyCertified systems ε) :
    ∀ i j : Fin n, i.val < j.val →
      ({i.val, j.val} : Finset ℕ) ∈ (valueComplex systems ε).simplices := by
  intro i j hij
  obtain ⟨s₀, h_bound⟩ := h_unif
  simp only [valueComplex, Set.mem_setOf_eq]
  constructor
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact i.isLt
    · exact j.isLt
  · intro a b ha hb hab ha_lt hb_lt
    use s₀
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha_eq | ha_eq <;> rcases hb with hb_eq | hb_eq
    · -- a = i.val and b = i.val, contradicts a < b
      subst ha_eq hb_eq; omega
    · -- a = i.val, b = j.val
      subst ha_eq hb_eq
      exact h_bound ⟨i.val, ha_lt⟩ ⟨j.val, hb_lt⟩
    · -- a = j.val, b = i.val
      subst ha_eq hb_eq
      rw [abs_sub_comm]
      exact h_bound ⟨i.val, hb_lt⟩ ⟨j.val, ha_lt⟩
    · -- a = j.val and b = j.val, contradicts a < b
      subst ha_eq hb_eq; omega

/-! ## Part 2: ValueAligned Implies Zero Metrics -/

/--
ValueAligned implies the maximum disagreement for each pair is bounded by 2ε.
This is the key bridge from the universal bound to zero metrics.
-/
theorem value_aligned_max_disagreement_bounded {n : ℕ}
    (systems : Fin n → ValueSystem S) (ε : ℚ) [Nonempty S]
    (h_aligned : ValueAligned systems ε) (i j : Fin n) :
    Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
      (fun s => |(systems i).values s - (systems j).values s|) ≤ 2 * ε := by
  apply Finset.sup'_le
  intro s _
  exact h_aligned i j s

/--
ValueAligned implies zero pairwise curvature.

This is the provable version of `aligned_zero_curvature_ax` under the
stronger ValueAligned hypothesis.
-/
theorem value_aligned_zero_curvature {n : ℕ} (systems : Fin n → ValueSystem S)
    (ε : ℚ) (_hε : ε > 0) [Nonempty S]
    (h_aligned : ValueAligned systems ε) :
    ∀ i j : Fin n, pairwiseCurvature systems i j ε = 0 := by
  intro i j
  unfold pairwiseCurvature
  simp only
  have h_max_le := value_aligned_max_disagreement_bounded systems ε h_aligned i j
  split_ifs with h_gt
  · -- Case: maxDisagree > 2ε contradicts h_max_le
    exfalso
    linarith
  · -- Case: maxDisagree ≤ 2ε, curvature = 0
    rfl

/--
ValueAligned implies zero misalignment.

This is the provable version of `aligned_implies_zero_misalignment_ax` under
the stronger ValueAligned hypothesis.
-/
theorem value_aligned_zero_misalignment {n : ℕ}
    (systems : Fin n → ValueSystem S) (ε : ℚ) (_hε : ε > 0) [Nonempty S]
    (h_aligned : ValueAligned systems ε) :
    misalignment systems ε = 0 := by
  unfold misalignment
  apply Finset.sum_eq_zero
  intro ⟨i, j⟩ _
  split_ifs with h_lt
  · -- For pair (i, j) with i < j, show squared excess = 0
    have h_max := value_aligned_max_disagreement_bounded systems ε h_aligned i j
    -- The excess is max(0, maxDisagree - 2ε) = 0 since maxDisagree ≤ 2ε
    have h_excess_zero : max 0 (Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
        (fun s => |(systems i).values s - (systems j).values s|) - 2 * ε) = 0 := by
      apply max_eq_left
      linarith
    simp only [h_excess_zero, mul_zero]
  · rfl

/--
ValueAligned implies zero gradient norm.

This is the provable version of `gradient_zero_when_aligned_ax` under
the stronger ValueAligned hypothesis.
-/
theorem value_aligned_zero_gradient {n : ℕ}
    (systems : Fin n → ValueSystem S) (ε : ℚ) [Nonempty S]
    (h_aligned : ValueAligned systems ε) :
    gradientNorm systems ε = 0 := by
  unfold gradientNorm misalignmentGradient
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro s _
  -- The gradient at (i, s) is a sum over j of terms that are 0 when |diff| ≤ 2ε
  have h_inner_zero : (∑ j : Fin n, if i ≠ j then
      let diff := (systems i).values s - (systems j).values s
      let absDiff := |diff|
      if absDiff > 2 * ε then 2 * (absDiff - 2 * ε) * (if diff > 0 then 1 else -1)
      else 0 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases h_ne : i ≠ j
    · -- i ≠ j, so first if branch is entered
      rw [if_pos h_ne]
      -- Now check the inner condition
      have h_bound := h_aligned i j s
      -- Since |(systems i).values s - (systems j).values s| ≤ 2 * ε,
      -- the condition absDiff > 2 * ε is false
      have h_not_gt : ¬(|(systems i).values s - (systems j).values s| > 2 * ε) := not_lt.mpr h_bound
      simp only [h_not_gt, ↓reduceIte]
    · -- i = j, so first if branch is not entered
      rw [if_neg h_ne]
  simp only [h_inner_zero, abs_zero]

/-! ## Part 3: Uniform Certification Implies H1Trivial -/

/--
Uniform certification implies all edges exist, making the complex "complete".
-/
theorem uniform_implies_complete_edges {n : ℕ} (_hn : n ≥ 2)
    (systems : Fin n → ValueSystem S) (ε : ℚ) (_hε : ε > 0) [Nonempty S]
    (h_unif : UniformlyCertified systems ε) :
    ∀ i j : ℕ, (hi : i < n) → (hj : j < n) → i < j →
      ∃ s : S, |(systems ⟨i, hi⟩).values s - (systems ⟨j, hj⟩).values s| ≤ 2 * ε := by
  intro i j hi hj _hij
  obtain ⟨s₀, h_bound⟩ := h_unif
  exact ⟨s₀, h_bound ⟨i, hi⟩ ⟨j, hj⟩⟩

/--
Uniform certification implies H1Trivial via complete complex.

When all pairs agree on a common situation, the value complex is complete
(all possible edges exist), and a complete complex has H¹ = 0.
-/
theorem uniform_implies_h1_trivial {n : ℕ} (hn : n ≥ 2)
    (systems : Fin n → ValueSystem S) (ε : ℚ) (hε : ε > 0) [Nonempty S]
    (h_unif : UniformlyCertified systems ε) :
    H1Trivial (valueComplex systems ε) := by
  apply Perspective.h1_trivial_of_complete_complex hn systems ε hε
  exact uniform_implies_complete_edges hn systems ε hε h_unif

/-! ## Part 4: Relationships Between Conditions -/

/--
ValueAligned implies UniformlyCertified (for every situation).
-/
theorem value_aligned_implies_uniformly_certified {n : ℕ}
    (systems : Fin n → ValueSystem S) (ε : ℚ) [Nonempty S]
    (h_aligned : ValueAligned systems ε) :
    UniformlyCertified systems ε := by
  use Classical.arbitrary S
  intro i j
  exact h_aligned i j _

/--
ValueAligned implies H1Trivial (via uniform certification).
-/
theorem value_aligned_implies_h1_trivial {n : ℕ} (hn : n ≥ 2)
    (systems : Fin n → ValueSystem S) (ε : ℚ) (hε : ε > 0) [Nonempty S]
    (h_aligned : ValueAligned systems ε) :
    H1Trivial (valueComplex systems ε) := by
  apply uniform_implies_h1_trivial hn systems ε hε
  exact value_aligned_implies_uniformly_certified systems ε h_aligned

/-! ## Part 5: Summary -/

/-
## Comparison to Original Axioms

Original axioms (in Perspective/):
- `aligned_zero_curvature_ax`: H1Trivial + Connected → curvature = 0
- `aligned_implies_zero_misalignment_ax`: H1Trivial + Connected → misalignment = 0
- `gradient_zero_when_aligned_ax`: H1Trivial + Connected → gradient = 0

These have a gap: H1Trivial only guarantees ∃s agreement, not ∀s agreement.

Our provable alternatives:
- `value_aligned_zero_curvature`: ValueAligned → curvature = 0
- `value_aligned_zero_misalignment`: ValueAligned → misalignment = 0
- `value_aligned_zero_gradient`: ValueAligned → gradient = 0

These work because ValueAligned directly gives the ∀s bound needed.

Usage: When you have `ValueAligned` (the universal bound), use these lemmas
instead of the axioms. The axioms remain for the case where you only have
`H1Trivial` (the existential condition from edge existence).
-/

end UniformCertification
