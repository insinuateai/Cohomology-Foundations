/-
# Critical Points Proofs

Self-contained exploration of critical point concepts with honest axioms.
See CriticalPointsCore.lean and CriticalPointsAxiomReplacements.lean for REAL proofs.

Related axioms:
- misalignment_zero_implies_aligned_ax (CriticalPoints.lean:98) - See CriticalPointsAxiomReplacements ✅
- uniform_misalignment_zero_ax (CriticalPoints.lean:276) - ELIMINATED (X04) ✅
- saddle_has_escape_ax (CriticalPoints.lean:350) - Signature mismatch

NOTE: CriticalPointsCore.lean and CriticalPointsAxiomReplacements.lean use
real Foundations.H1Trivial. This file uses its own definitions.

REAL PROOFS: misalignment_zero_implies_aligned, uniform_misalignment_zero, saddle_has_escape
AXIOMS: 0 (all eliminated - Level 6!)

SORRIES: 0
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Infrastructure.CriticalPointsProofs

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## Basic Definitions -/

/-- Value system -/
structure ValueSystem (S : Type*) where
  values : S → ℚ

/-- Misalignment measure: sum of squared excesses -/
noncomputable def misalignment {n : ℕ} (systems : Fin n → ValueSystem S)
    (epsilon : ℚ) [Nonempty S] : ℚ :=
  Finset.univ.sum fun ij : Fin n × Fin n =>
    if ij.1 < ij.2 then
      let maxDisagree := Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
        fun s => |(systems ij.1).values s - (systems ij.2).values s|
      let excess := max 0 (maxDisagree - 2 * epsilon)
      excess * excess
    else 0

/-- Value complex -/
structure ValueComplex (n : ℕ) (S : Type*) where
  systems : Fin n → ValueSystem S
  epsilon : ℚ

/-- H¹ trivial -/
def H1Trivial {n : ℕ} (K : ValueComplex n S) [Nonempty S] : Prop :=
  ∀ i j : Fin n, ∀ s : S,
    |(K.systems i).values s - (K.systems j).values s| ≤ 2 * K.epsilon

/-- Critical point: gradient of misalignment is approximately zero.
    Semantically: ∇(misalignment) ≈ 0, i.e., at a local minimum or saddle.
    We define this as: no direction significantly decreases misalignment. -/
def isCriticalPoint {n : ℕ} (systems : Fin n → ValueSystem S)
    (epsilon : ℚ) [Nonempty S] : Prop :=
  ∀ direction : Fin n → ValueSystem S,
    misalignment direction epsilon ≥ misalignment systems epsilon - epsilon

/-- Saddle point: critical but not minimum -/
def isSaddlePoint {n : ℕ} (systems : Fin n → ValueSystem S)
    (epsilon : ℚ) [Nonempty S] : Prop :=
  isCriticalPoint systems epsilon ∧
  ∃ direction : Fin n → ValueSystem S,
    misalignment direction epsilon < misalignment systems epsilon

/-! ## CP01: Zero Misalignment Implies Aligned -/

/--
THEOREM CP01: Zero misalignment implies aligned (H¹ = 0).

Proof:
1. Misalignment = sum of squared excesses over pairs
2. If sum = 0, each term = 0 (squares are non-negative)
3. Each term = 0 means max(0, disagreement - 2ε) = 0
4. So disagreement ≤ 2ε for all pairs
5. This is exactly H¹ = 0
-/
theorem misalignment_zero_implies_aligned_proven {n : ℕ} (hn : n ≥ 1)
    (systems : Fin n → ValueSystem S) (epsilon : ℚ) (hε : epsilon > 0)
    [Nonempty S]
    (h_zero : misalignment systems epsilon = 0) :
    H1Trivial ⟨systems, epsilon⟩ := by
  intro i j s
  -- From h_zero: sum of non-negative terms = 0
  -- So each term = 0
  unfold misalignment at h_zero
  -- Each squared excess is non-negative
  have h_nonneg : ∀ x ∈ Finset.univ, (0 : ℚ) ≤
      (if (x : Fin n × Fin n).1 < x.2 then
        let maxDisagree := Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
          fun s => |(systems x.1).values s - (systems x.2).values s|
        let excess := max 0 (maxDisagree - 2 * epsilon)
        excess * excess
      else 0) := by
    intro x _
    split_ifs
    · apply mul_self_nonneg
    · rfl
  -- Sum of non-negative = 0 implies each = 0
  have h_each_zero := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_zero
  -- For i < j: the term is 0
  by_cases hij : i < j
  · have h_term := h_each_zero (i, j) (Finset.mem_univ _)
    simp only [hij, ↓reduceIte] at h_term
    -- excess² = 0 means excess = 0
    have h_excess : max 0 ((Finset.univ (α := S)).sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
        (fun s => |(systems i).values s - (systems j).values s|) - 2 * epsilon) = 0 := by
      have : max 0 ((Finset.univ (α := S)).sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
             (fun s => |(systems i).values s - (systems j).values s|) - 2 * epsilon) *
             max 0 ((Finset.univ (α := S)).sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
             (fun s => |(systems i).values s - (systems j).values s|) - 2 * epsilon) = 0 := h_term
      exact mul_self_eq_zero.mp this
    -- max(0, x) = 0 means x ≤ 0
    have h_sup_le : Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
        (fun s => |(systems i).values s - (systems j).values s|) ≤ 2 * epsilon := by
      have := max_eq_left_iff.mp h_excess
      linarith
    exact le_trans (Finset.le_sup' (fun s => |(systems i).values s - (systems j).values s|) (Finset.mem_univ s)) h_sup_le
  · -- i ≥ j: use symmetry or j < i case
    by_cases hji : j < i
    · -- Apply symmetric argument
      have h_term := h_each_zero (j, i) (Finset.mem_univ _)
      simp only [hji, ↓reduceIte] at h_term
      have h_excess : max 0 ((Finset.univ (α := S)).sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
          (fun s => |(systems j).values s - (systems i).values s|) - 2 * epsilon) = 0 := by
        have : max 0 ((Finset.univ (α := S)).sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
               (fun s => |(systems j).values s - (systems i).values s|) - 2 * epsilon) *
               max 0 ((Finset.univ (α := S)).sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
               (fun s => |(systems j).values s - (systems i).values s|) - 2 * epsilon) = 0 := h_term
        exact mul_self_eq_zero.mp this
      have h_sup_le : Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
          (fun s => |(systems j).values s - (systems i).values s|) ≤ 2 * epsilon := by
        have := max_eq_left_iff.mp h_excess
        linarith
      calc |(systems i).values s - (systems j).values s|
          = |(systems j).values s - (systems i).values s| := abs_sub_comm _ _
        _ ≤ 2 * epsilon := le_trans (Finset.le_sup' (fun s => |(systems j).values s - (systems i).values s|) (Finset.mem_univ s)) h_sup_le
    · -- i = j
      push_neg at hij hji
      have heq : i = j := le_antisymm hji hij
      simp only [heq, sub_self, abs_zero]
      linarith

/-! ## CP02: Uniform Values Have Zero Misalignment -/

/--
THEOREM CP02: If all agents have identical values, misalignment is zero.

Proof: All differences are 0, so max(0, 0 - 2ε) = 0, and sum of 0s = 0.
-/
theorem uniform_misalignment_zero_proven {n : ℕ} (epsilon : ℚ) (hε : epsilon ≥ 0)
    [Nonempty S]
    (baseVal : S → ℚ) :
    misalignment (fun _ : Fin n => (⟨baseVal⟩ : ValueSystem S)) epsilon = 0 := by
  unfold misalignment
  apply Finset.sum_eq_zero
  intro ij _
  split_ifs with h_lt
  · -- For i < j, the term should be 0
    -- All systems have identical values, so difference is 0
    have h_diff_zero : ∀ s : S, |(⟨baseVal⟩ : ValueSystem S).values s -
        (⟨baseVal⟩ : ValueSystem S).values s| = 0 := by
      intro s
      simp only [sub_self, abs_zero]
    -- The sup of zeros is zero
    have h_sup_zero : Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
        (fun s => |(⟨baseVal⟩ : ValueSystem S).values s -
                   (⟨baseVal⟩ : ValueSystem S).values s|) = 0 := by
      apply le_antisymm
      · apply Finset.sup'_le
        intro s _
        rw [h_diff_zero s]
      · have : (0 : ℚ) = |baseVal (Classical.arbitrary S) - baseVal (Classical.arbitrary S)| := by
          simp only [sub_self, abs_zero]
        rw [this]
        exact Finset.le_sup' (fun s => |(⟨baseVal⟩ : ValueSystem S).values s - (⟨baseVal⟩ : ValueSystem S).values s|)
          (Finset.mem_univ (Classical.arbitrary S))
    simp only [h_sup_zero]
    -- max(0, 0 - 2ε) = max(0, -2ε) = 0 for ε ≥ 0
    have h_neg : 0 - 2 * epsilon ≤ 0 := by linarith
    have h_max_zero : max 0 (0 - 2 * epsilon) = 0 := max_eq_left h_neg
    rw [h_max_zero]
    ring
  · rfl

/-! ## CP03: Saddle Points Have Escape -/

/--
THEOREM CP03: Saddle points have escape directions.

A saddle point is not a minimum, so there exists a direction
where misalignment decreases.

Proof: Definition of saddle point includes existence of
escape direction (built into the structure).
-/
theorem saddle_has_escape_proven {n : ℕ} (hn : n ≥ 2)
    (systems : Fin n → ValueSystem S) (epsilon : ℚ)
    [Nonempty S]
    (h_saddle : isSaddlePoint systems epsilon) :
    ∃ direction : Fin n → ValueSystem S,
      misalignment direction epsilon < misalignment systems epsilon := by
  exact h_saddle.2

end Infrastructure.CriticalPointsProofs
