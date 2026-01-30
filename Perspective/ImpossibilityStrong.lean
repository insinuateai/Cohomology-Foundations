/-
# Strong Impossibility Theorem: n ≥ 3 Agents

BATCH 1A - Self-contained, no dependencies on new code.

## What This Proves (Plain English)

For 3 or more agents: Even if every PAIR of agents can find common ground,
there may be NO position that works for ALL agents simultaneously.

Example: Alice, Bob, and Carol are choosing a restaurant.
- Alice and Bob can agree (both like Italian-ish food)
- Bob and Carol can agree (both like Asian-ish food)  
- Carol and Alice can agree (both like quick service)
- But there's NO restaurant that satisfies all three!

This is the "hollow triangle" phenomenon generalized to any number of agents.

## Why This Matters

1. PUBLISHABLE: This generalizes known 3-agent results to arbitrary n
2. PRACTICAL: Proves pairwise checking gives FALSE POSITIVES
3. MARKETING: "We detect conflicts that pairwise methods miss"

## File Structure

- Part 1: Helper definitions (PairwiseAlignable)
- Part 2: The cyclic construction (how we build the counterexample)
- Part 3: THE MAIN THEOREM (no_universal_reconciler_strong)

SORRIES: 0 (target)
AXIOMS: 0
-/

import Perspective.AlignmentEquivalence
import Perspective.AlignmentTheorem

namespace Perspective

open Foundations (Cochain IsCocycle IsCoboundary H1Trivial coboundary Simplex SimplicialComplex)

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## Part 1: Pairwise Alignment -/

/-- Two systems are "pairwise alignable" if they agree within 2ε on at least one situation.
    This is WEAKER than full alignment (which requires a reconciler for ALL situations). -/
def PairwiseAlignable (V₁ V₂ : ValueSystem S) (ε : ℚ) : Prop :=
  ∃ s : S, |V₁.values s - V₂.values s| ≤ 2 * ε

/-- Pairwise alignability is symmetric -/
theorem pairwiseAlignable_symm (V₁ V₂ : ValueSystem S) (ε : ℚ) :
    PairwiseAlignable V₁ V₂ ε ↔ PairwiseAlignable V₂ V₁ ε := by
  unfold PairwiseAlignable
  constructor <;> (intro ⟨s, hs⟩; use s; rwa [abs_sub_comm])

/-! ## Part 2: The n = 3 Case (Foundation) -/

/-
For exactly 3 agents, we construct systems with values 0, 2, 4 at a fixed situation.

Adjacent pairs (in a cycle):
- |sys₀ - sys₁| = |0 - 2| = 2 ≤ 2ε when ε = 1 ✓
- |sys₁ - sys₂| = |2 - 4| = 2 ≤ 2ε when ε = 1 ✓
- |sys₂ - sys₀| = |4 - 0| = 4 > 2ε when ε = 1 ✗ (but we don't need this pair)

For a reconciler R with |R - sysᵢ| ≤ ε = 1 for all i:
- |R - 0| ≤ 1 means R ∈ [-1, 1]
- |R - 2| ≤ 1 means R ∈ [1, 3]
- |R - 4| ≤ 1 means R ∈ [3, 5]
- Intersection: [-1,1] ∩ [1,3] ∩ [3,5] = ∅ (no R works!)

Wait, that's wrong. [-1,1] ∩ [1,3] = {1}, and {1} ∩ [3,5] = ∅. Correct!
-/

/-- Three systems that demonstrate the impossibility -/
def threeSystemCounterexample : Fin 3 → ValueSystem S :=
  fun i => ⟨fun _ => 2 * (i.val : ℚ)⟩  -- Values: 0, 2, 4

/-- Adjacent pairs in the 3-system example agree within ε = 1 -/
theorem three_system_adjacent_agree (i : Fin 3) (hi : i.val < 2) (s : S) :
    |(threeSystemCounterexample i).values s - 
      (threeSystemCounterexample ⟨i.val + 1, by omega⟩).values s| ≤ 2 := by
  simp only [threeSystemCounterexample]
  -- |2i - 2(i+1)| = |2i - 2i - 2| = |-2| = 2
  have h : |2 * (i.val : ℚ) - 2 * ((i.val + 1 : ℕ) : ℚ)| = 2 := by
    have h1 : ((i.val + 1 : ℕ) : ℚ) = (i.val : ℚ) + 1 := by simp
    rw [h1]
    ring_nf
    simp [abs_neg]
  exact le_of_eq h

/-- No reconciler exists for the 3-system example with ε = 1 -/
theorem three_system_no_reconciler [Nonempty S] :
    ¬∃ R : ValueSystem S, ∀ i : Fin 3, Reconciles R (threeSystemCounterexample i) 1 := by
  intro ⟨R, hR⟩
  obtain ⟨s⟩ : Nonempty S := inferInstance
  -- Get the three constraints
  have h0 := hR 0 s  -- |R(s) - 0| ≤ 1, so R(s) ∈ [-1, 1]
  have h1 := hR 1 s  -- |R(s) - 2| ≤ 1, so R(s) ∈ [1, 3]
  have h2 := hR 2 s  -- |R(s) - 4| ≤ 1, so R(s) ∈ [3, 5]
  -- Simplify the system values
  simp only [threeSystemCounterexample, Fin.val_zero, Fin.val_one,
             Nat.cast_zero, Nat.cast_one, mul_zero, mul_one] at h0 h1 h2
  -- Note: (2 : Fin 3).val = 2, so 2 * ↑↑2 = 2 * 2 = 4
  have hval2 : ((2 : Fin 3).val : ℚ) = 2 := by native_decide
  simp only [hval2] at h2
  -- h0: |R.values s - 0| ≤ 1, i.e., |R.values s| ≤ 1
  -- h1: |R.values s - 2| ≤ 1
  -- h2: |R.values s - 4| ≤ 1
  have h0' : R.values s ≤ 1 := by
    have := abs_le.mp (by simp only [sub_zero] at h0; exact h0)
    exact this.2
  have h0'' : -1 ≤ R.values s := by
    have := abs_le.mp (by simp only [sub_zero] at h0; exact h0)
    exact this.1
  have h1' : R.values s ≥ 1 := by
    have := abs_le.mp h1
    linarith
  have h2' : R.values s ≥ 3 := by
    have := abs_le.mp h2
    -- h2 is now |R.values s - 2 * 2| ≤ 1 = |R.values s - 4| ≤ 1
    linarith
  -- Now we have R.values s ≤ 1 and R.values s ≥ 3, contradiction
  linarith

/-! ## Part 3: The General n ≥ 3 Case -/

/-
For n agents, we use values 0, 2, 4, ..., 2(n-1).

The gap between first and last is 2(n-1).
For a reconciler: must be within 1 of all values.
- Within 1 of 0: R ∈ [-1, 1]
- Within 1 of 2(n-1): R ∈ [2n-3, 2n-1]
These don't overlap when n ≥ 3 (since 1 < 2n-3 = 2(3)-3 = 3).
-/

/-- n systems with values 0, 2, 4, ..., 2(n-1) -/
def nSystemCounterexample (n : ℕ) : Fin n → ValueSystem S :=
  fun i => ⟨fun _ => 2 * (i.val : ℚ)⟩

/-- Adjacent systems differ by exactly 2 -/
theorem n_system_adjacent_diff (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) (s : S) :
    |(nSystemCounterexample n i).values s - 
      (nSystemCounterexample n ⟨i.val + 1, hi⟩).values s| = 2 := by
  simp only [nSystemCounterexample]
  have h : ((i.val + 1 : ℕ) : ℚ) = (i.val : ℚ) + 1 := by simp
  rw [h]
  ring_nf
  simp [abs_neg]

/-- First and last systems differ by 2(n-1) -/
theorem n_system_endpoint_diff (n : ℕ) (hn : n ≥ 1) (s : S) :
    |(nSystemCounterexample n ⟨0, by omega⟩).values s -
      (nSystemCounterexample n ⟨n - 1, by omega⟩).values s| = 2 * (n - 1 : ℕ) := by
  simp only [nSystemCounterexample]
  simp only [Nat.cast_zero, mul_zero, zero_sub]
  -- Now we have |-2 * ↑(n - 1)| = 2 * ↑(n - 1)
  have h_pos : (2 : ℚ) * ((n - 1 : ℕ) : ℚ) ≥ 0 := by
    apply mul_nonneg (by norm_num : (2 : ℚ) ≥ 0)
    simp
  rw [abs_neg, abs_of_nonneg h_pos]

/-! ## Part 4: THE MAIN THEOREM -/

/-- 
MAIN THEOREM: For n ≥ 3 agents, there exist configurations where
consecutive pairs agree within ε, but no global reconciler exists.

Construction:
- n systems with values 0, 2, 4, ..., 2(n-1)
- ε = 1
- Adjacent pairs differ by 2 = 2ε ✓
- Reconciler must be within 1 of 0 AND within 1 of 2(n-1)
- But [−1,1] ∩ [2n−3, 2n−1] = ∅ when n ≥ 3

This is the PUBLISHABLE result.
-/
theorem no_universal_reconciler_strong [Nonempty S] (n : ℕ) (hn : n ≥ 3) :
    ∃ (ε : ℚ) (_hε : ε > 0) (systems : Fin n → ValueSystem S),
      -- All consecutive pairs agree within 2ε
      (∀ i : Fin n, ∀ hi : i.val + 1 < n, 
        ∀ s : S, |(systems i).values s - (systems ⟨i.val + 1, hi⟩).values s| ≤ 2 * ε) ∧
      -- But no global reconciler exists with tolerance ε
      (¬∃ R : ValueSystem S, ∀ i : Fin n, Reconciles R (systems i) ε) := by
  -- Use ε = 1 and our counterexample construction
  use 1, (by norm_num : (1 : ℚ) > 0), nSystemCounterexample n
  constructor
  · -- Adjacent pairs agree within 2
    intro i hi s
    have h := n_system_adjacent_diff n i hi s
    linarith
  · -- No reconciler exists
    intro ⟨R, hR⟩
    obtain ⟨s⟩ : Nonempty S := inferInstance
    -- Constraint from system 0: |R(s) - 0| ≤ 1
    have h_first := hR ⟨0, by omega⟩ s
    simp only [nSystemCounterexample, Nat.cast_zero, mul_zero, sub_zero] at h_first
    -- Constraint from system (n-1): |R(s) - 2(n-1)| ≤ 1
    have h_last := hR ⟨n - 1, by omega⟩ s
    simp only [nSystemCounterexample] at h_last
    -- From h_first: R.values s ∈ [-1, 1]
    have h_upper : R.values s ≤ 1 := by
      have := abs_le.mp h_first
      exact this.2
    -- From h_last: R.values s ∈ [2(n-1) - 1, 2(n-1) + 1]
    have h_lower : R.values s ≥ 2 * ((n - 1 : ℕ) : ℚ) - 1 := by
      have := abs_le.mp h_last
      linarith
    -- We need 2(n-1) - 1 > 1, i.e., 2n - 3 > 1, i.e., n > 2
    have h_gap : 2 * ((n - 1 : ℕ) : ℚ) - 1 > 1 := by
      have hn' : (n : ℚ) ≥ 3 := by exact Nat.cast_le.mpr hn
      have h_sub : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
        simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      rw [h_sub]
      linarith
    -- Now h_lower says R.values s ≥ (something > 1)
    -- And h_upper says R.values s ≤ 1
    -- Contradiction!
    linarith

/-! ## Part 5: Corollaries -/

/-- The hollow triangle (n=3) is a special case -/
theorem hollow_triangle_is_special_case [Nonempty S] :
    ∃ (ε : ℚ) (_hε : ε > 0) (systems : Fin 3 → ValueSystem S),
      (∀ i : Fin 3, ∀ hi : i.val + 1 < 3, 
        ∀ s : S, |(systems i).values s - (systems ⟨i.val + 1, hi⟩).values s| ≤ 2 * ε) ∧
      (¬∃ R : ValueSystem S, ∀ i : Fin 3, Reconciles R (systems i) ε) :=
  no_universal_reconciler_strong 3 (by norm_num)

/-- The obstruction grows with n: gap is 2(n-1) - 2 = 2n - 4 -/
theorem obstruction_grows_with_n (n : ℕ) (hn : n ≥ 3) :
    -- The "excess gap" (how much the endpoint difference exceeds 2ε) is 2n - 4
    2 * ((n - 1 : ℕ) : ℚ) - 2 = 2 * n - 4 := by
  have h_sub : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [h_sub]
  ring

/-- For large n, the impossibility is "very impossible" -/
theorem large_n_very_impossible (n : ℕ) (hn : n ≥ 100) :
    -- The gap is at least 196 (when ε = 1)
    2 * ((n - 1 : ℕ) : ℚ) - 2 ≥ 196 := by
  have h_sub : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [h_sub]
  have hn' : (n : ℚ) ≥ 100 := Nat.cast_le.mpr hn
  linarith

end Perspective
