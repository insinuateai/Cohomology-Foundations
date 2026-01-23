/-
# Main Theorem: No Universal Alignment

This file proves fundamental impossibility results about value alignment:
- No AI can be aligned with ALL possible human value systems
- Alignment must be contextual (for any AI, some human exists it can't align with)
-/

import Perspective.Alignment
import Mathlib.Tactic.Linarith

namespace Perspective

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- No AI value system can be aligned with ALL possible human value systems -/
theorem no_universal_alignment [Nonempty S] (ε : ℚ) (hε : 0 < ε) :
    ¬∃ (A : ValueSystem S), ∀ (H : ValueSystem S), Alignable H A ε := by
  intro ⟨A, hA⟩
  let H : ValueSystem S := ⟨fun s => A.values s + 3 * ε⟩
  have h_not_align : ¬Alignable H A ε := by
    intro ⟨r⟩
    obtain ⟨s⟩ : Nonempty S := inferInstance
    have h1 := r.acceptable_to_H s
    have h2 := r.acceptable_to_A s
    have h1' : |H.values s - r.values s| ≤ ε := by rw [abs_sub_comm]; exact h1
    have h_diff : |H.values s - A.values s| = 3 * ε := by
      simp only [H]
      have h_pos : 0 < 3 * ε := by linarith [hε]
      calc |A.values s + 3 * ε - A.values s| = |3 * ε| := by ring_nf
        _ = 3 * ε := abs_of_pos h_pos
    have h_tri : |H.values s - A.values s| ≤ 2 * ε := by
      calc |H.values s - A.values s|
          = |H.values s - r.values s + (r.values s - A.values s)| := by ring_nf
        _ ≤ |H.values s - r.values s| + |r.values s - A.values s| := abs_add_le _ _
        _ ≤ ε + ε := add_le_add h1' h2
        _ = 2 * ε := by ring
    have : 3 * ε ≤ 2 * ε := h_diff ▸ h_tri
    linarith
  exact h_not_align (hA H)

/-- Alignment must be contextual: for any AI, there's some human it can't align with -/
theorem alignment_is_contextual [Nonempty S] (ε : ℚ) (hε : 0 < ε) :
    ∀ (A : ValueSystem S), ∃ (H : ValueSystem S), ¬Alignable H A ε := by
  intro A
  use ⟨fun s => A.values s + 3 * ε⟩
  intro ⟨r⟩
  obtain ⟨s⟩ : Nonempty S := inferInstance
  have h1 := r.acceptable_to_H s
  have h2 := r.acceptable_to_A s
  have h1' : |A.values s + 3 * ε - r.values s| ≤ ε := by rw [abs_sub_comm]; exact h1
  have h_tri : |A.values s + 3 * ε - A.values s| ≤ 2 * ε := by
    calc |A.values s + 3 * ε - A.values s|
        = |A.values s + 3 * ε - r.values s + (r.values s - A.values s)| := by ring_nf
      _ ≤ |A.values s + 3 * ε - r.values s| + |r.values s - A.values s| := abs_add_le _ _
      _ ≤ ε + ε := add_le_add h1' h2
      _ = 2 * ε := by ring
  have h_eq : |A.values s + 3 * ε - A.values s| = 3 * ε := by
    have h_pos : 0 < 3 * ε := by linarith [hε]
    calc |A.values s + 3 * ε - A.values s| = |3 * ε| := by ring_nf
      _ = 3 * ε := abs_of_pos h_pos
  have : 3 * ε ≤ 2 * ε := h_eq ▸ h_tri
  linarith

end Perspective
