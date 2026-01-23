/-
# Alignment Definition
-/

import Perspective.ValueSystem

namespace Perspective

variable {S : Type*} [Fintype S] [DecidableEq S]

structure Reconciliation (H A : ValueSystem S) (ε : ℚ) where
  values : S → ℚ
  acceptable_to_H : ∀ s, |values s - H.values s| ≤ ε
  acceptable_to_A : ∀ s, |values s - A.values s| ≤ ε

def Alignable (H A : ValueSystem S) (ε : ℚ) : Prop :=
  Nonempty (Reconciliation H A ε)

theorem alignable_of_agree_everywhere (H A : ValueSystem S) (ε : ℚ)
    (h : ∀ s, LocallyAgree H A s ε) : Alignable H A ε := by
  refine ⟨Reconciliation.mk H.values (fun s => by
    simp
    have : LocallyAgree H A s ε := h s
    unfold LocallyAgree at this
    exact abs_nonneg _ |>.trans this) (fun s => ?_)⟩
  have h_sym := (locallyAgree_symm H A s ε).mp (h s)
  unfold LocallyAgree at h_sym
  rw [abs_sub_comm] at h_sym
  exact h_sym

theorem alignable_symm (H A : ValueSystem S) (ε : ℚ) :
    Alignable H A ε ↔ Alignable A H ε := by
  constructor <;> intro ⟨r⟩
  · exact ⟨Reconciliation.mk r.values r.acceptable_to_A r.acceptable_to_H⟩
  · exact ⟨Reconciliation.mk r.values r.acceptable_to_A r.acceptable_to_H⟩

end Perspective
