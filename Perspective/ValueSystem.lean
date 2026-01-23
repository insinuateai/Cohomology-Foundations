/-
# Value Systems
-/

import Foundations.Cohomology
import Mathlib.Data.Rat.Defs

namespace Perspective

variable {S : Type*} [Fintype S] [DecidableEq S]

structure ValueSystem (S : Type*) where
  values : S → ℚ

def LocallyAgree (V₁ V₂ : ValueSystem S) (s : S) (ε : ℚ) : Prop :=
  |V₁.values s - V₂.values s| ≤ ε

instance (V₁ V₂ : ValueSystem S) (s : S) (ε : ℚ) : Decidable (LocallyAgree V₁ V₂ s ε) := by
  unfold LocallyAgree; infer_instance

def Agree (V₁ V₂ : ValueSystem S) (ε : ℚ) : Prop :=
  ∃ s : S, LocallyAgree V₁ V₂ s ε

def AgreementSet (V₁ V₂ : ValueSystem S) (ε : ℚ) : Finset S :=
  Finset.univ.filter (fun s => decide (LocallyAgree V₁ V₂ s ε))

lemma locallyAgree_symm (V₁ V₂ : ValueSystem S) (s : S) (ε : ℚ) :
    LocallyAgree V₁ V₂ s ε ↔ LocallyAgree V₂ V₁ s ε := by
  unfold LocallyAgree
  constructor <;> intro h
  · calc |V₂.values s - V₁.values s| = |-(V₁.values s - V₂.values s)| := by ring_nf
      _ = |V₁.values s - V₂.values s| := abs_neg _
      _ ≤ ε := h
  · calc |V₁.values s - V₂.values s| = |-(V₂.values s - V₁.values s)| := by ring_nf
      _ = |V₂.values s - V₁.values s| := abs_neg _
      _ ≤ ε := h

end Perspective
