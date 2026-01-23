/-
# Cohomology Groups

H^k = ker(δᵏ) / im(δᵏ⁻¹)

The first cohomology H¹ measures "obstructions to gluing".
-/

import Foundations.Coboundary

namespace Foundations

/-- A k-cocycle is a cochain in the kernel of δ -/
def IsCocycle (K : SimplicialComplex) (k : ℕ) (f : Cochain K k) : Prop :=
  δ K k f = 0

/-- The set of k-cocycles -/
def Cocycles (K : SimplicialComplex) (k : ℕ) : Set (Cochain K k) :=
  { f | IsCocycle K k f }

/-- A k-coboundary is a cochain in the image of δ -/
def IsCoboundary (K : SimplicialComplex) (k : ℕ) (f : Cochain K k) : Prop :=
  match k with
  | 0 => False  -- No 0-coboundaries (no (-1)-cochains)
  | k' + 1 => ∃ g : Cochain K k', δ K k' g = f

/-- The set of k-coboundaries -/
def Coboundaries (K : SimplicialComplex) (k : ℕ) : Set (Cochain K k) :=
  { f | IsCoboundary K k f }

/-- Every coboundary is a cocycle (consequence of δ² = 0) -/
theorem coboundary_is_cocycle (K : SimplicialComplex) (k : ℕ) (f : Cochain K k) :
  IsCoboundary K k f → IsCocycle K k f := by
  intro h
  cases k with
  | zero => cases h  -- No 0-coboundaries
  | succ k' =>
    obtain ⟨g, hg⟩ := h
    simp only [IsCocycle]
    rw [← hg]
    exact delta_sq_zero K k' g

/-- Coboundaries ⊆ Cocycles -/
theorem coboundaries_subset_cocycles (K : SimplicialComplex) (k : ℕ) :
  Coboundaries K k ⊆ Cocycles K k := by
  intro f hf
  exact coboundary_is_cocycle K k f hf

/-- H¹ is trivial iff every 1-cocycle is a 1-coboundary -/
def H1Trivial (K : SimplicialComplex) : Prop :=
  ∀ f : Cochain K 1, IsCocycle K 1 f → IsCoboundary K 1 f

end Foundations
