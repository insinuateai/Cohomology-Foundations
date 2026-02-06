/-
# Cohomology as Module Theory

Defines δ as a linear map and cocycles/coboundaries as submodules.
This enables computing dimH1 as dimension of quotient module.
-/

import Foundations.CochainVectorSpace
import Foundations.Cohomology
import Mathlib.LinearAlgebra.Quotient.Basic

namespace Foundations

open Finset BigOperators

variable {K : SimplicialComplex}

/-! ## Coboundary as a Linear Map -/

/-- The coboundary operator δ is additive -/
theorem coboundary_add (K : SimplicialComplex) (k : ℕ) (f g : Cochain K k) :
    δ K k (f + g) = δ K k f + δ K k g := by
  funext ⟨s, hs⟩
  simp only [coboundary, Cochain.add_apply]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext i
  ring

/-- The coboundary operator δ respects scalar multiplication -/
theorem coboundary_smul (K : SimplicialComplex) (k : ℕ) (a : ℚ) (f : Cochain K k) :
    δ K k (a • f) = a • δ K k f := by
  funext ⟨s, hs⟩
  simp only [coboundary, Cochain.smul_apply]
  rw [Finset.mul_sum]
  congr 1
  ext i
  ring

/-- The coboundary operator as a ℚ-linear map -/
def coboundaryLinearMap (K : SimplicialComplex) (k : ℕ) :
    Cochain K k →ₗ[ℚ] Cochain K (k + 1) where
  toFun := δ K k
  map_add' := coboundary_add K k
  map_smul' := coboundary_smul K k

/-! ## Cocycles as a Submodule -/

/-- The submodule of k-cocycles (kernel of δᵏ) -/
def CocycleSubmodule (K : SimplicialComplex) (k : ℕ) : Submodule ℚ (Cochain K k) :=
  LinearMap.ker (coboundaryLinearMap K k)

/-- A cochain is a cocycle iff it's in the CocycleSubmodule -/
theorem mem_cocycleSubmodule_iff {k : ℕ} (f : Cochain K k) :
    f ∈ CocycleSubmodule K k ↔ IsCocycle K k f := by
  simp only [CocycleSubmodule, LinearMap.mem_ker, coboundaryLinearMap]
  rfl

/-! ## Coboundaries as a Submodule -/

/-- The submodule of k-coboundaries (image of δᵏ⁻¹) -/
def CoboundarySubmodule (K : SimplicialComplex) (k : ℕ) : Submodule ℚ (Cochain K k) :=
  match k with
  | 0 => ⊥  -- No 0-coboundaries
  | k' + 1 => LinearMap.range (coboundaryLinearMap K k')

/-- For k ≥ 1, a cochain is a coboundary iff it's in the CoboundarySubmodule -/
theorem mem_coboundarySubmodule_iff_succ {k' : ℕ} (f : Cochain K (k' + 1)) :
    f ∈ CoboundarySubmodule K (k' + 1) ↔ IsCoboundary K (k' + 1) f := by
  simp only [CoboundarySubmodule, LinearMap.mem_range, coboundaryLinearMap, IsCoboundary]
  constructor
  · intro ⟨g, hg⟩; exact ⟨g, hg⟩
  · intro ⟨g, hg⟩; exact ⟨g, hg⟩

/-- For 1-cochains specifically (most relevant for H¹) -/
theorem mem_coboundarySubmodule_iff_one (f : Cochain K 1) :
    f ∈ CoboundarySubmodule K 1 ↔ IsCoboundary K 1 f :=
  mem_coboundarySubmodule_iff_succ f

/-! ## Coboundaries are Cocycles -/

/-- Every coboundary is a cocycle (submodule version of δ² = 0) -/
theorem coboundarySubmodule_le_cocycleSubmodule (K : SimplicialComplex) (k : ℕ) :
    CoboundarySubmodule K k ≤ CocycleSubmodule K k := by
  intro f hf
  cases k with
  | zero =>
    -- For k=0, CoboundarySubmodule is ⊥, so f = 0
    simp only [CoboundarySubmodule, Submodule.mem_bot] at hf
    rw [hf]
    simp only [CocycleSubmodule, LinearMap.mem_ker, map_zero]
  | succ k' =>
    rw [mem_coboundarySubmodule_iff_succ] at hf
    rw [mem_cocycleSubmodule_iff]
    exact coboundary_is_cocycle K (k' + 1) f hf

/-! ## H¹ Infrastructure -/

/-- Coboundaries viewed as a submodule of the cocycles -/
def CoboundaryInCocycles (K : SimplicialComplex) (k : ℕ) :
    Submodule ℚ (CocycleSubmodule K k) :=
  (CoboundarySubmodule K k).comap (CocycleSubmodule K k).subtype

/-- The first cohomology group as a quotient module -/
def H1Module (K : SimplicialComplex) : Type :=
  (CocycleSubmodule K 1) ⧸ (CoboundaryInCocycles K 1)

instance H1Module.addCommGroup : AddCommGroup (H1Module K) :=
  Submodule.Quotient.addCommGroup _

instance H1Module.module : Module ℚ (H1Module K) :=
  Submodule.Quotient.module _

/-- H1Trivial is equivalent to the coboundaries being all of the cocycles -/
theorem h1_trivial_iff_coboundary_eq_cocycle :
    H1Trivial K ↔ CoboundarySubmodule K 1 = CocycleSubmodule K 1 := by
  constructor
  · intro h
    ext f
    constructor
    · intro hf
      exact coboundarySubmodule_le_cocycleSubmodule K 1 hf
    · intro hf
      rw [mem_coboundarySubmodule_iff_one]
      rw [mem_cocycleSubmodule_iff] at hf
      exact h f hf
  · intro h f hf
    rw [← mem_coboundarySubmodule_iff_one]
    rw [h]
    rw [mem_cocycleSubmodule_iff]
    exact hf

end Foundations
