/-
# Cohomology Dimension

Defines dimH1 as the dimension of the first cohomology group.
This enables stating theorems about single-cycle complexes.
-/

import Foundations.CohomologyModule
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Foundations

open Finset BigOperators

variable {K : SimplicialComplex}

/-! ## Finite-dimensionality of H¹ -/

/-- When the simplicial complex has finite k-simplices, the cocycle submodule is finite-dimensional -/
instance CocycleSubmodule.finiteDimensional (K : SimplicialComplex) (k : ℕ)
    [Fintype (KSimplexType K k)] :
    Module.Finite ℚ (CocycleSubmodule K k) :=
  inferInstance

/-- H1Module is finite-dimensional when the simplicial complex is finite -/
instance H1Module.finiteDimensional [Fintype (KSimplexType K 0)] [Fintype (KSimplexType K 1)] :
    Module.Finite ℚ (H1Module K) := by
  unfold H1Module
  infer_instance

/-! ## Dimension of H¹ -/

/-- The dimension of H¹(K) as a ℚ-vector space -/
noncomputable def dimH1 (K : SimplicialComplex)
    [Fintype (KSimplexType K 0)] [Fintype (KSimplexType K 1)] : ℕ :=
  Module.finrank ℚ (H1Module K)

/-! ## Single-Cycle Complexes -/

/-- A complex has a single cycle if dimH1 = 1 -/
def HasSingleCycle (K : SimplicialComplex)
    [Fintype (KSimplexType K 0)] [Fintype (KSimplexType K 1)] : Prop :=
  dimH1 K = 1

/-- HasSingleCycle implies H1 is nontrivial -/
theorem hasSingleCycle_implies_not_h1_trivial
    [Fintype (KSimplexType K 0)] [Fintype (KSimplexType K 1)]
    (h : HasSingleCycle K) : ¬H1Trivial K := by
  intro h_triv
  unfold HasSingleCycle dimH1 at h
  -- H1Trivial means the quotient is trivial
  rw [h1_trivial_iff_coboundary_eq_cocycle] at h_triv
  -- When coboundaries = cocycles, the CoboundaryInCocycles is ⊤
  have h_top : CoboundaryInCocycles K 1 = ⊤ := by
    ext ⟨f, hf⟩
    simp only [Submodule.mem_top, iff_true]
    unfold CoboundaryInCocycles
    simp only [Submodule.mem_comap, Submodule.coe_subtype]
    rw [h_triv]
    exact hf
  -- Then H1Module is trivial (Subsingleton)
  unfold H1Module at h
  have h_sing : Subsingleton ((CocycleSubmodule K 1) ⧸ (CoboundaryInCocycles K 1)) := by
    rw [h_top]
    infer_instance
  -- Subsingleton has finrank 0
  have h_zero : Module.finrank ℚ ((CocycleSubmodule K 1) ⧸ (CoboundaryInCocycles K 1)) = 0 :=
    Module.finrank_zero_of_subsingleton
  -- But h says finrank = 1
  omega

/-- If H1 is nontrivial, dimH1 ≥ 1

This follows from the fact that finrank 0 implies Subsingleton,
which would mean all cocycles are coboundaries (H1Trivial).

Mathematical proof: If dimH1 = 0, then the quotient Cocycles/Coboundaries is trivial,
meaning every cocycle is a coboundary, i.e., H1Trivial holds. -/
theorem not_h1_trivial_implies_dimH1_pos
    [Fintype (KSimplexType K 0)] [Fintype (KSimplexType K 1)]
    (h : ¬H1Trivial K) : dimH1 K ≥ 1 := by
  by_contra h_lt
  push_neg at h_lt
  have h_zero : dimH1 K = 0 := Nat.lt_one_iff.mp h_lt
  apply h
  rw [h1_trivial_iff_coboundary_eq_cocycle]
  unfold dimH1 H1Module at h_zero
  -- finrank 0 over a field means the space is trivial
  -- We use the contrapositive: if cocycles ≠ coboundaries, then dimH1 > 0
  ext f
  constructor
  · intro hf
    exact coboundarySubmodule_le_cocycleSubmodule K 1 hf
  · intro hf
    rw [mem_cocycleSubmodule_iff] at hf
    -- The quotient has finrank 0, so it's subsingleton
    -- In a subsingleton quotient, [f] = [0], so f is a coboundary
    have hf' : f ∈ CocycleSubmodule K 1 := by rw [mem_cocycleSubmodule_iff]; exact hf
    -- Build subsingleton from finrank 0
    have h_triv : (⊤ : Submodule ℚ ((CocycleSubmodule K 1) ⧸ (CoboundaryInCocycles K 1))) = ⊥ := by
      rw [← Submodule.finrank_eq_zero, finrank_top, h_zero]
    have h_sing : Subsingleton ((CocycleSubmodule K 1) ⧸ (CoboundaryInCocycles K 1)) := by
      constructor
      intro x y
      have hx : x ∈ (⊤ : Submodule ℚ _) := Submodule.mem_top
      have hy : y ∈ (⊤ : Submodule ℚ _) := Submodule.mem_top
      rw [h_triv, Submodule.mem_bot] at hx hy
      rw [hx, hy]
    have h_eq : (Submodule.Quotient.mk ⟨f, hf'⟩ : (CocycleSubmodule K 1) ⧸ (CoboundaryInCocycles K 1)) =
        Submodule.Quotient.mk 0 := Subsingleton.elim _ _
    rw [Submodule.Quotient.eq] at h_eq
    simp only [sub_zero] at h_eq
    unfold CoboundaryInCocycles at h_eq
    simp only [Submodule.mem_comap, Submodule.coe_subtype] at h_eq
    exact h_eq

end Foundations
