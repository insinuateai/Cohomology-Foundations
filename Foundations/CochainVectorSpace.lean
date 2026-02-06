/-
# Cochain Vector Space Structure

Establishes Cochain K k as a finite-dimensional ℚ-vector space.
This is foundational infrastructure for computing dimH1.
-/

import Foundations.Cochain
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dimension.DivisionRing

namespace Foundations

open Finset BigOperators

variable {K : SimplicialComplex} {k : ℕ}

/-! ## AddCommGroup structure for Cochain -/

/-- Cochain forms an AddCommGroup with pointwise operations -/
instance Cochain.addCommGroup : AddCommGroup (Cochain K k) :=
  Pi.addCommGroup

/-! ## Module ℚ structure for Cochain -/

/-- Cochain forms a ℚ-module with pointwise scalar multiplication -/
instance Cochain.module : Module ℚ (Cochain K k) :=
  Pi.module _ _ _

/-! ## Finite-dimensionality when ksimplices is finite -/

/-- The type of k-simplices in K -/
abbrev KSimplexType (K : SimplicialComplex) (k : ℕ) := { s : Simplex // s ∈ K.ksimplices k }

/-- Cochain K k is isomorphic to functions KSimplexType K k → ℚ -/
def cochainEquivPi (K : SimplicialComplex) (k : ℕ) :
    Cochain K k ≃ₗ[ℚ] (KSimplexType K k → ℚ) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- When K has finitely many k-simplices, Cochain K k is finite-dimensional -/
instance Cochain.finiteDimensional [h : Fintype (KSimplexType K k)] :
    Module.Finite ℚ (Cochain K k) := by
  have : Module.Finite ℚ (KSimplexType K k → ℚ) := Module.Finite.pi
  exact Module.Finite.equiv (cochainEquivPi K k).symm

/-- The dimension of Cochain K k equals the number of k-simplices -/
theorem Cochain.finrank_eq [Fintype (KSimplexType K k)] :
    Module.finrank ℚ (Cochain K k) = Fintype.card (KSimplexType K k) := by
  -- finrank of a→ℚ equals card(a) when each component is 1-dimensional
  have h1 : Module.finrank ℚ (KSimplexType K k → ℚ) =
      ∑ _i : KSimplexType K k, Module.finrank ℚ ℚ := Module.finrank_pi_fintype ℚ
  simp only [Module.finrank_self, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h1
  have h3 : Module.finrank ℚ (Cochain K k) =
      Module.finrank ℚ (KSimplexType K k → ℚ) :=
    LinearEquiv.finrank_eq (cochainEquivPi K k)
  rw [h3, h1]

end Foundations
