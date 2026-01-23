/-
# Cochain Groups

A k-cochain is a function from k-simplices to coefficients.
-/

import Foundations.Simplex

namespace Foundations

/-- A k-cochain assigns a coefficient to each k-simplex -/
def Cochain (K : SimplicialComplex) (k : ℕ) :=
  { s : Simplex // s ∈ K.ksimplices k } → Coeff

namespace Cochain

variable {K : SimplicialComplex} {k : ℕ}

/-- Zero cochain -/
instance : Zero (Cochain K k) where
  zero := fun _ => 0

/-- Cochain addition -/
instance : Add (Cochain K k) where
  add f g := fun s => f s + g s

/-- Cochain negation -/
instance : Neg (Cochain K k) where
  neg f := fun s => -f s

/-- Scalar multiplication -/
instance : SMul Coeff (Cochain K k) where
  smul c f := fun s => c * f s

/-- Cochain subtraction -/
instance : Sub (Cochain K k) where
  sub f g := fun s => f s - g s

@[simp]
lemma zero_apply (s : { s : Simplex // s ∈ K.ksimplices k }) :
    (0 : Cochain K k) s = 0 := rfl

@[simp]
lemma add_apply (f g : Cochain K k) (s : { s : Simplex // s ∈ K.ksimplices k }) :
    (f + g) s = f s + g s := rfl

@[simp]
lemma neg_apply (f : Cochain K k) (s : { s : Simplex // s ∈ K.ksimplices k }) :
    (-f) s = -f s := rfl

@[simp]
lemma sub_apply (f g : Cochain K k) (s : { s : Simplex // s ∈ K.ksimplices k }) :
    (f - g) s = f s - g s := rfl

@[simp]
lemma smul_apply (c : Coeff) (f : Cochain K k) (s : { s : Simplex // s ∈ K.ksimplices k }) :
    (c • f) s = c * f s := rfl

end Cochain

end Foundations
