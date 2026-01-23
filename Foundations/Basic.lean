/-
# Basic Definitions

Foundational types for the cohomology formalization.
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring

namespace Foundations

/-- We work over the rationals for exact arithmetic (matching TypeScript implementation) -/
abbrev Coeff := ℚ

/-- A vertex represents a turn index in the conversation -/
abbrev Vertex := ℕ

/-- Orientation sign: (-1)^n -/
def sign (n : ℕ) : Coeff := if n % 2 = 0 then 1 else -1

@[simp]
lemma sign_zero : sign 0 = 1 := rfl

@[simp]
lemma sign_one : sign 1 = -1 := rfl

lemma sign_add (m n : ℕ) : sign (m + n) = sign m * sign n := by
  unfold sign
  split_ifs with h1 h2 h3 <;> try (exfalso; omega)
  · -- m + n even, m even, n even: 1 = 1 * 1
    ring
  · -- m + n even, m odd, n odd: 1 = (-1) * (-1)
    ring
  · -- m + n odd, m even, n odd: -1 = 1 * (-1)
    ring
  · -- m + n odd, m odd, n even: -1 = (-1) * 1
    ring

end Foundations
