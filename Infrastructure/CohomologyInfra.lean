/-
  Infrastructure/CohomologyInfra.lean

  Enhanced cohomology infrastructure.

  SORRIES: 0
  AXIOMS: 0
-/

import Foundations.Cohomology
import Foundations.Coboundary
import H1Characterization.OneConnected

namespace Infrastructure

open Foundations H1Characterization

/-! ## Section 1: Cocycle/Coboundary Characterization -/

/-- A 1-cochain f is a cocycle iff δf = 0 -/
theorem cocycle_def (K : SimplicialComplex) (f : Cochain K 1) :
    IsCocycle K 1 f ↔ δ K 1 f = 0 := Iff.rfl

/-- A 1-cochain f is a coboundary iff there exists g with f = δ⁰g -/
theorem coboundary_iff_exists_preimage (K : SimplicialComplex) (f : Cochain K 1) :
    IsCoboundary K 1 f ↔ ∃ g : Cochain K 0, δ K 0 g = f := Iff.rfl

/-! ## Section 2: H¹ = 0 Characterizations -/

/-- H¹ = 0 means every cocycle is a coboundary -/
theorem h1_trivial_def (K : SimplicialComplex) :
    H1Trivial K ↔ ∀ f : Cochain K 1, IsCocycle K 1 f → IsCoboundary K 1 f := Iff.rfl

/-! ## Section 3: Zero Cochain Properties -/

/-- The zero cochain is always a cocycle -/
theorem zero_is_cocycle (K : SimplicialComplex) (k : ℕ) :
    IsCocycle K k (0 : Cochain K k) := by
  unfold IsCocycle
  funext σ
  simp only [Cochain.zero_apply, coboundary, mul_zero, Finset.sum_const_zero]

/-- The zero cochain is a coboundary for k ≥ 1 -/
theorem zero_is_coboundary (K : SimplicialComplex) (k : ℕ) (hk : k ≥ 1) :
    IsCoboundary K k (0 : Cochain K k) := by
  cases k with
  | zero => omega
  | succ k' =>
    use 0
    funext σ
    simp only [Cochain.zero_apply, coboundary, mul_zero, Finset.sum_const_zero]

/-! ## Section 4: Sign Function Properties -/

/-- Sign alternates: sign(i+1) = -sign(i) -/
theorem sign_succ (i : ℕ) : sign (i + 1) = -sign i := by
  unfold sign
  split_ifs with h1 h2
  · omega  -- (i+1) % 2 = 0 and i % 2 = 0 is impossible
  · ring   -- 1 = -(-1)
  · ring   -- -1 = -1
  · omega  -- (i+1) % 2 ≠ 0 and i % 2 ≠ 0 is impossible

/-- Sign squared is 1 -/
theorem sign_sq (i : ℕ) : sign i * sign i = 1 := by
  unfold sign
  split_ifs <;> ring

/-- Sum of paired terms with opposite signs cancels -/
theorem sign_sum_cancel (i : ℕ) (x : ℚ) :
    sign i * x + sign (i + 1) * x = 0 := by
  rw [sign_succ]
  ring

/-! ## Section 5: Local-to-Global Principle -/

/-- If H¹ = 0 and f is a cocycle, then f is a coboundary -/
theorem local_coboundary_implies_global (K : SimplicialComplex) [Nonempty K.vertexSet]
    (hK : H1Trivial K) (f : Cochain K 1) (hf : IsCocycle K 1 f) :
    IsCoboundary K 1 f := hK f hf

/-! ## Section 6: Stability Results -/

/-- H¹ = 0 is preserved (tautologically) -/
theorem h1_trivial_stable (K : SimplicialComplex) [Nonempty K.vertexSet]
    (hK : H1Trivial K) :
    ∀ f : Cochain K 1, IsCocycle K 1 f → IsCoboundary K 1 f := hK

/-! ## Summary -/

#check cocycle_def
#check coboundary_iff_exists_preimage
#check h1_trivial_def
#check zero_is_cocycle
#check zero_is_coboundary
#check sign_succ
#check sign_sq
#check local_coboundary_implies_global

end Infrastructure
