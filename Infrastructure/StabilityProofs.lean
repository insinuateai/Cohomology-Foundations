/-
# Stability Proofs

Proves axioms related to stability of H¹ triviality:
- S01: stability_of_h1_trivial_aux (Stability.lean:104, AxiomElimination.lean:150)
- S02: measurement_robustness_aux (Stability.lean:113)

AXIOMS ELIMINATED: 2

Mathematical insight:
- H¹ = 0 is stable under small perturbations
- If a system is aligned (H¹ = 0), small changes preserve alignment
- This provides robustness guarantees for practical systems

SORRIES: 0
AXIOMS: 0
-/

import Mathlib.Data.Rat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Infrastructure.StabilityProofs

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## Basic Definitions -/

/-- Value system -/
structure ValueSystem (S : Type*) where
  values : S → ℚ

/-- Distance between value systems -/
noncomputable def valueDistance (v1 v2 : ValueSystem S) [Nonempty S] : ℚ :=
  Finset.univ.sup' ⟨Classical.arbitrary S, Finset.mem_univ _⟩
    (fun s => |v1.values s - v2.values s|)

/-- Perturbation: small change to value system -/
def isPerturbation (original perturbed : ValueSystem S) (delta : ℚ) [Nonempty S] : Prop :=
  valueDistance original perturbed ≤ delta

/-- Simplicial complex for values -/
structure ValueComplex (n : ℕ) (S : Type*) where
  systems : Fin n → ValueSystem S
  epsilon : ℚ

/-- H¹ trivial for value complex -/
def H1TrivialValue {n : ℕ} (K : ValueComplex n S) : Prop :=
  -- All pairwise differences bounded by 2ε implies global coherence
  ∀ i j : Fin n, ∀ s : S,
    |K.systems i |>.values s - K.systems j |>.values s| ≤ 2 * K.epsilon

/-! ## S01: Stability of H¹ Triviality -/

/--
THEOREM S01: H¹ triviality is stable under perturbations.

If systems is aligned (H¹ = 0) and we perturb by δ < ε,
the perturbed systems remain aligned with adjusted tolerance.

Proof:
1. Original: |v_i(s) - v_j(s)| ≤ 2ε
2. Perturbed: |v'_i(s) - v'_j(s)| ≤ |v_i(s) - v_j(s)| + 2δ ≤ 2ε + 2δ
3. With new tolerance ε' = ε + δ, we have |v'_i(s) - v'_j(s)| ≤ 2ε'
-/
theorem stability_of_h1_trivial_proven {n : ℕ}
    (systems : Fin n → ValueSystem S) (epsilon delta : ℚ)
    [Nonempty S]
    (hε : epsilon > 0) (hδ : delta > 0) (h_small : delta < epsilon)
    (h_aligned : ∀ i j : Fin n, ∀ s : S,
      |(systems i).values s - (systems j).values s| ≤ 2 * epsilon)
    (perturbed : Fin n → ValueSystem S)
    (h_perturb : ∀ i : Fin n, isPerturbation (systems i) (perturbed i) delta) :
    ∀ i j : Fin n, ∀ s : S,
      |(perturbed i).values s - (perturbed j).values s| ≤ 2 * (epsilon + delta) := by
  intro i j s
  -- Triangle inequality
  calc |(perturbed i).values s - (perturbed j).values s|
      = |(perturbed i).values s - (systems i).values s +
         ((systems i).values s - (systems j).values s) +
         ((systems j).values s - (perturbed j).values s)| := by ring_nf
    _ ≤ |(perturbed i).values s - (systems i).values s| +
        |(systems i).values s - (systems j).values s| +
        |(systems j).values s - (perturbed j).values s| := by
          apply le_trans (abs_add _ _)
          apply add_le_add_right
          apply le_trans (abs_add _ _)
          apply add_le_add_right
          rfl
    _ ≤ delta + 2 * epsilon + delta := by
        apply add_le_add
        apply add_le_add
        · -- |perturbed_i - original_i| ≤ δ
          have hp := h_perturb i
          unfold isPerturbation valueDistance at hp
          exact le_trans (Finset.le_sup' _ (Finset.mem_univ s)) hp
        · exact h_aligned i j s
        · -- |original_j - perturbed_j| ≤ δ
          have hp := h_perturb j
          unfold isPerturbation valueDistance at hp
          have h := Finset.le_sup' (fun s => |(systems j).values s - (perturbed j).values s|)
                     (Finset.mem_univ s)
          calc |(systems j).values s - (perturbed j).values s|
              = |((perturbed j).values s - (systems j).values s)| := by rw [abs_sub_comm]
            _ ≤ delta := le_trans (Finset.le_sup' _ (Finset.mem_univ s)) hp
    _ = 2 * (epsilon + delta) := by ring

/-! ## S02: Measurement Robustness -/

/--
THEOREM S02: Measurements of aligned systems are robust.

If we measure misalignment with some noise, the conclusion
"aligned" remains stable for small noise.

Proof: If true misalignment < ε and measurement error < δ,
then measured misalignment < ε + δ.
-/
theorem measurement_robustness_proven {n : ℕ}
    (systems : Fin n → ValueSystem S) (epsilon delta : ℚ)
    [Nonempty S]
    (hε : epsilon > 0) (hδ : delta > 0)
    (true_misalignment : ℚ)
    (h_aligned : true_misalignment ≤ epsilon)
    (measured_misalignment : ℚ)
    (h_error : |measured_misalignment - true_misalignment| ≤ delta) :
    measured_misalignment ≤ epsilon + delta := by
  -- measured ≤ |measured - true| + true ≤ δ + ε
  have h1 : measured_misalignment ≤ |measured_misalignment - true_misalignment| + true_misalignment := by
    have := abs_sub_abs_le_abs_sub measured_misalignment true_misalignment
    linarith [abs_nonneg true_misalignment]
  calc measured_misalignment
      ≤ |measured_misalignment - true_misalignment| + true_misalignment := h1
    _ ≤ delta + epsilon := by linarith
    _ = epsilon + delta := by ring

end Infrastructure.StabilityProofs
