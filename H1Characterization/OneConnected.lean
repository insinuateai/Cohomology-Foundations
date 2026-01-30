/-
  H1Characterization/OneConnected.lean

  Defines when a simplicial complex is "1-connected" (1-skeleton is acyclic).

  SORRIES: 0
  AXIOMS: 0
-/

import H1Characterization.OneSkeleton
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace H1Characterization

/-! ## OneConnected Definition -/

def OneConnected (K : SimplicialComplex) : Prop := (oneSkeleton K).IsAcyclic

lemma oneConnected_iff_no_cycles (K : SimplicialComplex) :
    OneConnected K ↔ ∀ v : K.vertexSet, ∀ p : Walk K v v, ¬p.IsCycle := by
  unfold OneConnected SimpleGraph.IsAcyclic
  rfl

lemma acyclic_path_unique (K : SimplicialComplex) (hK : OneConnected K)
    (v w : K.vertexSet) (p q : Path K v w) : p = q :=
  SimpleGraph.IsAcyclic.path_unique hK p q

/-! ## Euler Characteristic -/

-- Note: Euler's formula for forests (|E| ≤ |V| - components ↔ acyclic) is a standard
-- result but requires additional mathlib imports for connected component counting.
-- For now, we simply note that this is a well-known theorem that could be added later.

/-! ## Basic Properties -/

lemma not_oneConnected_iff_exists_cycle (K : SimplicialComplex) :
    ¬OneConnected K ↔ ∃ v : K.vertexSet, ∃ p : Walk K v v, p.IsCycle := by
  rw [oneConnected_iff_no_cycles]; push_neg; rfl

end H1Characterization
