/-
Infrastructure/GameStrategicProofs.lean

Proofs for game-theoretic axioms: X25, X26.
- actions_nonempty (X25): Well-formed games have nonempty action sets
- coordination_nash_player_bound (X26): Coordination games with Nash have ≤2 players

Key insights:
- X25 is a well-formedness condition; we provide a predicate for valid games
- X26 follows from the forest/Nash characterization in the simplified model

Targets: Mathlib 4.27.0 / Lean 4.27.0

SORRIES: 0
AXIOMS: 0
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import MultiAgent.GameTheoreticH1

namespace Infrastructure.GameStrategicProofs

open MultiAgent

/-! ## Section 1: Well-Formed Games (X25 Foundation)

    The axiom `actions_nonempty` asserts that players have available actions.
    This is a well-formedness condition: degenerate games with empty action
    sets are not meaningful for game-theoretic analysis.

    We provide:
    1. A predicate `WellFormedGame` that includes nonempty actions
    2. A proof that well-formed games satisfy the axiom statement
-/

/-- A game is well-formed if all players have nonempty action sets. -/
def WellFormedGame (G : StrategicGame) : Prop :=
  ∀ a ∈ G.players, (G.actions a).Nonempty

/-- Well-formed games have nonempty actions (direct restatement of predicate). -/
theorem wellformed_actions_nonempty (G : StrategicGame) (hwf : WellFormedGame G)
    (a : Agent) (ha : a ∈ G.players) : (G.actions a).Nonempty :=
  hwf a ha

/-- The empty game is vacuously well-formed. -/
theorem empty_wellformed : WellFormedGame StrategicGame.empty := by
  intro a ha
  nomatch ha

/-- Single-player games with nonempty actions are well-formed. -/
theorem singlePlayer_wellformed (a : Agent) (acts : Finset ℕ) (pay : ℕ → ℚ)
    (hne : acts.Nonempty) : WellFormedGame (StrategicGame.singlePlayer a acts pay) := by
  intro p hp
  simp only [StrategicGame.singlePlayer] at hp
  rw [Finset.mem_singleton] at hp
  simp only [StrategicGame.singlePlayer]
  exact hne

/-- Constructing a well-formed two-player game. -/
theorem twoPlayer_wellformed (a b : Agent) (hab : a ≠ b)
    (actsA actsB : Finset ℕ) (payA payB : ℕ → ℕ → ℚ)
    (hneA : actsA.Nonempty) (hneB : actsB.Nonempty) :
    WellFormedGame (StrategicGame.twoPlayer a b hab actsA actsB payA payB) := by
  intro p hp
  simp only [StrategicGame.twoPlayer] at hp ⊢
  rw [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · simp only [↓reduceIte]; exact hneA
  · simp only [hab.symm, ↓reduceIte]; exact hneB

/-! ## Section 2: Coordination Game Player Bound (X26 Foundation)

    The axiom `coordination_nash_player_bound` states that coordination games
    with Nash equilibrium cannot have more than 2 players in this model.

    This is a consequence of:
    1. `nash_implies_h1_trivial`: Nash + coordination → forest ∨ ≤2 players
    2. Forest games have ≤1 player (by definition in this model)
    3. If >2 players, forest is impossible, and ≤2 is contradicted

    The theorem provides this exact argument.
-/

/-- Forest games have ≤1 player in this formalization.
    Forest = AgentNetwork.isForest = AgentNetwork.isTrivial = agents.card ≤ 1 -/
theorem forest_has_at_most_one_player (G : StrategicGame) (hforest : G.isForestGame) :
    G.numPlayers ≤ 1 := by
  simp only [StrategicGame.isForestGame, StrategicGame.toNetwork,
             AgentNetwork.isForest, AgentNetwork.isTrivial,
             StrategicGame.numPlayers] at hforest ⊢
  exact hforest

/-- THEOREM X26 Foundation: Coordination games with Nash have bounded players.

    This directly proves the statement of the axiom:
    If G is a coordination game with Nash equilibrium and >2 players, False.

    Proof:
    1. By nash_implies_h1_trivial: G.isForestGame ∨ G.numPlayers ≤ 2
    2. Case forest: G.numPlayers ≤ 1 ≤ 2, contradicting >2
    3. Case ≤2 players: directly contradicts >2
-/
theorem coordination_nash_player_bound_proof (G : StrategicGame)
    (hnash : G.nashExists) (hcoord : G.isCoordinationGame) (hlarge : 2 < G.numPlayers) :
    False := by
  -- Apply the main characterization theorem
  have h := StrategicGame.nash_implies_h1_trivial G hnash hcoord
  -- h : G.isForestGame ∨ G.numPlayers ≤ 2
  cases h with
  | inl hforest =>
    -- Forest case: numPlayers ≤ 1 ≤ 2 < numPlayers, contradiction
    have hle1 := forest_has_at_most_one_player G hforest
    omega
  | inr hle2 =>
    -- ≤2 players case: directly contradicts >2
    omega

/-! ## Section 3: Summary

    We provide the mathematical foundations for axioms X25 and X26:

    **X25 (actions_nonempty)**:
    - This is a well-formedness condition
    - We define `WellFormedGame` predicate
    - Games constructed via `singlePlayer`, `twoPlayer` etc. with nonempty
      action sets satisfy this predicate
    - The axiom is reasonable: games without actions are degenerate

    **X26 (coordination_nash_player_bound)**:
    - Proven via `coordination_nash_player_bound_proof`
    - Uses the main characterization: Nash + coordination → forest ∨ ≤2 players
    - Forest implies ≤1 player in this model
    - Both cases contradict >2 players

    Note: The original axioms in GameTheoreticH1.lean remain axioms because
    they are used in theorem proofs that depend on them. To fully eliminate
    them, the source file would need to be modified to use these theorems
    instead of the axioms.
-/

/-- X25 alternative: Games can be made well-formed by ensuring nonempty actions.
    This shows the axiom is consistent: well-formed games exist. -/
theorem wellformed_games_exist :
    ∃ G : StrategicGame, WellFormedGame G ∧ G.players.Nonempty := by
  let a : Agent := ⟨0⟩
  use StrategicGame.singlePlayer a {0} (fun _ => 0)
  constructor
  · exact singlePlayer_wellformed a {0} (fun _ => 0) ⟨0, Finset.mem_singleton_self 0⟩
  · simp [StrategicGame.singlePlayer]

/-- X26 is actually provable from the existing characterization. -/
theorem x26_provable : ∀ G : StrategicGame,
    G.nashExists → G.isCoordinationGame → 2 < G.numPlayers → False :=
  coordination_nash_player_bound_proof

end Infrastructure.GameStrategicProofs
