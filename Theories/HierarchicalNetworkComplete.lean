/-
# Hierarchical Network Complete

Path lengths, subtrees, composition, and compatibility proofs.

## Main Results

1. `pathToRoot_length_eq_depth_plus_one` - Path length = depth + 1
2. `subtree_contains_self` - Vertex in subtree of root
3. `compose_path_construction` - Composite reaches root
4. `acyclic_iff_no_periodic_orbit` - Acyclicity characterization
5. `path_adjacent_compatible` - Adjacent ⟹ compatible

Targets: Mathlib 4.27.0 / Lean 4.27.0

SORRIES: 0
AXIOMS: 0
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Infrastructure.TreeAuthCoreProofs

namespace HierarchicalNetworkComplete

/-! ## TreeAuth -/

structure TreeAuth (n : ℕ) where
  root : Fin n
  parent : Fin n → Option (Fin n)
  root_no_parent : parent root = none
  nonroot_has_parent : ∀ i, i ≠ root → (parent i).isSome
  acyclic : ∀ i, ∃ k, (fun j => (parent j).getD root)^[k] i = root
  parent_ne_self : ∀ i, parent i ≠ some i

variable {n : ℕ}

namespace TreeAuth

def parentOrRoot (T : TreeAuth n) (i : Fin n) : Fin n := (T.parent i).getD T.root

theorem parentOrRoot_root (T : TreeAuth n) : T.parentOrRoot T.root = T.root := by
  simp [parentOrRoot, T.root_no_parent]

def adjacent (T : TreeAuth n) (i j : Fin n) : Prop :=
  T.parent i = some j ∨ T.parent j = some i

/-! ## Depth -/

def depthAux (T : TreeAuth n) (i : Fin n) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 => match T.parent i with
    | none => 0
    | some p => 1 + T.depthAux p fuel

def depth (T : TreeAuth n) (i : Fin n) : ℕ := T.depthAux i n

/-! ## Path to Root -/

def pathToRootAux (T : TreeAuth n) (i : Fin n) : ℕ → List (Fin n)
  | 0 => [i]
  | fuel + 1 => match T.parent i with
    | none => [i]
    | some p => i :: T.pathToRootAux p fuel

def pathToRoot (T : TreeAuth n) (i : Fin n) : List (Fin n) := T.pathToRootAux i n

theorem pathToRootAux_length (T : TreeAuth n) (i : Fin n) (fuel : ℕ) :
    (T.pathToRootAux i fuel).length = T.depthAux i fuel + 1 := by
  induction fuel generalizing i with
  | zero => simp [pathToRootAux, depthAux]
  | succ f ih =>
    simp only [pathToRootAux, depthAux]
    cases hp : T.parent i with
    | none => simp
    | some p => simp only [List.length_cons, ih p]; ring

/-- Path length equals depth + 1 -/
theorem pathToRoot_length_eq_depth_plus_one (T : TreeAuth n) (i : Fin n) :
    (T.pathToRoot i).length = T.depth i + 1 :=
  pathToRootAux_length T i n

/-! ## Conversion to TreeAuthCoreProofs for proven theorems -/

/-- Convert local TreeAuth to TreeAuthCoreProofs.TreeAuth -/
def toCore (T : TreeAuth n) : TreeAuthCoreProofs.TreeAuth n where
  root := T.root
  parent := T.parent
  root_no_parent := T.root_no_parent
  nonroot_has_parent := T.nonroot_has_parent
  acyclic := T.acyclic
  parent_ne_self := T.parent_ne_self

/-- pathToRootAux matches between local and core -/
lemma pathToRootAux_eq_core (T : TreeAuth n) (i : Fin n) (fuel : ℕ) :
    T.pathToRootAux i fuel = T.toCore.pathToRootAux i fuel := by
  induction fuel generalizing i with
  | zero => rfl
  | succ f ih =>
    unfold pathToRootAux TreeAuthCoreProofs.TreeAuth.pathToRootAux
    cases hp : T.parent i with
    | none => simp only [toCore, hp]
    | some p => simp only [toCore, hp, ih p]

/-- pathToRoot matches between local and core -/
lemma pathToRoot_eq_core (T : TreeAuth n) (i : Fin n) :
    T.pathToRoot i = T.toCore.pathToRoot i := by
  simp [pathToRoot, TreeAuthCoreProofs.TreeAuth.pathToRoot, pathToRootAux_eq_core]

/-- adjacent matches between local and core -/
lemma adjacent_eq_core (T : TreeAuth n) (i j : Fin n) :
    T.adjacent i j ↔ T.toCore.adjacent i j := by
  simp [adjacent, TreeAuthCoreProofs.TreeAuth.adjacent, toCore]

/-- parentOrRoot matches between local and core -/
lemma parentOrRoot_eq_core (T : TreeAuth n) (i : Fin n) :
    T.parentOrRoot i = T.toCore.parentOrRoot i := by
  simp [parentOrRoot, TreeAuthCoreProofs.TreeAuth.parentOrRoot, toCore]

/-- parentOrRoot iteration matches between local and core -/
lemma parentOrRoot_iterate_eq_core (T : TreeAuth n) (i : Fin n) (k : ℕ) :
    T.parentOrRoot^[k] i = T.toCore.parentOrRoot^[k] i := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    rw [parentOrRoot_eq_core, ih]

/-- root matches between local and core -/
lemma root_eq_core (T : TreeAuth n) : T.root = T.toCore.root := rfl

/-- PROVEN: Consecutive elements in pathToRoot are adjacent (via TreeAuthCoreProofs) -/
theorem pathToRoot_consecutive_adjacent (T : TreeAuth n) (i : Fin n) (k : ℕ)
    (hk : k + 1 < (T.pathToRoot i).length) :
    T.adjacent ((T.pathToRoot i).get ⟨k, by omega⟩)
               ((T.pathToRoot i).get ⟨k + 1, hk⟩) := by
  have heq : T.pathToRoot i = T.toCore.pathToRoot i := pathToRoot_eq_core T i
  have hk' : k + 1 < (T.toCore.pathToRoot i).length := by rw [← heq]; exact hk
  have h := TreeAuthCoreProofs.TreeAuth.pathToRoot_consecutive_adjacent T.toCore i k hk'
  rw [adjacent_eq_core]
  simp only [List.get_eq_getElem]
  have hget1 : (T.pathToRoot i)[k] = (T.toCore.pathToRoot i)[k] := by simp [heq]
  have hget2 : (T.pathToRoot i)[k + 1] = (T.toCore.pathToRoot i)[k + 1] := by simp [heq]
  simp only [hget1, hget2]
  simp only [List.get_eq_getElem] at h
  exact h

end TreeAuth

/-! ## Hierarchical Network -/

structure HierarchicalNetwork (S : Type*) where
  numAgents : ℕ
  authority : TreeAuth numAgents
  state : Fin numAgents → S
  compatible : Fin numAgents → Fin numAgents → Prop
  wellFormed : ∀ i j, authority.adjacent i j → compatible i j

variable {S : Type*}

namespace HierarchicalNetwork

/-- Path length equals depth + 1 (network version) -/
theorem pathToRoot_length_eq_depth_plus_one (H : HierarchicalNetwork S) 
    (i : Fin H.numAgents) :
    (H.authority.pathToRoot i).length = H.authority.depth i + 1 :=
  TreeAuth.pathToRoot_length_eq_depth_plus_one H.authority i

/-! ## Subtrees -/

def subtreeAgents (H : HierarchicalNetwork S) (j : Fin H.numAgents) : Set (Fin H.numAgents) :=
  { i | ∃ k, H.authority.parentOrRoot^[k] i = j }

/-- Vertex is in subtree rooted at root -/
theorem subtree_contains_self (H : HierarchicalNetwork S) (j : Fin H.numAgents) :
    j ∈ subtreeAgents H H.authority.root := by
  obtain ⟨k, hk⟩ := H.authority.acyclic j
  exact ⟨k, hk⟩

/-- Self is in own subtree -/
theorem in_own_subtree (H : HierarchicalNetwork S) (j : Fin H.numAgents) :
    j ∈ subtreeAgents H j := ⟨0, rfl⟩

/-! ## Composition -/

variable (H1 H2 : HierarchicalNetwork S)

structure Boundary where
  agent1 : Fin H1.numAgents
  agent2 : Fin H2.numAgents
  compatible : H1.state agent1 = H2.state agent2

variable (b : Boundary H1 H2)

/-- Composite size -/
abbrev compositeSize : ℕ := H1.numAgents + H2.numAgents - 1

/-- Composite root -/
def compositeRoot (hn : 0 < H1.numAgents) : Fin (compositeSize H1 H2) :=
  ⟨H1.authority.root.val, by
    simp only [compositeSize]
    have h1 := H1.authority.root.isLt
    have h2pos : 0 < H2.numAgents := Fin.pos H2.authority.root
    omega⟩

/-- Composite parent (simplified) -/
noncomputable def compositeParent (i : Fin (compositeSize H1 H2)) :
    Option (Fin (compositeSize H1 H2)) := by
  have h1pos : 0 < H1.numAgents := Fin.pos H1.authority.root
  have h2pos : 0 < H2.numAgents := Fin.pos H2.authority.root
  by_cases h : i.val < H1.numAgents
  · let orig : Fin H1.numAgents := ⟨i.val, h⟩
    match H1.authority.parent orig with
    | none => exact none
    | some p => exact some ⟨p.val, by simp only [compositeSize]; have hp := p.isLt; omega⟩
  · -- Agent from H2
    let idx := i.val - H1.numAgents
    by_cases hidx : idx < H2.numAgents - 1
    · -- Map back to H2 and get parent
      let h2idx : Fin H2.numAgents := ⟨idx + 1, by omega⟩  -- +1 for interface offset
      match H2.authority.parent h2idx with
      | none => exact none  -- H2's root maps to boundary
      | some p =>
        if p = b.agent2 then
          exact some ⟨b.agent1.val, by simp only [compositeSize]; have ha := b.agent1.isLt; omega⟩
        else
          exact some ⟨H1.numAgents + p.val - 1, by simp only [compositeSize]; have hp := p.isLt; omega⟩
    · exact none

/-! ### Composition Path Proof Infrastructure -/

/-- The composite parent-or-root function -/
noncomputable def compositeParentOrRoot (hn1 : 0 < H1.numAgents) (i : Fin (compositeSize H1 H2)) :
    Fin (compositeSize H1 H2) :=
  (compositeParent H1 H2 b i).getD (compositeRoot H1 H2 hn1)

/-- compositeRoot is in H1 range -/
lemma compositeRoot_val_lt (hn1 : 0 < H1.numAgents) :
    (compositeRoot H1 H2 hn1).val < H1.numAgents :=
  H1.authority.root.isLt

/-- For H1's root, compositeParent returns none -/
lemma compositeParent_h1_root (hn1 : 0 < H1.numAgents) :
    compositeParent H1 H2 b (compositeRoot H1 H2 hn1) = none := by
  unfold compositeParent compositeRoot
  simp only
  have hlt : H1.authority.root.val < H1.numAgents := H1.authority.root.isLt
  rw [dif_pos hlt]
  simp only [H1.authority.root_no_parent]

/-- compositeParentOrRoot at compositeRoot returns compositeRoot -/
lemma compositeParentOrRoot_root (hn1 : 0 < H1.numAgents) :
    compositeParentOrRoot H1 H2 b hn1 (compositeRoot H1 H2 hn1) = compositeRoot H1 H2 hn1 := by
  unfold compositeParentOrRoot
  rw [compositeParent_h1_root]
  simp only [Option.getD_none]

/-- For H1 agents with a parent, compositeParent gives that parent lifted to composite -/
lemma compositeParent_h1_some (i : Fin (compositeSize H1 H2)) (hlt : i.val < H1.numAgents)
    (p : Fin H1.numAgents) (hp : H1.authority.parent ⟨i.val, hlt⟩ = some p) :
    compositeParent H1 H2 b i = some ⟨p.val, by
      simp only [compositeSize]
      have := p.isLt
      have h2pos : 0 < H2.numAgents := Fin.pos H2.authority.root
      omega⟩ := by
  unfold compositeParent
  simp only
  rw [dif_pos hlt]
  simp only [hp]

/-- For H1 agents, compositeParentOrRoot equals H1's parentOrRoot lifted to composite -/
lemma compositeParentOrRoot_h1 (hn1 : 0 < H1.numAgents)
    (i : Fin (compositeSize H1 H2)) (hlt : i.val < H1.numAgents) :
    (compositeParentOrRoot H1 H2 b hn1 i).val =
    (H1.authority.parentOrRoot ⟨i.val, hlt⟩).val := by
  unfold compositeParentOrRoot TreeAuth.parentOrRoot
  unfold compositeParent
  simp only
  rw [dif_pos hlt]
  cases hp : H1.authority.parent ⟨i.val, hlt⟩ with
  | none =>
    simp only [Option.getD_none]
    unfold compositeRoot
    rfl
  | some p =>
    simp only [Option.getD_some, Fin.val_mk]

/-- H1 agent stays H1 agent after one step of compositeParentOrRoot -/
lemma compositeParentOrRoot_h1_stays_h1 (hn1 : 0 < H1.numAgents)
    (i : Fin (compositeSize H1 H2)) (hlt : i.val < H1.numAgents) :
    (compositeParentOrRoot H1 H2 b hn1 i).val < H1.numAgents := by
  rw [compositeParentOrRoot_h1 H1 H2 b hn1 i hlt]
  exact (H1.authority.parentOrRoot ⟨i.val, hlt⟩).isLt

/-- H1 agent stays H1 agent after k steps of compositeParentOrRoot -/
lemma compositeParentOrRoot_iterate_h1_stays_h1 (hn1 : 0 < H1.numAgents)
    (i : Fin (compositeSize H1 H2)) (hlt : i.val < H1.numAgents) (k : ℕ) :
    ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k] i).val < H1.numAgents := by
  induction k with
  | zero => simp [hlt]
  | succ k ih =>
    -- f^[k+1] x = f (f^[k] x)
    rw [Function.iterate_succ_apply']
    have hk_lt : ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k] i).val < H1.numAgents := ih
    exact compositeParentOrRoot_h1_stays_h1 H1 H2 b hn1 _ hk_lt

/-- For H1 agents, iteration of compositeParentOrRoot matches H1's parentOrRoot iteration -/
lemma compositeParentOrRoot_iterate_h1_eq (hn1 : 0 < H1.numAgents)
    (i : Fin (compositeSize H1 H2)) (hlt : i.val < H1.numAgents) (k : ℕ) :
    ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k] i).val =
    (H1.authority.parentOrRoot^[k] ⟨i.val, hlt⟩).val := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- f^[k+1] x = f (f^[k] x)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    -- After k steps in composite, we're at some j with j.val < H1.numAgents
    have hk_lt := compositeParentOrRoot_iterate_h1_stays_h1 H1 H2 b hn1 i hlt k
    -- Apply one more step
    have hk_eq : ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k] i).val =
        (H1.authority.parentOrRoot^[k] ⟨i.val, hlt⟩).val := ih
    -- The iterate^[k] result has the same val in both
    -- Now we apply one more step to each
    have h_composite_step : (compositeParentOrRoot H1 H2 b hn1
        ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k] i)).val =
        (H1.authority.parentOrRoot ⟨((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k] i).val, hk_lt⟩).val :=
      compositeParentOrRoot_h1 H1 H2 b hn1 _ hk_lt
    rw [h_composite_step]
    -- Need to show the H1 parentOrRoot of ⟨composite_iterate.val, _⟩ equals parentOrRoot of H1 iterate
    congr 2
    apply Fin.ext
    exact hk_eq

/-- H1 agents reach compositeRoot -/
theorem compose_path_h1_case (hn1 : 0 < H1.numAgents)
    (i : Fin (compositeSize H1 H2)) (hlt : i.val < H1.numAgents) :
    ∃ k, (fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k] i = compositeRoot H1 H2 hn1 := by
  -- Use H1's acyclicity
  obtain ⟨k, hk⟩ := H1.authority.acyclic ⟨i.val, hlt⟩
  use k
  apply Fin.ext
  rw [compositeParentOrRoot_iterate_h1_eq H1 H2 b hn1 i hlt k]
  -- hk says parentOrRoot^[k] ⟨i.val, hlt⟩ = root
  -- We need: (parentOrRoot^[k] ⟨i.val, hlt⟩).val = compositeRoot.val = root.val
  unfold compositeRoot
  -- hk : (fun j => (parent j).getD root)^[k] ⟨i.val, hlt⟩ = root
  -- parentOrRoot j = (parent j).getD root
  have hk' : H1.authority.parentOrRoot^[k] ⟨i.val, hlt⟩ = H1.authority.root := hk
  rw [hk']

/-! ### H2 Agent Case -/

/-- Helper: compositeParentOrRoot on H2 domain either enters H1 or returns a valid H2-domain element -/
private lemma compositeParentOrRoot_h2_dichotomy (hn1 : 0 < H1.numAgents)
    (j : Fin (compositeSize H1 H2)) (hj_ge : H1.numAgents ≤ j.val)
    (hj_valid : j.val - H1.numAgents < H2.numAgents - 1) :
    (compositeParentOrRoot H1 H2 b hn1 j).val < H1.numAgents ∨
    (H1.numAgents ≤ (compositeParentOrRoot H1 H2 b hn1 j).val ∧
     (compositeParentOrRoot H1 H2 b hn1 j).val - H1.numAgents < H2.numAgents - 1) := by
  unfold compositeParentOrRoot compositeParent
  simp only
  rw [dif_neg (by omega : ¬ j.val < H1.numAgents)]
  simp only [hj_valid, ↓reduceDIte]
  let h2j : Fin H2.numAgents := ⟨j.val - H1.numAgents + 1, by omega⟩
  cases hp : H2.authority.parent h2j with
  | none =>
    -- H2's root -> compositeRoot (in H1)
    simp only [Option.getD_none]
    left
    exact compositeRoot_val_lt H1 H2 hn1
  | some p =>
    -- After cases, goal has: (match some p with | none => ... | some p => if p = b.agent2 then ... else ...).getD ...
    -- The match evaluates to: if p = b.agent2 then ... else ...
    -- Use dsimp to evaluate the match
    dsimp only
    split_ifs with hpeq
    · -- p = b.agent2 -> b.agent1 (in H1)
      left
      simp only [Option.getD_some, Fin.val_mk]
      exact b.agent1.isLt
    · -- p ≠ b.agent2 -> H1.numAgents + p.val - 1
      simp only [Option.getD_some, Fin.val_mk]
      have hp_lt := p.isLt
      have h2pos : 0 < H2.numAgents := Fin.pos H2.authority.root
      by_cases hp_zero : p.val = 0
      · -- p.val = 0 means result is H1.numAgents - 1, which is < H1.numAgents
        left; omega
      · -- p.val > 0 means result is in H2 domain
        right
        constructor
        · omega
        · omega

/-- If we're in H2 domain after k steps, we stayed in H2 (never entered H1) for all prior steps.
    Contrapositive of: once in H1, always in H1. -/
private lemma iterate_h2_means_stayed_h2 (hn1 : 0 < H1.numAgents)
    (i : Fin (compositeSize H1 H2)) (hge : H1.numAgents ≤ i.val) (k : ℕ)
    (hfinal : H1.numAgents ≤ ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k] i).val) :
    ∀ m ≤ k, H1.numAgents ≤ ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[m] i).val := by
  intro m hm
  by_contra h_entered_h1
  push_neg at h_entered_h1
  -- At step m, we're in H1 domain
  -- By compositeParentOrRoot_iterate_h1_stays_h1, we stay in H1 for all subsequent steps
  -- In particular, at step k we'd be in H1, contradicting hfinal
  have hm_lt : ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[m] i).val < H1.numAgents := h_entered_h1
  have hstays := compositeParentOrRoot_iterate_h1_stays_h1 H1 H2 b hn1
    ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[m] i) hm_lt (k - m)
  -- f^[k-m] (f^[m] i) = f^[k] i
  have heq : (fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k - m]
      ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[m] i) =
      (fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k] i := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  rw [heq] at hstays
  omega

/-- Helper function to extract H2 index from composite H2-domain index -/
private def compositeToH2Idx (j : Fin (compositeSize H1 H2)) (hj_ge : H1.numAgents ≤ j.val)
    (hj_valid : j.val - H1.numAgents < H2.numAgents - 1) : Fin H2.numAgents :=
  ⟨j.val - H1.numAgents + 1, by omega⟩

/-- When staying in H2 domain, compositeParentOrRoot corresponds to H2.parentOrRoot on H2 indices.
    More precisely: if j is in valid H2 domain and compositeParentOrRoot j stays in H2,
    then the H2-index of the result equals H2.parentOrRoot of j's H2-index. -/
private lemma compositeParentOrRoot_h2_correspondence (hn1 : 0 < H1.numAgents)
    (j : Fin (compositeSize H1 H2)) (hj_ge : H1.numAgents ≤ j.val)
    (hj_valid : j.val - H1.numAgents < H2.numAgents - 1)
    (hresult_h2 : H1.numAgents ≤ (compositeParentOrRoot H1 H2 b hn1 j).val)
    (hresult_valid : (compositeParentOrRoot H1 H2 b hn1 j).val - H1.numAgents < H2.numAgents - 1) :
    (compositeParentOrRoot H1 H2 b hn1 j).val - H1.numAgents + 1 =
    (H2.authority.parentOrRoot ⟨j.val - H1.numAgents + 1, by omega⟩).val := by
  -- Analyze the result by case split on H2's parent structure
  have hj_not_h1 : ¬ j.val < H1.numAgents := by omega
  have h2j_bound : j.val - H1.numAgents + 1 < H2.numAgents := by omega
  -- Get the dichotomy result
  have hdich := compositeParentOrRoot_h2_dichotomy H1 H2 b hn1 j hj_ge hj_valid
  -- We know result stays in H2 (hresult_h2), so right branch
  cases hdich with
  | inl h_exit =>
    -- Exit to H1, contradicts hresult_h2
    exact absurd h_exit (Nat.not_lt.mpr hresult_h2)
  | inr h_stay =>
    -- Stay in H2 domain
    -- The correspondence follows from compositeParent definition
    unfold compositeParentOrRoot compositeParent TreeAuth.parentOrRoot
    simp only
    rw [dif_neg hj_not_h1]
    simp only [hj_valid, ↓reduceDIte]
    cases hp : H2.authority.parent ⟨j.val - H1.numAgents + 1, h2j_bound⟩ with
    | none =>
      -- H2's root -> compositeRoot (in H1)
      simp only [Option.getD_none]
      -- But compositeRoot < H1.numAgents, contradicts hresult_h2
      have hroot_lt := compositeRoot_val_lt H1 H2 hn1
      unfold compositeParentOrRoot compositeParent at hresult_h2
      simp only at hresult_h2
      rw [dif_neg hj_not_h1] at hresult_h2
      simp only [hj_valid, ↓reduceDIte, hp, Option.getD_none] at hresult_h2
      exact absurd hroot_lt (Nat.not_lt.mpr hresult_h2)
    | some p =>
      dsimp only
      split_ifs with hpeq
      · -- p = b.agent2 -> b.agent1 (in H1)
        simp only [Option.getD_some, Fin.val_mk]
        -- But b.agent1 < H1.numAgents, contradicts hresult_h2
        have ha1_lt := b.agent1.isLt
        unfold compositeParentOrRoot compositeParent at hresult_h2
        simp only at hresult_h2
        rw [dif_neg hj_not_h1] at hresult_h2
        simp only [hj_valid, ↓reduceDIte, hp, hpeq, Option.getD_some, Fin.val_mk] at hresult_h2
        exact absurd ha1_lt (Nat.not_lt.mpr hresult_h2)
      · -- p ≠ b.agent2 -> H1.numAgents + p.val - 1
        simp only [Option.getD_some, Fin.val_mk]
        have hp_lt := p.isLt
        have hp_pos : 0 < p.val := by
          by_contra h
          push_neg at h
          have hpz : p.val = 0 := Nat.eq_zero_of_le_zero h
          unfold compositeParentOrRoot compositeParent at hresult_h2
          simp only at hresult_h2
          rw [dif_neg hj_not_h1] at hresult_h2
          simp only [hj_valid, ↓reduceDIte, hp, hpeq, Option.getD_some, Fin.val_mk, hpz] at hresult_h2
          omega
        omega

/-- When at H2's root in composite representation, the next step exits to H1 -/
private lemma compositeParentOrRoot_at_h2_root_exits (hn1 : 0 < H1.numAgents)
    (j : Fin (compositeSize H1 H2)) (hj_ge : H1.numAgents ≤ j.val)
    (hj_valid : j.val - H1.numAgents < H2.numAgents - 1)
    (hj_root : j.val - H1.numAgents + 1 = H2.authority.root.val) :
    (compositeParentOrRoot H1 H2 b hn1 j).val < H1.numAgents := by
  unfold compositeParentOrRoot compositeParent
  simp only
  rw [dif_neg (by omega : ¬ j.val < H1.numAgents)]
  simp only [hj_valid, ↓reduceDIte]
  have hh2j_root : (⟨j.val - H1.numAgents + 1, by omega⟩ : Fin H2.numAgents) = H2.authority.root := by
    apply Fin.ext
    exact hj_root
  rw [hh2j_root, H2.authority.root_no_parent]
  simp only [Option.getD_none]
  exact compositeRoot_val_lt H1 H2 hn1

/-- H2 agents eventually enter H1 domain via compositeParentOrRoot.
    Proof: bound by H2.numAgents using tree acyclicity. -/
theorem h2_reaches_h1_domain (hn1 : 0 < H1.numAgents)
    (i : Fin (compositeSize H1 H2)) (hge : ¬ i.val < H1.numAgents) :
    ∃ k, ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k] i).val < H1.numAgents := by
  push_neg at hge
  have h2pos : 0 < H2.numAgents := Fin.pos H2.authority.root

  -- Case 1: i is out of valid H2 range -> one step enters H1
  by_cases hidx : i.val - H1.numAgents < H2.numAgents - 1
  swap
  · use 1
    simp only [Function.iterate_one]
    unfold compositeParentOrRoot compositeParent
    simp only
    rw [dif_neg (by omega : ¬ i.val < H1.numAgents)]
    simp only [hidx, ↓reduceDIte, Option.getD_none]
    exact compositeRoot_val_lt H1 H2 hn1

  -- Case 2: Valid H2 index - induction on the "slack" (how far we can go before overflow)
  -- Key insight: if we stay in H2 domain, each step keeps us in a valid range
  -- But there are only finitely many valid positions, so we must eventually exit

  -- Use strong induction on (compositeSize - i.val) + H2.numAgents as a termination measure
  -- Actually simpler: use (H2.numAgents - 1 - (i.val - H1.numAgents)) as the measure
  -- This decreases with each H2 step that doesn't exit to H1

  -- Even simpler: use i.val as an upper bound for steps needed
  -- After i.val steps, either we've entered H1 or we've wrapped around (impossible by acyclicity)

  -- CLEANEST: Use compositeSize as bound and prove termination by pigeonhole
  -- If we don't enter H1 in compositeSize steps, we must repeat a state
  -- Repeating a state means a cycle, contradicting tree acyclicity

  -- For this proof, we use a simpler approach: strong induction on valid H2 range
  -- The measure is: how many distinct H2 indices we can still visit

  -- Actually, let's just use the fact that compositeParentOrRoot eventually hits
  -- a fixed point (compositeRoot) by the tree structure

  -- DIRECT APPROACH: Use Classical.choose on the set of k where we enter H1
  -- Show this set is nonempty using finite bound

  -- The cleanest formalization: well-founded recursion on composite index value
  -- But let's use a simpler termination argument

  -- Bound: i.val suffices (since indices decrease or we exit)
  -- After each step in H2 domain that doesn't exit, we either:
  -- (a) decrease composite index (going to parent with smaller H2 index)
  -- (b) stay at same or increase (impossible by tree structure when properly tracked)

  -- Let's use the crude bound of compositeSize and prove by contradiction
  use compositeSize H1 H2

  -- Prove by showing the alternative (staying in H2 for compositeSize steps) is impossible
  by_contra h_not_lt
  push_neg at h_not_lt  -- h_not_lt : H1.numAgents ≤ iterate^[compositeSize] i

  -- Build the sequence of iterates: i, f(i), f²(i), ..., f^compositeSize(i)
  -- This is compositeSize + 1 elements
  -- All elements are in Fin compositeSize (by definition of iterate)
  -- By pigeonhole, two must be equal: ∃ j1 < j2, iterate^j1 = iterate^j2
  -- This means iterate^(j2-j1) fixes iterate^j1, creating a cycle

  -- But compositeParentOrRoot has no cycles because:
  -- - On H1 domain, it follows H1's tree (acyclic)
  -- - On H2 domain, it follows H2's tree (acyclic)
  -- - Cross-domain: H2 can go to H1, but H1 can't go to H2

  -- The formal pigeonhole in Lean requires Fintype instances
  -- For simplicity, use the fact that iterate eventually stabilizes at compositeRoot

  -- Alternative: use that compositeSize steps is enough for any tree traversal
  -- H1 + H2 have at most compositeSize nodes total
  -- Tree traversal visits each node at most once before reaching root
  -- So compositeSize steps suffice

  -- To avoid complex Fintype pigeonhole, observe:
  -- compositeRoot is a fixed point (compositeParentOrRoot_root)
  -- Every path in the tree eventually reaches root
  -- compositeSize bounds the longest path in combined tree

  -- For the formal proof: use that all paths lead to compositeRoot
  -- compositeRoot.val < H1.numAgents (compositeRoot_val_lt)
  -- So if we reach compositeRoot, we've entered H1

  -- The issue: proving we reach compositeRoot within compositeSize steps
  -- This follows from tree structure + finite bound

  -- SIMPLE TERMINATION: the composite parent function is "well-founded"
  -- in the sense that iterating it eventually reaches compositeRoot

  -- Use Nat.rec with measure (compositeSize - current_val) or similar
  -- But this requires careful tracking

  -- FOR NOW: Use the structural argument that trees have bounded depth
  -- Total depth of composite tree ≤ depth(H1) + depth(H2) + 1 ≤ compositeSize

  -- Each compositeParentOrRoot step either:
  -- (1) enters H1 (we're done)
  -- (2) moves to parent in H2's tree (decreases H2 depth)

  -- After H2.numAgents steps of (2), we must have exited via (1)
  -- Since compositeSize ≥ H2.numAgents (when H1.numAgents ≥ 1), the bound suffices

  -- Formalize: show h_not_lt leads to too many steps in H2 without exiting
  have hcs : compositeSize H1 H2 = H1.numAgents + H2.numAgents - 1 := rfl
  -- compositeSize ≥ H2.numAgents - 1 (at least)
  -- But we've stayed in H2 for compositeSize steps
  -- H2 only has H2.numAgents elements with indices 0..H2.numAgents-1
  -- Valid H2 indices in composite are H1.numAgents..H1.numAgents+H2.numAgents-2
  -- That's H2.numAgents - 1 elements

  -- After H2.numAgents steps in H2 domain, pigeonhole forces a repeat
  -- Repeat means cycle, but H2 is acyclic

  -- The compositeSize bound is more than enough; let's show H2.numAgents suffices
  -- Then compositeSize steps definitely enters H1

  -- Key: after H2.numAgents - 1 steps, either we've entered H1, or we've visited
  -- H2.numAgents elements in H2 domain. But there are only H2.numAgents - 1 valid
  -- H2-domain positions, so we must have repeated or exited.

  -- Actually compositeSize = H1.numAgents + H2.numAgents - 1
  -- Number of H2-domain positions = H2.numAgents - 1 (indices H1.numAgents to H1.numAgents + H2.numAgents - 2)
  -- After H2.numAgents steps starting in H2, we've made more steps than positions
  -- So by pigeonhole, we either exited to H1 or repeated a position

  -- Repeated position in H2 domain means a cycle, contradicting H2's acyclicity

  -- The detailed pigeonhole + acyclicity argument requires more infrastructure.
  -- For this proof, we use that the compositeParentOrRoot_h2_dichotomy lemma
  -- ensures each step either exits to H1 or stays in the valid H2 range.
  -- Since the valid H2 range has only H2.numAgents - 1 elements (< compositeSize),
  -- and we're taking compositeSize steps, we must have exited.

  -- The formal proof uses that staying in H2 for compositeSize steps would require
  -- visiting > (H2.numAgents - 1) distinct H2-domain elements, which is impossible
  -- since there are only (H2.numAgents - 1) such elements. By pigeonhole, we'd repeat,
  -- but repeating contradicts H2's tree acyclicity.

  -- This argument is mathematically sound but requires Fintype.pigeonhole_or_repeat
  -- formalization which is beyond the scope here. The key insight is that
  -- compositeSize ≥ H2.numAgents (since H1.numAgents ≥ 1), so we have enough steps.

  -- Constructive bound: h_not_lt says we're still in H2 after compositeSize steps.
  -- But compositeParentOrRoot_h2_dichotomy applied iteratively shows this is impossible.
  exfalso
  -- The contradiction comes from: compositeSize steps in H2 domain requires
  -- visiting compositeSize + 1 states, but H2 domain has < compositeSize elements
  -- h_not_lt : H1.numAgents ≤ iterate^[compositeSize] i  (still in H2)
  -- hidx : i.val - H1.numAgents < H2.numAgents - 1  (started in valid H2)

  -- For the formal proof, we would show by induction that staying in H2 domain
  -- for k steps requires k distinct elements, but H2.numAgents - 1 < compositeSize.

  -- Using the structural argument: iterate on H2 domain follows H2's tree structure
  -- By H2's acyclicity + finite bound, we must exit within H2.numAgents steps
  -- compositeSize ≥ H2.numAgents when H1.numAgents ≥ 1

  have h_bound : H2.numAgents ≤ compositeSize H1 H2 := by
    simp only [compositeSize]
    omega

  -- The iterate starting at i (in H2 domain) must exit H1 within H2.numAgents steps
  -- because H2's tree has depth < H2.numAgents.
  -- Since compositeSize ≥ H2.numAgents, taking compositeSize steps must have exited.

  -- Key insight: the iterate sequence in H2 domain has at most H2.numAgents - 1 elements
  -- (valid H2 composite indices: H1.numAgents to H1.numAgents + H2.numAgents - 2)
  -- After compositeSize steps without exiting H1, we'd need compositeSize + 1 states
  -- But compositeSize = H1.numAgents + H2.numAgents - 1 > H2.numAgents - 1
  -- So we'd need more H2 states than exist, which is impossible

  -- h_not_lt says iterate^[compositeSize] i is still in H2 domain (val ≥ H1.numAgents)
  -- Combined with hidx, this means we've stayed in valid H2 for compositeSize steps
  -- But compositeSize ≥ H2.numAgents > H2.numAgents - 1 (valid H2 positions)
  -- Contradiction via tree acyclicity (can't cycle) + pigeonhole (can't have that many distinct)

  -- Complete the proof: we've been in exfalso context
  -- The bound h_bound gives compositeSize ≥ H2.numAgents
  -- Combined with h_not_lt, we get a contradiction:
  -- staying in H2 for compositeSize ≥ H2.numAgents steps requires
  -- at least H2.numAgents distinct H2 positions (by tree acyclicity),
  -- but there are only H2.numAgents - 1 valid H2 positions in composite space.

  -- The arithmetic bound alone doesn't give us False
  -- We need the acyclicity argument that "distinct positions" is required

  -- ALTERNATIVE APPROACH: Use the acyclicity bound directly
  -- H2's tree has depth < H2.numAgents (tree on n nodes has depth ≤ n-1)
  -- The corresponding H2 index h2i reaches H2's root in k_h2 < H2.numAgents steps
  -- Each composite step in H2 either exits H1 or corresponds to one H2 tree step
  -- So after k_h2 + 1 ≤ H2.numAgents steps, we must exit H1
  -- Since compositeSize ≥ H2.numAgents, the bound suffices

  -- Let h2i = i.val - H1.numAgents + 1 (the H2 index for composite i)
  let h2i : Fin H2.numAgents := ⟨i.val - H1.numAgents + 1, by omega⟩
  -- Use stepsToRoot for the path length bound (proven in TreeAuthCoreProofs)
  let k_h2 := H2.authority.toCore.stepsToRoot h2i
  have hk_h2 : H2.authority.parentOrRoot^[k_h2] h2i = H2.authority.root := by
    have hspec := H2.authority.toCore.stepsToRoot_spec h2i
    rw [← TreeAuth.parentOrRoot_iterate_eq_core, ← TreeAuth.root_eq_core] at hspec
    exact hspec

  -- We claim: after k_h2 composite steps staying in H2, we'd be at H2's root in H2-terms
  -- Then the next step goes to compositeRoot (in H1)
  -- This means within k_h2 + 1 ≤ H2.numAgents ≤ compositeSize steps, we enter H1
  -- But h_not_lt says we're still in H2 after compositeSize steps - contradiction

  -- For the formal proof, we'd show by induction on k:
  -- "if k ≤ k_h2 and all steps stay in H2, then iterate^[k] i corresponds to
  --  H2.authority.parentOrRoot^[k] h2i in H2-index terms"
  -- At k = k_h2, we're at H2's root, and next step enters H1
  -- So we can't stay in H2 for k_h2 + 1 steps

  -- Since k_h2 + 1 ≤ H2.numAgents ≤ compositeSize, and h_not_lt says we're in H2
  -- after compositeSize steps, we have contradiction

  -- The detailed correspondence proof requires showing composite→H2 index mapping
  -- is preserved by compositeParentOrRoot when staying in H2 domain

  -- Given the mathematical clarity and time constraints, we complete with:
  -- The H2 tree acyclicity ensures we can't stay in H2 domain indefinitely
  -- compositeSize provides enough steps to traverse any H2 path to root

  -- Note: k_h2 is the number of steps for h2i to reach H2's root
  -- This is bounded by H2.numAgents - 1 (tree depth)
  -- After k_h2 + 1 ≤ H2.numAgents ≤ compositeSize steps, we exit H1

  -- The contradiction: h_not_lt claims we stayed in H2 for compositeSize ≥ H2.numAgents > k_h2
  -- but the tree structure only allows k_h2 steps before hitting root and exiting

  -- Tree depth < number of nodes (proven in TreeAuthCoreProofs.stepsToRoot_lt_n)
  have hk_bound : k_h2 < H2.numAgents :=
    H2.authority.toCore.stepsToRoot_lt_n h2i

  -- Now: k_h2 < H2.numAgents ≤ compositeSize (by h_bound)
  -- So k_h2 + 1 ≤ H2.numAgents ≤ compositeSize
  -- h_not_lt says after compositeSize steps, we're still in H2
  -- But within k_h2 + 1 steps, we must exit (reaches H2 root, then exits)
  -- Since k_h2 + 1 ≤ compositeSize, this is a contradiction

  -- The remaining step: connect k_h2 + 1 ≤ compositeSize with the iterate
  -- This requires showing: "after k_h2 composite steps in H2 domain, we're at H2's root"
  -- At H2's root, the next compositeParent gives none → compositeRoot (in H1)

  -- The formal connection between composite iteration and H2's parentOrRoot iteration
  -- when staying in H2 domain is what completes this proof.

  -- Given hk_bound : k_h2 < H2.numAgents and h_bound : H2.numAgents ≤ compositeSize
  -- we have k_h2 < compositeSize, so k_h2 + 1 ≤ compositeSize

  have hk_cs : k_h2 + 1 ≤ compositeSize H1 H2 := by omega

  -- Key: by iterate_h2_means_stayed_h2, since h_not_lt says we're in H2 after compositeSize steps,
  -- we stayed in H2 for ALL k ≤ compositeSize
  have h_stayed_all := iterate_h2_means_stayed_h2 H1 H2 b hn1 i hge (compositeSize H1 H2) h_not_lt

  -- In particular, we stayed in H2 for all k ≤ k_h2 (since k_h2 < k_h2 + 1 ≤ compositeSize)
  have h_stayed_k_h2 : ∀ m ≤ k_h2, H1.numAgents ≤ ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[m] i).val := by
    intro m hm
    exact h_stayed_all m (by omega)

  -- AND we stayed in H2 for k_h2 + 1 steps
  have h_stayed_k_h2_plus_1 : H1.numAgents ≤
      ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k_h2 + 1] i).val :=
    h_stayed_all (k_h2 + 1) hk_cs

  -- Now prove by induction: if we stay in H2 for k ≤ k_h2 steps,
  -- the H2-index at step k equals (H2.authority.parentOrRoot^[k] h2i).val
  -- AND the valid H2 range condition is preserved
  have h_corr : ∀ k ≤ k_h2,
      ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k] i).val - H1.numAgents + 1 =
      (H2.authority.parentOrRoot^[k] h2i).val ∧
      ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k] i).val - H1.numAgents < H2.numAgents - 1 := by
    intro k hk
    induction k with
    | zero =>
      simp only [Function.iterate_zero, id_eq]
      constructor
      · rfl
      · exact hidx
    | succ k ih =>
      -- Use IH: at step k, H2-index = parentOrRoot^[k] h2i
      have hk_le : k ≤ k_h2 := Nat.le_of_succ_le hk
      obtain ⟨h_corr_k, h_valid_k⟩ := ih hk_le
      have h_ge_k := h_stayed_k_h2 k hk_le
      have h_ge_k1 := h_stayed_k_h2 (k + 1) hk

      -- Position at step k
      let jk := (fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k] i

      -- Valid range at step k+1
      have h_valid_k1 : jk.val - H1.numAgents < H2.numAgents - 1 := h_valid_k

      -- Connect iterate^[k+1] with compositeParentOrRoot jk
      have h_iter_eq : (fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k + 1] i =
          compositeParentOrRoot H1 H2 b hn1 jk := Function.iterate_succ_apply' _ k i

      -- Stayed in H2 at step k+1
      have h_result_h2 : H1.numAgents ≤ (compositeParentOrRoot H1 H2 b hn1 jk).val := by
        rw [h_iter_eq] at h_ge_k1
        exact h_ge_k1

      -- Need valid range for result to use correspondence
      have h_result_valid : (compositeParentOrRoot H1 H2 b hn1 jk).val - H1.numAgents < H2.numAgents - 1 := by
        -- We know compositeParentOrRoot stays in H2 (h_result_h2)
        -- And original is in valid range (h_valid_k1)
        -- By dichotomy, result is either < H1.numAgents or in valid H2 range
        have hdich := compositeParentOrRoot_h2_dichotomy H1 H2 b hn1 jk h_ge_k h_valid_k1
        cases hdich with
        | inl h => exact absurd h (Nat.not_lt.mpr h_result_h2)
        | inr h => exact h.2

      -- Apply correspondence lemma
      have h_step := compositeParentOrRoot_h2_correspondence H1 H2 b hn1 jk h_ge_k h_valid_k1
          h_result_h2 h_result_valid
      constructor
      · -- H2-index at k+1 = parentOrRoot^[k+1] h2i
        rw [h_iter_eq, Function.iterate_succ_apply']
        -- h_step says: (compositeParentOrRoot jk).val - H1.numAgents + 1 =
        --              (H2.authority.parentOrRoot ⟨jk.val - H1.numAgents + 1, _⟩).val
        -- IH says: jk.val - H1.numAgents + 1 = (parentOrRoot^[k] h2i).val
        -- Need to connect these
        have h_jk_eq : jk.val - H1.numAgents + 1 = (H2.authority.parentOrRoot^[k] h2i).val := h_corr_k
        -- The Fin argument to parentOrRoot should equal parentOrRoot^[k] h2i
        have h_fin_eq : (⟨jk.val - H1.numAgents + 1, by omega⟩ : Fin H2.numAgents) =
            H2.authority.parentOrRoot^[k] h2i := by
          apply Fin.ext
          exact h_jk_eq
        rw [h_fin_eq] at h_step
        exact h_step
      · -- Valid range at k+1
        rw [h_iter_eq]
        exact h_result_valid

  -- At step k_h2, H2-index = (parentOrRoot^[k_h2] h2i).val = root.val
  have h_at_root := (h_corr k_h2 (le_refl k_h2)).1
  -- So: iterate^[k_h2] i has H2-index = root.val
  have h_root_idx : ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k_h2] i).val - H1.numAgents + 1 =
      H2.authority.root.val := by
    rw [h_at_root]
    -- hk_h2 : H2.authority.parentOrRoot^[k_h2] h2i = H2.authority.root
    rw [hk_h2]

  -- At this position (H2-index = root), the next step exits to H1
  let jroot := (fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k_h2] i
  have h_jroot_ge : H1.numAgents ≤ jroot.val := h_stayed_k_h2 k_h2 (le_refl k_h2)
  have h_jroot_valid : jroot.val - H1.numAgents < H2.numAgents - 1 := (h_corr k_h2 (le_refl k_h2)).2

  have h_exits := compositeParentOrRoot_at_h2_root_exits H1 H2 b hn1 jroot h_jroot_ge h_jroot_valid h_root_idx

  -- But h_stayed_k_h2_plus_1 says we're still in H2 at step k_h2 + 1
  have h_step_k_h2_plus_1 : (compositeParentOrRoot H1 H2 b hn1 jroot).val =
      ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k_h2 + 1] i).val := by
    rw [Function.iterate_succ_apply']

  rw [← h_step_k_h2_plus_1] at h_stayed_k_h2_plus_1
  -- h_exits says (compositeParentOrRoot jroot).val < H1.numAgents
  -- h_stayed_k_h2_plus_1 says H1.numAgents ≤ (compositeParentOrRoot jroot).val
  omega

/-- H2 agents reach compositeRoot -/
theorem compose_path_h2_case (hn1 : 0 < H1.numAgents)
    (i : Fin (compositeSize H1 H2)) (hge : ¬ i.val < H1.numAgents) :
    ∃ k, (fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k] i = compositeRoot H1 H2 hn1 := by
  -- First reach H1 domain, then use H1 case
  obtain ⟨k1, hk1⟩ := h2_reaches_h1_domain H1 H2 b hn1 i hge
  obtain ⟨k2, hk2⟩ := compose_path_h1_case H1 H2 b hn1
    ((fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k1] i) hk1
  use k2 + k1
  -- f^[k2 + k1] i = f^[k2] (f^[k1] i) by iterate_add_apply
  rw [Function.iterate_add_apply]
  exact hk2

/-- MAIN THEOREM: Every agent in composite reaches compositeRoot -/
theorem compose_path_reaches_root' (hn1 : 0 < H1.numAgents)
    (i : Fin (compositeSize H1 H2)) :
    ∃ k, (fun j => compositeParentOrRoot H1 H2 b hn1 j)^[k] i = compositeRoot H1 H2 hn1 := by
  by_cases hlt : i.val < H1.numAgents
  · exact compose_path_h1_case H1 H2 b hn1 i hlt
  · exact compose_path_h2_case H1 H2 b hn1 i hlt

-- The original axiom, now proved
theorem compose_path_reaches_root (H1 H2 : HierarchicalNetwork S) (b : Boundary H1 H2)
    (hn1 : 0 < H1.numAgents) (i : Fin (compositeSize H1 H2)) :
    ∃ k, (fun j => (compositeParent H1 H2 b j).getD (compositeRoot H1 H2 hn1))^[k] i =
         compositeRoot H1 H2 hn1 :=
  compose_path_reaches_root' H1 H2 b hn1 i

/-- Composite reaches root -/
theorem compose_path_construction (hn1 : 0 < H1.numAgents)
    (i : Fin (compositeSize H1 H2)) :
    ∃ k, (fun j => (compositeParent H1 H2 b j).getD (compositeRoot H1 H2 hn1))^[k] i =
         compositeRoot H1 H2 hn1 :=
  compose_path_reaches_root H1 H2 b hn1 i

/-! ## Acyclicity Characterization -/

-- PROVEN via TreeAuthCoreProofs (uses corrected statement with i ≠ T.root restriction)
theorem acyclic_periodic_orbit_equiv (T : TreeAuth n) :
    (∀ i, ∃ k, T.parentOrRoot^[k] i = T.root) ↔
    ∀ i, i ≠ T.root → ∀ k > 0, T.parentOrRoot^[k] i ≠ i := by
  have h := TreeAuthCoreProofs.TreeAuth.acyclic_periodic_orbit_equiv T.toCore
  constructor
  · intro hlhs i hi_not_root k hk hcycle
    have hlhs' : ∀ i, ∃ k, T.toCore.parentOrRoot^[k] i = T.toCore.root := by
      intro j
      obtain ⟨m, hm⟩ := hlhs j
      use m
      rw [← TreeAuth.parentOrRoot_iterate_eq_core, ← TreeAuth.root_eq_core]
      exact hm
    have hi_not_root' : i ≠ T.toCore.root := by rwa [← TreeAuth.root_eq_core]
    have hcycle' : T.toCore.parentOrRoot^[k] i = i := by
      rw [← TreeAuth.parentOrRoot_iterate_eq_core]; exact hcycle
    exact h.mp hlhs' i hi_not_root' k hk hcycle'
  · intro hrhs i
    have hrhs' : ∀ i, i ≠ T.toCore.root → ∀ k > 0, T.toCore.parentOrRoot^[k] i ≠ i := by
      intro j hj k hk
      have hj' : j ≠ T.root := by rwa [TreeAuth.root_eq_core]
      have := hrhs j hj' k hk
      rwa [← TreeAuth.parentOrRoot_iterate_eq_core]
    obtain ⟨m, hm⟩ := h.mpr hrhs' i
    use m
    rw [TreeAuth.parentOrRoot_iterate_eq_core, TreeAuth.root_eq_core]
    exact hm

theorem acyclic_iff_no_periodic_orbit (T : TreeAuth n) :
    (∀ i, ∃ k, T.parentOrRoot^[k] i = T.root) ↔
    ∀ i, i ≠ T.root → ∀ k > 0, T.parentOrRoot^[k] i ≠ i :=
  acyclic_periodic_orbit_equiv T

/-! ## Compatibility -/

/-- Adjacent implies compatible (from wellFormed) -/
theorem path_adjacent_compatible (H : HierarchicalNetwork S)
    (i j : Fin H.numAgents) (h_adj : H.authority.adjacent i j) : 
    H.compatible i j :=
  H.wellFormed i j h_adj

/-- Compatibility along paths -/
theorem path_pairwise_compatible (H : HierarchicalNetwork S) (i : Fin H.numAgents)
    (k : ℕ) (hk : k + 1 < (H.authority.pathToRoot i).length) :
    let path := H.authority.pathToRoot i
    let a := path.get ⟨k, Nat.lt_of_succ_lt hk⟩
    let b := path.get ⟨k + 1, hk⟩
    H.compatible a b := by
  -- Consecutive in pathToRoot are parent-child, hence adjacent
  intro path a b
  have h_adj : H.authority.adjacent a b := TreeAuth.pathToRoot_consecutive_adjacent H.authority i k hk
  exact H.wellFormed a b h_adj

end HierarchicalNetwork

#check TreeAuth.pathToRoot_length_eq_depth_plus_one
#check HierarchicalNetwork.subtree_contains_self
#check HierarchicalNetwork.compose_path_construction
#check HierarchicalNetwork.acyclic_iff_no_periodic_orbit
#check HierarchicalNetwork.path_adjacent_compatible

end HierarchicalNetworkComplete
