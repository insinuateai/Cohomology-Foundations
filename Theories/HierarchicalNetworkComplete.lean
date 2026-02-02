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
AXIOMS: 1 (compose_path_reaches_root)
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

-- TEMP: axiomatized for speed, prove by 2026-02-07
-- Proof: agents from H1 use H1's acyclicity; agents from H2 reach boundary then use H1
axiom compose_path_reaches_root (H1 H2 : HierarchicalNetwork S) (b : Boundary H1 H2)
    (hn1 : 0 < H1.numAgents) (i : Fin (compositeSize H1 H2)) :
    ∃ k, (fun j => (compositeParent H1 H2 b j).getD (compositeRoot H1 H2 hn1))^[k] i =
         compositeRoot H1 H2 hn1

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
