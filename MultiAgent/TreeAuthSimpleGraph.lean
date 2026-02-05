/-
# TreeAuth to SimpleGraph Bridge

Converts a TreeAuth rooted tree structure to a SimpleGraph and proves
the resulting undirected graph is acyclic (IsAcyclic).

## Main Results

1. `treeAuthGraph` - SimpleGraph from TreeAuth
2. `treeAuthGraph_acyclic` - The graph is acyclic
3. `treeAuthGraph_connected` - The graph is connected (n > 0)
4. `treeAuthGraph_isTree` - Combined: it's a tree

## Proof Strategy

Acyclicity via depth function:
- Each vertex has unique depth (distance from root)
- Adjacent vertices have depth differing by exactly 1
- A cycle would require returning to start depth
- But ±1 steps that sum to 0 require equal ups/downs
- This forces edge repetition, contradicting simple cycle

Targets: Mathlib 4.27.0 / Lean 4.27.0

SORRIES: 0
AXIOMS: 0 (depth_parent_fuel_analysis is now a theorem)

Author: Tenured Cohomology Foundations
Date: January 2026
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Infrastructure.TreeAuthCoreProofs
import Infrastructure.ExtendedGraphInfra

namespace TreeAuthSimpleGraph

/-! ## Section 1: TreeAuth Structure -/

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

theorem parent_ne (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) : p ≠ i := by
  intro h; subst p; exact T.parent_ne_self i hp

def adjacent (T : TreeAuth n) (i j : Fin n) : Prop :=
  T.parent i = some j ∨ T.parent j = some i

theorem adjacent_symm (T : TreeAuth n) {i j : Fin n} : T.adjacent i j ↔ T.adjacent j i := by
  simp [adjacent, or_comm]

theorem adjacent_ne (T : TreeAuth n) {i j : Fin n} (h : T.adjacent i j) : i ≠ j := by
  intro heq; subst heq
  cases h with
  | inl h => exact T.parent_ne_self i h
  | inr h => exact T.parent_ne_self i h

/-! ## Section 2: Depth Function -/

/-- Depth with fuel-based recursion -/
def depthAux (T : TreeAuth n) (i : Fin n) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 => match T.parent i with
    | none => 0
    | some p => 1 + T.depthAux p fuel

def depth (T : TreeAuth n) (i : Fin n) : ℕ := T.depthAux i n

theorem depth_root (T : TreeAuth n) : T.depth T.root = 0 := by
  simp only [depth]
  cases n with
  | zero => exact Fin.elim0 T.root
  | succ k => simp [depthAux, T.root_no_parent]

/-- stepsToRoot: minimum iterations to reach root -/
noncomputable def stepsToRoot (T : TreeAuth n) (i : Fin n) : ℕ := Nat.find (T.acyclic i)

lemma stepsToRoot_spec (T : TreeAuth n) (i : Fin n) :
    T.parentOrRoot^[T.stepsToRoot i] i = T.root := Nat.find_spec (T.acyclic i)

lemma stepsToRoot_min (T : TreeAuth n) (i : Fin n) (k : ℕ)
    (hk : T.parentOrRoot^[k] i = T.root) : T.stepsToRoot i ≤ k := Nat.find_le hk

lemma stepsToRoot_root (T : TreeAuth n) : T.stepsToRoot T.root = 0 := by
  have h : T.parentOrRoot^[0] T.root = T.root := rfl
  exact Nat.eq_zero_of_le_zero (T.stepsToRoot_min T.root 0 h)

lemma stepsToRoot_pos_of_ne_root (T : TreeAuth n) {i : Fin n} (hi : i ≠ T.root) :
    T.stepsToRoot i > 0 := by
  by_contra h; push_neg at h
  have hs : T.stepsToRoot i = 0 := Nat.eq_zero_of_le_zero h
  have := T.stepsToRoot_spec i
  rw [hs, Function.iterate_zero, id_eq] at this
  exact hi this

lemma parentOrRoot_of_parent (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) :
    T.parentOrRoot i = p := by simp only [parentOrRoot, hp, Option.getD_some]

lemma ne_root_of_parent_some (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) :
    i ≠ T.root := by intro heq; rw [heq, T.root_no_parent] at hp; cases hp

lemma stepsToRoot_parent (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) :
    T.stepsToRoot i = T.stepsToRoot p + 1 := by
  have hi_ne_root := T.ne_root_of_parent_some hp
  have h_pos := T.stepsToRoot_pos_of_ne_root hi_ne_root
  have hp_reaches : T.parentOrRoot^[T.stepsToRoot i - 1] p = T.root := by
    have hspec := T.stepsToRoot_spec i
    have hstep : T.parentOrRoot^[T.stepsToRoot i] i =
        T.parentOrRoot^[T.stepsToRoot i - 1] (T.parentOrRoot i) := by
      conv_lhs => rw [show T.stepsToRoot i = T.stepsToRoot i - 1 + 1 by omega]
      rw [Function.iterate_add_apply, Function.iterate_one]
    rw [hstep, T.parentOrRoot_of_parent hp] at hspec
    exact hspec
  have hle : T.stepsToRoot p ≤ T.stepsToRoot i - 1 := T.stepsToRoot_min p _ hp_reaches
  have hge : T.stepsToRoot p ≥ T.stepsToRoot i - 1 := by
    by_contra h; push_neg at h
    have hp_spec := T.stepsToRoot_spec p
    have hreach : T.parentOrRoot^[T.stepsToRoot p + 1] i = T.root := by
      have hstep : T.parentOrRoot^[T.stepsToRoot p + 1] i =
          T.parentOrRoot^[T.stepsToRoot p] (T.parentOrRoot i) := by
        rw [Function.iterate_add_apply, Function.iterate_one]
      rw [hstep, T.parentOrRoot_of_parent hp]
      exact hp_spec
    have hmin := T.stepsToRoot_min i _ hreach
    omega
  omega

lemma iterate_comm {α : Type*} (f : α → α) (m k : ℕ) (x : α) :
    f^[m] (f^[k] x) = f^[k] (f^[m] x) := by
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]

lemma stepsToRoot_lt_n (T : TreeAuth n) (i : Fin n) : T.stepsToRoot i < n := by
  by_contra h; push_neg at h
  have hn_pos : 0 < n := Fin.pos i
  have h_distinct : ∀ a b, a < T.stepsToRoot i → b < T.stepsToRoot i → a < b →
      T.parentOrRoot^[a] i ≠ T.parentOrRoot^[b] i := by
    intro a b ha hb hab heq
    have hcyc : T.parentOrRoot^[b - a] (T.parentOrRoot^[a] i) = T.parentOrRoot^[a] i := by
      calc T.parentOrRoot^[b - a] (T.parentOrRoot^[a] i)
          = T.parentOrRoot^[b - a + a] i := by rw [Function.iterate_add_apply]
        _ = T.parentOrRoot^[b] i := by rw [Nat.sub_add_cancel (le_of_lt hab)]
        _ = T.parentOrRoot^[a] i := heq.symm
    have hrea : T.parentOrRoot^[T.stepsToRoot i - a] (T.parentOrRoot^[a] i) = T.root := by
      have hspec := T.stepsToRoot_spec i
      have heq' : T.stepsToRoot i = T.stepsToRoot i - a + a := (Nat.sub_add_cancel (le_of_lt ha)).symm
      rw [heq', Function.iterate_add_apply] at hspec
      exact hspec
    let m := b - a
    have hm_pos : m > 0 := by simp only [m]; omega
    have iter_cyc : ∀ t, T.parentOrRoot^[m * t] (T.parentOrRoot^[a] i) = T.parentOrRoot^[a] i := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        have hmul : m * (t + 1) = m + m * t := by ring
        calc T.parentOrRoot^[m * (t + 1)] (T.parentOrRoot^[a] i)
            = T.parentOrRoot^[m + m * t] (T.parentOrRoot^[a] i) := by rw [hmul]
          _ = T.parentOrRoot^[m] (T.parentOrRoot^[m * t] (T.parentOrRoot^[a] i)) := by
              rw [Function.iterate_add_apply]
          _ = T.parentOrRoot^[m] (T.parentOrRoot^[a] i) := by rw [ih]
          _ = T.parentOrRoot^[a] i := hcyc
    have hne_root : T.parentOrRoot^[a] i ≠ T.root := fun heq_root =>
      Nat.not_lt.mpr (T.stepsToRoot_min i a heq_root) ha
    by_cases hsmod : (T.stepsToRoot i - a) % m = 0
    · have hs_eq : T.stepsToRoot i - a = m * ((T.stepsToRoot i - a) / m) := by
        have := Nat.div_add_mod (T.stepsToRoot i - a) m; omega
      have hrea' : T.parentOrRoot^[m * ((T.stepsToRoot i - a) / m)] (T.parentOrRoot^[a] i) = T.root := by
        rw [← hs_eq]; exact hrea
      rw [iter_cyc] at hrea'
      exact hne_root hrea'
    · have hdiv : T.stepsToRoot i - a = (T.stepsToRoot i - a) % m + m * ((T.stepsToRoot i - a) / m) := by
        have := Nat.div_add_mod (T.stepsToRoot i - a) m; omega
      have hrea' : T.parentOrRoot^[(T.stepsToRoot i - a) % m] (T.parentOrRoot^[a] i) = T.root := by
        have key : T.parentOrRoot^[T.stepsToRoot i - a] (T.parentOrRoot^[a] i) = T.root := hrea
        rw [hdiv, Function.iterate_add_apply] at key
        simp only [iter_cyc] at key
        exact key
      have hreach : T.parentOrRoot^[a + (T.stepsToRoot i - a) % m] i = T.root := by
        rw [Function.iterate_add_apply, iterate_comm]
        exact hrea'
      have hmin := T.stepsToRoot_min i _ hreach
      have hmod_lt : (T.stepsToRoot i - a) % m < m := Nat.mod_lt _ hm_pos
      have hmod_lt_s : (T.stepsToRoot i - a) % m < T.stepsToRoot i - a := by
        have : m ≤ T.stepsToRoot i - a := by simp only [m]; omega
        omega
      omega
  have h_root_distinct : ∀ k, k < T.stepsToRoot i → T.parentOrRoot^[k] i ≠ T.root := by
    intro k hk heq_root
    exact Nat.not_lt.mpr (T.stepsToRoot_min i k heq_root) hk
  have h_past_root : ∀ k, k ≥ T.stepsToRoot i → T.parentOrRoot^[k] i = T.root := by
    intro k hk
    obtain ⟨d, hd⟩ : ∃ d, k = T.stepsToRoot i + d := ⟨k - T.stepsToRoot i, by omega⟩
    rw [hd, Function.iterate_add_apply, iterate_comm, T.stepsToRoot_spec]
    clear hk hd h_root_distinct h_distinct hn_pos h
    induction d with
    | zero => rfl
    | succ d ih => rw [Function.iterate_succ_apply', ih, T.parentOrRoot_root]
  let f : Fin (n + 1) → Fin n := fun k => T.parentOrRoot^[k.val] i
  have hinj : Function.Injective f := by
    intro a b heq
    simp only [f] at heq
    rcases Nat.lt_trichotomy a.val b.val with hlt | heq' | hgt
    · exfalso
      by_cases hb : b.val < T.stepsToRoot i
      · exact h_distinct a.val b.val (by omega) hb hlt heq
      · rw [h_past_root b.val (by omega)] at heq
        exact h_root_distinct a.val (by omega) heq
    · exact Fin.ext heq'
    · exfalso
      by_cases ha : a.val < T.stepsToRoot i
      · exact h_distinct b.val a.val (by omega) ha hgt heq.symm
      · rw [h_past_root a.val (by omega)] at heq
        exact h_root_distinct b.val (by omega) heq.symm
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  omega

lemma depthAux_eq_stepsToRoot (T : TreeAuth n) (i : Fin n) (fuel : ℕ)
    (hfuel : fuel ≥ T.stepsToRoot i) : T.depthAux i fuel = T.stepsToRoot i := by
  induction fuel generalizing i with
  | zero =>
    have hzero : T.stepsToRoot i = 0 := Nat.eq_zero_of_le_zero hfuel
    have hi_root : i = T.root := by
      have := T.stepsToRoot_spec i
      rw [hzero, Function.iterate_zero, id_eq] at this
      exact this
    subst hi_root
    simp only [T.stepsToRoot_root, depthAux]
  | succ f ih =>
    cases hs : T.stepsToRoot i with
    | zero =>
      have hi_root : i = T.root := by
        have := T.stepsToRoot_spec i
        rw [hs, Function.iterate_zero, id_eq] at this
        exact this
      subst hi_root
      simp only [depthAux, T.root_no_parent]
    | succ s =>
      have hi_ne_root : i ≠ T.root := by intro heq; rw [heq, T.stepsToRoot_root] at hs; cases hs
      have hpar_some := T.nonroot_has_parent i hi_ne_root
      rw [Option.isSome_iff_exists] at hpar_some
      obtain ⟨p, hp⟩ := hpar_some
      have hsteps_p : T.stepsToRoot p = s := by have := T.stepsToRoot_parent hp; omega
      simp only [depthAux, hp]
      rw [ih p (by omega)]
      omega

lemma depth_eq_stepsToRoot (T : TreeAuth n) (i : Fin n) : T.depth i = T.stepsToRoot i := by
  simp only [depth]
  exact T.depthAux_eq_stepsToRoot i n (le_of_lt (T.stepsToRoot_lt_n i))

/-- PROVEN: depth of child = depth of parent + 1 -/
theorem depth_parent_fuel_analysis (T : TreeAuth n) {i p : Fin n}
    (hp : T.parent i = some p) : T.depth i = T.depth p + 1 := by
  rw [T.depth_eq_stepsToRoot i, T.depth_eq_stepsToRoot p, T.stepsToRoot_parent hp]

/-- Parent has depth one less -/
theorem depth_parent (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) :
    T.depth i = T.depth p + 1 :=
  depth_parent_fuel_analysis T hp

/-- Adjacent vertices have depth differing by 1 -/
theorem adjacent_depth (T : TreeAuth n) {i j : Fin n} (h : T.adjacent i j) :
    T.depth i = T.depth j + 1 ∨ T.depth j = T.depth i + 1 := by
  cases h with
  | inl hp => left; exact depth_parent T hp
  | inr hp => right; exact depth_parent T hp

/-! ## Section 3: SimpleGraph Construction -/

/-- The undirected graph from TreeAuth -/
def toSimpleGraph (T : TreeAuth n) : SimpleGraph (Fin n) where
  Adj i j := T.adjacent i j
  symm := fun _ _ h => T.adjacent_symm.mp h
  loopless := fun i h => T.adjacent_ne h rfl

/-- Adjacency matches -/
theorem toSimpleGraph_adj (T : TreeAuth n) (i j : Fin n) :
    (T.toSimpleGraph).Adj i j ↔ T.adjacent i j := Iff.rfl

/-! ## Section 4: Path to Root -/

def pathToRootAux (T : TreeAuth n) (i : Fin n) : ℕ → List (Fin n)
  | 0 => [i]
  | fuel + 1 => match T.parent i with
    | none => [i]
    | some p => i :: T.pathToRootAux p fuel

def pathToRoot (T : TreeAuth n) (i : Fin n) : List (Fin n) := T.pathToRootAux i n

theorem pathToRoot_nonempty (T : TreeAuth n) (i : Fin n) : T.pathToRoot i ≠ [] := by
  simp only [pathToRoot]
  cases n with
  | zero => exact Fin.elim0 i
  | succ k => simp [pathToRootAux]; split <;> simp

theorem pathToRoot_head (T : TreeAuth n) (i : Fin n) : (T.pathToRoot i).head? = some i := by
  simp only [pathToRoot]
  cases n with
  | zero => exact Fin.elim0 i
  | succ k => simp [pathToRootAux]; split <;> rfl

theorem pathToRoot_last (T : TreeAuth n) (i : Fin n) (hn : 0 < n) :
    (T.pathToRoot i).getLast? = some T.root := by
  -- Key insight: pathToRootAux builds list following parent links
  -- With n fuel, acyclicity ensures we reach root (stepsToRoot < n)
  simp only [pathToRoot]
  suffices h : ∀ (j : Fin n) (fuel : ℕ),
      (∃ m ≤ fuel, T.parentOrRoot^[m] j = T.root) →
      (T.pathToRootAux j fuel).getLast? = some T.root by
    apply h i n
    use T.stepsToRoot i
    exact ⟨le_of_lt (T.stepsToRoot_lt_n i), T.stepsToRoot_spec i⟩
  -- Now prove the sufficiency condition
  intro j fuel ⟨m, hm_le, hm_eq⟩
  induction fuel generalizing j m with
  | zero =>
    simp only [Nat.le_zero] at hm_le
    subst hm_le
    simp only [Function.iterate_zero, id_eq] at hm_eq
    simp only [pathToRootAux, List.getLast?_singleton, hm_eq]
  | succ fuel' ih =>
    cases hp : T.parent j with
    | none =>
      -- j has no parent, so j = root
      simp only [pathToRootAux, hp, List.getLast?_singleton]
      have hj_root : j = T.root := by
        by_contra h
        have := T.nonroot_has_parent j h
        simp [hp] at this
      exact congrArg some hj_root
    | some p =>
      -- j has parent p, recurse
      simp only [pathToRootAux, hp]
      -- (j :: pathToRootAux p fuel').getLast? = (pathToRootAux p fuel').getLast?
      -- pathToRootAux always returns nonempty list starting with the input
      have hpath_eq : ∃ rest, T.pathToRootAux p fuel' = p :: rest := by
        cases fuel' with
        | zero => exact ⟨[], rfl⟩
        | succ f =>
          simp only [pathToRootAux]
          cases T.parent p with
          | none => exact ⟨[], rfl⟩
          | some q => exact ⟨T.pathToRootAux q f, rfl⟩
      obtain ⟨rest, hrest⟩ := hpath_eq
      rw [hrest, List.getLast?_cons_cons]
      cases m with
      | zero =>
        simp only [Function.iterate_zero, id_eq] at hm_eq
        subst hm_eq
        -- root has no parent, contradiction
        rw [T.root_no_parent] at hp
        cases hp
      | succ m' =>
        have hm'_le : m' ≤ fuel' := by omega
        have hm'_eq : T.parentOrRoot^[m'] p = T.root := by
          have hstep : T.parentOrRoot^[m' + 1] j = T.parentOrRoot^[m'] (T.parentOrRoot j) := by
            rw [Function.iterate_succ_apply]
          have hpor : T.parentOrRoot j = p := by simp [parentOrRoot, hp]
          rw [hstep, hpor] at hm_eq
          exact hm_eq
        have := ih p m' hm'_le hm'_eq
        rw [hrest] at this
        exact this

/-! ## Section 5: Reachability -/

/-- Every vertex is reachable from root -/
theorem reachable_from_root (T : TreeAuth n) (i : Fin n) :
    T.toSimpleGraph.Reachable T.root i := by
  -- Path from root to i exists via parent links
  obtain ⟨k, hk⟩ := T.acyclic i
  -- Build walk by following parentOrRoot backwards
  induction k generalizing i with
  | zero =>
    simp only [Function.iterate_zero, id_eq] at hk
    rw [hk]
  | succ k ih =>
    cases hp : T.parent i with
    | none =>
      -- i is root
      have hi_root : i = T.root := by
        by_contra h
        have := T.nonroot_has_parent i h
        simp [hp] at this
      rw [hi_root]
    | some p =>
      -- i has parent p, reach p then step to i
      have h_iter : (fun j => (T.parent j).getD T.root)^[k] p = T.root := by
        have hstep : (fun j => (T.parent j).getD T.root)^[k + 1] i =
            (fun j => (T.parent j).getD T.root)^[k] ((T.parent i).getD T.root) := by
          rw [Function.iterate_succ_apply]
        simp only [hp, Option.getD_some] at hstep
        rw [hstep] at hk
        exact hk
      have h_reach_p := ih p h_iter
      have h_adj : T.toSimpleGraph.Adj p i := by
        simp only [toSimpleGraph_adj, adjacent]
        right; exact hp
      exact h_reach_p.trans (SimpleGraph.Adj.reachable h_adj)

/-- Graph is connected when n > 0 -/
theorem toSimpleGraph_connected (T : TreeAuth n) (hn : 0 < n) : T.toSimpleGraph.Connected := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact SimpleGraph.Connected.mk (fun i j => (reachable_from_root T i).symm.trans (reachable_from_root T j))

/-! ## Section 6: Acyclicity -/

/-! ### Type Bridge to TreeAuthCoreProofs

TreeAuthSimpleGraph.TreeAuth and TreeAuthCoreProofs.TreeAuth have identical
structure definitions. We provide conversion to use the proven acyclicity theorem.
-/

/-- Convert TreeAuthSimpleGraph.TreeAuth to TreeAuthCoreProofs.TreeAuth -/
private def toProofTreeAuth (T : TreeAuth n) : TreeAuthCoreProofs.TreeAuth n where
  root := T.root
  parent := T.parent
  root_no_parent := T.root_no_parent
  nonroot_has_parent := T.nonroot_has_parent
  acyclic := T.acyclic
  parent_ne_self := T.parent_ne_self

/-- The SimpleGraphs from both TreeAuth types have the same adjacency relation -/
private lemma toSimpleGraph_adj_iff' (T : TreeAuth n) (i j : Fin n) :
    T.toSimpleGraph.Adj i j ↔ (toProofTreeAuth T).toSimpleGraph.Adj i j := by
  simp only [toSimpleGraph_adj, TreeAuthCoreProofs.TreeAuth.toSimpleGraph]
  rfl

/-- The SimpleGraphs are equal -/
private lemma toSimpleGraph_eq (T : TreeAuth n) :
    T.toSimpleGraph = (toProofTreeAuth T).toSimpleGraph := by
  ext i j
  exact toSimpleGraph_adj_iff' T i j

-- T02 ELIMINATED: Proven via type bridge to TreeAuthCoreProofs
-- The proof TreeAuth has the same graph (definitionally equal adjacency)
theorem toSimpleGraph_acyclic_aux (T : TreeAuth n) (v : Fin n)
    (p : T.toSimpleGraph.Walk v v) (hp : p.IsCycle) : False := by
  -- Show graphs are equal
  have h_eq : T.toSimpleGraph = (toProofTreeAuth T).toSimpleGraph := toSimpleGraph_eq T
  -- Use Eq.rec to transport everything at once
  exact Eq.rec (motive := fun G _ => ∀ (q : G.Walk v v), q.IsCycle → False)
    (fun q hq => TreeAuthCoreProofs.TreeAuth.toSimpleGraph_acyclic_aux (toProofTreeAuth T) v q hq)
    h_eq.symm p hp

/-- Key lemma: No cycle exists in the tree graph.

Proof by depth analysis:
- Each edge changes depth by ±1
- A cycle returns to start, so Σ(depth changes) = 0
- This requires equal up and down steps
- Each edge appears once in cycle (simple)
- But up/down on same edge = 2 traversals
- Contradiction with simple cycle
-/
theorem toSimpleGraph_acyclic (T : TreeAuth n) : T.toSimpleGraph.IsAcyclic := by
  intro v p hp
  exact toSimpleGraph_acyclic_aux T v p hp

/-- The graph is a tree -/
theorem toSimpleGraph_isTree (T : TreeAuth n) (hn : 0 < n) : T.toSimpleGraph.IsTree :=
  ⟨toSimpleGraph_connected T hn, toSimpleGraph_acyclic T⟩

open ExtendedGraphInfra

/-- Deep theorem: a TreeAuth graph has |E| + 1 = |V|. -/
theorem toSimpleGraph_edgeCount (T : TreeAuth n) (hn : 0 < n) :
    edgeCount T.toSimpleGraph + 1 = vertexCount (V := Fin n) := by
  classical
  have htree : T.toSimpleGraph.IsTree := toSimpleGraph_isTree T hn
  simpa using (tree_edgeCount (G := T.toSimpleGraph) htree)

/-- Euler characteristic for TreeAuth graphs: |E| + 1 = |V| (components = 1). -/
theorem toSimpleGraph_euler (T : TreeAuth n) (hn : 0 < n) :
    edgeCount T.toSimpleGraph + componentCount T.toSimpleGraph = vertexCount (V := Fin n) := by
  classical
  have htree : T.toSimpleGraph.IsTree := toSimpleGraph_isTree T hn
  simpa using (tree_euler (G := T.toSimpleGraph) htree)

end TreeAuth

/-! ## Section 7: Summary -/

#check TreeAuth.toSimpleGraph
#check TreeAuth.toSimpleGraph_adj
#check TreeAuth.reachable_from_root
#check TreeAuth.toSimpleGraph_connected
#check TreeAuth.toSimpleGraph_acyclic
#check TreeAuth.toSimpleGraph_isTree

end TreeAuthSimpleGraph
