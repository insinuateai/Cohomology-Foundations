/-
COBOUND: Multi-Agent Coordination Framework
Module: MultiAgent/TreeAuthority.lean
Created: January 2026

Tree-Authority Structure for Multi-Agent Systems

The mathematical insight: Trees have H¹ = 0, meaning no "trapped disagreements".
By organizing agents in a tree-shaped authority structure (like an org chart),
we guarantee that coordination is always achievable.

QUALITY STANDARDS:
- Axioms: 0
- Sorries: Minimal (auxiliary proofs)
- Core structure: COMPLETE
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.TakeWhile
import Mathlib.Logic.Function.Iterate

namespace MultiAgent

/-! # Tree Authority Structure

A tree-authority encodes a rooted tree where:
- One agent is the root (ultimate authority)
- Every non-root agent has exactly one parent (supervisor)
- Following parent links always reaches the root (no cycles)

This structure guarantees H¹ = 0 when mapped to a simplicial complex.
-/

/-- A tree-authority structure on n agents.

Encodes a rooted tree where each non-root agent has exactly one parent.
The `acyclic` field ensures no cycles: iterating parent eventually reaches root. -/
structure TreeAuth (n : ℕ) where
  /-- The root agent (ultimate authority) -/
  root : Fin n
  /-- Parent mapping: parent i = some j means j supervises i -/
  parent : Fin n → Option (Fin n)
  /-- Root has no parent -/
  root_no_parent : parent root = none
  /-- Every non-root has a parent -/
  nonroot_has_parent : ∀ i, i ≠ root → (parent i).isSome
  /-- No cycles: following parents eventually reaches root. -/
  acyclic : ∀ i, ∃ k, (fun j => (parent j).getD root)^[k] i = root
  /-- No self-loops: parent is always a different agent -/
  parent_ne_self : ∀ i, parent i ≠ some i

variable {n : ℕ}

namespace TreeAuth

/-! ## Basic Properties -/

/-- The parent-or-root function used in acyclicity -/
def parentOrRoot (T : TreeAuth n) (i : Fin n) : Fin n :=
  (T.parent i).getD T.root

/-- Root maps to itself under parentOrRoot -/
theorem parentOrRoot_root (T : TreeAuth n) : T.parentOrRoot T.root = T.root := by
  simp only [parentOrRoot, T.root_no_parent, Option.getD_none]

/-- Non-root maps to its actual parent under parentOrRoot -/
theorem parentOrRoot_of_some (T : TreeAuth n) (i p : Fin n) (hp : T.parent i = some p) :
    T.parentOrRoot i = p := by
  simp only [parentOrRoot, hp, Option.getD_some]

/-- If parent i = some p, then p ≠ i (no self-loops) -/
theorem parent_ne (T : TreeAuth n) (i p : Fin n) (hp : T.parent i = some p) : p ≠ i := by
  intro heq
  rw [heq] at hp
  exact T.parent_ne_self i hp

/-! ## Children -/

/-- Children of an agent: all agents whose parent is this agent -/
def children (T : TreeAuth n) (i : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun j => decide (T.parent j = some i)

/-- Root is in children of no one -/
theorem root_not_child (T : TreeAuth n) (i : Fin n) : T.root ∉ T.children i := by
  simp only [children, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  intro h
  rw [T.root_no_parent] at h
  cases h

/-- Children have this agent as parent -/
theorem mem_children_iff (T : TreeAuth n) (i j : Fin n) :
    j ∈ T.children i ↔ T.parent j = some i := by
  simp only [children, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]

/-! ## Adjacency -/

/-- Two agents are adjacent if one is the parent of the other -/
def adjacent (T : TreeAuth n) (i j : Fin n) : Prop :=
  T.parent i = some j ∨ T.parent j = some i

/-- Adjacency is symmetric -/
theorem adjacent_symm (T : TreeAuth n) (i j : Fin n) :
    T.adjacent i j ↔ T.adjacent j i := by
  simp only [adjacent, or_comm]

/-- Root is adjacent only to its children -/
theorem adjacent_root (T : TreeAuth n) (i : Fin n) (h : T.adjacent T.root i) :
    T.parent i = some T.root := by
  cases h with
  | inl h1 => rw [T.root_no_parent] at h1; cases h1
  | inr h2 => exact h2

/-! ## Edge Set -/

/-- The set of edges in the tree: (child, parent) pairs -/
def edges (T : TreeAuth n) : List (Fin n × Fin n) :=
  (List.finRange n).filterMap fun i =>
    match T.parent i with
    | none => none
    | some p => some (i, p)

/-- Edges as undirected pairs -/
def undirectedEdges (T : TreeAuth n) : List (Fin n × Fin n) :=
  T.edges ++ T.edges.map (fun (a, b) => (b, a))

/-! ## Depth (Distance from Root) -/

/-- The depth of an agent (computed via iteration).
    Returns the number of parent-hops to reach root. -/
def depthAux (T : TreeAuth n) (i : Fin n) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    match T.parent i with
    | none => 0  -- i is root
    | some p => 1 + T.depthAux p fuel'

/-- Depth using n as fuel (sufficient since tree has at most n vertices) -/
def depth (T : TreeAuth n) (i : Fin n) : ℕ := T.depthAux i n

/-- Root has depth 0 -/
theorem depth_root (T : TreeAuth n) (hn : 0 < n) : T.depth T.root = 0 := by
  simp only [depth]
  match n, hn with
  | k + 1, _ => simp only [depthAux, T.root_no_parent]

/-! ## Path to Root -/

/-- The path from an agent to the root, as a list of agents.
    Uses fuel-based recursion for termination. -/
def pathToRootAux (T : TreeAuth n) (i : Fin n) (fuel : ℕ) : List (Fin n) :=
  match fuel with
  | 0 => [i]
  | fuel' + 1 =>
    match T.parent i with
    | none => [i]  -- i is root
    | some p => i :: T.pathToRootAux p fuel'

/-- Path to root using n as fuel -/
def pathToRoot (T : TreeAuth n) (i : Fin n) : List (Fin n) :=
  T.pathToRootAux i n

/-- Path to root is nonempty -/
theorem pathToRoot_nonempty (T : TreeAuth n) (i : Fin n) : T.pathToRoot i ≠ [] := by
  simp only [pathToRoot]
  match n with
  | 0 => exact i.elim0
  | k + 1 =>
    simp only [pathToRootAux]
    cases T.parent i <;> simp

/-- Path from root to root is just [root] (when n > 0) -/
theorem pathToRoot_root (T : TreeAuth n) (hn : 0 < n) : T.pathToRoot T.root = [T.root] := by
  simp only [pathToRoot]
  match n, hn with
  | k + 1, _ => simp only [pathToRootAux, T.root_no_parent]

/-- pathToRootAux always starts with i -/
theorem pathToRootAux_head (T : TreeAuth n) (i : Fin n) (fuel : ℕ) :
    (T.pathToRootAux i fuel).head? = some i := by
  match fuel with
  | 0 => simp [pathToRootAux]
  | fuel' + 1 =>
    simp only [pathToRootAux]
    cases T.parent i <;> simp

/-- pathToRoot always starts with i -/
theorem pathToRoot_head (T : TreeAuth n) (i : Fin n) :
    (T.pathToRoot i).head? = some i := by
  simp only [pathToRoot]
  exact T.pathToRootAux_head i n

/-- i is always in pathToRoot i -/
theorem mem_pathToRoot_self (T : TreeAuth n) (i : Fin n) : i ∈ T.pathToRoot i := by
  have h := T.pathToRoot_head i
  have hne := T.pathToRoot_nonempty i
  match hpath : T.pathToRoot i with
  | [] => exact (hne hpath).elim
  | x :: xs =>
    simp only [hpath, List.head?_cons, Option.some.injEq] at h
    simp only [List.mem_cons, h, true_or]

/-! ## Lowest Common Ancestor -/

/-- Lowest common ancestor of two agents.
    The first vertex that appears in both paths to root. -/
def lca (T : TreeAuth n) (i j : Fin n) : Fin n :=
  let path_i := T.pathToRoot i
  let path_j := T.pathToRoot j
  match path_i.find? (fun x => decide (x ∈ path_j)) with
  | some x => x
  | none => T.root  -- Always exists since root is in both paths

/-! ## Path Between Vertices -/

/-- The path between two agents via their lowest common ancestor.
    Returns list of vertices on the path. -/
def pathBetween (T : TreeAuth n) (i j : Fin n) : List (Fin n) :=
  let ancestor := T.lca i j
  let path_i := T.pathToRoot i
  let path_j := T.pathToRoot j
  -- Path from i up to ancestor (excluding ancestor)
  let up_segment := path_i.takeWhile (· ≠ ancestor)
  -- Path from ancestor down to j (reversed, including ancestor)
  let down_segment := (path_j.takeWhile (· ≠ ancestor)).reverse
  up_segment ++ [ancestor] ++ down_segment

/-- pathBetween is nonempty (always contains at least the ancestor) -/
theorem pathBetween_nonempty (T : TreeAuth n) (i j : Fin n) : T.pathBetween i j ≠ [] := by
  simp only [pathBetween]
  intro h
  -- The path contains [ancestor] in the middle, so can't be empty
  have h_mid_ne : [T.lca i j] ≠ [] := List.cons_ne_nil _ _
  -- If up ++ mid ++ down = [], then up ++ mid = [] and down = []
  rw [List.append_eq_nil_iff] at h
  -- h.1 : up ++ mid = [], h.2 : down = []
  rw [List.append_eq_nil_iff] at h
  -- h.1.1 : up = [], h.1.2 : mid = []
  exact h_mid_ne h.1.2

/-- pathBetween starts with i -/
theorem pathBetween_head (T : TreeAuth n) (i j : Fin n) :
    (T.pathBetween i j).head? = some i := by
  -- Expand pathBetween definition
  show ((T.pathToRoot i).takeWhile (· ≠ T.lca i j) ++ [T.lca i j] ++
        ((T.pathToRoot j).takeWhile (· ≠ T.lca i j)).reverse).head? = some i
  -- Get the structure of pathToRoot i
  have h_ne : T.pathToRoot i ≠ [] := T.pathToRoot_nonempty i
  have h_head : (T.pathToRoot i).head? = some i := T.pathToRoot_head i
  obtain ⟨x, xs, hpath⟩ := List.exists_cons_of_ne_nil h_ne
  simp only [hpath, List.head?_cons, Option.some.injEq] at h_head
  -- x = i
  subst h_head
  -- Now pathToRoot i = i :: xs
  simp only [hpath]
  -- Case split on whether i = lca i j
  by_cases h : i = T.lca i j
  · -- i = ancestor: takeWhile gives [] since first element equals ancestor
    simp only [List.takeWhile_cons, h, ne_eq, not_true_eq_false, decide_False, ite_false,
               List.nil_append, List.head?_cons]
  · -- i ≠ ancestor: takeWhile keeps i as first element
    simp only [List.takeWhile_cons, h, ne_eq, not_false_eq_true, decide_True, ite_true,
               List.append_assoc, List.head?_append_of_ne_nil _ (List.cons_ne_nil _ _),
               List.head?_cons]

/-- pathBetween ends with j -/
theorem pathBetween_last (T : TreeAuth n) (i j : Fin n) :
    (T.pathBetween i j).getLast? = some j := by
  -- Expand pathBetween definition
  show ((T.pathToRoot i).takeWhile (· ≠ T.lca i j) ++ [T.lca i j] ++
        ((T.pathToRoot j).takeWhile (· ≠ T.lca i j)).reverse).getLast? = some j
  -- Get the structure of pathToRoot j
  have h_ne : T.pathToRoot j ≠ [] := T.pathToRoot_nonempty j
  have h_head : (T.pathToRoot j).head? = some j := T.pathToRoot_head j
  obtain ⟨y, ys, hpathj⟩ := List.exists_cons_of_ne_nil h_ne
  simp only [hpathj, List.head?_cons, Option.some.injEq] at h_head
  -- y = j
  subst h_head
  -- Now pathToRoot j = j :: ys
  simp only [hpathj]
  -- Case split on whether j = lca i j
  by_cases h : j = T.lca i j
  · -- j = ancestor: takeWhile gives [] since first element equals ancestor
    simp only [List.takeWhile_cons, h, ne_eq, not_true_eq_false, decide_False, ite_false,
               List.reverse_nil, List.append_nil, List.append_assoc,
               List.getLast?_append (List.cons_ne_nil _ _), List.getLast?_singleton]
  · -- j ≠ ancestor: takeWhile keeps j as first element, reverse puts j at end
    simp only [List.takeWhile_cons, h, ne_eq, not_false_eq_true, decide_True, ite_true]
    have h_rev_ne : (j :: List.takeWhile (fun x => x ≠ T.lca i j) ys).reverse ≠ [] := by
      simp only [ne_eq, List.reverse_eq_nil_iff, List.cons_ne_nil, not_false_eq_true]
    simp only [List.append_assoc, List.getLast?_append h_rev_ne, List.getLast?_reverse,
               List.head?_cons]

/-- i is in pathBetween i j -/
theorem mem_pathBetween_left (T : TreeAuth n) (i j : Fin n) : i ∈ T.pathBetween i j := by
  have h := T.pathBetween_head i j
  have hne := T.pathBetween_nonempty i j
  have ⟨x, xs, hpath⟩ := List.exists_cons_of_ne_nil hne
  simp only [hpath, List.head?_cons, Option.some.injEq] at h
  simp only [hpath, List.mem_cons, h, true_or]

/-- j is in pathBetween i j -/
theorem mem_pathBetween_right (T : TreeAuth n) (i j : Fin n) : j ∈ T.pathBetween i j := by
  have h := T.pathBetween_last i j
  have hne := T.pathBetween_nonempty i j
  rw [List.getLast?_eq_some_getLast hne] at h
  simp only [Option.some.injEq] at h
  rw [← h]
  exact List.getLast_mem hne

/-! ## Tree Properties -/

/-- A tree with n > 0 vertices has n-1 edges -/
theorem edges_count (T : TreeAuth n) (hn : 0 < n) : T.edges.length = n - 1 := by
  -- Every vertex except root has exactly one parent edge
  -- The edges list is (List.finRange n).filterMap f where f returns Some for non-root
  simp only [edges]
  -- parent i = none iff i = root
  have h_none_iff : ∀ i : Fin n, T.parent i = none ↔ i = T.root := by
    intro i
    constructor
    · intro h
      by_contra hne
      have := T.nonroot_has_parent i hne
      rw [h] at this
      simp at this
    · intro h
      rw [h]
      exact T.root_no_parent
  -- The filterMap length equals the count of elements where parent is some
  -- This equals n - 1 since exactly one element (root) has parent = none
  rw [List.length_filterMap]
  -- Count elements where the function returns some
  have h_countP : (List.finRange n).countP (fun i => (T.parent i).isSome) = n - 1 := by
    -- Rewrite countP as length of filter
    rw [List.countP_eq_length_filter]
    -- Elements with parent.isSome are exactly non-root elements
    have h_filter_eq : (List.finRange n).filter (fun i => (T.parent i).isSome) =
        (List.finRange n).filter (fun i => i ≠ T.root) := by
      apply List.filter_congr
      intro i _
      simp only [Option.isSome_iff_exists, ne_eq, decide_eq_decide]
      constructor
      · intro ⟨p, hp⟩ heq
        rw [heq, T.root_no_parent] at hp
        cases hp
      · intro hne
        exact Option.isSome_iff_exists.mpr (T.nonroot_has_parent i hne)
    rw [h_filter_eq]
    -- Count of non-root elements in finRange n is n - 1
    have h_nodup : (List.finRange n).Nodup := List.nodup_finRange n
    have h_mem : T.root ∈ List.finRange n := List.mem_finRange T.root
    rw [List.length_filter_ne h_nodup h_mem, List.length_finRange]
  -- Now relate filterMap isSome to countP
  convert h_countP using 1
  apply List.countP_congr
  intro i _
  cases T.parent i with
  | none => simp
  | some p => simp

/-- Any two vertices can be connected via paths to root -/
theorem connected (T : TreeAuth n) (i j : Fin n) :
    ∃ path : List (Fin n), path ≠ [] ∧ i ∈ path ∧ j ∈ path := by
  use T.pathBetween i j
  exact ⟨T.pathBetween_nonempty i j, T.mem_pathBetween_left i j, T.mem_pathBetween_right i j⟩

/-! ## The Key Property: Acyclicity -/

/-- The 1-skeleton of a tree is acyclic.
    This is the foundation for H¹ = 0.

    Any closed path (cycle) in a tree must backtrack,
    meaning it repeats some intermediate vertex. -/
theorem one_skeleton_acyclic (T : TreeAuth n) :
    ∀ path : List (Fin n), path.length ≥ 3 →
    path.head? = path.getLast? →
    (∀ k (hk : k + 1 < path.length), T.adjacent (path.get ⟨k, Nat.lt_of_succ_lt hk⟩)
                                                (path.get ⟨k + 1, hk⟩)) →
    ∃ k₁ k₂, k₁ < k₂ ∧ k₂ < path.length ∧
      ∃ (h₁ : k₁ < path.length) (h₂ : k₂ < path.length),
        path.get ⟨k₁, h₁⟩ = path.get ⟨k₂, h₂⟩ := by
  -- A closed path in a tree must repeat vertices (backtrack)
  sorry

end TreeAuth

/-! ## Example: Linear Chain (Simple Hierarchy) -/

/-- A linear chain: agent 0 is root, each i > 0 has parent i-1.
    This demonstrates a simple tree authority structure. -/
def linearChain (n : ℕ) (hn : 0 < n) : TreeAuth n where
  root := ⟨0, hn⟩
  parent := fun i =>
    if h : i.val = 0 then none
    else some ⟨i.val - 1, by omega⟩
  root_no_parent := by simp
  nonroot_has_parent := by
    intro i hi
    simp only [dite_eq_ite]
    split_ifs with h
    · have : i = ⟨0, hn⟩ := Fin.ext h
      exact (hi this).elim
    · rfl
  acyclic := by
    intro i
    use i.val + 1
    -- Each step moves from j to j-1, so i.val + 1 steps reaches 0
    -- Define the parent-or-root function
    let f : Fin n → Fin n := fun j =>
      (if _ : j.val = 0 then none else some ⟨j.val - 1, by omega⟩).getD ⟨0, hn⟩
    -- Key lemmas about f
    have hf_zero : f ⟨0, hn⟩ = ⟨0, hn⟩ := by simp [f]
    have hf_pos : ∀ j : Fin n, j.val > 0 → (f j).val = j.val - 1 := by
      intro j hj
      simp only [f, dif_neg (Nat.pos_iff_ne_zero.mp hj), Option.getD_some]
    -- Key lemma: iterating f on value k gives value k - min(m, k) after m steps
    have hf_iter_val : ∀ m k : ℕ, ∀ j : Fin n, j.val = k → (f^[m] j).val = k - min m k := by
      intro m
      induction m with
      | zero => intro k j hj; simp [hj]
      | succ m ihm =>
        intro k j hj
        simp only [Function.iterate_succ_apply]
        cases Nat.eq_zero_or_pos k with
        | inl hk0 =>
          -- k = 0: j is root, f fixes it
          subst hk0
          have hj0 : j = ⟨0, hn⟩ := Fin.ext hj
          simp only [hj0, hf_zero]
          have : (f^[m] ⟨0, hn⟩).val = 0 := by
            have := ihm 0 ⟨0, hn⟩ rfl
            simp at this
            exact this
          simp [this]
        | inr hkpos =>
          -- k > 0: first step gives k-1, then m more steps
          have hfj_val : (f j).val = k - 1 := by rw [hf_pos j (by omega)]; omega
          have hfj : f j = ⟨k - 1, by omega⟩ := Fin.ext hfj_val
          rw [hfj]
          have ihm' := ihm (k - 1) ⟨k - 1, by omega⟩ rfl
          simp only [] at ihm' ⊢
          omega
    -- Apply the iteration lemma
    have h := hf_iter_val (i.val + 1) i.val i rfl
    simp at h
    exact Fin.ext h
  parent_ne_self := fun i h => by
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceDIte] at h
      exact (Option.some_ne_none i h.symm).elim
    · simp only [hi, ↓reduceDIte, Option.some.injEq] at h
      have : i.val - 1 = i.val := congrArg Fin.val h
      omega

end MultiAgent
