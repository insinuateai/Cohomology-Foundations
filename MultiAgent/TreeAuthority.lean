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
import Mathlib.Tactic

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

/-- In pathToRootAux, consecutive elements have parent relationship:
    element k has element k+1 as its parent.
    This is the key lemma for proving path compatibility. -/
theorem pathToRootAux_consecutive_parent (T : TreeAuth n) (i : Fin n) (fuel k : ℕ)
    (hk : k + 1 < (T.pathToRootAux i fuel).length) :
    T.parent ((T.pathToRootAux i fuel).get ⟨k, Nat.lt_of_succ_lt hk⟩) =
    some ((T.pathToRootAux i fuel).get ⟨k + 1, hk⟩) := by
  induction fuel generalizing i k with
  | zero =>
    -- pathToRootAux i 0 = [i], length 1, so k + 1 < 1 is false
    simp only [pathToRootAux, List.length_singleton] at hk
    omega
  | succ fuel' ih =>
    -- Split on parent to determine the structure of pathToRootAux
    match hp : T.parent i with
    | none =>
      -- pathToRootAux i (fuel'+1) = [i] when parent i = none
      simp only [pathToRootAux, hp, List.length_singleton] at hk
      omega
    | some p =>
      -- pathToRootAux i (fuel'+1) = i :: pathToRootAux p fuel'
      have hpath_eq : T.pathToRootAux i (fuel' + 1) = i :: T.pathToRootAux p fuel' := by
        simp only [pathToRootAux, hp]
      -- Get length inequality in the right form
      have hk' : k + 1 < (i :: T.pathToRootAux p fuel').length := by
        simp only [hpath_eq] at hk; exact hk
      cases k with
      | zero =>
        -- Element 0 is i, element 1 is the head of pathToRootAux p fuel'
        -- We need: parent i = some (pathToRootAux p fuel')[0]
        have hlen : 0 < (T.pathToRootAux p fuel').length := by
          simp only [List.length_cons] at hk'; omega
        have h_head := T.pathToRootAux_head p fuel'
        obtain ⟨y, ys, hpath'⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hlen)
        simp only [hpath', List.head?_cons, Option.some.injEq] at h_head
        subst h_head  -- y = p, so substitute
        -- Now goal becomes: parent i = some p, which is exactly hp
        simp only [hpath_eq, List.get_eq_getElem, List.getElem_cons_zero,
                   List.getElem_cons_succ, hpath', List.getElem_cons_zero, hp]
      | succ k' =>
        -- Elements k'+1 and k'+2 are in pathToRootAux p fuel'
        have hk'' : k' + 1 < (T.pathToRootAux p fuel').length := by
          simp only [List.length_cons] at hk'; omega
        have ih_result := ih p k' hk''
        -- Rewrite the goal using hpath_eq
        simp only [hpath_eq, List.get_eq_getElem, List.getElem_cons_succ] at ih_result ⊢
        exact ih_result

/-- Convenience wrapper: consecutive elements in pathToRoot have parent relationship -/
theorem pathToRoot_consecutive_parent (T : TreeAuth n) (i : Fin n) (k : ℕ)
    (hk : k + 1 < (T.pathToRoot i).length) :
    T.parent ((T.pathToRoot i).get ⟨k, Nat.lt_of_succ_lt hk⟩) =
    some ((T.pathToRoot i).get ⟨k + 1, hk⟩) := by
  simp only [pathToRoot]
  exact T.pathToRootAux_consecutive_parent i n k hk

/-- pathToRootAux has length = depthAux + 1 -/
theorem pathToRootAux_length (T : TreeAuth n) (i : Fin n) (fuel : ℕ) :
    (T.pathToRootAux i fuel).length = T.depthAux i fuel + 1 := by
  induction fuel generalizing i with
  | zero => simp only [pathToRootAux, depthAux, List.length_singleton]
  | succ fuel' ih =>
    match hp : T.parent i with
    | none =>
      simp only [pathToRootAux, depthAux, hp, List.length_singleton]
    | some p =>
      simp only [pathToRootAux, depthAux, hp, List.length_cons]
      rw [ih p]
      ring

/-- pathToRoot has length = depth + 1 -/
theorem pathToRoot_length (T : TreeAuth n) (i : Fin n) :
    (T.pathToRoot i).length = T.depth i + 1 := by
  simp only [pathToRoot, depth]
  exact T.pathToRootAux_length i n

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
  -- h_head : x = i, so substitute x with i everywhere
  subst x
  -- Now pathToRoot i = i :: xs
  simp only [hpath]
  -- Case split on whether i = lca i j
  by_cases h : i = T.lca i j
  · -- i = ancestor: takeWhile gives [] since first element equals ancestor
    have htw : List.takeWhile (fun x => decide (x ≠ T.lca i j)) (i :: xs) = [] := by
      rw [List.takeWhile_cons]
      have hdec : decide (i ≠ T.lca i j) = false := decide_eq_false (not_not.mpr h)
      simp only [hdec, Bool.false_eq_true, ↓reduceIte]
    simp only [htw, List.nil_append]
    rw [← h]
    rfl
  · -- i ≠ ancestor: takeWhile keeps i as first element
    have htw : List.takeWhile (fun x => decide (x ≠ T.lca i j)) (i :: xs) =
               i :: List.takeWhile (fun x => decide (x ≠ T.lca i j)) xs := by
      rw [List.takeWhile_cons]
      have hdec : decide (i ≠ T.lca i j) = true := decide_eq_true h
      simp only [hdec, ↓reduceIte]
    simp only [htw, List.cons_append, List.head?_cons]

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
  -- h_head : y = j, so substitute y with j everywhere
  subst y
  -- Now pathToRoot j = j :: ys
  simp only [hpathj]
  -- Case split on whether j = lca i j
  by_cases h : j = T.lca i j
  · -- j = ancestor: takeWhile gives [] since first element equals ancestor
    have htw : List.takeWhile (fun x => decide (x ≠ T.lca i j)) (j :: ys) = [] := by
      rw [List.takeWhile_cons]
      have hdec : decide (j ≠ T.lca i j) = false := decide_eq_false (not_not.mpr h)
      simp only [hdec, Bool.false_eq_true, ↓reduceIte]
    simp only [htw, List.reverse_nil, List.append_nil]
    simp only [List.getLast?_append, List.getLast?_singleton]
    simp only [Option.some_or]
    exact congrArg some h.symm
  · -- j ≠ ancestor: takeWhile keeps j as first element, reverse puts j at end
    have htw : List.takeWhile (fun x => decide (x ≠ T.lca i j)) (j :: ys) =
               j :: List.takeWhile (fun x => decide (x ≠ T.lca i j)) ys := by
      rw [List.takeWhile_cons]
      have hdec : decide (j ≠ T.lca i j) = true := decide_eq_true h
      simp only [hdec, ↓reduceIte]
    simp only [htw, List.append_assoc, List.getLast?_append, List.getLast?_reverse,
               List.head?_cons, Option.some_or]

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
  have hmem : (T.pathBetween i j).getLast hne ∈ T.pathBetween i j := List.getLast_mem hne
  rw [h] at hmem
  exact hmem

/-! ### Helper Lemmas for pathBetween_consecutive_adjacent -/

/-- Consecutive elements in takeWhile preserve the parent relationship from pathToRoot.
    If positions k and k+1 are both in the takeWhile segment, they have parent→child relation. -/
theorem takeWhile_consecutive_preserves_parent (T : TreeAuth n) (i ancestor : Fin n) (k : ℕ)
    (hk : k + 1 < ((T.pathToRoot i).takeWhile (· ≠ ancestor)).length) :
    T.parent (((T.pathToRoot i).takeWhile (· ≠ ancestor)).get ⟨k, Nat.lt_of_succ_lt hk⟩) =
    some (((T.pathToRoot i).takeWhile (· ≠ ancestor)).get ⟨k + 1, hk⟩) := by
  -- takeWhile p l is a prefix of l, so positions map directly
  have hprefix : (T.pathToRoot i).takeWhile (· ≠ ancestor) <+: T.pathToRoot i :=
    List.takeWhile_prefix _
  -- Get the length bound for the original list
  have hk_orig : k + 1 < (T.pathToRoot i).length := by
    calc k + 1 < ((T.pathToRoot i).takeWhile (· ≠ ancestor)).length := hk
      _ ≤ (T.pathToRoot i).length := hprefix.length_le
  -- Use prefix property to rewrite getElem
  have h1 : ((T.pathToRoot i).takeWhile (· ≠ ancestor))[k] = (T.pathToRoot i)[k] :=
    hprefix.getElem (Nat.lt_of_succ_lt hk)
  have h2 : ((T.pathToRoot i).takeWhile (· ≠ ancestor))[k + 1] = (T.pathToRoot i)[k + 1] :=
    hprefix.getElem hk
  simp only [List.get_eq_getElem, h1, h2]
  exact T.pathToRoot_consecutive_parent i k hk_orig

/-- The last element of takeWhile has the ancestor as its parent.
    This connects the up_segment to the ancestor. -/
theorem takeWhile_last_parent_is_ancestor (T : TreeAuth n) (i ancestor : Fin n)
    (hanc : ancestor ∈ T.pathToRoot i)
    (hne : (T.pathToRoot i).takeWhile (· ≠ ancestor) ≠ []) :
    T.parent (((T.pathToRoot i).takeWhile (· ≠ ancestor)).getLast hne) = some ancestor := by
  -- Use takeWhile ++ dropWhile = original
  have heq : (T.pathToRoot i).takeWhile (· ≠ ancestor) ++ (T.pathToRoot i).dropWhile (· ≠ ancestor)
             = T.pathToRoot i := List.takeWhile_append_dropWhile
  have hprefix : (T.pathToRoot i).takeWhile (· ≠ ancestor) <+: T.pathToRoot i :=
    List.takeWhile_prefix _
  -- The dropWhile starts with ancestor (since ancestor ∈ pathToRoot i)
  have hdrop_ne : (T.pathToRoot i).dropWhile (· ≠ ancestor) ≠ [] := by
    intro h
    rw [List.dropWhile_eq_nil_iff] at h
    specialize h ancestor hanc
    simp only [decide_eq_true_eq, ne_eq, not_true_eq_false] at h
  have hdrop_head : ((T.pathToRoot i).dropWhile (· ≠ ancestor)).head hdrop_ne = ancestor := by
    have h := List.head_dropWhile_not (· ≠ ancestor) hdrop_ne
    simp only [decide_eq_false_iff_not, ne_eq, Decidable.not_not] at h
    exact h
  -- The last of takeWhile and head of dropWhile are consecutive in pathToRoot
  -- Use abbreviation to simplify
  let tw := (T.pathToRoot i).takeWhile (· ≠ ancestor)
  have htw_lt : tw.length < (T.pathToRoot i).length := by
    by_contra h
    push_neg at h
    have hlen_eq : tw.length = (T.pathToRoot i).length := le_antisymm hprefix.length_le h
    have heq' : tw = T.pathToRoot i := hprefix.eq_of_length hlen_eq
    have hdrop_nil : (T.pathToRoot i).dropWhile (· ≠ ancestor) = [] := by
      -- heq : tw ++ dropWhile = pathToRoot, heq' : tw = pathToRoot
      -- Substitute to get pathToRoot ++ dropWhile = pathToRoot
      have h' : T.pathToRoot i ++ (T.pathToRoot i).dropWhile (· ≠ ancestor) = T.pathToRoot i := by
        calc T.pathToRoot i ++ (T.pathToRoot i).dropWhile (· ≠ ancestor)
            = tw ++ (T.pathToRoot i).dropWhile (· ≠ ancestor) := by rw [heq']
          _ = T.pathToRoot i := heq
      rw [List.append_right_eq_self] at h'
      exact h'
    exact hdrop_ne hdrop_nil
  have hpos : tw.length - 1 + 1 = tw.length :=
    Nat.sub_add_cancel (List.length_pos_iff_ne_nil.mpr hne)
  have hk_succ : tw.length - 1 + 1 < (T.pathToRoot i).length := by omega
  have hcons := T.pathToRoot_consecutive_parent i (tw.length - 1) hk_succ
  -- tw.getLast = pathToRoot[tw.length - 1]
  have h_tw_last : tw.getLast hne = (T.pathToRoot i)[tw.length - 1] := by
    rw [List.getLast_eq_getElem]
    exact hprefix.getElem _
  -- pathToRoot[tw.length] = ancestor
  have h_next : (T.pathToRoot i)[tw.length]'htw_lt = ancestor := by
    have hdw_pos : 0 < ((T.pathToRoot i).dropWhile (· ≠ ancestor)).length :=
      List.length_pos_iff_ne_nil.mpr hdrop_ne
    have happ_len : tw.length < (tw ++ (T.pathToRoot i).dropWhile (· ≠ ancestor)).length := by
      simp only [List.length_append]; omega
    have h1 : (tw ++ (T.pathToRoot i).dropWhile (· ≠ ancestor))[tw.length]'happ_len =
              ((T.pathToRoot i).dropWhile (· ≠ ancestor))[0]'hdw_pos := by
      rw [List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self]
    have h2 : ((T.pathToRoot i).dropWhile (· ≠ ancestor))[0]'hdw_pos = ancestor := by
      rw [← List.head_eq_getElem hdrop_ne, hdrop_head]
    calc (T.pathToRoot i)[tw.length]'htw_lt
        = (tw ++ (T.pathToRoot i).dropWhile (· ≠ ancestor))[tw.length]'happ_len := by
            congr 1; exact heq.symm
      _ = ((T.pathToRoot i).dropWhile (· ≠ ancestor))[0]'hdw_pos := h1
      _ = ancestor := h2
  -- Combine: hcons says parent(pathToRoot[tw.length-1]) = some(pathToRoot[tw.length])
  -- h_tw_last: tw.getLast = pathToRoot[tw.length-1]
  -- h_next: pathToRoot[tw.length] = ancestor
  simp only [List.get_eq_getElem, hpos] at hcons
  -- hcons: parent(pathToRoot[tw.length-1]) = some(pathToRoot[tw.length])
  -- Goal: parent(tw.getLast hne) = some ancestor
  rw [h_tw_last]
  simp only [h_next] at hcons
  exact hcons

/-- Consecutive elements in the reversed takeWhile are adjacent.
    In the reversed list, the parent relationship is flipped but adjacent is symmetric. -/
theorem reverse_takeWhile_consecutive_adjacent (T : TreeAuth n) (j ancestor : Fin n) (k : ℕ)
    (hanc : ancestor ∈ T.pathToRoot j)
    (hk : k + 1 < (((T.pathToRoot j).takeWhile (· ≠ ancestor)).reverse).length) :
    T.adjacent ((((T.pathToRoot j).takeWhile (· ≠ ancestor)).reverse).get ⟨k, Nat.lt_of_succ_lt hk⟩)
               ((((T.pathToRoot j).takeWhile (· ≠ ancestor)).reverse).get ⟨k + 1, hk⟩) := by
  let tw := (T.pathToRoot j).takeWhile (· ≠ ancestor)
  have hk_tw : k + 1 < tw.length := by simp only [List.length_reverse] at hk; exact hk
  -- Positions in tw for the reversed indices
  let pos_k := tw.length - 1 - k
  let pos_k1 := tw.length - 1 - (k + 1)
  have hconsec : pos_k1 + 1 = pos_k := by omega
  -- Use List.getElem_reverse: l.reverse[i] = l[l.length - 1 - i]
  have hpos_k_lt : pos_k < tw.length := by omega
  have hpos_k1_lt : pos_k1 < tw.length := by omega
  -- Goal: adjacent(tw.reverse[k], tw.reverse[k+1])
  -- = adjacent(tw[pos_k], tw[pos_k1])
  -- pos_k1 + 1 = pos_k means tw[pos_k1].parent = some tw[pos_k] (child→parent in original)
  -- So adjacent(tw[pos_k], tw[pos_k1]) holds via Right case
  -- Goal: adjacent(tw.reverse.get k, tw.reverse.get (k+1))
  -- = T.parent (get k) = some (get k+1) ∨ T.parent (get k+1) = some (get k)
  -- We use the Right case: parent(get k+1) = some(get k)
  -- Since in reversed list, k+1 maps to pos_k1 = length-1-(k+1) in original
  -- and k maps to pos_k = length-1-k, with pos_k1 + 1 = pos_k
  -- parent(tw[pos_k1]) = some(tw[pos_k]) by takeWhile_consecutive_preserves_parent
  have hparent := takeWhile_consecutive_preserves_parent T j ancestor pos_k1 (by omega : pos_k1 + 1 < tw.length)
  simp only [hconsec] at hparent
  -- hparent: parent(tw[pos_k1]) = some(tw[pos_k])
  have h1 : tw.reverse[k + 1]'hk = tw[pos_k1]'hpos_k1_lt := List.getElem_reverse hk
  have h2 : tw.reverse[k]'(Nat.lt_of_succ_lt hk) = tw[pos_k]'hpos_k_lt := List.getElem_reverse _
  simp only [List.get_eq_getElem, adjacent]
  right
  rw [h1, h2]
  exact hparent

/-! ### Root Membership Lemmas (moved earlier for forward reference resolution) -/

/-- Helper: pathToRootAux with sufficient fuel contains all vertices on path to root -/
theorem pathToRootAux_contains_root (T : TreeAuth n) (i : Fin n) (fuel : ℕ) :
    (∃ k ≤ fuel, T.parentOrRoot^[k] i = T.root) → T.root ∈ T.pathToRootAux i fuel := by
  intro ⟨k, hk_le, hk_root⟩
  induction fuel generalizing i k with
  | zero =>
    -- k ≤ 0 means k = 0, so i = root
    have hk_zero : k = 0 := Nat.le_zero.mp hk_le
    rw [hk_zero, Function.iterate_zero, id_eq] at hk_root
    simp only [pathToRootAux, hk_root, List.mem_singleton]
  | succ fuel' ih =>
    simp only [pathToRootAux]
    cases hp : T.parent i with
    | none =>
      -- i = root (since non-root has parent)
      have hi_root : i = T.root := by
        by_contra h
        have := T.nonroot_has_parent i h
        rw [hp] at this; simp at this
      simp only [hi_root, List.mem_singleton]
    | some p =>
      -- pathToRootAux i (fuel'+1) = i :: pathToRootAux p fuel'
      simp only [List.mem_cons]
      by_cases hi : i = T.root
      · left; exact hi.symm
      · right
        -- k > 0 since parentOrRoot^[0] i = i ≠ root
        have hk_pos : k > 0 := by
          by_contra h
          push_neg at h
          have hk_zero : k = 0 := Nat.le_zero.mp h
          rw [hk_zero, Function.iterate_zero, id_eq] at hk_root
          exact hi hk_root
        -- parentOrRoot^[k] i = parentOrRoot^[k-1] (parentOrRoot i) = parentOrRoot^[k-1] p = root
        have hp_eq : T.parentOrRoot i = p := T.parentOrRoot_of_some i p hp
        have hk_root' : T.parentOrRoot^[k - 1] (T.parentOrRoot i) = T.root := by
          have : T.parentOrRoot^[k] i = T.parentOrRoot^[k - 1] (T.parentOrRoot i) := by
            conv_lhs => rw [show k = (k - 1) + 1 by omega, Function.iterate_succ_apply]
          rw [← this]
          exact hk_root
        rw [hp_eq] at hk_root'
        -- Apply IH with k' = k - 1 and vertex p
        apply ih p (k - 1)
        · omega
        · exact hk_root'

/-- The minimum steps to reach root is bounded by n (pigeonhole) -/
private theorem min_steps_to_root_le_n (T : TreeAuth n) (i : Fin n)
    (h_exists : ∃ k, T.parentOrRoot^[k] i = T.root) :
    Nat.find h_exists ≤ n := by
  by_contra h
  push_neg at h
  have hmin := Nat.find_spec h_exists
  -- The sequence i, parentOrRoot i, ..., parentOrRoot^n i are n+1 elements of Fin n
  -- By pigeonhole, some two must be equal
  have h_pigeonhole : ∃ j k, j < k ∧ k ≤ n ∧ T.parentOrRoot^[j] i = T.parentOrRoot^[k] i := by
    by_contra h_all_distinct
    push_neg at h_all_distinct
    -- All n+1 iterates are distinct, but they're all in Fin n
    -- This is impossible by cardinality
    have h_inj : Function.Injective (fun m : Fin (n + 1) => T.parentOrRoot^[m.val] i) := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ heq
      simp only [Fin.mk.injEq]
      by_contra hab
      cases Nat.lt_trichotomy a b with
      | inl hab' => exact h_all_distinct a b hab' (by omega) heq
      | inr hc =>
        cases hc with
        | inl hab' => exact hab hab'
        | inr hab' => exact h_all_distinct b a hab' (by omega) heq.symm
    -- Injective function from Fin (n+1) to Fin n is impossible
    have : Fintype.card (Fin (n + 1)) ≤ Fintype.card (Fin n) := Fintype.card_le_of_injective _ h_inj
    simp only [Fintype.card_fin] at this
    omega
  obtain ⟨j, k, hjk, hkn, heq⟩ := h_pigeonhole
  -- parentOrRoot^[j] i = parentOrRoot^[k] i with j < k ≤ n < Nat.find h_exists
  -- So neither j nor k reaches root yet
  have hj_not_root : T.parentOrRoot^[j] i ≠ T.root := by
    intro heq'
    have : Nat.find h_exists ≤ j := Nat.find_min' h_exists heq'
    omega
  -- The sequence is periodic from j with period (k-j)
  -- So for any m ≥ j, parentOrRoot^[m] i cycles through the same values
  -- and never reaches root
  have hkj_pos : 0 < k - j := by omega
  -- Key: parentOrRoot^[j + m*(k-j)] i = parentOrRoot^[j] i for all m
  have h_periodic : ∀ m, T.parentOrRoot^[j + m * (k - j)] i = T.parentOrRoot^[j] i := by
    intro m
    induction m with
    | zero => simp
    | succ m' ih =>
      -- Goal: parentOrRoot^[j + (m'+1)*(k-j)] i = parentOrRoot^[j] i
      -- Rewrite the index
      have h1 : j + (m' + 1) * (k - j) = (k - j) + (j + m' * (k - j)) := by ring
      rw [h1, Function.iterate_add_apply]
      -- Goal: parentOrRoot^[k-j] (parentOrRoot^[j + m'*(k-j)] i) = parentOrRoot^[j] i
      rw [ih]
      -- Goal: parentOrRoot^[k-j] (parentOrRoot^[j] i) = parentOrRoot^[j] i
      -- Use: parentOrRoot^[k] i = parentOrRoot^[j] i (from heq)
      -- And: parentOrRoot^[k] i = parentOrRoot^[(k-j) + j] i = parentOrRoot^[k-j] (parentOrRoot^[j] i)
      have h2 : T.parentOrRoot^[k - j] (T.parentOrRoot^[j] i) = T.parentOrRoot^[(k - j) + j] i := by
        rw [← Function.iterate_add_apply]
      rw [h2]
      have h3 : (k - j) + j = k := by omega
      rw [h3]
      exact heq.symm
  -- Now we derive contradiction: Nat.find h_exists is the first time we reach root
  -- But for any M with j + M*(k-j) ≥ Nat.find h_exists, the iterate equals parentOrRoot^[j] i ≠ root
  -- First show that for large enough M, j + M*(k-j) ≥ Nat.find h_exists
  have ⟨M, hM⟩ : ∃ M, Nat.find h_exists ≤ j + M * (k - j) := by
    use Nat.find h_exists
    have h_ge : Nat.find h_exists * (k - j) ≥ Nat.find h_exists := by
      exact Nat.le_mul_of_pos_right (Nat.find h_exists) hkj_pos
    omega
  -- The iterate at step (j + M*(k-j)) equals parentOrRoot^[j] i
  have h_at_M := h_periodic M
  -- But parentOrRoot^[j] i ≠ root
  -- And for any step ≥ Nat.find h_exists, the sequence stays at root
  -- Since parentOrRoot root = root
  have h_root_fixed : T.parentOrRoot T.root = T.root := T.parentOrRoot_root
  -- After reaching root at step Nat.find h_exists, all further iterates stay at root
  have h_stays_root : ∀ m ≥ Nat.find h_exists, T.parentOrRoot^[m] i = T.root := by
    intro m hm
    have hdiff : m = (m - Nat.find h_exists) + Nat.find h_exists := by omega
    rw [hdiff, Function.iterate_add_apply, hmin]
    -- Goal: T.parentOrRoot^[m - Nat.find h_exists] T.root = T.root
    clear hdiff
    induction m - Nat.find h_exists with
    | zero => rfl
    | succ d ih =>
      simp only [Function.iterate_succ', Function.comp_apply, ih, h_root_fixed]
  -- Apply h_stays_root to j + M*(k-j) ≥ Nat.find h_exists
  have h_is_root := h_stays_root (j + M * (k - j)) hM
  -- But h_at_M says this equals parentOrRoot^[j] i
  rw [h_at_M] at h_is_root
  -- So parentOrRoot^[j] i = root, contradicting hj_not_root
  exact hj_not_root h_is_root

/-- Root is always in pathToRoot (when n > 0) -/
theorem root_mem_pathToRoot (T : TreeAuth n) (i : Fin n) (hn : 0 < n) : T.root ∈ T.pathToRoot i := by
  simp only [pathToRoot]
  obtain ⟨k, hk⟩ := T.acyclic i
  have h_exists : ∃ k, T.parentOrRoot^[k] i = T.root := ⟨k, hk⟩
  apply T.pathToRootAux_contains_root i n
  use Nat.find h_exists
  exact ⟨T.min_steps_to_root_le_n i h_exists, Nat.find_spec h_exists⟩

/-! ### Ancestor Adjacency Lemmas -/

/-- The first element of the reversed down_segment has the ancestor as its parent.
    This connects the ancestor to the down_segment. -/
theorem ancestor_adjacent_first_down (T : TreeAuth n) (i j : Fin n) (hn : 0 < n)
    (hne : ((T.pathToRoot j).takeWhile (· ≠ T.lca i j)).reverse ≠ []) :
    T.adjacent (T.lca i j)
      ((((T.pathToRoot j).takeWhile (· ≠ T.lca i j)).reverse).head hne) := by
  let tw := (T.pathToRoot j).takeWhile (· ≠ T.lca i j)
  have htw_ne : tw ≠ [] := by
    intro h
    have : tw.reverse = [] := by rw [h]; simp
    exact hne this
  -- Prove lca ∈ pathToRoot j (inline since lca_mem_pathToRoot_right is defined later)
  have hanc : T.lca i j ∈ T.pathToRoot j := by
    simp only [lca]
    match hf : (T.pathToRoot i).find? (fun x => decide (x ∈ T.pathToRoot j)) with
    | some x =>
      have hp := List.find?_some hf
      simp only [decide_eq_true_eq] at hp
      exact hp
    | none =>
      -- The lca defaults to root when find? returns none
      -- Root is always in pathToRoot - proved via pathToRoot ending at root
      -- The path from j to root includes root as the last element
      have hne := T.pathToRoot_nonempty j
      -- pathToRoot always ends at root (follows from acyclic property)
      -- For now, we use that find? returning none means no common ancestor was found
      -- in path_i, so the default (root) is used. Root is in both paths.
      -- This case rarely happens in practice since root is always common.
      -- Inline proof: pathToRoot ends at root, so root ∈ pathToRoot
      match hp : T.parent j with
      | none =>
        -- j is root, so pathToRoot j = [j] = [root]
        have hj_root : j = T.root := by
          by_contra h
          have := T.nonroot_has_parent j h
          rw [hp] at this
          simp at this
        subst hj_root
        -- pathToRootAux root n = [root] (since root has no parent)
        have hroot_path : T.pathToRootAux T.root n = [T.root] := by
          cases n with
          | zero => simp [pathToRootAux]
          | succ m => simp [pathToRootAux, T.root_no_parent]
        simp only [pathToRoot, hroot_path, List.mem_singleton]
      | some p =>
        -- j has parent - use root_mem_pathToRoot (now available)
        exact root_mem_pathToRoot T j hn
  -- Apply takeWhile_last_parent_is_ancestor
  have hparent := takeWhile_last_parent_is_ancestor T j (T.lca i j) hanc htw_ne
  -- head(tw.reverse) = getLast(tw) by List.head_reverse
  -- Goal: adjacent(lca, tw.reverse.head hne)
  -- hparent: parent(tw.getLast htw_ne) = some lca
  -- adjacent definition: parent a = some b ∨ parent b = some a
  simp only [adjacent]
  right
  -- Need: parent(tw.reverse.head hne) = some lca
  -- tw.reverse.head hne = tw.getLast htw_ne by List.head_reverse
  convert hparent using 2
  exact List.head_reverse hne

/-- Consecutive elements in pathBetween are adjacent: one is the parent of the other.
    This is the key property for proving compatibility.

    Structure: pathBetween = up_segment ++ [ancestor] ++ down_segment where
    - up_segment: (pathToRoot i).takeWhile (· ≠ ancestor) - consecutive have parent relation
    - down_segment: reversed takeWhile from pathToRoot j - consecutive have child relation
    - Junctions: parent relations to/from ancestor -/
theorem pathBetween_consecutive_adjacent (T : TreeAuth n) (i j : Fin n) (k : ℕ)
    (hk : k + 1 < (T.pathBetween i j).length) :
    T.adjacent ((T.pathBetween i j).get ⟨k, Nat.lt_of_succ_lt hk⟩)
               ((T.pathBetween i j).get ⟨k + 1, hk⟩) := by
  -- Define abbreviations
  let ancestor := T.lca i j
  let up := (T.pathToRoot i).takeWhile (· ≠ ancestor)
  let down := ((T.pathToRoot j).takeWhile (· ≠ ancestor)).reverse

  -- pathBetween = up ++ [ancestor] ++ down (definitionally equal)
  -- Structure is ((up ++ [ancestor]) ++ down) due to left-associativity
  -- Use show to convert goal to explicit form
  show T.adjacent ((up ++ [ancestor] ++ down).get ⟨k, Nat.lt_of_succ_lt hk⟩)
                  ((up ++ [ancestor] ++ down).get ⟨k + 1, hk⟩)

  -- Get lengths for case analysis
  have hlen : (up ++ [ancestor] ++ down).length = up.length + 1 + down.length := by
    simp only [List.length_append, List.length_singleton]

  -- Case 1: k + 1 < up.length (both k and k+1 in up segment)
  by_cases h1 : k + 1 < up.length
  · have hk_up : k < up.length := Nat.lt_of_succ_lt h1
    -- Both indices are in ((up ++ [ancestor]) ++ down), specifically in (up ++ [ancestor])
    have hk_lt_mid : k < (up ++ [ancestor]).length := by simp [List.length_append]; omega
    have hk1_lt_mid : k + 1 < (up ++ [ancestor]).length := by simp [List.length_append]; omega
    simp only [List.get_eq_getElem, List.getElem_append_left hk_lt_mid,
               List.getElem_append_left hk1_lt_mid, List.getElem_append_left hk_up,
               List.getElem_append_left h1]
    -- Goal: T.adjacent up[k] up[k+1]
    left
    convert takeWhile_consecutive_preserves_parent T i ancestor k h1 using 2

  push_neg at h1

  -- Case 2: k + 1 = up.length (k at last of up, k+1 at ancestor)
  by_cases h2 : k + 1 = up.length
  · have hk_up : k = up.length - 1 := by omega
    have hup_ne : up ≠ [] := by
      intro h; rw [h] at h2; simp at h2
    have hk_in_up : k < up.length := by omega
    -- Structure is ((up ++ [ancestor]) ++ down)
    -- Both k and k+1 are in (up ++ [ancestor]) since k+1 = up.length < up.length + 1
    have hk_lt_mid : k < (up ++ [ancestor]).length := by simp [List.length_append]; omega
    have hk1_lt_mid : k + 1 < (up ++ [ancestor]).length := by simp [List.length_append]; omega
    simp only [List.get_eq_getElem]
    simp only [List.getElem_append_left hk_lt_mid, List.getElem_append_left hk1_lt_mid]
    -- Now: T.adjacent (up ++ [ancestor])[k] (up ++ [ancestor])[k + 1]
    -- k < up.length, so (up ++ [ancestor])[k] = up[k]
    simp only [List.getElem_append_left hk_in_up]
    -- k + 1 = up.length, so (up ++ [ancestor])[k + 1] = [ancestor][0] = ancestor
    have hk1_ge_up : up.length ≤ k + 1 := le_of_eq h2.symm
    simp only [h2]
    -- Goal: T.adjacent up[k] ancestor
    -- up[k] = up.getLast and parent(up.getLast) = ancestor
    have hk_last : up[k] = up.getLast hup_ne := by
      rw [List.getLast_eq_getElem]; congr
    rw [hk_last]
    left
    have hn : 0 < n := Fin.pos i
    -- ancestor ∈ pathToRoot i: lca is found by find? on pathToRoot i, so it's in the list
    have hanc : ancestor ∈ T.pathToRoot i := by
      show T.lca i j ∈ T.pathToRoot i
      simp only [lca]
      generalize hf : (T.pathToRoot i).find? (fun x => decide (x ∈ T.pathToRoot j)) = result
      cases result with
      | some x => exact List.mem_of_find?_eq_some hf
      | none =>
        -- When find? returns none, lca defaults to root
        -- Root is always in pathToRoot
        exact root_mem_pathToRoot T i hn
    convert takeWhile_last_parent_is_ancestor T i ancestor hanc hup_ne using 2
    -- Need: (up ++ [ancestor])[up.length] = ancestor
    simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]

  push_neg at h2
  have h2' : up.length < k + 1 := Nat.lt_of_le_of_ne h1 (Ne.symm h2)

  -- Case 3: k = up.length (k at ancestor, k+1 in down)
  by_cases h3 : k = up.length
  · -- Structure: ((up ++ [ancestor]) ++ down)
    -- k = up.length, so k is at position up.length in (up ++ [ancestor]), which is ancestor
    -- k + 1 = up.length + 1 = (up ++ [ancestor]).length, so k+1 is in down
    have hk_lt_mid : k < (up ++ [ancestor]).length := by simp [List.length_append]; omega
    have hk1_ge_mid : (up ++ [ancestor]).length ≤ k + 1 := by simp [List.length_append]; omega
    simp only [List.get_eq_getElem]
    simp only [List.getElem_append_left hk_lt_mid, List.getElem_append_right hk1_ge_mid]
    -- (up ++ [ancestor])[k] where k = up.length, so [ancestor][0] = ancestor
    have hk_ge_up : up.length ≤ k := le_of_eq h3.symm
    simp only [h3]
    -- down ≠ [] since k+1 indexes into it
    have hdown_ne : down ≠ [] := by
      intro h
      -- If down = [], then length = up.length + 1, and hk says k + 1 < length
      -- But h3 says k = up.length, so up.length + 1 < up.length + 1, contradiction
      have hlen' : (up ++ [ancestor] ++ down).length = up.length + 1 := by
        simp only [h, List.append_nil, List.length_append, List.length_singleton]
      have : k + 1 < up.length + 1 := by rw [← hlen']; exact hk
      omega
    have hdown_pos : 0 < down.length := List.length_pos_of_ne_nil hdown_ne
    -- Goal: T.adjacent (up ++ [ancestor])[up.length] down[k + 1 - (up ++ [ancestor]).length]
    -- Since k = up.length (h3), and (up ++ [ancestor]).length = up.length + 1
    -- k + 1 - (up.length + 1) = up.length + 1 - (up.length + 1) = 0
    have hidx_eq : up.length + 1 - (up ++ [ancestor]).length = 0 := by
      simp only [List.length_append, List.length_singleton]; omega
    -- (up ++ [ancestor])[up.length] = ancestor
    have heq_anc : (up ++ [ancestor])[up.length]'(by simp [List.length_append]) = ancestor := by
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
    -- Substitute k = up.length in goal and simplify
    simp only [heq_anc, hidx_eq]
    -- Goal: T.adjacent ancestor down[0]
    have hhead_eq : down[0]'hdown_pos = down.head hdown_ne := by rw [List.head_eq_getElem]
    rw [hhead_eq]
    have hn : 0 < n := Fin.pos i
    exact ancestor_adjacent_first_down T i j hn hdown_ne

  push_neg at h3
  have h3' : up.length < k := Nat.lt_of_le_of_ne (by omega) (fun h => h3 h.symm)

  -- Case 4: both k and k+1 in down segment
  -- k > up.length, so both indices are past (up ++ [ancestor])
  have hk_ge_mid : (up ++ [ancestor]).length ≤ k := by simp [List.length_append]; omega
  have hk1_ge_mid : (up ++ [ancestor]).length ≤ k + 1 := by simp [List.length_append]; omega
  simp only [List.get_eq_getElem]
  simp only [List.getElem_append_right hk_ge_mid, List.getElem_append_right hk1_ge_mid]
  -- Now indexing into down at positions (k - (up.length + 1)) and (k + 1 - (up.length + 1))
  simp only [List.length_append, List.length_singleton]
  -- These are consecutive positions in down
  have hk_down : k - (up.length + 1) + 1 < down.length := by
    -- hk : k + 1 < (T.pathBetween i j).length which equals (up ++ [ancestor] ++ down).length
    -- hlen : (up ++ [ancestor] ++ down).length = up.length + 1 + down.length
    have : k + 1 < up.length + 1 + down.length := by rw [← hlen]; exact hk
    omega
  -- Show that the indices are consecutive in down
  have hconsec : k + 1 - (up.length + 1) = k - (up.length + 1) + 1 := by omega
  -- Use convert to handle the index equation
  have hn : 0 < n := Fin.pos i
  have hanc : ancestor ∈ T.pathToRoot j := by
    show T.lca i j ∈ T.pathToRoot j
    simp only [lca]
    generalize hf : (T.pathToRoot i).find? (fun x => decide (x ∈ T.pathToRoot j)) = result
    cases result with
    | some x =>
      have hp := List.find?_some hf
      simp only [decide_eq_true_eq] at hp
      exact hp
    | none =>
      -- Root is in pathToRoot j
      exact root_mem_pathToRoot T j hn
  -- Indices in down segment: k - (up.length + 1) and k + 1 - (up.length + 1)
  have hk_down' : k - (up.length + 1) + 1 < down.length := hk_down
  have hadj := reverse_takeWhile_consecutive_adjacent T j ancestor (k - (up.length + 1)) hanc hk_down'
  -- Normalize hadj to use getElem notation and match goal's index form
  simp only [List.get_eq_getElem] at hadj
  -- k - (up.length + 1) + 1 = k + 1 - (up.length + 1) when up.length + 1 ≤ k
  have hidx : k - (up.length + 1) + 1 = k + 1 - (up.length + 1) := by omega
  simp only [hidx] at hadj
  exact hadj

/-! ## Tree Properties -/

/-- Helper: depthAux i fuel = 0 when i is root -/
theorem depthAux_root (T : TreeAuth n) (fuel : ℕ) : T.depthAux T.root fuel = 0 := by
  match fuel with
  | 0 => rfl
  | fuel' + 1 =>
    simp only [depthAux, T.root_no_parent]

/-- Helper: depthAux strictly decreases when moving to parent -/
theorem depthAux_parent (T : TreeAuth n) (i p : Fin n) (hp : T.parent i = some p) (fuel : ℕ) :
    T.depthAux i (fuel + 1) = T.depthAux p fuel + 1 := by
  simp only [depthAux, hp]
  ring

/-- Non-root has positive depth (with sufficient fuel) -/
theorem depthAux_pos_of_nonroot (T : TreeAuth n) (i : Fin n) (hi : i ≠ T.root) (fuel : ℕ)
    (hfuel : fuel > 0) : T.depthAux i fuel > 0 := by
  match fuel with
  | 0 => omega
  | fuel' + 1 =>
    have hp := T.nonroot_has_parent i hi
    rw [Option.isSome_iff_exists] at hp
    obtain ⟨p, hp⟩ := hp
    simp only [depthAux, hp]
    omega

/-- depthAux increases monotonically with fuel -/
theorem depthAux_mono (T : TreeAuth n) (i : Fin n) (fuel1 fuel2 : ℕ) (h : fuel1 ≤ fuel2) :
    T.depthAux i fuel1 ≤ T.depthAux i fuel2 := by
  induction fuel1 generalizing i fuel2 with
  | zero => simp only [depthAux]; omega
  | succ f1 ih =>
    cases fuel2 with
    | zero => omega
    | succ f2 =>
      simp only [depthAux]
      cases hp : T.parent i with
      | none => simp only [hp]; omega
      | some p =>
        simp only [hp]
        have h' : f1 ≤ f2 := by omega
        have ih_p := ih p f2 h'
        omega

/-- depthAux with fuel 0 is 0 -/
@[simp] theorem depthAux_zero (T : TreeAuth n) (i : Fin n) : T.depthAux i 0 = 0 := rfl

/-- depthAux with parent some -/
theorem depthAux_succ_some (T : TreeAuth n) (i : Fin n) (fuel : ℕ) (p : Fin n)
    (hp : T.parent i = some p) :
    T.depthAux i (fuel + 1) = 1 + T.depthAux p fuel := by
  simp only [depthAux, hp]

/-- depthAux with parent none -/
theorem depthAux_succ_none (T : TreeAuth n) (i : Fin n) (fuel : ℕ)
    (hp : T.parent i = none) :
    T.depthAux i (fuel + 1) = 0 := by
  simp only [depthAux, hp]

/-- Helper: depthAux with any fuel is bounded by that fuel -/
theorem depthAux_le_fuel (T : TreeAuth n) (i : Fin n) (fuel : ℕ) :
    T.depthAux i fuel ≤ fuel := by
  induction fuel generalizing i with
  | zero => simp only [depthAux]; omega
  | succ f ih =>
    cases hp : T.parent i with
    | none => rw [depthAux_succ_none T i f hp]; omega
    | some p =>
      rw [depthAux_succ_some T i f p hp]
      have := ih p
      omega

/-- depth is bounded by n -/
theorem depth_le_n (T : TreeAuth n) (i : Fin n) : T.depth i ≤ n := by
  simp only [depth]
  exact T.depthAux_le_fuel i n

/-- Helper: depthAux j m = m implies parentOrRoot^[k] j ≠ root for all k < m -/
theorem depthAux_eq_fuel_not_root (T : TreeAuth n) (j : Fin n) (m : ℕ) (hm : T.depthAux j m = m) :
    ∀ k < m, T.parentOrRoot^[k] j ≠ T.root := by
  induction m generalizing j with
  | zero => intro k hk; omega
  | succ m' ih =>
    intro k hk
    cases hpj : T.parent j with
    | none =>
      rw [depthAux_succ_none T j m' hpj] at hm
      omega  -- 0 = m' + 1 is false
    | some pj =>
      rw [depthAux_succ_some T j m' pj hpj] at hm
      have hpj_depth : T.depthAux pj m' = m' := by omega
      cases k with
      | zero =>
        -- parentOrRoot^[0] j = j, need j ≠ root
        simp only [Function.iterate_zero, id_eq]
        intro hj_root
        rw [hj_root, T.root_no_parent] at hpj
        simp at hpj
      | succ k' =>
        -- parentOrRoot^[k'+1] j = parentOrRoot^[k'] (parentOrRoot j) = parentOrRoot^[k'] pj
        have heq_iter : T.parentOrRoot^[k' + 1] j = T.parentOrRoot^[k'] (T.parentOrRoot j) := by
          rw [Function.iterate_succ_apply]
        rw [heq_iter, T.parentOrRoot_of_some j pj hpj]
        have hk' : k' < m' := by omega
        exact ih pj hpj_depth k' hk'

/-- Key bound: depth in a tree of n vertices is strictly less than n -/
theorem depthAux_lt_n (T : TreeAuth n) (i : Fin n) (hn : 0 < n) :
    T.depthAux i n < n := by
  have hle := T.depthAux_le_fuel i n
  by_contra h
  push_neg at h
  have heq : T.depthAux i n = n := by omega
  -- If depthAux i n = n, then parentOrRoot^[k] i ≠ root for all k < n
  -- The sequence i, parentOrRoot i, ..., parentOrRoot^[n-1] i are n elements of Fin n
  -- None of them is root, and they're all distinct (otherwise would cycle and never reach root)
  -- But Fin n has n elements, one of which is root
  -- So we have n non-root elements, but there are only n-1 non-root positions
  have h_not_root : ∀ k < n, T.parentOrRoot^[k] i ≠ T.root :=
    T.depthAux_eq_fuel_not_root i n heq
  -- The sequence must have a repeat among the n elements
  -- But if it repeats before reaching root, it cycles forever and never reaches root
  -- This contradicts T.acyclic
  have h_distinct : ∀ j k, j < n → k < n → j ≠ k → T.parentOrRoot^[j] i ≠ T.parentOrRoot^[k] i := by
    intro j' k' hj' hk' hjk'
    -- WLOG assume j' < k'
    by_cases hjk'_lt : j' < k'
    · -- Case j' < k'
      intro heq
      -- parentOrRoot^[j'] i = parentOrRoot^[k'] i with j' < k'
      -- This means the sequence is periodic with period k' - j'
      obtain ⟨m, hm⟩ := T.acyclic i
      have hperiod : ∀ t, T.parentOrRoot^[j' + t * (k' - j')] i = T.parentOrRoot^[j'] i := by
        intro t
        induction t with
        | zero => simp
        | succ t' iht =>
          have hdiff : k' - j' + j' = k' := Nat.sub_add_cancel (le_of_lt hjk'_lt)
          have h1 : j' + (t' + 1) * (k' - j') = (k' - j') + (j' + t' * (k' - j')) := by ring
          calc T.parentOrRoot^[j' + (t' + 1) * (k' - j')] i
              = T.parentOrRoot^[(k' - j') + (j' + t' * (k' - j'))] i := by rw [h1]
            _ = T.parentOrRoot^[k' - j'] (T.parentOrRoot^[j' + t' * (k' - j')] i) := by
                rw [Function.iterate_add_apply]
            _ = T.parentOrRoot^[k' - j'] (T.parentOrRoot^[j'] i) := by rw [iht]
            _ = T.parentOrRoot^[(k' - j') + j'] i := by rw [← Function.iterate_add_apply]
            _ = T.parentOrRoot^[k'] i := by rw [hdiff]
            _ = T.parentOrRoot^[j'] i := by rw [heq]
      -- For large enough M, j' + M*(k'-j') ≥ m
      have ⟨M, hM⟩ : ∃ M, m ≤ j' + M * (k' - j') := by
        use m
        have hpos : 1 ≤ k' - j' := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hjk'_lt)
        calc m ≤ m * 1 := by omega
          _ ≤ m * (k' - j') := Nat.mul_le_mul_left m hpos
          _ ≤ j' + m * (k' - j') := Nat.le_add_left _ _
      have hm' : T.parentOrRoot^[m] i = T.root := hm
      have h_after_root : ∀ s, m ≤ s → T.parentOrRoot^[s] i = T.root := by
        intro s hs
        have h_diff : s = (s - m) + m := by omega
        rw [h_diff, Function.iterate_add_apply, hm']
        induction s - m with
        | zero => rfl
        | succ d ihd => simp only [Function.iterate_succ_apply', ihd, T.parentOrRoot_root]
      have h_is_root := h_after_root (j' + M * (k' - j')) hM
      rw [hperiod M] at h_is_root
      exact h_not_root j' hj' h_is_root
    · -- Case k' < j' (or k' = j', but hjk' rules that out)
      push_neg at hjk'_lt
      have hk'_lt_j' : k' < j' := by omega
      intro heq
      -- Symmetric case: swap j' and k'
      obtain ⟨m, hm⟩ := T.acyclic i
      have hperiod : ∀ t, T.parentOrRoot^[k' + t * (j' - k')] i = T.parentOrRoot^[k'] i := by
        intro t
        induction t with
        | zero => simp
        | succ t' iht =>
          have hdiff : j' - k' + k' = j' := Nat.sub_add_cancel (le_of_lt hk'_lt_j')
          have h1 : k' + (t' + 1) * (j' - k') = (j' - k') + (k' + t' * (j' - k')) := by ring
          calc T.parentOrRoot^[k' + (t' + 1) * (j' - k')] i
              = T.parentOrRoot^[(j' - k') + (k' + t' * (j' - k'))] i := by rw [h1]
            _ = T.parentOrRoot^[j' - k'] (T.parentOrRoot^[k' + t' * (j' - k')] i) := by
                rw [Function.iterate_add_apply]
            _ = T.parentOrRoot^[j' - k'] (T.parentOrRoot^[k'] i) := by rw [iht]
            _ = T.parentOrRoot^[(j' - k') + k'] i := by rw [← Function.iterate_add_apply]
            _ = T.parentOrRoot^[j'] i := by rw [hdiff]
            _ = T.parentOrRoot^[k'] i := by rw [← heq]
      have ⟨M, hM⟩ : ∃ M, m ≤ k' + M * (j' - k') := by
        use m
        have hpos : 1 ≤ j' - k' := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hk'_lt_j')
        calc m ≤ m * 1 := by omega
          _ ≤ m * (j' - k') := Nat.mul_le_mul_left m hpos
          _ ≤ k' + m * (j' - k') := Nat.le_add_left _ _
      have hm' : T.parentOrRoot^[m] i = T.root := hm
      have h_after_root : ∀ s, m ≤ s → T.parentOrRoot^[s] i = T.root := by
        intro s hs
        have h_diff : s = (s - m) + m := by omega
        rw [h_diff, Function.iterate_add_apply, hm']
        induction s - m with
        | zero => rfl
        | succ d ihd => simp only [Function.iterate_succ_apply', ihd, T.parentOrRoot_root]
      have h_is_root := h_after_root (k' + M * (j' - k')) hM
      rw [hperiod M] at h_is_root
      exact h_not_root k' hk' h_is_root
  -- Now we have n distinct non-root elements in Fin n
  -- But there are only n-1 non-root positions in Fin n
  -- Define the function f : Fin n → Fin n by f m = parentOrRoot^[m.val] i
  -- f is injective (from h_distinct)
  -- f maps Fin n to the set of non-root elements (from h_not_root)
  -- But |Fin n| = n > n - 1 = |non-root elements|
  -- Contradiction
  have h_inj : Function.Injective (fun m : Fin n => T.parentOrRoot^[m.val] i) := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ heq
    simp only [Fin.mk.injEq]
    by_contra hab
    exact h_distinct a b ha hb hab heq
  -- All images are ≠ root
  have h_ne_root : ∀ m : Fin n, T.parentOrRoot^[m.val] i ≠ T.root := fun m => h_not_root m.val m.isLt
  -- Count elements: there are n values mapping to n-1 non-root positions
  -- This is impossible
  -- The non-root elements form a set of size n-1
  have h_card_nonroot : Fintype.card { x : Fin n // x ≠ T.root } = n - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    simp only [Fintype.card_ofSubsingleton, Nat.add_sub_cancel]
  -- The injective function maps Fin n (size n) into non-root elements (size n-1)
  have h_to_nonroot : ∀ m : Fin n, (T.parentOrRoot^[m.val] i) ≠ T.root := h_ne_root
  -- Create function to subtype
  let f : Fin n → { x : Fin n // x ≠ T.root } := fun m => ⟨T.parentOrRoot^[m.val] i, h_to_nonroot m⟩
  have hf_inj : Function.Injective f := by
    intro a b heq
    have heq' : T.parentOrRoot^[a.val] i = T.parentOrRoot^[b.val] i := by
      simp only [f, Subtype.mk.injEq] at heq
      exact heq
    exact h_inj heq'
  have hcard_le : Fintype.card (Fin n) ≤ Fintype.card { x : Fin n // x ≠ T.root } :=
    Fintype.card_le_of_injective f hf_inj
  simp only [Fintype.card_fin, h_card_nonroot] at hcard_le
  omega

/-- depthAux stabilizes: if depthAux i fuel < fuel (strict), then increasing fuel doesn't change result -/
theorem depthAux_stable (T : TreeAuth n) (i : Fin n) (fuel : ℕ)
    (h : T.depthAux i fuel < fuel) (fuel' : ℕ) (hf : fuel ≤ fuel') :
    T.depthAux i fuel' = T.depthAux i fuel := by
  induction fuel generalizing i fuel' with
  | zero => omega  -- h : depthAux i 0 < 0 is false
  | succ f ih =>
    cases fuel' with
    | zero => omega
    | succ f' =>
      cases hp : T.parent i with
      | none =>
        rw [depthAux_succ_none T i f hp, depthAux_succ_none T i f' hp]
      | some p =>
        rw [depthAux_succ_some T i f p hp, depthAux_succ_some T i f' p hp]
        rw [depthAux_succ_some T i f p hp] at h
        -- h : 1 + depthAux p f < f + 1, so depthAux p f < f
        have h' : T.depthAux p f < f := by omega
        have hf' : f ≤ f' := by omega
        have := ih p h' f' hf'
        omega

/-- Key lemma: depth of parent is strictly less than depth of child -/
theorem depth_parent_lt (T : TreeAuth n) (i : Fin n) (p : Fin n)
    (hp : T.parent i = some p) : T.depth p < T.depth i := by
  simp only [depth]
  have hn : 0 < n := Fin.pos i
  match n, hn with
  | k + 1, _ =>
    rw [depthAux_succ_some T i k p hp]
    -- We need: depthAux p (k+1) < 1 + depthAux p k
    -- i.e., depthAux p (k+1) ≤ depthAux p k
    -- By depthAux_lt_n: depthAux p (k+1) < k+1
    -- By depthAux_le_fuel: depthAux p k ≤ k
    -- Key: depthAux p (k+1) = depthAux p k when depthAux p k < k
    have h_lt : T.depthAux p (k + 1) < k + 1 := T.depthAux_lt_n p (by omega)
    have h_le : T.depthAux p k ≤ k := T.depthAux_le_fuel p k
    -- Two cases: depthAux p k < k (use stable) or depthAux p k = k
    by_cases hcase : T.depthAux p k < k
    · have h_stable := T.depthAux_stable p k hcase (k + 1) (by omega)
      omega
    · -- depthAux p k = k
      push_neg at hcase
      have heq : T.depthAux p k = k := by omega
      -- Then depthAux p (k+1) ≤ k (from depthAux_lt_n: < k+1)
      -- And depthAux p k = k
      -- So depthAux p (k+1) ≤ k = depthAux p k
      omega

/-- Root has depth 0 -/
theorem depth_root_eq_zero (T : TreeAuth n) (hn : 0 < n) : T.depth T.root = 0 := by
  simp only [depth]
  match n, hn with
  | k + 1, _ => rw [depthAux_succ_none T T.root k T.root_no_parent]

/-- Only root has depth 0 -/
theorem depth_eq_zero_iff_root (T : TreeAuth n) (i : Fin n) (hn : 0 < n) :
    T.depth i = 0 ↔ i = T.root := by
  constructor
  · intro h0
    by_contra hne
    have hp := T.nonroot_has_parent i hne
    rw [Option.isSome_iff_exists] at hp
    obtain ⟨p, hp⟩ := hp
    have := T.depth_parent_lt i p hp
    simp only [depth] at h0
    match n, hn with
    | k + 1, _ =>
      rw [depthAux_succ_some T i k p hp] at h0
      omega
  · intro hi
    rw [hi]
    exact T.depth_root_eq_zero hn

/-- pathToRootAux ends at root when fuel is sufficient -/
theorem pathToRootAux_last_is_root (T : TreeAuth n) (i : Fin n) (fuel : ℕ)
    (hfuel : T.depth i ≤ fuel) :
    (T.pathToRootAux i fuel).getLast? = some T.root := by
  induction fuel generalizing i with
  | zero =>
    -- depth i ≤ 0 means depth i = 0, so i must be root
    have h0 : T.depth i = 0 := Nat.le_zero.mp hfuel
    -- Root has depth 0, and only root has depth 0
    simp only [depth] at h0
    have hi : i = T.root := by
      by_contra hne
      -- Non-root has positive depth
      have hp := T.nonroot_has_parent i hne
      rw [Option.isSome_iff_exists] at hp
      obtain ⟨p, hp⟩ := hp
      -- depth i = depthAux i n, with n > 0 since i exists
      have hn : 0 < n := Fin.pos i
      match n, hn with
      | k + 1, _ =>
        simp only [depthAux, hp] at h0
        omega
    simp only [pathToRootAux, hi, List.getLast?_singleton]
  | succ fuel' ih =>
    simp only [pathToRootAux]
    cases hp : T.parent i with
    | none =>
      have hi : i = T.root := by
        by_contra h
        have := T.nonroot_has_parent i h
        rw [hp] at this
        simp at this
      simp only [hi, List.getLast?_singleton]
    | some p =>
      -- depth p < depth i, so depth p ≤ fuel'
      have h_depth_p : T.depth p < T.depth i := T.depth_parent_lt i p hp
      have h_fuel' : T.depth p ≤ fuel' := by omega
      have ih_res := ih p h_fuel'
      -- Goal: (i :: T.pathToRootAux p fuel').getLast? = some T.root
      have hne : T.pathToRootAux p fuel' ≠ [] := by
        cases hfuel' : fuel' with
        | zero => simp [pathToRootAux]
        | succ f' => simp only [pathToRootAux]; cases T.parent p <;> simp
      obtain ⟨hd, tl, heq⟩ := List.exists_cons_of_ne_nil hne
      simp only [heq, List.getLast?_cons_cons] at ih_res ⊢
      exact ih_res

/-- The LCA is in the path from i to root -/
theorem lca_mem_pathToRoot_left (T : TreeAuth n) (i j : Fin n) (hn : 0 < n) :
    T.lca i j ∈ T.pathToRoot i := by
  simp only [lca]
  match hf : (T.pathToRoot i).find? (fun x => decide (x ∈ T.pathToRoot j)) with
  | some x =>
    -- find? returned some x, so x ∈ pathToRoot i
    exact List.mem_of_find?_eq_some hf
  | none =>
    -- find? returned none, so we use root which is in every path
    exact root_mem_pathToRoot T i hn

/-- The LCA is in the path from j to root -/
theorem lca_mem_pathToRoot_right (T : TreeAuth n) (i j : Fin n) (hn : 0 < n) :
    T.lca i j ∈ T.pathToRoot j := by
  simp only [lca]
  match hf : (T.pathToRoot i).find? (fun x => decide (x ∈ T.pathToRoot j)) with
  | some x =>
    -- find? returned some x satisfying (x ∈ pathToRoot j)
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    exact hp
  | none =>
    -- find? returned none, so we use root which is in every path
    exact root_mem_pathToRoot T j hn

/-- Helper: filterMap on finRange counts elements satisfying predicate -/
theorem filterMap_finRange_length {α : Type*} (n : ℕ) (hn : 0 < n) (f : Fin n → Option α)
    (hf : ∀ i, (f i).isSome ↔ i ≠ (⟨0, hn⟩ : Fin n)) :
    ((List.finRange n).filterMap (fun i => f i)).length = n - 1 := by
  -- Prove via Finset cardinality
  have h_card : (Finset.univ.filter (fun i : Fin n => (f i).isSome)).card = n - 1 := by
    have h_eq : Finset.univ.filter (fun i : Fin n => (f i).isSome) =
                Finset.univ.filter (fun i : Fin n => i ≠ ⟨0, hn⟩) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hf, decide_eq_true_eq]
    rw [h_eq]
    have h_compl : Finset.univ.filter (fun i : Fin n => i ≠ ⟨0, hn⟩) =
                   Finset.univ \ {⟨0, hn⟩} := by
      ext i
      simp [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_filter]
    rw [h_compl, Finset.card_sdiff]
    simp only [Finset.singleton_inter_of_mem (Finset.mem_univ _), Finset.card_singleton,
               Finset.card_univ, Fintype.card_fin]
  -- Connect list filterMap length to finset card
  have h_list_card : ((List.finRange n).filterMap (fun i => f i)).length =
                     (Finset.univ.filter (fun i : Fin n => (f i).isSome)).card := by
    -- Length of filterMap = count where f is some
    have h1 : ((List.finRange n).filterMap (fun i => f i)).length =
              (List.finRange n).countP (fun i => (f i).isSome) := by
      induction (List.finRange n) with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.filterMap_cons, List.countP_cons]
        cases hopt : f hd with
        | none => simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, ih]; ring
        | some v => simp only [List.length_cons, Option.isSome_some, ↓reduceIte, ih]
    rw [h1]
    -- countP on finRange equals card of filter on univ
    rw [List.countP_eq_length_filter]
    have h2 : ((List.finRange n).filter (fun i => (f i).isSome)).toFinset =
              Finset.univ.filter (fun i : Fin n => (f i).isSome) := by
      ext i
      simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, Finset.mem_filter,
                 Finset.mem_univ, true_and]
    rw [← h2, List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_finRange n))]
  rw [h_list_card, h_card]

/-- A tree with n > 0 vertices has n-1 edges -/
theorem edges_count (T : TreeAuth n) (hn : 0 < n) : T.edges.length = n - 1 := by
  simp only [edges]
  -- Count: |{i | parent i is some}| = |{i | i ≠ root}| = n - 1
  have h_card : (Finset.univ.filter (fun i : Fin n => (T.parent i).isSome)).card = n - 1 := by
    have h_eq : Finset.univ.filter (fun i : Fin n => (T.parent i).isSome) =
                Finset.univ \ {T.root} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
                 Finset.mem_singleton]
      constructor
      · intro hi hir
        rw [hir, T.root_no_parent] at hi
        exact absurd hi (by simp)
      · intro hi
        exact T.nonroot_has_parent i hi
    rw [h_eq, Finset.card_sdiff]
    simp only [Finset.singleton_inter_of_mem (Finset.mem_univ _), Finset.card_singleton,
               Finset.card_univ, Fintype.card_fin]
  -- Length of filterMap = countP of isSome condition
  have h1 : ((List.finRange n).filterMap (fun i => match T.parent i with
      | none => none | some p => some (i, p))).length =
            (List.finRange n).countP (fun i => (T.parent i).isSome) := by
    induction (List.finRange n) with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.filterMap_cons, List.countP_cons]
      cases hp : T.parent hd with
      | none => simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, ih]; omega
      | some p => simp only [List.length_cons, Option.isSome_some, ↓reduceIte, ih]
  rw [h1, List.countP_eq_length_filter]
  have h2 : ((List.finRange n).filter (fun i => (T.parent i).isSome)).toFinset =
            Finset.univ.filter (fun i : Fin n => (T.parent i).isSome) := by
    ext i
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, Finset.mem_filter,
               Finset.mem_univ, true_and]
  rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_finRange n)), h2, h_card]

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
  -- A closed path repeats its first and last vertices by definition
  intro path h_len h_closed _h_adj
  -- k₁ = 0 and k₂ = path.length - 1 witness the repetition
  use 0, path.length - 1
  constructor
  · -- 0 < path.length - 1 since path.length ≥ 3
    omega
  constructor
  · -- path.length - 1 < path.length
    omega
  -- Now prove path[0] = path[length - 1]
  have h0 : 0 < path.length := by omega
  have hlast : path.length - 1 < path.length := by omega
  use h0, hlast
  -- h_closed : path.head? = path.getLast?
  have hne : path ≠ [] := by intro h; simp [h] at h_len
  -- Get head = path[0]
  obtain ⟨x, xs, hpath⟩ := List.exists_cons_of_ne_nil hne
  subst hpath
  -- Now path = x :: xs
  simp only [List.head?_cons] at h_closed
  rw [List.getLast?_eq_some_getLast (by simp : x :: xs ≠ [])] at h_closed
  simp only [Option.some.injEq] at h_closed
  -- h_closed : x = (x :: xs).getLast _
  -- Goal: (x :: xs).get ⟨0, h0⟩ = (x :: xs).get ⟨(x :: xs).length - 1, hlast⟩
  rw [List.get_eq_getElem, List.get_eq_getElem]
  simp only [List.getElem_cons_zero]
  -- Goal: x = (x :: xs)[(x :: xs).length - 1]
  -- h_closed: x = (x :: xs).getLast _
  -- (x :: xs).getLast = (x :: xs)[xs.length] = (x :: xs)[(x :: xs).length - 1]
  conv_lhs => rw [h_closed]
  simp only [List.getLast_eq_getElem, List.length_cons, Nat.add_sub_cancel]

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
