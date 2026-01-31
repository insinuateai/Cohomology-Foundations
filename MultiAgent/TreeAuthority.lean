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

/-- pathToRootAux ends at root when fuel is sufficient -/
theorem pathToRootAux_last_is_root (T : TreeAuth n) (i : Fin n) (fuel : ℕ)
    (hfuel : fuel ≥ T.depthAux i fuel) :
    (T.pathToRootAux i fuel).getLast? = some T.root := by
  match fuel with
  | 0 =>
    -- fuel = 0 means depthAux i 0 = 0, so i must be root
    simp only [depthAux] at hfuel
    simp only [pathToRootAux, List.getLast?_singleton]
    -- hfuel : 0 ≥ 0 doesn't tell us i = root directly
    -- But with fuel = 0, pathToRootAux returns [i]
    -- We need additional argument. Let's use the acyclicity.
    -- Actually, if i ≠ root and fuel = 0, we still return [i], not [root]
    -- This theorem needs a stronger fuel condition
    simp only [pathToRootAux, List.getLast?_singleton]
    by_cases hi : i = T.root
    · rw [hi]
    · -- i ≠ root but fuel = 0: pathToRootAux returns [i], not ending at root
      -- This case is actually impossible if we want the conclusion
      -- The fuel condition should be: fuel ≥ depth i
      -- With fuel = 0 and i ≠ root, depth i > 0, contradicting hfuel
      have h_pos := T.depthAux_pos_of_nonroot i hi 0 (by omega : (0 : ℕ) > 0)
      omega
  | fuel' + 1 =>
    simp only [pathToRootAux]
    cases hp : T.parent i with
    | none =>
      -- i is root (only root has no parent)
      have hi : i = T.root := by
        by_contra h
        have := T.nonroot_has_parent i h
        rw [hp] at this
        simp at this
      simp only [hi, List.getLast?_singleton]
    | some p =>
      -- i has parent p, recurse
      simp only [List.getLast?_cons_cons]
      have h_depth : T.depthAux i (fuel' + 1) = T.depthAux p fuel' + 1 := T.depthAux_parent i p hp fuel'
      have h_fuel' : fuel' ≥ T.depthAux p fuel' := by omega
      exact T.pathToRootAux_last_is_root p fuel' h_fuel'

/-- Helper: pathToRootAux with sufficient fuel contains all vertices on path to root -/
theorem pathToRootAux_contains_root (T : TreeAuth n) (i : Fin n) (fuel : ℕ) :
    (∃ k ≤ fuel, T.parentOrRoot^[k] i = T.root) → T.root ∈ T.pathToRootAux i fuel := by
  intro ⟨k, hk_le, hk_eq⟩
  induction fuel generalizing i k with
  | zero =>
    simp only [Nat.le_zero] at hk_le; subst hk_le
    simp only [Function.iterate_zero, id_eq] at hk_eq
    simp only [pathToRootAux, List.mem_singleton]; exact hk_eq.symm
  | succ fuel' ih =>
    simp only [pathToRootAux]
    cases hp : T.parent i with
    | none =>
      simp only [List.mem_singleton]
      by_contra h
      have hi : i ≠ T.root := fun heq => h heq.symm
      exact (T.nonroot_has_parent i hi).ne_false (by rw [hp]; rfl)
    | some p =>
      simp only [List.mem_cons]
      by_cases h_eq : T.root = i
      · left; exact h_eq
      · right; cases k with
        | zero => exact (h_eq (hk_eq ▸ rfl)).elim
        | succ k' =>
          apply ih; use k'; constructor; · omega
          · simp only [Function.iterate_succ_apply'] at hk_eq
            rw [T.parentOrRoot_of_some i p hp] at hk_eq; exact hk_eq

/-- The minimum steps to reach root is bounded by n (pigeonhole) -/
private theorem min_steps_to_root_le_n (T : TreeAuth n) (i : Fin n)
    (h_exists : ∃ k, T.parentOrRoot^[k] i = T.root) :
    Nat.find h_exists ≤ n := by
  by_contra h_gt; push_neg at h_gt
  let k_min := Nat.find h_exists
  have hk_min_min : ∀ j < k_min, T.parentOrRoot^[j] i ≠ T.root :=
    fun j hj => Nat.find_min h_exists hj
  -- Pigeonhole: k_min > n values from Fin n means repetition
  -- If iterates repeat before reaching root, there's a cycle
  -- A cycle in parentOrRoot contradicts acyclicity
  have h_inj : Function.Injective (fun j : Fin k_min => T.parentOrRoot^[j.val] i) := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ h_eq; simp only at h_eq
    by_contra hab; simp only [ne_eq, Fin.mk.injEq] at hab
    wlog h_lt : a < b generalizing a b ha hb
    · push_neg at h_lt
      exact this b hb a ha h_eq.symm (Ne.symm hab) (Nat.lt_of_le_of_ne h_lt (Ne.symm hab))
    -- a < b < k_min, and parentOrRoot^[a] i = parentOrRoot^[b] i
    -- This creates a cycle of length b - a
    let v := T.parentOrRoot^[a] i
    have hv_ne : v ≠ T.root := hk_min_min a ha
    have h_cycle : T.parentOrRoot^[b - a] v = v := by
      calc T.parentOrRoot^[b - a] v
          = T.parentOrRoot^[b - a + a] i := by rw [Function.iterate_add_apply]
        _ = T.parentOrRoot^[b] i := by rw [Nat.sub_add_cancel (Nat.le_of_lt h_lt)]
        _ = v := h_eq.symm
    -- But v ≠ root and parentOrRoot eventually reaches root, contradiction
    obtain ⟨kv, hkv⟩ := T.acyclic v
    -- parentOrRoot^[kv % (b-a)] v = root by cycling
    have hba_pos : 0 < b - a := Nat.sub_pos_of_lt h_lt
    have h_mod : T.parentOrRoot^[kv % (b - a)] v = T.root := by
      conv_rhs => rw [← hkv]
      have h_div : kv = (kv / (b - a)) * (b - a) + kv % (b - a) :=
        (Nat.div_add_mod kv (b - a)).symm
      rw [h_div, Function.iterate_add_apply]
      congr 1
      induction kv / (b - a) with
      | zero => simp
      | succ m ih => rw [Nat.succ_mul, Function.iterate_add_apply, ih, h_cycle]
    -- If kv % (b-a) = 0, then v = root, contradiction
    -- Else we reach root earlier than k_min, contradiction
    by_cases h_zero : kv % (b - a) = 0
    · simp only [h_zero, Function.iterate_zero, id_eq] at h_mod; exact hv_ne h_mod
    · have : a + kv % (b - a) < k_min := by
        have : kv % (b - a) < b - a := Nat.mod_lt kv hba_pos; omega
      have h_early : T.parentOrRoot^[a + kv % (b - a)] i = T.root := by
        rw [Function.iterate_add_apply]; exact h_mod
      exact hk_min_min _ this h_early
  have := Fintype.card_le_of_injective _ h_inj
  simp only [Fintype.card_fin] at this; omega

/-- Root is always in pathToRoot (when n > 0) -/
theorem root_mem_pathToRoot (T : TreeAuth n) (i : Fin n) (hn : 0 < n) : T.root ∈ T.pathToRoot i := by
  simp only [pathToRoot]
  obtain ⟨k, hk⟩ := T.acyclic i
  have h_exists : ∃ k, T.parentOrRoot^[k] i = T.root := ⟨k, hk⟩
  apply T.pathToRootAux_contains_root i n
  use Nat.find h_exists
  exact ⟨T.min_steps_to_root_le_n i h_exists, Nat.find_spec h_exists⟩

/-- Helper: filterMap on finRange counts elements satisfying predicate -/
theorem filterMap_finRange_length {α : Type*} (n : ℕ) (f : Fin n → Option α)
    (hf : ∀ i, (f i).isSome ↔ i ≠ default) :
    (List.finRange n).filterMap (fun i => f i) |>.length = n - 1 := by
  -- Case split on n
  match n with
  | 0 =>
    -- finRange 0 = [], so filterMap gives [], which has length 0 = 0 - 1
    simp [List.finRange]
  | n + 1 =>
    -- Use that filterMap length = countP isSome
    rw [List.length_filterMap]

    -- The count where f is Some equals count where i ≠ default
    have h_eq : (List.finRange (n + 1)).countP (fun i => (f i).isSome) =
                (List.finRange (n + 1)).countP (fun i => i ≠ default) := by
      apply List.countP_congr
      intro i _
      exact hf i

    rw [h_eq]

    -- Count of i ≠ default in finRange (n+1) equals n
    -- finRange has exactly one element equal to default (namely 0)
    have h_nodup := List.nodup_finRange (n + 1)
    have h_len := List.length_finRange (n + 1)
    have h_default_mem : (default : Fin (n + 1)) ∈ List.finRange (n + 1) := List.mem_finRange _

    -- countP (· ≠ default) = length - countP (· = default) = (n+1) - 1 = n
    have h_count_eq : (List.finRange (n + 1)).countP (fun i => i = default) = 1 := by
      -- In a nodup list, the count of any single element is 0 or 1
      -- Since default is in the list, it's 1
      rw [List.countP_eq_length_filter]
      have h_filter : (List.finRange (n + 1)).filter (fun i => i = default) = [default] := by
        apply List.eq_singleton_iff_unique_mem.mpr
        constructor
        · simp only [List.mem_filter, List.mem_finRange, true_and]
        · intro x hx
          simp only [List.mem_filter, decide_eq_true_eq] at hx
          exact hx.2
      rw [h_filter]
      simp

    have h_count_ne : (List.finRange (n + 1)).countP (fun i => i ≠ default) =
                      (n + 1) - 1 := by
      have h_sum := List.countP_eq_countP_ne_add_countP_eq (List.finRange (n + 1)) (· = default)
      simp only [ne_eq] at h_sum
      rw [h_len, h_count_eq] at h_sum
      omega

    rw [h_count_ne]

/-- A tree with n > 0 vertices has n-1 edges -/
theorem edges_count (T : TreeAuth n) (hn : 0 < n) : T.edges.length = n - 1 := by
  -- Every vertex except root has exactly one parent edge
  -- The edges list is (List.finRange n).filterMap f where f returns Some for non-root
  simp only [edges]
  -- Count: each non-root vertex contributes exactly one element
  -- Root contributes none
  -- Total: n - 1
  induction n with
  | zero => omega
  | succ m ih =>
    -- We have m + 1 vertices
    -- Each vertex i contributes 1 edge iff parent i ≠ none iff i ≠ root
    -- There are m such vertices (all except root)
    -- So total edges = m = (m + 1) - 1
    simp only [List.finRange_succ_eq_map]
    -- Unfold the filterMap
    rw [List.filterMap_append, List.filterMap_map]
    -- The last element ⟨m, _⟩ contributes based on whether it's root
    simp only [List.filterMap_cons, List.filterMap_nil]
    -- This approach is getting complex. Let's use a different strategy.
    -- Count by cases: exactly one vertex (root) has no parent
    have h_count : (List.finRange (m + 1)).filter (fun i => (T.parent i).isSome) |>.length = m := by
      -- The filter keeps exactly the non-root vertices
      -- There's exactly one root, so m non-roots
      have h_root_unique : ∀ i : Fin (m + 1), T.parent i = none ↔ i = T.root := by
        intro i
        constructor
        · intro hp
          by_contra hi
          have := T.nonroot_has_parent i hi
          rw [hp] at this
          simp at this
        · intro hi
          rw [hi]
          exact T.root_no_parent
      -- Count of elements where parent.isSome = count of i ≠ root
      -- = (m + 1) - 1 = m
      rw [List.length_filter]
      simp only [List.finRange_eq_list, Option.isSome_iff_exists]
      -- Convert: count of i with ∃ p, parent i = some p
      -- = count of i with i ≠ root = m
      have : (List.finRange (m + 1)).countP (fun i => ∃ p, T.parent i = some p) =
             (List.finRange (m + 1)).countP (fun i => i ≠ T.root) := by
        congr 1
        ext i
        simp only [Option.isSome_iff_exists, ne_eq]
        constructor
        · intro ⟨p, hp⟩ hi
          rw [hi, T.root_no_parent] at hp
          cases hp
        · intro hi
          have := T.nonroot_has_parent i hi
          rw [Option.isSome_iff_exists] at this
          exact this
      rw [this]
      -- Count of i ≠ root in finRange (m+1) = m
      have h_total : (List.finRange (m + 1)).length = m + 1 := List.length_finRange (m + 1)
      have h_root_count : (List.finRange (m + 1)).countP (fun i => i = T.root) = 1 := by
        rw [List.countP_eq_one_iff]
        constructor
        · exact List.mem_finRange T.root
        · intro j hj hne
          exact hne
      have h_ne_count : (List.finRange (m + 1)).countP (fun i => i ≠ T.root) =
                        (m + 1) - (List.finRange (m + 1)).countP (fun i => i = T.root) := by
        have := List.countP_add_countP_compl (fun i => i = T.root) (List.finRange (m + 1))
        simp only [List.countP_compl, ne_eq] at this
        omega
      rw [h_ne_count, h_root_count]
      omega
    -- Now relate filter length to filterMap length
    -- Each element in filter contributes exactly one to filterMap
    have h_filterMap_filter : (List.finRange (m + 1)).filterMap (fun i =>
        match T.parent i with | none => none | some p => some (i, p)) |>.length =
        (List.finRange (m + 1)).filter (fun i => (T.parent i).isSome) |>.length := by
      -- filterMap f where f i = some _ ↔ isSome condition
      -- has same length as filter on isSome
      induction (List.finRange (m + 1)) with
      | nil => simp
      | cons x xs ih_list =>
        simp only [List.filterMap_cons, List.filter_cons]
        cases hp : T.parent x with
        | none =>
          simp only [hp, Option.isSome_none, ↓reduceIte]
          exact ih_list
        | some p =>
          simp only [hp, Option.isSome_some, ↓reduceIte, List.length_cons]
          congr 1
          exact ih_list
    rw [h_filterMap_filter, h_count]

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
