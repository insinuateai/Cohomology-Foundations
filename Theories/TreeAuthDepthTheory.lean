/-
# TreeAuth Depth Theory

Depth-based proofs for TreeAuth acyclicity.

## Main Results

1. `depth_bounded` - Depth ≤ n - 1
2. `pathToRoot_unique_induction` - Path to root is unique
3. `no_cycle_depth_argument` - No cycles via depth
4. `simpleGraph_acyclic_of_tree` - SimpleGraph.IsAcyclic

Targets: Mathlib 4.27.0 / Lean 4.27.0

SORRIES: 2 (depth_bounded, no_cycle_via_depth_aux)
AXIOMS: 0
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

namespace TreeAuthDepthTheory

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

theorem parentOrRoot_of_parent (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) :
    T.parentOrRoot i = p := by simp [parentOrRoot, hp]

theorem parent_ne (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) : p ≠ i := by
  intro h; subst p; exact T.parent_ne_self i hp

/-! ## Depth Function -/

/-- Depth defined via Nat.find using the acyclicity condition -/
noncomputable def depth (T : TreeAuth n) (i : Fin n) : ℕ :=
  Nat.find (T.acyclic i)

/-- The depth is the number of steps to reach root -/
theorem depth_spec (T : TreeAuth n) (i : Fin n) :
    T.parentOrRoot^[T.depth i] i = T.root :=
  Nat.find_spec (T.acyclic i)

/-- Depth is minimal -/
theorem depth_min (T : TreeAuth n) (i : Fin n) (k : ℕ) (hk : T.parentOrRoot^[k] i = T.root) :
    T.depth i ≤ k :=
  Nat.find_min' (T.acyclic i) hk

theorem depth_root (T : TreeAuth n) : T.depth T.root = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply depth_min
  simp [Function.iterate_zero]

theorem parentOrRoot_iterate_succ (T : TreeAuth n) (i : Fin n) (k : ℕ) :
    T.parentOrRoot^[k + 1] i = T.parentOrRoot^[k] (T.parentOrRoot i) := by
  rw [Function.iterate_succ_apply]

/-- If parent i = some p, then depth i = depth p + 1 -/
theorem depth_parent (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) :
    T.depth p + 1 = T.depth i := by
  have hpor : T.parentOrRoot i = p := parentOrRoot_of_parent T hp
  -- depth p is the min k such that parentOrRoot^[k] p = root
  -- depth i is the min k such that parentOrRoot^[k] i = root
  -- Since parentOrRoot i = p, parentOrRoot^[k+1] i = parentOrRoot^[k] p
  -- So if parentOrRoot^[depth p] p = root, then parentOrRoot^[depth p + 1] i = root
  -- Thus depth i ≤ depth p + 1
  -- Conversely, if parentOrRoot^[depth i] i = root, need depth i ≥ 1 (since i ≠ root)
  -- and parentOrRoot^[depth i - 1] p = root, so depth p ≤ depth i - 1
  apply Nat.le_antisymm
  · -- depth p + 1 ≤ depth i
    -- First show depth i ≥ 1 (since i ≠ root because it has a parent)
    have hi_ne_root : i ≠ T.root := by
      intro h
      rw [h, T.root_no_parent] at hp
      cases hp
    have hdepth_pos : 0 < T.depth i := by
      by_contra h
      push_neg at h
      have heq : T.depth i = 0 := Nat.le_zero.mp h
      have : T.parentOrRoot^[0] i = T.root := heq ▸ depth_spec T i
      simp at this
      exact hi_ne_root this
    -- depth i ≥ 1, so depth i = (depth i - 1) + 1
    have hdec : T.depth i = (T.depth i - 1) + 1 := (Nat.sub_add_cancel hdepth_pos).symm
    -- parentOrRoot^[depth i] i = root means parentOrRoot^[depth i - 1] (parentOrRoot i) = root
    have hspec := depth_spec T i
    rw [hdec, parentOrRoot_iterate_succ, hpor] at hspec
    -- So parentOrRoot^[depth i - 1] p = root, meaning depth p ≤ depth i - 1
    have hle := depth_min T p (T.depth i - 1) hspec
    omega
  · -- depth i ≤ depth p + 1
    have hspec := depth_spec T p
    -- parentOrRoot^[depth p] p = root
    -- parentOrRoot^[depth p + 1] i = parentOrRoot^[depth p] (parentOrRoot i) = parentOrRoot^[depth p] p = root
    have h : T.parentOrRoot^[T.depth p + 1] i = T.root := by
      rw [parentOrRoot_iterate_succ, hpor, hspec]
    exact depth_min T i (T.depth p + 1) h

theorem depth_lt_of_parent (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) :
    T.depth p < T.depth i := by
  have := depth_parent T hp
  omega

/-- Depth is bounded by n (there are only n nodes) -/
theorem depth_bounded (T : TreeAuth n) (i : Fin n) : T.depth i ≤ n := by
  -- The depth is at most n because there are n nodes
  -- A path of length > n would have to revisit a node
  -- This follows from the fact that parentOrRoot maps Fin n to Fin n
  -- and eventually reaches root
  sorry -- This requires Pigeonhole principle; not critical for our goals


/-! ## Path to Root -/

/-- Path to root using well-founded recursion on depth -/
noncomputable def pathToRoot (T : TreeAuth n) (i : Fin n) : List (Fin n) :=
  match hp : T.parent i with
  | none => [i]
  | some p => i :: T.pathToRoot p
termination_by T.depth i
decreasing_by
  simp_wf
  exact depth_lt_of_parent T hp

theorem pathToRoot_root (T : TreeAuth n) : T.pathToRoot T.root = [T.root] := by
  unfold pathToRoot
  split
  · rfl
  · next p h => rw [T.root_no_parent] at h; cases h

theorem pathToRoot_cons (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) :
    T.pathToRoot i = i :: T.pathToRoot p := by
  conv_lhs => unfold pathToRoot
  split
  · next h => simp [hp] at h
  · next q hq =>
    have heq : p = q := by rw [hp] at hq; cases hq; rfl
    subst heq
    rfl

theorem pathToRoot_head (T : TreeAuth n) (i : Fin n) :
    (T.pathToRoot i).head? = some i := by
  conv_lhs => unfold pathToRoot
  split <;> simp

theorem pathToRoot_nonempty (T : TreeAuth n) (i : Fin n) :
    T.pathToRoot i ≠ [] := by
  conv_lhs => unfold pathToRoot
  split <;> simp

/-- Path to root ends at root -/
theorem pathToRoot_last_is_root (T : TreeAuth n) (i : Fin n) :
    (T.pathToRoot i).getLast? = some T.root := by
  induction' hd : T.depth i using Nat.strong_induction_on with d ih generalizing i
  cases hp : T.parent i with
  | none =>
    -- i is root
    have hi : i = T.root := by
      by_contra hne
      have := T.nonroot_has_parent i hne
      simp [hp] at this
    subst hi
    simp [pathToRoot_root]
  | some p =>
    rw [pathToRoot_cons T hp]
    have hdep : T.depth p < T.depth i := depth_lt_of_parent T hp
    have ihp := ih (T.depth p) (hd ▸ hdep) p rfl
    -- (i :: pathToRoot p).getLast? = (pathToRoot p).getLast? when pathToRoot p ≠ []
    have hne := pathToRoot_nonempty T p
    cases hp2 : T.pathToRoot p with
    | nil => exact (hne hp2).elim
    | cons x xs =>
      -- (i :: x :: xs).getLast? = (x :: xs).getLast?
      simp only [List.getLast?_cons_cons, hp2] at ihp ⊢
      exact ihp

/-- Consecutive elements in path are parent-child -/
theorem pathToRoot_consecutive (T : TreeAuth n) (i : Fin n) :
    ∀ j, j + 1 < (T.pathToRoot i).length →
      ∃ a b, (T.pathToRoot i)[j]? = some a ∧
             (T.pathToRoot i)[j + 1]? = some b ∧ T.parent a = some b := by
  induction' hd : T.depth i using Nat.strong_induction_on with d ih generalizing i
  intro j hj
  cases hp : T.parent i with
  | none =>
    -- i is root, path = [i], no j with j+1 < 1
    have hi : i = T.root := by
      by_contra hne
      have := T.nonroot_has_parent i hne
      simp [hp] at this
    subst hi
    simp [pathToRoot_root] at hj
  | some p =>
    rw [pathToRoot_cons T hp]
    -- path = i :: pathToRoot p
    cases j with
    | zero =>
      -- j = 0: first two elements are i and head of pathToRoot p
      use i, p
      simp only [List.getElem?_cons_zero]
      constructor
      · trivial
      constructor
      · have hph : (T.pathToRoot p).head? = some p := pathToRoot_head T p
        rw [List.head?_eq_getElem?] at hph
        exact hph
      · exact hp
    | succ j' =>
      -- (j' + 1) + 1 < length means j' + 1 < (pathToRoot p).length
      rw [pathToRoot_cons T hp, List.length_cons] at hj
      have hj' : j' + 1 < (T.pathToRoot p).length := by omega
      have hdep : T.depth p < T.depth i := depth_lt_of_parent T hp
      obtain ⟨a, b, ha, hb, hab⟩ := ih (T.depth p) (hd ▸ hdep) p rfl j' hj'
      use a, b
      simp only [List.getElem?_cons_succ, ha, hb, hab, and_self]

/-- Valid path: starts at i, consecutive are parent-child, ends at root -/
structure IsValidPath (T : TreeAuth n) (i : Fin n) (p : List (Fin n)) : Prop where
  nonempty : p ≠ []
  head_eq : p.head? = some i
  last_eq : p.getLast? = some T.root
  consecutive : ∀ j, j + 1 < p.length →
    ∃ a b, p[j]? = some a ∧ p[j + 1]? = some b ∧ T.parent a = some b

/-- Path to root is valid -/
theorem pathToRoot_valid (T : TreeAuth n) (i : Fin n) :
    IsValidPath T i (T.pathToRoot i) := by
  constructor
  · exact pathToRoot_nonempty T i
  · exact pathToRoot_head T i
  · -- Last is root: follows from acyclicity axiom
    -- The acyclicity condition ensures iterating parent eventually reaches root
    -- This requires induction on path construction
    exact pathToRoot_last_is_root T i
  · -- Consecutive are parent-child: by construction of pathToRootAux
    exact pathToRoot_consecutive T i

/-- Path to root is unique -/
theorem pathToRoot_unique_induction (T : TreeAuth n) (i : Fin n)
    (p : List (Fin n)) (h_valid : IsValidPath T i p) (hn : 0 < n) :
    p = T.pathToRoot i := by
  induction' hd : T.depth i using Nat.strong_induction_on with d ih generalizing i p
  cases hp : T.parent i with
  | none =>
    -- i is root (since non-root has parent)
    have hi : i = T.root := by
      by_contra hne
      have := T.nonroot_has_parent i hne
      simp [hp] at this
    subst hi
    -- pathToRoot root = [root]
    rw [pathToRoot_root]
    -- p is a valid path starting at root and ending at root
    -- By consecutive property and starting at root (no parent), p = [root]
    cases hpe : p with
    | nil => exact (h_valid.nonempty hpe).elim
    | cons x xs =>
      have hhead := h_valid.head_eq
      simp only [hpe, List.head?_cons] at hhead
      cases hhead
      -- So x = root
      cases xs with
      | nil => rfl
      | cons y ys =>
        -- If xs ≠ [], then by consecutive there's y with parent root = some y
        -- But root has no parent - contradiction
        have hcons := h_valid.consecutive 0
        simp only [hpe, List.length_cons, Nat.zero_add, Nat.succ_lt_succ_iff, Nat.zero_lt_succ,
          forall_true_left, List.getElem?_cons_zero, List.getElem?_cons_succ] at hcons
        obtain ⟨a, b, ha, hb, hab⟩ := hcons
        simp only [Option.some.injEq] at ha hb
        subst ha hb
        rw [T.root_no_parent] at hab
        cases hab
  | some parent_i =>
    rw [pathToRoot_cons T hp]
    -- p = i :: tail, and tail is valid path from parent_i to root
    cases hpe : p with
    | nil => exact (h_valid.nonempty hpe).elim
    | cons x xs =>
      have hhead := h_valid.head_eq
      simp only [hpe, List.head?_cons] at hhead
      cases hhead
      -- So x = i
      -- xs must be a valid path from parent_i to root
      -- First, show xs ≠ [] (since path ends at root ≠ i when i has parent)
      cases hxs : xs with
      | nil =>
        -- p = [i], but getLast? p = some root means i = root
        -- But i has parent, so i ≠ root - contradiction
        have hlast := h_valid.last_eq
        simp only [hpe, hxs, List.getLast?_singleton] at hlast
        cases hlast
        rw [T.root_no_parent] at hp
        cases hp
      | cons y ys =>
        -- xs = y :: ys
        -- By consecutive at j=0, parent i = some y
        have hcons0 := h_valid.consecutive 0
        simp only [hpe, List.length_cons, Nat.zero_add, Nat.succ_lt_succ_iff, Nat.zero_lt_succ,
          forall_true_left, List.getElem?_cons_zero, List.getElem?_cons_succ, hxs,
          List.getElem?_cons_zero] at hcons0
        obtain ⟨a, b, ha, hb, hab⟩ := hcons0
        simp only [Option.some.injEq] at ha hb
        subst ha hb
        -- So parent i = some y, meaning y = parent_i
        have heq : parent_i = y := by
          rw [hp] at hab
          cases hab
          rfl
        subst heq
        -- Now y is replaced by parent_i, hxs : xs = parent_i :: ys
        -- xs is a valid path from parent_i to root
        have hvalid_xs : IsValidPath T parent_i xs := by
          constructor
          · simp [hxs]
          · simp [hxs]
          · -- getLast? xs = getLast? p (since p = i :: xs has ≥2 elements)
            have : p.getLast? = xs.getLast? := by
              simp only [hpe, hxs, List.getLast?_cons_cons]
            rw [← this]
            exact h_valid.last_eq
          · -- consecutive for xs follows from consecutive for p shifted by 1
            intro j hj
            have hj' : (j + 1) + 1 < p.length := by simp [hpe, hxs] at hj ⊢; omega
            obtain ⟨a, b, ha, hb, hab⟩ := h_valid.consecutive (j + 1) hj'
            use a, b
            simp only [hpe, List.getElem?_cons_succ] at ha hb
            exact ⟨ha, hb, hab⟩
        -- By IH, xs = pathToRoot parent_i
        have hdep : T.depth parent_i < T.depth i := depth_lt_of_parent T hp
        have := ih (T.depth parent_i) (hd ▸ hdep) parent_i xs hvalid_xs rfl
        rw [← this, hxs]

/-! ## SimpleGraph -/

def toSimpleGraph (T : TreeAuth n) : SimpleGraph (Fin n) where
  Adj i j := T.parent i = some j ∨ T.parent j = some i
  symm := by intro i j h; tauto
  loopless := by intro i h; cases h with
    | inl h => exact T.parent_ne_self i h
    | inr h => exact T.parent_ne_self i h

/-- Walk in the SimpleGraph -/
structure SGWalk (T : TreeAuth n) (v : Fin n) where
  vertices : List (Fin n)
  nonempty : vertices ≠ []
  start_eq : vertices.head? = some v
  finish_eq : vertices.getLast? = some v
  len_ge_3 : vertices.length ≥ 3
  adjacent : ∀ j, j + 1 < vertices.length →
    ∃ a b, vertices[j]? = some a ∧ vertices[j + 1]? = some b ∧ T.toSimpleGraph.Adj a b
  simple : vertices.tail.Nodup

/-- Adjacency implies depth differs by exactly 1 -/
theorem adj_depth (T : TreeAuth n) {a b : Fin n} (h : T.toSimpleGraph.Adj a b) :
    T.depth a = T.depth b + 1 ∨ T.depth b = T.depth a + 1 := by
  simp only [toSimpleGraph] at h
  cases h with
  | inl hp =>
    -- parent a = some b, so depth a = depth b + 1
    left
    exact (depth_parent T hp).symm
  | inr hp =>
    -- parent b = some a, so depth b = depth a + 1
    right
    exact (depth_parent T hp).symm

/-- If a is adjacent to b and depth a ≤ depth b, then depth b = depth a + 1 -/
theorem adj_depth_le (T : TreeAuth n) {a b : Fin n} (h : T.toSimpleGraph.Adj a b)
    (hle : T.depth a ≤ T.depth b) : T.depth b = T.depth a + 1 := by
  cases adj_depth T h with
  | inl h1 => omega
  | inr h2 => exact h2

/-- No cycle via depth argument - the core lemma

Proof outline: Consider minimum depth vertex m in the cycle's tail.
Both its neighbors have depth ≥ depth(m), so by adjacency (±1 difference),
both have depth = depth(m) + 1, making them children of m.
The cycle portion connecting these children (avoiding m) provides an
alternative path between siblings, but in a tree the only path between
siblings goes through their parent. This contradicts the Nodup property.
-/
theorem no_cycle_via_depth_aux (T : TreeAuth n) (hn : 0 < n) (v : Fin n) (c : SGWalk T v) : False := by
  -- The detailed proof requires careful case analysis on cycle structure
  -- and showing that the path between children of minimum must revisit minimum.
  -- Key insight: at minimum depth vertex, both neighbors are children (depth + 1).
  -- Any path between siblings avoiding parent must visit depth ≤ parent depth,
  -- but minimum is already at minimum depth in cycle, contradiction.
  sorry

-- Consecutive elements in walk support are adjacent by walk definition
theorem walk_adjacent_extraction (T : TreeAuth n) (v : Fin n) (p : T.toSimpleGraph.Walk v v) :
    ∀ j, j + 1 < p.support.length →
      ∃ a b, p.support[j]? = some a ∧ p.support[j + 1]? = some b ∧ T.toSimpleGraph.Adj a b := by
  intro j hj
  -- j + 1 < support.length means j + 1 ≤ walk.length (since support.length = walk.length + 1)
  have hlen : p.support.length = p.length + 1 := p.length_support
  have hj_le : j ≤ p.length := by omega
  have hj1_le : j + 1 ≤ p.length := by omega
  -- Use getVert to get the vertices
  use p.getVert j, p.getVert (j + 1)
  refine ⟨?_, ?_, ?_⟩
  · -- p.support.get? j = some (p.getVert j)
    exact (p.getVert_eq_support_getElem? hj_le).symm
  · -- p.support.get? (j + 1) = some (p.getVert (j + 1))
    exact (p.getVert_eq_support_getElem? hj1_le).symm
  · -- T.toSimpleGraph.Adj (p.getVert j) (p.getVert (j + 1))
    exact p.adj_getVert_succ (by omega : j < p.length)

/-- No cycle via depth argument -/
theorem no_cycle_depth_argument (T : TreeAuth n) (hn : 0 < n) (v : Fin n)
    (c : SGWalk T v) : False := by
  -- Core argument: Consider minimum depth vertex m in cycle.
  -- Both neighbors have depth = depth(m) + 1 (both are children).
  -- But path between children must go through m (tree property).
  -- This contradicts simple cycle (would revisit m).
  exact no_cycle_via_depth_aux T hn v c

/-- SimpleGraph is acyclic -/
theorem simpleGraph_acyclic_of_tree (T : TreeAuth n) (hn : 0 < n) : T.toSimpleGraph.IsAcyclic := by
  intro v p hp
  -- Convert p to SGWalk
  have hne := SimpleGraph.Walk.support_ne_nil p
  have c : SGWalk T v := {
    vertices := p.support
    nonempty := hne
    start_eq := by
      have h := SimpleGraph.Walk.head_support p
      simp only [List.head?_eq_some_head hne, h]
    finish_eq := by
      have h := SimpleGraph.Walk.getLast_support p
      simp only [List.getLast?_eq_some_getLast hne, h]
    len_ge_3 := by
      have := hp.three_le_length
      simp only [SimpleGraph.Walk.length_support]
      omega
    adjacent := walk_adjacent_extraction T v p
    simple := hp.support_nodup
  }
  exact no_cycle_depth_argument T hn v c

end TreeAuth

#check TreeAuth.depth_bounded
#check TreeAuth.pathToRoot_unique_induction
#check TreeAuth.no_cycle_depth_argument
#check TreeAuth.simpleGraph_acyclic_of_tree

end TreeAuthDepthTheory
