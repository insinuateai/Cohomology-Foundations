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
  -- A path of length > n would have to revisit a node by pigeonhole
  by_contra h
  push_neg at h
  -- depth i > n means depth i ≥ n + 1
  have hn1 : n + 1 ≤ T.depth i := Nat.succ_le_of_lt h
  -- Consider the function g : Fin (n + 1) → Fin n, g(m) = parentOrRoot^[m] i
  let g : Fin (n + 1) → Fin n := fun m => T.parentOrRoot^[m.val] i
  have hcard : Fintype.card (Fin (n + 1)) > Fintype.card (Fin n) := by simp
  -- By pigeonhole, ∃ a ≠ b with g(a) = g(b)
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
  -- WLOG a < b
  wlog hab_lt : a < b generalizing a b
  · have hle : b ≤ a := Nat.le_of_not_lt hab_lt
    exact this b a hab.symm heq.symm (hab.symm.lt_of_le hle)
  -- Let j = parentOrRoot^[a] i = parentOrRoot^[b] i
  let j := g a
  have hja : T.parentOrRoot^[a.val] i = j := rfl
  have hjb : T.parentOrRoot^[b.val] i = j := heq.symm
  -- parentOrRoot^[b - a] j = j (j is in a cycle under parentOrRoot)
  have hcycle : T.parentOrRoot^[b.val - a.val] j = j := by
    calc T.parentOrRoot^[b.val - a.val] j
        = T.parentOrRoot^[b.val - a.val] (T.parentOrRoot^[a.val] i) := by rw [hja]
      _ = T.parentOrRoot^[(b.val - a.val) + a.val] i := by rw [Function.iterate_add_apply]
      _ = T.parentOrRoot^[b.val] i := by congr 1; omega
      _ = j := hjb
  -- d = b - a > 0
  have hd_pos : 0 < b.val - a.val := Nat.sub_pos_of_lt hab_lt
  -- Show j must be root (otherwise contradicts acyclicity)
  have hj_eq_root : j = T.root := by
    by_contra hne
    -- By acyclicity, ∃ k, parentOrRoot^[k] j = root
    obtain ⟨k, hk⟩ := T.acyclic j
    let d := b.val - a.val
    let r := k % d
    have hr_lt : r < d := Nat.mod_lt k hd_pos
    -- Show parentOrRoot^[m * d] j = j for all m (periodicity)
    have hperiod : ∀ m, T.parentOrRoot^[m * d] j = j := by
      intro m
      induction m with
      | zero => simp
      | succ m' ih =>
        have hsum : (m' + 1) * d = d + m' * d := by ring
        calc T.parentOrRoot^[(m' + 1) * d] j
            = T.parentOrRoot^[d + m' * d] j := by rw [hsum]
          _ = T.parentOrRoot^[d] (T.parentOrRoot^[m' * d] j) := by
              rw [Function.iterate_add_apply]
          _ = T.parentOrRoot^[d] j := by rw [ih]
          _ = j := hcycle
    -- parentOrRoot^[k] j = parentOrRoot^[r] j by periodicity
    have hk_eq_r : T.parentOrRoot^[k] j = T.parentOrRoot^[r] j := by
      have hperiod_inst : T.parentOrRoot^[(k / d) * d] j = j := hperiod (k / d)
      have hcomm : ∀ a b x, T.parentOrRoot^[a] (T.parentOrRoot^[b] x) =
                            T.parentOrRoot^[b] (T.parentOrRoot^[a] x) := by
        intros a b x
        simp only [← Function.iterate_add_apply, add_comm]
      calc T.parentOrRoot^[k] j
          = T.parentOrRoot^[(k / d) * d + k % d] j := by rw [Nat.div_add_mod']
        _ = T.parentOrRoot^[(k / d) * d] (T.parentOrRoot^[k % d] j) := by
            rw [Function.iterate_add_apply]
        _ = T.parentOrRoot^[k % d] (T.parentOrRoot^[(k / d) * d] j) := hcomm _ _ _
        _ = T.parentOrRoot^[k % d] j := by rw [hperiod_inst]
        _ = T.parentOrRoot^[r] j := rfl
    -- So root = parentOrRoot^[r] j
    have hr_root : T.parentOrRoot^[r] j = T.root := hk_eq_r ▸ hk
    -- parentOrRoot^[d] j = parentOrRoot^[d - r] root = root
    have hd_root : T.parentOrRoot^[d] j = T.root := by
      have hsplit : d = (d - r) + r := by omega
      have hiter_root : ∀ m, T.parentOrRoot^[m] T.root = T.root := by
        intro m
        induction m with
        | zero => simp
        | succ m' ih => rw [Function.iterate_succ_apply', ih, parentOrRoot_root]
      have hd_eq : d = (d - r) + r := by omega
      have h1 : T.parentOrRoot^[d] j = T.parentOrRoot^[(d - r) + r] j := by congr 1
      have h2 : T.parentOrRoot^[(d - r) + r] j = T.parentOrRoot^[d - r] (T.parentOrRoot^[r] j) := by
        rw [Function.iterate_add_apply]
      have h3 : T.parentOrRoot^[d - r] (T.parentOrRoot^[r] j) = T.parentOrRoot^[d - r] T.root := by
        rw [hr_root]
      calc T.parentOrRoot^[d] j
          = T.parentOrRoot^[(d - r) + r] j := h1
        _ = T.parentOrRoot^[d - r] (T.parentOrRoot^[r] j) := h2
        _ = T.parentOrRoot^[d - r] T.root := h3
        _ = T.root := hiter_root (d - r)
    -- But parentOrRoot^[d] j = j ≠ root, contradiction
    rw [hcycle] at hd_root
    exact hne hd_root
  -- j = root, so depth i ≤ a < n + 1 ≤ depth i, contradiction
  have hdepth_le : T.depth i ≤ a.val := by
    apply depth_min
    rw [hj_eq_root] at hja
    exact hja
  have ha_lt : a.val < n + 1 := a.isLt
  omega


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

/-- Walk in the SimpleGraph (circuit-like: at least 4 vertices for 3+ edges) -/
structure SGWalk (T : TreeAuth n) (v : Fin n) where
  vertices : List (Fin n)
  nonempty : vertices ≠ []
  start_eq : vertices.head? = some v
  finish_eq : vertices.getLast? = some v
  len_ge_4 : vertices.length ≥ 4  -- Changed from ≥ 3 to match IsCircuit (3+ edges)
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

/-- From adjacency and depth, determine parent relationship -/
theorem parent_of_adj_depth (T : TreeAuth n) {a b : Fin n}
    (hadj : T.toSimpleGraph.Adj a b) (hdepth : T.depth a = T.depth b + 1) :
    T.parent a = some b := by
  simp only [toSimpleGraph] at hadj
  cases hadj with
  | inl h => exact h
  | inr h => have := (depth_parent T h).symm; omega

/-- If x ∈ pathToRoot y, then depth x ≤ depth y -/
theorem mem_pathToRoot_depth_le (T : TreeAuth n) {x y : Fin n}
    (hmem : x ∈ T.pathToRoot y) : T.depth x ≤ T.depth y := by
  -- Strong induction on depth of y
  have : ∀ d, ∀ y : Fin n, T.depth y = d → x ∈ T.pathToRoot y → T.depth x ≤ T.depth y := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro y hdy hmem_y
      cases hp : T.parent y with
      | none =>
        -- y is root
        have hy_root : y = T.root := by
          by_contra hne; have := T.nonroot_has_parent y hne; simp [hp] at this
        subst hy_root
        rw [pathToRoot_root] at hmem_y
        simp at hmem_y
        rw [hmem_y]
      | some p =>
        rw [pathToRoot_cons T hp, List.mem_cons] at hmem_y
        cases hmem_y with
        | inl heq => rw [heq]
        | inr hmem_p =>
          have hdep_p : T.depth p < T.depth y := depth_lt_of_parent T hp
          have hle_p := ih (T.depth p) (hdy ▸ hdep_p) p rfl hmem_p
          omega
  exact this (T.depth y) y rfl hmem

/-- Sibling cannot be ancestor: if a and b are both children of c, then a ∉ pathToRoot b -/
theorem sibling_not_in_path (T : TreeAuth n) {a b c : Fin n}
    (ha : T.parent a = some c) (hb : T.parent b = some c) (hab : a ≠ b) :
    a ∉ T.pathToRoot b := by
  intro hmem
  have ha_depth : T.depth a = T.depth c + 1 := (depth_parent T ha).symm
  have hb_depth : T.depth b = T.depth c + 1 := (depth_parent T hb).symm
  -- pathToRoot b = b :: pathToRoot c (since parent b = some c)
  have hpath : T.pathToRoot b = b :: T.pathToRoot c := pathToRoot_cons T hb
  rw [hpath, List.mem_cons] at hmem
  cases hmem with
  | inl h => exact hab h
  | inr h =>
    -- a ∈ pathToRoot c means depth a ≤ depth c
    -- But depth a = depth c + 1 > depth c - contradiction
    have hle := T.mem_pathToRoot_depth_le h
    omega

/-- Helper: walk from child to non-descendant must go through parent -/
theorem walk_from_child_passes_parent (T : TreeAuth n) {x a b : Fin n}
    (hxa : T.parent x = some a) (hdepth : T.depth x > T.depth b)
    (w : T.toSimpleGraph.Walk x b) : a ∈ w.support := by
  match w with
  | .nil =>
    -- x = b contradicts depth(x) > depth(b)
    simp only [gt_iff_lt, lt_self_iff_false] at hdepth
  | @SimpleGraph.Walk.cons _ _ _ y _ hadj w' =>
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
    -- hadj : Adj x y, w' : Walk y b
    -- Goal: a = x ∨ a ∈ w'.support
    simp only [toSimpleGraph] at hadj
    cases hadj with
    | inl hxy =>
      -- parent x = some y, combined with parent x = some a gives y = a
      rw [hxa] at hxy; cases hxy
      -- Now y = a, and w' : Walk a b, so a ∈ w'.support
      right; exact SimpleGraph.Walk.start_mem_support w'
    | inr hyx =>
      -- parent y = some x, so y is child of x
      -- depth(y) = depth(x) + 1 > depth(b), so y is also deeper than b
      have hdepth_y : T.depth y = T.depth x + 1 := (depth_parent T hyx).symm
      have hdepth' : T.depth y > T.depth b := by omega
      -- By recursion, walk from y to b passes through x
      have hx_mem : x ∈ w'.support := walk_from_child_passes_parent T hyx hdepth' w'
      -- Split w' at x and show a ∈ suffix
      obtain ⟨w1, w2, hw'_eq⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hx_mem
      -- w2 is a walk from x to b, apply recursively
      have hdepth2 : T.depth x > T.depth b := by omega
      have ha_in_w2 : a ∈ w2.support := walk_from_child_passes_parent T hxa hdepth2 w2
      -- a ∈ w2.support ⊆ w'.support (via the tail of w2.support)
      right
      rw [hw'_eq, SimpleGraph.Walk.support_append]
      -- w'.support = w1.support ++ w2.support.tail
      -- a ∈ w2.support, and w2 starts at x, so a ∈ x :: w2.support.tail
      have hax : a ≠ x := by intro h; rw [h] at hxa; exact T.parent_ne_self x hxa
      have ha_tail : a ∈ w2.support.tail := by
        rw [SimpleGraph.Walk.support_eq_cons w2, List.mem_cons] at ha_in_w2
        rcases ha_in_w2 with rfl | h
        · exact (hax rfl).elim
        · exact h
      exact List.mem_append_right _ ha_tail
termination_by w.length

/-- Key lemma: In a tree, any walk between siblings must pass through their parent -/
theorem walk_between_siblings_passes_parent (T : TreeAuth n) {a b c : Fin n}
    (ha : T.parent a = some c) (hb : T.parent b = some c) (hab : a ≠ b)
    (w : T.toSimpleGraph.Walk a b) : c ∈ w.support := by
  match w with
  | .nil => exact (hab rfl).elim
  | @SimpleGraph.Walk.cons _ _ _ x _ hadj w' =>
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
    -- hadj : Adj a x, w' : Walk x b
    -- Goal: c = a ∨ c ∈ w'.support
    simp only [toSimpleGraph] at hadj
    cases hadj with
    | inl hax =>
      -- parent a = some x, but parent a = some c, so x = c
      rw [ha] at hax; cases hax
      -- Now x = c, and c ∈ w'.support (it's the first element)
      right; exact SimpleGraph.Walk.start_mem_support w'
    | inr hxa =>
      -- parent x = some a, so x is child of a (grandchild of c)
      by_cases hxc : x = c
      · right; rw [← hxc]; exact SimpleGraph.Walk.start_mem_support w'
      · right
        -- depth(x) = depth(a) + 1 = depth(c) + 2 > depth(c) + 1 = depth(b)
        have hdepth_x : T.depth x = T.depth a + 1 := (depth_parent T hxa).symm
        have hdepth_a : T.depth a = T.depth c + 1 := (depth_parent T ha).symm
        have hdepth_b : T.depth b = T.depth c + 1 := (depth_parent T hb).symm
        have hdepth : T.depth x > T.depth b := by omega
        -- Walk from x to b must pass through a (x's parent)
        have ha_mem : a ∈ w'.support := walk_from_child_passes_parent T hxa hdepth w'
        -- Split w' at a
        obtain ⟨w1, w2, hw'_eq⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp ha_mem
        -- w2 is a walk from a to b, apply recursively
        have hc_in_w2 : c ∈ w2.support := walk_between_siblings_passes_parent T ha hb hab w2
        -- c ∈ w2.support ⊆ w'.support (via the tail of w2.support)
        rw [hw'_eq, SimpleGraph.Walk.support_append]
        -- w'.support = w1.support ++ w2.support.tail
        -- c ∈ w2.support, and w2 starts at a
        have hca : c ≠ a := by intro h; rw [h] at ha; exact T.parent_ne_self a ha
        have hc_tail : c ∈ w2.support.tail := by
          rw [SimpleGraph.Walk.support_eq_cons w2, List.mem_cons] at hc_in_w2
          rcases hc_in_w2 with rfl | h
          · exact (hca rfl).elim
          · exact h
        exact List.mem_append_right _ hc_tail
termination_by w.length

/-- Build a Walk from a list where consecutive elements are adjacent -/
def walkOfList (T : TreeAuth n) (vs : List (Fin n)) (hne : vs ≠ [])
    (hadj : ∀ i, (hi : i + 1 < vs.length) →
      T.toSimpleGraph.Adj (vs[i]'(Nat.lt_of_succ_lt hi)) (vs[i + 1]'hi)) :
    T.toSimpleGraph.Walk (vs.head hne) (vs.getLast hne) :=
  match vs, hne with
  | [_], _ => .nil
  | a :: b :: rest, _ =>
    let h1 : 0 + 1 < (a :: b :: rest).length := by simp
    have hadj0 : T.toSimpleGraph.Adj a b := hadj 0 h1
    have hne' : (b :: rest) ≠ [] := List.cons_ne_nil _ _
    have hadj' : ∀ i, (hi : i + 1 < (b :: rest).length) →
        T.toSimpleGraph.Adj ((b :: rest)[i]'(Nat.lt_of_succ_lt hi)) ((b :: rest)[i + 1]'hi) := by
      intro i hi
      have h2 : (i + 1) + 1 < (a :: b :: rest).length := by simp at hi ⊢; omega
      exact hadj (i + 1) h2
    .cons hadj0 (walkOfList T (b :: rest) hne' hadj')
termination_by vs.length

/-- The support of walkOfList contains exactly the input list -/
theorem walkOfList_support (T : TreeAuth n) (vs : List (Fin n)) (hne : vs ≠ [])
    (hadj : ∀ i, (hi : i + 1 < vs.length) →
      T.toSimpleGraph.Adj (vs[i]'(Nat.lt_of_succ_lt hi)) (vs[i + 1]'hi)) :
    (walkOfList T vs hne hadj).support = vs := by
  match vs, hne with
  | [x], _ => simp [walkOfList, SimpleGraph.Walk.support_nil]
  | a :: b :: rest, _ =>
    simp only [walkOfList, SimpleGraph.Walk.support_cons]
    have hne' : (b :: rest) ≠ [] := List.cons_ne_nil _ _
    have hadj' : ∀ i, (hi : i + 1 < (b :: rest).length) →
        T.toSimpleGraph.Adj ((b :: rest)[i]'(Nat.lt_of_succ_lt hi)) ((b :: rest)[i + 1]'hi) := by
      intro i hi
      have h2 : (i + 1) + 1 < (a :: b :: rest).length := by simp at hi ⊢; omega
      exact hadj (i + 1) h2
    have ih := walkOfList_support T (b :: rest) hne' hadj'
    exact congrArg (a :: ·) ih
termination_by vs.length

/-- No cycle via depth argument - the core lemma

Proof outline: Consider minimum depth vertex m in the cycle's tail.
Both its neighbors have depth ≥ depth(m), so by adjacency (±1 difference),
both have depth = depth(m) + 1, making them children of m.
The cycle portion connecting these children (avoiding m) provides an
alternative path between siblings, but in a tree the only path between
siblings goes through their parent. This contradicts the Nodup property.
-/
theorem no_cycle_via_depth_aux (T : TreeAuth n) (hn : 0 < n) (v : Fin n) (c : SGWalk T v) : False := by
  -- Key insight: at minimum depth vertex m in cycle, both neighbors are children.
  -- With length ≥ 4, we have two distinct neighbors that are both children of m.
  -- In a tree, distinct children can't be connected without going through parent.
  -- Get cycle structure
  have hlen : c.vertices.length ≥ 4 := c.len_ge_4
  -- The tail has at least 3 elements (cycle length ≥ 4 means ≥ 4 vertices)
  have htail_len : c.vertices.tail.length ≥ 3 := by
    cases hv : c.vertices with
    | nil => simp [hv] at hlen
    | cons x xs =>
      simp only [List.tail_cons]
      simp only [hv, List.length_cons] at hlen
      omega
  have htail_ne : c.vertices.tail ≠ [] := by
    intro h
    have : c.vertices.tail.length = 0 := by simp [h]
    omega
  -- Convert tail to a Finset to find minimum depth using Finset API
  let tailList := c.vertices.tail
  let tailSet : Finset (Fin n) := tailList.toFinset
  have htailSet_ne : tailSet.Nonempty := by
    simp only [Finset.Nonempty, List.mem_toFinset, tailSet]
    cases htl : tailList with
    | nil => exact (htail_ne htl).elim
    | cons x xs => exact ⟨x, .head xs⟩
  -- Find minimum depth vertex using Finset.argmin
  have hdepth_min := Finset.exists_min_image tailSet (T.depth ·) htailSet_ne
  obtain ⟨m, hm_mem, hm_min⟩ := hdepth_min
  -- m is in the tail
  have hm_in_tail : m ∈ tailList := List.mem_toFinset.mp hm_mem
  -- m has minimum depth among all tail vertices
  have hmin_le : ∀ x ∈ tailList, T.depth m ≤ T.depth x := by
    intro x hx
    exact hm_min x (List.mem_toFinset.mpr hx)
  -- Now we use the key structural argument:
  -- In a tree-derived graph, adjacent vertices have depth differing by exactly 1.
  -- If m is at minimum depth, its neighbors have depth ≥ min_depth.
  -- Combined with |depth diff| = 1, neighbors have depth = min_depth + 1.
  -- This means both neighbors are children of m (T.parent neighbor = some m).
  -- But adjacent vertices in the cycle that are both children of the same vertex m
  -- would require an edge between siblings, which is impossible in a tree
  -- (siblings have same depth, but edges only exist between parent-child pairs).
  -- Case analysis on cycle structure to find two adjacent children of m
  -- The tail is Nodup, so vertices are distinct
  have hnodup := c.simple
  -- The cycle has form [v, x₁, x₂, ..., xₖ, v] where tail = [x₁, ..., xₖ, v]
  -- Adjacent pairs in cycle: (v,x₁), (x₁,x₂), ..., (xₖ₋₁,xₖ), (xₖ,v)
  -- Find where m appears and examine its neighbors
  -- By adjacency property and minimum depth, m's neighbors have depth = depth(m) + 1
  -- These neighbors are children of m, but the edge between them would require
  -- one to be parent of other, contradicting equal depths.
  -- Actually, the contradiction comes from: two children of m are connected
  -- by a path not going through m. But in a tree, path between siblings
  -- must go through their parent.
  -- Simpler argument: look at ANY edge in the cycle where both endpoints
  -- have depth ≥ min_depth. If both have depth = min_depth + 1, they're
  -- siblings (children of same parent at depth min_depth).
  -- But siblings can't be adjacent in a parent-pointer tree.
  -- Find two consecutive vertices in tail, both with depth min_depth + 1
  -- This happens at the neighbors of m
  -- Get m's position in the full cycle
  cases hcv : c.vertices with
  | nil => exact (c.nonempty hcv).elim
  | cons head rest =>
    -- rest = tail, head = v
    have hrest_eq : rest = tailList := by simp [tailList, hcv]
    -- m is at index idx in rest
    -- Neighbors of m in cycle: if idx > 0, left neighbor is rest[idx-1]
    --                          if idx < rest.length - 1, right neighbor is rest[idx+1]
    --                          if idx = 0, left neighbor is head = v
    --                          if idx = rest.length - 1, right neighbor is head (via wraparound)
    -- But head = v also appears at the end of rest (cycle closes)
    -- Actually, need to be more careful. Let's check if idx is interior.
    have hrest_len : rest.length ≥ 3 := by rw [hrest_eq]; exact htail_len
    -- Case: idx = 0 (m is first element of tail)
    -- Then m's left neighbor is head = v, right neighbor is rest[1]
    -- Both have depth ≥ min_depth, so both = min_depth + 1
    -- Case: idx = rest.length - 1 (m is last element of tail = v)
    -- Then m's neighbors are rest[idx-1] and head = v (via the start)
    -- Since m = v = head in this case, and the cycle goes head - rest[0] - ... - rest[last] = head
    -- The neighbors of v are rest[0] and rest[rest.length - 2]
    -- All of this is getting complex. Let me use a different approach.
    -- Key fact: In the cycle, there exists an edge (a, b) where both a, b are in tail
    -- and both have depth ≥ min_depth. If depth(m) is the minimum, then
    -- for the edge involving m, the other endpoint has depth = min_depth + 1.
    -- Consider m's predecessor in the cycle. This has depth = min_depth + 1.
    -- Consider m's successor in the cycle. This has depth = min_depth + 1.
    -- The predecessor and successor are different (cycle length ≥ 3).
    -- Both are children of m (since their parent has depth one less = min_depth = depth(m)).
    -- But in a tree, siblings (different children of same parent) cannot be adjacent!
    -- Wait, pred and succ are not necessarily adjacent to each other.
    -- The issue is: the cycle goes ... - pred - m - succ - ...
    -- pred and succ are adjacent to m, not to each other (unless cycle has length 3).
    -- The path from pred to succ avoiding m goes the long way around the cycle.
    -- This path connects two children of m without using m.
    -- In a tree, any path between children must use their parent. Contradiction!
    -- To formalize "path between children without parent is impossible":
    -- If parent(a) = some m and parent(b) = some m and path from a to b avoids m,
    -- then all vertices on path have depth ≥ min_depth + 1 (since depth ≥ min_depth
    -- and only m has depth = min_depth). But to go from a's subtree to b's subtree,
    -- must pass through m. Contradiction.
    -- For simplicity, let's just derive contradiction from the edge structure:
    -- Consider the edge (m, succ) in the cycle. succ has depth = min_depth + 1.
    -- So T.parent succ = some m (succ is child of m).
    -- Consider the edge (pred, m). pred has depth = min_depth + 1.
    -- So T.parent pred = some m (pred is child of m).
    -- Now the long path from pred to succ uses vertices from tail except m.
    -- All these vertices have depth ≥ min_depth, and the only vertex with
    -- depth = min_depth is m (which is excluded). So all have depth ≥ min_depth + 1.
    -- Consider any vertex x on this path. x has depth ≥ min_depth + 1.
    -- The path starts at pred (depth min_depth + 1) and ends at succ (depth min_depth + 1).
    -- Since adjacent vertices have |depth diff| = 1, and we start and end at min_depth + 1,
    -- and never go below min_depth + 1, we must stay at depth ≥ min_depth + 1.
    -- But to connect pred (in m's subtree) to succ (in m's subtree, different branch),
    -- we need to go through m or an ancestor. But m has depth min_depth and ancestors
    -- have depth < min_depth. Since we stay at depth ≥ min_depth + 1, we can't reach
    -- succ from pred. Contradiction!
    -- The technical lemma needed: if parent(a) = some m and parent(b) = some m and a ≠ b,
    -- then any walk from a to b in T.toSimpleGraph visits m or a vertex of depth < depth(m).
    -- Let's prove this indirectly by showing the walk can't exist under our constraints.
    -- Get the predecessor and successor of m
    -- Find the index of m in rest (= tailList)
    have hm_in_rest : m ∈ rest := by rw [hrest_eq]; exact hm_in_tail
    let idx := rest.idxOf m
    have hidx_tail : idx < rest.length := List.idxOf_lt_length_of_mem hm_in_rest
    have hm_at_rest_idx : rest[idx]'hidx_tail = m := List.getElem_idxOf hidx_tail
    -- Index of m in full cycle is idx + 1 (since full cycle = head :: rest)
    let m_idx := idx + 1
    have hm_idx_lt : m_idx < c.vertices.length := by simp [hcv, m_idx]; omega
    have hm_at_idx : c.vertices[m_idx]'hm_idx_lt = m := by
      simp only [hcv, List.getElem_cons_succ]
      exact hm_at_rest_idx
    -- Predecessor (at index m_idx - 1 if m_idx > 0, else wraparound to end)
    -- Successor (at index m_idx + 1 if m_idx + 1 < length, else stop)
    -- Since m_idx = idx + 1 ≥ 1, predecessor exists at m_idx - 1
    have hpred_idx_lt : m_idx - 1 < c.vertices.length := by omega
    let pred := c.vertices[m_idx - 1]'hpred_idx_lt
    -- Check if successor exists
    by_cases hsucc_exists : m_idx + 1 < c.vertices.length
    · -- Successor exists
      let succ := c.vertices[m_idx + 1]'hsucc_exists
      -- pred and succ are adjacent to m
      have hpred_adj : T.toSimpleGraph.Adj pred m := by
        have hadj := c.adjacent (m_idx - 1) (by omega : m_idx - 1 + 1 < c.vertices.length)
        obtain ⟨a, b, ha, hb, hab⟩ := hadj
        have ha' : a = pred := by
          have : c.vertices[m_idx - 1]? = some pred := List.getElem?_eq_getElem hpred_idx_lt
          rw [this] at ha; exact Option.some.inj ha.symm
        have hb' : b = m := by
          have hlt : m_idx < c.vertices.length := hm_idx_lt
          have : c.vertices[m_idx]? = some m := by rw [List.getElem?_eq_getElem hlt, hm_at_idx]
          have hmidx : m_idx - 1 + 1 = m_idx := by omega
          rw [hmidx] at hb; rw [this] at hb; exact Option.some.inj hb.symm
        rw [← ha', ← hb']; exact hab
      have hsucc_adj : T.toSimpleGraph.Adj m succ := by
        have hadj := c.adjacent m_idx (by omega : m_idx + 1 < c.vertices.length)
        obtain ⟨a, b, ha, hb, hab⟩ := hadj
        have ha' : a = m := by
          have : c.vertices[m_idx]? = some m := by rw [List.getElem?_eq_getElem hm_idx_lt, hm_at_idx]
          rw [this] at ha; exact Option.some.inj ha.symm
        have hb' : b = succ := by
          have : c.vertices[m_idx + 1]? = some succ := List.getElem?_eq_getElem hsucc_exists
          rw [this] at hb; exact Option.some.inj hb.symm
        rw [← ha', ← hb']; exact hab
      -- pred and succ are in tail (for depth minimality)
      have hpred_in_tail : pred ∈ tailList := by
        -- pred = c.vertices[m_idx - 1] where m_idx = idx + 1, so m_idx - 1 = idx
        -- tailList = c.vertices.tail = rest (since c.vertices = head :: rest)
        simp only [tailList, hcv, List.tail_cons]
        -- Goal is now: pred ∈ rest
        have hm_idx_eq : m_idx - 1 = idx := by simp only [m_idx]; omega
        by_cases hidx_zero : idx = 0
        · -- idx = 0: pred = c.vertices[0] = head = v, and v ∈ rest (last element)
          have hstart := c.start_eq
          simp only [hcv, List.head?_cons] at hstart
          have hhead_eq_v : head = v := Option.some.inj hstart
          have hfinish := c.finish_eq
          simp only [hcv] at hfinish
          have hrest_ne : rest ≠ [] := by intro h; simp [h] at hrest_len
          have hv_in_rest : v ∈ rest := by
            have hcons_last : (head :: rest).getLast? = rest.getLast? := by
              cases rest with
              | nil => exact (hrest_ne rfl).elim
              | cons b l => exact List.getLast?_cons_cons
            rw [hcons_last, List.getLast?_eq_some_getLast hrest_ne] at hfinish
            have hrest_last_eq_v : rest.getLast hrest_ne = v := Option.some.inj hfinish
            rw [← hrest_last_eq_v]
            exact List.getLast_mem hrest_ne
          -- pred = c.vertices[0] = head = v
          have hpred_eq_v : pred = v := by
            simp only [pred, hcv, hm_idx_eq, hidx_zero, List.getElem_cons_zero, hhead_eq_v]
          rw [hpred_eq_v]
          exact hv_in_rest
        · -- idx > 0: pred = rest[idx - 1] ∈ rest
          have hidx_pos : 0 < idx := Nat.pos_of_ne_zero hidx_zero
          have hrest_idx_lt : idx - 1 < rest.length := by omega
          have hmem_rest : rest[idx - 1]'hrest_idx_lt ∈ rest := List.getElem_mem hrest_idx_lt
          -- pred = c.vertices[m_idx - 1] = (head :: rest)[idx] = rest[idx - 1]
          have hpred_eq : pred = rest[idx - 1]'hrest_idx_lt := by
            simp only [pred, hcv, hm_idx_eq]
            have hidx_lt_cons : idx < (head :: rest).length := by simp; omega
            match hidx : idx with
            | 0 => simp only [hidx] at hidx_zero; exact (hidx_zero trivial).elim
            | k + 1 => simp only [Nat.add_sub_cancel, List.getElem_cons_succ]
          rw [hpred_eq]
          exact hmem_rest
      have hsucc_in_tail : succ ∈ tailList := by
        simp only [tailList, hcv, List.tail_cons]
        -- succ = c.vertices[m_idx + 1] = (head :: rest)[m_idx + 1] = rest[m_idx]
        have hrest_idx_lt : m_idx < rest.length := by
          simp only [List.length_cons, hcv] at hsucc_exists; omega
        have hsucc_lt : m_idx + 1 < (head :: rest).length := by simp only [List.length_cons]; omega
        have heq : (head :: rest)[m_idx + 1]'hsucc_lt = rest[m_idx]'hrest_idx_lt := List.getElem_cons_succ head rest m_idx hsucc_lt
        have hmem_rest : rest[m_idx]'hrest_idx_lt ∈ rest := List.getElem_mem hrest_idx_lt
        have hsucc_eq : succ = rest[m_idx]'hrest_idx_lt := by simp only [succ, hcv, heq]
        simp only [hsucc_eq]
        exact hmem_rest
      -- By minimality, depth pred ≥ depth m and depth succ ≥ depth m
      have hpred_ge := hmin_le pred hpred_in_tail
      have hsucc_ge := hmin_le succ hsucc_in_tail
      -- By adjacency, |depth pred - depth m| = 1 and |depth succ - depth m| = 1
      have hpred_depth := adj_depth T hpred_adj
      have hsucc_depth := adj_depth T hsucc_adj
      -- Combined: depth pred = depth m + 1 and depth succ = depth m + 1
      have hpred_eq : T.depth pred = T.depth m + 1 := by
        cases hpred_depth with
        | inl h => exact h  -- T.depth pred = T.depth m + 1
        | inr h => omega    -- T.depth m = T.depth pred + 1 contradicts hpred_ge
      have hsucc_eq : T.depth succ = T.depth m + 1 := by
        cases hsucc_depth with
        | inl h => omega    -- T.depth m = T.depth succ + 1 contradicts hsucc_ge
        | inr h => exact h  -- T.depth succ = T.depth m + 1
      -- So pred and succ are both children of m
      -- T.parent pred = some m and T.parent succ = some m
      have hpred_child : T.parent pred = some m := by
        simp only [toSimpleGraph] at hpred_adj
        cases hpred_adj with
        | inl h =>
          -- parent pred = some m
          exact h
        | inr h =>
          -- parent m = some pred, so depth m = depth pred + 1
          have := (depth_parent T h).symm
          omega
      have hsucc_child : T.parent succ = some m := by
        simp only [toSimpleGraph] at hsucc_adj
        cases hsucc_adj with
        | inl h =>
          -- parent m = some succ, so depth m = depth succ + 1
          have := (depth_parent T h).symm
          omega
        | inr h =>
          -- parent succ = some m
          exact h
      -- pred ≠ succ (they're at different positions in a Nodup list)
      have hpred_ne_succ : pred ≠ succ := by
        -- pred is at index m_idx - 1, succ is at index m_idx + 1 in full list
        -- These map to indices m_idx - 2 and m_idx in tail (after removing head)
        -- Actually, let's show they're different by their positions
        intro heq
        -- If pred = succ, they're at indices m_idx - 1 and m_idx + 1
        -- In the tail, which is Nodup, same element can't appear twice
        -- pred is at tail index m_idx - 2 (if m_idx ≥ 2) or... this is getting complex
        -- Simpler: m_idx - 1 ≠ m_idx + 1 since that would require -1 = 1
        -- And in a Nodup list, different indices have different elements
        -- But the Nodup is on the tail, not the full list
        -- Let me use the Nodup property more carefully
        -- c.vertices[k] for k ≥ 1 is rest[k-1]
        -- pred = c.vertices[m_idx - 1], succ = c.vertices[m_idx + 1]
        -- If m_idx ≥ 2: pred = rest[m_idx - 2], succ = rest[m_idx]
        -- If m_idx = 1: pred = c.vertices[0] = head = v
        cases Nat.lt_or_eq_of_le (Nat.one_le_iff_ne_zero.mpr (by omega : m_idx ≠ 0)) with
        | inl hm_gt_1 =>
          -- m_idx ≥ 2
          have hp_idx : m_idx - 1 - 1 < rest.length := by omega
          have hs_idx : m_idx + 1 - 1 < rest.length := by simp [hcv] at hsucc_exists; omega
          have hpred' : pred = rest[m_idx - 1 - 1]'hp_idx := by
            -- pred = c.vertices[m_idx - 1] = (head :: rest)[m_idx - 1]
            -- Since m_idx ≥ 2, m_idx - 1 ≥ 1, so (head :: rest)[m_idx - 1] = rest[m_idx - 2]
            have hlt : (m_idx - 1 - 1) + 1 < (head :: rest).length := by
              simp only [hcv] at hpred_idx_lt; omega
            have heq : (head :: rest)[(m_idx - 1 - 1) + 1]'hlt = rest[m_idx - 1 - 1]'hp_idx :=
              List.getElem_cons_succ head rest (m_idx - 1 - 1) hlt
            simp only [pred, hcv]
            convert heq using 2
            omega
          have hsucc' : succ = rest[m_idx + 1 - 1]'hs_idx := by
            simp only [succ, hcv, Nat.add_sub_cancel, List.getElem_cons_succ]
          rw [hpred', hsucc'] at heq
          have hidx_ne : m_idx - 1 - 1 ≠ m_idx + 1 - 1 := by omega
          -- hnodup : c.vertices.tail.Nodup, and c.vertices.tail = rest (via hcv)
          have hnodup' : rest.Nodup := by simp only [hcv, List.tail_cons] at hnodup; exact hnodup
          exact hidx_ne ((List.Nodup.getElem_inj_iff hnodup').mp heq)
        | inr hm_eq_1 =>
          -- m_idx = 1, so idx = 0
          -- pred = c.vertices[0] = head = v
          -- succ = c.vertices[2] = rest[1]
          have hpred' : pred = head := by simp [pred, hcv, hm_eq_1]
          have hs_idx : 1 < rest.length := by simp [hcv, hm_eq_1] at hsucc_exists; omega
          have hsucc' : succ = rest[1]'hs_idx := by
            simp only [succ, hcv, ← hm_eq_1, Nat.add_sub_cancel, List.getElem_cons_succ]
          -- head = v, and v appears at end of rest (getLast rest = v)
          -- By Nodup of rest, v appears exactly once, so rest[1] ≠ v unless 1 = rest.length - 1
          -- But then rest.length = 2, and rest = [x, v] for some x
          -- rest[1] = v in that case
          -- Is that possible? Let's check what happens then.
          -- If rest = [something, v], then tail = rest has length 2
          -- The cycle is [v, something, v], length 3
          -- m is at idx = 0 in tail, so m = rest[0] = something
          -- pred = v, succ = rest[1] = v
          -- So pred = succ = v. But we derived pred ≠ succ!
          -- Actually we're trying to derive a contradiction from pred = succ = heq
          -- If pred = succ, we need to show this is impossible
          -- In this case, pred = head = v and succ = rest[1]
          -- If heq : pred = succ, then v = rest[1]
          -- rest = tail, and finish_eq says getLast (head :: rest) = v
          -- So getLast rest = v (since rest ≠ [])
          -- If rest[1] = v = getLast rest, and rest is Nodup, then 1 = rest.length - 1
          -- So rest.length = 2
          -- But we have htail_len : rest.length ≥ 2, so this is possible
          -- The issue is whether this contradicts something else
          -- In this case, the cycle is [v, m, v] which has 3 vertices
          -- But len_ge_3 says vertices.length ≥ 3, which is satisfied
          -- Hmm, wait, actually if m_idx = 1 and succ is at m_idx + 1 = 2, and succ = v
          -- Then the cycle is [v, m, v], and we have:
          -- - Edge v - m (adjacent)
          -- - Edge m - v (adjacent)
          -- These give T.parent v = some m or T.parent m = some v (from first edge)
          -- and T.parent m = some v or T.parent v = some m (from second edge)
          -- Both edges give the same adjacency, which is fine.
          -- The problem is: we said hpred_child : T.parent pred = some m
          -- But pred = v, so T.parent v = some m
          -- And we said hsucc_child : T.parent succ = some m
          -- But succ = v = pred, so T.parent v = some m (same thing)
          -- Now, pred and succ are the same vertex v. The Nodup of tail is [m, v].
          -- m ≠ v for Nodup.
          -- The cycle [v, m, v] connects v to m to v.
          -- Both edges give adjacency v - m, meaning parent(v) = some m or parent(m) = some v.
          -- From hpred_child (with pred = v), we have parent(v) = some m.
          -- This means depth(v) = depth(m) + 1.
          -- But m is in the tail [m, v], and we said m has minimum depth in tail.
          -- If depth(v) = depth(m) + 1 > depth(m), this is consistent.
          -- So actually pred = succ = v is a valid possibility!
          -- But then our argument about "two different children" breaks down.
          -- Let me reconsider...
          -- Wait, the assumption hsucc_exists says m_idx + 1 < c.vertices.length.
          -- c.vertices = [v, m, v] has length 3. m_idx = 1.
          -- m_idx + 1 = 2 < 3. So hsucc_exists is true.
          -- succ = c.vertices[2] = v.
          -- pred = c.vertices[0] = v.
          -- So pred = succ = v, and hpred_ne_succ would be False!
          -- This means the hpred_ne_succ proof can't go through in this case.
          -- Let me find a different approach for this edge case.
          -- Actually wait, I think there's an issue with my earlier reasoning.
          -- The cycle has vertices [head, rest...] = [v, ...stuff..., v]
          -- The tail is rest = [...stuff..., v]
          -- If rest.length = 2, then rest = [m, v] for some m.
          -- Full cycle = [v, m, v], which has 3 vertices.
          -- The edges are v-m (index 0-1) and m-v (index 1-2).
          -- Both give adjacency v-m.
          -- In this case, pred (at index 0) = v, and succ (at index 2) = v.
          -- So pred = succ = v.
          -- But wait, we need to check: is m_idx + 1 = 2 < 3? Yes.
          -- So this case is covered by hsucc_exists.
          -- In this case, we can't use "pred ≠ succ" because they're equal!
          -- So we need a different argument for the length-3 cycle case.
          -- For a length-3 cycle [v, a, v]:
          -- v and a are adjacent. Edge v-a means parent(v) = some a or parent(a) = some v.
          -- The tail is [a, v], with Nodup (so a ≠ v).
          -- Minimum depth is min(depth(a), depth(v)).
          -- Case: depth(a) ≤ depth(v). Then m = a.
          -- Neighbors of m = a: v (at index 0) and v (at index 2). Both are v!
          -- By minimality depth(v) ≥ depth(a).
          -- By adjacency |depth(v) - depth(a)| = 1, so depth(v) = depth(a) + 1.
          -- So v is a child of a: parent(v) = some a.
          -- Now the cycle v - a - v has both edges being v-a adjacency.
          -- This is fine for a valid cycle, but where's the contradiction?
          -- The cycle just goes v → a → v. Edge v-a and edge a-v.
          -- Both are the same edge (undirected)!
          -- But a cycle/circuit must have at least 3 edges. Let me check.
          -- Actually, looking at SGWalk: len_ge_3 says vertices.length ≥ 3.
          -- vertices.length = 3 means 2 edges (length - 1).
          -- But IsCircuit requires 3 ≤ p.length (3 edges).
          -- In simpleGraph_acyclic_of_tree, we set len_ge_3 based on hp.three_le_length.
          -- hp : p.IsCircuit, and IsCircuit.three_le_length gives 3 ≤ p.length.
          -- So p has at least 3 edges, meaning p.support has at least 4 vertices.
          -- So c.vertices.length ≥ 4, not ≥ 3!
          -- Let me re-read the code...
          -- In simpleGraph_acyclic_of_tree:
          --   len_ge_3 := by
          --     have := hp.three_le_length
          --     simp only [SimpleGraph.Walk.length_support]
          --     omega
          -- hp.three_le_length gives 3 ≤ p.length.
          -- length_support gives p.support.length = p.length + 1.
          -- So p.support.length ≥ 4.
          -- So c.vertices.length ≥ 4!
          -- This means the case rest.length = 2 is impossible.
          -- Great, so our proof should work. Let me adjust.
          -- We have htail_len : c.vertices.tail.length ≥ 2, but actually we need ≥ 3.
          -- Hmm wait, the original SGWalk has len_ge_3 : vertices.length ≥ 3.
          -- But when we construct it from IsCircuit, we get vertices.length ≥ 4.
          -- For the general SGWalk, we only have ≥ 3.
          -- So the proof needs to handle the length-3 case differently, or
          -- we need to strengthen the hypothesis.
          -- Actually, looking at the theorem statement, it says:
          --   theorem no_cycle_via_depth_aux (T : TreeAuth n) (hn : 0 < n) (v : Fin n) (c : SGWalk T v) : False
          -- And the SGWalk has len_ge_3 : vertices.length ≥ 3.
          -- So we need to handle the length = 3 case.
          -- For length = 3: [v, a, v] with edges v-a and a-v. But these are the same edge!
          -- A walk that uses the same edge twice (v → a → v) is not a simple circuit.
          -- The simple property says tail.Nodup. Tail = [a, v], which is Nodup iff a ≠ v.
          -- But there's no constraint that edges are distinct.
          -- Hmm, actually let me look at IsCircuit again.
          -- IsCircuit is a closed trail (no repeated edges) with length ≥ 3.
          -- The edge v-a appears once? No, it appears twice: from v to a, and from a to v.
          -- Wait, in a SimpleGraph, Adj is symmetric, so v-a and a-v are the "same edge".
          -- But in a Walk, we traverse edges with direction.
          -- IsCircuit.IsTrail says no edge is repeated.
          -- The walk v → a → v uses the edge {v, a} twice: once as v→a, once as a→v.
          -- These are the same edge (unordered pair), so this violates IsTrail!
          -- So a length-2 walk (3 vertices) like v → a → v is NOT a valid circuit!
          -- Therefore, IsCircuit with 3 ≤ length means at least 3 distinct edges,
          -- which means at least 4 vertices.
          -- So the case rest.length = 2 (c.vertices.length = 3) can't arise from IsCircuit.
          -- But SGWalk has len_ge_3 with ≥ 3, not ≥ 4.
          -- Ah, but SGWalk is only constructed from IsCircuit, so in practice it has length ≥ 4.
          -- But the theorem statement allows any SGWalk with len_ge_3.
          -- So either:
          -- 1. The proof needs to handle length = 3, or
          -- 2. The SGWalk definition should require length ≥ 4, or
          -- 3. We add additional constraints.
          -- Looking at the conversion in simpleGraph_acyclic_of_tree, it correctly gets len_ge_3
          -- from IsCircuit.three_le_length, giving ≥ 4. So the constructed SGWalk has length ≥ 4.
          -- But someone could call no_cycle_via_depth_aux with a different SGWalk of length 3.
          -- Let me check if length 3 is actually possible for a valid SGWalk...
          -- For [v, a, v] to be a valid SGWalk:
          -- - nonempty: ✓
          -- - start_eq: ✓
          -- - finish_eq: ✓
          -- - len_ge_3: ≥ 3, ✓
          -- - adjacent: v-a at j=0, a-v at j=1, both OK if v and a are adjacent.
          -- - simple: tail.Nodup = [a, v].Nodup, OK if a ≠ v.
          -- So a length-3 SGWalk IS possible in theory.
          -- We need to handle this case.
          -- For length 3: [v, a, v], tail = [a, v], min is depth(a) or depth(v).
          -- WLOG min = depth(a) (since if depth(v) ≤ depth(a), swap roles).
          -- Actually can't swap since start must be v. But let's consider both.
          -- Sub-case: depth(a) ≤ depth(v). Then m = a (at tail index 0).
          -- m_idx = 0 + 1 = 1 in full list.
          -- pred = c.vertices[0] = v.
          -- succ check: m_idx + 1 = 2 < 3? Yes. succ = c.vertices[2] = v.
          -- pred = succ = v. Hmm.
          -- Sub-case: depth(v) ≤ depth(a). Then m = v (at tail index 1).
          -- m_idx = 1 + 1 = 2 in full list.
          -- pred = c.vertices[1] = a.
          -- succ check: m_idx + 1 = 3 < 3? No! So hsucc_exists is false.
          -- So we go to the else branch (which I haven't written yet).
          -- OK so for length 3 with min at v, succ doesn't exist. Let me handle that branch.
          -- For now, in this inner case, if pred = succ = v, we need a different argument.
          -- Since depth(v) = depth(a) + 1 (v is child of a, from hpred_child with pred = v),
          -- and the cycle is v - a - v, this is a valid "cycle" of length 2.
          -- But wait, for a circuit we need 3 distinct edges. Here we only have 1 edge {v, a}
          -- used twice. So this is NOT a valid IsCircuit.
          -- The issue is that SGWalk allows this, but in practice it doesn't arise from IsCircuit.
          -- For the proof to be complete, we need to either:
          -- A. Handle this case (show it leads to contradiction somehow else), or
          -- B. Strengthen SGWalk to require length ≥ 4.
          -- Let me think about option A. For [v, a, v] with edges v-a and a-v (same edge),
          -- is there a contradiction?
          -- The edge v-a means parent(v) = some a or parent(a) = some v.
          -- WLOG parent(a) = some v (the case parent(v) = some a is symmetric).
          -- Then depth(a) = depth(v) + 1.
          -- The tail [a, v] has minimum at v (since depth(v) < depth(a)).
          -- m = v at tail index 1. m_idx = 2.
          -- m_idx + 1 = 3, and c.vertices.length = 3, so hsucc_exists is false.
          -- We go to the else branch.
          -- In the else branch, m_idx = 2 = c.vertices.length - 1 (last element).
          -- m = v at the last position. But v also at position 0.
          -- The cycle is v - a - v. m at position 2 has pred at position 1 (which is a).
          -- m at position 2 has no succ in the list, but the cycle "wraps" back to position 0 (also v).
          -- But v = m, so the "succ" is m itself, not a different child.
          -- So for this case, there's only one neighbor of m (which is a), not two.
          -- Let me see what happens:
          -- depth(a) = depth(v) + 1 (child of v).
          -- The "long way" from a to a (itself) avoiding v would be... just a (trivial).
          -- No contradiction there.
          -- Actually, the other edge is a - v (from position 1 to position 2).
          -- This is the same edge as v - a.
          -- So the cycle uses the single edge {v, a} twice!
          -- If we think of it as a directed walk, it goes v → a → v, using edge {v,a} in both directions.
          -- For IsCircuit, IsTrail says the edge set has no duplicates.
          -- The edges in the walk are determined by the consecutive pairs.
          -- Walk v → a → v has edges s(v, a) (from v to a) and s(a, v) (from a to v).
          -- As unordered pairs, s(v, a) = s(a, v). So the same edge appears twice!
          -- This violates IsTrail, hence IsCircuit.
          -- So a length-3 walk [v, a, v] is NOT a valid IsCircuit (not a trail).
          -- But SGWalk doesn't require IsTrail; it only requires Nodup of tail.
          -- So SGWalk is a weaker notion than IsCircuit.
          -- For the proof of simpleGraph_acyclic_of_tree, we convert IsCircuit to SGWalk.
          -- The conversion preserves: Nodup of tail comes from IsCircuit's support_nodup.
          -- Wait, let me check IsCircuit again.
          -- IsCircuit.support_nodup says p.support.tail.Nodup.
          -- For walk v → a → v, support = [v, a, v], tail = [a, v], which IS Nodup.
          -- So support_nodup is satisfied!
          -- What about IsTrail? IsCircuit requires IsTrail.
          -- IsTrail says the edges are distinct.
          -- Walk v → a → v has p.edges = [s(v, a), s(a, v)] = [s(v, a), s(v, a)].
          -- So p.edges.Nodup would be [s(v, a), s(v, a)].Nodup, which is false!
          -- Hence this walk is NOT a trail, hence NOT a circuit.
          -- So the length-3 case actually can't arise from IsCircuit!
          -- Therefore, in simpleGraph_acyclic_of_tree, the SGWalk always has length ≥ 4.
          -- For no_cycle_via_depth_aux, which takes any SGWalk, the length-3 case
          -- might arise, but it would require the same edge to appear twice,
          -- which... wait, SGWalk doesn't track edges, only vertices.
          -- SGWalk allows [v, a, v] as a valid cycle, even though it uses the same edge twice.
          -- The key is: does no_cycle_via_depth_aux hold for such SGWalks?
          -- For [v, a, v]:
          -- If depth(a) ≤ depth(v), then m = a. Both neighbors are v.
          -- depth(v) ≥ depth(a), and |depth(v) - depth(a)| = 1, so depth(v) = depth(a) + 1.
          -- v is child of a. The cycle v - a - v shows v adjacent to a.
          -- Is there a contradiction? We have a single edge between parent a and child v.
          -- The cycle uses it twice. That's allowed in SGWalk but not IsCircuit.
          -- There's no contradiction from the tree structure itself.
          -- So no_cycle_via_depth_aux is NOT true for all SGWalks, only for those
          -- arising from IsCircuits (i.e., length ≥ 4 and IsTrail).
          -- Hmm, this is a problem. Let me re-examine.
          -- Actually, I think the issue is that the length-3 case [v, a, v] represents
          -- going back and forth on a single edge. This is a "degenerate" cycle that
          -- doesn't exist in an acyclic graph either, because it requires the edge v-a
          -- to exist, which it does in our tree. But going v → a → v is just a round trip,
          -- not a true cycle.
          -- The no_cycle_depth_argument theorem says no IsCircuit exists. IsCircuit requires
          -- at least 3 distinct edges and no edge repeated.
          -- For the general SGWalk (which allows edge repeats), the theorem might not hold.
          -- But the theorem no_cycle_via_depth_aux is stated for SGWalk, not IsCircuit.
          -- Let me check if SGWalk is only used internally and IsCircuit is the external API.
          -- Looking at simpleGraph_acyclic_of_tree:
          --   T.toSimpleGraph.IsAcyclic means ∀ v, ∀ c : Walk v v, ¬c.IsCircuit.
          -- So we're proving there's no IsCircuit, not no SGWalk.
          -- The conversion from IsCircuit to SGWalk in the proof ensures SGWalk has length ≥ 4.
          -- But no_cycle_via_depth_aux is stated more generally.
          -- For a clean proof, we have two options:
          -- 1. Strengthen SGWalk to require length ≥ 4 (matching IsCircuit).
          -- 2. Prove no_cycle_via_depth_aux handles length 3 (or show it's vacuously true).
          -- For option 2, we need to show [v, a, v] can't be an SGWalk of a tree graph.
          -- But it can: if a-v is an edge (parent-child), then [v, a, v] satisfies SGWalk.
          -- So option 2 doesn't work.
          -- For option 1, changing SGWalk requires modifying the structure.
          -- Alternatively, we can add a hypothesis to no_cycle_via_depth_aux.
          -- Or we can just note that the length-3 case is impossible for IsCircuit and
          -- therefore the else branch here (where hpred_ne_succ fails) is dead code.
          -- For now, let me just add a sorry or exfalso for the length-3 case and
          -- proceed with the rest of the proof, since in practice it doesn't arise.
          -- Actually, let's try: for the length-3 case [v, a, v], we have pred = succ = v.
          -- hpred_child : parent v = some m = some a (since m = a)
          -- hsucc_child : parent v = some m = some a (same)
          -- So v is child of a. The tail [a, v] has a ≠ v (Nodup).
          -- depth(v) = depth(a) + 1.
          -- min_depth = depth(a) (assuming a is the minimum).
          -- Hmm, is there any constraint we can use?
          -- Actually for this case, the "two children" are the same vertex v.
          -- So the argument about "path between two children" doesn't apply.
          -- Let me think of a different argument for length-3.
          -- For [v, a, v] to be a valid SGWalk:
          -- - v ≠ a (from Nodup of [a, v])
          -- - v and a are adjacent
          -- In a tree, v-a edge means parent(v) = some a or parent(a) = some v.
          -- Let's say parent(v) = some a (v is child of a). Then depth(v) = depth(a) + 1.
          -- The cycle [v, a, v] traces v → a → v.
          -- Edges: v-a, a-v (same edge, used twice).
          -- This is NOT an IsCircuit (not a trail).
          -- But it IS an SGWalk if we allow edge reuse.
          -- For the theorem to hold, we need to show this can't happen.
          -- Actually, for a tree, the graph IS connected and acyclic (for ≥ 4 vertices).
          -- For 2 vertices connected by a single edge, the only "cycle" is the length-2
          -- back-and-forth [v, a, v], which is NOT a circuit.
          -- So IsAcyclic holds because there's no circuit, not because there's no SGWalk.
          -- OK so the conclusion is: no_cycle_via_depth_aux might be too strong as stated.
          -- It claims to show False for any SGWalk, but the length-3 SGWalk exists in trees.
          -- The fix is to either:
          -- A. Change SGWalk to match IsCircuit more closely (require IsTrail-like property).
          -- B. Change no_cycle_via_depth_aux to only handle length ≥ 4.
          -- C. Find a different argument for length 3.
          -- For option C: length-3 SGWalk [v, a, v] uses edge v-a twice.
          -- The simple property (tail Nodup) doesn't rule this out.
          -- Can we derive a contradiction from using the same edge twice?
          -- Hmm, actually we can argue: edges in a tree are parent-child.
          -- If we traverse v → a → v, the first edge is child-to-parent (v→a if parent(v) = a),
          -- the second is parent-to-child (a→v).
          -- For any vertex x in the walk, it's visited how many times?
          -- v: twice (at start and end). a: once.
          -- But wait, for an SGWalk, finish_eq says getLast = v, and start_eq says head = v.
          -- And simple says tail is Nodup. Tail = [a, v]. So a ≠ v, and v appears once in tail.
          -- So v appears twice in the full list [v, a, v]: at index 0 and index 2.
          -- This is allowed by SGWalk (it's like a closed walk).
          -- Hmm, I'm stuck on the length-3 case. Let me just proceed with the main proof
          -- for length ≥ 4 and handle length 3 separately or note that it doesn't arise.
          -- For pragmatic purposes, since simpleGraph_acyclic_of_tree constructs SGWalk from
          -- IsCircuit which has length ≥ 4, the theorem will work in practice.
          -- I'll add a subcase for when pred = succ (the length-3 scenario) and
          -- use a different argument there.
          -- If pred = succ, then the cycle has the form [..., pred, m, pred, ...].
          -- This means pred appears twice consecutively around m.
          -- In the cycle [head, rest...], if m is at position 1 in the full list,
          -- pred = head and succ = rest[1].
          -- If pred = succ, then head = rest[1].
          -- But head = v and rest ends with v (finish_eq), so we need to check if rest[1] = v.
          -- If rest = [m, v] (length 2), then rest[1] = v = head.
          -- So pred = succ = v iff rest.length = 2.
          -- In this case, we can use the Nodup of tail = rest:
          -- rest = [m, v] with m ≠ v.
          -- The edges are v-m and m-v (same edge).
          -- For a tree, this is allowed (just traversing one edge back and forth).
          -- There's no contradiction from tree structure, only from IsCircuit's IsTrail.
          -- So we need to additionally argue that rest.length ≥ 3 or handle length 2 specially.
          -- Since len_ge_3 says full list length ≥ 3, rest.length = full.length - 1 ≥ 2.
          -- So rest.length ≥ 2, and the edge case is rest.length = 2 exactly.
          -- Let me add a check: if rest.length = 2, we can argue differently.
          -- For rest.length = 2, the cycle is [v, m, v] with one edge v-m.
          -- Going v → m → v uses the edge twice.
          -- For IsCircuit, this is not a trail (edge repeated).
          -- For SGWalk, this is valid.
          -- We need to show this leads to False, but it doesn't for SGWalk in general.
          -- Unless... the adjacency property requires different edges?
          -- No, adjacency just requires each consecutive pair to be adjacent in the graph.
          -- OK so I think the cleanest fix is to add an assumption that the cycle length is ≥ 4,
          -- or change the SGWalk definition to require length ≥ 4.
          -- But I'd rather not change the definition since it's used elsewhere.
          -- Let me just add a case split: if rest.length = 2, do something special.
          -- For rest.length = 2, we have [v, m, v] and the only edge is v-m.
          -- The depth argument gives: min depth is depth(m) or depth(v).
          -- If depth(m) ≤ depth(v), min is m. Neighbor is v. depth(v) = depth(m) + 1.
          -- If depth(v) ≤ depth(m), min is v. Neighbor is m. depth(m) = depth(v) + 1.
          -- Either way, one is parent of the other. No contradiction yet.
          -- But for a TRUE cycle (circuit), we need at least 3 edges.
          -- With 2 vertices and 1 edge, there's no circuit, only back-and-forth.
          -- The fact that [v, m, v] is an SGWalk doesn't contradict acyclicity.
          -- So the theorem no_cycle_via_depth_aux doesn't hold for SGWalk in general!
          -- We need to either:
          -- 1. Add an hypothesis that the cycle has no repeated edges.
          -- 2. Change SGWalk.
          -- 3. Prove a weaker statement.
          -- For now, let me just handle the ≥ 4 case properly and use `by omega` or
          -- `exact absurd rfl (by omega)` for the impossible length-2 case.
          -- Actually, let me check: for m_idx = 1 and hm_eq_1, and pred = succ = v (heq),
          -- we have rest.length = 2.
          -- But we have hrest_len : rest.length ≥ 2.
          -- If rest.length = 2, then... hmm, this is borderline.
          -- Let me add an explicit case split and see.
          -- Actually, let me just use a simpler approach.
          -- If pred = succ, then the walk uses the same edge m-pred twice (m-pred and pred-m).
          -- In a tree, using the same edge twice in a closed walk means the walk length
          -- is 2 (just back and forth). For length ≥ 3, this can't happen.
          -- So if len_ge_3 and pred = succ, we need to derive contradiction.
          -- Hmm, but len_ge_3 says ≥ 3 vertices, which allows 2 edges, which allows
          -- [v, a, v] with edges v-a and a-v.
          -- OK I'm going around in circles. Let me just add the explicit check for
          -- rest.length > 2 in the hpred_ne_succ proof.
          -- From hm_eq_1, we have m_idx = 1, so idx = 0, so m is the first element of tail.
          -- pred = v (head), succ = rest[1] (second element of rest).
          -- For pred = succ, we need rest[1] = v.
          -- Since rest = tail ends with v (finish_eq gives head :: rest ends with v, so rest ends with v),
          -- rest[last] = v.
          -- If rest[1] = rest[last] = v, then 1 = rest.length - 1 (by Nodup), so rest.length = 2.
          -- So if rest.length ≥ 3, then rest[1] ≠ v = rest[last], so pred ≠ succ.
          -- Let me add this constraint.
          -- But we only have htail_len : rest.length ≥ 2. We need ≥ 3.
          -- For the theorem to hold for length-3 cycles, we need a different argument.
          -- For now, let me just add exfalso and a note.
          -- Actually, let me just strengthen htail_len to ≥ 3 using the fact that
          -- for the theorem to hold, we need length ≥ 4 (from IsCircuit).
          -- But that changes the SGWalk definition or the theorem statement...
          -- Let me take the pragmatic approach: add an explicit case check.
          by_cases hrest_gt2 : rest.length > 2
          · -- rest.length ≥ 3, so 1 < rest.length - 1
            have hs_idx : 1 < rest.length := by omega
            -- rest[1] ≠ rest[rest.length - 1] = v by Nodup (since 1 ≠ rest.length - 1)
            have hlast_idx : rest.length - 1 < rest.length := by omega
            have hv_last : rest[rest.length - 1]'hlast_idx = v := by
              have hfinish := c.finish_eq
              have hrest_ne : rest ≠ [] := by intro h; simp [h] at hrest_len
              -- (head :: rest).getLast? = some v
              have hfull_ne : (head :: rest : List (Fin n)) ≠ [] := List.cons_ne_nil _ _
              simp only [hcv] at hfinish
              rw [List.getLast?_eq_some_getLast hfull_ne] at hfinish
              have hlast_eq_v : (head :: rest).getLast hfull_ne = v := Option.some.inj hfinish
              -- (head :: rest).getLast = rest.getLast when rest ≠ []
              have hcons_last : (head :: rest).getLast hfull_ne = rest.getLast hrest_ne :=
                List.getLast_cons hrest_ne
              rw [hcons_last] at hlast_eq_v
              -- rest.getLast = rest[rest.length - 1]
              rw [← List.getLast_eq_getElem hrest_ne]
              exact hlast_eq_v
            have h1_ne_last : (1 : ℕ) ≠ rest.length - 1 := by omega
            have hnodup' : rest.Nodup := by simp only [hcv, List.tail_cons] at hnodup; exact hnodup
            -- heq : pred = succ, hpred' : pred = head, hsucc' : succ = rest[1]
            -- So head = rest[1]
            -- Also head = v (from start_eq) and v = rest[rest.length - 1] (from hv_last)
            -- So rest[1] = rest[rest.length - 1], contradicting 1 ≠ rest.length - 1 via Nodup
            have hstart := c.start_eq
            simp only [hcv, List.head?_cons] at hstart
            have hhead_eq_v : head = v := Option.some.inj hstart
            have h1 : rest[1] = head := by rw [← hpred', ← hsucc']; exact heq.symm
            have h2 : rest[1] = v := by rw [h1, hhead_eq_v]
            have h3 : rest[1] = rest[rest.length - 1] := by rw [h2, ← hv_last]
            exact h1_ne_last ((List.Nodup.getElem_inj_iff hnodup').mp h3)
          · -- rest.length ≤ 2, combined with ≥ 2 gives rest.length = 2
            -- This is the degenerate case [v, m, v] which shouldn't arise from IsCircuit
            -- but is technically a valid SGWalk. We'll derive contradiction differently.
            push_neg at hrest_gt2
            have hrest_eq2 : rest.length = 2 := by omega
            -- rest = [m, v] where m = rest[0]
            -- The cycle is [v, m, v]
            -- Both edges are v-m (same edge used twice)
            -- In a tree, parent(v) = some m or parent(m) = some v
            -- Either way, one is ancestor of other
            -- We have hpred_child : parent v = some m (since pred = v)
            -- So v is child of m, depth(v) = depth(m) + 1
            -- The cycle just goes v → m → v, no contradiction from tree structure
            -- But we need to show False somehow!
            -- The issue is that [v, m, v] uses the same edge twice,
            -- which violates the IsCircuit property but not SGWalk.
            -- For SGWalk, this is actually a valid structure in a tree.
            -- So no_cycle_via_depth_aux is not true in general for SGWalk!
            -- For now, we need to add an additional hypothesis or change SGWalk.
            -- Let me see if there's anything in the current constraints that rules this out.
            -- hnodup : [m, v].Nodup, so m ≠ v. ✓
            -- adjacent at j=0: v - m are adjacent. ✓
            -- adjacent at j=1: m - v are adjacent. ✓ (same edge)
            -- start_eq, finish_eq: ✓
            -- len_ge_3: 3 ≥ 3. ✓
            -- So [v, m, v] is a valid SGWalk. And there's no contradiction from tree structure.
            -- The theorem statement is too strong!
            -- Let me check if we can derive a contradiction from some other property.
            -- Hmm, actually, wait. I assumed hpred_child : parent v = some m.
            -- This came from the adjacency v-m and the depth comparison.
            -- If parent(v) = some m, then v ≠ root (since root has no parent).
            -- But also m ≠ root unless depth(m) = 0.
            -- In the cycle [v, m, v], both v and m are visited.
            -- If m = root, then depth(m) = 0, depth(v) = 1.
            -- If m ≠ root, m has some parent p, but p is not in the cycle.
            -- Hmm, still no contradiction.
            -- OK I'll just admit that the length-2 case (rest.length = 2) is a gap.
            -- For the actual use case (IsCircuit), this doesn't arise.
            -- Let me just mark it and move on.
            -- Actually, I just realized: the problem says "len_ge_3 : vertices.length ≥ 3"
            -- but for IsCircuit, we have "three_le_length : 3 ≤ p.length" where p.length
            -- is the number of edges, not vertices.
            -- support.length = p.length + 1, so support.length ≥ 4.
            -- So the conversion gives vertices.length ≥ 4, not ≥ 3.
            -- So len_ge_3 : vertices.length ≥ 3 is a weaker statement than what we get from IsCircuit.
            -- For simpleGraph_acyclic_of_tree, we construct SGWalk with c.len_ge_4 satisfied by:
            --   hp.three_le_length gives 3 ≤ p.length
            --   simp gives c.vertices.length = p.length + 1 ≥ 4
            -- But SGWalk.len_ge_3 only requires ≥ 3.
            -- So the SGWalk we construct actually has length ≥ 4, but the type only requires ≥ 3.
            -- In no_cycle_via_depth_aux, we can't assume ≥ 4, only ≥ 3.
            -- So the theorem is stated more generally than needed.
            -- Options:
            -- A. Prove False for length = 3 (hard, maybe impossible).
            -- B. Change SGWalk.len_ge_3 to ≥ 4.
            -- C. Add assumption to no_cycle_via_depth_aux.
            -- D. Use a hack/sorry for the impossible case.
            -- For now, I'll use omega to show rest.length = 2 is impossible given
            -- the constraints we have. But we don't have such a constraint!
            -- Let me trace back: htail_len : rest.length ≥ 2 comes from hlen : c.vertices.length ≥ 3.
            -- c.vertices = head :: rest, so rest.length = c.vertices.length - 1 ≥ 2.
            -- We can't get rest.length ≥ 3 from this.
            -- So the gap is real. I'll add a sorry for this edge case and document it.
            -- Or better: change the theorem to add an extra hypothesis len_ge_4.
            -- SGWalk now has len_ge_4, so rest.length ≥ 3 (from hrest_len).
            -- This contradicts rest.length ≤ 2 (from hrest_gt2), so this branch is impossible.
            omega
      -- Now we have hpred_ne_succ : pred ≠ succ, hpred_child, hsucc_child
      -- pred and succ are distinct children of m
      -- The cycle provides a path succ → c[m_idx+2] → ... → v → ... → pred NOT through m
      -- But in a tree, any path between siblings must go through their parent
      -- This is a contradiction
      --
      -- Build the walk from succ to pred using cycle vertices, avoiding m
      -- The path goes: succ → c[m_idx+2] → ... → c[last-1] → v → c[1] → ... → pred
      -- Since m is at index m_idx and we skip that index, m ∉ path

      -- First, we build a walk from succ to pred using the cycle's adjacency
      -- The cycle wraps: succ = c[m_idx+1] → ... → c[last] = v = c[0] → ... → c[m_idx-1] = pred

      -- Key observation: since m_idx + 1 < c.vertices.length (hsucc_exists),
      -- m is NOT at the last position, so m ≠ v (since v is at positions 0 and last)
      have hm_ne_v : m ≠ v := by
        intro heq
        -- If m = v, then m is at the last position of the tail (since tail ends with v)
        -- But m is at index idx in the tail, where idx = m_idx - 1
        -- The tail's last index is rest.length - 1
        -- If m = v, then idx = rest.length - 1
        -- So m_idx - 1 = rest.length - 1, i.e., m_idx = rest.length
        -- But m_idx < c.vertices.length - 1 (since hsucc_exists says m_idx + 1 < c.vertices.length)
        -- c.vertices.length = 1 + rest.length (from hcv), so m_idx < rest.length
        -- This contradicts m_idx = rest.length
        have hm_idx_bound : m_idx < rest.length := by simp [hcv] at hsucc_exists; omega
        -- v is at the last position of rest (from finish_eq)
        have hrest_ne : rest ≠ [] := by intro h; simp [h] at hrest_len
        have hfull_ne : (head :: rest : List (Fin n)) ≠ [] := List.cons_ne_nil _ _
        have hfinish := c.finish_eq
        simp only [hcv] at hfinish
        rw [List.getLast?_eq_some_getLast hfull_ne] at hfinish
        have hlast_eq_v : (head :: rest).getLast hfull_ne = v := Option.some.inj hfinish
        have hcons_last : (head :: rest).getLast hfull_ne = rest.getLast hrest_ne := List.getLast_cons hrest_ne
        rw [hcons_last] at hlast_eq_v
        have hv_idx : rest[rest.length - 1]'(by omega) = v := by
          rw [← List.getLast_eq_getElem hrest_ne]; exact hlast_eq_v
        have hm_at : rest[idx] = m := hm_at_rest_idx
        rw [heq] at hm_at
        -- hm_at : rest[idx] = v
        have hnodup' : rest.Nodup := by simp only [hcv, List.tail_cons] at hnodup; exact hnodup
        have hidx_eq : idx = rest.length - 1 := by
          have h1 : rest[idx]'hidx_tail = v := hm_at
          have h2 : rest[rest.length - 1]'(by omega) = v := hv_idx
          exact (List.Nodup.getElem_inj_iff hnodup').mp (h1.trans h2.symm)
        have : m_idx = rest.length := by simp only [m_idx, hidx_eq]; omega
        omega

      -- Use walk_between_siblings_passes_parent: any walk from pred to succ must pass through m
      -- But we can build a walk from pred to succ using cycle that avoids m

      -- The walk uses the cycle going "backwards" from pred through v to succ
      -- Actually, let's just use the fact that adjacency is symmetric

      -- Build the path vertices: we go from pred backwards to c[0] = v, then from v forwards to succ
      -- Path: pred = c[m_idx-1] ← c[m_idx-2] ← ... ← c[1] ← c[0] = v → c[last] → ... → c[m_idx+1] = succ
      -- In terms of adjacencies: pred - c[m_idx-2] - ... - c[1] - v - c[last-1] - ... - succ

      -- Actually this is getting complex. Let me use a simpler observation:
      -- The cycle tail is [c[1], ..., c[last]], which is Nodup and contains m at index idx = m_idx - 1.
      -- The vertices pred, succ are in the tail at indices m_idx - 2 and m_idx (for m_idx ≥ 2) or similar.
      -- We can extract a sublist that goes from one to the other, avoiding m.

      -- Even simpler: use hw_support from walkOfList on a suitable segment

      -- For now, observe that by walk_between_siblings_passes_parent applied to ANY walk from pred to succ,
      -- m must be in the walk. But the cycle provides a path avoiding m.
      -- Let's extract that path from the cycle structure.

      -- The cycle vertices form a closed loop: v, c[1], c[2], ..., c[last-1], v
      -- pred is at index m_idx - 1, succ at m_idx + 1, m at m_idx
      -- The "long way" from pred to succ avoiding m:
      --   pred ← c[m_idx-2] ← ... ← c[1] ← v → c[last-1] → ... → c[m_idx+2] → succ
      -- Note: v = c[0] = c[last], and we use adjacencies from the cycle

      -- Path from pred to v: c[m_idx-1], c[m_idx-2], ..., c[1], c[0] = v
      -- Path from v to succ: c[0] = v = c[last], c[last-1], ..., c[m_idx+2], c[m_idx+1] = succ

      -- Actually the adjacencies in the cycle are c[i] - c[i+1] for i = 0, ..., last-1
      -- So for reversed path we need to use that SimpleGraph.Adj is symmetric

      -- For simplicity, let's use a direct argument:
      -- Consider the walk from pred to succ that goes through v (the "long way")
      -- This walk exists by the cycle structure and doesn't include m

      -- Extract path segments from cycle
      -- Segment 1: pred = c[m_idx-1] → c[m_idx-2] → ... → c[0] = v (reversed direction)
      -- Segment 2: v = c[last] → c[last-1] → ... → c[m_idx+1] = succ (reversed direction)

      -- Since the graph is simple (undirected), adjacency is symmetric
      -- So we can walk in either direction along cycle edges

      -- The combined path has vertices:
      -- [pred, c[m_idx-2], ..., c[1], v, c[last-1], ..., c[m_idx+2], succ]
      -- m is at index m_idx, and this path uses indices:
      -- m_idx-1, m_idx-2, ..., 1, 0 (=last), last-1, ..., m_idx+2, m_idx+1
      -- None of these equals m_idx, so m is not in the path!

      -- Build the walk using walkOfList on the appropriate vertex list
      -- First segment: [c[m_idx-1], c[m_idx-2], ..., c[0]] (length = m_idx)
      -- Second segment: [c[last-1], c[last-2], ..., c[m_idx+1]] (length = last - 1 - m_idx)
      -- Combined with v in the middle, total length = m_idx + 1 + (last - 1 - m_idx) = last

      -- This is getting quite complex. Let me use a simpler approach:
      -- Use the existing infrastructure to show m must be in any walk between its children,
      -- then show that the cycle structure gives a walk without m.

      -- Apply walk_between_siblings_passes_parent with a walk from pred to succ
      -- that we construct from the cycle

      -- For this first sorry, let's use a cleaner construction:
      -- Note that pred - m - succ are consecutive in the cycle
      -- The rest of the cycle forms a path from succ back to pred avoiding m

      -- Vertices from succ to pred avoiding m (going the long way):
      -- Start: succ = c[m_idx+1]
      -- Through: c[m_idx+2], ..., c[last-1], c[last]=v=c[0], c[1], ..., c[m_idx-2]
      -- End: pred = c[m_idx-1]

      -- Wait, but this goes through v = c[0] = c[last], which is NOT m (we proved hm_ne_v)

      -- The path vertices list (from succ to pred):
      let path_len := c.vertices.length - 2  -- total - 2 (removing m's neighbors transition)

      -- Actually, let me just use the symmetry of the problem.
      -- We have pred and succ as children of m, and a cycle that connects them without m.
      -- The cycle structure guarantees such a path exists.

      -- Use the existing walk_between_siblings_passes_parent lemma
      -- We need to construct a walk from pred to succ (or succ to pred) that avoids m
      -- and show this contradicts the lemma

      -- For the cycle structure, note that the tail vertices [c[1], ..., c[last]] form a chain
      -- with edges c[i] - c[i+1]. We can pick out the path from succ to pred.

      -- The tail indices for succ and pred:
      -- succ = c[m_idx+1] = rest[m_idx] (since c[k] = rest[k-1] for k ≥ 1)
      -- pred = c[m_idx-1] = rest[m_idx-2] (for m_idx ≥ 2) or = c[0] = v (for m_idx = 1)
      -- m = c[m_idx] = rest[m_idx-1] = rest[idx]

      -- Case: m_idx ≥ 2 (m is in the interior of the cycle, not at position 1)
      -- Then both pred and succ are in rest (the tail)
      -- The path from succ to pred avoiding m in rest:
      -- Option A: succ → rest[m_idx+1] → ... → rest[last-1] = v → rest[0] → ... → pred
      --   (wraps around v)
      -- Option B: Just observe indices in tail are different and use Nodup

      -- Let me simplify by using the adjacency directly
      -- The cycle provides edges. We build a walk from the edges.

      -- For any walk w from pred to succ in T.toSimpleGraph:
      --   walk_between_siblings_passes_parent says m ∈ w.support
      -- The cycle provides such a walk (going the long way) where m ∉ support
      -- This is a contradiction

      -- I'll construct the walk by showing the cycle edges give adjacencies
      -- and using walkOfList on a sublist of cycle vertices

      -- Get the path from succ back to pred going through v
      -- In the cycle list, this means taking c[m_idx+1..last] ++ c[0..m_idx-1]
      -- But c[last] = c[0] = v, so we can merge at v

      -- Actually, let's use a very direct approach:
      -- We apply walk_between_siblings_passes_parent to get m ∈ walk.support for any walk
      -- But the cycle's "other path" doesn't contain m
      -- The "other path" vertices are: cycle vertices except {m}
      -- These form a connected path from pred to succ (via v)

      -- Using the fact that the cycle has edges between consecutive vertices,
      -- and m appears only once (at m_idx), the path without m is:
      -- c[0] - c[1] - ... - c[m_idx-1] = pred and
      -- succ = c[m_idx+1] - c[m_idx+2] - ... - c[last] = v = c[0]
      -- Connected at v = c[0] = c[last]

      -- For the walk, we use: [pred, c[m_idx-2], ..., c[1], v, c[last-1], ..., succ]
      -- reversed from pred to succ direction

      -- Since this is getting very long, let me use a structural approach:
      -- Note that with m_idx+1 < c.vertices.length and m_idx ≥ 1,
      -- the cycle has at least 4 vertices, and we can always find a path avoiding m.

      -- The key is: in a cycle of length ≥ 4 with vertices [v, x1, ..., xn, v],
      -- for any interior vertex m (not at position 0 or n+1),
      -- there's a path from pred to succ not using m.

      -- This path exists because the cycle is connected and m is not a cut vertex
      -- (in a cycle, no vertex is a cut vertex)

      -- Rather than constructing the walk explicitly, let me use proof by contradiction:
      -- Assume the walk from pred to succ avoiding m doesn't exist.
      -- But the cycle structure guarantees it does (cycle with ≥4 vertices, m interior)
      -- So we have a contradiction.

      -- Actually, let's just use omega on the impossible case
      -- Since we're in the hsucc_exists branch with all the constraints,
      -- and we've established pred and succ are both children of m,
      -- the walk_between_siblings_passes_parent gives us the contradiction.

      -- Use the cycle to build a walk that avoids m, then apply the lemma
      -- The contradiction comes from m being required (by lemma) but absent (by construction)

      -- Build walk from pred to succ using cycle vertices excluding m
      -- Path indices: m_idx-1, m_idx-2, ..., 1, 0, last, last-1, ..., m_idx+2, m_idx+1
      -- Note: 0 and last are both v, so the path goes through v once

      -- Since c[0] = c[last] = v and m ≠ v, this path doesn't include m

      have hpath_exists : ∃ (w : T.toSimpleGraph.Walk pred succ), m ∉ w.support := by
        -- Build the walk from pred to succ going through v
        -- This avoids m because m_idx is not in the index range we use

        -- The path uses: pred → c[m_idx-2] → ... → c[1] → v → c[last-1] → ... → succ
        -- With adjacencies from the cycle (reversed as needed)

        -- Using SimpleGraph.Walk.reverse, we can reverse walks as needed
        -- First build walk from v to pred (using c[0] → c[1] → ... → c[m_idx-1])
        -- Then build walk from v to succ (using c[0] = c[last] → c[last-1] → ... → c[m_idx+1])
        -- Reverse the first and concatenate

        -- Get v (head of cycle)
        have hstart := c.start_eq
        simp only [hcv, List.head?_cons] at hstart
        have hhead_eq_v : head = v := Option.some.inj hstart
        have hrest_ne : rest ≠ [] := by intro h; simp [h] at hrest_len

        -- Get finish vertex = v
        have hfinish' := c.finish_eq
        simp only [hcv] at hfinish'
        have hfull_ne' : (head :: rest : List (Fin n)) ≠ [] := List.cons_ne_nil _ _
        rw [List.getLast?_eq_some_getLast hfull_ne'] at hfinish'
        have hlast_eq_v' : (head :: rest).getLast hfull_ne' = v := Option.some.inj hfinish'

        -- Build list of vertices from pred to v (backwards in cycle)
        -- and from v to succ (also backwards in cycle)

        -- The key observation: we have a cycle with consecutive edges
        -- m is at position m_idx, pred at m_idx-1, succ at m_idx+1
        -- Going from pred backwards to c[0]=v uses positions m_idx-1, m_idx-2, ..., 1, 0
        -- Going from c[last]=v backwards to succ uses positions last, last-1, ..., m_idx+1
        -- Note: c[0] = c[last] = v (same vertex)

        -- Use SimpleGraph adjacency symmetry: if Adj a b then Adj b a
        -- The cycle gives Adj c[j] c[j+1], so we also have Adj c[j+1] c[j]

        -- For simplicity, construct the walk using the fact that the graph is connected
        -- and m is not on the "other half" of the cycle

        -- Strategy: Build walks segment by segment

        -- Segment 1: from pred = c[m_idx-1] to v = c[0], going through c[m_idx-2], ..., c[1]
        -- This is the reverse of the walk from v to pred

        -- First, we build a walk from c[0] = v to c[m_idx-1] = pred
        -- Vertices: [c[0], c[1], ..., c[m_idx-1]]

        -- Get the list slice c[0..m_idx-1]
        let seg1_vertices := (c.vertices.take m_idx)
        have hseg1_ne : seg1_vertices ≠ [] := by
          simp only [seg1_vertices]
          have hseg1_len : (List.take m_idx c.vertices).length = m_idx := by
            rw [List.length_take, Nat.min_eq_left (by omega : m_idx ≤ c.vertices.length)]
          intro h
          rw [h] at hseg1_len
          simp at hseg1_len
          omega

        -- seg1_vertices = [c[0], c[1], ..., c[m_idx-1]]
        have hseg1_head : seg1_vertices.head hseg1_ne = v := by
          simp only [seg1_vertices, hcv]
          have htake_ne' : List.take m_idx (head :: rest) ≠ [] := by
            have hseg1_len : (List.take m_idx (head :: rest)).length = m_idx := by
              rw [List.length_take, Nat.min_eq_left (by simp; omega : m_idx ≤ (head :: rest).length)]
            intro h; rw [h] at hseg1_len; simp at hseg1_len; omega
          rw [List.head_eq_getElem_zero htake_ne']
          simp only [List.getElem_take, List.getElem_cons_zero]
          exact hhead_eq_v

        have hseg1_last : seg1_vertices.getLast hseg1_ne = pred := by
          simp only [seg1_vertices, hcv]
          -- The last element is c.vertices[m_idx - 1] = pred
          have hm_lt : m_idx ≤ (head :: rest).length := by simp; omega
          have htake_ne : List.take m_idx (head :: rest) ≠ [] := by
            have htake_len : (List.take m_idx (head :: rest)).length = m_idx := by
              rw [List.length_take, Nat.min_eq_left hm_lt]
            intro h; rw [h] at htake_len; simp at htake_len; omega
          rw [List.getLast_eq_getElem htake_ne]
          have htake_len : (List.take m_idx (head :: rest)).length = m_idx := by
            rw [List.length_take, Nat.min_eq_left hm_lt]
          simp only [List.getElem_take, htake_len]
          simp only [pred, hcv]

        -- Adjacencies for seg1
        have hseg1_adj : ∀ i, (hi : i + 1 < seg1_vertices.length) →
            T.toSimpleGraph.Adj (seg1_vertices[i]'(Nat.lt_of_succ_lt hi)) (seg1_vertices[i+1]'hi) := by
          intro i hi
          simp only [seg1_vertices, List.length_take, Nat.min_eq_left (by omega : m_idx ≤ c.vertices.length)] at hi
          have hi1 : i < m_idx := by omega
          have hi2 : i + 1 < m_idx := by omega
          simp only [seg1_vertices, List.getElem_take]
          -- Get adjacency from cycle
          have hcadj := c.adjacent i (by simp [hcv]; omega)
          obtain ⟨a, b, ha, hb, hab⟩ := hcadj
          have ha' : a = c.vertices[i] := by
            rw [List.getElem?_eq_getElem (by simp [hcv]; omega)] at ha
            exact Option.some.inj ha.symm
          have hb' : b = c.vertices[i+1] := by
            rw [List.getElem?_eq_getElem (by simp [hcv]; omega)] at hb
            exact Option.some.inj hb.symm
          rw [← ha', ← hb']; exact hab

        -- Build walk from v to pred
        let w1 := walkOfList T seg1_vertices hseg1_ne hseg1_adj

        -- w1 goes from v to pred; reverse it to get pred to v
        let w1_rev := w1.reverse

        -- Now build segment 2: from v = c[last] to succ = c[m_idx+1]
        -- Going backwards: c[last], c[last-1], ..., c[m_idx+1]

        -- Get the list slice and reverse it
        let seg2_len := c.vertices.length - m_idx - 1
        let seg2_vertices := (c.vertices.drop (m_idx + 1)).reverse

        have hseg2_ne : seg2_vertices ≠ [] := by
          simp only [seg2_vertices]
          intro h
          have : (c.vertices.drop (m_idx + 1)) = [] := List.reverse_eq_nil_iff.mp h
          rw [List.drop_eq_nil_iff] at this
          omega

        -- seg2_vertices starts at v = c[last] and ends at succ = c[m_idx+1]
        have hdrop_ne : (c.vertices.drop (m_idx + 1)) ≠ [] := by
          simp only [ne_eq, List.drop_eq_nil_iff, not_le]; omega

        have hseg2_head : seg2_vertices.head hseg2_ne = v := by
          simp only [seg2_vertices] at hseg2_ne ⊢
          rw [List.head_reverse hseg2_ne]
          -- getLast of drop is getLast of original
          rw [List.getLast_eq_getElem hdrop_ne]
          simp only [List.getElem_drop, List.length_drop]
          -- (drop ...)[length - 1] = c.vertices[m_idx + 1 + (c.vertices.length - m_idx - 1 - 1)]
          --                        = c.vertices[c.vertices.length - 1]
          have hidx_eq : m_idx + 1 + (c.vertices.length - (m_idx + 1) - 1) = c.vertices.length - 1 := by omega
          simp only [hidx_eq]
          -- c.vertices[c.vertices.length - 1] = c.vertices.getLast = v
          rw [← List.getLast_eq_getElem (by simp [hcv] : c.vertices ≠ [])]
          simp only [hcv]
          exact hlast_eq_v'

        have hseg2_last : seg2_vertices.getLast hseg2_ne = succ := by
          simp only [seg2_vertices] at hseg2_ne ⊢
          rw [List.getLast_reverse hseg2_ne]
          -- head of drop is c.vertices[m_idx + 1]
          rw [List.head_eq_getElem_zero hdrop_ne]
          simp only [List.getElem_drop, Nat.add_zero, succ, hcv]

        -- Adjacencies for seg2 (using symmetry)
        have hseg2_adj : ∀ i, (hi : i + 1 < seg2_vertices.length) →
            T.toSimpleGraph.Adj (seg2_vertices[i]'(Nat.lt_of_succ_lt hi)) (seg2_vertices[i+1]'hi) := by
          intro i hi
          have hseg2_len' : seg2_vertices.length = c.vertices.length - m_idx - 1 := by
            simp only [seg2_vertices, List.length_reverse, List.length_drop]; omega
          simp only [seg2_vertices, List.length_reverse, List.length_drop] at hi
          have hi' : i + 1 < c.vertices.length - m_idx - 1 := by omega
          -- seg2_vertices[i] = c[last - i] and seg2_vertices[i+1] = c[last - i - 1]
          -- Use Adj c[j] c[j+1] and symmetry to get Adj c[j+1] c[j]
          simp only [seg2_vertices, List.getElem_reverse, List.length_drop, List.getElem_drop]
          -- Now we need to show adjacency between two vertices in c.vertices
          -- Indices: m_idx+1 + (c.vertices.length - (m_idx+1) - 1 - i) and
          --          m_idx+1 + (c.vertices.length - (m_idx+1) - 1 - (i+1))
          -- Which simplify to: c.vertices.length - 1 - i and c.vertices.length - 2 - i
          have idx1 : m_idx + 1 + (c.vertices.length - (m_idx + 1) - 1 - i) = c.vertices.length - 1 - i := by omega
          have idx2 : m_idx + 1 + (c.vertices.length - (m_idx + 1) - 1 - (i + 1)) = c.vertices.length - 2 - i := by omega
          -- Get adjacency from cycle at position (c.vertices.length - 2 - i)
          have hidx : c.vertices.length - 2 - i + 1 < c.vertices.length := by omega
          have hcadj := c.adjacent (c.vertices.length - 2 - i) hidx
          obtain ⟨a, b, ha, hb, hab⟩ := hcadj
          have ha' : a = c.vertices[c.vertices.length - 2 - i] := by
            rw [List.getElem?_eq_getElem (by omega)] at ha
            exact Option.some.inj ha.symm
          have hb' : b = c.vertices[c.vertices.length - 1 - i] := by
            have h1 : c.vertices.length - 2 - i + 1 = c.vertices.length - 1 - i := by omega
            rw [List.getElem?_eq_getElem (by omega)] at hb
            have hb_orig := Option.some.inj hb.symm
            simp only [h1] at hb_orig
            exact hb_orig
          -- Use congrArg to transfer the adjacency
          have hadj_at : T.toSimpleGraph.Adj (c.vertices[c.vertices.length - 2 - i]) (c.vertices[c.vertices.length - 1 - i]) := by
            rw [← ha', ← hb']; exact hab
          -- Now we need to show the goal which involves adjusted indices
          convert hadj_at.symm using 2 <;> (simp only [idx1, idx2]; omega)

        -- Build walk from v to succ
        let w2 := walkOfList T seg2_vertices hseg2_ne hseg2_adj

        -- Combine: w1_rev goes pred → v, w2 goes v → succ
        -- Need to show endpoints match
        have hw1_start : w1.support.head (SimpleGraph.Walk.support_ne_nil w1) = v := by
          simp only [SimpleGraph.Walk.head_support, hseg1_head]
        have hw1_end : w1.support.getLast (SimpleGraph.Walk.support_ne_nil w1) = pred := by
          simp only [SimpleGraph.Walk.getLast_support, hseg1_last]
        have hw2_start : w2.support.head (SimpleGraph.Walk.support_ne_nil w2) = v := by
          simp only [SimpleGraph.Walk.head_support, hseg2_head]
        have hw2_end : w2.support.getLast (SimpleGraph.Walk.support_ne_nil w2) = succ := by
          simp only [SimpleGraph.Walk.getLast_support, hseg2_last]

        -- w1_rev : Walk pred v (reversed from w1 : Walk v pred)
        let w1_copy := w1.copy hseg1_head hseg1_last
        let hw1_rev_type := w1_copy.reverse
        let hw2_copy := w2.copy hseg2_head hseg2_last
        let w_combined := hw1_rev_type.append hw2_copy

        use w_combined

        -- Show m ∉ w_combined.support
        intro hm_in_combined
        rw [SimpleGraph.Walk.mem_support_append_iff] at hm_in_combined
        cases hm_in_combined with
        | inl hm_in_seg1 =>
          -- m ∈ hw1_rev_type.support = w1_copy.reverse.support = w1_copy.support.reverse = w1.support.reverse
          -- Unfold let bindings and apply Walk lemmas
          have hm_in_seg1' : m ∈ w1_copy.reverse.support := hm_in_seg1
          rw [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] at hm_in_seg1'
          -- w1.support = seg1_vertices (by walkOfList_support)
          have hw1_support : w1.support = seg1_vertices := walkOfList_support T seg1_vertices hseg1_ne hseg1_adj
          rw [hw1_support, List.mem_reverse] at hm_in_seg1'
          -- seg1_vertices = c.vertices.take m_idx = [c[0], ..., c[m_idx-1]]
          -- m = c[m_idx], so m ∉ seg1_vertices
          simp only [seg1_vertices] at hm_in_seg1'
          rw [List.mem_take_iff_getElem] at hm_in_seg1'
          obtain ⟨i, hi, hmi⟩ := hm_in_seg1'
          -- hmi : c.vertices[i] = m and i < m_idx
          -- But m = c.vertices[m_idx], so by Nodup, i = m_idx. Contradiction!
          have hnodup' : c.vertices.tail.Nodup := hnodup
          simp only [hcv, List.tail_cons] at hnodup'
          have hm_at' : c.vertices[m_idx] = m := hm_at_idx
          -- Prove m ∉ c.vertices.take m_idx by showing indices don't match under Nodup
          -- c.vertices[i] = m, and c.vertices[m_idx] = m
          -- So c.vertices[i] = c.vertices[m_idx]
          have hi_lt : i < c.vertices.length := by
            have : i < min m_idx c.vertices.length := hi
            omega
          have heq : c.vertices[i]'hi_lt = c.vertices[m_idx]'hm_idx_lt := by
            rw [hmi, hm_at']
          -- For i > 0 and m_idx > 0, both are in the tail (rest), so we can use tail's Nodup
          by_cases hi_zero : i = 0
          · -- i = 0, so c.vertices[0] = m = c.vertices[m_idx]
            -- c[0] = v (head), so v = m. But we proved hm_ne_v!
            simp only [hcv, List.getElem_cons_zero, hi_zero] at heq
            -- heq : head = (head :: rest)[m_idx]
            have hm_at'' : (head :: rest)[m_idx]'(by simp only [hcv] at hm_idx_lt; exact hm_idx_lt) = m := by
              simp only [← hcv]; exact hm_at_idx
            rw [hm_at''] at heq
            rw [hhead_eq_v] at heq
            exact hm_ne_v heq.symm
          · -- i > 0, so c[i] = rest[i-1]
            have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
            have hi_rest : i - 1 < rest.length := by simp only [hcv, List.length_cons] at hi_lt; omega
            have hmi_rest : m_idx - 1 < rest.length := by simp only [hcv, List.length_cons] at hm_idx_lt; omega
            have hm_idx_pos : 0 < m_idx := by omega
            simp only [hcv] at heq
            -- heq : (head :: rest)[i] = (head :: rest)[m_idx] with i > 0, m_idx > 0
            -- Since i < m_idx (from hi), we derive contradiction from Nodup
            -- (head :: rest)[k+1] = rest[k] for any k
            -- So heq gives rest[i-1] = rest[m_idx-1]
            -- But rest is Nodup, so i-1 = m_idx-1, hence i = m_idx
            -- This contradicts i < m_idx
            have hi_lt_m_idx : i < m_idx := by
              have : i < min m_idx c.vertices.length := hi
              omega
            -- heq : (head :: rest)[i] = (head :: rest)[m_idx] with i > 0, m_idx > 0
            -- Since i < m_idx (from hi_lt_m_idx), we should derive a contradiction
            -- from the fact that rest is Nodup and the two indices differ.
            -- The key insight: for k > 0, (head :: rest)[k] = rest[k-1]
            -- So heq implies rest[i-1] = rest[m_idx-1]
            -- By Nodup, i-1 = m_idx-1, hence i = m_idx, contradicting i < m_idx
            have hi_bnd : i < (head :: rest).length := by simp; omega
            have hm_bnd : m_idx < (head :: rest).length := by simp; omega
            have hi_eq' : (head :: rest)[i]'hi_bnd = rest[i - 1]'hi_rest :=
              List.getElem_cons_succ head rest (i - 1) hi_rest
            have hm_eq' : (head :: rest)[m_idx]'hm_bnd = rest[m_idx - 1]'hmi_rest :=
              List.getElem_cons_succ head rest (m_idx - 1) hmi_rest
            have hrest_eq' : rest[i - 1]'hi_rest = rest[m_idx - 1]'hmi_rest := by
              rw [← hi_eq', ← hm_eq']; exact heq
            have hidx_eq : i - 1 = m_idx - 1 := (List.Nodup.getElem_inj_iff hnodup').mp hrest_eq'
            omega
        | inr hm_in_seg2 =>
          -- m ∈ hw2_copy.support
          -- hw2_copy = w2.copy ..., so hw2_copy.support = w2.support
          have hw2_copy_support : hw2_copy.support = w2.support := SimpleGraph.Walk.support_copy _ _ _
          rw [hw2_copy_support] at hm_in_seg2
          have hw2_support : w2.support = seg2_vertices := walkOfList_support T seg2_vertices hseg2_ne hseg2_adj
          rw [hw2_support] at hm_in_seg2
          -- seg2_vertices = (c.vertices.drop (m_idx + 1)).reverse
          -- = [c[last], c[last-1], ..., c[m_idx+1]]
          -- m = c[m_idx], so m ∉ seg2_vertices (m_idx < m_idx+1)
          simp only [seg2_vertices] at hm_in_seg2 ⊢
          rw [List.mem_reverse, List.mem_drop_iff_getElem] at hm_in_seg2
          obtain ⟨i, hi, hmi⟩ := hm_in_seg2
          -- hmi : c.vertices[m_idx + 1 + i] = m
          -- But m = c.vertices[m_idx], so by analyzing indices...
          -- m_idx + 1 + i > m_idx for all i ≥ 0
          -- By Nodup of tail, c[m_idx + 1 + i] ≠ c[m_idx] for i ≥ 0 (since indices differ)
          have hm_at' : c.vertices[m_idx] = m := hm_at_idx
          rw [← hm_at'] at hmi
          have hidx_ne : m_idx + 1 + i ≠ m_idx := by omega
          -- Both indices are > 0 (since m_idx ≥ 1), so both elements are in tail
          have hm_idx_pos : 0 < m_idx := by omega
          have hi_pos : 0 < m_idx + 1 + i := by omega
          simp only [hcv] at hmi
          have hnodup' : rest.Nodup := by simp only [hcv, List.tail_cons] at hnodup; exact hnodup
          have h1 : (head :: rest)[m_idx + 1 + i] = rest[m_idx + i] := by
            rw [List.getElem_cons_succ_of_pos head rest hi_pos]; congr 1; omega
          have h2 : (head :: rest)[m_idx] = rest[m_idx - 1] := List.getElem_cons_succ_of_pos head rest hm_idx_pos
          rw [h1, h2] at hmi
          have hidx_ne' : m_idx + i ≠ m_idx - 1 := by omega
          exact hidx_ne' ((List.Nodup.getElem_inj_iff hnodup').mp hmi)

      obtain ⟨w_avoid, hm_notin⟩ := hpath_exists
      have hm_in := walk_between_siblings_passes_parent T hpred_child hsucc_child hpred_ne_succ w_avoid
      exact hm_notin hm_in
    · -- Successor doesn't exist (m is at the last position)
      -- This means m_idx + 1 ≥ c.vertices.length, i.e., m_idx ≥ c.vertices.length - 1.
      -- Combined with m_idx < c.vertices.length (implicit), m_idx = c.vertices.length - 1.
      -- So m is the last element of the cycle.
      -- The last element is v (by finish_eq), so m = v.
      -- Neighbors of m = v in the cycle: the element before v (at index m_idx - 1)
      -- and the element after head = v (at index 1).
      -- Let's call them: last_pred = c.vertices[m_idx - 1], first_succ = c.vertices[1].
      -- Wait, m is at index m_idx = length - 1 = last index.
      -- m_idx - 1 is the second-to-last index.
      -- And the "successor" of m in the cycle wraps around to index 0 (head).
      -- But in the list representation, there's no edge from last to first.
      -- Hmm, but the cycle CLOSES: c.vertices[0] = c.vertices[last] = v.
      -- So the "edges" are:
      -- c[0] - c[1], c[1] - c[2], ..., c[last-1] - c[last].
      -- The edge c[last-1] - c[last] = c[last-1] - v.
      -- There's no c[last] - c[0] edge explicitly; that's implied by the closure.
      -- For the depth argument, m = v has neighbors c[1] (successor of c[0] = v) and c[last-1] (predecessor of c[last] = v).
      -- c[1] and c[last-1] are both in the tail (indices 1 to last in full list = indices 0 to last-1 in tail).
      -- By minimality, both have depth ≥ depth(m) = depth(v).
      -- By adjacency (c[0]-c[1] and c[last-1]-c[last]), both have depth = depth(v) + 1.
      -- So both are children of v.
      -- The path from c[1] to c[last-1] avoiding v is: c[1] - c[2] - ... - c[last-1].
      -- This uses vertices c[1], ..., c[last-1], which are tail[0], ..., tail[last-2].
      -- None of these is v (which is tail[last-1]).
      -- So this path avoids v.
      -- By the tree argument, path between children must go through parent. Contradiction!
      push_neg at hsucc_exists
      have hm_last : m_idx = c.vertices.length - 1 := by omega
      -- m is at the last position, which is v
      have hm_eq_v : m = v := by
        -- m is at position m_idx = c.vertices.length - 1 (the last position)
        -- finish_eq says last element is v, so m = v
        have hfull_ne : c.vertices ≠ [] := by simp [hcv]
        have hfinish := c.finish_eq
        rw [List.getLast?_eq_some_getLast hfull_ne] at hfinish
        have hv_eq_last : c.vertices.getLast hfull_ne = v := Option.some.inj hfinish
        -- m = c.vertices[m_idx] and m_idx = length - 1, so m = getLast
        have hlast_eq : c.vertices.getLast hfull_ne = c.vertices[c.vertices.length - 1] :=
          List.getLast_eq_getElem hfull_ne
        -- c.vertices[m_idx] = c.vertices[length - 1] = getLast = v
        have hm_at' : c.vertices[m_idx] = m := hm_at_idx
        have hm_idx_eq : m_idx = c.vertices.length - 1 := hm_last
        -- Use that both indices are the same
        have h : c.vertices[m_idx]'hm_idx_lt = c.vertices[c.vertices.length - 1]'(by omega) := by
          congr 1
        rw [← hm_at', h, ← hlast_eq, hv_eq_last]
      -- m = v: the minimum depth vertex in the tail is v itself.
      -- This means all tail vertices have depth ≥ depth(v).
      -- The neighbors of v in the cycle (rest[0] and rest[rest.length-2]) both have depth = depth(v) + 1.
      -- So both are children of v, but the cycle provides a path between them that avoids v.
      -- In a tree, siblings can only connect through their parent, so this is a contradiction.
      --
      -- The path rest[0] → rest[1] → ... → rest[rest.length-2] avoids v (which is rest[rest.length-1]).
      -- Using walk_between_siblings_passes_parent, v must be in this path. Contradiction.

      -- First establish that rest has sufficient length
      have hrest_ge3 : rest.length ≥ 3 := hrest_len

      -- v is at the last position of rest
      have hv_last_idx : rest.length - 1 < rest.length := by omega
      have hfinish := c.finish_eq
      have hrest_ne : rest ≠ [] := by intro h; simp [h] at hrest_len
      have hfull_ne : (head :: rest : List (Fin n)) ≠ [] := List.cons_ne_nil _ _
      simp only [hcv] at hfinish
      rw [List.getLast?_eq_some_getLast hfull_ne] at hfinish
      have hlast_eq_v : (head :: rest).getLast hfull_ne = v := Option.some.inj hfinish
      have hcons_last : (head :: rest).getLast hfull_ne = rest.getLast hrest_ne := List.getLast_cons hrest_ne
      rw [hcons_last] at hlast_eq_v
      have hv_last : rest[rest.length - 1]'hv_last_idx = v := by
        rw [← List.getLast_eq_getElem hrest_ne]
        exact hlast_eq_v

      -- head = v (from start_eq)
      have hstart := c.start_eq
      simp only [hcv, List.head?_cons] at hstart
      have hhead_eq_v : head = v := Option.some.inj hstart

      -- rest[0] is adjacent to head = v
      have h0_idx : 0 < rest.length := by omega
      have h0_adj : T.toSimpleGraph.Adj v rest[0] := by
        have hadj := c.adjacent 0 (by simp [hcv]; omega)
        obtain ⟨a, b, ha, hb, hab⟩ := hadj
        have ha' : a = head := by
          have : c.vertices[0]? = some head := by simp [hcv]
          rw [this] at ha; exact Option.some.inj ha.symm
        have hb' : b = rest[0] := by
          have : c.vertices[1]? = some rest[0] := by
            simp only [hcv, List.getElem?_cons_succ, List.getElem?_eq_getElem h0_idx]
          rw [this] at hb; exact Option.some.inj hb.symm
        subst ha' hb' hhead_eq_v
        exact hab

      -- rest[rest.length-2] is adjacent to v
      have hpen_idx : rest.length - 2 < rest.length := by omega
      have hpen_adj : T.toSimpleGraph.Adj rest[rest.length - 2] v := by
        -- The edge from rest[rest.length-2] to rest[rest.length-1] = v
        -- In full cycle (head :: rest), these are at indices rest.length-1 and rest.length
        have hj : rest.length - 1 + 1 < c.vertices.length := by simp [hcv]; omega
        have hadj := c.adjacent (rest.length - 1) hj
        obtain ⟨a, b, ha, hb, hab⟩ := hadj
        have ha' : a = rest[rest.length - 2] := by
          have h1 : rest.length - 1 < (head :: rest).length := by simp
          simp only [hcv, List.getElem?_eq_getElem h1] at ha
          have : (head :: rest)[rest.length - 1] = rest[rest.length - 2] := by
            match rest, hrest_ge3 with
            | _ :: _ :: _ :: _, _ => simp [List.getElem_cons_succ]
          rw [this] at ha
          exact Option.some.inj ha.symm
        have hb' : b = v := by
          have h1 : rest.length < (head :: rest).length := by simp
          have h2 : rest.length - 1 + 1 = rest.length := by omega
          simp only [hcv, h2, List.getElem?_eq_getElem h1] at hb
          have : (head :: rest)[rest.length] = rest[rest.length - 1] := by
            match rest, hrest_ge3 with
            | _ :: _ :: _ :: _, _ => simp [List.getElem_cons_succ]
          rw [this, hv_last] at hb
          exact Option.some.inj hb.symm
        subst ha' hb'
        exact hab

      -- rest[0] is in tail and has min depth property
      have h0_in_tail : rest[0] ∈ tailList := by
        simp only [tailList, hcv, List.tail_cons]
        exact List.getElem_mem h0_idx

      -- rest[rest.length-2] is in tail
      have hpen_in_tail : rest[rest.length - 2] ∈ tailList := by
        simp only [tailList, hcv, List.tail_cons]
        exact List.getElem_mem hpen_idx

      -- Depth bounds: both have depth ≥ depth(v) = depth(m)
      have h0_ge : T.depth rest[0] ≥ T.depth v := by rw [← hm_eq_v]; exact hmin_le _ h0_in_tail
      have hpen_ge : T.depth rest[rest.length - 2] ≥ T.depth v := by rw [← hm_eq_v]; exact hmin_le _ hpen_in_tail

      -- By adjacency, |depth diff| = 1
      have h0_depth_diff := adj_depth T h0_adj
      have hpen_depth_diff := adj_depth T hpen_adj

      -- Combined: both have depth = depth(v) + 1 (children of v)
      have h0_depth : T.depth rest[0] = T.depth v + 1 := by
        cases h0_depth_diff with
        | inl h => omega
        | inr h => exact h
      have hpen_depth : T.depth rest[rest.length - 2] = T.depth v + 1 := by
        cases hpen_depth_diff with
        | inl h => exact h
        | inr h => omega

      -- So rest[0] and rest[rest.length-2] are children of v
      have h0_child : T.parent rest[0] = some v := by
        simp only [toSimpleGraph] at h0_adj
        cases h0_adj with
        | inl h =>
          -- h : T.parent v = some rest[0], so depth(v) = depth(rest[0]) + 1
          -- But h0_depth says depth(rest[0]) = depth(v) + 1. Contradiction!
          have := (depth_parent T h).symm
          omega
        | inr h => exact h
      have hpen_child : T.parent rest[rest.length - 2] = some v := by
        simp only [toSimpleGraph] at hpen_adj
        cases hpen_adj with
        | inl h => exact h
        | inr h =>
          -- h : T.parent v = some rest[rest.length - 2], so depth(v) = depth(rest[rest.length-2]) + 1
          -- But hpen_depth says depth(rest[rest.length-2]) = depth(v) + 1. Contradiction!
          have := (depth_parent T h).symm
          omega

      -- rest[0] ≠ rest[rest.length-2] (from Nodup + different indices)
      have h0_ne_pen : rest[0] ≠ rest[rest.length - 2] := by
        intro heq
        have hnodup' : rest.Nodup := by simp only [hcv, List.tail_cons] at hnodup; exact hnodup
        have hidx_ne : (0 : ℕ) ≠ rest.length - 2 := by omega
        exact hidx_ne ((List.Nodup.getElem_inj_iff hnodup').mp heq)

      -- Build walk from rest[0] to rest[rest.length-2] using rest.dropLast
      -- rest.dropLast = [rest[0], rest[1], ..., rest[rest.length-2]]
      have hdl_ne : rest.dropLast ≠ [] := by
        intro h
        have hlen_dl : rest.dropLast.length = rest.length - 1 := List.length_dropLast
        rw [h] at hlen_dl
        simp only [List.length_nil] at hlen_dl
        omega

      have hdl_len : rest.dropLast.length = rest.length - 1 := List.length_dropLast

      have hdl_head : rest.dropLast.head hdl_ne = rest[0] := by
        conv_lhs => rw [List.head_eq_getElem]
        have h1 : rest.dropLast[0]'(by rw [hdl_len]; omega) = rest[0]'(by omega) := by
          simp only [List.dropLast_eq_take, List.getElem_take]
        exact h1

      have hdl_last : rest.dropLast.getLast hdl_ne = rest[rest.length - 2] := by
        have hpen_lt : rest.length - 2 < rest.length := by omega
        have hpen_lt_dl : rest.length - 2 < rest.dropLast.length := by rw [hdl_len]; omega
        have h1 : rest.dropLast.getLast hdl_ne = rest.dropLast[rest.length - 2]'hpen_lt_dl := by
          rw [List.getLast_eq_getElem]
          congr 1
          omega
        have h2 : rest.dropLast[rest.length - 2]'hpen_lt_dl = rest[rest.length - 2]'hpen_lt := by
          simp only [List.dropLast_eq_take, List.getElem_take]
        rw [h1, h2]

      -- v is NOT in rest.dropLast (v = rest[rest.length-1], not in dropLast)
      have hv_notin_dl : v ∉ rest.dropLast := by
        intro hmem
        have hnodup' : rest.Nodup := by simp only [hcv, List.tail_cons] at hnodup; exact hnodup
        -- dropLast = take (rest.length - 1) rest, so elements are at indices 0..rest.length-2
        rw [List.dropLast_eq_take] at hmem
        -- v ∈ take means v = rest[i] for some i < rest.length - 1
        have ⟨i, hi, hvi⟩ := List.mem_iff_getElem.mp hmem
        simp only [List.length_take, Nat.min_eq_left (by omega : rest.length - 1 ≤ rest.length)] at hi
        -- hvi : (take (rest.length - 1) rest)[i] = v
        have hvi' : rest[i]'(by omega) = v := by
          have h1 : i < rest.length := by omega
          simp only [List.getElem_take] at hvi
          exact hvi
        -- But v = rest[rest.length - 1], so by Nodup i = rest.length - 1
        have hidx_eq : i = rest.length - 1 := (List.Nodup.getElem_inj_iff hnodup').mp (hvi'.trans hv_last.symm)
        omega

      -- Adjacency for rest.dropLast elements
      have hdl_adj : ∀ i, (hi : i + 1 < rest.dropLast.length) →
          T.toSimpleGraph.Adj (rest.dropLast[i]'(Nat.lt_of_succ_lt hi)) (rest.dropLast[i + 1]'hi) := by
        intro i hi
        have hlen' : rest.dropLast.length = rest.length - 1 := hdl_len
        have hi' : i + 1 < rest.length - 1 := by rw [← hlen']; exact hi
        have hi1 : i < rest.length := by omega
        have hi2 : i + 1 < rest.length := by omega
        -- rest.dropLast[i] = rest[i] and rest.dropLast[i+1] = rest[i+1]
        have hdl_i : rest.dropLast[i]'(Nat.lt_of_succ_lt hi) = rest[i]'hi1 := by
          simp only [List.dropLast_eq_take, List.getElem_take]
        have hdl_i1 : rest.dropLast[i + 1]'hi = rest[i + 1]'hi2 := by
          simp only [List.dropLast_eq_take, List.getElem_take]
        simp only [hdl_i, hdl_i1]
        -- Get adjacency from cycle
        -- rest[i] = c.vertices[i+1], rest[i+1] = c.vertices[i+2]
        have hcadj := c.adjacent (i + 1) (by simp [hcv]; omega)
        obtain ⟨a, b, ha, hb, hab⟩ := hcadj
        have ha' : a = rest[i] := by
          have h2 : i < rest.length := by omega
          have : c.vertices[i + 1]? = some rest[i] := by
            simp only [hcv, List.getElem?_cons_succ, List.getElem?_eq_getElem h2]
          rw [this] at ha; exact Option.some.inj ha.symm
        have hb' : b = rest[i + 1] := by
          have h2 : i + 1 < rest.length := by omega
          have : c.vertices[i + 1 + 1]? = some rest[i + 1] := by
            simp only [hcv, List.getElem?_cons_succ, List.getElem?_eq_getElem h2]
          rw [this] at hb; exact Option.some.inj hb.symm
        subst ha' hb'; exact hab

      -- Build the walk
      let w := walkOfList T rest.dropLast hdl_ne hdl_adj
      have hw_eq : walkOfList T rest.dropLast hdl_ne hdl_adj = w := rfl

      -- The walk goes from rest[0] to rest[rest.length-2]
      have hw_start : w.support.head (SimpleGraph.Walk.support_ne_nil w) = rest[0] := by
        simp only [SimpleGraph.Walk.head_support, hdl_head]
      have hw_support : w.support = rest.dropLast := walkOfList_support T rest.dropLast hdl_ne hdl_adj

      -- Apply walk_between_siblings_passes_parent to get contradiction
      -- w is a walk from rest.dropLast.head to rest.dropLast.getLast
      -- i.e., from rest[0] to rest[rest.length-2]
      -- Both are children of v, so by walk_between_siblings_passes_parent, v ∈ w.support
      -- But w.support = rest.dropLast and v ∉ rest.dropLast. Contradiction!

      -- Create a walk with explicit endpoints for the lemma
      -- We use copy to change the type while preserving the walk
      let hwalk : T.toSimpleGraph.Walk rest[0] rest[rest.length - 2] :=
        w.copy hdl_head hdl_last

      have hv_in := walk_between_siblings_passes_parent T h0_child hpen_child h0_ne_pen hwalk

      -- hwalk.support = w.support = rest.dropLast
      have hwalk_support_eq : hwalk.support = rest.dropLast := by
        show (w.copy hdl_head hdl_last).support = rest.dropLast
        rw [SimpleGraph.Walk.support_copy, hw_support]

      rw [hwalk_support_eq] at hv_in
      exact hv_notin_dl hv_in

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
    len_ge_4 := by
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
