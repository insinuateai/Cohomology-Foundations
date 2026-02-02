/-
COBOUND: Multi-Agent Coordination Framework
Module: Infrastructure/TreeAuthCoreProofs.lean
Created: February 2026

# TreeAuth Core Proofs — Axiom Elimination Registry
Consolidates axioms from the TreeAuth cluster for systematic elimination.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace TreeAuthCoreProofs

/-! ═══════════════════════════════════════════════════════════════════
    TreeAuth structure (canonical definition)
    ═══════════════════════════════════════════════════════════════════ -/
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

def adjacent (T : TreeAuth n) (i j : Fin n) : Prop :=
  T.parent i = some j ∨ T.parent j = some i

/-! ═══════════════════════════════════════════════════════════════════
    Depth via well-founded recursion on stepsToRoot
    ═══════════════════════════════════════════════════════════════════ -/

/-- The number of steps to reach root from node i -/
noncomputable def stepsToRoot (T : TreeAuth n) (i : Fin n) : ℕ :=
  Nat.find (T.acyclic i)

lemma stepsToRoot_spec (T : TreeAuth n) (i : Fin n) :
    T.parentOrRoot^[T.stepsToRoot i] i = T.root :=
  Nat.find_spec (T.acyclic i)

lemma stepsToRoot_min (T : TreeAuth n) (i : Fin n) (k : ℕ)
    (hk : T.parentOrRoot^[k] i = T.root) : T.stepsToRoot i ≤ k :=
  Nat.find_le hk

lemma stepsToRoot_root (T : TreeAuth n) : T.stepsToRoot T.root = 0 := by
  have h : T.parentOrRoot^[0] T.root = T.root := rfl
  exact Nat.eq_zero_of_le_zero (T.stepsToRoot_min T.root 0 h)

lemma parentOrRoot_of_parent (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) :
    T.parentOrRoot i = p := by
  simp only [parentOrRoot, hp, Option.getD_some]

lemma parentOrRoot_root (T : TreeAuth n) : T.parentOrRoot T.root = T.root := by
  simp only [parentOrRoot, T.root_no_parent, Option.getD_none]

lemma ne_root_of_parent_some (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) :
    i ≠ T.root := by
  intro heq
  rw [heq, T.root_no_parent] at hp
  cases hp

lemma stepsToRoot_pos_of_ne_root (T : TreeAuth n) {i : Fin n} (hi : i ≠ T.root) :
    T.stepsToRoot i > 0 := by
  by_contra h
  push_neg at h
  have hs : T.stepsToRoot i = 0 := Nat.eq_zero_of_le_zero h
  have := T.stepsToRoot_spec i
  rw [hs, Function.iterate_zero, id_eq] at this
  exact hi this

lemma iterate_comm {α : Type*} (f : α → α) (m n : ℕ) (x : α) :
    f^[m] (f^[n] x) = f^[n] (f^[m] x) := by
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]

lemma stepsToRoot_parent (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) :
    T.stepsToRoot i = T.stepsToRoot p + 1 := by
  have hi_ne_root := T.ne_root_of_parent_some hp
  have h_pos := T.stepsToRoot_pos_of_ne_root hi_ne_root
  -- Show p reaches root in (stepsToRoot i - 1) steps
  have hp_reaches : T.parentOrRoot^[T.stepsToRoot i - 1] p = T.root := by
    have hspec := T.stepsToRoot_spec i
    -- Use: f^[k+1] x = f^[k] (f^[1] x) = f^[k] (f x) via iterate_add_apply
    have hstep : T.parentOrRoot^[T.stepsToRoot i] i =
        T.parentOrRoot^[T.stepsToRoot i - 1] (T.parentOrRoot i) := by
      conv_lhs => rw [show T.stepsToRoot i = T.stepsToRoot i - 1 + 1 by omega]
      rw [Function.iterate_add_apply, Function.iterate_one]
    rw [hstep, T.parentOrRoot_of_parent hp] at hspec
    exact hspec
  -- stepsToRoot p ≤ stepsToRoot i - 1
  have hle : T.stepsToRoot p ≤ T.stepsToRoot i - 1 := T.stepsToRoot_min p _ hp_reaches
  -- stepsToRoot p ≥ stepsToRoot i - 1 (by minimality of stepsToRoot i)
  have hge : T.stepsToRoot p ≥ T.stepsToRoot i - 1 := by
    by_contra h
    push_neg at h
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

lemma stepsToRoot_lt_n (T : TreeAuth n) (i : Fin n) : T.stepsToRoot i < n := by
  by_contra h
  push_neg at h
  -- Build sequence: i, parentOrRoot i, parentOrRoot^2 i, ...
  -- First n elements must be distinct (otherwise cycle before root)
  -- But they're in Fin n, so pigeonhole forces repeat
  have hn_pos : 0 < n := Fin.pos i
  -- Prove: elements before root are distinct
  have h_distinct : ∀ a b, a < T.stepsToRoot i → b < T.stepsToRoot i → a < b →
      T.parentOrRoot^[a] i ≠ T.parentOrRoot^[b] i := by
    intro a b ha hb hab heq
    -- If equal, we have a cycle of length (b - a)
    have hcyc : T.parentOrRoot^[b - a] (T.parentOrRoot^[a] i) = T.parentOrRoot^[a] i := by
      calc T.parentOrRoot^[b - a] (T.parentOrRoot^[a] i)
          = T.parentOrRoot^[b - a + a] i := by rw [Function.iterate_add_apply]
        _ = T.parentOrRoot^[b] i := by rw [Nat.sub_add_cancel (le_of_lt hab)]
        _ = T.parentOrRoot^[a] i := heq.symm
    -- But parentOrRoot^[stepsToRoot i - a] reaches root
    have hrea : T.parentOrRoot^[T.stepsToRoot i - a] (T.parentOrRoot^[a] i) = T.root := by
      have hspec := T.stepsToRoot_spec i
      have heq' : T.stepsToRoot i = T.stepsToRoot i - a + a := (Nat.sub_add_cancel (le_of_lt ha)).symm
      rw [heq', Function.iterate_add_apply] at hspec
      exact hspec
    -- Cycle argument: m = b - a, s = stepsToRoot i - a
    let m := b - a
    let s := T.stepsToRoot i - a
    have hm_pos : m > 0 := by simp only [m]; omega
    have hs_pos : s > 0 := by simp only [s]; omega
    -- parentOrRoot^[m*t] x = x for all t
    have iter_cyc : ∀ t, T.parentOrRoot^[m * t] (T.parentOrRoot^[a] i) =
        T.parentOrRoot^[a] i := by
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
    -- Use cycle + reach root contradiction
    -- s = m * (s / m) + s % m, apply iter_cyc to reduce
    have hne_root : T.parentOrRoot^[a] i ≠ T.root := fun heq_root =>
      Nat.not_lt.mpr (T.stepsToRoot_min i a heq_root) ha
    -- If we have a cycle of length m and reach root in s steps, we get a contradiction
    -- Because: root = parentOrRoot^[s] x = parentOrRoot^[s mod m] x
    -- If s mod m = 0: root = x, but x ≠ root
    -- If s mod m > 0: we reach root faster, but then the cycle would have to include root
    -- which contradicts the cycle returning to x ≠ root
    -- Simpler: the cycle means parentOrRoot^[k*m] x = x for all k
    -- So the orbit of x has size dividing m
    -- But root is in the orbit (reached in s steps), so x must reach root
    -- Once at root, we stay at root
    -- So root = parentOrRoot^[s] x = parentOrRoot^[s mod m] x = some element in the orbit before root
    -- But all orbit elements before root are ≠ root, contradiction
    -- Let's just use: if s mod m = 0, contradiction; else reach root faster contradicts minimality
    by_cases hsmod : (T.stepsToRoot i - a) % m = 0
    · -- parentOrRoot^[s] x = root, and s = m * (s/m), so
      -- root = parentOrRoot^[m * (s/m)] x = x (by iter_cyc), contradiction
      have hs_eq : T.stepsToRoot i - a = m * ((T.stepsToRoot i - a) / m) := by
        have := Nat.div_add_mod (T.stepsToRoot i - a) m
        omega
      have hrea' : T.parentOrRoot^[m * ((T.stepsToRoot i - a) / m)] (T.parentOrRoot^[a] i) = T.root := by
        rw [← hs_eq]; exact hrea
      rw [iter_cyc] at hrea'
      exact hne_root hrea'
    · -- s mod m > 0, so we reach root in fewer steps
      have hm_lt_s : m < T.stepsToRoot i - a := by simp only [m]; omega
      have hlt : (T.stepsToRoot i - a) % m < T.stepsToRoot i - a :=
        Nat.lt_of_lt_of_le (Nat.mod_lt _ hm_pos) (le_of_lt hm_lt_s)
      have hdiv : T.stepsToRoot i - a = (T.stepsToRoot i - a) % m + m * ((T.stepsToRoot i - a) / m) := by
        have := Nat.div_add_mod (T.stepsToRoot i - a) m
        omega
      have hrea' : T.parentOrRoot^[(T.stepsToRoot i - a) % m] (T.parentOrRoot^[a] i) = T.root := by
        have key : T.parentOrRoot^[T.stepsToRoot i - a] (T.parentOrRoot^[a] i) = T.root := hrea
        rw [hdiv, Function.iterate_add_apply] at key
        -- key : f^[s%m] (f^[m*(s/m)] x) = root
        -- Use iter_cyc to simplify f^[m*(s/m)] x = x
        simp only [iter_cyc] at key
        exact key
      have hreach : T.parentOrRoot^[a + (T.stepsToRoot i - a) % m] i = T.root := by
        rw [Function.iterate_add_apply, iterate_comm]
        exact hrea'
      have := T.stepsToRoot_min i _ hreach
      omega
  -- Now: stepsToRoot i + 1 distinct elements must fit in Fin n
  have h_root_distinct : ∀ k, k < T.stepsToRoot i → T.parentOrRoot^[k] i ≠ T.root := by
    intro k hk heq_root
    exact Nat.not_lt.mpr (T.stepsToRoot_min i k heq_root) hk
  -- Helper: iterating past stepsToRoot stays at root
  have h_past_root : ∀ k, k ≥ T.stepsToRoot i → T.parentOrRoot^[k] i = T.root := by
    intro k hk
    obtain ⟨d, hd⟩ : ∃ d, k = T.stepsToRoot i + d := ⟨k - T.stepsToRoot i, by omega⟩
    rw [hd, Function.iterate_add_apply, iterate_comm]
    have hspec := T.stepsToRoot_spec i
    rw [hspec]
    clear hk hd hspec h_root_distinct h_distinct hn_pos h
    induction d with
    | zero => rfl
    | succ d ih => rw [Function.iterate_succ_apply, T.parentOrRoot_root, ih]
  -- Pigeonhole: n+1 distinct elements in Fin n is impossible
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

/-! ═══════════════════════════════════════════════════════════════════
    Fuel-based depth (for compatibility with source files)
    ═══════════════════════════════════════════════════════════════════ -/

def depthAux (T : TreeAuth n) (i : Fin n) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 => match T.parent i with
    | none => 0
    | some p => 1 + T.depthAux p fuel

def depth (T : TreeAuth n) (i : Fin n) : ℕ := T.depthAux i n

lemma depthAux_root (T : TreeAuth n) (fuel : ℕ) : T.depthAux T.root fuel = 0 := by
  cases fuel with
  | zero => rfl
  | succ f => simp only [depthAux, T.root_no_parent]

lemma depthAux_parent (T : TreeAuth n) {i p : Fin n} (hp : T.parent i = some p) (fuel : ℕ) :
    T.depthAux i (fuel + 1) = 1 + T.depthAux p fuel := by
  simp only [depthAux, hp]

/-- depthAux agrees with stepsToRoot when fuel is sufficient -/
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
      simp only [depthAux_root]
    | succ s =>
      have hi_ne_root : i ≠ T.root := by
        intro heq
        rw [heq, T.stepsToRoot_root] at hs
        cases hs
      have hpar_some := T.nonroot_has_parent i hi_ne_root
      rw [Option.isSome_iff_exists] at hpar_some
      obtain ⟨p, hp⟩ := hpar_some
      have hsteps_p : T.stepsToRoot p = s := by
        have := T.stepsToRoot_parent hp
        omega
      rw [depthAux_parent T hp, ih p (by omega)]
      omega

lemma depth_eq_stepsToRoot (T : TreeAuth n) (i : Fin n) : T.depth i = T.stepsToRoot i := by
  simp only [depth]
  exact T.depthAux_eq_stepsToRoot i n (le_of_lt (T.stepsToRoot_lt_n i))

/-! ═══════════════════════════════════════════════════════════════════
    THEOREM 1/7 — depth_parent_fuel_analysis
    ═══════════════════════════════════════════════════════════════════ -/

theorem depth_parent_fuel_analysis (T : TreeAuth n) {i p : Fin n}
    (hp : T.parent i = some p) :
    T.depth i = T.depth p + 1 := by
  rw [T.depth_eq_stepsToRoot i, T.depth_eq_stepsToRoot p, T.stepsToRoot_parent hp]

/-! ═══════════════════════════════════════════════════════════════════
    Path to root functions
    ═══════════════════════════════════════════════════════════════════ -/

def pathToRootAux (T : TreeAuth n) (i : Fin n) : ℕ → List (Fin n)
  | 0 => [i]
  | fuel + 1 => match T.parent i with
    | none => [i]
    | some p => i :: T.pathToRootAux p fuel

def pathToRoot (T : TreeAuth n) (i : Fin n) : List (Fin n) := T.pathToRootAux i n

lemma pathToRootAux_head (T : TreeAuth n) (i : Fin n) (fuel : ℕ) :
    (T.pathToRootAux i fuel).head? = some i := by
  cases fuel with
  | zero => rfl
  | succ f =>
    simp only [pathToRootAux]
    cases T.parent i with
    | none => rfl
    | some p => rfl

lemma pathToRootAux_nonempty (T : TreeAuth n) (i : Fin n) (fuel : ℕ) :
    (T.pathToRootAux i fuel).length > 0 := by
  cases fuel with
  | zero => simp [pathToRootAux]
  | succ f =>
    simp only [pathToRootAux]
    cases T.parent i with
    | none => simp
    | some p => simp [List.length_cons]

lemma pathToRootAux_length (T : TreeAuth n) (i : Fin n) (fuel : ℕ)
    (hfuel : fuel ≥ T.stepsToRoot i) :
    (T.pathToRootAux i fuel).length = T.stepsToRoot i + 1 := by
  induction fuel generalizing i with
  | zero =>
    have hs : T.stepsToRoot i = 0 := Nat.eq_zero_of_le_zero hfuel
    simp only [pathToRootAux, List.length_singleton, hs]
  | succ f ih =>
    cases hs : T.stepsToRoot i with
    | zero =>
      have hi_root : i = T.root := by
        have := T.stepsToRoot_spec i
        rw [hs, Function.iterate_zero, id_eq] at this
        exact this
      simp only [pathToRootAux, hi_root, T.root_no_parent, List.length_singleton]
    | succ s =>
      have hi_ne_root : i ≠ T.root := by
        intro heq
        rw [heq, T.stepsToRoot_root] at hs
        cases hs
      have hpar := T.nonroot_has_parent i hi_ne_root
      rw [Option.isSome_iff_exists] at hpar
      obtain ⟨p, hp⟩ := hpar
      have hsteps_p : T.stepsToRoot p = s := by
        have := T.stepsToRoot_parent hp
        omega
      simp only [pathToRootAux, hp, List.length_cons]
      rw [ih p (by omega), hsteps_p]

lemma pathToRoot_length (T : TreeAuth n) (i : Fin n) :
    (T.pathToRoot i).length = T.stepsToRoot i + 1 := by
  simp only [pathToRoot]
  exact T.pathToRootAux_length i n (le_of_lt (T.stepsToRoot_lt_n i))

/-! ═══════════════════════════════════════════════════════════════════
    THEOREM 7/7 — pathToRoot_consecutive_adjacent
    ═══════════════════════════════════════════════════════════════════ -/

lemma pathToRootAux_get_succ (T : TreeAuth n) (i : Fin n) (fuel : ℕ)
    (hfuel : fuel ≥ T.stepsToRoot i) (k : ℕ) (hk : k + 1 < (T.pathToRootAux i fuel).length) :
    ∃ p, T.parent ((T.pathToRootAux i fuel).get ⟨k, by omega⟩) = some p ∧
      (T.pathToRootAux i fuel).get ⟨k + 1, hk⟩ = p := by
  induction fuel generalizing i k with
  | zero =>
    simp only [pathToRootAux, List.length_singleton] at hk
    omega
  | succ f ih =>
    cases hs : T.stepsToRoot i with
    | zero =>
      have hi_root : i = T.root := by
        have := T.stepsToRoot_spec i
        rw [hs, Function.iterate_zero, id_eq] at this
        exact this
      simp only [pathToRootAux, hi_root, T.root_no_parent, List.length_singleton] at hk
      omega
    | succ s =>
      have hi_ne_root : i ≠ T.root := by
        intro heq
        rw [heq, T.stepsToRoot_root] at hs
        cases hs
      have hpar := T.nonroot_has_parent i hi_ne_root
      rw [Option.isSome_iff_exists] at hpar
      obtain ⟨p, hp⟩ := hpar
      have hsteps_p : T.stepsToRoot p = s := by
        have := T.stepsToRoot_parent hp
        omega
      -- pathToRootAux i (f+1) = i :: pathToRootAux p f when parent i = some p
      have hpath : T.pathToRootAux i (f + 1) = i :: T.pathToRootAux p f := by
        simp only [pathToRootAux, hp]
      cases k with
      | zero =>
        -- k = 0: get 0 = i, get 1 = first element of pathToRootAux p f
        use p
        constructor
        · -- parent (get 0) = parent i = some p
          simp only [pathToRootAux, List.get_eq_getElem, List.getElem_cons_zero, hp]
        · -- get 1 = p (first element of pathToRootAux p f)
          simp only [pathToRootAux, hp, List.get_eq_getElem, List.getElem_cons_succ]
          -- Goal: p = (T.pathToRootAux p f)[0]
          -- pathToRootAux starts with the node itself
          have hhead := T.pathToRootAux_head p f
          rw [List.head?_eq_some_iff] at hhead
          obtain ⟨tail, heq⟩ := hhead
          simp only [heq, List.getElem_cons_zero]
      | succ k' =>
        -- k = k' + 1: delegate to ih on p
        have hlen : (T.pathToRootAux i (f + 1)).length = (T.pathToRootAux p f).length + 1 := by
          simp only [pathToRootAux, hp, List.length_cons]
        have hk' : k' + 1 < (T.pathToRootAux p f).length := by
          simp only [pathToRootAux, hp, List.length_cons] at hk
          omega
        obtain ⟨q, hq_parent, hq_eq⟩ := ih p (by omega) k' hk'
        use q
        constructor
        · -- get (k'+1) of (i :: rest) = get k' of rest
          simp only [pathToRootAux, hp, List.get_eq_getElem, List.getElem_cons_succ]
          exact hq_parent
        · -- get (k'+2) of (i :: rest) = get (k'+1) of rest
          simp only [pathToRootAux, hp, List.get_eq_getElem, List.getElem_cons_succ]
          exact hq_eq

theorem pathToRoot_consecutive_adjacent (T : TreeAuth n) (i : Fin n) (k : ℕ)
    (hk : k + 1 < (T.pathToRoot i).length) :
    T.adjacent ((T.pathToRoot i).get ⟨k, by omega⟩)
               ((T.pathToRoot i).get ⟨k + 1, hk⟩) := by
  simp only [pathToRoot] at hk ⊢
  have hfuel : n ≥ T.stepsToRoot i := le_of_lt (T.stepsToRoot_lt_n i)
  obtain ⟨p, hp_parent, hp_eq⟩ := T.pathToRootAux_get_succ i n hfuel k hk
  simp only [adjacent]
  left
  rw [hp_eq]
  exact hp_parent

/-! ═══════════════════════════════════════════════════════════════════
    THEOREM 6/7 — acyclic_periodic_orbit_equiv
    ═══════════════════════════════════════════════════════════════════ -/

/-
Equivalence between "everyone reaches root" and "non-root nodes have no periodic orbits".

Note: The original statement claimed ∀ i, ∀ k > 0, parentOrRoot^[k] i ≠ i, but this is
false for the root (since parentOrRoot root = root). The corrected statement restricts
the RHS to non-root nodes: ∀ i, i ≠ T.root → ∀ k > 0, parentOrRoot^[k] i ≠ i.

Forward: If i ≠ root has a periodic orbit of length k but also reaches root in s steps,
then by modular arithmetic i = root, contradiction.
Backward: Uses T.acyclic (all nodes reach root by definition of TreeAuth).
-/
theorem acyclic_periodic_orbit_equiv (T : TreeAuth n) :
    (∀ i, ∃ k, T.parentOrRoot^[k] i = T.root) ↔
    ∀ i, i ≠ T.root → ∀ k > 0, T.parentOrRoot^[k] i ≠ i := by
  constructor
  · -- Forward: if everyone reaches root, non-root nodes don't have periodic orbits
    intro h_reaches i hi_not_root k hk_pos hcycle
    obtain ⟨s, hs⟩ := h_reaches i
    -- The proof shows: if i has a periodic orbit of length k, but also reaches root,
    -- then i = root (contradiction with hi_not_root)
    have iter_cyc : ∀ t, T.parentOrRoot^[k * t] i = i := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        have heq : k * (t + 1) = k + k * t := by ring
        calc T.parentOrRoot^[k * (t + 1)] i
            = T.parentOrRoot^[k + k * t] i := by rw [heq]
          _ = T.parentOrRoot^[k] (T.parentOrRoot^[k * t] i) := by
              rw [← Function.iterate_add_apply]
          _ = T.parentOrRoot^[k] i := by rw [ih]
          _ = i := hcycle
    -- Use iter_cyc to simplify: parentOrRoot^[s] i = parentOrRoot^[s % k] (parentOrRoot^[k*(s/k)] i)
    have hdiv : s = s % k + k * (s / k) := (Nat.mod_add_div s k).symm
    have hs' : T.parentOrRoot^[s % k] i = T.root := by
      calc T.parentOrRoot^[s % k] i
          = T.parentOrRoot^[s % k] (T.parentOrRoot^[k * (s / k)] i) := by rw [iter_cyc (s / k)]
        _ = T.parentOrRoot^[s % k + k * (s / k)] i := by rw [← Function.iterate_add_apply]
        _ = T.parentOrRoot^[s] i := by rw [← hdiv]
        _ = T.root := hs
    by_cases hsmod : s % k = 0
    · simp only [hsmod, Function.iterate_zero, id_eq] at hs'
      exact hi_not_root hs'
    · have hlt : s % k < k := Nat.mod_lt s hk_pos
      have hstay_root : T.parentOrRoot^[k - s % k] T.root = T.root := by
        clear hcycle hs hs' hdiv hsmod hlt iter_cyc hi_not_root h_reaches
        induction (k - s % k) with
        | zero => rfl
        | succ m ih => rw [Function.iterate_succ_apply', ih, T.parentOrRoot_root]
      have hkeq : k = k - s % k + s % k := (Nat.sub_add_cancel (Nat.le_of_lt hlt)).symm
      have : T.parentOrRoot^[k] i = T.root := by
        conv_lhs => rw [hkeq]
        rw [Function.iterate_add_apply, hs', hstay_root]
      rw [hcycle] at this
      exact hi_not_root this
  · -- Backward: no periodic orbits for non-root nodes → reaches root
    intro _
    exact T.acyclic

/-! ═══════════════════════════════════════════════════════════════════
    Simple Graph from TreeAuth
    ═══════════════════════════════════════════════════════════════════ -/

def edges (T : TreeAuth n) : List (Fin n × Fin n) :=
  (List.finRange n).filterMap fun i =>
    match T.parent i with
    | none => none
    | some p => some (i, p)

def children (T : TreeAuth n) (i : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun j => T.parent j = some i

def toSimpleGraph (T : TreeAuth n) : SimpleGraph (Fin n) where
  Adj i j := T.adjacent i j
  symm := fun _ _ h => by simp only [adjacent] at h ⊢; tauto
  loopless := fun i h => by
    simp only [adjacent] at h
    cases h with
    | inl h => exact T.parent_ne_self i h
    | inr h => exact T.parent_ne_self i h

/-! ═══════════════════════════════════════════════════════════════════
    THEOREM 2/7 — toSimpleGraph_acyclic_aux
    Proof: minimum-depth vertex in cycle leads to contradiction
    ═══════════════════════════════════════════════════════════════════ -/

lemma adjacent_depth (T : TreeAuth n) {i j : Fin n} (hadj : T.adjacent i j) :
    T.depth i = T.depth j + 1 ∨ T.depth j = T.depth i + 1 := by
  simp only [adjacent] at hadj
  cases hadj with
  | inl hi => left; exact T.depth_parent_fuel_analysis hi
  | inr hj => right; exact T.depth_parent_fuel_analysis hj

theorem toSimpleGraph_acyclic_aux (T : TreeAuth n) (v : Fin n)
    (p : T.toSimpleGraph.Walk v v) (hp : p.IsCycle) : False := by
  -- Key insight: In a tree (parent-pointer structure), every vertex except root
  -- has a unique parent. A cycle would require going "down" and "back up" to return,
  -- but the minimum-depth vertex in the cycle has both neighbors deeper,
  -- meaning it's the parent of both - but then the path between those children
  -- must go through their common parent, contradicting the cycle being simple.
  -- Use strong induction on n
  have hlen := hp.three_le_length
  -- For now, use sorry as the full proof requires careful minimum-depth argument
  -- The cycle has support [v, v₁, v₂, ..., vₖ] with v = endpoint
  -- Let m be the vertex with minimum depth in the support (excluding last v)
  -- By IsCycle, support.tail has no repeats, so m appears once in interior
  -- m's two neighbors in the cycle (prev, next) are adjacent to m
  -- adjacent means parent relation, so depth differs by 1
  -- Both prev and next have depth ≥ depth m (m is minimum)
  -- So both have depth = depth m + 1, meaning m is parent of both
  -- But then any path from prev to next in the tree must go through m (their LCA)
  -- The cycle path prev → ... → next avoids m (appears once), contradiction
  sorry

end TreeAuth

end TreeAuthCoreProofs
