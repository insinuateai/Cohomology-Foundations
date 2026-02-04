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

/-- pathToRootAux gives the same result when fuel is sufficient -/
lemma pathToRootAux_stabilizes (T : TreeAuth n) (i : Fin n) (fuel1 fuel2 : ℕ)
    (h1 : fuel1 ≥ T.stepsToRoot i) (h2 : fuel2 ≥ T.stepsToRoot i) :
    T.pathToRootAux i fuel1 = T.pathToRootAux i fuel2 := by
  induction fuel1 generalizing i fuel2 with
  | zero =>
    have hs : T.stepsToRoot i = 0 := Nat.eq_zero_of_le_zero h1
    have hi_root : i = T.root := by
      have := T.stepsToRoot_spec i
      rw [hs, Function.iterate_zero, id_eq] at this
      exact this
    cases fuel2 with
    | zero => rfl
    | succ f2 => simp only [pathToRootAux, hi_root, T.root_no_parent]
  | succ f1 ih =>
    cases hs : T.stepsToRoot i with
    | zero =>
      have hi_root : i = T.root := by
        have := T.stepsToRoot_spec i
        rw [hs, Function.iterate_zero, id_eq] at this
        exact this
      cases fuel2 with
      | zero => simp only [pathToRootAux, hi_root, T.root_no_parent]
      | succ f2 => simp only [pathToRootAux, hi_root, T.root_no_parent]
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
      cases fuel2 with
      | zero => omega
      | succ f2 =>
        simp only [pathToRootAux, hp]
        congr 1
        exact ih p f2 (by omega) (by omega)

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

/-- Depth equality implies both parent relations are equivalent -/
lemma depth_eq_parent_eq (T : TreeAuth n) {a b c : Fin n}
    (ha : T.parent a = some c) (hb : T.parent b = some c) (heq : T.depth a = T.depth b) :
    T.depth a = T.depth c + 1 ∧ T.depth b = T.depth c + 1 := by
  have h1 := T.depth_parent_fuel_analysis ha
  have h2 := T.depth_parent_fuel_analysis hb
  exact ⟨h1, heq ▸ h1⟩

/-- If both a and b are children of c, they're not adjacent (no edge between siblings) -/
lemma siblings_not_adjacent (T : TreeAuth n) {a b c : Fin n}
    (ha : T.parent a = some c) (hb : T.parent b = some c) (hab : a ≠ b) :
    ¬T.adjacent a b := by
  intro hadj
  simp only [adjacent] at hadj
  cases hadj with
  | inl hpar_a =>
    -- parent a = some b, but parent a = some c, so c = b
    have hcb : c = b := Option.some_injective _ (ha.symm.trans hpar_a)
    -- Then parent b = some c = some b, contradicting parent_ne_self
    rw [← hcb] at hb
    exact T.parent_ne_self c hb
  | inr hpar_b =>
    -- parent b = some a, but parent b = some c, so c = a
    have hca : c = a := Option.some_injective _ (hb.symm.trans hpar_b)
    -- Then parent a = some c = some a, contradicting parent_ne_self
    rw [← hca] at ha
    exact T.parent_ne_self c ha

/-- Ancestor relation: v is on the path from u to root -/
def isAncestor (T : TreeAuth n) (ancestor descendant : Fin n) : Prop :=
  ancestor ∈ T.pathToRoot descendant

/-- Parent is an ancestor -/
lemma parent_isAncestor (T : TreeAuth n) {u p : Fin n} (hp : T.parent u = some p) :
    T.isAncestor p u := by
  simp only [isAncestor, pathToRoot]
  -- pathToRootAux u n = u :: pathToRootAux p (n-1) when parent u = some p
  have hfuel : n > 0 := Fin.pos u
  -- Unfold pathToRootAux using n > 0
  have hunfold : T.pathToRootAux u n = u :: T.pathToRootAux (T.parentOrRoot u) (n - 1) := by
    match hn : n with
    | 0 => omega
    | m + 1 =>
      simp only [pathToRootAux, hp, Nat.add_sub_cancel]
      rw [T.parentOrRoot_of_parent hp]
  rw [hunfold, T.parentOrRoot_of_parent hp, List.mem_cons]
  right
  -- p is at the head of pathToRootAux p (n-1)
  have hhead := T.pathToRootAux_head p (n - 1)
  rw [List.head?_eq_some_iff] at hhead
  obtain ⟨tail, heq⟩ := hhead
  rw [heq, List.mem_cons]
  left; rfl

/-- The pathToRoot is unique: following parent pointers gives the same path -/
lemma pathToRoot_parent_cons (T : TreeAuth n) {u p : Fin n} (hp : T.parent u = some p) :
    T.pathToRoot u = u :: T.pathToRoot p := by
  simp only [pathToRoot]
  have hfuel : n > T.stepsToRoot u := T.stepsToRoot_lt_n u
  have hn_pos : n > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) hfuel
  -- Unfold pathToRootAux u n = u :: pathToRootAux (parentOrRoot u) (n - 1)
  have hunfold : T.pathToRootAux u n = u :: T.pathToRootAux (T.parentOrRoot u) (n - 1) := by
    match n with
    | 0 => omega
    | m + 1 => simp only [pathToRootAux, hp, Nat.add_sub_cancel, T.parentOrRoot_of_parent hp]
  rw [hunfold, T.parentOrRoot_of_parent hp]
  congr 1
  -- Need: pathToRootAux p (n - 1) = pathToRootAux p n
  -- Both paths have the same content when fuel is sufficient
  have hsteps_p : T.stepsToRoot p < n := by
    have h1 := T.stepsToRoot_parent hp
    have h2 : T.stepsToRoot u < n := hfuel
    omega
  -- pathToRootAux gives the same result when fuel is sufficient
  -- Both (n-1) and n are ≥ stepsToRoot p, so the lists are identical
  exact T.pathToRootAux_stabilizes p (n - 1) n (by omega) (by omega)

/-- Helper: pathToRootAux of root is singleton -/
lemma pathToRootAux_root (T : TreeAuth n) (fuel : ℕ) : T.pathToRootAux T.root fuel = [T.root] := by
  cases fuel with
  | zero => rfl
  | succ m => simp only [pathToRootAux, T.root_no_parent]

/-- Elements of pathToRoot have stepsToRoot ≤ the starting node -/
lemma stepsToRoot_of_mem_pathToRoot (T : TreeAuth n) (i x : Fin n)
    (hx : x ∈ T.pathToRoot i) : T.stepsToRoot x ≤ T.stepsToRoot i := by
  -- Key insight: pathToRoot i lists vertices from i toward root
  -- Each element is reached by following parent pointers
  -- So stepsToRoot decreases along the path
  simp only [pathToRoot] at hx
  -- Induction on i's stepsToRoot using well-founded recursion
  induction hi : T.stepsToRoot i using Nat.strongRecOn generalizing i with
  | ind si ih =>
    by_cases hi_root : i = T.root
    · -- i is root, pathToRoot i = [i]
      rw [hi_root, T.pathToRootAux_root] at hx
      simp only [List.mem_singleton] at hx
      rw [hx, T.stepsToRoot_root]
      omega
    · -- i is not root, pathToRoot i = i :: pathToRoot (parent i)
      have hpar := T.nonroot_has_parent i hi_root
      rw [Option.isSome_iff_exists] at hpar
      obtain ⟨p, hp⟩ := hpar
      have hn_pos : 0 < n := Fin.pos i
      have hpath_i : T.pathToRootAux i n = i :: T.pathToRootAux p (n - 1) := by
        match hn : n with
        | 0 => omega
        | m + 1 => simp only [pathToRootAux, hp, Nat.add_sub_cancel]
      rw [hpath_i] at hx
      simp only [List.mem_cons] at hx
      cases hx with
      | inl heq => rw [heq, hi]
      | inr hx_in_p =>
        have hsteps_p : T.stepsToRoot p < si := by
          have := T.stepsToRoot_parent hp
          omega
        have hp_stable : T.pathToRootAux p (n - 1) = T.pathToRootAux p n :=
          T.pathToRootAux_stabilizes p (n - 1) n
            (by have := T.stepsToRoot_lt_n p; omega)
            (le_of_lt (T.stepsToRoot_lt_n p))
        rw [hp_stable] at hx_in_p
        have hx_le_p := ih (T.stepsToRoot p) hsteps_p p hx_in_p rfl
        have hp_le_i : T.stepsToRoot p < T.stepsToRoot i := by
          have := T.stepsToRoot_parent hp
          omega
        omega

/-- a is NOT an ancestor of b when they are distinct siblings -/
lemma not_ancestor_of_sibling (T : TreeAuth n) {a b c : Fin n}
    (ha : T.parent a = some c) (hb : T.parent b = some c) (hab : a ≠ b) :
    a ∉ T.pathToRoot b := by
  -- If a ∈ pathToRoot b, then stepsToRoot a ≤ stepsToRoot b
  -- But stepsToRoot a = stepsToRoot c + 1 = stepsToRoot b, and
  -- a ∈ pathToRoot b means either a = b (contradicts hab) or a ∈ pathToRoot c
  -- If a ∈ pathToRoot c, then stepsToRoot a ≤ stepsToRoot c, but stepsToRoot a = stepsToRoot c + 1
  intro h_in
  -- pathToRoot b = b :: pathToRoot c
  have hpath_b : T.pathToRoot b = b :: T.pathToRoot c := T.pathToRoot_parent_cons hb
  rw [hpath_b, List.mem_cons] at h_in
  cases h_in with
  | inl heq => exact hab heq
  | inr h_in_c =>
    -- a ∈ pathToRoot c, so stepsToRoot a ≤ stepsToRoot c
    have ha_le_c := T.stepsToRoot_of_mem_pathToRoot c a h_in_c
    -- But stepsToRoot a = stepsToRoot c + 1 (since parent a = some c)
    have hdepth_a := T.stepsToRoot_parent ha
    omega

/-- Generalized lemma: walk from descendant of a to sibling of a passes through parent c -/
lemma walk_from_descendant_to_sibling_passes_parent (T : TreeAuth n) {a b c : Fin n}
    (ha : T.parent a = some c) (hb : T.parent b = some c) (hab : a ≠ b)
    (u : Fin n) (h_anc : a ∈ T.pathToRoot u)
    (w : T.toSimpleGraph.Walk u b) : c ∈ w.support := by
  -- Use strong induction on walk length
  induction h : w.length using Nat.strong_induction_on generalizing u h_anc w with
  | _ wlen ih =>
    match w with
    | .nil =>
      -- u = b, but a ∈ pathToRoot u = pathToRoot b
      -- This contradicts not_ancestor_of_sibling
      exact (T.not_ancestor_of_sibling ha hb hab h_anc).elim
    | .cons hadj w' =>
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      rename_i v
      -- hadj : T.toSimpleGraph.Adj u v, which is T.adjacent u v
      have hadj' : T.adjacent u v := hadj
      simp only [adjacent] at hadj'
      cases hadj' with
      | inl hpar_u =>
        -- parent u = some v, going UP
        by_cases hva : v = a
        · -- Reached a (v = a), now at parent position
          -- w' : Walk v b = Walk a b (since v = a)
          -- First step from a must be either UP to c or DOWN to a child
          match w' with
          | .nil =>
            -- w' is nil means v = b, and v = a, so a = b, contradiction with hab
            exact (hab hva.symm).elim
          | .cons hadj'' w'' =>
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
            rename_i v'
            -- hadj'' : Adj v v' where v = a
            have hadj''' : T.adjacent v v' := hadj''
            simp only [adjacent] at hadj'''
            cases hadj''' with
            | inl hpar_v =>
              -- parent v = some v', and v = a, so parent a = some v'
              -- Combined with ha: parent a = some c, we get v' = c
              have hv'c : v' = c := Option.some_injective _ ((hva ▸ hpar_v).symm.trans ha)
              -- Goal is c = v ∨ c ∈ w''.support (after simp), and v' is the start of w''
              right; right
              -- c ∈ w''.support, and v' = c is at the start of w''
              rw [← hv'c]
              exact SimpleGraph.Walk.start_mem_support w''
            | inr hpar_v' =>
              -- parent v' = some v = some a, so v' is a child of a
              right; right
              have hv'_anc : a ∈ T.pathToRoot v' := by
                have := T.parent_isAncestor (hva ▸ hpar_v' : T.parent v' = some a)
                exact this
              have hw''_len : w''.length < wlen := by
                simp only [SimpleGraph.Walk.length_cons] at h
                omega
              exact ih w''.length hw''_len v' hv'_anc w'' rfl
        · -- v ≠ a but v = parent u
          -- a ∈ pathToRoot u = u :: pathToRoot v (since parent u = some v)
          -- So a = u or a ∈ pathToRoot v
          have hpath_u : T.pathToRoot u = u :: T.pathToRoot v := T.pathToRoot_parent_cons hpar_u
          rw [hpath_u] at h_anc
          simp only [List.mem_cons] at h_anc
          cases h_anc with
          | inl hau =>
            -- a = u, so v = parent a = c (since parent a = some c and parent u = some v)
            have hvc : v = c := Option.some_injective _ (hpar_u.symm.trans (hau ▸ ha))
            right
            rw [← hvc]
            exact SimpleGraph.Walk.start_mem_support w'
          | inr h_anc_v =>
            -- a ∈ pathToRoot v, apply IH
            right
            have hw'_len : w'.length < wlen := by
              simp only [SimpleGraph.Walk.length_cons] at h
              omega
            exact ih w'.length hw'_len v h_anc_v w' rfl
      | inr hpar_v =>
        -- parent v = some u, going DOWN (v is a child of u)
        -- v is still in the subtree of a
        right
        have hv_anc : a ∈ T.pathToRoot v := by
          -- pathToRoot v = v :: pathToRoot u (since parent v = some u)
          have hpath_v : T.pathToRoot v = v :: T.pathToRoot u := T.pathToRoot_parent_cons hpar_v
          rw [hpath_v, List.mem_cons]
          right; exact h_anc
        have hw'_len : w'.length < wlen := by
          simp only [SimpleGraph.Walk.length_cons] at h
          omega
        exact ih w'.length hw'_len v hv_anc w' rfl

/-- Key lemma: In a tree, any walk from vertex a to vertex b must pass through
    their lowest common ancestor. For siblings (children of same parent c),
    any walk between them must pass through c. -/
lemma walk_between_siblings_passes_parent (T : TreeAuth n) {a b c : Fin n}
    (ha : T.parent a = some c) (hb : T.parent b = some c) (hab : a ≠ b)
    (w : T.toSimpleGraph.Walk a b) : c ∈ w.support := by
  -- Proof by induction on walk
  -- Core insight: any walk from a to b must either:
  -- 1. Go directly through c (if first step is a → c)
  -- 2. Go down first (a → child), but then must come back up through c to reach b
  -- Since both a and b are children of c, any path between them in the tree
  -- must pass through their parent c.
  -- Use the generalized lemma: a is an ancestor of a (trivially)
  have ha_anc : a ∈ T.pathToRoot a := by
    simp only [pathToRoot]
    have := T.pathToRootAux_head a n
    rw [List.head?_eq_some_iff] at this
    obtain ⟨tail, heq⟩ := this
    rw [heq, List.mem_cons]
    left; rfl
  exact T.walk_from_descendant_to_sibling_passes_parent ha hb hab a ha_anc w

theorem toSimpleGraph_acyclic_aux (T : TreeAuth n) (v : Fin n)
    (p : T.toSimpleGraph.Walk v v) (hp : p.IsCycle) : False := by
  /-
  Proof Strategy (Minimum Depth Argument):
  1. Find vertex m with minimum depth in the cycle's support
  2. Both neighbors of m in the cycle have depth ≥ depth(m) (by minimality)
  3. By adjacent_depth, neighbors have depth = depth(m) ± 1
  4. Combined: both neighbors have depth = depth(m) + 1, so m is parent of both
  5. The cycle provides a walk between the two neighbors not through m
  6. But walk_between_siblings_passes_parent requires any such walk to include m
  7. Contradiction
  -/

  have hlen := hp.three_le_length

  -- Find minimum depth vertex using Finset.min'
  let support_finset : Finset (Fin n) := p.support.toFinset
  have hsup_nonempty : support_finset.Nonempty := by
    use v
    simp only [support_finset, List.mem_toFinset]
    exact SimpleGraph.Walk.start_mem_support p

  -- Get a vertex with minimum depth using Classical.choose
  have hmin_exists : ∃ m ∈ p.support, ∀ x ∈ p.support, T.depth m ≤ T.depth x := by
    -- Use well-ordering on the image of depth
    let depths := support_finset.image T.depth
    have hdepths_nonempty : depths.Nonempty := hsup_nonempty.image _
    let min_depth := depths.min' hdepths_nonempty
    have hmin_in : min_depth ∈ depths := Finset.min'_mem depths hdepths_nonempty
    rw [Finset.mem_image] at hmin_in
    obtain ⟨m, hm_in, hm_eq⟩ := hmin_in
    use m
    constructor
    · exact List.mem_toFinset.mp hm_in
    · intro x hx
      have hx_in : x ∈ support_finset := List.mem_toFinset.mpr hx
      have hx_depth_in : T.depth x ∈ depths := Finset.mem_image_of_mem _ hx_in
      rw [hm_eq]
      exact Finset.min'_le depths (T.depth x) hx_depth_in

  obtain ⟨m, hm_sup, hm_min⟩ := hmin_exists

  -- Rotate the cycle so m is at position 0, giving c : Walk m m
  let c := p.rotate hm_sup
  have hc_cycle : c.IsCycle := hp.rotate hm_sup

  -- The rotated cycle has the same length
  -- rotate = dropUntil.append(takeUntil), and length is preserved
  have hc_len_ge : 3 ≤ c.length := by
    have h_edges_perm : ∃ k, c.edges.rotate k = p.edges :=
      SimpleGraph.Walk.rotate_edges p hm_sup
    obtain ⟨k, hk⟩ := h_edges_perm
    have h_len : c.edges.length = p.edges.length := by
      rw [← hk, List.length_rotate]
    simp only [SimpleGraph.Walk.length_edges] at h_len hlen
    omega

  -- c.getVert 0 = m, c.getVert c.length = m
  have hc_start : c.getVert 0 = m := SimpleGraph.Walk.getVert_zero c
  have hc_end : c.getVert c.length = m := SimpleGraph.Walk.getVert_length c

  -- The two neighbors of m in the cycle are at positions 1 and length-1
  let n1 := c.getVert 1
  let n2 := c.getVert (c.length - 1)

  -- Both neighbors are adjacent to m
  have h_adj_n1 : T.toSimpleGraph.Adj m n1 := by
    have h : 0 < c.length := by omega
    have := c.adj_getVert_succ h
    simp only [hc_start, Nat.zero_add] at this
    exact this

  have h_adj_n2 : T.toSimpleGraph.Adj n2 m := by
    have h : c.length - 1 < c.length := by omega
    have := c.adj_getVert_succ h
    have heq : c.length - 1 + 1 = c.length := by omega
    simp only [heq, hc_end] at this
    exact this

  -- n1 and n2 are distinct (by getVert_injOn' on the rotated cycle)
  -- getVert_injOn' is injective on {i | i ≤ p.length - 1}
  have hn12_ne : n1 ≠ n2 := by
    have h_inj := hc_cycle.getVert_injOn'
    intro heq
    have h1_range : (1 : ℕ) ∈ {i | i ≤ c.length - 1} := by simp; omega
    have h2_range : c.length - 1 ∈ {i | i ≤ c.length - 1} := by simp
    have h12_eq : (1 : ℕ) = c.length - 1 := h_inj h1_range h2_range heq
    omega

  -- Both neighbors are in the original cycle's support (via mem_support_rotate_iff)
  have h_n1_in_support : n1 ∈ p.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff p hm_sup]
    exact SimpleGraph.Walk.getVert_mem_support c 1

  have h_n2_in_support : n2 ∈ p.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff p hm_sup]
    exact SimpleGraph.Walk.getVert_mem_support c (c.length - 1)

  -- By minimality, both neighbors have depth ≥ depth m
  have h_depth_n1_ge : T.depth m ≤ T.depth n1 := hm_min n1 h_n1_in_support
  have h_depth_n2_ge : T.depth m ≤ T.depth n2 := hm_min n2 h_n2_in_support

  -- By adjacent_depth, neighbors have depth = depth m ± 1
  -- Combined with ≥, both must have depth = depth m + 1
  have h_adj_n1' : T.adjacent m n1 := h_adj_n1
  have h_adj_n2' : T.adjacent n2 m := h_adj_n2

  have h_depth_n1 : T.depth n1 = T.depth m + 1 := by
    have h := T.adjacent_depth h_adj_n1'
    omega

  have h_depth_n2 : T.depth n2 = T.depth m + 1 := by
    have h_adj_sym : T.adjacent m n2 := by simp only [adjacent] at h_adj_n2' ⊢; tauto
    have h := T.adjacent_depth h_adj_sym
    omega

  -- So m is the parent of both n1 and n2
  have h_parent_n1 : T.parent n1 = some m := by
    simp only [adjacent] at h_adj_n1'
    cases h_adj_n1' with
    | inl h => have := T.depth_parent_fuel_analysis h; omega
    | inr h => exact h

  have h_parent_n2 : T.parent n2 = some m := by
    simp only [adjacent] at h_adj_n2'
    cases h_adj_n2' with
    | inl h => exact h
    | inr h => have := T.depth_parent_fuel_analysis h; omega

  -- Now we extract the inner walk from n1 to n2 that avoids m
  -- c = cons h_adj c_tail where c_tail : Walk n1' m
  have hc_not_nil : ¬c.Nil := hc_cycle.not_nil

  -- Decompose c as cons h_adj c_tail
  -- not_nil_iff: ∃ (u : V) (h : G.Adj v u) (q : G.Walk u w), p = cons h q
  obtain ⟨n1', h_adj, c_tail, hc_eq⟩ := SimpleGraph.Walk.not_nil_iff.mp hc_not_nil

  -- n1' = n1 (both are c.getVert 1)
  have hn1'_eq : n1' = n1 := by
    -- n1 := c.getVert 1, and (cons h_adj c_tail).getVert 1 = c_tail.getVert 0 = n1'
    have h1 : c.getVert 1 = c_tail.getVert 0 := by
      conv_lhs => rw [hc_eq]
      rfl  -- by definition of getVert on cons
    have h2 : c_tail.getVert 0 = n1' := SimpleGraph.Walk.getVert_zero c_tail
    -- n1' = c_tail.getVert 0 = c.getVert 1 = n1
    rw [h2] at h1
    exact h1.symm

  -- c_tail is a path (by cons_isCycle_iff)
  have h_c_tail_path : c_tail.IsPath := by
    rw [hc_eq, SimpleGraph.Walk.cons_isCycle_iff] at hc_cycle
    exact hc_cycle.1

  have h_c_tail_len : c_tail.length = c.length - 1 := by
    rw [hc_eq]; simp [SimpleGraph.Walk.length_cons]

  -- c.length = (cons h_adj c_tail).length by hc_eq
  have hc_len_eq_cons : c.length = (SimpleGraph.Walk.cons h_adj c_tail).length := by
    rw [hc_eq]

  -- n2 ∈ c_tail.support
  have h_n2_in_tail : n2 ∈ c_tail.support := by
    -- c.getVert (c.length - 1) = n2, and c.getVert (n+1) = c_tail.getVert n
    have h_n2_pos : c_tail.getVert (c.length - 2) = n2 := by
      -- (cons h_adj c_tail).getVert (c.length - 1) = c_tail.getVert (c.length - 2)
      have hne : c.length - 1 ≠ 0 := by omega
      have heq : c.getVert (c.length - 1) = c_tail.getVert (c.length - 1 - 1) := by
        conv_lhs => rw [hc_eq]
        -- Now LHS is (cons h_adj c_tail).getVert (c.length - 1)
        -- But c.length = (cons h_adj c_tail).length, so this is still c.length - 1
        rw [← hc_len_eq_cons]
        exact SimpleGraph.Walk.getVert_cons c_tail h_adj hne
      have : c.length - 1 - 1 = c.length - 2 := by omega
      rw [this] at heq
      exact heq.symm
    rw [← h_n2_pos]
    exact SimpleGraph.Walk.getVert_mem_support c_tail (c.length - 2)

  -- The inner walk from n1' to n2
  let inner_walk := c_tail.takeUntil n2 h_n2_in_tail

  -- By walk_between_siblings_passes_parent, m must be in inner_walk.support
  -- Need to convert n1' to n1 using hn1'_eq
  have h_m_in_inner : m ∈ inner_walk.support := by
    have h_parent_n1' : T.parent n1' = some m := hn1'_eq ▸ h_parent_n1
    have hn1'2_ne : n1' ≠ n2 := hn1'_eq ▸ hn12_ne
    exact T.walk_between_siblings_passes_parent h_parent_n1' h_parent_n2 hn1'2_ne inner_walk

  -- But m ≠ n2 (m is parent of n2)
  have hm_ne_n2 : m ≠ n2 := by
    intro heq; rw [heq] at h_parent_n2
    exact T.parent_ne_self n2 h_parent_n2

  -- By endpoint_notMem_support_takeUntil: m ∉ inner_walk.support
  have h_inner_not_m : m ∉ inner_walk.support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil h_c_tail_path h_n2_in_tail hm_ne_n2

  exact h_inner_not_m h_m_in_inner

end TreeAuth

end TreeAuthCoreProofs
