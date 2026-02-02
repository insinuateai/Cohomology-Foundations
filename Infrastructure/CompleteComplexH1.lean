/-
# Complete Complex H¹ Triviality

Infrastructure for proving that complete simplicial complexes have trivial H¹.
This eliminates axiom C03 (complete_complex_coboundary_aux').

## Main Results

1. `valueComplex_vertex_mem` - Vertices are in the complex
2. `valueComplex_edge_mem` - Edges are in the complex when complete
3. `valueComplex_triangle_mem` - Triangles are in the complex when complete
4. `complete_complex_coboundary_proven` - The main theorem (eliminates C03)

## The Root Vertex Method

For a complete complex (all edges exist), every 1-cocycle is a coboundary:
1. Pick root vertex 0
2. Define 0-cochain g: g({0}) = 0, g({v}) = f({0,v}) for v > 0
3. Show δg = f using the cocycle condition on triangles

SORRIES: 0
AXIOMS: 0

Author: Infrastructure Team
Date: February 2026
-/

import Perspective.ValueComplex
import Foundations.Cohomology
import Foundations.Coboundary
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith

namespace Infrastructure.CompleteComplexH1

open Foundations (Cochain IsCocycle IsCoboundary H1Trivial coboundary Simplex SimplicialComplex sign sign_zero sign_one Coeff)
open Foundations.Simplex (face face_card face_subset)
open Perspective (ValueSystem valueComplex)

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## Section 1: ValueComplex Membership Lemmas -/

/-- A vertex {v} is in valueComplex when v < n -/
theorem valueComplex_vertex_mem {n : ℕ} (systems : Fin n → ValueSystem S) (ε : ℚ)
    (v : ℕ) (hv : v < n) :
    ({v} : Simplex) ∈ (valueComplex systems ε).simplices := by
  simp only [valueComplex, Set.mem_setOf_eq]
  constructor
  · intro w hw
    simp only [Finset.mem_singleton] at hw
    rw [hw]; exact hv
  · intro i j hi hj hij _ _
    simp only [Finset.mem_singleton] at hi hj
    omega

/-- An edge {a,b} is in valueComplex when the complete condition holds -/
theorem valueComplex_edge_mem {n : ℕ} (systems : Fin n → ValueSystem S) (ε : ℚ)
    (a b : ℕ) (ha : a < n) (hb : b < n) (hab : a < b)
    (h_complete : ∀ (i j : ℕ) (hi : i < n) (hj : j < n), i < j →
      ∃ s : S, |(systems ⟨i, hi⟩).values s - (systems ⟨j, hj⟩).values s| ≤ 2 * ε) :
    ({a, b} : Simplex) ∈ (valueComplex systems ε).simplices := by
  simp only [valueComplex, Set.mem_setOf_eq]
  constructor
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  · intro i j hi hj hij hi_lt hj_lt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · omega
    · exact h_complete _ _ ha hb hab
    · omega
    · omega

/-- A triangle {a,b,c} is in valueComplex when the complete condition holds -/
theorem valueComplex_triangle_mem {n : ℕ} (systems : Fin n → ValueSystem S) (ε : ℚ)
    (a b c : ℕ) (ha : a < n) (hb : b < n) (hc : c < n) (hab : a < b) (hbc : b < c)
    (h_complete : ∀ (i j : ℕ) (hi : i < n) (hj : j < n), i < j →
      ∃ s : S, |(systems ⟨i, hi⟩).values s - (systems ⟨j, hj⟩).values s| ≤ 2 * ε) :
    ({a, b, c} : Simplex) ∈ (valueComplex systems ε).simplices := by
  simp only [valueComplex, Set.mem_setOf_eq]
  constructor
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  · intro i j hi hj hij hi_lt hj_lt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
    · omega
    · exact h_complete _ _ ha hb hab
    · exact h_complete _ _ ha hc (lt_trans hab hbc)
    · omega
    · omega
    · exact h_complete _ _ hb hc hbc
    · omega
    · omega
    · omega

/-! ## Section 2: Coboundary and Cocycle Conditions

The detailed computation of coboundary formula for edges and cocycle condition
on triangles requires careful handling of Finset sorting and face operations.

Mathematical facts (standard algebraic topology):
1. For sorted edge {a,b} with a < b: (δg)({a,b}) = g({b}) - g({a})
2. For sorted triangle {a,b,c} with a < b < c and 1-cocycle f:
   f({b,c}) - f({a,c}) + f({a,b}) = 0, so f({b,c}) = f({a,c}) - f({a,b})
-/

/-- Sorting {a,b} with a < b gives [a,b] -/
lemma sort_pair (a b : ℕ) (hab : a < b) :
    ({a, b} : Finset ℕ).sort (· ≤ ·) = [a, b] := by
  have hab' : a ≠ b := ne_of_lt hab
  -- Use that both lists have same elements and are sorted
  have h_len : (({a, b} : Finset ℕ).sort (· ≤ ·)).length = 2 := by
    rw [Finset.length_sort, Finset.card_pair hab']
  -- Get the sorted list as [x, y]
  obtain ⟨x, y, hxy⟩ : ∃ x y, ({a, b} : Finset ℕ).sort (· ≤ ·) = [x, y] := by
    match h : ({a, b} : Finset ℕ).sort (· ≤ ·) with
    | [] => rw [h, List.length_nil] at h_len; omega
    | [_] => rw [h, List.length_singleton] at h_len; omega
    | [x, y] => exact ⟨x, y, rfl⟩
    | _ :: _ :: _ :: _ => rw [h] at h_len; simp only [List.length_cons] at h_len; omega
  -- x and y must be a and b
  have hx_mem : x ∈ ({a, b} : Finset ℕ) := by rw [← Finset.mem_sort (· ≤ ·), hxy]; simp
  have hy_mem : y ∈ ({a, b} : Finset ℕ) := by rw [← Finset.mem_sort (· ≤ ·), hxy]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx_mem hy_mem
  -- The sort is pairwise, so x ≤ y
  have hxy_le : x ≤ y := by
    have hsort := Finset.pairwise_sort ({a, b} : Finset ℕ) (· ≤ ·)
    rw [hxy] at hsort
    simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.Pairwise.nil,
               and_true] at hsort
    exact hsort.1
  -- x ≠ y from nodup
  have hxy_ne : x ≠ y := by
    have hnodup := Finset.sort_nodup ({a, b} : Finset ℕ) (· ≤ ·)
    rw [hxy] at hnodup
    simp only [List.nodup_cons, List.mem_singleton, List.nodup_nil, and_true] at hnodup
    exact hnodup.1
  -- Case analysis to show [x, y] = [a, b]
  rcases hx_mem with rfl | rfl <;> rcases hy_mem with rfl | rfl
  · -- x = a, y = a: contradiction
    exact (hxy_ne rfl).elim
  · -- x = a, y = b: this is what we want
    exact hxy
  · -- x = b, y = a: contradicts x ≤ y since b > a
    omega
  · -- x = b, y = b: contradiction
    exact (hxy_ne rfl).elim

/-- face 0 of {a,b} (a < b) is {b} -/
lemma face_zero_of_pair (a b : ℕ) (hab : a < b) :
    Simplex.face ({a, b} : Simplex) ⟨0, by simp [Finset.card_pair (ne_of_lt hab)]⟩ = {b} := by
  unfold Simplex.face
  simp only [sort_pair a b hab, List.length_cons, List.length_singleton, Nat.add_one_sub_one,
             List.get_eq_getElem, List.getElem_cons_zero]
  ext x
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro ⟨hxa, hxab⟩
    cases hxab with
    | inl hxa' => exact (hxa hxa').elim
    | inr hxb => exact hxb
  · intro hxb
    rw [hxb]
    exact ⟨ne_of_gt hab, Or.inr rfl⟩

/-- face 1 of {a,b} (a < b) is {a} -/
lemma face_one_of_pair (a b : ℕ) (hab : a < b) :
    Simplex.face ({a, b} : Simplex) ⟨1, by simp [Finset.card_pair (ne_of_lt hab)]⟩ = {a} := by
  unfold Simplex.face
  simp only [sort_pair a b hab, List.length_cons, List.length_singleton, Nat.add_one_sub_one,
             List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
  ext x
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro ⟨hxb, hxab⟩
    cases hxab with
    | inl hxa => exact hxa
    | inr hxb' => exact (hxb hxb').elim
  · intro hxa
    rw [hxa]
    exact ⟨ne_of_lt hab, Or.inl rfl⟩

/-- The coboundary of a 0-cochain on an edge equals g(larger) - g(smaller).

    Mathematical proof: For sorted edge {a,b} with a < b:
    - face 0 removes position 0 (value a), leaving {b}
    - face 1 removes position 1 (value b), leaving {a}
    - (δg)({a,b}) = sign(0)*g(face 0) + sign(1)*g(face 1) = g({b}) - g({a})

    This is a standard computation in simplicial cohomology.
    The detailed Lean proof requires careful API work with Finset.sort and face operations. -/
theorem coboundary_edge_formula {K : SimplicialComplex}
    (g : Cochain K 0)
    (a b : ℕ) (hab : a < b)
    (h_edge : ({a, b} : Simplex) ∈ K.ksimplices 1)
    (h_a_vert : ({a} : Simplex) ∈ K.ksimplices 0)
    (h_b_vert : ({b} : Simplex) ∈ K.ksimplices 0) :
    coboundary K 0 g ⟨{a, b}, h_edge⟩ = g ⟨{b}, h_b_vert⟩ - g ⟨{a}, h_a_vert⟩ := by
  -- The edge has 2 vertices
  have hcard : ({a, b} : Simplex).card = 2 := Finset.card_pair (ne_of_lt hab)
  -- Compute faces
  have hface0 : Simplex.face ({a, b} : Simplex) ⟨0, by rw [hcard]; omega⟩ = {b} :=
    face_zero_of_pair a b hab
  have hface1 : Simplex.face ({a, b} : Simplex) ⟨1, by rw [hcard]; omega⟩ = {a} :=
    face_one_of_pair a b hab
  -- Create explicit Fin indices
  have h_idx0 : 0 < ({a, b} : Simplex).card := by rw [hcard]; omega
  have h_idx1 : 1 < ({a, b} : Simplex).card := by rw [hcard]; omega
  let i0 : Fin ({a, b} : Simplex).card := ⟨0, h_idx0⟩
  let i1 : Fin ({a, b} : Simplex).card := ⟨1, h_idx1⟩
  -- Show Finset.univ = {i0, i1}
  have h_univ : (Finset.univ : Finset (Fin ({a, b} : Simplex).card)) = {i0, i1} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    have hi : i.val < 2 := by rw [← hcard]; exact i.isLt
    rcases i with ⟨n, hn⟩
    rcases n with _ | n
    · left; ext; rfl
    · rcases n with _ | n
      · right; ext; rfl
      · omega
  have h_ne : i0 ≠ i1 := by intro h; have : (0 : ℕ) = 1 := congrArg Fin.val h; omega
  -- Unfold and expand the sum
  simp only [coboundary]
  -- Use sum_pair
  have h_sum : ∀ (f : Fin ({a, b} : Simplex).card → Coeff),
      ∑ i : Fin ({a, b} : Simplex).card, f i = f i0 + f i1 := fun f => by
    rw [show (Finset.univ : Finset (Fin ({a, b} : Simplex).card)) = {i0, i1} from h_univ]
    exact Finset.sum_pair h_ne
  rw [h_sum]
  -- Simplify signs
  have h_i0_val : i0.val = 0 := rfl
  have h_i1_val : i1.val = 1 := rfl
  simp only [h_i0_val, h_i1_val, sign_zero, sign_one, one_mul, neg_one_mul]
  -- Use face equalities and Subtype.ext
  have h_face_i0 : ({a, b} : Simplex).face i0 = {b} := hface0
  have h_face_i1 : ({a, b} : Simplex).face i1 = {a} := hface1
  -- Need to show: g ⟨face i0, _⟩ + -g ⟨face i1, _⟩ = g ⟨{b}, _⟩ - g ⟨{a}, _⟩
  -- The g arguments have auto-derived membership proofs. Use congrArg.
  have h_face0_mem : ({a, b} : Simplex).face i0 ∈ K.ksimplices 0 := by
    rw [h_face_i0]; exact h_b_vert
  have h_face1_mem : ({a, b} : Simplex).face i1 ∈ K.ksimplices 0 := by
    rw [h_face_i1]; exact h_a_vert
  -- The LHS uses auto-derived proofs which may differ from h_face0_mem, h_face1_mem
  -- But Subtype.ext shows the values are equal
  have h_g0 : g ⟨({a, b} : Simplex).face i0, h_face0_mem⟩ = g ⟨{b}, h_b_vert⟩ := by
    congr 1; apply Subtype.ext; exact h_face_i0
  have h_g1 : g ⟨({a, b} : Simplex).face i1, h_face1_mem⟩ = g ⟨{a}, h_a_vert⟩ := by
    congr 1; apply Subtype.ext; exact h_face_i1
  -- The auto-derived proofs in the goal equal our explicit proofs by proof irrelevance
  simp only [h_g0, h_g1]; ring

/-- Sorting {a,b,c} with a < b < c gives [a,b,c] -/
lemma sort_triple (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    ({a, b, c} : Finset ℕ).sort (· ≤ ·) = [a, b, c] := by
  have hac : a < c := lt_trans hab hbc
  have hab' : a ≠ b := ne_of_lt hab
  have hbc' : b ≠ c := ne_of_lt hbc
  have hac' : a ≠ c := ne_of_lt hac
  -- Use same approach as sort_pair: enumerate and check
  have h_len : (({a, b, c} : Finset ℕ).sort (· ≤ ·)).length = 3 := by
    rw [Finset.length_sort]
    have h1 : a ∉ ({b, c} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg; exact ⟨hab', hac'⟩
    rw [Finset.card_insert_of_notMem h1, Finset.card_pair hbc']
  -- Get the sorted list as [x, y, z]
  obtain ⟨x, y, z, hxyz⟩ : ∃ x y z, ({a, b, c} : Finset ℕ).sort (· ≤ ·) = [x, y, z] := by
    match h : ({a, b, c} : Finset ℕ).sort (· ≤ ·) with
    | [] => rw [h, List.length_nil] at h_len; omega
    | [_] => rw [h, List.length_singleton] at h_len; omega
    | [_, _] => rw [h] at h_len; simp only [List.length_cons, List.length_nil] at h_len; omega
    | [x, y, z] => exact ⟨x, y, z, rfl⟩
    | _ :: _ :: _ :: _ :: _ => rw [h] at h_len; simp only [List.length_cons] at h_len; omega
  -- x, y, z must be a, b, c
  have hx_mem : x ∈ ({a, b, c} : Finset ℕ) := by rw [← Finset.mem_sort (· ≤ ·), hxyz]; simp
  have hy_mem : y ∈ ({a, b, c} : Finset ℕ) := by rw [← Finset.mem_sort (· ≤ ·), hxyz]; simp
  have hz_mem : z ∈ ({a, b, c} : Finset ℕ) := by rw [← Finset.mem_sort (· ≤ ·), hxyz]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx_mem hy_mem hz_mem
  -- Pairwise property: x ≤ y ≤ z
  have hxy_le : x ≤ y := by
    have hsort := Finset.pairwise_sort ({a, b, c} : Finset ℕ) (· ≤ ·)
    rw [hxyz] at hsort
    simp only [List.pairwise_cons] at hsort
    exact hsort.1 y (by simp)
  have hyz_le : y ≤ z := by
    have hsort := Finset.pairwise_sort ({a, b, c} : Finset ℕ) (· ≤ ·)
    rw [hxyz] at hsort
    simp only [List.pairwise_cons] at hsort
    exact hsort.2.1 z (by simp)
  -- Nodup property
  have hnodup := Finset.sort_nodup ({a, b, c} : Finset ℕ) (· ≤ ·)
  rw [hxyz] at hnodup
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.nodup_nil,
             List.not_mem_nil, or_false, and_true] at hnodup
  have hxy_ne : x ≠ y := fun h => hnodup.1 (Or.inl h)
  have hxz_ne : x ≠ z := fun h => hnodup.1 (Or.inr h)
  have hyz_ne : y ≠ z := hnodup.2.1
  -- x < y < z from ≤ and ≠
  have hxy_lt : x < y := lt_of_le_of_ne hxy_le hxy_ne
  have hyz_lt : y < z := lt_of_le_of_ne hyz_le hyz_ne
  -- Now case split to determine x, y, z
  -- Since a < b < c and x < y < z, and {x,y,z} = {a,b,c}, we must have x=a, y=b, z=c
  rcases hx_mem with rfl | rfl | rfl <;> rcases hy_mem with rfl | rfl | rfl <;>
      rcases hz_mem with rfl | rfl | rfl
  all_goals (first | exact hxyz | omega)

/-- Card of {a,b,c} when a, b, c distinct -/
lemma card_triple (a b c : ℕ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset ℕ).card = 3 := by
  have h1 : a ∉ ({b, c} : Finset ℕ) := by simp [hab, hac]
  rw [Finset.card_insert_of_notMem h1, Finset.card_pair hbc]

/-- face 0 of {a,b,c} (a < b < c) is {b,c} (remove a) -/
lemma face_zero_of_triple (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    Simplex.face ({a, b, c} : Simplex) ⟨0, by
      rw [card_triple a b c (ne_of_lt hab) (ne_of_lt (lt_trans hab hbc)) (ne_of_lt hbc)]; omega⟩
      = {b, c} := by
  unfold Simplex.face
  simp only [sort_triple a b c hab hbc, List.get_eq_getElem, List.getElem_cons_zero]
  ext x
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro ⟨hne, hx⟩
    rcases hx with rfl | rfl | rfl
    · exact (hne rfl).elim
    · left; rfl
    · right; rfl
  · intro hx
    rcases hx with rfl | rfl
    · exact ⟨(ne_of_lt hab).symm, Or.inr (Or.inl rfl)⟩
    · exact ⟨(ne_of_lt (lt_trans hab hbc)).symm, Or.inr (Or.inr rfl)⟩

/-- face 1 of {a,b,c} (a < b < c) is {a,c} (remove b) -/
lemma face_one_of_triple (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    Simplex.face ({a, b, c} : Simplex) ⟨1, by
      rw [card_triple a b c (ne_of_lt hab) (ne_of_lt (lt_trans hab hbc)) (ne_of_lt hbc)]; omega⟩
      = {a, c} := by
  unfold Simplex.face
  simp only [sort_triple a b c hab hbc, List.get_eq_getElem, List.getElem_cons_succ,
             List.getElem_cons_zero]
  ext x
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro ⟨hne, hx⟩
    rcases hx with rfl | rfl | rfl
    · left; rfl
    · exact (hne rfl).elim
    · right; rfl
  · intro hx
    rcases hx with rfl | rfl
    · exact ⟨ne_of_lt hab, Or.inl rfl⟩
    · exact ⟨(ne_of_lt hbc).symm, Or.inr (Or.inr rfl)⟩

/-- face 2 of {a,b,c} (a < b < c) is {a,b} (remove c) -/
lemma face_two_of_triple (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    Simplex.face ({a, b, c} : Simplex) ⟨2, by
      rw [card_triple a b c (ne_of_lt hab) (ne_of_lt (lt_trans hab hbc)) (ne_of_lt hbc)]; omega⟩
      = {a, b} := by
  unfold Simplex.face
  simp only [sort_triple a b c hab hbc, List.get_eq_getElem, List.getElem_cons_succ,
             List.getElem_cons_zero]
  ext x
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro ⟨hne, hx⟩
    rcases hx with rfl | rfl | rfl
    · left; rfl
    · right; rfl
    · exact (hne rfl).elim
  · intro hx
    rcases hx with rfl | rfl
    · exact ⟨ne_of_lt (lt_trans hab hbc), Or.inl rfl⟩
    · exact ⟨ne_of_lt hbc, Or.inr (Or.inl rfl)⟩

/-- sign of 2 is 1 (since (-1)^2 = 1) -/
lemma sign_two : sign 2 = (1 : Coeff) := by
  unfold sign; simp

/-- Cocycle condition on triangle: f({b,c}) = f({a,c}) - f({a,b}). -/
theorem cocycle_triangle_condition {K : SimplicialComplex}
    (f : Cochain K 1) (hf : IsCocycle K 1 f)
    (a b c : ℕ) (hab : a < b) (hbc : b < c)
    (h_tri : ({a, b, c} : Simplex) ∈ K.ksimplices 2)
    (h_ab : ({a, b} : Simplex) ∈ K.ksimplices 1)
    (h_ac : ({a, c} : Simplex) ∈ K.ksimplices 1)
    (h_bc : ({b, c} : Simplex) ∈ K.ksimplices 1) :
    f ⟨{b, c}, h_bc⟩ = f ⟨{a, c}, h_ac⟩ - f ⟨{a, b}, h_ab⟩ := by
  -- The cocycle condition says δf = 0
  -- Evaluating at the triangle: (δf)({a,b,c}) = 0
  -- Expanding: f({b,c}) - f({a,c}) + f({a,b}) = 0
  -- Therefore: f({b,c}) = f({a,c}) - f({a,b})
  have hcard : ({a, b, c} : Simplex).card = 3 := by
    have hab' := ne_of_lt hab; have hbc' := ne_of_lt hbc
    have hac' := ne_of_lt (lt_trans hab hbc)
    have h1 : a ∉ ({b, c} : Finset ℕ) := by simp; push_neg; exact ⟨hab', hac'⟩
    rw [Finset.card_insert_of_notMem h1, Finset.card_pair hbc']
  -- IsCocycle means coboundary K 1 f = 0
  have h_cocycle : coboundary K 1 f = 0 := hf
  -- Evaluate at the triangle
  have h_eval : coboundary K 1 f ⟨{a, b, c}, h_tri⟩ = 0 := by
    rw [h_cocycle]; rfl
  -- Expand coboundary
  simp only [coboundary] at h_eval
  -- Create explicit Fin indices
  have h_idx0 : 0 < ({a, b, c} : Simplex).card := by rw [hcard]; omega
  have h_idx1 : 1 < ({a, b, c} : Simplex).card := by rw [hcard]; omega
  have h_idx2 : 2 < ({a, b, c} : Simplex).card := by rw [hcard]; omega
  let i0 : Fin ({a, b, c} : Simplex).card := ⟨0, h_idx0⟩
  let i1 : Fin ({a, b, c} : Simplex).card := ⟨1, h_idx1⟩
  let i2 : Fin ({a, b, c} : Simplex).card := ⟨2, h_idx2⟩
  -- Show Finset.univ = {i0, i1, i2}
  have h_univ : (Finset.univ : Finset (Fin ({a, b, c} : Simplex).card)) = {i0, i1, i2} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    have hi : i.val < 3 := by rw [← hcard]; exact i.isLt
    rcases i with ⟨n, hn⟩
    rcases n with _ | n
    · left; ext; rfl
    · rcases n with _ | n
      · right; left; ext; rfl
      · rcases n with _ | n
        · right; right; ext; rfl
        · omega
  have h_ne01 : i0 ≠ i1 := by intro h; have : (0 : ℕ) = 1 := congrArg Fin.val h; omega
  have h_ne02 : i0 ≠ i2 := by intro h; have : (0 : ℕ) = 2 := congrArg Fin.val h; omega
  have h_ne12 : i1 ≠ i2 := by intro h; have : (1 : ℕ) = 2 := congrArg Fin.val h; omega
  have h_i2_notin : i2 ∉ ({i0, i1} : Finset _) := by simp [h_ne02.symm, h_ne12.symm]
  have h_i1_notin : i1 ∉ ({i0} : Finset _) := by simp [h_ne01.symm]
  -- Expand the sum
  -- {i0, i1, i2} = insert i0 (insert i1 {i2})
  have h_i0_notin : i0 ∉ ({i1, i2} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg; exact ⟨h_ne01, h_ne02⟩
  have h_i1_notin' : i1 ∉ ({i2} : Finset _) := by simp [h_ne12]
  have h_sum : ∀ (g : Fin ({a, b, c} : Simplex).card → Coeff),
      ∑ i : Fin ({a, b, c} : Simplex).card, g i = g i0 + g i1 + g i2 := fun g => by
    rw [show (Finset.univ : Finset (Fin ({a, b, c} : Simplex).card)) = {i0, i1, i2} from h_univ]
    rw [Finset.sum_insert h_i0_notin, Finset.sum_insert h_i1_notin', Finset.sum_singleton]
    ring
  rw [h_sum] at h_eval
  -- Simplify signs
  have h_i0_val : i0.val = 0 := rfl
  have h_i1_val : i1.val = 1 := rfl
  have h_i2_val : i2.val = 2 := rfl
  simp only [h_i0_val, h_i1_val, h_i2_val, sign_zero, sign_one, sign_two,
             one_mul, neg_one_mul] at h_eval
  -- Face computations
  have hface0 : ({a, b, c} : Simplex).face i0 = {b, c} := face_zero_of_triple a b c hab hbc
  have hface1 : ({a, b, c} : Simplex).face i1 = {a, c} := face_one_of_triple a b c hab hbc
  have hface2 : ({a, b, c} : Simplex).face i2 = {a, b} := face_two_of_triple a b c hab hbc
  -- Face membership
  have h_face0_mem : ({a, b, c} : Simplex).face i0 ∈ K.ksimplices 1 := by rw [hface0]; exact h_bc
  have h_face1_mem : ({a, b, c} : Simplex).face i1 ∈ K.ksimplices 1 := by rw [hface1]; exact h_ac
  have h_face2_mem : ({a, b, c} : Simplex).face i2 ∈ K.ksimplices 1 := by rw [hface2]; exact h_ab
  -- Rewrite f values
  have h_f0 : f ⟨({a, b, c} : Simplex).face i0, h_face0_mem⟩ = f ⟨{b, c}, h_bc⟩ := by
    congr 1; apply Subtype.ext; exact hface0
  have h_f1 : f ⟨({a, b, c} : Simplex).face i1, h_face1_mem⟩ = f ⟨{a, c}, h_ac⟩ := by
    congr 1; apply Subtype.ext; exact hface1
  have h_f2 : f ⟨({a, b, c} : Simplex).face i2, h_face2_mem⟩ = f ⟨{a, b}, h_ab⟩ := by
    congr 1; apply Subtype.ext; exact hface2
  -- Now h_eval says: f({b,c}) - f({a,c}) + f({a,b}) = 0
  simp only [h_f0, h_f1, h_f2] at h_eval
  -- Solve for f({b,c})
  linarith

/-! ## Section 3: The Main Theorem -/

/-- C03: Complete complex coboundary property.
    When all pairs agree within 2ε, every 1-cocycle is a coboundary. -/
theorem complete_complex_coboundary_proven {n : ℕ} (hn : n ≥ 1)
    (systems : Fin n → ValueSystem S) (ε : ℚ)
    (f : Cochain (valueComplex systems ε) 1)
    (hf : IsCocycle (valueComplex systems ε) 1 f)
    (h_complete : ∀ (i j : ℕ) (hi : i < n) (hj : j < n), i < j →
      ∃ s : S, |(systems ⟨i, hi⟩).values s - (systems ⟨j, hj⟩).values s| ≤ 2 * ε) :
    IsCoboundary (valueComplex systems ε) 1 f := by
  let K := valueComplex systems ε
  have h0 : 0 < n := hn

  -- Define 0-cochain g using root vertex method
  let g : Cochain K 0 := fun ⟨σ, hσ⟩ =>
    -- σ is a 0-simplex {v} for some v
    let v := σ.min' (by
      have h1 : σ ∈ K.ksimplices 0 := hσ
      simp only [SimplicialComplex.ksimplices] at h1
      have hcard : σ.card = 1 := h1.2
      exact Finset.card_pos.mp (hcard ▸ Nat.one_pos))
    if hv : v = 0 then
      0
    else
      have hv_lt : v < n := by
        have h1 := hσ.1
        simp only [valueComplex] at h1
        exact h1.1 v (Finset.min'_mem _ _)
      have hv_pos : 0 < v := Nat.pos_of_ne_zero hv
      have h0v : ({0, v} : Simplex) ∈ K.ksimplices 1 := by
        refine ⟨valueComplex_edge_mem systems ε 0 v h0 hv_lt hv_pos h_complete, ?_⟩
        rw [Finset.card_pair]; exact (ne_of_gt hv_pos).symm
      f ⟨{0, v}, h0v⟩

  use g
  funext ⟨σ, hσ⟩

  -- σ is a 1-simplex, get its two elements
  have h_card : σ.card = 2 := hσ.2
  obtain ⟨x, y, hxy, hσ_eq⟩ := Finset.card_eq_two.mp h_card
  subst hσ_eq

  -- Get the smaller and larger element
  let a := min x y
  let b := max x y
  have hab : a < b := by
    simp only [a, b]
    cases Nat.lt_or_gt_of_ne hxy with
    | inl h => simp [min_eq_left (le_of_lt h), max_eq_right (le_of_lt h), h]
    | inr h => simp [min_eq_right (le_of_lt h), max_eq_left (le_of_lt h), h]

  have hσ_eq' : ({x, y} : Simplex) = {a, b} := by
    simp only [a, b]
    cases Nat.lt_or_gt_of_ne hxy with
    | inl h => simp [min_eq_left (le_of_lt h), max_eq_right (le_of_lt h)]
    | inr h =>
      simp [min_eq_right (le_of_lt h), max_eq_left (le_of_lt h)]
      exact (Finset.pair_comm y x).symm

  -- Use the sorted form
  have hσ' : ({a, b} : Simplex) ∈ K.ksimplices 1 := by rw [← hσ_eq']; exact hσ

  have ha_lt : a < n := by
    have := hσ.1
    simp only [valueComplex] at this
    have hx := this.1 x (by simp)
    have hy := this.1 y (by simp)
    simp only [a]; exact min_lt_iff.mpr (Or.inl hx)

  have hb_lt : b < n := by
    have := hσ.1
    simp only [valueComplex] at this
    have hx := this.1 x (by simp)
    have hy := this.1 y (by simp)
    simp only [b]; exact max_lt hx hy

  have h_a_vert : ({a} : Simplex) ∈ K.ksimplices 0 :=
    ⟨valueComplex_vertex_mem systems ε a ha_lt, by simp⟩
  have h_b_vert : ({b} : Simplex) ∈ K.ksimplices 0 :=
    ⟨valueComplex_vertex_mem systems ε b hb_lt, by simp⟩

  -- The result for {x,y} equals result for {a,b}
  have h_eq : (⟨{x, y}, hσ⟩ : K.ksimplices 1) = ⟨{a, b}, hσ'⟩ := by
    apply Subtype.ext; exact hσ_eq'

  conv_lhs => rw [h_eq]
  conv_rhs => rw [h_eq]

  -- Apply coboundary formula
  have h_cob := coboundary_edge_formula g a b hab hσ' h_a_vert h_b_vert
  rw [h_cob]

  -- Case split: a = 0 or a > 0
  by_cases ha0 : a = 0
  · -- Case a = 0: g({0}) = 0, g({b}) = f({0,b})
    have hb_ne : b ≠ 0 := by
      intro hb0
      rw [ha0, hb0] at hab
      exact Nat.lt_irrefl 0 hab
    have hga : g ⟨{a}, h_a_vert⟩ = 0 := by
      simp only [g, Finset.min'_singleton]
      simp only [ha0, ↓reduceDIte]
    have hgb : g ⟨{b}, h_b_vert⟩ = f ⟨{a, b}, hσ'⟩ := by
      simp only [g, Finset.min'_singleton, hb_ne, ↓reduceDIte]
      congr 1; apply Subtype.ext
      simp only [ha0, Finset.pair_comm 0 b]
    rw [hga, hgb]; ring

  · -- Case a > 0: use cocycle condition on triangle {0, a, b}
    have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
    have hb_pos : 0 < b := lt_trans ha_pos hab

    -- Triangle {0, a, b} membership
    have h_tri : ({0, a, b} : Simplex) ∈ K.ksimplices 2 := by
      refine ⟨valueComplex_triangle_mem systems ε 0 a b h0 ha_lt hb_lt ha_pos hab h_complete, ?_⟩
      -- {0, a, b} has 3 elements since 0 < a < b
      have h0a : (0 : ℕ) ≠ a := (ne_of_gt ha_pos).symm
      have h0b : (0 : ℕ) ≠ b := (ne_of_gt hb_pos).symm
      have hab' : a ≠ b := ne_of_lt hab
      have h0_notin : (0 : ℕ) ∉ ({a, b} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨h0a, h0b⟩
      rw [Finset.card_insert_of_notMem h0_notin, Finset.card_pair hab']

    -- Edge memberships
    have h_0a : ({0, a} : Simplex) ∈ K.ksimplices 1 :=
      ⟨valueComplex_edge_mem systems ε 0 a h0 ha_lt ha_pos h_complete,
       Finset.card_pair (ne_of_gt ha_pos).symm⟩
    have h_0b : ({0, b} : Simplex) ∈ K.ksimplices 1 :=
      ⟨valueComplex_edge_mem systems ε 0 b h0 hb_lt hb_pos h_complete,
       Finset.card_pair (ne_of_gt hb_pos).symm⟩

    -- Cocycle condition: f({a,b}) = f({0,b}) - f({0,a})
    have h_cocycle := cocycle_triangle_condition f hf 0 a b ha_pos hab h_tri h_0a h_0b hσ'

    -- Compute g values
    have hga : g ⟨{a}, h_a_vert⟩ = f ⟨{0, a}, h_0a⟩ := by
      simp only [g, Finset.min'_singleton, ha0, ↓reduceDIte]

    have hb_ne : b ≠ 0 := ne_of_gt hb_pos
    have hgb : g ⟨{b}, h_b_vert⟩ = f ⟨{0, b}, h_0b⟩ := by
      simp only [g, Finset.min'_singleton, hb_ne, ↓reduceDIte]

    rw [hga, hgb, h_cocycle]

end Infrastructure.CompleteComplexH1
