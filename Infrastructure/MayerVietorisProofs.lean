/-
# Mayer-Vietoris Proofs

Constructive proofs of Mayer-Vietoris for H¹ using the cochain restriction infrastructure.

## Key Result

If A and B are subcomplexes with:
1. H¹(A) = 0
2. H¹(B) = 0
3. A ∩ B is connected (and nonempty)

Then H¹(A ∪ B) = 0.

SORRIES: 0
AXIOMS: 0
-/

import Foundations.Cohomology
import Infrastructure.CochainRestriction
import H1Characterization.ForestCoboundary

namespace Infrastructure.MayerVietorisProofs

open Classical
open Foundations (Simplex SimplicialComplex Cochain IsCocycle IsCoboundary H1Trivial coboundary sign)
open Infrastructure.CochainRestriction (union inter IsSubcomplex HasConnectedIntersection
  union_sub_left union_sub_right inter_sub_left inter_sub_right
  restrictCochain restrict_preserves_cocycle can_adjust_to_agree)
open H1Characterization (oneSkeleton OneConnected)

/-! ## Helper Lemmas for Gluing -/

/-- Given gA on A and gB on B that agree on A ∩ B (up to constant c), construct a global witness.
    We prioritize using gA when the vertex is in both A and B. -/
noncomputable def glueWitnesses (A B : SimplicialComplex)
    (gA : Cochain A 0) (gB : Cochain B 0) (c : ℚ) :
    Cochain (union A B) 0 :=
  fun ⟨s, hs⟩ =>
    if hA : s ∈ A.ksimplices 0
    then gA ⟨s, hA⟩
    else
      have hB : s ∈ B.ksimplices 0 := by
        simp only [SimplicialComplex.ksimplices, union, Set.mem_setOf_eq, Set.mem_union] at hs ⊢
        obtain ⟨hs_mem, hs_card⟩ := hs
        rcases hs_mem with hA_mem | hB_mem
        · exact absurd ⟨hA_mem, hs_card⟩ hA
        · exact ⟨hB_mem, hs_card⟩
      gB ⟨s, hB⟩ + c

/-- The glued witness equals gA on vertices in A -/
theorem glueWitnesses_on_A (A B : SimplicialComplex)
    (gA : Cochain A 0) (gB : Cochain B 0) (c : ℚ)
    (s : (union A B).ksimplices 0) (hA : s.val ∈ A.ksimplices 0) :
    glueWitnesses A B gA gB c s = gA ⟨s.val, hA⟩ := by
  simp only [glueWitnesses, hA, dite_true]

/-- The glued witness equals gB + c on vertices in B \ A -/
theorem glueWitnesses_on_B_not_A (A B : SimplicialComplex)
    (gA : Cochain A 0) (gB : Cochain B 0) (c : ℚ)
    (s : (union A B).ksimplices 0) (hA : s.val ∉ A.ksimplices 0) (hB : s.val ∈ B.ksimplices 0) :
    glueWitnesses A B gA gB c s = gB ⟨s.val, hB⟩ + c := by
  simp only [glueWitnesses, hA, dite_false]

/-! ## Coboundary Computation -/

/-- Face of a 1-simplex (edge) has cardinality 1 -/
theorem face_of_edge_card (e : Simplex) (he : e.card = 2) (i : Fin e.card) :
    (e.face i).card = 1 := by
  have h_pos : e.card > 0 := by omega
  rw [Simplex.face_card e i h_pos, he]

/-- If edge e is in A, then both its vertices are in A.ksimplices 0 -/
theorem edge_faces_in_A (A : SimplicialComplex) (e : Simplex) (he : e ∈ A.ksimplices 1)
    (i : Fin e.card) : e.face i ∈ A.ksimplices 0 := by
  have h_mem : e ∈ A.simplices := he.1
  have h_face_mem : e.face i ∈ A.simplices := A.down_closed e h_mem i
  have h_face_card : (e.face i).card = 1 := face_of_edge_card e he.2 i
  exact ⟨h_face_mem, h_face_card⟩

/-- If edge e is in B, then both its vertices are in B.ksimplices 0 -/
theorem edge_faces_in_B (B : SimplicialComplex) (e : Simplex) (he : e ∈ B.ksimplices 1)
    (i : Fin e.card) : e.face i ∈ B.ksimplices 0 := by
  have h_mem : e ∈ B.simplices := he.1
  have h_face_mem : e.face i ∈ B.simplices := B.down_closed e h_mem i
  have h_face_card : (e.face i).card = 1 := face_of_edge_card e he.2 i
  exact ⟨h_face_mem, h_face_card⟩

/-- Face of union edge is in union -/
theorem edge_faces_in_union (A B : SimplicialComplex) (e : Simplex) (he : e ∈ (union A B).ksimplices 1)
    (i : Fin e.card) : e.face i ∈ (union A B).ksimplices 0 := by
  have h_mem : e ∈ (union A B).simplices := he.1
  have h_face_mem : e.face i ∈ (union A B).simplices := (union A B).down_closed e h_mem i
  have h_face_card : (e.face i).card = 1 := face_of_edge_card e he.2 i
  exact ⟨h_face_mem, h_face_card⟩

/-- If vertex v is in both A and B, it's in their intersection -/
theorem vertex_in_both_is_in_inter (A B : SimplicialComplex) (v : Simplex)
    (hA : v ∈ A.ksimplices 0) (hB : v ∈ B.ksimplices 0) :
    v ∈ (inter A B).ksimplices 0 := by
  simp only [SimplicialComplex.ksimplices, inter, Set.mem_setOf_eq, Set.mem_inter_iff]
  exact ⟨⟨hA.1, hB.1⟩, hA.2⟩

/-! ## Main Theorem -/

/-- Simple Mayer-Vietoris for H¹: union of H¹-trivial complexes with connected intersection -/
theorem simple_mayer_vietoris (A B : SimplicialComplex)
    (hA : H1Trivial A)
    (hB : H1Trivial B)
    (h_inter_nonempty : (inter A B).vertexSet.Nonempty)
    (h_inter_conn : HasConnectedIntersection A B) :
    H1Trivial (union A B) := by
  intro f hf
  -- Restrict f to A and B
  let fA := restrictCochain (union A B) A (union_sub_left A B) 1 f
  let fB := restrictCochain (union A B) B (union_sub_right A B) 1 f
  -- fA and fB are cocycles
  have hfA_coc : IsCocycle A 1 fA := restrict_preserves_cocycle (union A B) A (union_sub_left A B) f hf
  have hfB_coc : IsCocycle B 1 fB := restrict_preserves_cocycle (union A B) B (union_sub_right A B) f hf
  -- By H¹(A) = 0 and H¹(B) = 0, get witnesses
  obtain ⟨gA, hgA⟩ := hA fA hfA_coc
  obtain ⟨gB, hgB⟩ := hB fB hfB_coc
  -- By can_adjust_to_agree, get constant c for agreement on intersection
  obtain ⟨c, hc⟩ := can_adjust_to_agree A B (union A B)
    (union_sub_left A B) (union_sub_right A B)
    h_inter_conn h_inter_nonempty f gA gB hgA hgB
  -- Construct global witness
  let g := glueWitnesses A B gA gB c
  use g
  -- Prove δg = f by checking on all edges
  funext ⟨e, he⟩
  -- e is either in A or in B (or both)
  have he_union := he.1
  simp only [union, Set.mem_union] at he_union
  -- The key insight: on any edge, the coboundary computation either
  -- uses only gA values (if edge in A), or uses values that
  -- differ by a constant c (which cancels in the difference).
  rcases he_union with he_A | he_B
  · -- Case: e ∈ A
    have he_A_k : e ∈ A.ksimplices 1 := ⟨he_A, he.2⟩
    -- Both faces of e are in A
    -- Compute δg(e) = Σᵢ sign(i) * g(face i)
    simp only [coboundary]
    -- Both faces are in A, so we use gA values
    have h_eq : (∑ i : Fin e.card, sign i * glueWitnesses A B gA gB c ⟨e.face i, edge_faces_in_union A B e he i⟩) =
                (∑ i : Fin e.card, sign i * gA ⟨e.face i, edge_faces_in_A A e he_A_k i⟩) := by
      congr 1
      ext i
      congr 1
      exact glueWitnesses_on_A A B gA gB c ⟨e.face i, edge_faces_in_union A B e he i⟩ (edge_faces_in_A A e he_A_k i)
    rw [h_eq]
    -- This equals δgA(e) = fA(e) = f(e)
    have h_delta_gA : (∑ i : Fin e.card, sign i * gA ⟨e.face i, edge_faces_in_A A e he_A_k i⟩) =
                      (coboundary A 0 gA) ⟨e, he_A_k⟩ := rfl
    rw [h_delta_gA, hgA]
    rfl
  · -- Case: e ∈ B (and possibly in A too)
    by_cases he_also_A : e ∈ A.simplices
    · -- e ∈ A ∩ B: same as case above
      have he_A_k : e ∈ A.ksimplices 1 := ⟨he_also_A, he.2⟩
      simp only [coboundary]
      have h_eq : (∑ i : Fin e.card, sign i * glueWitnesses A B gA gB c ⟨e.face i, edge_faces_in_union A B e he i⟩) =
                  (∑ i : Fin e.card, sign i * gA ⟨e.face i, edge_faces_in_A A e he_A_k i⟩) := by
        congr 1
        ext i
        congr 1
        exact glueWitnesses_on_A A B gA gB c ⟨e.face i, edge_faces_in_union A B e he i⟩ (edge_faces_in_A A e he_A_k i)
      rw [h_eq]
      have h_delta_gA : (∑ i : Fin e.card, sign i * gA ⟨e.face i, edge_faces_in_A A e he_A_k i⟩) =
                        (coboundary A 0 gA) ⟨e, he_A_k⟩ := rfl
      rw [h_delta_gA, hgA]
      rfl
    · -- e ∈ B \ A: the interesting case
      have he_B_k : e ∈ B.ksimplices 1 := ⟨he_B, he.2⟩
      simp only [coboundary]
      -- For each face i of e:
      -- - If face i ∈ A: use gA(face i) = gB(face i) + c (by agreement)
      -- - If face i ∉ A: use gB(face i) + c directly
      -- Either way, the answer is gB(face i) + c, so the sum is δgB(e) + c*Σsign(i)
      -- And Σsign(i) = 0 for any edge (sign(0) + sign(1) = 1 + (-1) = 0)
      -- Therefore δg(e) = δgB(e) = fB(e) = f(e)

      -- Show that for each face, the witness value equals gB + c
      have h_each_face : ∀ i : Fin e.card,
          glueWitnesses A B gA gB c ⟨e.face i, edge_faces_in_union A B e he i⟩ =
          gB ⟨e.face i, edge_faces_in_B B e he_B_k i⟩ + c := by
        intro i
        let fi := e.face i
        have h_fi_B : fi ∈ B.ksimplices 0 := edge_faces_in_B B e he_B_k i
        by_cases h_fi_A : fi ∈ A.ksimplices 0
        · -- Face is in both A and B, so it's in A ∩ B
          -- By agreement condition: gA(fi) = gB(fi) + c
          rw [glueWitnesses_on_A A B gA gB c ⟨fi, edge_faces_in_union A B e he i⟩ h_fi_A]
          -- Need: gA ⟨fi, h_fi_A⟩ = gB ⟨fi, h_fi_B⟩ + c
          have h_fi_inter : fi ∈ (inter A B).ksimplices 0 := vertex_in_both_is_in_inter A B fi h_fi_A h_fi_B
          exact hc ⟨fi, h_fi_inter⟩
        · -- Face is only in B
          exact glueWitnesses_on_B_not_A A B gA gB c ⟨fi, edge_faces_in_union A B e he i⟩ h_fi_A h_fi_B

      -- Rewrite the sum using h_each_face
      have h_sum_eq : (∑ i : Fin e.card, sign i * glueWitnesses A B gA gB c ⟨e.face i, edge_faces_in_union A B e he i⟩) =
                      (∑ i : Fin e.card, sign i * (gB ⟨e.face i, edge_faces_in_B B e he_B_k i⟩ + c)) := by
        congr 1
        ext i
        rw [h_each_face i]
      rw [h_sum_eq]

      -- Expand: sign i * (gB + c) = sign i * gB + sign i * c
      -- and (∑ sign i * c) = c * (∑ sign i) = c * 0 = 0
      have h_expand : (∑ i : Fin e.card, sign i * (gB ⟨e.face i, edge_faces_in_B B e he_B_k i⟩ + c)) =
                      (∑ i : Fin e.card, sign i * gB ⟨e.face i, edge_faces_in_B B e he_B_k i⟩) +
                      c * (∑ i : Fin e.card, sign i) := by
        have h1 : (∑ i : Fin e.card, sign i * (gB ⟨e.face i, edge_faces_in_B B e he_B_k i⟩ + c)) =
                  (∑ i : Fin e.card, (sign i * gB ⟨e.face i, edge_faces_in_B B e he_B_k i⟩ + sign i * c)) := by
          congr 1
          funext i
          ring
        rw [h1, Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
        congr 1
        funext i
        ring
      rw [h_expand]

      -- The sum of signs is 0 for an edge (card = 2)
      have h_sign_sum : (∑ i : Fin e.card, sign i) = 0 := by
        have hcard : e.card = 2 := he.2
        -- Reindex sum from Fin e.card to Fin 2
        have h : (∑ i : Fin e.card, sign i.val) = (∑ i : Fin 2, sign i.val) := by
          refine Finset.sum_equiv (Fin.castOrderIso hcard).toEquiv ?_ ?_
          · intro i; simp
          · intro i _; rfl
        rw [h]
        -- Fin 2 = {0, 1}, so sum = sign 0 + sign 1 = 1 + (-1) = 0
        simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
        rw [Foundations.sign_zero, Foundations.sign_one]
        ring
      rw [h_sign_sum, mul_zero, add_zero]

      -- The remaining sum equals δgB(e)
      have h_delta_gB : (∑ i : Fin e.card, sign i * gB ⟨e.face i, edge_faces_in_B B e he_B_k i⟩) =
                        (coboundary B 0 gB) ⟨e, he_B_k⟩ := rfl
      rw [h_delta_gB, hgB]
      rfl

/-! ## Corollaries -/

/-- If K = A ∪ B with both acyclic and connected intersection, K is acyclic -/
theorem acyclic_union_acyclic (A B : SimplicialComplex)
    (hA : H1Trivial A) (hB : H1Trivial B)
    (h_conn : HasConnectedIntersection A B)
    (h_nonempty : (inter A B).vertexSet.Nonempty) :
    H1Trivial (union A B) :=
  simple_mayer_vietoris A B hA hB h_nonempty h_conn

end Infrastructure.MayerVietorisProofs
