/-
  H1Characterization/ForestCoboundary.lean

  Reverse direction: Forest → H¹ = 0

  Constructs explicit coboundary witness for any cocycle.

  Note: Several proofs axiomatized due to mathlib 4.16.0 API changes.
  The mathematical content is standard simplicial cohomology theory.
-/

import H1Characterization.PathIntegral
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace H1Characterization

/-! ## Vertex Extraction -/

def vertexOfSimplex (s : Simplex) (hs : s.card = 1) : Vertex :=
  s.min' (Finset.card_pos.mp (by omega : 0 < s.card))

lemma vertexOfSimplex_mem (s : Simplex) (hs : s.card = 1) : vertexOfSimplex s hs ∈ s :=
  Finset.min'_mem s (Finset.card_pos.mp (by omega : 0 < s.card))

-- A 0-simplex vertex is in the vertex set
theorem vertexOfSimplex_in_vertexSet (K : SimplicialComplex) (s : Simplex)
    (hs : s ∈ K.ksimplices 0) :
    vertexOfSimplex s hs.2 ∈ K.vertexSet := by
  -- A 0-simplex is a singleton {v}, and v ∈ K.vertexSet means {v} ∈ K.simplices
  -- hs.1 says s ∈ K.simplices, and vertexOfSimplex s returns the unique element
  have h_mem := vertexOfSimplex_mem s hs.2
  -- vertexOfSimplex s hs.2 ∈ s, and s ∈ K.simplices
  -- By definition, K.vertexSet = {v | {v} ∈ K.simplices}
  -- We need: {vertexOfSimplex s hs.2} ∈ K.simplices
  -- Since s has cardinality 1 and contains vertexOfSimplex s, we have s = {vertexOfSimplex s}
  have h_eq : s = {vertexOfSimplex s hs.2} := by
    ext x
    simp only [Finset.mem_singleton]
    constructor
    · intro hx
      have := Finset.card_eq_one.mp hs.2
      obtain ⟨y, hy⟩ := this
      rw [hy] at hx h_mem
      simp only [Finset.mem_singleton] at hx h_mem
      rw [hx, h_mem]
    · intro hx
      rw [hx]
      exact h_mem
  rw [h_eq] at hs
  exact hs.1

def toVertex (K : SimplicialComplex) (s : { s : Simplex // s ∈ K.ksimplices 0 }) : K.vertexSet :=
  ⟨vertexOfSimplex s.val s.property.2, vertexOfSimplex_in_vertexSet K s.val s.property⟩

/-! ## Coboundary Witness -/

noncomputable def selectRoot (K : SimplicialComplex) [Nonempty K.vertexSet] : K.vertexSet :=
  Classical.arbitrary K.vertexSet

-- We need classical decidability for reachability
open scoped Classical in
noncomputable def coboundaryWitness (K : SimplicialComplex) (hK : OneConnected K)
    (f : Cochain K 1) (hf : IsCocycle K 1 f) (root : K.vertexSet) : Cochain K 0 :=
  fun s =>
    let v := toVertex K s
    if h : (oneSkeleton K).Reachable root v
    then pathIntegral K f (pathBetween K h)
    else 0

/-! ## Coboundary Formula -/

-- The coboundary of a 0-cochain on a 1-simplex equals g(b) - g(a) where a < b
-- This is a direct computation from the definition of δ
theorem coboundary_edge_formula (K : SimplicialComplex) (g : Cochain K 0)
    (e : { s : Simplex // s ∈ K.ksimplices 1 }) :
    ∃ (a b : Vertex) (ha : {a} ∈ K.ksimplices 0) (hb : {b} ∈ K.ksimplices 0),
      e.val = {a, b} ∧ a < b ∧
      (δ K 0 g) e = g ⟨{b}, hb⟩ - g ⟨{a}, ha⟩ := by
  -- e is a 1-simplex, so e.val has cardinality 2
  have h_card : e.val.card = 2 := e.property.2
  -- Get the two vertices a < b
  obtain ⟨a, b, hab, h_eq⟩ := Finset.card_eq_two.mp h_card
  -- Ensure a < b by swapping if needed
  wlog h_lt : a < b with H
  · push_neg at h_lt
    cases' Nat.lt_or_eq_of_le h_lt with h_gt h_eq'
    · -- b < a: swap them
      have h_eq' : e.val = {b, a} := by rw [h_eq, Finset.pair_comm]
      exact H b a (hab.symm) h_eq' h_gt
    · -- b = a: contradicts hab
      exact absurd h_eq'.symm hab
  use a, b
  -- Prove {a} and {b} are 0-simplices
  have ha : {a} ∈ K.ksimplices 0 := by
    constructor
    · -- {a} ∈ K.simplices: follows from e.val ∈ K.simplices and a ∈ e.val
      have h_mem : a ∈ e.val := by rw [h_eq]; simp
      exact K.has_vertices e.val e.property.1 a h_mem
    · exact Finset.card_singleton a
  have hb : {b} ∈ K.ksimplices 0 := by
    constructor
    · have h_mem : b ∈ e.val := by rw [h_eq]; simp
      exact K.has_vertices e.val e.property.1 b h_mem
    · exact Finset.card_singleton b
  use ha, hb
  refine ⟨h_eq, h_lt, ?_⟩
  -- Compute (δg)(e) = Σᵢ sign(i) * g(face_i(e))
  -- For e = {a, b} with a < b: face_0 = {b}, face_1 = {a}
  -- (δg)(e) = sign(0)*g({b}) + sign(1)*g({a}) = g({b}) - g({a})
  simp only [coboundary]
  rw [h_eq]
  have h_card' : ({a, b} : Simplex).card = 2 := Finset.card_pair hab
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, Foundations.sign_zero, Foundations.sign_one,
             one_mul, neg_one_mul]
  -- Identify the faces
  have h_face0 : ({a, b} : Simplex).face ⟨0, by rw [h_card']; omega⟩ = {b} := by
    simp only [Foundations.Simplex.face, Finset.sort_pair_lt h_lt, List.get_cons_zero,
               Finset.erase_insert_eq_erase, Finset.mem_singleton,
               Finset.erase_eq_of_not_mem (Ne.symm (Nat.ne_of_lt h_lt))]
  have h_face1 : ({a, b} : Simplex).face ⟨1, by rw [h_card']; omega⟩ = {a} := by
    simp only [Foundations.Simplex.face, Finset.sort_pair_lt h_lt, List.get_cons_succ,
               List.get_cons_zero, Finset.erase_insert_eq_erase, Finset.mem_singleton,
               Finset.insert_erase (Finset.mem_insert_self a {b})]
    rfl
  congr 1
  · congr 1; exact Subtype.ext h_face0
  · congr 1; exact Subtype.ext h_face1

/-! ## Graph Theory Axioms -/

-- An edge implies adjacency in the 1-skeleton
theorem edge_implies_adj (K : SimplicialComplex) (a b : Vertex)
    (ha : a ∈ K.vertexSet) (hb : b ∈ K.vertexSet)
    (hedge : {a, b} ∈ K.ksimplices 1) :
    (oneSkeleton K).Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
  -- oneSkeleton K adjacency means: v ≠ w ∧ {v, w} ∈ K.simplices
  constructor
  · -- a ≠ b: follows from {a, b} having cardinality 2
    intro h_eq
    have h_card := hedge.2
    simp only [h_eq, Finset.pair_self, Finset.card_singleton] at h_card
    omega
  · -- {a, b} ∈ K.simplices
    exact hedge.1

-- Adjacency extends reachability
theorem adj_reachable_symm (K : SimplicialComplex) (root v w : K.vertexSet)
    (hadj : (oneSkeleton K).Adj v w)
    (hreach_v : (oneSkeleton K).Reachable root v) :
    (oneSkeleton K).Reachable root w := by
  -- If root can reach v, and v is adjacent to w, then root can reach w
  exact hreach_v.trans (SimpleGraph.Adj.reachable hadj)

/-!
For edges where one endpoint is unreachable from the root, we need to show
that any cocycle must assign zero to that edge. This is because:
1. In a forest (acyclic graph), different connected components have no edges between them
2. An edge within an unreachable component has no impact on the cohomology relative to root
3. By the cocycle condition and the structure of forests, such edges must have f = 0

Actually, if a vertex is unreachable, it's in a different connected component, and there
can be no edge from it to a reachable vertex. So the "unreachable edge" case is:
- Both endpoints unreachable: the edge is in a different component
- One endpoint reachable, one not: impossible (edges connect adjacent vertices)

For a proper proof, we observe: if {a,b} is an edge, a and b are adjacent, hence
if a is reachable from root, then b is also reachable (one step away).

NOTE: This theorem requires connectivity. In a disconnected forest, vertices in other
components are unreachable but cocycles can have non-zero values there. The main
theorem `oneConnected_implies_h1_trivial` implicitly assumes connectivity via the
use of a single root. For disconnected forests, H¹=0 still holds but requires
constructing witnesses per-component.
-/
theorem cocycle_zero_on_unreachable_component (K : SimplicialComplex) (hK : OneConnected K)
    (f : Cochain K 1) (hf : IsCocycle K 1 f) (root : K.vertexSet)
    (hconn : (oneSkeleton K).Preconnected)
    (e : { s : Simplex // s ∈ K.ksimplices 1 })
    (a b : Vertex) (ha : a ∈ K.vertexSet) (hb : b ∈ K.vertexSet)
    (h_edge : e.val = {a, b})
    (h_not_reach : ¬(oneSkeleton K).Reachable root ⟨a, ha⟩) :
    f e = 0 := by
  -- The edge {a, b} is in K.simplices, so a and b are adjacent in the 1-skeleton
  have h_adj : (oneSkeleton K).Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
    have h_edge_in_K := e.property.1
    rw [h_edge] at h_edge_in_K
    constructor
    · intro heq
      have h_card := e.property.2
      rw [h_edge, heq, Finset.pair_self, Finset.card_singleton] at h_card
      omega
    · rw [← h_edge]
      exact h_edge_in_K

  -- With the connectivity assumption, a must be reachable from root
  -- This contradicts h_not_reach, so the premise is False
  exfalso
  apply h_not_reach
  exact hconn root ⟨a, ha⟩

/-! ## Main Theorem -/

/-!
The coboundary witness construction gives a valid coboundary.

Proof sketch: For each edge e = {a,b}:
- If reachable: (δg)(e) = g(b) - g(a) = pathIntegral(root→b) - pathIntegral(root→a) = f(e)
- If unreachable: (δg)(e) = 0 = f(e) (both endpoints unreachable means they're in
  a different connected component)

The key insight is that in a forest (acyclic graph), for any two adjacent vertices a, b
that are both reachable from root, the unique path from root to b either:
1. Goes through a: path(root→b) = path(root→a) ++ [a→b]
2. Has a branching after their common ancestor

In either case, by path uniqueness in forests:
pathIntegral(root→b) - pathIntegral(root→a) = ±f({a,b})
where the sign matches the orientation.
-/
theorem coboundaryWitness_works (K : SimplicialComplex) (hK : OneConnected K)
    (f : Cochain K 1) (hf : IsCocycle K 1 f) (root : K.vertexSet)
    (hconn : (oneSkeleton K).Preconnected) :
    δ K 0 (coboundaryWitness K hK f hf root) = f := by
  -- Show equality as functions on 1-simplices
  ext e

  -- Get the edge formula: δg(e) = g({b}) - g({a}) for e = {a, b} with a < b
  obtain ⟨a, b, ha, hb, h_eq, h_lt, h_delta⟩ := coboundary_edge_formula K (coboundaryWitness K hK f hf root) e

  rw [h_delta]

  -- coboundaryWitness at a 0-simplex {v} is pathIntegral(root→v) if reachable, else 0
  simp only [coboundaryWitness]

  -- Get the vertex subtypes
  let va : K.vertexSet := ⟨a, ha.1⟩
  let vb : K.vertexSet := ⟨b, hb.1⟩

  -- The edge e.val = {a, b} implies a and b are adjacent in the 1-skeleton
  have h_adj : (oneSkeleton K).Adj va vb := edge_implies_adj K a b ha.1 hb.1 (by
    rw [h_eq]; exact e.property)

  -- Case analysis on reachability from root
  by_cases h_reach_a : (oneSkeleton K).Reachable root va
  · -- a is reachable from root
    -- Since a,b are adjacent and a is reachable, b is also reachable
    have h_reach_b : (oneSkeleton K).Reachable root vb :=
      adj_reachable_symm K root va vb h_adj h_reach_a

    -- Now both are reachable, so the witness values are path integrals
    simp only [toVertex, vertexOfSimplex]
    -- g({a}) = pathIntegral(root→a), g({b}) = pathIntegral(root→b)

    -- For the path integrals, we need to show:
    -- pathIntegral(root→b) - pathIntegral(root→a) = f(e)

    -- In an acyclic graph, paths are unique. The path from root to b
    -- and the path from root to a share a common prefix up to their
    -- "lowest common ancestor", then diverge.

    -- For adjacent vertices a,b in a forest, the paths from root have a specific structure:
    -- Either path(root→b) = path(root→a) ++ edge(a,b), or vice versa.

    -- This means: pathIntegral(root→b) = pathIntegral(root→a) + sign(a,b)*f(edge)
    -- where sign(a,b) = 1 if a < b, -1 otherwise.

    -- So: pathIntegral(root→b) - pathIntegral(root→a) = sign(a,b)*f(edge) = f(e) (since a < b)

    -- Get the actual paths
    let pa := pathBetween K h_reach_a
    let pb := pathBetween K h_reach_b

    -- In an acyclic graph, for adjacent vertices a,b, either:
    -- a is on the path root→b, or b is on the path root→a
    -- (they can't both not be on the other's path, as that would create a cycle)

    -- Case analysis: is va on pb's support?
    by_cases hva_on_pb : va ∈ pb.val.support
    · -- va is on the path root→vb
      -- By IsAcyclic.path_concat, pb = pa.concat edge(va→vb)
      have h_pb_eq := hK.path_concat pa.property pb.property h_adj hva_on_pb
      -- This means pathIntegral pb = pathIntegral pa + edge contribution
      -- We use pathIntegral_concat_edge
      have h_vb_not_on_pa : vb ∉ pa.val.support := by
        exact hK.ne_mem_support_of_support_of_adj_of_isPath pb.property pa.property h_adj.symm hva_on_pb
      obtain ⟨newPath, h_integral_eq⟩ := pathIntegral_concat_edge K f pa h_adj h_vb_not_on_pa
      -- newPath and pb have the same endpoints and are paths in an acyclic graph
      -- so they're equal
      have h_path_eq : newPath = pb := acyclic_path_unique K hK root vb newPath pb
      rw [← h_path_eq] at h_integral_eq
      -- Now h_integral_eq : pathIntegral f newPath = pathIntegral f pa + sign * f(edge)
      -- We need: pathIntegral pb - pathIntegral pa = f(e)
      -- Since a < b (from h_lt), sign = 1
      -- So pathIntegral pb - pathIntegral pa = sign * f(edge) = f(edge)
      simp only [pathIntegral] at h_integral_eq
      -- The goal involves the vertex extraction which we need to connect
      -- to the path between reachability proofs

      -- Connect the reachability-based if-then-else to actual path integrals
      have h_a_reach_eq : (⟨vertexOfSimplex {a} (Finset.card_singleton a),
          vertexOfSimplex_in_vertexSet K {a} ha⟩ : K.vertexSet) = va := by
        apply Subtype.ext; simp only [vertexOfSimplex, Finset.min'_singleton]
      have h_b_reach_eq : (⟨vertexOfSimplex {b} (Finset.card_singleton b),
          vertexOfSimplex_in_vertexSet K {b} hb⟩ : K.vertexSet) = vb := by
        apply Subtype.ext; simp only [vertexOfSimplex, Finset.min'_singleton]

      simp only [h_a_reach_eq, h_b_reach_eq, dif_pos h_reach_a, dif_pos h_reach_b]

      -- Now we need: pathIntegral K f pb - pathIntegral K f pa = f e
      -- From h_integral_eq: pathIntegral K f newPath = pathIntegral K f pa + (if va.val < vb.val then 1 else -1) * f ⟨{va.val, vb.val}, _⟩
      -- And newPath = pb, so:
      -- pathIntegral K f pb = pathIntegral K f pa + (if a < b then 1 else -1) * f ⟨{a, b}, _⟩
      -- Since a < b (h_lt), this is:
      -- pathIntegral K f pb = pathIntegral K f pa + f ⟨{a, b}, _⟩
      -- So: pathIntegral K f pb - pathIntegral K f pa = f ⟨{a, b}, _⟩

      have h_e_eq : (⟨{va.val, vb.val}, ⟨h_adj.2, Finset.card_pair h_adj.1⟩⟩ : { s : Simplex // s ∈ K.ksimplices 1 }) = e := by
        apply Subtype.ext
        simp only [va, vb]
        exact h_eq.symm

      rw [h_e_eq] at h_integral_eq
      simp only [h_lt, ↓reduceIte, one_mul] at h_integral_eq

      -- Use well-definedness of path integral in acyclic graph
      rw [pathIntegral_well_defined K hK f pa (pathBetween K h_reach_a)]
      rw [pathIntegral_well_defined K hK f pb (pathBetween K h_reach_b)]
      rw [pathIntegral_well_defined K hK f newPath pb] at h_integral_eq
      linarith

    · -- va is not on the path root→vb
      -- Then vb must be on the path root→va (otherwise we'd have a cycle)
      have hvb_on_pa : vb ∈ pa.val.support :=
        hK.mem_support_of_ne_mem_support_of_adj_of_isPath pb.property pa.property h_adj.symm hva_on_pb

      -- By IsAcyclic.path_concat, pa = pb.concat edge(vb→va)
      have h_pa_eq := hK.path_concat pb.property pa.property h_adj.symm hvb_on_pa

      -- vb on pa means va not on pb (already have this)
      have h_va_not_on_pb : va ∉ pb.val.support := hva_on_pb

      -- pathIntegral pa = pathIntegral pb + contribution(vb→va)
      obtain ⟨newPath, h_integral_eq⟩ := pathIntegral_concat_edge K f pb h_adj.symm h_va_not_on_pb
      have h_path_eq : newPath = pa := acyclic_path_unique K hK root va newPath pa

      rw [← h_path_eq] at h_integral_eq

      have h_a_reach_eq : (⟨vertexOfSimplex {a} (Finset.card_singleton a),
          vertexOfSimplex_in_vertexSet K {a} ha⟩ : K.vertexSet) = va := by
        apply Subtype.ext; simp only [vertexOfSimplex, Finset.min'_singleton]
      have h_b_reach_eq : (⟨vertexOfSimplex {b} (Finset.card_singleton b),
          vertexOfSimplex_in_vertexSet K {b} hb⟩ : K.vertexSet) = vb := by
        apply Subtype.ext; simp only [vertexOfSimplex, Finset.min'_singleton]

      simp only [h_a_reach_eq, h_b_reach_eq, dif_pos h_reach_a, dif_pos h_reach_b]

      -- h_integral_eq: pathIntegral newPath = pathIntegral pb + (if vb.val < va.val then 1 else -1) * f edge(vb, va)
      -- Since a < b, we have vb.val = b > a = va.val, so va.val < vb.val, so vb.val < va.val is false
      -- Wait, let me reconsider: va.val = a, vb.val = b, and a < b (h_lt)
      -- So vb.val < va.val is false (b < a is false since a < b)
      -- So the sign is -1
      -- pathIntegral pa = pathIntegral pb + (-1) * f ⟨{vb.val, va.val}, _⟩
      -- = pathIntegral pb - f ⟨{a, b}, _⟩  (since {vb.val, va.val} = {b, a} = {a, b})
      -- So: pathIntegral pb - pathIntegral pa = f ⟨{a, b}, _⟩ = f e

      have h_edge_simplex_eq : ({vb.val, va.val} : Simplex) = {a, b} := by
        simp only [va, vb]
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

      have h_e_eq : (⟨{vb.val, va.val}, ⟨h_adj.symm.2, Finset.card_pair h_adj.symm.1⟩⟩ : { s : Simplex // s ∈ K.ksimplices 1 }) = e := by
        apply Subtype.ext
        simp only [h_edge_simplex_eq, h_eq]

      rw [h_e_eq] at h_integral_eq

      -- vb.val = b, va.val = a, and a < b, so vb.val < va.val is (b < a) which is false
      have h_not_lt : ¬(vb.val < va.val) := by simp only [va, vb]; omega

      simp only [h_not_lt, ↓reduceIte, neg_one_mul] at h_integral_eq

      rw [pathIntegral_well_defined K hK f pa (pathBetween K h_reach_a)]
      rw [pathIntegral_well_defined K hK f pb (pathBetween K h_reach_b)]
      rw [pathIntegral_well_defined K hK f newPath pa] at h_integral_eq
      linarith

  · -- a is not reachable from root
    -- Use the cocycle_zero lemma
    have h_zero := cocycle_zero_on_unreachable_component K hK f hf root hconn e a b ha.1 hb.1 h_eq h_reach_a

    -- The witness values:
    -- g({a}) = 0 (a not reachable)
    -- g({b}) = 0 or pathIntegral (depending on b's reachability)

    -- If b is also not reachable: g({b}) = 0, so g({b}) - g({a}) = 0 = f(e)
    -- If b is reachable: contradiction (since a,b adjacent and b reachable implies a reachable)

    by_cases h_reach_b : (oneSkeleton K).Reachable root vb
    · -- b reachable but a not: contradiction
      exfalso
      apply h_reach_a
      exact h_reach_b.trans (SimpleGraph.Adj.reachable h_adj.symm)
    · -- Both not reachable
      simp only [toVertex, vertexOfSimplex]
      -- Need to show g({b}) - g({a}) = f(e) = 0
      rw [h_zero]
      -- g({a}) = 0, g({b}) = 0 (both not reachable)
      -- The toVertex of {a} is a, and toVertex of {b} is b
      -- We need to show the reachability conditions match
      have h_a_eq : (⟨vertexOfSimplex {a} (Finset.card_singleton a),
          vertexOfSimplex_in_vertexSet K {a} ha⟩ : K.vertexSet) = va := by
        apply Subtype.ext
        simp only [vertexOfSimplex, Finset.min'_singleton]
      have h_b_eq : (⟨vertexOfSimplex {b} (Finset.card_singleton b),
          vertexOfSimplex_in_vertexSet K {b} hb⟩ : K.vertexSet) = vb := by
        apply Subtype.ext
        simp only [vertexOfSimplex, Finset.min'_singleton]
      simp only [h_a_eq, h_b_eq, dif_neg h_reach_a, dif_neg h_reach_b, sub_zero]

theorem oneConnected_implies_h1_trivial (K : SimplicialComplex) (hK : OneConnected K)
    (hconn : (oneSkeleton K).Preconnected)
    [Nonempty K.vertexSet] : H1Trivial K := by
  intro f hf
  use coboundaryWitness K hK f hf (selectRoot K)
  exact coboundaryWitness_works K hK f hf (selectRoot K) hconn

end H1Characterization
