/-
  H1Characterization/CycleCochain/Proofs.lean

  Proofs that require ForestCoboundary lemmas.
  Completes the axioms from Definitions.lean.

  Note: Many proofs axiomatized due to mathlib 4.16.0 API changes.
  The mathematical content is standard simplicial cohomology theory.
-/

import H1Characterization.CycleCochain.Definitions
import H1Characterization.ForestCoboundary

namespace H1Characterization

/-! ## Proofs Using ForestCoboundary -/

-- Key lemma: coboundary on an oriented edge
-- This is a direct calculation from the coboundary definition.
-- Proof: (δ⁰g)(e) = ∑ᵢ sign(i) * g(e.face i) = g({tgt}) - g({src}) for edge e = {src, tgt}
-- After multiplying by oe.sign, the signs work out correctly.
theorem oriented_edge_coboundary_proof (K : SimplicialComplex) (g : Cochain K 0)
    (oe : OrientedEdge K) :
    oe.sign * (δ K 0 g) ⟨oe.toSimplex, oe.mem_edges⟩ =
    g (vertex0Simplex K oe.tgt) - g (vertex0Simplex K oe.src) := by
  -- The coboundary on a 1-simplex (edge) is:
  -- (δ⁰g)(e) = Σᵢ sign(i) * g(e.face i)
  -- For edge e = {a, b} with a < b (canonical ordering):
  --   face 0 = {b} (remove first vertex a), face 1 = {a} (remove second vertex b)
  --   (δ⁰g)(e) = sign(0) * g({b}) + sign(1) * g({a}) = g({b}) - g({a})
  --
  -- The OrientedEdge has src and tgt which may or may not be in canonical order.
  -- oe.sign = 1 if src < tgt, -1 if src > tgt
  --
  -- Case 1: src < tgt (oe.sign = 1)
  --   e = {src, tgt} in canonical order
  --   (δ⁰g)(e) = g({tgt}) - g({src})
  --   oe.sign * (δ⁰g)(e) = g({tgt}) - g({src}) ✓
  --
  -- Case 2: src > tgt (oe.sign = -1)
  --   e = {tgt, src} = {src, tgt} (same set, canonical order is {tgt, src})
  --   (δ⁰g)(e) = g({src}) - g({tgt}) (since src is second in canonical order)
  --   oe.sign * (δ⁰g)(e) = -1 * (g({src}) - g({tgt})) = g({tgt}) - g({src}) ✓

  simp only [OrientedEdge.sign, OrientedEdge.toSimplex, coboundary, vertex0Simplex]
  -- e = {src.val, tgt.val}
  -- We need to compute the sum over faces
  have h_card : ({oe.src.val, oe.tgt.val} : Simplex).card = 2 := Finset.card_pair oe.adj.1
  -- The two faces of a 2-element set are singletons
  -- After sorting, if a < b then sorted = [a, b], face 0 = {b}, face 1 = {a}

  by_cases h : oe.src.val < oe.tgt.val
  · -- Case: src < tgt, oe.sign = 1
    simp only [h, ↓reduceIte, one_mul]
    -- The edge {src, tgt} has canonical order [src, tgt]
    -- face 0 removes src, giving {tgt}
    -- face 1 removes tgt, giving {src}
    -- δg(e) = sign(0)*g({tgt}) + sign(1)*g({src}) = g({tgt}) - g({src})
    -- We need: Σᵢ sign(i) * g(face i) = g({tgt}) - g({src})

    -- Compute the sum explicitly for a 2-element set
    have h_sum : ∑ i : Fin ({oe.src.val, oe.tgt.val} : Simplex).card,
        Foundations.sign i.val * g ⟨({oe.src.val, oe.tgt.val} : Simplex).face i, _⟩ =
        g ⟨{oe.tgt.val}, _⟩ - g ⟨{oe.src.val}, _⟩ := by
      rw [show ({oe.src.val, oe.tgt.val} : Simplex).card = 2 from h_card]
      simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
      simp only [Foundations.sign_zero, Foundations.sign_one, one_mul, neg_one_mul]
      -- Need to identify the faces
      -- For {a, b} with a < b: sorted = [a, b]
      -- face ⟨0, _⟩ removes sorted[0] = a, leaving {b}
      -- face ⟨1, _⟩ removes sorted[1] = b, leaving {a}
      have h_sort : ({oe.src.val, oe.tgt.val} : Simplex).sort (· ≤ ·) = [oe.src.val, oe.tgt.val] := by
        rw [Finset.sort_pair h]
      have h_face0 : ({oe.src.val, oe.tgt.val} : Simplex).face ⟨0, by rw [h_card]; omega⟩ = {oe.tgt.val} := by
        simp only [Simplex.face]
        rw [h_sort]
        simp only [List.get_cons_zero, Finset.erase_insert_eq_erase]
        simp only [Finset.mem_singleton, oe.adj.1.symm, not_false_eq_true, Finset.erase_eq_of_not_mem]
      have h_face1 : ({oe.src.val, oe.tgt.val} : Simplex).face ⟨1, by rw [h_card]; omega⟩ = {oe.src.val} := by
        simp only [Simplex.face]
        rw [h_sort]
        simp only [List.get_cons_succ, List.get_cons_zero]
        ext x
        simp only [Finset.mem_erase, ne_eq, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro ⟨hne, hx⟩
          rcases hx with rfl | rfl
          · rfl
          · exact absurd rfl hne
        · intro hx
          subst hx
          exact ⟨oe.adj.1.symm, Or.inl rfl⟩
      congr 1
      · congr 1
        exact Subtype.ext h_face0
      · congr 1
        exact Subtype.ext h_face1
    convert h_sum using 2 <;> simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] <;>
      constructor <;> try rfl
    · have := K.has_vertices _ oe.adj.2 oe.tgt.val (by simp)
      simp only [Simplex.vertex] at this; exact this
    · exact Finset.card_singleton _
    · have := K.has_vertices _ oe.adj.2 oe.src.val (by simp)
      simp only [Simplex.vertex] at this; exact this
    · exact Finset.card_singleton _
  · -- Case: src ≥ tgt, oe.sign = -1
    simp only [h, ↓reduceIte, neg_one_mul, neg_sub]
    push_neg at h
    -- Either src = tgt (impossible for an edge) or src > tgt
    have h_ne : oe.src.val ≠ oe.tgt.val := oe.adj.1
    have h_gt : oe.src.val > oe.tgt.val := Nat.lt_of_le_of_ne h h_ne

    -- The edge {src, tgt} = {tgt, src} has canonical order [tgt, src]
    -- face 0 removes tgt, giving {src}
    -- face 1 removes src, giving {tgt}
    -- δg(e) = sign(0)*g({src}) + sign(1)*g({tgt}) = g({src}) - g({tgt})
    -- We need: g({src}) - g({tgt})

    have h_sum : ∑ i : Fin ({oe.src.val, oe.tgt.val} : Simplex).card,
        Foundations.sign i.val * g ⟨({oe.src.val, oe.tgt.val} : Simplex).face i, _⟩ =
        g ⟨{oe.src.val}, _⟩ - g ⟨{oe.tgt.val}, _⟩ := by
      rw [show ({oe.src.val, oe.tgt.val} : Simplex).card = 2 from h_card]
      simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
      simp only [Foundations.sign_zero, Foundations.sign_one, one_mul, neg_one_mul]
      -- For {a, b} with b < a: {a, b} = {b, a}, sorted = [b, a]
      -- face ⟨0, _⟩ removes sorted[0] = b, leaving {a}
      -- face ⟨1, _⟩ removes sorted[1] = a, leaving {b}
      have h_eq : ({oe.src.val, oe.tgt.val} : Simplex) = {oe.tgt.val, oe.src.val} := by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      have h_sort : ({oe.src.val, oe.tgt.val} : Simplex).sort (· ≤ ·) = [oe.tgt.val, oe.src.val] := by
        rw [h_eq, Finset.sort_pair h_gt]
      have h_face0 : ({oe.src.val, oe.tgt.val} : Simplex).face ⟨0, by rw [h_card]; omega⟩ = {oe.src.val} := by
        simp only [Simplex.face]
        rw [h_sort]
        simp only [List.get_cons_zero]
        ext x
        simp only [Finset.mem_erase, ne_eq, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro ⟨hne, hx⟩
          rcases hx with rfl | rfl
          · rfl
          · exact absurd rfl hne
        · intro hx
          subst hx
          exact ⟨h_ne, Or.inl rfl⟩
      have h_face1 : ({oe.src.val, oe.tgt.val} : Simplex).face ⟨1, by rw [h_card]; omega⟩ = {oe.tgt.val} := by
        simp only [Simplex.face]
        rw [h_sort]
        simp only [List.get_cons_succ, List.get_cons_zero, Finset.erase_insert_eq_erase]
        simp only [Finset.mem_singleton, h_ne, not_false_eq_true, Finset.erase_eq_of_not_mem]
      congr 1
      · congr 1
        exact Subtype.ext h_face0
      · congr 1
        exact Subtype.ext h_face1
    convert h_sum using 2 <;> simp only [SimplicialComplex.ksimplices, Set.mem_setOf_eq] <;>
      constructor <;> try rfl
    · have := K.has_vertices _ oe.adj.2 oe.src.val (by simp)
      simp only [Simplex.vertex] at this; exact this
    · exact Finset.card_singleton _
    · have := K.has_vertices _ oe.adj.2 oe.tgt.val (by simp)
      simp only [Simplex.vertex] at this; exact this
    · exact Finset.card_singleton _

/-!
## Cycle Indicator Self-Contribution Proof

A cycle is a trail, meaning no edge is repeated. This proof requires showing that:
1. Each oriented edge appears exactly once in the walkToOrientedEdges list
2. If oe.src < oe.tgt, then oe appears with that orientation (countPositive = 1, countNegative = 0)
3. If oe.tgt < oe.src, then oe appears reversed (countPositive = 0, countNegative = 1)

This requires lemmas about:
- SimpleGraph.Walk.IsTrail → edges.Nodup (no repeated edges in trail)
- walkToOrientedEdges preserves edge uniqueness
- Counting properties in lists with Nodup

These are standard graph theory facts.
-/

-- Helper lemma: in a trail, an oriented edge appears with exactly one orientation
theorem cycleIndicator_self_contribution_proof (K : SimplicialComplex) {v : K.vertexSet}
    (C : Walk K v v) (hC : C.IsCycle) :
    ∀ oe ∈ walkToOrientedEdges K C,
      oe.sign * cycleIndicator K C ⟨oe.toSimplex, oe.mem_edges⟩ = 1 := by
  intro oe hoe
  -- A cycle is a trail (no repeated edges) with length ≥ 3
  -- Therefore each edge appears exactly once with one specific orientation

  simp only [cycleIndicator, countPositive, countNegative]
  simp only [OrientedEdge.sign]

  -- oe is in walkToOrientedEdges K C, so it's an edge of C
  -- Since C is a trail, each edge appears exactly once
  -- oe has either src < tgt (positive) or tgt < src (negative)

  by_cases h : oe.src.val < oe.tgt.val
  · -- Case: src < tgt, so oe.sign = 1
    simp only [h, ↓reduceIte, one_mul]
    -- oe contributes 1 to countPositive and 0 to countNegative
    -- Since it's a trail, this edge appears exactly once with this orientation
    -- So countPositive = 1 and countNegative = 0
    -- cycleIndicator = 1 - 0 = 1 ✓

    -- The key insight: in a trail, each undirected edge appears at most once
    -- If oe is in walkToOrientedEdges with src < tgt, then:
    -- - countPositive counts edges matching (toSimplex, src < tgt) = 1 (just oe)
    -- - countNegative counts edges matching (toSimplex, tgt < src) = 0 (opposite orientation)

    have h_trail : C.IsTrail := hC.isTrail
    -- A trail has no repeated edges (as darts)
    have h_nodup : C.darts.Nodup := h_trail.darts_nodup

    -- countPositive = 1: oe matches itself exactly once
    have h_pos : (walkToOrientedEdges K C).countP
        (fun oe' => oe'.toSimplex = oe.toSimplex ∧ oe'.src.val < oe'.tgt.val) = 1 := by
      -- oe is in the list and matches the predicate
      -- The list has no duplicates (from trail), so it appears exactly once
      unfold walkToOrientedEdges at hoe ⊢
      simp only [List.mem_map] at hoe
      obtain ⟨d, hd_mem, hd_eq⟩ := hoe
      -- d is a dart in C.darts, and oe = ⟨d.fst, d.snd, d.adj⟩
      -- Need to count how many darts d' have the same simplex and src < tgt

      -- Since C is a trail, each undirected edge {a,b} appears at most once
      -- The simplex oe.toSimplex = {src, tgt}
      -- If d' maps to an oriented edge with the same simplex and src' < tgt',
      -- then {d'.fst.val, d'.snd.val} = {src, tgt} and d'.fst.val < d'.snd.val
      -- This means d'.fst = src and d'.snd = tgt (same dart)
      -- So d' = d (by nodup)

      -- Count = 1 because:
      -- 1. oe itself matches (oe ∈ list and satisfies predicate)
      -- 2. No other element matches (trail + same simplex + same orientation → same dart)
      rw [List.countP_eq_one]
      use d
      constructor
      · exact hd_mem
      constructor
      · simp only [hd_eq, OrientedEdge.toSimplex]
        exact ⟨rfl, h⟩
      · intro d' hd'_mem hd'_pred
        -- d' has the same simplex and orientation as d
        simp only at hd'_pred
        obtain ⟨h_simp, h_lt⟩ := hd'_pred
        -- The simplex {d'.fst.val, d'.snd.val} = {src, tgt} = {d.fst.val, d.snd.val}
        simp only [hd_eq, OrientedEdge.toSimplex] at h_simp
        -- Since d'.fst.val < d'.snd.val and d.fst.val < d.snd.val (= h),
        -- and the sets are equal, we must have d'.fst = d.fst and d'.snd = d.snd
        have h_eq_fst : d'.fst = d.fst := by
          have : d'.fst.val ∈ ({d.fst.val, d.snd.val} : Finset ℕ) := by
            rw [← h_simp]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | h_eq
          · rfl
          · -- d'.fst.val = d.snd.val, but d'.fst.val < d'.snd.val
            -- and d'.snd.val ∈ {d.fst.val, d.snd.val}
            have h_snd_mem : d'.snd.val ∈ ({d.fst.val, d.snd.val} : Finset ℕ) := by
              rw [← h_simp]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at h_snd_mem
            rcases h_snd_mem with h_eq2 | rfl
            · -- d'.snd.val = d.fst.val
              -- Then d'.fst.val = d.snd.val > d.fst.val = d'.snd.val
              -- But d'.fst.val < d'.snd.val, contradiction
              subst h_eq h_eq2
              omega
            · -- d'.snd.val = d.snd.val, d'.fst.val = d.snd.val
              -- Then d'.fst.val = d'.snd.val, contradicting d'.fst.val < d'.snd.val
              subst h_eq
              omega
        have h_eq_snd : d'.snd = d.snd := by
          have : d'.snd.val ∈ ({d.fst.val, d.snd.val} : Finset ℕ) := by
            rw [← h_simp]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h_eq | rfl
          · -- d'.snd.val = d.fst.val
            have h_fst_eq : d'.fst.val = d.fst.val := congrArg Subtype.val h_eq_fst
            -- d'.fst.val = d.fst.val < d.snd.val (by h : oe.src.val < oe.tgt.val)
            -- d'.snd.val = d.fst.val
            -- So d'.fst.val = d.fst.val and d'.snd.val = d.fst.val
            -- But d'.fst.val < d'.snd.val, so d.fst.val < d.fst.val, contradiction
            simp only [hd_eq] at h
            subst h_eq
            omega
          · rfl
        -- Now d'.fst = d.fst and d'.snd = d.snd
        ext <;> [exact congrArg Subtype.val h_eq_fst; exact congrArg Subtype.val h_eq_snd]

    -- countNegative = 0: no edge has same simplex with opposite orientation
    have h_neg : (walkToOrientedEdges K C).countP
        (fun oe' => oe'.toSimplex = oe.toSimplex ∧ oe'.tgt.val < oe'.src.val) = 0 := by
      rw [List.countP_eq_zero]
      intro oe' hoe'
      simp only [not_and]
      intro h_simp
      -- oe' has the same simplex as oe: {oe'.src, oe'.tgt} = {oe.src, oe.tgt}
      -- oe has src < tgt
      -- If oe' has tgt' < src', then the orientation is reversed
      -- But a trail uses each undirected edge at most once
      -- So if oe (with src < tgt) is in the list, the reversed version isn't

      -- This is because in a SimpleGraph.Walk, each dart encodes direction
      -- If we traverse edge {a,b} going a→b, we get dart (a,b)
      -- If we traverse it going b→a, we get dart (b,a)
      -- A trail can't have both (a,b) and (b,a) because that would mean
      -- using the same undirected edge twice

      intro h_rev
      -- oe' has same simplex as oe but opposite orientation
      -- oe': tgt' < src', oe: src < tgt
      -- Simplex {oe'.src, oe'.tgt} = {oe.src, oe.tgt}

      unfold walkToOrientedEdges at hoe hoe'
      simp only [List.mem_map] at hoe hoe'
      obtain ⟨d, hd_mem, hd_eq⟩ := hoe
      obtain ⟨d', hd'_mem, hd'_eq⟩ := hoe'

      -- d and d' are distinct darts with the same underlying edge
      -- d goes from lower to higher (src < tgt)
      -- d' goes from higher to lower (tgt' < src')
      simp only [hd_eq, hd'_eq, OrientedEdge.toSimplex] at h_simp

      -- d.toSym2 = d'.toSym2 (same undirected edge)
      -- But d and d' have opposite directions
      have h_same_edge : d.toProd.1.val ∈ ({d'.toProd.1.val, d'.toProd.2.val} : Finset ℕ) ∧
                         d.toProd.2.val ∈ ({d'.toProd.1.val, d'.toProd.2.val} : Finset ℕ) := by
        constructor
        · have : d.toProd.1.val ∈ ({d.toProd.1.val, d.toProd.2.val} : Finset ℕ) := by simp
          rw [h_simp] at this; exact this
        · have : d.toProd.2.val ∈ ({d.toProd.1.val, d.toProd.2.val} : Finset ℕ) := by simp
          rw [h_simp] at this; exact this

      simp only [Finset.mem_insert, Finset.mem_singleton] at h_same_edge
      obtain ⟨h1, h2⟩ := h_same_edge

      simp only [hd_eq] at h
      simp only [hd'_eq] at h_rev

      -- d: d.fst → d.snd with d.fst.val < d.snd.val
      -- d': d'.fst → d'.snd with d'.snd.val < d'.fst.val

      -- From h_simp: {d.fst.val, d.snd.val} = {d'.fst.val, d'.snd.val}
      -- From h: d.fst.val < d.snd.val
      -- From h_rev: d'.snd.val < d'.fst.val

      -- So the smaller element is d.fst.val and d'.snd.val
      -- The larger element is d.snd.val and d'.fst.val

      rcases h1 with h1a | h1b <;> rcases h2 with h2a | h2b
      · -- d.fst = d'.fst, d.snd = d'.fst → d.snd = d.fst, contradiction with h
        subst h1a h2a; omega
      · -- d.fst = d'.fst, d.snd = d'.snd
        -- Then d = d' but h says d.fst < d.snd and h_rev says d'.snd < d'.fst
        -- Contradiction: d.fst < d.snd and d.snd < d.fst
        subst h1a h2b; omega
      · -- d.fst = d'.snd, d.snd = d'.fst
        -- d goes low→high, d' goes high→low
        -- They traverse the same edge in opposite directions
        -- This means d.symm = d' (as darts)
        -- A trail can't contain both d and d.symm

        have h_symm : d.symm = d' := by
          ext
          · simp only [SimpleGraph.Dart.symm, h1b]
          · simp only [SimpleGraph.Dart.symm, h2a]

        -- In a trail, edges are not repeated, but d and d.symm share the same edge
        -- Actually, IsTrail.darts_nodup means darts (including direction) are unique
        -- But d ≠ d.symm, so both could appear... unless we use a stronger property

        -- Actually, IsTrail means edges (not darts) are unique
        -- So if d is in the trail, d.symm cannot be (same undirected edge)
        have h_edges_nodup : C.edges.Nodup := h_trail.edges_nodup
        -- edges is the list of Sym2 (undirected edges)
        -- d and d' = d.symm have the same Sym2

        have h_d_edge : d.edge ∈ C.edges := SimpleGraph.Walk.dart_edge_mem_edges hd_mem
        have h_d'_edge : d'.edge ∈ C.edges := SimpleGraph.Walk.dart_edge_mem_edges hd'_mem
        have h_same : d.edge = d'.edge := by
          rw [← h_symm]
          simp only [SimpleGraph.Dart.edge_symm]

        -- Both d.edge and d'.edge are in C.edges with d.edge = d'.edge
        -- And edges are nodup, so they must be the same occurrence
        -- But we'd need to show d = d' which contradicts h ≠ h_rev

        -- Actually, List.Nodup means no duplicates, so if d.edge = d'.edge
        -- and both are in edges, they must be at the same position
        -- But d and d' came from different darts... unless they're the same dart

        -- The issue is that darts_nodup doesn't prevent d and d.symm
        -- We need to use edges_nodup

        -- If d.edge = d'.edge and both d.edge, d'.edge ∈ C.edges and C.edges.Nodup,
        -- then they're the same element of the list.
        -- But C.edges = C.darts.map Dart.edge
        -- So if d.edge = d'.edge appears twice, it would violate Nodup

        -- Actually, the issue is more subtle. Let me think again.
        -- C.edges can have the same edge multiple times (from different traversals)
        -- But IsTrail says edges.Nodup, so each undirected edge appears once.
        -- Therefore, d and d' must be the same dart (contradicting opposite orientations)

        have h_false : d = d' := by
          -- Both d and d' contribute the same edge to C.edges
          -- Since C.edges is nodup, this edge appears exactly once
          -- So d and d' must be the same dart
          by_contra h_ne
          -- d.edge and d'.edge are both in C.edges at different positions
          -- (because d ≠ d' but they're both in C.darts)
          -- This contradicts C.edges.Nodup

          -- Get positions of d and d' in C.darts
          have ⟨i, hi, hi_eq⟩ := List.mem_iff_getElem.mp hd_mem
          have ⟨j, hj, hj_eq⟩ := List.mem_iff_getElem.mp hd'_mem

          -- If i = j then d = d', contradiction
          have h_i_ne_j : i ≠ j := by
            intro h_eq
            subst h_eq
            have : d = d' := by rw [← hi_eq, ← hj_eq]
            exact h_ne this

          -- C.edges = C.darts.map Dart.edge
          -- So C.edges[i] = d.edge and C.edges[j] = d'.edge
          have h_edges_eq : C.edges = C.darts.map SimpleGraph.Dart.edge := rfl
          have h_len : C.edges.length = C.darts.length := by simp [h_edges_eq]

          have hi' : i < C.edges.length := by rw [h_len]; exact hi
          have hj' : j < C.edges.length := by rw [h_len]; exact hj

          have h_ei : C.edges[i] = d.edge := by
            simp only [h_edges_eq, List.getElem_map, hi_eq]
          have h_ej : C.edges[j] = d'.edge := by
            simp only [h_edges_eq, List.getElem_map, hj_eq]

          -- d.edge = d'.edge = h_same
          -- So C.edges[i] = C.edges[j] with i ≠ j
          -- This contradicts h_edges_nodup

          have h_dup : C.edges[i] = C.edges[j] := by rw [h_ei, h_ej, h_same]
          exact h_edges_nodup.getElem_ne_getElem h_i_ne_j h_dup

        -- But d = d' means d.fst = d'.fst and d.snd = d'.snd
        -- Which means d.fst.val < d.snd.val (from h) and d'.snd.val < d'.fst.val (from h_rev)
        -- So d.fst.val < d.snd.val = d'.snd.val < d'.fst.val = d.fst.val
        -- Contradiction!
        subst h_false
        omega

      · -- d.fst = d'.snd, d.snd = d'.snd → d.fst = d.snd, contradiction with h
        subst h1b h2b; omega

    -- Combine: cycleIndicator = countPositive - countNegative = 1 - 0 = 1
    simp only [h_pos, h_neg, Nat.cast_one, Nat.cast_zero, sub_zero]

  · -- Case: src ≥ tgt, so oe.sign = -1
    simp only [h, ↓reduceIte, neg_one_mul, neg_sub]
    push_neg at h
    have h_ne : oe.src.val ≠ oe.tgt.val := oe.adj.1
    have h_gt : oe.src.val > oe.tgt.val := Nat.lt_of_le_of_ne h h_ne

    -- Similar to the above case but with reversed orientation
    -- countPositive = 0, countNegative = 1
    -- cycleIndicator = 0 - 1 = -1
    -- oe.sign * (-1) = (-1) * (-1) = 1 ✓

    have h_trail : C.IsTrail := hC.isTrail

    have h_pos : (walkToOrientedEdges K C).countP
        (fun oe' => oe'.toSimplex = oe.toSimplex ∧ oe'.src.val < oe'.tgt.val) = 0 := by
      rw [List.countP_eq_zero]
      intro oe' hoe'
      simp only [not_and]
      intro h_simp h_lt
      -- Similar contradiction argument
      unfold walkToOrientedEdges at hoe hoe'
      simp only [List.mem_map] at hoe hoe'
      obtain ⟨d, hd_mem, hd_eq⟩ := hoe
      obtain ⟨d', hd'_mem, hd'_eq⟩ := hoe'

      simp only [hd_eq, hd'_eq, OrientedEdge.toSimplex] at h_simp

      have h_edges_nodup : C.edges.Nodup := h_trail.edges_nodup

      -- oe has tgt < src (h_gt), oe' has src' < tgt' (h_lt)
      -- Same simplex means same undirected edge
      -- Trail means this edge appears once, so d = d'
      -- But d has one direction, d' has opposite, contradiction

      have h_d_edge : d.edge ∈ C.edges := SimpleGraph.Walk.dart_edge_mem_edges hd_mem
      have h_d'_edge : d'.edge ∈ C.edges := SimpleGraph.Walk.dart_edge_mem_edges hd'_mem

      have h_same : d.edge = d'.edge := by
        simp only [SimpleGraph.Dart.edge, Sym2.eq, Sym2.rel_iff']
        simp only [hd_eq, hd'_eq] at h_gt h_lt h_simp
        -- {d.fst.val, d.snd.val} = {d'.fst.val, d'.snd.val}
        -- with d.snd.val < d.fst.val and d'.fst.val < d'.snd.val
        left
        constructor
        · have : d.fst.val ∈ ({d'.fst.val, d'.snd.val} : Finset ℕ) := by
            rw [← h_simp]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | h_eq
          · rfl
          · -- d.fst.val = d'.snd.val, d.snd.val < d.fst.val = d'.snd.val < d'.fst.val
            -- But d.snd.val must be in {d'.fst.val, d'.snd.val}
            have : d.snd.val ∈ ({d'.fst.val, d'.snd.val} : Finset ℕ) := by
              rw [← h_simp]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h_eq2 | rfl
            · -- d.snd = d'.fst, d.fst = d'.snd
              subst h_eq h_eq2
              omega
            · -- d.snd = d'.snd, d.fst = d'.snd → d.fst = d.snd
              subst h_eq
              omega
        · have : d.snd.val ∈ ({d'.fst.val, d'.snd.val} : Finset ℕ) := by
            rw [← h_simp]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h_eq | rfl
          · -- d.snd = d'.fst, need to show d.fst = d'.snd
            have : d.fst.val ∈ ({d'.fst.val, d'.snd.val} : Finset ℕ) := by
              rw [← h_simp]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | h_eq2
            · -- d.fst = d'.fst = d.snd, contradicts h_gt
              subst h_eq; omega
            · subst h_eq h_eq2; rfl
          · -- d.snd = d'.snd, but d.snd < d.fst and d'.fst < d'.snd = d.snd
            -- So d'.fst < d.snd < d.fst
            -- d.fst must be in {d'.fst, d'.snd} = {d'.fst, d.snd}
            have : d.fst.val ∈ ({d'.fst.val, d'.snd.val} : Finset ℕ) := by
              rw [← h_simp]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with rfl | h_eq
            · -- d.fst = d'.fst, d.snd = d'.snd, so d = d' same direction
              -- But d has snd < fst and d' has fst < snd, contradiction
              omega
            · -- d.fst = d'.snd = d.snd, contradicts h_gt
              subst h_eq; omega

      -- Same edge in nodup list means same dart
      have h_false : d = d' := by
        by_contra h_ne_dart
        have ⟨i, hi, hi_eq⟩ := List.mem_iff_getElem.mp hd_mem
        have ⟨j, hj, hj_eq⟩ := List.mem_iff_getElem.mp hd'_mem
        have h_i_ne_j : i ≠ j := by
          intro h_eq; subst h_eq
          have : d = d' := by rw [← hi_eq, ← hj_eq]
          exact h_ne_dart this
        have h_edges_eq : C.edges = C.darts.map SimpleGraph.Dart.edge := rfl
        have h_len : C.edges.length = C.darts.length := by simp [h_edges_eq]
        have hi' : i < C.edges.length := by rw [h_len]; exact hi
        have hj' : j < C.edges.length := by rw [h_len]; exact hj
        have h_ei : C.edges[i] = d.edge := by simp only [h_edges_eq, List.getElem_map, hi_eq]
        have h_ej : C.edges[j] = d'.edge := by simp only [h_edges_eq, List.getElem_map, hj_eq]
        have h_dup : C.edges[i] = C.edges[j] := by rw [h_ei, h_ej, h_same]
        exact h_edges_nodup.getElem_ne_getElem h_i_ne_j h_dup

      subst h_false
      simp only [hd_eq, hd'_eq] at h_gt h_lt
      omega

    have h_neg : (walkToOrientedEdges K C).countP
        (fun oe' => oe'.toSimplex = oe.toSimplex ∧ oe'.tgt.val < oe'.src.val) = 1 := by
      -- Similar to h_pos case but oe matches
      unfold walkToOrientedEdges at hoe ⊢
      simp only [List.mem_map] at hoe
      obtain ⟨d, hd_mem, hd_eq⟩ := hoe

      rw [List.countP_eq_one]
      use d
      constructor
      · exact hd_mem
      constructor
      · simp only [hd_eq, OrientedEdge.toSimplex]
        exact ⟨rfl, h_gt⟩
      · intro d' hd'_mem hd'_pred
        simp only at hd'_pred
        obtain ⟨h_simp, h_lt'⟩ := hd'_pred
        simp only [hd_eq, OrientedEdge.toSimplex] at h_simp

        have h_eq_fst : d'.fst = d.fst := by
          have : d'.fst.val ∈ ({d.fst.val, d.snd.val} : Finset ℕ) := by
            rw [← h_simp]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | h_eq
          · rfl
          · have : d'.snd.val ∈ ({d.fst.val, d.snd.val} : Finset ℕ) := by
              rw [← h_simp]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h_eq2 | rfl
            · subst h_eq h_eq2; omega
            · subst h_eq; omega
        have h_eq_snd : d'.snd = d.snd := by
          have : d'.snd.val ∈ ({d.fst.val, d.snd.val} : Finset ℕ) := by
            rw [← h_simp]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h_eq | rfl
          · have h_fst_eq : d'.fst.val = d.fst.val := congrArg Subtype.val h_eq_fst
            subst h_eq
            omega
          · rfl
        ext <;> [exact congrArg Subtype.val h_eq_fst; exact congrArg Subtype.val h_eq_snd]

    simp only [h_pos, h_neg, Nat.cast_zero, Nat.cast_one, zero_sub, neg_neg]

end H1Characterization
