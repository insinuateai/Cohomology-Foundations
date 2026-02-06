/-
# Component Edge Counting Infrastructure

Infrastructure for proving the disconnected_graph_edge_component_bound.

## Mathematical Insight

For a disconnected graph with c ≥ 2 components on n vertices:
1. Each edge lies entirely within one component
2. A component with k vertices has ≤ k(k-1)/2 edges
3. Max total edges with c components = (n-c+1)(n-c)/2 (when c-1 are singletons)
4. Algebraically: (n-c+1)(n-c)/2 + c ≤ n(n-1)/2 + 1 for c ∈ [2, n]

SORRIES: 0 (all proofs complete!)
AXIOMS: 0

Author: Infrastructure Team
Date: February 2026
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Infrastructure.ComponentEdgeCounting

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Section 1: Basic Component Lemmas -/

/-- Adjacent vertices are in the same connected component. -/
theorem adj_same_component (v w : V) (hadj : G.Adj v w) :
    G.connectedComponentMk v = G.connectedComponentMk w :=
  ConnectedComponent.eq.mpr hadj.reachable

/-- Every edge's endpoints are in the same connected component. -/
theorem edge_endpoints_same_component (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ∃ c : G.ConnectedComponent, ∀ u, u ∈ e → G.connectedComponentMk u = c := by
  classical
  -- Use Sym2.ind to handle the edge as s(a, b), carrying the hypothesis
  revert he
  refine Sym2.ind (fun a b => ?_) e
  intro he'
  -- Now he' : s(a,b) ∈ G.edgeSet, i.e., G.Adj a b
  use G.connectedComponentMk a
  intro u hu
  rcases Sym2.mem_iff.mp hu with ha | hb
  · -- u = a
    rw [ha]
  · -- u = b, need: G.connectedComponentMk b = G.connectedComponentMk a
    rw [hb]
    exact (adj_same_component G a b he').symm

/-! ## Section 1b: Component Counting Infrastructure -/

/-- Number of vertices in a connected component. -/
noncomputable def componentVertexCount [Fintype G.ConnectedComponent] (c : G.ConnectedComponent) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v => G.connectedComponentMk v = c)).card

/-- Edges within a connected component.
    An edge belongs to component c if both endpoints are in c. -/
noncomputable def componentEdges [Fintype G.edgeSet] (c : G.ConnectedComponent) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter (fun e => Sym2.lift ⟨fun v w =>
    G.connectedComponentMk v = c ∧ G.connectedComponentMk w = c,
    fun v w => by simp only [and_comm]⟩ e)

/-- Both endpoints of an edge in componentEdges are in the same component. -/
lemma componentEdges_endpoints [Fintype G.edgeSet] (c : G.ConnectedComponent)
    (e : Sym2 V) (he : e ∈ componentEdges G c) :
    ∀ u, u ∈ e → G.connectedComponentMk u = c := by
  classical
  simp only [componentEdges, Finset.mem_filter] at he
  obtain ⟨_, hc⟩ := he
  revert hc
  refine Sym2.ind (fun a b => ?_) e
  intro hab u hu
  simp only [Sym2.lift_mk] at hab
  rcases Sym2.mem_iff.mp hu with ha | hb
  · exact ha ▸ hab.1
  · exact hb ▸ hab.2

/-- Every edge belongs to exactly one component (the one containing both endpoints). -/
lemma mem_componentEdges_iff [Fintype G.edgeSet] (e : Sym2 V) (he : e ∈ G.edgeFinset) (c : G.ConnectedComponent) :
    e ∈ componentEdges G c ↔ ∀ u, u ∈ e → G.connectedComponentMk u = c := by
  classical
  constructor
  · exact componentEdges_endpoints G c e
  · intro h
    simp only [componentEdges, Finset.mem_filter]
    constructor
    · exact he
    · revert h
      refine Sym2.ind (fun a b => ?_) e
      intro h
      simp only [Sym2.lift_mk]
      exact ⟨h a (Sym2.mem_mk_left a b), h b (Sym2.mem_mk_right a b)⟩

/-- Edges partition by component: every edge is in exactly one componentEdges set. -/
lemma edge_mem_unique_component [Fintype G.edgeSet] (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    ∃! c : G.ConnectedComponent, e ∈ componentEdges G c := by
  classical
  obtain ⟨c, hc⟩ := edge_endpoints_same_component G e (mem_edgeFinset.mp he)
  use c
  refine ⟨?_, ?_⟩
  · show e ∈ componentEdges G c
    rw [mem_componentEdges_iff G e he]
    exact hc
  · intro c' hc'
    have h := componentEdges_endpoints G c' e hc'
    -- Get a vertex in e (Sym2 is always nonempty for inhabited types, use the edge structure)
    revert hc h
    refine Sym2.ind (fun a b => ?_) e
    intro hc h
    have h1 := hc a (Sym2.mem_mk_left a b)
    have h2 := h a (Sym2.mem_mk_left a b)
    exact h2.symm.trans h1

/-- Component edges are pairwise disjoint. -/
lemma pairwise_disjoint_componentEdges [Fintype G.edgeSet] [Fintype G.ConnectedComponent] :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset G.ConnectedComponent)) (componentEdges G) := by
  classical
  intro c₁ _ c₂ _ hne
  simp only [Function.onFun, Finset.disjoint_left]
  intro e he₁ he₂
  have h₁ := componentEdges_endpoints G c₁ e he₁
  have h₂ := componentEdges_endpoints G c₂ e he₂
  -- Get a vertex in e
  revert h₁ h₂
  refine Sym2.ind (fun a b => ?_) e
  intro h₁ h₂
  have ha₁ := h₁ a (Sym2.mem_mk_left a b)
  have ha₂ := h₂ a (Sym2.mem_mk_left a b)
  exact hne (ha₁.symm.trans ha₂)

/-- The union of all componentEdges equals edgeFinset. -/
lemma edgeFinset_eq_biUnion_componentEdges [Fintype G.edgeSet] [Fintype G.ConnectedComponent] :
    G.edgeFinset = Finset.biUnion Finset.univ (componentEdges G) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨c, hc, _⟩ := edge_mem_unique_component G e he
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨c, hc⟩
  · intro he
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at he
    obtain ⟨c, hc⟩ := he
    simp only [componentEdges, Finset.mem_filter] at hc
    exact hc.1

/-- Sum of component vertex counts equals total vertex count. -/
lemma sum_componentVertexCount_eq_card [Fintype G.ConnectedComponent] :
    Finset.univ.sum (componentVertexCount G) = Fintype.card V := by
  classical
  -- Define the partition function
  let f : G.ConnectedComponent → Finset V := fun c => Finset.univ.filter (fun v => G.connectedComponentMk v = c)
  -- Show that componentVertexCount equals card of f
  have hf_eq : ∀ c, componentVertexCount G c = (f c).card := by
    intro c
    simp only [componentVertexCount, f]
  -- Partition vertices by component
  have h_partition : (Finset.univ : Finset V) = Finset.biUnion Finset.univ f := by
    ext v
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, f]
    exact ⟨fun _ => ⟨G.connectedComponentMk v, rfl⟩, fun _ => trivial⟩
  have h_disjoint : Set.PairwiseDisjoint (↑(Finset.univ : Finset G.ConnectedComponent)) f := by
    intro c₁ _ c₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left, f]
    intro v hv₁ hv₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂
    exact hne (hv₁.symm.trans hv₂)
  calc Finset.univ.sum (componentVertexCount G)
      = Finset.univ.sum (fun c => (f c).card) := by simp only [hf_eq]
    _ = (Finset.biUnion Finset.univ f).card := (Finset.card_biUnion h_disjoint).symm
    _ = (Finset.univ : Finset V).card := by rw [← h_partition]
    _ = Fintype.card V := Finset.card_univ

/-- Each component has at least one vertex. -/
lemma componentVertexCount_pos [Fintype G.ConnectedComponent] (c : G.ConnectedComponent) :
    0 < componentVertexCount G c := by
  classical
  simp only [componentVertexCount]
  rw [Finset.card_pos]
  obtain ⟨v, hv⟩ := c.exists_rep
  use v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hv

/-- Component with k vertices has at most k(k-1)/2 edges. -/
lemma componentEdges_card_le [Fintype G.edgeSet] [Fintype G.ConnectedComponent] (c : G.ConnectedComponent) :
    (componentEdges G c).card ≤ componentVertexCount G c * (componentVertexCount G c - 1) / 2 := by
  classical
  -- The edges in component c form a graph on componentVertexCount G c vertices
  -- So they are bounded by the complete graph on that many vertices
  let vertices_in_c := Finset.univ.filter (fun v => G.connectedComponentMk v = c)
  have hk : vertices_in_c.card = componentVertexCount G c := by
    simp only [componentVertexCount, vertices_in_c]
  -- Each edge has distinct endpoints (from graph irreflexivity)
  -- and both endpoints in vertices_in_c
  -- So componentEdges G c ⊆ vertices_in_c.offDiag.image Sym2.mk
  have h_subset : componentEdges G c ⊆ vertices_in_c.offDiag.image Sym2.mk := by
    intro e he
    simp only [Finset.mem_image, Finset.mem_offDiag]
    -- Get endpoints of the edge
    have he_edge : e ∈ G.edgeFinset := by
      simp only [componentEdges, Finset.mem_filter] at he
      exact he.1
    -- e is an edge, so it has form s(a, b) with a ≠ b
    revert he he_edge
    refine Sym2.ind (fun a b => ?_) e
    intro he he_edge
    use (a, b)
    constructor
    · constructor
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, vertices_in_c]
        exact componentEdges_endpoints G c _ he a (Sym2.mem_mk_left a b)
      · constructor
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, vertices_in_c]
          exact componentEdges_endpoints G c _ he b (Sym2.mem_mk_right a b)
        · -- a ≠ b because it's an edge
          intro hab
          simp only at hab
          rw [hab] at he_edge
          simp only [mem_edgeFinset] at he_edge
          exact G.loopless b he_edge
    · rfl
  calc (componentEdges G c).card
      ≤ (vertices_in_c.offDiag.image Sym2.mk).card := Finset.card_le_card h_subset
    _ = vertices_in_c.card.choose 2 := Sym2.card_image_offDiag vertices_in_c
    _ = componentVertexCount G c * (componentVertexCount G c - 1) / 2 := by
        rw [hk, Nat.choose_two_right]

/-! ## Section 2: Algebraic Bounds -/

/-- Key algebraic fact: m(m-1) ≤ (n-1)(n-2) when m ≤ n - 2 and n ≥ 2. -/
theorem product_mono_bound (n m : ℕ) (hn : n ≥ 2) (hm : m ≤ n - 2) :
    m * (m - 1) ≤ (n - 1) * (n - 2) := by
  have h1 : m ≤ n - 1 := by omega
  have h2 : m - 1 ≤ n - 2 := by omega
  calc m * (m - 1) ≤ (n - 1) * (m - 1) := Nat.mul_le_mul_right _ h1
    _ ≤ (n - 1) * (n - 2) := Nat.mul_le_mul_left _ h2

/-- Main algebraic inequality: (n-c+1)*(n-c)/2 + c ≤ n*(n-1)/2 + 1 when c ≥ 2 and c ≤ n and n ≥ 2.

    Proof sketch:
    Let m = n - c. Then we need m(m+1)/2 + c ≤ n(n-1)/2 + 1.
    Equivalently: m(m+1) + 2c ≤ n(n-1) + 2.
    Since c = n - m: m(m+1) + 2(n-m) = m² - m + 2n = m(m-1) + 2n.
    We need: m(m-1) + 2n ≤ n(n-1) + 2.
    Equivalently: m(m-1) ≤ (n-1)(n-2).
    Since m ≤ n-2, this follows from product_mono_bound. -/
theorem disconnected_algebraic_bound (n c : ℕ) (hn : n ≥ 2) (hc_ge : c ≥ 2) (hc_le : c ≤ n) :
    (n - c + 1) * (n - c) / 2 + c ≤ n * (n - 1) / 2 + 1 := by
  set m := n - c with hm_def
  have hm_le : m ≤ n - 2 := by omega
  have h_mono := product_mono_bound n m hn hm_le
  -- Use Mathlib's even lemmas for consecutive integer products
  have h_m_even : Even (m * (m + 1)) := Nat.even_mul_succ_self m
  have h_n_even : Even (n * (n - 1)) := Nat.even_mul_pred_self n
  -- Get the half values
  obtain ⟨k_m, hk_m⟩ := h_m_even
  obtain ⟨k_n, hk_n⟩ := h_n_even
  -- Rewrite to use k values: hk_m says m*(m+1) = k_m + k_m = 2*k_m
  have h_m_div : m * (m + 1) / 2 = k_m := by
    have : k_m + k_m = 2 * k_m := by ring
    rw [hk_m, this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have h_n_div : n * (n - 1) / 2 = k_n := by
    have : k_n + k_n = 2 * k_n := by ring
    rw [hk_n, this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have h_m_comm : (m + 1) * m = m * (m + 1) := Nat.mul_comm _ _
  have h_lhs : (m + 1) * m / 2 = k_m := by rw [h_m_comm, h_m_div]
  -- Key inequality: m*(m+1) + 2c ≤ n*(n-1) + 2
  -- Equivalent to: m(m-1) + 2n ≤ n(n-1) + 2, i.e., m(m-1) ≤ (n-1)(n-2) ✓
  have key_ineq : m * (m + 1) + 2 * c ≤ n * (n - 1) + 2 := by
    -- Work with integers for cleaner subtraction
    have hc_eq : c = n - m := by omega
    -- Key identity: m*(m+1) + 2*(n-m) = m*(m-1) + 2*n (when m ≥ 1, else 0 + 2n = 2n)
    -- And: n*(n-1) + 2 = (n-1)*(n-2) + 2*n
    -- So we need: m*(m-1) ≤ (n-1)*(n-2), which is h_mono
    have key : m * (m - 1) + 2 * n ≤ (n - 1) * (n - 2) + 2 * n := by linarith [h_mono]
    -- Now show the LHS and RHS match these forms
    have lhs_form : m * (m + 1) + 2 * c = m * (m - 1) + 2 * n := by
      -- c = n - m, so 2*c = 2*n - 2*m
      -- m*(m+1) + 2*(n-m) = m² + m + 2n - 2m = m² - m + 2n = m*(m-1) + 2n (for m ≥ 1)
      -- For m = 0: 0 + 2*n = 0 + 2*n ✓
      cases hm : m with
      | zero =>
        simp only [Nat.zero_mul, Nat.zero_add]
        -- m = 0 means n - c = 0, so n ≤ c, combined with c ≤ n gives c = n
        have hcn : c = n := by
          have h1 : n - c = 0 := by rw [← hm_def, hm]
          have h2 : n ≤ c := Nat.sub_eq_zero_iff_le.mp h1
          exact le_antisymm hc_le h2
        simp [hcn]
      | succ m' =>
        simp only [Nat.add_sub_cancel]
        -- Goal: (m' + 1) * (m' + 1 + 1) + 2 * c = (m' + 1) * m' + 2 * n
        have hm'_bound : m' + 1 ≤ n - 2 := by rw [← hm]; exact hm_le
        have hn_ge : n ≥ m' + 3 := by omega
        have hc_val : c = n - m' - 1 := by omega
        -- Key algebraic identity (no subtraction on RHS)
        -- LHS = (m'+1)*(m'+2) + 2*c = (m'+1)*(m'+2) + 2*(n - m' - 1)
        -- Need n ≥ m' + 1 for subtraction to be valid
        have hn_sub : n ≥ m' + 1 := by omega
        have hc_expand : 2 * c = 2 * n - 2 * m' - 2 := by
          rw [hc_val]
          have h1 : n - m' - 1 = n - (m' + 1) := by omega
          rw [h1]
          omega
        -- (m'+1)*(m'+2) = m'² + 3m' + 2
        -- (m'+1)*m' = m'² + m'
        -- LHS = m'² + 3m' + 2 + 2n - 2m' - 2 = m'² + m' + 2n = RHS
        have h_lhs : (m' + 1) * (m' + 2) + 2 * c = (m' + 1) * (m' + 2) + (2 * n - 2 * m' - 2) := by
          rw [hc_expand]
        have h_expand : (m' + 1) * (m' + 2) + (2 * n - 2 * m' - 2) = (m' + 1) * m' + 2 * n := by
          have h1 : (m' + 1) * (m' + 2) = m' * m' + 3 * m' + 2 := by ring
          have h2 : (m' + 1) * m' = m' * m' + m' := by ring
          rw [h1, h2]
          omega
        rw [h_lhs, h_expand]
    have rhs_form : n * (n - 1) + 2 = (n - 1) * (n - 2) + 2 * n := by
      -- n * (n - 1) = n² - n, (n-1)*(n-2) = n² - 3n + 2
      -- LHS = n² - n + 2, RHS = n² - 3n + 2 + 2n = n² - n + 2 ✓
      obtain ⟨n', hn'⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
      rw [hn']
      -- Simplify the subtractions
      have h1 : n' + 2 - 1 = n' + 1 := by omega
      have h2 : n' + 2 - 2 = n' := by omega
      simp only [h1, h2]
      -- Goal: (n'+2) * (n'+1) + 2 = (n'+1) * n' + 2 * (n'+2)
      ring
    rw [lhs_form, rhs_form]
    exact key
  -- Convert from product inequality to half inequality using k values
  have from_key : k_m + c ≤ k_n + 1 := by
    have h1 : 2 * k_m + 2 * c ≤ 2 * k_n + 2 := by
      calc 2 * k_m + 2 * c = m * (m + 1) + 2 * c := by linarith
        _ ≤ n * (n - 1) + 2 := key_ineq
        _ = 2 * k_n + 2 := by linarith
    linarith
  -- Final calculation
  calc (n - c + 1) * (n - c) / 2 + c
      = (m + 1) * m / 2 + c := by rw [← hm_def]
    _ = k_m + c := by rw [h_lhs]
    _ ≤ k_n + 1 := from_key
    _ = n * (n - 1) / 2 + 1 := by rw [h_n_div]

/-- Components ≤ vertices for any graph with nonempty vertex set. -/
theorem components_le_vertices [Fintype G.ConnectedComponent] (hne : Nonempty V) :
    Fintype.card G.ConnectedComponent ≤ Fintype.card V := by
  let f : G.ConnectedComponent → V := fun c => c.exists_rep.choose
  have hf_inj : Function.Injective f := by
    intro c1 c2 h
    have h1 := c1.exists_rep.choose_spec
    have h2 := c2.exists_rep.choose_spec
    simp only [f] at h
    rw [← h1, ← h2, h]
  exact Fintype.card_le_of_injective f hf_inj

/-! ## Section 2b: Convexity Bound -/

/-- Key convexity lemma: For c ≥ 2 parts each with size ≥ 1 summing to n,
    the sum of k_i(k_i-1)/2 is at most (n-c+1)(n-c)/2.

    This is because f(x) = x(x-1)/2 is convex, so the maximum is achieved at
    an extreme point: c-1 singletons and one component of size n-c+1. -/
lemma sum_edges_le_concentrated {c n : ℕ} (hc : c ≥ 2) (hcn : c ≤ n)
    (sizes : Fin c → ℕ) (hsum : Finset.univ.sum sizes = n) (hpos : ∀ i, 1 ≤ sizes i) :
    Finset.univ.sum (fun i => sizes i * (sizes i - 1) / 2) ≤
    (n - c + 1) * (n - c) / 2 := by
  -- Strategy: Each component i has size k_i ≥ 1, and the largest possible
  -- component size is n - (c-1) = n - c + 1 (when c-1 components are singletons).
  -- Each term k_i(k_i-1)/2 is bounded by (n-c+1)(k_i-1)/2.

  -- Upper bound each component size: sizes i ≤ n - c + 1
  have h_max_size : ∀ i, sizes i ≤ n - c + 1 := by
    intro i
    -- The other c-1 components contribute at least c-1 to the sum
    have h_other_sum : (Finset.univ.erase i).sum sizes ≥ c - 1 := by
      calc (Finset.univ.erase i).sum sizes
          ≥ (Finset.univ.erase i).sum (fun _ => 1) := Finset.sum_le_sum (fun j _ => hpos j)
        _ = (Finset.univ.erase i).card := by simp
        _ = c - 1 := by simp [Finset.card_erase_of_mem]
    have h_decomp : sizes i + (Finset.univ.erase i).sum sizes = n := by
      rw [← hsum]
      conv_rhs => rw [← Finset.insert_erase (Finset.mem_univ i)]
      have h_not_mem : i ∉ Finset.univ.erase i := Finset.notMem_erase i _
      rw [Finset.sum_insert h_not_mem]
    omega
  -- Compute Σ(k_i - 1) = n - c
  have h_sum_sub : Finset.univ.sum (fun i => sizes i - 1) = n - c := by
    have h_ge : Finset.univ.sum sizes ≥ c := by
      calc Finset.univ.sum sizes ≥ Finset.univ.sum (fun _ => 1) := Finset.sum_le_sum (fun i _ => hpos i)
        _ = c := by simp
    -- Σ(k_i - 1) = Σk_i - c when each k_i ≥ 1
    have h_eq : Finset.univ.sum (fun i => sizes i - 1) + c = Finset.univ.sum sizes := by
      have : Finset.univ.sum (fun i => sizes i - 1) + Finset.univ.sum (fun _ : Fin c => 1) =
             Finset.univ.sum sizes := by
        rw [← Finset.sum_add_distrib]
        congr 1
        ext i
        have := hpos i
        omega
      simpa using this
    omega
  -- Use a simpler bound: Σ k(k-1)/2 ≤ (n-c+1) * Σ(k-1) / 2 = (n-c+1)(n-c)/2
  -- This follows since each k ≤ n-c+1
  have h_double_bound : 2 * Finset.univ.sum (fun i => sizes i * (sizes i - 1) / 2) ≤
                        (n - c + 1) * (n - c) := by
    -- 2 * Σ(f i / 2) ≤ Σ f i because 2 * (n / 2) ≤ n
    have h_two_mul_div : ∀ m : ℕ, 2 * (m / 2) ≤ m := fun m => by
      have : m / 2 * 2 ≤ m := Nat.div_mul_le_self m 2
      linarith
    calc 2 * Finset.univ.sum (fun i => sizes i * (sizes i - 1) / 2)
        ≤ 2 * Finset.univ.sum (fun i => (n - c + 1) * (sizes i - 1) / 2) := by
            apply Nat.mul_le_mul_left
            apply Finset.sum_le_sum
            intro i _
            apply Nat.div_le_div_right
            exact Nat.mul_le_mul_right _ (h_max_size i)
      _ = Finset.univ.sum (fun i => 2 * ((n - c + 1) * (sizes i - 1) / 2)) := by rw [Finset.mul_sum]
      _ ≤ Finset.univ.sum (fun i => (n - c + 1) * (sizes i - 1)) := by
            apply Finset.sum_le_sum
            intro i _
            exact h_two_mul_div _
      _ = (n - c + 1) * Finset.univ.sum (fun i => sizes i - 1) := by rw [Finset.mul_sum]
      _ = (n - c + 1) * (n - c) := by rw [h_sum_sub]
  omega

/-! ## Section 3: Main Results -/

/-- MAIN THEOREM: e + c ≤ n(n-1)/2 + 1 for any graph.
    This is the bound needed for h1_dim_components_bound. -/
theorem edges_plus_components_le [Fintype G.edgeSet] [Fintype G.ConnectedComponent] :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent ≤
    Fintype.card V * (Fintype.card V - 1) / 2 + 1 := by
  classical
  let n := Fintype.card V
  let e := G.edgeFinset.card
  let c := Fintype.card G.ConnectedComponent
  -- Edge bound: e ≤ n(n-1)/2
  have he_le : e ≤ n * (n - 1) / 2 := by
    calc e = G.edgeFinset.card := rfl
      _ ≤ (⊤ : SimpleGraph V).edgeFinset.card := by
          apply Finset.card_le_card
          intro x hx
          simp only [mem_edgeFinset] at hx ⊢
          rw [edgeSet_top, Sym2.diagSet_compl_eq_setOf_not_isDiag, Set.mem_setOf_eq]
          exact G.not_isDiag_of_mem_edgeSet hx
      _ = n * (n - 1) / 2 := by
          rw [card_edgeFinset_top_eq_card_choose_two]
          simp only [Nat.choose_two_right]
          rfl
  -- Case split on n and c
  by_cases hn_zero : n = 0
  · -- n = 0: empty graph
    have hV : Fintype.card V = 0 := hn_zero
    have hV_empty : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    -- e = 0 since no edges possible with no vertices
    have he_zero : e = 0 := by
      have : n * (n - 1) / 2 = 0 := by simp [hn_zero]
      omega
    -- c = 0 since V is empty
    have hc_zero : c = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun cc => hV_empty.false cc.exists_rep.choose⟩
    calc G.edgeFinset.card + Fintype.card G.ConnectedComponent
        = e + c := rfl
      _ = 0 + 0 := by rw [he_zero, hc_zero]
      _ = 0 := by ring
      _ ≤ 1 := Nat.zero_le _
      _ = Fintype.card V * (Fintype.card V - 1) / 2 + 1 := by rw [hV]
  · -- n ≥ 1
    have hne : Nonempty V := by
      by_contra h
      push_neg at h
      have : Fintype.card V = 0 := Fintype.card_eq_zero_iff.mpr ⟨fun v => h.false v⟩
      exact hn_zero this
    have hn_pos : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn_zero
    have hc_le_n : c ≤ n := components_le_vertices G hne
    by_cases hn_small : n = 1
    · -- n = 1: single vertex, e = 0, c = 1
      have he1 : e ≤ 0 := by
        have : n * (n - 1) / 2 = 0 := by simp [hn_small]
        omega
      have he_zero : e = 0 := Nat.eq_zero_of_le_zero he1
      have hc1 : c ≤ 1 := by
        have : c ≤ n := hc_le_n
        omega
      have hgoal : Fintype.card V * (Fintype.card V - 1) / 2 + 1 = 1 := by
        have hV1 : Fintype.card V = 1 := hn_small
        simp only [hV1]
      calc G.edgeFinset.card + Fintype.card G.ConnectedComponent
          = e + c := rfl
        _ = 0 + c := by rw [he_zero]
        _ ≤ 0 + 1 := by omega
        _ = 1 := by ring
        _ = Fintype.card V * (Fintype.card V - 1) / 2 + 1 := hgoal.symm
    · -- n ≥ 2
      have hn : n ≥ 2 := by omega
      by_cases hc_small : c ≤ 1
      · -- c ≤ 1: e + c ≤ n(n-1)/2 + 1 directly
        have h1 : e + c ≤ n * (n - 1) / 2 + 1 := by
          calc e + c ≤ n * (n - 1) / 2 + c := Nat.add_le_add_right he_le c
            _ ≤ n * (n - 1) / 2 + 1 := by omega
        exact h1
      · -- c ≥ 2: use the algebraic bound
        have hc_ge : c ≥ 2 := by omega
        have h_alg := disconnected_algebraic_bound n c hn hc_ge hc_le_n
        -- Need: e ≤ (n-c+1)(n-c)/2
        -- This follows from component edge counting:
        -- - Edges partition by component
        -- - Each component with k vertices has ≤ k(k-1)/2 edges
        -- - Total ≤ Σᵢ kᵢ(kᵢ-1)/2 ≤ (n-c+1)(n-c)/2 by convexity
        calc e + c ≤ (n - c + 1) * (n - c) / 2 + c := by
              -- This is the key step using component infrastructure
              -- Step 1: e = Σ_i (componentEdges G c_i).card
              have h_edge_partition : G.edgeFinset.card = Finset.univ.sum (fun c => (componentEdges G c).card) := by
                rw [edgeFinset_eq_biUnion_componentEdges G]
                rw [Finset.card_biUnion (pairwise_disjoint_componentEdges G)]
              -- Step 2: Each (componentEdges G c_i).card ≤ k_i(k_i-1)/2
              have h_comp_bound : Finset.univ.sum (fun cc => (componentEdges G cc).card) ≤
                                  Finset.univ.sum (fun cc => componentVertexCount G cc * (componentVertexCount G cc - 1) / 2) := by
                apply Finset.sum_le_sum
                intro i _
                exact componentEdges_card_le G i
              -- Step 3: Use convexity bound
              -- Need to relate Fintype.card G.ConnectedComponent to c
              have hc_eq : Fintype.card G.ConnectedComponent = c := rfl
              -- Apply convexity bound with componentVertexCount as sizes
              have h_convex : Finset.univ.sum (fun cc : G.ConnectedComponent =>
                                componentVertexCount G cc * (componentVertexCount G cc - 1) / 2) ≤
                              (n - c + 1) * (n - c) / 2 := by
                -- We use sum_edges_le_concentrated with sizes = componentVertexCount G
                -- Need Fin c → ℕ, but we have G.ConnectedComponent → ℕ
                -- Since |G.ConnectedComponent| = c, use equivFin
                let equiv := (Fintype.equivFin G.ConnectedComponent)
                let sizes : Fin c → ℕ := fun i => componentVertexCount G (equiv.symm i)
                have h_sum : Finset.univ.sum sizes = n := by
                  simp only [sizes, n]
                  have h := sum_componentVertexCount_eq_card G
                  rw [← h]
                  exact Fintype.sum_equiv equiv.symm _ _ (fun _ => rfl)
                have h_pos : ∀ i, 1 ≤ sizes i := by
                  intro i
                  exact componentVertexCount_pos G _
                have h_bound := sum_edges_le_concentrated hc_ge hc_le_n sizes h_sum h_pos
                calc Finset.univ.sum (fun cc : G.ConnectedComponent =>
                       componentVertexCount G cc * (componentVertexCount G cc - 1) / 2)
                    = Finset.univ.sum (fun i : Fin c =>
                        componentVertexCount G (equiv.symm i) * (componentVertexCount G (equiv.symm i) - 1) / 2) := by
                        symm
                        apply Finset.sum_equiv equiv.symm
                        · intro i; simp
                        · intro i _; rfl
                  _ = Finset.univ.sum (fun i => sizes i * (sizes i - 1) / 2) := rfl
                  _ ≤ (n - c + 1) * (n - c) / 2 := h_bound
              -- Combine everything
              have h_e_le : e ≤ (n - c + 1) * (n - c) / 2 := by
                calc e = G.edgeFinset.card := rfl
                  _ = Finset.univ.sum (fun cc => (componentEdges G cc).card) := h_edge_partition
                  _ ≤ Finset.univ.sum (fun cc => componentVertexCount G cc * (componentVertexCount G cc - 1) / 2) := h_comp_bound
                  _ ≤ (n - c + 1) * (n - c) / 2 := h_convex
              linarith
          _ ≤ n * (n - 1) / 2 + 1 := h_alg

/-- The disconnected graph edge-component bound.
    For any disconnected graph: e + c ≤ n(n-1)/2 + 1 -/
theorem disconnected_edge_component_bound [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    (h_disconn : ¬G.Connected)
    (h_edge : G.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) / 2) :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent ≤
    Fintype.card V * (Fintype.card V - 1) / 2 + 1 :=
  edges_plus_components_le G

end Infrastructure.ComponentEdgeCounting
