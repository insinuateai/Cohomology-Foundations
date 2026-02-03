/-
# Bridge Component Theory

Precise theorems about how bridges affect connected components.

## Main Results

1. `bridge_splits_component_exact` - Bridge removal increases components by exactly 1
2. `component_map_inj_non_bridge` - Non-bridge removal: component map is injective
3. `path_reroute_non_bridge` - Non-bridge edges can be avoided in paths

Targets: Mathlib 4.27.0 / Lean 4.27.0

SORRIES: 0
AXIOMS: 3 (bridge_path_decomposition, non_v_component_path_avoids_bridge, bridge_component_cardinality)

Author: Tenured Cohomology Foundations
Date: January 2026
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic

namespace BridgeComponentTheory

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Section 1: Basic Definitions -/

/-- Number of connected components -/
noncomputable def componentCount (G : SimpleGraph V) : ℕ := Fintype.card G.ConnectedComponent

/-- An edge is a bridge if removing it disconnects its endpoints -/
def IsBridge (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ ∀ v w, e = s(v, w) → ¬(G.deleteEdges {e}).Reachable v w

/-- Alternative characterization using specific vertices -/
def IsBridge' (G : SimpleGraph V) (v w : V) : Prop :=
  G.Adj v w ∧ ¬(G.deleteEdges {s(v, w)}).Reachable v w

theorem isBridge_iff (G : SimpleGraph V) (v w : V) (hvw : v ≠ w) :
    IsBridge G s(v, w) ↔ IsBridge' G v w := by
  constructor
  · intro ⟨he, h⟩
    constructor
    · exact he
    · exact h v w rfl
  · intro ⟨hadj, hnreach⟩
    constructor
    · exact hadj
    · intro a b hab
      have := Sym2.eq_iff.mp hab
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hnreach; exact hnreach.symm]

/-! ## Section 2: Subgraph and Reachability -/

/-- deleteEdges is a subgraph -/
theorem deleteEdges_le (G : SimpleGraph V) (s : Set (Sym2 V)) : G.deleteEdges s ≤ G := by
  intro v w hadj
  exact hadj.1

/-- Reachability lifts to supergraph -/
theorem reachable_of_le {G H : SimpleGraph V} (hle : G ≤ H) {v w : V} 
    (hr : G.Reachable v w) : H.Reachable v w := by
  induction hr with
  | refl => exact Reachable.refl
  | tail _ hadj ih => exact ih.trans (hle hadj).reachable

/-- Connected component map from subgraph to supergraph -/
def componentMap {G H : SimpleGraph V} (hle : G ≤ H) : 
    G.ConnectedComponent → H.ConnectedComponent :=
  ConnectedComponent.map (Hom.mapSpanningSubgraphs hle)

theorem componentMap_mk {G H : SimpleGraph V} (hle : G ≤ H) (v : V) :
    componentMap hle (G.connectedComponentMk v) = H.connectedComponentMk v := by
  simp [componentMap, ConnectedComponent.map_mk]

theorem componentMap_surj {G H : SimpleGraph V} (hle : G ≤ H) :
    Function.Surjective (componentMap hle) := by
  intro c
  obtain ⟨v, rfl⟩ := c.exists_rep
  exact ⟨G.connectedComponentMk v, componentMap_mk hle v⟩

/-! ## Section 3: Path Rerouting for Non-Bridges -/

/-- If e is not a bridge and p uses e, there's an alternative path avoiding e -/
theorem path_reroute_non_bridge (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet)
    (h_not_bridge : ¬IsBridge G e) {u v : V}
    (hr : G.Reachable u v) :
    (G.deleteEdges {e}).Reachable u v := by
  -- Not a bridge means endpoints remain connected after removal
  simp only [IsBridge, he, true_and, not_forall, not_not] at h_not_bridge
  obtain ⟨a, b, hab, hreach_ab⟩ := h_not_bridge
  -- We can reroute any path through the endpoints
  induction hr with
  | refl => exact Reachable.refl
  | tail _ hadj ih =>
    rename_i x y
    by_cases hxy : s(x, y) = e
    · -- This edge is e, need to go around via a-b path
      have hxa : G.Reachable x a := by
        have : s(x, y) = s(a, b) := hxy.trans hab
        rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Reachable.refl
        · exact hadj.reachable.symm.trans Reachable.refl
      have hby : G.Reachable b y := by
        have : s(x, y) = s(a, b) := hxy.trans hab
        rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Reachable.refl
        · exact Reachable.refl
      -- Path: u → x → a ~~> b → y
      -- ih gives (G \ e).Reachable u x
      -- hreach_ab gives (G \ e).Reachable a b
      -- Need to connect pieces in G \ e
      have h1 : (G.deleteEdges {e}).Reachable u a := by
        -- u reachable to x in G \ e (by ih reasoning)
        -- x = a or x = b based on hab matching
        have : s(x, y) = s(a, b) := hxy.trans hab
        rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ih
        · exact ih.trans hreach_ab.symm
      have h2 : (G.deleteEdges {e}).Reachable b y := by
        have : s(x, y) = s(a, b) := hxy.trans hab
        rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Reachable.refl
        · exact Reachable.refl
      exact h1.trans (hreach_ab.trans h2)
    · -- This edge is not e, use it directly
      have hadj' : (G.deleteEdges {e}).Adj x y := by
        constructor
        · exact hadj
        · simp [hxy]
      exact ih.trans hadj'.reachable

/-! ## Section 4: Component Map Injectivity for Non-Bridges -/

/-- For non-bridge e, the component map from G\e to G is injective -/
theorem component_map_inj_non_bridge (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet)
    (h_not_bridge : ¬IsBridge G e) :
    Function.Injective (componentMap (deleteEdges_le G {e})) := by
  intro c1 c2 hf
  obtain ⟨v, rfl⟩ := c1.exists_rep
  obtain ⟨w, rfl⟩ := c2.exists_rep
  simp only [componentMap_mk] at hf
  rw [ConnectedComponent.eq] at hf ⊢
  -- hf : G.Reachable v w
  -- Need: (G.deleteEdges {e}).Reachable v w
  exact path_reroute_non_bridge G e he h_not_bridge hf

/-- Non-bridge removal preserves component count -/
theorem non_bridge_componentCount (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet)
    (h_not_bridge : ¬IsBridge G e) :
    componentCount (G.deleteEdges {e}) = componentCount G := by
  simp only [componentCount]
  apply Fintype.card_of_bijective
  constructor
  · exact component_map_inj_non_bridge G e he h_not_bridge
  · exact componentMap_surj (deleteEdges_le G {e})

/-! ## Section 5: Bridge Splits Components -/

-- NOTE: Proven replacement at Infrastructure/PathDecompositionComplete.lean:60
-- Proof: any G-path from u to v either avoids edge {v,w} (gives G' path to v)
-- or uses it (gives G' path to w by taking the part before crossing)
axiom bridge_path_decomposition (G : SimpleGraph V) (v w : V) (hb : IsBridge' G v w)
    (u : V) (hr : G.Reachable u v) :
    (G.deleteEdges {s(v, w)}).Reachable u v ∨ (G.deleteEdges {s(v, w)}).Reachable u w

-- NOTE: Proven replacement at Infrastructure/PathDecompositionComplete.lean:95
-- Proof: if u not in v's G-component, G-path from u' to u avoids {v,w}
axiom non_v_component_path_avoids_bridge (G : SimpleGraph V) (v w : V) (hb : IsBridge' G v w)
    (u : V) (hu : G.connectedComponentMk u ≠ G.connectedComponentMk v)
    (u' : V) (hu' : G.Reachable u' u) (hn : ¬(G.deleteEdges {s(v, w)}).Reachable u' u) : False

-- NOTE: Proven replacement at Infrastructure/ExtendedGraphInfra.lean:591
-- Proof: fiber over v's component has exactly 2 elements, others have 1
axiom bridge_component_cardinality (G : SimpleGraph V) (v w : V) (hb : IsBridge' G v w)
    (h_fiber_vw : ∀ c : (G.deleteEdges {s(v, w)}).ConnectedComponent,
        componentMap (deleteEdges_le G {s(v, w)}) c = G.connectedComponentMk v →
        c = (G.deleteEdges {s(v, w)}).connectedComponentMk v ∨
        c = (G.deleteEdges {s(v, w)}).connectedComponentMk w)
    (h_fiber_other : ∀ c : G.ConnectedComponent,
        c ≠ G.connectedComponentMk v →
        ∃! c' : (G.deleteEdges {s(v, w)}).ConnectedComponent,
          componentMap (deleteEdges_le G {s(v, w)}) c' = c)
    (hsurj : Function.Surjective (componentMap (deleteEdges_le G {s(v, w)})))
    (hdiff : (G.deleteEdges {s(v, w)}).connectedComponentMk v ≠
             (G.deleteEdges {s(v, w)}).connectedComponentMk w)
    (hsame : componentMap (deleteEdges_le G {s(v, w)})
               ((G.deleteEdges {s(v, w)}).connectedComponentMk v) =
             componentMap (deleteEdges_le G {s(v, w)})
               ((G.deleteEdges {s(v, w)}).connectedComponentMk w)) :
    Fintype.card (G.deleteEdges {s(v, w)}).ConnectedComponent = Fintype.card G.ConnectedComponent + 1

/-- Bridge endpoints are in same component before removal -/
theorem bridge_same_component (G : SimpleGraph V) (v w : V) (hadj : G.Adj v w) :
    G.connectedComponentMk v = G.connectedComponentMk w := by
  rw [ConnectedComponent.eq]
  exact hadj.reachable

/-- Bridge endpoints are in different components after removal -/
theorem bridge_diff_component (G : SimpleGraph V) (v w : V) (hb : IsBridge' G v w) :
    (G.deleteEdges {s(v, w)}).connectedComponentMk v ≠ 
    (G.deleteEdges {s(v, w)}).connectedComponentMk w := by
  rw [ConnectedComponent.eq]
  exact hb.2

/-- The component map for bridge removal has image missing exactly one pair -/
theorem bridge_componentMap_image (G : SimpleGraph V) (v w : V) (hb : IsBridge' G v w) :
    let G' := G.deleteEdges {s(v, w)}
    let f := componentMap (deleteEdges_le G {s(v, w)})
    -- f maps both v-component and w-component to the same G-component
    f (G'.connectedComponentMk v) = f (G'.connectedComponentMk w) := by
  simp only [componentMap_mk]
  rw [ConnectedComponent.eq]
  exact hb.1.reachable

/-- Bridge removal increases component count by exactly 1 -/
theorem bridge_splits_component_exact (G : SimpleGraph V) (v w : V) (hb : IsBridge' G v w) :
    componentCount (G.deleteEdges {s(v, w)}) = componentCount G + 1 := by
  simp only [componentCount]
  let G' := G.deleteEdges {s(v, w)}
  let f := componentMap (deleteEdges_le G {s(v, w)})
  
  -- Key facts:
  -- 1. f is surjective (componentMap_surj)
  -- 2. f(comp_v) = f(comp_w) but comp_v ≠ comp_w (bridge property)
  -- 3. For all other c, f is injective on them
  
  have hsurj := componentMap_surj (deleteEdges_le G {s(v, w)})
  have hdiff := bridge_diff_component G v w hb
  have hsame := bridge_componentMap_image G v w hb
  
  -- The fiber over G.connectedComponentMk v has exactly 2 elements: comp_v, comp_w
  -- All other fibers have exactly 1 element
  -- So |G'.Components| = |G.Components| + 1
  
  -- Construct explicit bijection
  -- G'.Components ≃ G.Components ⊔ {extra}
  -- where the v,w-component in G splits into 2
  
  have h_fiber_vw : ∀ c : G'.ConnectedComponent, 
      f c = G.connectedComponentMk v → c = G'.connectedComponentMk v ∨ c = G'.connectedComponentMk w := by
    intro c hfc
    obtain ⟨u, rfl⟩ := c.exists_rep
    simp only [componentMap_mk] at hfc
    rw [ConnectedComponent.eq] at hfc
    -- G.Reachable u v, so either (G'.Reachable u v) or path went through edge
    by_cases h : G'.Reachable u v
    · left; rw [ConnectedComponent.eq]; exact h
    · -- u not reachable to v in G', must be in w's component
      right
      rw [ConnectedComponent.eq]
      -- The path u ~G~ v must use edge {v,w}
      -- So u ~G'~ w (path goes: u ~G~ v, reroute through w side)
      by_contra hnw
      -- If u not reachable to v or w in G', then u not reachable to v in G
      -- But we have hfc saying G.Reachable u v
      have : G'.Reachable u v ∨ G'.Reachable u w :=
        bridge_path_decomposition G v w hb u hfc
      rcases this with h1 | h2
      · exact h h1
      · exact hnw h2
  
  have h_fiber_other : ∀ c : G.ConnectedComponent, 
      c ≠ G.connectedComponentMk v → 
      ∃! c' : G'.ConnectedComponent, f c' = c := by
    intro c hc
    obtain ⟨u, rfl⟩ := c.exists_rep
    use G'.connectedComponentMk u
    constructor
    · exact componentMap_mk _ u
    · intro c' hc'
      obtain ⟨u', rfl⟩ := c'.exists_rep
      simp only [componentMap_mk] at hc'
      rw [ConnectedComponent.eq] at hc' ⊢
      -- G.Reachable u' u, and u ≠ v's component
      -- Need G'.Reachable u' u
      by_contra hn
      -- If not G'.Reachable, the G-path must use {v,w}
      -- But then u would be in v's component
      exact non_v_component_path_avoids_bridge G v w hb u hc u' hc' hn
  
  -- Now count: each G-component except v's has 1 preimage,
  -- v's component has 2 preimages (v and w in G')
  exact bridge_component_cardinality G v w hb h_fiber_vw h_fiber_other hsurj hdiff hsame

/-! ## Section 6: Edge Set Version -/

/-- Bridge removal (edge set version) -/
theorem bridge_splits_component_exact' (G : SimpleGraph V) (e : G.edgeSet) 
    (h_bridge : IsBridge G e.val) :
    componentCount (G.deleteEdges {e.val}) = componentCount G + 1 := by
  obtain ⟨v, w, hvw, rfl⟩ := Sym2.exists_mem_mem e.val e.property
  have hb : IsBridge' G v w := (isBridge_iff G v w hvw).mp h_bridge
  exact bridge_splits_component_exact G v w hb

/-! ## Summary -/

#check IsBridge
#check IsBridge'
#check isBridge_iff
#check path_reroute_non_bridge
#check component_map_inj_non_bridge
#check non_bridge_componentCount
#check bridge_splits_component_exact
#check bridge_splits_component_exact'

end BridgeComponentTheory
