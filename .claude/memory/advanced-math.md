# Advanced Math Reference for Level 5/6 Proofs

Load this for deep proof work. Keep under 200 lines.

---

## 1. Proof Sketches

### δ² = 0 (The Masterpiece Pattern)
**Goal**: Show δ(δ(f)) = 0 for all cochains f

**Mathematical insight**: Double sum pairs terms with opposite signs.
For positions (a, b) with a < b:
- Remove a first, then b-1: sign = (-1)^a × (-1)^(b-1) = (-1)^(a+b-1)
- Remove b first, then a: sign = (-1)^b × (-1)^a = (-1)^(a+b)
These cancel since (-1)^(a+b-1) = -(-1)^(a+b)

**Proof architecture**:
1. `sign_cancel`: a < b → sign(a) × sign(b-1) + sign(b) × sign(a) = 0
2. `face_face_identity`: i < j → (s.face i).face (j-1) = (s.face j).face i
3. `double_sum_cancellation`: ∑ᵢ ∑ⱼ sign(i)×sign(j)×f(∂ⱼ∂ᵢs) = 0 via involution
4. Main theorem: unfold, rewrite, apply cancellation

### H¹ = 0 ⟺ Forest
**Goal**: First cohomology trivial iff 1-skeleton is acyclic

**Mathematical insight**: In a forest, any 1-cocycle f extends uniquely along paths.
- Cocycle condition: δf = 0 means f is "locally consistent"
- Forest property: unique path between any two connected vertices
- Construction: given 0-cochain g₀ at root, extend via g(v) = g₀ + ∑(path) f(edges)
- Uniqueness: no cycles means no obstruction to global extension

### Value Alignment Bounds
**Goal**: Show |vᵢ(s) - vⱼ(s)| ≤ 2ε for aligned systems

**Strategy**: Triangle inequality chains
- |vᵢ - vⱼ| ≤ |vᵢ - vₖ| + |vₖ - vⱼ| ≤ 2ε when k is mediator
- Use `abs_sub_le` from Mathlib for rational arithmetic

---

## 2. Domain Theory

### Type Hierarchy
```
Vertex := ℕ                           -- Agent/node index
Simplex := Finset Vertex              -- Finite vertex set (dim = card - 1)
SimplicialComplex := {
  simplices : Set Simplex,
  down_closed,                        -- Faces included
  has_vertices                        -- Non-empty
}
Cochain K k := {s ∈ K.ksimplices k} → ℚ   -- ℚ-valued on k-simplices
```

### Core Operators
```
δ : Cochain K k → Cochain K (k+1)     -- Coboundary (alternating face sum)
IsCocycle K k f := δ(f) = 0           -- Kernel of δ (closed forms)
IsCoboundary K k f := ∃ g, δ(g) = f   -- Image of δ (exact forms)
H1Trivial K := ∀ f, IsCocycle → IsCoboundary   -- H¹(K) = 0
OneConnected K := (oneSkeleton K).IsAcyclic    -- Forest property
```

### Main Theorem Chain
```
δ² = 0                     [Coboundary.lean]
    ↓
Coboundary ⊆ Cocycle       [Cohomology.lean: coboundary_is_cocycle]
    ↓
H¹(K) = 0 ⟺ OneConnected   [Characterization.lean]
    ↓
Applications: alignment, reconciliation, fairness
```

### Critical Limitation: Multi-Cycle
Several axioms are **mathematically false** for multi-cycle complexes:
- `remove_edge_from_single_cycle_aux'` - one edge doesn't kill all cycles
- `fill_triangle_h1_trivial_aux'` - one triangle doesn't affect independent cycles
- Requires `dim H¹(K) = 1` restriction or accept as limitation

---

## 3. Proof Strategies

### Involution Pairing
**When**: Sum equals zero via sign-reversing pairs
**How**: `Finset.sum_involution` with involution τ
**Obligations**:
1. τ(p) + p = 0 (paired terms cancel)
2. τ(p) ≠ p (no fixed points)
3. τ(τ(p)) = p (involution property)
4. τ(p) ∈ domain

### Minimum-Depth Cycle Argument
**When**: Need contradiction from cycle existence
**How**:
1. Find min-depth vertex via `Finset.min'`
2. Rotate cycle to start there with `IsCycle.rotate`
3. Extract neighbors at positions 1 and length-1 via `getVert`
4. Use `takeUntil` to construct inner walks
5. Apply `endpoint_notMem_support_takeUntil` for contradiction

### Dependent Type Handling
**When**: Sums over types with uniform cardinality
**How**: `finCongr` creates equivalence, `sum_equiv` reindexes
```lean
refine Finset.sum_equiv (finCongr h_card) ?_ ?_
· intro j; simp only [Finset.mem_univ]
· intro j _; simp only [finCongr_apply, Fin.val_cast]
```

### Simplicial Membership Proofs
**When**: Show face ∈ K.ksimplices k
**How**: Two-part goal (membership + cardinality)
```lean
constructor
· exact K.down_closed s hs_mem (face_index)  -- recursive
· rw [face_card]; omega                       -- arithmetic
```

### List Index Gymnastics
**When**: Manipulating sorted simplex lists
**How**: `split_ifs` on index relationships, `omega` for arithmetic
```lean
simp [List.getElem_eraseIdx]
split_ifs with h <;> omega
```

---

## 4. Mathlib Reference

### BigOperators (Summation)
| Lemma | Use |
|-------|-----|
| `Finset.sum_involution` | Sign-reversing cancellation (δ²=0) |
| `Finset.sum_equiv` | Reindex via bijection |
| `Finset.sum_product'` | Nested sums to products |
| `Finset.mul_sum` | Distribute multiplication |

### Finset/List Operations
| Lemma | Use |
|-------|-----|
| `Finset.sort` | Convert to sorted list |
| `Finset.length_sort` | Length = card |
| `List.eraseIdx` | Remove by index |
| `List.getElem_eraseIdx` | Access after erase |
| `Finset.card_erase_of_mem` | Card decreases by 1 |

### Graph Theory (SimpleGraph)
| Lemma | Use |
|-------|-----|
| `SimpleGraph.IsAcyclic` | No cycles definition |
| `Walk.transfer H hp` | Transfer walk to subgraph |
| `IsCycle.rotate c hm` | Rotate cycle to vertex |
| `Walk.takeUntil w hw` | Prefix to reachable vertex |
| `Reachable.mono hle h` | Monotonicity over inclusion |

### Arithmetic Tactics
| Tactic | Use |
|--------|-----|
| `omega` | Nat/Int linear arithmetic |
| `ring` | Commutative ring normalization |
| `field_simp` | Clear denominators |
| `abs_sub_le` | Triangle inequality for bounds |

### Type Operations
| Lemma | Use |
|-------|-----|
| `Fin.ext_iff` | Fin extensionality |
| `finCongr` | Equivalence from card equality |
| `Fintype.card_congr` | Card equality via bijection |

---

## 5. Known Blockers

### Cannot Eliminate (External Theory)
- Persistent homology stability (Cohen-Steiner theorems)
- Spectral graph theory (eigenvalues, Laplacian)
- H² infrastructure (tetrahedron homology)

### Current Sorries (12 total)
- `TreeAuthCoreProofs` (3) - tree authority
- `CompleteComplexH1` (2) - complete graph cohomology
- `TreeAuthorityAcyclicity` (3) - acyclicity proofs
- `TreeAuthDepthTheory` (2) - depth reasoning
- `SimplicialGraphBridge` (1) - bridge construction
- `TreeAuthorityH1` (1) - H¹ for trees

### Build Gotchas
- Walk induction broken for Sum endpoints → use pattern matching
- `subst x` replaces all occurrences → prefer `rw` or `subst_vars`
- Fintype instance mismatches → normalize via `Fintype.card_eq_nat_card`
