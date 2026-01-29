# CLAUDE.md - COBOUND Project Context

> **Last Updated**: January 2026  
> **Project**: Cohomology-Foundations (COBOUND)  
> **Status**: Active Development - Phase 4 Preparation  
> **Quality Score**: 82/100 → Target 95+

---

## 🎯 Mission Statement

COBOUND is the world's first formal verification of fundamental limits in AI alignment theory. We prove mathematically that:

- **H¹ = 0** → Alignment is possible (all value conflicts can be globally reconciled)
- **H¹ ≠ 0** → Alignment is mathematically impossible (local consistency, global impossibility)

This is not a library. This is **proven theorems that happen to also be products**.

---

## 🧮 Core Mathematical Framework

### The Fundamental Insight

AI alignment reduces to topology:

```
Multi-Agent Coordination ←→ Čech Cohomology
         ↓                        ↓
   Can agents align?    ←→    Is H¹ = 0?
         ↓                        ↓
   Forest network       ←→    No cycles
   (alignment works)          (no obstruction)
```

### Key Theorems (Crown Jewels)

| Theorem | Status | Location | Importance |
|---------|--------|----------|------------|
| δ² = 0 | ✅ PROVEN | Foundations/Coboundary.lean | Foundation of cohomology |
| H¹ = 0 ↔ Forest | ✅ PROVEN | H1Characterization/ | Core characterization |
| No Universal Alignment | ✅ PROVEN | Perspective/AlignmentTheorem.lean | Impossibility result |
| 2-Agent Alignment | ✅ PROVEN | Perspective/AlignmentEquivalence.lean | Positive result |
| 3+ Agent Obstruction | ✅ PROVEN | MultiAgent/AgentNetworks.lean | Cycle detection |

### Mathematical Definitions

```lean
-- Simplicial Complex: vertices with faces
structure SimplicialComplex where
  vertices : Type*
  faces : Set (Finset vertices)
  down_closed : ∀ s ∈ faces, ∀ t ⊆ s, t ∈ faces

-- k-Cochain: function from k-simplices to ℚ
def Cochain (K : SimplicialComplex) (k : ℕ) := 
  { s : Finset K.vertices // s ∈ K.faces ∧ s.card = k + 1 } → ℚ

-- Coboundary operator δ
def coboundary (K : SimplicialComplex) (k : ℕ) (f : Cochain K k) : Cochain K (k + 1) :=
  fun s => ∑ i : Fin (k + 2), (-1)^i.val * f (s.face i)

-- H¹ Triviality: every 1-cocycle is a 1-coboundary
def H1Trivial (K : SimplicialComplex) : Prop :=
  ∀ f : Cochain K 1, IsCocycle K 1 f → IsCoboundary K 1 f
```

---

## 📁 Codebase Structure

```
Cohomology-Foundations/
├── Foundations/           # 🏆 GOLD - Core mathematics (0 sorries, 0 axioms)
│   ├── Basic.lean         # Basic definitions
│   ├── Simplex.lean       # Simplicial complex
│   ├── Cochain.lean       # Cochain groups
│   ├── Coboundary.lean    # δ operator, δ² = 0
│   └── Cohomology.lean    # H⁰, H¹ definitions
│
├── H1Characterization/    # Core H¹ = 0 characterization
│   ├── Characterization.lean
│   ├── OneConnected.lean
│   ├── ForestCoboundary.lean
│   ├── PathIntegral.lean
│   ├── CycleCochain/
│   │   ├── Definitions.lean
│   │   └── Proofs.lean
│   └── LinearComplexity.lean
│
├── Perspective/           # Application theorems (fairness, alignment)
│   ├── AlignmentTheorem.lean
│   ├── AlignmentEquivalence.lean
│   ├── FairnessFoundations.lean
│   ├── SpectralGap.lean
│   ├── DimensionBound.lean
│   └── ... (40+ files)
│
├── MultiAgent/            # Multi-agent coordination
│   ├── AgentNetworks.lean
│   ├── CoordinationTopology.lean
│   ├── ConsensusObstruction.lean
│   ├── MemoryConsistency.lean
│   ├── GameTheoreticH1.lean
│   └── ... (15+ files)
│
├── lakefile.lean          # Build configuration
└── lake-manifest.json     # Dependencies (Mathlib 4.26.0)
```

---

## 📊 Current Quality Metrics

| Module | Files | Lines | Theorems | Axioms | Sorries | Grade |
|--------|-------|-------|----------|--------|---------|-------|
| Foundations | 6 | 1,107 | 21 | 0 | 0 | 🏆 GOLD |
| H1Characterization | 10 | 2,224 | 50 | 4 | 0 | ⭐ SILVER |
| Perspective | 49 | 20,281 | 442 | 100 | 0 | 🔶 BRONZE |
| MultiAgent | 17 | 5,956 | 489 | 48 | 12 | ⚠️ NEEDS WORK |
| **TOTAL** | **85** | **31,288** | **1,099** | **106** | **12** | **82/100** |

### Remaining Issues

**12 Sorries** (must fix before Phase 4):
- GameTheoreticH1.lean: 4 sorries
- MechanismDesign.lean: 2 sorries
- GlobalLocalDuality.lean: 2 sorries
- StrategicCoordination.lean: 1 sorry
- CoalitionCohomology.lean: 1 sorry
- PerspectiveSheaf.lean: 1 sorry

**106 Axioms** (reduce to ≤50):
- ~14 Legitimate (spectral theory, category theory)
- ~50 Bridge axioms (H1 ↔ property - should be theorems)
- ~20 Provable (can be converted to theorems)
- ~20+ Unused (DELETE immediately)

---

## ⚖️ Quality Standards

### Theorem Tiers

| Tier | Sorry Allowed | Axiom Allowed | Use For |
|------|---------------|---------------|---------|
| **Crown Jewel** | 0 | 0 | Core theorems (δ²=0, H¹ char) |
| **Core Lemma** | 0 | 0 | Supporting lemmas |
| **Application** | 1 (fix same session) | 0 | Domain applications |
| **Example** | 2 (fix within 24h) | 1 if justified | Demonstrations |

### Quality Gates

Before ANY commit:
```bash
# Must pass ALL gates
lake build                           # 0 errors
grep -rn "sorry" --include="*.lean" Foundations/    # Must be empty
grep -rn "sorry" --include="*.lean" H1Characterization/  # Should be empty
```

Before Phase 4:
- [ ] Total sorries ≤ 0
- [ ] Total axioms ≤ 50
- [ ] Build: 0 errors
- [ ] Quality score ≥ 95

---

## 🚫 What NOT To Do

### Never Do These:

1. **Never add sorry to Foundations/**
   - This is the mathematical foundation
   - ANY sorry here invalidates downstream proofs

2. **Never add axioms without justification**
   ```lean
   -- ❌ BAD
   axiom h1_implies_consensus : H1Trivial K → ConsensusExists K
   
   -- ✅ GOOD (prove it or document why axiom)
   /-- We axiomatize this because [reason].
       Reference: [citation] -/
   axiom spectral_gap_bound : ...
   ```

3. **Never use these tactics carelessly**
   ```lean
   -- ❌ DANGEROUS (hides incomplete proofs)
   sorry
   native_decide  -- Can timeout or fail silently
   assumption     -- May grab wrong hypothesis
   trivial        -- May not actually be trivial
   
   -- ✅ PREFERRED
   exact specific_lemma h1 h2
   simp only [lemma1, lemma2]
   omega  -- For natural number arithmetic
   ring   -- For ring arithmetic
   ```

4. **Never create circular dependencies**
   ```
   ❌ Foundations imports MultiAgent
   ❌ H1Characterization imports Perspective
   
   ✅ Dependency order: Foundations → H1Char → Perspective → MultiAgent
   ```

5. **Never exceed 3 axioms per file**
   - If a file has >3 axioms, refactor
   - Prove what can be proven
   - Document what cannot

---

## ✅ Preferred Patterns

### Proof Patterns

```lean
-- Sign arithmetic
unfold sign
split_ifs with h1 h2 h3 <;> try (exfalso; omega)
· ring

-- Finset membership
simp only [Finset.mem_filter, Finset.mem_univ, true_and]

-- List indexing after erase
simp only [List.get_eq_getElem]
rw [List.getElem_eraseIdx]
split_ifs with h <;> omega

-- Function extensionality on cochains
funext ⟨s, hs⟩
simp only [Cochain.zero_apply, coboundary]

-- Sum cancellation (key for δ² = 0)
apply Finset.sum_involution (g := pairing_function)
· intro p _; split_ifs <;> ring  -- Cancellation
· intro p _ _; simp; omega       -- Non-fixed
· intro p _; simp; omega         -- Involution
· intro p _; exact Finset.mem_product.mpr ⟨...⟩  -- Closure
```

### Documentation Pattern

```lean
/-- Brief description of what this proves.

    ## Mathematical Meaning
    Explain the geometric/topological intuition.
    
    ## Proof Strategy  
    1. First we show X
    2. Then we derive Y
    3. Finally we conclude Z
    
    ## Dependencies
    - `lemma_a` : Used for step 1
    - `lemma_b` : Used for step 2
-/
theorem important_theorem : Statement := by
  -- Step 1: Show X
  have hX : X := lemma_a
  -- Step 2: Derive Y
  have hY : Y := lemma_b hX
  -- Step 3: Conclude
  exact conclusion hY
```

---

## 🔧 Development Workflow

### For Fixing Sorries

1. **Locate**: `grep -rn "sorry" --include="*.lean" <module>/`
2. **Understand**: Read surrounding context, identify goal
3. **Strategize**: What lemmas/tactics will work?
4. **Implement**: Write proof
5. **Verify**: `lake build <Module>.<File>`
6. **Check**: `grep -n "sorry" <file>` returns empty

### For Reducing Axioms

1. **Find unused**: Check if axiom is actually referenced
2. **Classify**: Provable / External Math / Foundational / Unused
3. **Act**:
   - Unused → DELETE
   - Provable → Convert to theorem
   - External → Document with reference
   - Foundational → Keep with justification
4. **Verify**: Build passes, functionality preserved

### For Adding New Theorems

1. **Classify tier**: Crown Jewel / Core / Application / Example
2. **Check dependencies**: What existing lemmas can you use?
3. **Write with quality gate**:
   - Crown Jewel: MUST compile with 0 sorry, 0 axiom
   - Core: MUST compile with 0 sorry
   - Application: Fix any sorry before moving to next file
4. **Document**: Add docstring explaining meaning
5. **Verify**: `lake build`, grep for sorries

---

## 📚 Key Mathlib Lemmas

### Finset
```lean
Finset.sum_involution       -- Key for δ² = 0
Finset.sum_product'         -- Convert ∑ᵢ ∑ⱼ to ∑ (i,j)
Finset.card_erase_of_mem    -- |s \ {x}| = |s| - 1
Finset.length_sort          -- (s.sort f).length = s.card
```

### List
```lean
List.get_eq_getElem         -- Convert notations
List.getElem_eraseIdx       -- Access after erase
List.ext_getElem            -- List equality
```

### Tactics
```lean
omega       -- Natural number arithmetic
ring        -- Ring/field arithmetic
simp only   -- Controlled simplification
exact       -- Provide exact term
apply       -- Apply hypothesis
constructor -- Build conjunction/exists
rcases      -- Destruct hypothesis
calc        -- Chain of equalities
```

---

## 🎯 Current Objectives

### Immediate (Before Phase 4)

1. **Fix 12 sorries** → 0 sorries
   - Priority: GameTheoreticH1 (4), MechanismDesign (2), GlobalLocalDuality (2)
   - Then: Easy ones (Strategic, Coalition, Sheaf)

2. **Reduce 106 axioms** → ≤50 axioms
   - Delete unused axioms
   - Prove provable axioms (CycleCochain, OptimalRepair, DimensionBound)
   - Document remaining axioms

3. **Achieve quality score 95+**

### Phase 4 (After Cleanup)

- Information Cohomology foundations
- Perspective Geometry core theorems
- Computational Cohomology complexity theory
- Multi-Agent integration theorems

---

## 🏗️ Architecture Principles

### Module Independence
Each module should be:
- **Self-contained**: Minimal imports from other modules
- **Well-defined interface**: Clear exports
- **Testable**: Can build independently

### Proof Robustness
Proofs should be:
- **Explicit**: Prefer `exact` over `assumption`
- **Documented**: Explain strategy in comments
- **Maintainable**: Use named lemmas, not inline proofs

### Mathematical Integrity
The codebase must:
- **Never assert what can be proven**: Axioms are last resort
- **Never hide incompleteness**: Sorries must be tracked and fixed
- **Always preserve soundness**: Foundations must remain solid

---

## 📞 Quick Reference

### Build Commands
```bash
lake build                    # Full build
lake build Foundations        # Module only
lake build MultiAgent.GameTheoreticH1  # Single file
```

### Quality Check Commands
```bash
# Sorry count
grep -rn "sorry" --include="*.lean" . | grep -v ".lake" | wc -l

# Axiom count
grep -rn "^axiom" --include="*.lean" . | grep -v ".lake" | wc -l

# Theorem count
grep -rn "^theorem\|^lemma" --include="*.lean" . | grep -v ".lake" | wc -l

# File quality
for f in $(find . -name "*.lean" | grep -v ".lake"); do
  s=$(grep -c "sorry" "$f" 2>/dev/null || echo 0)
  a=$(grep -c "^axiom" "$f" 2>/dev/null || echo 0)
  if [ "$s" -gt 0 ] || [ "$a" -gt 3 ]; then
    echo "$f: $s sorries, $a axioms"
  fi
done
```

### Emergency Fixes
```lean
-- If stuck on natural number arithmetic:
omega

-- If stuck on ring arithmetic:
ring

-- If Finset membership is the issue:
simp only [Finset.mem_filter, Finset.mem_univ, true_and]

-- If List indexing is the issue:
simp only [List.get_eq_getElem]
rw [List.getElem_eraseIdx]
split_ifs with h <;> omega
```

---

## 🌟 Success Metrics

### For This Session
- [ ] Sorries fixed or reduced
- [ ] No new axioms added without justification
- [ ] All modified files build successfully
- [ ] Quality maintained or improved

### For Phase Completion
- [ ] 0 sorries in Foundations and H1Characterization
- [ ] ≤50 total axioms
- [ ] Quality score ≥95/100
- [ ] All Crown Jewel theorems complete

### For Project Completion
- [ ] 4,000+ theorems
- [ ] 0 sorries
- [ ] ≤30 axioms (all documented as foundational)
- [ ] Publication-ready mathematical rigor

---

*This document is the source of truth for COBOUND development. When in doubt, refer here.*