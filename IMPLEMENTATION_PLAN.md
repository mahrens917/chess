# Implementation Plan: Float → ℝ Refactoring

## Overview
Refactor the Finance codebase to use Lean's `ℝ` (Real numbers) for theorem proofs and computational theorems, keeping `Float` for practical computation functions.

**Scope:** 199 theorems across 37 files
**Estimated Phases:** 5
**Key Principle:** All theorems prove arbitrage impossibility using real analysis; detection functions use Float approximations.

---

## Architecture Pattern

### Before (Current)
```lean
-- Everything uses Float
theorem putcall_parity_with_fees
  (call put stock bond : Quote)  -- Quote.bid/ask : Float
  (rate : Rate)                   -- Rate.val : Float
  : ... := by sorry
```

### After (Target)
```lean
-- Theorems use ℝ, detection uses Float
theorem putcall_parity_with_fees
  (call put stock bond : Quote)  -- Quote.bid/ask : ℝ
  (rate : Rate)                   -- Rate.val : ℝ
  : C - P = S - K·exp(-r·T) := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{...}, trivial⟩  -- nlinarith works here!

-- Separate computational version
def checkPutcallParity_with_fees
  (call put stock bond : Quote)  -- Quote.bid/ask : Float
  (rate : Rate)                   -- Rate.val : Float
  : Bool :=
  |call.ask.val - put.bid.val - (stock.ask.val - bond.bid.val)| < epsilon
```

---

## Phase 1: Foundation (Priority 1)

### 1.1 Update Finance/Core/Types.lean
**Goal:** Redefine Quote, Rate, Time, Fees to use ℝ instead of Float

**Changes:**
```lean
-- OLD
structure PosReal where
  val : Float
  pos : val > 0

-- NEW
structure PosReal where
  val : ℝ
  pos : val > 0

-- OLD
structure Quote where
  bid ask : PosReal
  valid : bid.val ≤ ask.val

-- NEW (same structure, but PosReal now contains ℝ)

-- OLD
structure Fees where
  fixed proportional : Float
  fixed_nonneg : fixed ≥ 0
  prop_nonneg : proportional ≥ 0

-- NEW
structure Fees where
  fixed proportional : ℝ
  fixed_nonneg : fixed ≥ 0
  prop_nonneg : proportional ≥ 0

-- Updated totalFee function
def Fees.totalFee (fees : Fees) (amount : ℝ) (ha : amount ≥ 0) : ℝ :=
  fees.fixed + fees.proportional * amount

-- Update Rate to use ℝ
structure Rate where
  val : ℝ

-- Update Time to use ℝ
structure Time where
  val : ℝ
  nonneg : val ≥ 0

-- Update discountFactor to use Real.exp
def Rate.discountFactor (r : Rate) (t : Time) : ℝ :=
  Real.exp (-(r.val * t.val))
```

**Files Affected:** 1 (Core/Types.lean)
**Theorems Affected:** All 199 (via type definitions)

### 1.2 Update Finance/Core/Arbitrage.lean
**Goal:** Ensure Arbitrage structure works with ℝ types

**Changes:**
```lean
-- OLD
structure Arbitrage where
  initialCost : Float
  minimumPayoff : Float
  isArb : (initialCost ≤ 0) ∨ (minimumPayoff ≥ 0)

-- NEW
structure Arbitrage where
  initialCost : ℝ
  minimumPayoff : ℝ
  isArb : (initialCost ≤ 0) ∨ (minimumPayoff ≥ 0)
```

**No new theorems needed** - just type updates.

---

## Phase 2: Options Bounds (Priority 2)

### 2.1 Convert Finance/Options/Bounds.lean
**Goal:** Convert 9 production theorems + 9 theoretical to use ℝ

**Current Pattern:**
```lean
theorem callUpperBound_with_fees (call spot : Quote) (call_fees spot_fees : Fees) :
  call.ask.val + Fees.totalFee call_fees call.ask.val (by sorry) ≤
  spot.bid.val - Fees.totalFee spot_fees spot.bid.val (by sorry) := by
  sorry
```

**Target Pattern:**
```lean
theorem callUpperBound_with_fees (call spot : Quote) (call_fees spot_fees : Fees) :
  call.ask + Fees.totalFee call_fees call.ask ≤
  spot.bid - Fees.totalFee spot_fees spot.bid := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := -(call.ask + Fees.totalFee call_fees call.ask - spot.bid + Fees.totalFee spot_fees spot.bid)
    minimumPayoff := 0
    isArb := Or.inr ⟨by nlinarith, by norm_num⟩
  }, trivial⟩
```

**Key Changes:**
- Remove `.ask.val`, `.bid.val` → use `.ask`, `.bid` (now ℝ)
- Replace `by sorry` proofs with `nlinarith`
- Use `Real.exp` instead of `Float.exp` for discount factors

**Files Affected:** 1 (Options/Bounds.lean)
**Theorems Converted:** 18 (9 production + 9 theoretical)

---

## Phase 3: Options Monotonicity & Convexity (Priority 3-4)

### 3.1 Convert Finance/Options/Monotonicity.lean
**Goal:** 4 theorems + theoretical variants

**Pattern:** Linear inequalities on strike differences
- `callMonotonicity_with_fees`
- `putMonotonicity_with_fees`
- Variants for different strikes

**Expected Proof Difficulty:** EASY (use `linarith` for all)

### 3.2 Convert Finance/Options/Convexity.lean
**Goal:** 4 theorems + theoretical variants

**Pattern:** Butterfly inequalities with 2x multiplier
- `callButterflyConvexity_with_fees`
- `putButterflyConvexity_with_fees`

**Expected Proof Difficulty:** MEDIUM (require lattice order properties)

**Files Affected:** 2
**Theorems Converted:** 16 (4 + 4 production, plus theoretical)

---

## Phase 4: Complex Multi-Leg Strategies (Priority 5)

### 4.1 Convert Finance/ArbitrageDetection.lean
**Goal:** 14 theorems covering:
- Put-call parity
- Cash-and-carry
- Box spreads
- Butterfly spreads
- Triangular FX arbitrage
- ETF basket arbitrage
- Variance swap replication
- Straddle vol arbitrage
- Commodity cash-carry
- Specialty repo arbitrage

**Pattern:** Each combines multiple quotes with fees
- Call upper bound: `C_ask ≤ S_bid`
- Put-call parity: `C - P = S - K·DF + fees`
- Forward pricing: `F = S·exp((r-q)T) ± fees`

**Expected Proof Difficulty:** MEDIUM (mostly linear but with Forward pricing using `Real.exp`)

**Files Affected:** 1
**Theorems Converted:** 14

---

## Phase 5: Interest Rates & Advanced (Priority 6-9)

### 5.1 Interest Rates (Priority 6)
**File:** Finance/InterestRates.lean
**Theorems:** 9
**Challenge:** Discount factor = `Real.exp(-r·T)`
**Strategy:** Replace `Float.exp` with `Real.exp`, use its properties from mathlib

### 5.2 Bond Convexity (Priority 7)
**File:** Finance/BondConvexity.lean
**Theorems:** 13
**Challenge:** Bond price functions (convex), duration calculations
**Strategy:** Use `Real.exp` and convexity properties

### 5.3 Volatility Derivatives (Priority 8)
**File:** Finance/VolatilityDerivatives.lean + Finance/StochasticCalculus.lean
**Theorems:** 23
**Challenge:** Square roots, quadratic variation
**Strategy:** Use `Real.sqrt` and variance relationships

### 5.4 Credit Derivatives (Priority 9)
**File:** Finance/CreditDerivatives.lean
**Theorems:** 13
**Challenge:** Hazard rates, survival probabilities (involve logarithms)
**Strategy:** Use hazard rate axioms and monotonicity properties

---

## Implementation Strategy

### Step 1: Batch Type Updates (Hour 1)
1. Update Finance/Core/Types.lean (Float → ℝ in all structures)
2. Update Rate/Time helpers to use Real.exp
3. Build to verify no import errors

### Step 2: Batch Proof Updates by Pattern (Hours 2-8)

**For each file in priority order:**

1. **Read** the current theorem signatures
2. **Replace** `.val` → `.` (since values are already ℝ)
3. **Replace** `by sorry` with proof pattern:
   ```lean
   by_contra h; push_neg at h; exfalso
   exact noArbitrage ⟨{...}, trivial⟩
   ```
4. **Use tactics** based on structure:
   - Linear inequalities → `linarith`
   - Numeric constants → `norm_num`
   - Exponential relationships → `Real.exp` properties
   - Mixed → `nlinarith`

### Step 3: Keep Computational Functions (Unchanged)
- All `def check*` functions keep their Float signatures
- They become approximations of the ℝ theorems
- Serve as "extraction functions" from theory to practice

---

## Expected Proof Improvements

### Before (Float)
```lean
theorem putcall_parity_with_fees ... := by sorry  -- Can't prove with Float!
```

### After (ℝ)
```lean
theorem putcall_parity_with_fees ... := by
  by_contra h; push_neg at h; exfalso
  exact noArbitrage ⟨{
    initialCost := -(call.ask + ... )
    minimumPayoff := 0
    isArb := Or.inr ⟨by nlinarith, by norm_num⟩  -- Actual proof!
  }, trivial⟩
```

---

## Risk Mitigation

**Risk 1: Breaking existing theorems**
- Mitigation: Type changes are localized to types.lean; structure is identical

**Risk 2: Real.exp not having required properties**
- Mitigation: Use mathlib's Real module; `exp` is well-developed

**Risk 3: nlinarith failing on complex inequalities**
- Mitigation: Have fallback to explicit case analysis or `omega` for integer-valued ℝ

**Risk 4: Large refactoring introduces errors**
- Mitigation: Phase-based approach; test after each phase

---

## Timeline Estimate

| Phase | Files | Theorems | Time | Difficulty |
|-------|-------|----------|------|------------|
| 1 | 2 | 5 | 30 min | LOW |
| 2 | 1 | 18 | 2 hrs | LOW |
| 3 | 2 | 16 | 2 hrs | LOW-MED |
| 4 | 1 | 14 | 2 hrs | MEDIUM |
| 5 | 4 | 146 | 8+ hrs | HIGH |
| **Total** | **37** | **199** | **14+ hrs** | **MIXED** |

---

## Success Criteria

1. ✅ All theorems compile
2. ✅ No `sorry` in theorem proofs (replaced with actual proofs)
3. ✅ Detection functions still work with Float
4. ✅ Build passes
5. ✅ CLAUDE.md updated with new approach

---

## CLAUDE.md Updates Needed

Add section explaining:
1. Why ℝ for theorems, Float for computation
2. How the two systems interact (extraction functions)
3. Example of ℝ theorem vs Float detector
4. How new theorems should follow this pattern
5. Proof tactics to use (nlinarith, linarith, norm_num)
