# Finance: Formal No-Arbitrage Framework

A Lean 4 framework for formally verifying financial no-arbitrage conditions and computationally detecting arbitrage opportunities across markets.

## Vision

Markets are governed by no-arbitrage principles: you cannot make risk-free profit without capital. These principles manifest as mathematical constraints between prices of related instruments. When constraints are violated, arbitrage opportunities exist.

**This project aims to:**

1. **Formalize** no-arbitrage rules as mathematical theorems in Lean 4
2. **Prove** these rules hold under no-arbitrage assumptions
3. **Detect** violations computationally using the contrapositive of each theorem
4. **Discover** new rules by composing and generalizing existing ones

## Why Formal Verification?

| Approach | Limitation |
|----------|------------|
| Spreadsheets | No proof of correctness, easy to make errors |
| Trading algorithms | Encode rules but don't prove them |
| Academic papers | Proofs exist but aren't machine-checkable |

**Lean 4 gives us:**
- Machine-verified proofs that rules are mathematically correct
- Executable code extracted from proofs for real-time detection
- Compositional reasoning to derive new rules from existing ones
- Type safety preventing nonsensical operations (e.g., adding prices to rates)

## Core Design Principles

### Continuous Time, Positive Prices
- Time modeled as non-negative reals
- Prices as strictly positive floats
- Interest rates can be negative (real-world reality)

### Bid/Ask Spreads
Every tradeable price is a `Quote` with bid ≤ ask:
- You **buy** at the ask (pay more)
- You **sell** at the bid (receive less)
- The spread creates friction that tightens arbitrage bounds

### Transaction Fees
Real arbitrage must overcome costs:
- Fixed fees per trade
- Proportional fees (basis points)
- Profit must exceed total fees to be exploitable

### Proofs AND Computation
Every theorem has two forms:
- **Proof**: `no_arbitrage → constraint`
- **Detection**: `¬constraint → arbitrage_exists` (contrapositive)

The detection form is computable and runs against live market data.

---

## Rule Taxonomy

```
                            ┌─────────────────────────────────────┐
                            │         NO-ARBITRAGE AXIOM          │
                            │  "No risk-free profit without cost" │
                            └──────────────────┬──────────────────┘
                                               │
                 ┌─────────────────────────────┼─────────────────────────────┐
                 │                             │                             │
                 ▼                             ▼                             ▼
    ┌────────────────────────┐   ┌────────────────────────┐   ┌────────────────────────┐
    │     OPTION RULES       │   │    FORWARD RULES       │   │   CROSS-MARKET RULES   │
    └───────────┬────────────┘   └───────────┬────────────┘   └───────────┬────────────┘
                │                            │                            │
    ┌───────────┴───────────┐    ┌───────────┴───────────┐    ┌───────────┴───────────┐
    │                       │    │                       │    │                       │
    ▼                       ▼    ▼                       ▼    ▼                       ▼
┌─────────┐           ┌─────────┐ ┌─────────┐      ┌─────────┐ ┌─────────┐      ┌─────────┐
│ Single  │           │ Surface │ │  Spot-  │      │   FX    │ │ ETF vs  │      │ Futures │
│ Option  │           │  Rules  │ │ Forward │      │ Forward │ │  Under- │      │   vs    │
│ Bounds  │           │         │ │ Parity  │      │         │ │  lying  │      │ Options │
└────┬────┘           └────┬────┘ └─────────┘      └────┬────┘ └─────────┘      └─────────┘
     │                     │                            │
     ▼                     ▼                            ▼
┌─────────┐           ┌─────────┐                 ┌─────────┐
│Put-Call │           │ Strike  │                 │Triangu- │
│ Parity  │           │  Mono-  │                 │lar Arb  │
│         │           │ tonicity│                 │         │
└─────────┘           └────┬────┘                 └─────────┘
                           │
                           ▼
                      ┌─────────┐
                      │Butterfly│
                      │Convexity│
                      └────┬────┘
                           │
                           ▼
                      ┌─────────┐
                      │Calendar │
                      │ Spread  │
                      └─────────┘
```

---

## Rules to Formalize

### Phase 1: Option Foundations

| Rule | Statement | Detection Signal |
|------|-----------|------------------|
| **Put-Call Parity** | `C - P = S - K·e^(-rT)` | Synthetic vs actual price divergence |
| **Call Upper Bound** | `C ≤ S` | Call priced above spot |
| **Call Lower Bound** | `C ≥ max(0, S - K·e^(-rT))` | Call below intrinsic value |
| **Put Upper Bound** | `P ≤ K·e^(-rT)` | Put above discounted strike |
| **Put Lower Bound** | `P ≥ max(0, K·e^(-rT) - S)` | Put below intrinsic value |

### Phase 2: Option Surface Constraints

| Rule | Statement | Detection Signal |
|------|-----------|------------------|
| **Call Strike Monotonicity** | `K₁ < K₂ → C(K₁) ≥ C(K₂)` | Higher strike call costs more |
| **Put Strike Monotonicity** | `K₁ < K₂ → P(K₁) ≤ P(K₂)` | Lower strike put costs more |
| **Butterfly Convexity** | `C(K₂) ≤ λC(K₁) + (1-λ)C(K₃)` | Negative butterfly spread |
| **Calendar Spread** | `T₁ < T₂ → C(K,T₁) ≤ C(K,T₂)` | Near-dated costs more |

### Phase 3: Forward/Futures Rules

| Rule | Statement | Detection Signal |
|------|-----------|------------------|
| **Spot-Forward Parity** | `F = S·e^((r-q)T)` | Forward mispriced vs spot |
| **Covered Interest Parity** | `F/S = (1+r_d)/(1+r_f)` | FX forward mispriced |
| **Futures Convergence** | `F → S` as `T → 0` | Basis blow-out near expiry |

### Phase 4: Cross-Market Rules

| Rule | Statement | Detection Signal |
|------|-----------|------------------|
| **Triangular Arbitrage** | `(A/B)·(B/C)·(C/A) = 1` | Cross-rate inconsistency |
| **ETF vs Basket** | `ETF ≈ Σ wᵢ·Sᵢ` | ETF premium/discount |
| **Synthetic Forward** | `C - P + K·e^(-rT) = F·e^(-rT)` | Option-implied vs actual forward |

---

## Discovery Through Composition

Formalizing rules enables discovering new ones:

```
┌─────────────────┐     ┌─────────────────┐
│   Put-Call      │     │  Spot-Forward   │
│   Parity        │     │    Parity       │
│ C - P = S - Ke⁻ʳᵀ│     │   F = Se^(rT)   │
└────────┬────────┘     └────────┬────────┘
         │                       │
         └───────────┬───────────┘
                     │ compose
                     ▼
         ┌───────────────────────┐
         │   Options-Forward     │
         │      Relationship     │
         │  C - P = (F - K)e⁻ʳᵀ  │
         └───────────────────────┘
                     │
                     │ + Triangular FX Arb
                     ▼
         ┌───────────────────────┐
         │  Cross-Currency       │
         │  Option Arbitrage     │
         │  (new discovery!)     │
         └───────────────────────┘
```

**Key insight**: The contrapositive of composed theorems yields detection algorithms for complex multi-market arbitrage that may not be obvious from individual rules.

---

## Architecture

```
Finance/
├── Core/
│   ├── Types.lean          -- PosReal, Quote, Fees, Time, Rate
│   ├── Arbitrage.lean      -- Arbitrage type, no-arb axioms
│   └── Tactics.lean        -- Custom tactics for financial proofs
│
├── Options/
│   ├── European.lean       -- Put-call parity, bounds
│   ├── Surface.lean        -- Strike monotonicity, convexity
│   └── Calendar.lean       -- Time structure constraints
│
├── Forwards/
│   ├── SpotForward.lean    -- Cost of carry
│   ├── FX.lean             -- Covered interest parity
│   └── Futures.lean        -- Futures-specific rules
│
├── CrossMarket/
│   ├── Triangular.lean     -- FX triangular arbitrage
│   ├── ETF.lean            -- ETF vs underlying
│   └── Synthetic.lean      -- Synthetic positions
│
└── Detection/
    ├── Checker.lean        -- Computable constraint checkers
    ├── Scanner.lean        -- Multi-rule violation scanner
    └── Report.lean         -- Arbitrage opportunity reporting
```

---

## The Arbitrage Type

Central to everything is a formal definition of arbitrage:

```lean
/-- An arbitrage is a trading strategy with non-positive cost
    and strictly positive payoff, or negative cost and
    non-negative payoff. -/
structure Arbitrage where
  initialCost : Float      -- What you pay to enter (negative = you receive)
  minimumPayoff : Float    -- Guaranteed minimum at exit
  isArbitrage : (initialCost ≤ 0 ∧ minimumPayoff > 0) ∨
                (initialCost < 0 ∧ minimumPayoff ≥ 0)
```

Every no-arbitrage theorem proves:
```lean
theorem no_arb_implies_X (h : ¬∃ a : Arbitrage, ...) : X := ...
```

The contrapositive gives detection:
```lean
theorem detect_arb_from_not_X (h : ¬X) : ∃ a : Arbitrage, ... := ...
```

---

## Practical Workflow

```
┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│ Market Data  │────▶│   Checker    │────▶│  Violations  │
│ (quotes,     │     │ (runs all    │     │  (list of    │
│  rates, etc) │     │  rules)      │     │  broken      │
└──────────────┘     └──────────────┘     │  constraints)│
                                          └──────┬───────┘
                                                 │
                     ┌──────────────┐            │
                     │   Report     │◀───────────┘
                     │ (arbitrage   │
                     │  opportunities│
                     │  with P&L)   │
                     └──────────────┘
```

---

## Why This Matters

1. **Correctness**: Proofs are machine-checked; no subtle math errors
2. **Completeness**: Systematic coverage of known no-arb conditions
3. **Discovery**: Composition reveals non-obvious cross-market opportunities
4. **Speed**: Compiled Lean code runs fast on live data
5. **Extensibility**: Add new rules; they automatically compose with existing ones

---

## Getting Started

```bash
# Build the project
lake build

# Run tests
lake test

# Run the demo
lake exe demo
```

---

## References

- Harrison & Pliska (1981) - Martingales and stochastic integrals in the theory of continuous trading
- Carr & Madan (2005) - A note on sufficient conditions for no arbitrage
- Gatheral (2006) - The Volatility Surface
- Shreve (2004) - Stochastic Calculus for Finance

---

## Status

| Component | Status |
|-----------|--------|
| Core Types | Planned |
| Put-Call Parity | Planned |
| Option Bounds | Planned |
| Surface Constraints | Planned |
| Forward Rules | Planned |
| Cross-Market | Planned |
| Detection Engine | Planned |

---

## License

[TBD]
