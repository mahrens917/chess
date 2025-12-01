-- Calendar spreads and time-dependent option constraints
-- Enforces that option prices must increase (in value) with time to expiry

import Finance.Core
import Finance.Options.European

namespace Finance.Options

-- ============================================================================
-- Calendar Spread Definition
-- ============================================================================

/-- A calendar spread (or diagonal spread): long option with longer expiry,
    short option with shorter expiry, same strike.

    For calls: Buy C(K, T2), Sell C(K, T1) where T1 < T2
    For puts: Buy P(K, T2), Sell P(K, T1) where T1 < T2

    Intuition: The longer-dated option has more time value and should be worth more.
    A calendar spread profits if the longer-dated option appreciates more than
    the shorter-dated option depreciates (or decays less slowly).

    The spread is essentially a bet on volatility and time decay:
    - Long spread = betting volatility stays high or increases
    - Short spread = betting volatility drops or time decay is fast
-/
structure CalendarSpread where
  strike : Float
  nearExpiry : Time    -- T1: shorter time to expiry
  farExpiry : Time     -- T2: longer time to expiry

-- ============================================================================
-- Call Calendar Spread Monotonicity
-- ============================================================================

/-- Call Calendar Monotonicity: T₁ < T₂ → C(K, T₁) ≤ C(K, T₂)

    For the same strike K, a call option with longer time to expiry
    must be worth at least as much as one with shorter time to expiry.

    C(K, T₁) ≤ C(K, T₂) when T₁ < T₂

    Proof: An option with longer expiry is "more valuable" because:
    1. It has all the same exercise opportunities as the shorter-dated option
    2. Plus additional opportunities after T₁
    3. So it dominates the shorter-dated option

    More formally: if we could exercise early (American option), it's obvious.
    For European options, we use put-call parity and forward prices:
    - C(K,T2) - C(K,T1) = e^(-r·T1)·[F(T2) - F(T1)] + interest rate effects

    Violation creates calendar spread arbitrage:
    - If C(K, T₁) > C(K, T₂): sell near, buy far, lock in profit at T₁
-/
theorem callCalendarMonotonicity
    (K : Float) (T1 T2 : Time) (C1 C2 : Float)
    (hT : T1.val < T2.val) :
    C1 ≤ C2 := by
  -- Call Calendar Monotonicity follows from option dominance.
  -- Proof: A call with longer expiry has all the same payoff opportunities
  -- as the shorter-dated call, plus additional ones. By no-arbitrage,
  -- it cannot be worth less.
  sorry  -- Requires no-arbitrage axiom and option dominance argument

/-- Put Calendar Monotonicity: T₁ < T₂ → P(K, T₁) ≤ P(K, T₂)

    For puts, the same principle applies: longer expiry = more value.
    -/
theorem putCalendarMonotonicity
    (K : Float) (T1 T2 : Time) (P1 P2 : Float)
    (hT : T1.val < T2.val) :
    P1 ≤ P2 := by
  -- Put Calendar Monotonicity by the same argument as calls.
  sorry

-- ============================================================================
-- Calendar Spread Arbitrage Detection
-- ============================================================================

/-- Check if call calendar spread is mispriced (near more expensive than far).

    Returns the profit from: sell near call at ask, buy far call at bid.

    If C(K, T1)_ask > C(K, T2)_bid, the spread is profitable and signals
    the near call is too expensive or the far call is too cheap.

    Arbitrage execution at T₁:
    1. Sell the near call at C(K,T1)_ask (collect premium)
    2. Buy the far call at C(K,T2)_bid (pay premium)
    3. At time T₁:
       - If S > K: near call is exercised against you, you must buy at K to deliver
         (but your far call still has value, protecting you)
       - If S ≤ K: near call expires worthless, you keep the initial spread
    4. Profit = C(K,T1)_ask - C(K,T2)_bid - interest costs
-/
def checkCallCalendarViolation
    (callNearAsk callFarBid : Float)
    (K : Float) (T1 T2 : Time) :
    Float :=
  -- For now, just the naive spread without adjusting for financing costs
  callNearAsk - callFarBid

/-- Check if put calendar spread is mispriced. -/
def checkPutCalendarViolation
    (putNearAsk putFarBid : Float)
    (K : Float) (T1 T2 : Time) :
    Float :=
  putNearAsk - putFarBid

-- ============================================================================
-- Time Decay and Theta
-- ============================================================================

/-- Time decay (theta): how much an option loses value per unit time as expiry approaches.

    For European options, theta is typically negative for long options:
    as time passes, the option loses value (all else equal).

    Theta = -∂C/∂T

    In the Black-Scholes model, theta becomes increasingly negative as expiry approaches,
    especially for at-the-money options.

    For arbitrage purposes: if we observe two options at different expirations,
    the rate at which the near-dated option decays should match theoretical theta.

    Abnormal theta (slower or faster decay) signals mispricing.
-/
def theta
    (optionPrice : Float)
    (timeToExpiry : Time)
    (dPriceDTime : Float) :  -- How much price changes per unit time
    Float :=
  -dPriceDTime  -- Negative because price decreases as time increases

/-- Intrinsic value: the payoff if exercised immediately. -/
def callIntrinsicValue (spot strike : Float) : Float :=
  max 0 (spot - strike)

def putIntrinsicValue (spot strike : Float) : Float :=
  max 0 (strike - spot)

/-- Time value: total option value minus intrinsic value. -/
def callTimeValue (price spot strike : Float) : Float :=
  max 0 (price - max 0 (spot - strike))

def putTimeValue (price spot strike : Float) : Float :=
  max 0 (price - max 0 (strike - spot))

-- ============================================================================
-- Calendar Spread Analysis Structure
-- ============================================================================

/-- Result of analyzing a calendar spread for violations. -/
structure CalendarSpreadAnalysis where
  strike : Float
  nearExpiry : Float
  farExpiry : Float
  timeSpan : Float  -- T2 - T1
  optionType : String  -- "call" or "put"
  nearPrice : Float
  farPrice : Float
  spreadCost : Float  -- Cost of spread (far ask - near bid)
  profitIfViolation : Float  -- Profit if arbitrage exists
  hasArbitrage : Bool
  profitAsPercent : Float

/-- Analyze a call calendar spread for mispricing. -/
def analyzeCallCalendarSpread
    (K : Float) (T1 T2 : Float)
    (callNear callFar : Quote) :
    CalendarSpreadAnalysis :=
  let timeSpan := T2 - T1
  let nearMid := Quote.mid callNear
  let farMid := Quote.mid callFar
  let spreadCost := callFar.ask.val - callNear.bid.val
  let violation := checkCallCalendarViolation callNear.ask.val callFar.bid.val K ⟨T1, by sorry⟩ ⟨T2, by sorry⟩
  let arb := violation > 0
  let pctProfit := if nearMid > 0 then (violation / nearMid) * 100 else 0

  ⟨K, T1, T2, timeSpan, "call", nearMid, farMid, spreadCost, violation, arb, pctProfit⟩

/-- Analyze a put calendar spread for mispricing. -/
def analyzePutCalendarSpread
    (K : Float) (T1 T2 : Float)
    (putNear putFar : Quote) :
    CalendarSpreadAnalysis :=
  let timeSpan := T2 - T1
  let nearMid := Quote.mid putNear
  let farMid := Quote.mid putFar
  let spreadCost := putFar.ask.val - putNear.bid.val
  let violation := checkPutCalendarViolation putNear.ask.val putFar.bid.val K ⟨T1, by sorry⟩ ⟨T2, by sorry⟩
  let arb := violation > 0
  let pctProfit := if nearMid > 0 then (violation / nearMid) * 100 else 0

  ⟨K, T1, T2, timeSpan, "put", nearMid, farMid, spreadCost, violation, arb, pctProfit⟩

-- ============================================================================
-- Calendar Spread Composition with Butterfly Spreads
-- ============================================================================

/-- Diagonal Calendar Butterfly: time-dependent butterfly spread.

    Use options at three different expirations: T1 < T2 < T3

    Structure: Buy C(K, T3), Sell 2×C(K, T2), Buy C(K, T1)

    This combines:
    - Convexity in strike (butterfly)
    - Calendar spread effects (time dependencies)

    Violations simultaneously break both strike and time monotonicity,
    offering potentially larger arbitrage opportunities.
-/
structure DiagonalCalendarButterfly where
  strike : Float
  expiry1 : Time
  expiry2 : Time
  expiry3 : Time
  callPrice1 : Float
  callPrice2 : Float
  callPrice3 : Float

/-- Check diagonal butterfly for combined violations. -/
def checkDiagonalButterflyViolation
    (butterfly : DiagonalCalendarButterfly) :
    Float :=
  -- Combined violation of strike convexity and time monotonicity
  let basicButterfly := butterfly.callPrice1 - 2 * butterfly.callPrice2 + butterfly.callPrice3
  let timeEffect := (butterfly.callPrice3 - butterfly.callPrice1) / 2 -
                    butterfly.callPrice2
  basicButterfly + timeEffect

end Finance.Options
