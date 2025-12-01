-- Synthetic forward and options composition
-- Discovers no-arbitrage relationships by composing option and forward rules

import Finance.Core
import Finance.Options.European
import Finance.Forwards.SpotForward

namespace Finance.CrossMarket

-- ============================================================================
-- Synthetic Forward = Call - Put + Strike
-- ============================================================================

/-- A synthetic forward: replicate a forward contract using options and bonds.

    Buying a synthetic forward:
    1. Buy a call option at strike K (cost = C)
    2. Sell a put option at strike K (receive = P)
    3. Lend money at risk-free rate for discounted strike K·e^(-rT) (costs K·e^(-rT))

    Net payoff at expiry:
    - If S > K: exercise call (get asset at K), put expires worthless
      → Receive asset, net cost = K
    - If S ≤ K: put is exercised (you buy at K), call expires worthless
      → Receive asset, net cost = K
    - Either way: you own the asset, having paid K

    This is identical to a forward contract.

    Cost today: C - P + K·e^(-rT) (interest on borrowing)
    This should equal the forward price: F·e^(-rT)

    So: C - P + K·e^(-rT) = F·e^(-rT)
    Or: C - P = (F - K)·e^(-rT)
    Or: C - P = S·e^(-rT) - K·e^(-rT) = (S - K)·e^(-rT)  [put-call parity]
-/
theorem syntheticForwardEquivalence
    (callPrice putPrice strike forwardPrice : Float)
    (rate : Rate) (time : Time) :
    callPrice - putPrice + strike * Rate.discountFactor rate time =
    forwardPrice * Rate.discountFactor rate time := by
  -- The synthetic forward (long call + short put + borrow) equals the forward.
  -- Proof: Both positions give you the underlying asset at price K (or F).
  -- By no-arbitrage, they must cost the same today.
  sorry  -- Requires put-call parity

-- ============================================================================
-- Options-Forward Mispricing
-- ============================================================================

/-- Check if the synthetic forward is more expensive than the actual forward.

    If C - P + K·e^(-rT) > F·e^(-rT), you can:
    1. Sell the synthetic (sell call, buy put, borrow)
    2. Buy the forward
    3. Lock in profit at expiry

    Returns the deviation (positive = profit opportunity).
-/
def checkSyntheticVsForwardMispricing
    (callAsk putBid strike forwardBid : Float)
    (rate : Rate) (time : Time) :
    Float :=
  let df := Rate.discountFactor rate time
  let syntheticCost := callAsk - putBid + strike * df
  let forwardCost := forwardBid * df
  syntheticCost - forwardCost  -- Positive = synthetic is expensive

/-- Check if the actual forward is more expensive than the synthetic.

    If F·e^(-rT) > C - P + K·e^(-rT), you can:
    1. Buy the synthetic (buy call, sell put, lend)
    2. Sell the forward
    3. Lock in profit at expiry
-/
def checkForwardVsSyntheticMispricing
    (callBid putAsk strike forwardAsk : Float)
    (rate : Rate) (time : Time) :
    Float :=
  let df := Rate.discountFactor rate time
  let syntheticCost := callBid - putAsk + strike * df
  let forwardCost := forwardAsk * df
  forwardCost - syntheticCost  -- Positive = forward is expensive

-- ============================================================================
-- Box Spread: Composition of Two Vertical Spreads
-- ============================================================================

/-- A box spread: buy a call spread and sell a put spread at different strikes.

    Example: K1 < K2
    1. Buy call at K1, sell call at K2 (bull call spread)
    2. Sell put at K1, buy put at K2 (bear put spread)

    Payoff at expiry:
    - If S ≤ K1: calls worthless, short puts exercised
      → You buy at K1, owning the difference = K2 - K1
    - If K1 < S < K2: long call exercised, long put exercised
      → You buy at K1 with long put, sell at K2 with short call = K2 - K1
    - If S ≥ K2: short call exercised, puts worthless
      → You buy at K1 with long call, deliver at K2 = K2 - K1

    The payoff is always K2 - K1 (the "box"), regardless of stock price.
    This is a risk-free trade.

    Cost today: (C1 - C2) - (P1 - P2) + (K2 - K1)·e^(-rT)

    By no-arbitrage, this cost must equal the present value of K2 - K1:
    (C1 - C2) - (P1 - P2) = (K2 - K1)·(1 - e^(-rT))

    Violation = arbitrage: if the box costs less than it's worth, buy it.
-/
def boxSpreadPayoff (K1 K2 : Float) : Float :=
  K2 - K1  -- Always get this at expiry

def boxSpreadCost
    (C1 C2 P1 P2 K1 K2 : Float)
    (rate : Rate) (time : Time) :
    Float :=
  let df := Rate.discountFactor rate time
  (C1 - C2) - (P1 - P2) + (K2 - K1) * df

def boxSpreadArbitrage
    (C1 C2 P1 P2 K1 K2 : Float)
    (rate : Rate) (time : Time) :
    Float :=
  let boxValue := boxSpreadPayoff K1 K2 * Rate.discountFactor rate time
  let cost := boxSpreadCost C1 C2 P1 P2 K1 K2 rate time
  boxValue - cost  -- Positive = buy the box

-- ============================================================================
-- Butterfly and Box Combinations
-- ============================================================================

/-- A butterfly spread combined with box structure:

    Buy call butterfly (K1, K2, K3) and sell put butterfly (K1, K2, K3).

    This combines the convexity constraint with the put-call relationship,
    creating a more sophisticated no-arbitrage condition.

    The violation of this combined condition signals deeper mispricing.
-/
def butterflyBoxViolation
    (C1 C2 C3 P1 P2 P3 K1 K2 K3 : Float)
    (rate : Rate) (time : Time) :
    Float :=
  let df := Rate.discountFactor rate time
  -- Call butterfly cost
  let callButterfly := C1 - (2 : Float) * C2 + C3
  -- Put butterfly cost
  let putButterfly := P1 - (2 : Float) * P2 + P3
  -- Combined: should be zero by put-call parity
  (callButterfly - putButterfly) * df

-- ============================================================================
-- Options vs Futures Equivalence
-- ============================================================================

/-- Options on futures should price consistently with options on spot.

    For a futures contract, there's a fundamental relationship:
    C_futures(K, T) ≈ C_spot(K, T) (when adjusted for financing)

    Violation creates spread arbitrage between options markets.
-/
def spotOptionsVsFuturesOptions
    (callSpotPrice callFuturesPrice : Float)
    (rate yield : Rate) (time : Time) :
    Float :=
  let df := Rate.discountFactor rate time
  let expectedRatio := Float.exp ((yield.val - rate.val) * time.val)
  callSpotPrice - (callFuturesPrice * expectedRatio)

-- ============================================================================
-- Cross-Maturity Spread: Diagonal Calendar Spread Arbitrage
-- ============================================================================

/-- Synthetic forward at different maturities should be consistent.

    If we can create a synthetic forward at T1 and another at T2,
    the forward rate implied by the T2 forward should match the forward rate
    from T1 to T2.

    Forward from T1 to T2 should equal:
    F(0,T2) / F(0,T1)

    Violation: buy one, sell the other, lock in the rate discrepancy.
-/
def impliedForwardFromNestedSynthetics
    (syntheticCost_T1 syntheticCost_T2 : Float)
    (time1 time2 : Time) :
    Float :=
  if syntheticCost_T1 > 0 then
    syntheticCost_T2 / syntheticCost_T1
  else
    0

-- ============================================================================
-- Composition Analysis Structure
-- ============================================================================

/-- Result of analyzing a synthetic-forward arbitrage. -/
structure SyntheticForwardArbitrage where
  callSymbol : String
  putSymbol : String
  forwardSymbol : String
  syntheticPrice : Float
  forwardPrice : Float
  mispricing : Float  -- How much they diverge
  profitOpportunity : Float  -- After fees
  arbitrageType : String  -- "synthetic_expensive" or "forward_expensive"
  recommendation : String

/-- Result of analyzing a box spread. -/
structure BoxSpreadArbitrage where
  K1 : Float
  K2 : Float
  boxValue : Float
  boxCost : Float
  profit : Float
  profitAsPercent : Float
  profitableIfBought : Bool  -- Cost < intrinsic value

/-- Comprehensive composition analysis. -/
structure CompositionArbitrageReport where
  syntheticForwardOpportunities : List SyntheticForwardArbitrage
  boxSpreadOpportunities : List BoxSpreadArbitrage
  butterflyBoxViolations : List Float
  totalOpportunities : Nat
  totalProfit : Float
  bestOpportunity : Option (String × Float)

end Finance.CrossMarket
