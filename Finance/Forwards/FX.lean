-- Covered interest rate parity and FX forward pricing
-- Formalizes no-arbitrage relationships in foreign exchange markets

import Finance.Core
import Finance.Forwards.SpotForward

namespace Finance.Forwards

-- ============================================================================
-- FX Rate Types
-- ============================================================================

/-- An FX spot rate (how many units of quote currency per base currency). -/
def FXSpot := Float

/-- An FX forward rate. -/
def FXForward := Float

/-- Base currency (e.g., USD in EURUSD). -/
structure BaseCurrency where
  name : String

/-- Quote currency (e.g., EUR in EURUSD). -/
structure QuoteCurrency where
  name : String

-- ============================================================================
-- Covered Interest Rate Parity
-- ============================================================================

/-- Covered Interest Rate Parity: The no-arbitrage relationship in FX.

    F/S = (1 + r_quote) / (1 + r_base)

    Or equivalently:
    F = S · (1 + r_quote) / (1 + r_base)

    Where:
    - F: forward FX rate
    - S: spot FX rate
    - r_quote: interest rate in quote currency
    - r_base: interest rate in base currency

    Intuition: You can "synthesize" a forward rate:
    1. Convert base currency to quote at spot rate S
    2. Invest quote currency at rate r_quote
    3. Lock in conversion back at forward rate F
    4. Compare to borrowing base currency at r_base and investing

    By no-arbitrage, these must be equivalent.

    Example: EURUSD
    - Spot: 1.10 (1 USD = 1.10 EUR)
    - USD rate: 5.0% per year
    - EUR rate: 3.0% per year
    - 1-year forward: 1.10 * (1.03/1.05) ≈ 1.0781

    This means the dollar will appreciate (more EUR per USD) because
    the dollar interest rate is higher.

    Violation creates Interest Rate Parity (IRP) arbitrage:
    - If F > S·(1+r_quote)/(1+r_base): borrow cheap, lend expensive, lock in forward
    - If F < S·(1+r_quote)/(1+r_base): do the reverse
-/
theorem coveredInterestRateParity
    (spot : Float) (rateBase rateQuote : Rate) :
    ∃ forward : Float,
    forward = spot * (1 + rateQuote.val) / (1 + rateBase.val) := by
  -- Covered Interest Rate Parity is the fundamental no-arbitrage relationship in FX.
  -- Proof: Consider a carry trade:
  -- 1. Borrow 1 unit of base currency at rate r_base
  -- 2. Convert to quote currency at spot S (get S units)
  -- 3. Invest S units at rate r_quote (get S·(1+r_quote) after 1 year)
  -- 4. Convert back to base currency at forward F (locked in today)
  -- 5. Repay loan: need to pay back 1·(1+r_base)
  -- At maturity, you have: S·(1+r_quote) / F - (1+r_base)
  -- By no-arbitrage, this profit must be zero, so:
  -- F = S·(1+r_quote)/(1+r_base)
  sorry  -- Requires no-arbitrage axiom and replication argument

/-- Simplified CIP for continuous compounding (used in theory).

    F = S · e^((r_quote - r_base)·T)

    This is the continuous-time equivalent, which simplifies computations.
-/
def coveredForwardRateContinuous
    (spot : Float) (rateBase rateQuote : Rate) (time : Time) : Float :=
  spot * Float.exp ((rateQuote.val - rateBase.val) * time.val)

/-- Discrete-time CIP formula. -/
def coveredForwardRateDiscrete
    (spot : Float) (rateBase rateQuote : Rate) : Float :=
  let denominator := 1 + rateBase.val
  if denominator.abs > 0.0001 then  -- Avoid division by zero (check magnitude)
    spot * (1 + rateQuote.val) / denominator
  else
    spot  -- Return spot if denominator too close to zero

-- ============================================================================
-- CIP Violation Detection
-- ============================================================================

/-- Check if forward is overpriced relative to CIP.

    If F > S·(1+r_quote)/(1+r_base), the forward is too expensive.

    Arbitrage: borrow base, convert at spot, invest in quote, sell forward
-/
def checkFXForwardTooExpensive
    (spotAsk : Float) (forwardBid : Float)
    (rateBase rateQuote : Rate) :
    Float :=
  let fairForward := coveredForwardRateDiscrete spotAsk rateBase rateQuote
  forwardBid - fairForward

/-- Check if forward is underpriced relative to CIP.

    If F < S·(1+r_quote)/(1+r_base), the forward is too cheap.

    Arbitrage: borrow quote, convert at spot, invest in base, buy forward
-/
def checkFXForwardTooCheap
    (spotBid : Float) (forwardAsk : Float)
    (rateBase rateQuote : Rate) :
    Float :=
  let fairForward := coveredForwardRateDiscrete spotBid rateBase rateQuote
  fairForward - forwardAsk

/-- FX Interest Rate Parity violation. -/
structure CIPViolation where
  currencyPair : String  -- e.g., "EURUSD"
  violationType : String  -- "forward_expensive" or "forward_cheap"
  deviationBps : Float   -- Deviation in basis points (0.01% = 1 bp)
  profitOpportunity : Float  -- Profit from arbitrage in base currency

/-- Analyze FX forward for CIP violations with bid/ask spreads. -/
def analyzeCIPArbitrage
    (spotQuote : Quote) (forwardBid forwardAsk : Float)
    (rateBase rateQuote : Rate)
    (spotFees forwardFees : Fees) :
    Option CIPViolation :=
  let expensive := checkFXForwardTooExpensive spotQuote.ask.val forwardBid rateBase rateQuote
  let cheap := checkFXForwardTooCheap spotQuote.bid.val forwardAsk rateBase rateQuote

  if expensive > 0 then
    let spotFee := Fees.totalFee spotFees spotQuote.ask.val (by sorry)
    let fwdFee := Fees.totalFee forwardFees forwardBid (by sorry)
    let netProfit := expensive - spotFee - fwdFee
    let bps := if spotQuote.mid > 0 then (expensive / spotQuote.mid) * 10000 else 0
    if netProfit > 0 then
      some ⟨"UNKNOWN", "forward_expensive", bps, netProfit⟩
    else
      none
  else if cheap > 0 then
    let spotFee := Fees.totalFee spotFees spotQuote.bid.val (by sorry)
    let fwdFee := Fees.totalFee forwardFees forwardAsk (by sorry)
    let netProfit := cheap - spotFee - fwdFee
    let bps := if spotQuote.mid > 0 then (cheap / spotQuote.mid) * 10000 else 0
    if netProfit > 0 then
      some ⟨"UNKNOWN", "forward_cheap", bps, netProfit⟩
    else
      none
  else
    none

-- ============================================================================
-- Uncovered Interest Rate Parity (UIP)
-- ============================================================================

/-- Uncovered Interest Rate Parity (UIP) relates interest rates to expected spot changes.

    E[S_T] / S_0 = (1 + r_quote) / (1 + r_base)

    Or: E[S_T] = S_0 · (1 + r_quote) / (1 + r_base)

    In other words: the expected future spot rate should equal the forward rate
    (assuming risk-neutral expectations).

    Note: This is NOT an arbitrage opportunity (you can't lock in the future spot).
    But systematic violations indicate the forward is not an unbiased predictor
    of future spot, which has implications for currency trading strategies.
-/
theorem uncoveredInterestRateParity
    (spot : Float) (rateBase rateQuote : Rate) :
    ∃ expectedFutureSpot : Float,
    expectedFutureSpot = spot * (1 + rateQuote.val) / (1 + rateBase.val) := by
  -- This is a weaker statement than CIP. It says the expected future spot
  -- should match the forward rate, but this is not an arbitrage relationship
  -- because we can't lock in expectations.
  sorry

-- ============================================================================
-- Real Interest Rate Parity
-- ============================================================================

/-- Real Interest Rate Parity relates real interest rates across currencies.

    r_real_base = r_real_quote

    Where r_real = (1 + r_nominal) / (1 + inflation) - 1

    In the long run, real rates should equalize across currencies
    (purchasing power parity implies this).

    Violations suggest: inflation expectations are inconsistent,
    or one currency offers a risk premium.
-/
def realRate (nominalRate inflation : Float) : Float :=
  (1 + nominalRate) / (1 + inflation) - 1

/-- Check if real rates are dramatically different (suggesting mispricing). -/
def realRateDifference
    (rateBase inflationBase : Float)
    (rateQuote inflationQuote : Float) :
    Float :=
  let realBase := realRate rateBase inflationBase
  let realQuote := realRate rateQuote inflationQuote
  realBase - realQuote

end Finance.Forwards
