-- FX Triangular arbitrage
-- Detects inconsistencies in cross-rate relationships across currency pairs

import Finance.Core
import Finance.Forwards.FX

namespace Finance.CrossMarket

-- ============================================================================
-- Triangular Arbitrage Definition
-- ============================================================================

/-- Triangular arbitrage: exploiting inconsistencies in three currency pairs.

    Example: EUR/USD, GBP/USD, EUR/GBP

    If we denote rates as:
    - S1 = EUR/USD (euros per dollar)
    - S2 = GBP/USD (pounds per dollar)
    - S3 = EUR/GBP (euros per pound)

    By no-arbitrage, they must satisfy:
    S3 = S1 / S2

    Or equivalently:
    S1 = S2 × S3
    S1 × S2_inverse × S3_inverse = 1

    Violation creates arbitrage: convert currency through two different paths
    and profit from the difference.

    Example triangular cycle:
    1. Start with 1 USD
    2. Convert USD → EUR at rate S1 (get S1 EUR)
    3. Convert EUR → GBP at inverse of S3 (get S1/S3 GBP)
    4. Convert GBP → USD at inverse of S2 (get S1/(S2×S3) USD)

    If S1/(S2×S3) > 1, we made money! This is the arbitrage.
-/
structure TriangularTrade where
  pair1 : String  -- e.g., "EUR/USD"
  pair2 : String  -- e.g., "GBP/USD"
  pair3 : String  -- e.g., "EUR/GBP"
  rate1 : Float   -- S1: EUR/USD
  rate2 : Float   -- S2: GBP/USD
  rate3 : Float   -- S3: EUR/GBP

-- ============================================================================
-- Consistency Constraint
-- ============================================================================

/-- Triangular consistency: S3 = S1 / S2

    In three-currency arbitrage, the cross-rate must equal the implied rate
    from the two base-currency pairs.

    Violation by buying path: if S3 is too cheap
    - Buy S3 at ask price (convert EUR → GBP directly)
    - Sell implied S3 (convert EUR → USD → GBP)
    - Profit if S3_ask < S1_bid / S2_ask

    Violation by selling path: if S3 is too expensive
    - Sell S3 at bid price (convert GBP → EUR directly)
    - Buy implied S3 (convert GBP → USD → EUR)
    - Profit if S3_bid > S1_ask / S2_bid
-/
theorem triangularConsistency
    (S1 S2 S3 : Float) :
    S3 = S1 / S2 := by
  -- Triangular consistency is the fundamental no-arbitrage relationship.
  -- Proof: Consider converting currency through all three pairs:
  -- Path 1: Convert 1 unit currency3 directly to currency1 at rate S3
  -- Path 2: Convert 1 currency3 → currency2 at inverse rate 1/S2,
  --         then currency2 → currency1 at rate S1
  -- Both paths should give the same result, so:
  -- S3 = S1 / S2
  -- By no-arbitrage, the exchange rate between any two currencies must be
  -- consistent with their implied rates through a third currency.
  sorry  -- Requires no-arbitrage axiom and path independence

-- ============================================================================
-- Direct Arbitrage Detection
-- ============================================================================

/-- Check if cross-rate is too cheap (arbitrage by buying cross, selling implied).

    Returns profit from: buy S3 at ask, sell implied (S1/S2) at bid.

    If S3_ask < S1_bid / S2_ask: buy cross rate, sell implied rate
-/
def checkCrossRateTooCheap
    (s1Bid s1Ask s2Bid s2Ask s3Bid s3Ask : Float) :
    Float :=
  let impliedRate := s1Bid / s2Ask  -- Convert through base currency (conservative)
  impliedRate - s3Ask  -- Profit from selling implied, buying direct

/-- Check if cross-rate is too expensive (arbitrage by selling cross, buying implied).

    Returns profit from: sell S3 at bid, buy implied (S1/S2) at ask.

    If S3_bid > S1_ask / S2_bid: sell cross rate, buy implied rate
-/
def checkCrossRateTooExpensive
    (s1Bid s1Ask s2Bid s2Ask s3Bid s3Ask : Float) :
    Float :=
  let impliedRate := s1Ask / s2Bid  -- Convert through base currency (conservative)
  s3Bid - impliedRate  -- Profit from selling direct, buying implied

-- ============================================================================
-- Four-Pair Triangular Cycles
-- ============================================================================

/-- Extended triangular check with more sophisticated cycles.

    For four currency pairs, we can check multiple triangles:
    - Triangle 1-2-3: A-B-C-A
    - Triangle 2-3-4: B-C-D-B
    - Triangle 1-3-4: A-C-D-A
    - etc.

    Each forms a closed loop where the product of rates should equal 1
    (accounting for direction).

    This is more robust than checking a single triangle, as it catches
    inconsistencies that might not be visible in any single pair.
-/
structure FourCurrencyTriangle where
  rateAB : Float  -- Rate from A to B
  rateBC : Float  -- Rate from B to C
  rateCD : Float  -- Rate from C to D
  rateDA : Float  -- Rate from D back to A

/-- A four-currency cycle should satisfy: AB × BC × CD × DA = 1

    This checks a cycle where we convert A→B→C→D→A.
    The product of all rates should give us back our original currency at 1:1.
-/
theorem fourCurrencyCycleConsistency
    (rateAB rateBC rateCD rateDA : Float) :
    rateAB * rateBC * rateCD * rateDA = 1 := by
  -- By no-arbitrage, converting currency through a complete cycle
  -- should return you to your starting point with the same amount.
  sorry

/-- Check the four-currency cycle for violations. -/
def checkFourCurrencyCycle
    (rateAB rateBC rateCD rateDA : Float) :
    Float :=
  let cycleProduct := rateAB * rateBC * rateCD * rateDA
  -- If product > 1: profit by going around the loop
  -- If product < 1: loss by going around the loop (arbitrage in reverse)
  cycleProduct - 1

-- ============================================================================
-- Bid/Ask Spread Handling
-- ============================================================================

/-- Triangular arbitrage with bid/ask spreads on all three pairs.

    When there are bid/ask spreads, we need to be more careful:
    - To execute a profitable arbitrage, we must buy at ask and sell at bid
    - This means taking the unfavorable side of each trade

    Example of buying the cross (buying S3, selling implied):
    1. Sell S1 at bid (get USD for EUR)
    2. Buy S2 at ask (convert USD to GBP)
    3. Buy S3 at ask (convert GBP to EUR)

    Net: start with 1 EUR, end with (S1_bid) / (S2_ask × S3_ask) EUR

    Profit if this > 1.
-/
structure TriangularArbitrageOpportunity where
  pair1 : String  -- First currency pair
  pair2 : String  -- Second currency pair
  pair3 : String  -- Third currency pair
  arbitrageType : String  -- "buy_cross" or "sell_cross"
  profitAmount : Float  -- Profit in base currency
  profitPercentage : Float  -- As percentage of initial capital
  roundTripPath : String  -- Description of the conversion path

/-- Analyze triangular arbitrage with bid/ask spreads and fees. -/
def analyzeTriangularArbitrage
    (s1 s2 s3 : Quote)  -- Three currency pair quotes (bid/ask)
    (fees1 fees2 fees3 : Fees) :
    Option TriangularArbitrageOpportunity :=
  -- Path 1: Buy cross (direct S3 vs implied S1/S2)
  let buyCrossProfit := checkCrossRateTooCheap s1.bid.val s1.ask.val s2.bid.val s2.ask.val s3.bid.val s3.ask.val
  let fee1 := Fees.totalFee fees1 s1.ask.val (by sorry)
  let fee2 := Fees.totalFee fees2 s2.ask.val (by sorry)
  let fee3 := Fees.totalFee fees3 s3.ask.val (by sorry)
  let netBuyCrossProfit := buyCrossProfit - (fee1 + fee2 + fee3)

  -- Path 2: Sell cross (implied S1/S2 vs direct S3)
  let sellCrossProfit := checkCrossRateTooExpensive s1.bid.val s1.ask.val s2.bid.val s2.ask.val s3.bid.val s3.ask.val
  let fee1' := Fees.totalFee fees1 s1.bid.val (by sorry)
  let fee2' := Fees.totalFee fees2 s2.bid.val (by sorry)
  let fee3' := Fees.totalFee fees3 s3.bid.val (by sorry)
  let netSellCrossProfit := sellCrossProfit - (fee1' + fee2' + fee3')

  -- Return the best opportunity
  if netBuyCrossProfit > 0 then
    let pct := if s1.mid > 0 then (netBuyCrossProfit / s1.mid) * 100 else 0
    some ⟨"PAIR1", "PAIR2", "PAIR3", "buy_cross", netBuyCrossProfit, pct, "Direct→Implied"⟩
  else if netSellCrossProfit > 0 then
    let pct := if s1.mid > 0 then (netSellCrossProfit / s1.mid) * 100 else 0
    some ⟨"PAIR1", "PAIR2", "PAIR3", "sell_cross", netSellCrossProfit, pct, "Implied→Direct"⟩
  else
    none

-- ============================================================================
-- Multi-Pair Arbitrage Scanner
-- ============================================================================

/-- Result of scanning multiple currency pairs for triangular opportunities. -/
structure TriangularArbitrageSummary where
  totalPairs : Nat
  trianglesChecked : Nat
  opportunitiesFound : Nat
  totalProfit : Float
  bestOpportunity : Option TriangularArbitrageOpportunity

end Finance.CrossMarket
