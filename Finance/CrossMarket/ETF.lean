-- ETF vs underlying basket arbitrage
-- Detects mispricing between ETF and its constituent holdings

import Finance.Core

namespace Finance.CrossMarket

-- ============================================================================
-- ETF vs Basket Definition
-- ============================================================================

/-- An ETF (Exchange Traded Fund) tracks an underlying basket of assets.

    Example: SPY tracks the S&P 500
    - SPY can be traded continuously on the exchange
    - The underlying basket (500 stocks) can be traded

    By no-arbitrage, the ETF price should equal the Net Asset Value (NAV):
    ETF Price ≈ NAV = Σ wᵢ × Sᵢ + carrying costs

    Where:
    - wᵢ: weight of asset i in the index
    - Sᵢ: current price of asset i
    - carrying costs: financing, dividends, management fees
-/
structure ETFBasketComponents where
  etfSymbol : String
  constituents : List (String × Float)  -- (symbol, weight)
  managementFee : Float  -- Annual percentage fee
  basketCash : Float  -- Cash/cash equivalents in basket

-- ============================================================================
-- Net Asset Value (NAV) Definition
-- ============================================================================

/-- The Net Asset Value: the theoretical fair value of the ETF.

    NAV = Σ (weight_i × Price_i) + cash - liabilities - accrued costs

    For example, SPY holding 500 stocks:
    NAV = 0.005 × AAPL_price + 0.003 × MSFT_price + ... + cash

    The ETF should trade very close to NAV. If it deviates, arbitrage opportunities exist.

    - If ETF_price < NAV: buy ETF, sell (short) the basket, lock in profit
    - If ETF_price > NAV: sell ETF, buy the basket, lock in profit
-/
def netAssetValue (constituents : List (String × Float)) (prices : String → Float) : Float :=
  constituents.foldl (fun acc (symbol, weight) =>
    acc + weight * prices symbol
  ) 0

/-- Calculate the implied NAV per share. -/
def navPerShare
    (constituents : List (String × Float))
    (prices : String → Float)
    (sharesOutstanding : Float) :
    Float :=
  if sharesOutstanding > 0 then
    netAssetValue constituents prices / sharesOutstanding
  else
    0

-- ============================================================================
-- ETF Premium/Discount
-- ============================================================================

/-- ETF premium: how much the ETF is trading above NAV.

    Premium = (ETF_Price - NAV) / NAV

    Positive premium: ETF trading above fair value (sell opportunity)
    Negative premium (discount): ETF trading below fair value (buy opportunity)

    Typically, premiums/discounts are small (< 1%) due to active arbitrage.
    Large deviations indicate either:
    1. Market dislocations (illiquidity, market stress)
    2. Temporary pricing inefficiencies
    3. Hidden costs not in the NAV calculation

    Example: During COVID crash, some ETFs traded at 5-10% discounts
    because basket constituents were too illiquid to rebalance quickly.
-/
def etfPremium
    (etfPrice nav : Float) :
    Float :=
  if nav > 0 then
    (etfPrice - nav) / nav
  else
    0

/-- ETF tracking error: standard deviation of premium over time.

    Low tracking error: ETF is efficiently priced
    High tracking error: ETF has significant or variable mispricing
-/
structure TrackingError where
  meanPremium : Float
  volatilityOfPremium : Float  -- Standard deviation
  maxDiscount : Float
  maxPremium : Float
  daysWithLargeMispricing : Nat  -- > 1% premium/discount

-- ============================================================================
-- Create/Redeem Mechanism
-- ============================================================================

/-- The creation/redemption process keeps ETF price close to NAV.

    Creation: If ETF trades at premium:
    - Market maker delivers the exact basket of 100,000 shares to ETF provider
    - Receives 100,000 ETF shares
    - Sells those shares at the premium
    - Locks in arbitrage profit

    Redemption: If ETF trades at discount:
    - Market maker buys 100,000 ETF shares at discount price
    - Delivers them to ETF provider
    - Receives the underlying basket
    - Sells the basket at higher NAV price
    - Locks in arbitrage profit

    The arbitrage is self-limiting: as market makers create/redeem,
    ETF price moves toward NAV, closing the opportunity.

    But if the basket is hard to trade (illiquid), arbitrage might not work,
    and the premium/discount can persist.
-/
structure CreationRedemption where
  basketSize : Nat  -- Number of shares per creation unit (e.g., 100,000)
  creationFee : Float  -- Fee to create new ETF shares from basket
  redemptionFee : Float  -- Fee to redeem ETF shares for basket

def creationArbitrageProfit
    (etfPrice nav : Float)
    (fees creationFee : Float) :
    Float :=
  if etfPrice > nav then
    etfPrice - nav - fees - creationFee
  else
    0

def redemptionArbitrageProfit
    (etfPrice nav : Float)
    (fees redemptionFee : Float) :
    Float :=
  if etfPrice < nav then
    nav - etfPrice - fees - redemptionFee
  else
    0

-- ============================================================================
-- ETF Basket Mismatch
-- ============================================================================

/-- Index reconstruction effects: the ETF basket might not perfectly match
    the index it tracks.

    Reasons:
    1. New stocks added to index slowly (don't rebalance immediately)
    2. Delisted stocks (ETF holds but can't sell)
    3. Sector weighting differences
    4. Liquidity constraints (can't hold microcaps)

    Result: NAV calculation might not match the actual index value.

    Example: Russell 2000 index updates in June cause temporary mismatches.
    Small-cap stocks enter/leave the index, but ETFs take time to rebalance.
    This creates profitable arbitrage for a few days.
-/
structure BasketMismatch where
  missingConstituents : List String  -- Stocks in index but not in ETF
  excessConstituents : List String   -- Stocks in ETF but not in index
  weightingDifferences : Float  -- Sum of |wETF - wIndex| for each stock
  estimatedMispricing : Float  -- How much of NAV difference this explains

-- ============================================================================
-- ETF Mispricing Detection
-- ============================================================================

/-- Result of analyzing an ETF for arbitrage. -/
structure ETFArbitrageOpportunity where
  etfSymbol : String
  currentPrice : Float
  navValue : Float
  premium : Float  -- As a percentage
  arbitrageType : String  -- "creation" or "redemption"
  profitPerShare : Float
  profitAsPercent : Float
  recommendedAction : String

/-- Analyze an ETF for creation/redemption arbitrage. -/
def analyzeETFArbitrage
    (etfSymbol : String)
    (etfPrice nav : Float)
    (creationFees redemptionFees : Float)
    (minProfitThreshold : Float) :
    Option ETFArbitrageOpportunity :=
  let premium := etfPremium etfPrice nav
  let creationProfit := creationArbitrageProfit etfPrice nav creationFees creationFees
  let redemptionProfit := redemptionArbitrageProfit etfPrice nav redemptionFees redemptionFees

  if creationProfit > minProfitThreshold then
    let pct := (creationProfit / nav) * 100
    some ⟨etfSymbol, etfPrice, nav, premium * 100, "creation", creationProfit, pct, "Sell ETF, create from basket"⟩
  else if redemptionProfit > minProfitThreshold then
    let pct := (redemptionProfit / nav) * 100
    some ⟨etfSymbol, etfPrice, nav, premium * 100, "redemption", redemptionProfit, pct, "Buy ETF, redeem for basket"⟩
  else
    none

-- ============================================================================
-- Multiple ETF Comparison
-- ============================================================================

/-- When multiple ETFs track the same index (e.g., SPY, IVV, VOO all track S&P 500),
    they should all trade near the same NAV.

    If two ETFs have different premiums, you can:
    - Buy the discounted one
    - Sell the premium one
    - Both should track the same thing, so you've locked in profit

    This is simpler than creation/redemption (no need to touch the actual basket).
-/
def comparativeETFArbitrage
    (etf1Symbol etf2Symbol : String)
    (etf1Price etf1NAV etf2Price etf2NAV : Float) :
    Option (String × Float) :=  -- (best strategy, profit)
  let premium1 := etfPremium etf1Price etf1NAV
  let premium2 := etfPremium etf2Price etf2NAV
  let spread := premium1 - premium2

  if spread > 0 then
    -- ETF1 has higher premium, sell it and buy ETF2
    some ⟨"Sell " ++ etf1Symbol ++ ", Buy " ++ etf2Symbol, spread⟩
  else if spread < 0 then
    -- ETF2 has higher premium, sell it and buy ETF1
    some ⟨"Sell " ++ etf2Symbol ++ ", Buy " ++ etf1Symbol, -spread⟩
  else
    none

end Finance.CrossMarket
