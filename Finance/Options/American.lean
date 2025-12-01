-- American options with early exercise and binomial tree pricing
-- Allows exercise at any time before expiry (unlike European options)

import Finance.Core
import Finance.Options.European
import Finance.Options.BlackScholes

namespace Finance.Options

-- ============================================================================
-- American Option Fundamentals
-- ============================================================================

/-- An American option (can be exercised at any time before expiry). -/
structure AmericanOption where
  strike : Float
  timeToExpiry : Float
  dividendSchedule : List (Float × Float)  -- (ex-dividend date, dividend amount)

/-- Binomial tree node: holds option value at a given price level and time. -/
structure BinomialNode where
  price : Float         -- Stock price at this node
  europeanValue : Float -- European option value (no early exercise)
  americanValue : Float -- American option value (with early exercise)
  exerciseValue : Float -- Intrinsic value (immediate exercise payoff)

/-- Parameters for binomial tree construction. -/
structure BinomialParams where
  volatility : Float
  riskFreeRate : Float
  dividendYield : Float
  timeToExpiry : Float
  stepsPerYear : Nat := 100  -- Number of steps in tree

-- ============================================================================
-- Binomial Tree Construction
-- ============================================================================

/-- Compute up and down multipliers for binomial tree.

    Standard binomial model:
    - u = e^(σ√dt)  (up multiplier)
    - d = 1/u        (down multiplier)
    - p = (e^((r-q)dt) - d) / (u - d)  (risk-neutral probability)

    Where dt = T/N (time step size)
-/
def computeUDMultipliers (params : BinomialParams) :
    Float × Float × Float :=  -- (u, d, prob)
  if params.stepsPerYear = 0 then (1.0, 1.0, 0.5)
  else
    let dt := params.timeToExpiry / params.stepsPerYear.toFloat
    let u := Float.exp (params.volatility * Float.sqrt dt)
    let d := 1.0 / u
    let drift := Float.exp ((params.riskFreeRate - params.dividendYield) * dt)
    let prob := (drift - d) / (u - d)
    (u, d, prob)

/-- Build terminal payoffs (leaf nodes) of binomial tree.

    At expiration, option value = intrinsic value.
    For a call: max(S - K, 0)
    For a put: max(K - S, 0)
-/
def terminalPayoffs (strike : Float) (spotPrice : Float) (u d : Float) (steps : Nat)
    (isCall : Bool) :
    Array Float :=
  let mut payoffs := Array.mkEmpty (steps + 1)
  for j in [0 : steps + 1] do
    let upMoves := j
    let downMoves := steps - j
    let finalPrice := spotPrice * (u ^ upMoves) * (d ^ downMoves)
    let intrinsic := if isCall then
      max 0 (finalPrice - strike)
    else
      max 0 (strike - finalPrice)
    payoffs := payoffs.push intrinsic
  payoffs

/-- Backward induction: compute American option value with early exercise.

    For each node, the value is:
    max(intrinsic_value, discounted_expected_future_value)

    Where discounted_expected_future_value =
      e^(-r*dt) * (p * value_up + (1-p) * value_down)
-/
def backwardInduction
    (strikePrice : Float)
    (spotPrice : Float)
    (params : BinomialParams)
    (isCall : Bool) :
    Float :=
  let (u, d, p) := computeUDMultipliers params

  if params.stepsPerYear = 0 then
    -- Degenerate case: use intrinsic value
    if isCall then max 0 (spotPrice - strikePrice)
    else max 0 (strikePrice - spotPrice)
  else
    let steps := params.stepsPerYear
    let dt := params.timeToExpiry / steps.toFloat
    let discount := Float.exp (-params.riskFreeRate * dt)

    -- Initialize with terminal payoffs
    let mut values := terminalPayoffs strikePrice spotPrice u d steps isCall

    -- Backward induction through tree
    let mut step := steps - 1
    while step > 0 do
      let mut nextValues := Array.mkEmpty (step + 1)
      for j in [0 : step + 1] do
        let upPrice := spotPrice * (u ^ j) * (d ^ (step - j))

        -- European continuation value
        let upValue := values.get! (j + 1)
        let downValue := values.get! j
        let continuationValue := discount * (p * upValue + (1.0 - p) * downValue)

        -- Intrinsic value
        let intrinsic := if isCall then
          max 0 (upPrice - strikePrice)
        else
          max 0 (strikePrice - upPrice)

        -- American: take max of exercise and continuation
        let americanValue := max intrinsic continuationValue
        nextValues := nextValues.push americanValue
      values := nextValues
      step := step - 1

    values.get! 0  -- Return root node value

-- ============================================================================
-- American vs European Comparison
-- ============================================================================

/-- Value of early exercise opportunity (American - European).

    Should be positive for calls on dividend stocks and all puts.
-/
def earlyExerciseValue
    (spotPrice : Float)
    (strikePrice : Float)
    (params : BinomialParams)
    (isCall : Bool) :
    Float :=
  let americanValue := backwardInduction strikePrice spotPrice params isCall

  let europeanInput : BlackScholesInput := {
    spot := spotPrice
    strike := strikePrice
    timeToExpiry := params.timeToExpiry
    riskFreeRate := params.riskFreeRate
    volatility := params.volatility
    dividendYield := params.dividendYield
  }
  let europeanPricing := blackScholesPrice europeanInput
  let europeanValue := if isCall then europeanPricing.callPrice else europeanPricing.putPrice

  americanValue - europeanValue

/-- Check if American option is underpriced relative to lower bound.

    American call value ≥ max(European call value, intrinsic value)
    American put value ≥ max(European put value, intrinsic value)
-/
def checkAmericanUnderpriced
    (optionSymbol : String)
    (spotPrice : Float)
    (strikePrice : Float)
    (marketPrice : Float)
    (params : BinomialParams)
    (isCall : Bool)
    (fees : Fees) :
    Option (String × Float) :=
  let intrinsic := if isCall then
    max 0 (spotPrice - strikePrice)
  else
    max 0 (strikePrice - spotPrice)

  let americanValue := backwardInduction strikePrice spotPrice params isCall
  let lowerBound := max intrinsic americanValue
  let underpriceAmount := lowerBound - marketPrice

  if underpriceAmount > 0.0001 then
    let fee_cost := Fees.totalFee fees marketPrice (by sorry)
    let netProfit := underpriceAmount - fee_cost
    if netProfit > 0 then
      some (optionSymbol, netProfit)
    else
      none
  else
    none

/-- Check if American option is overpriced.

    American option ≤ spot (for call) or strike (for put) at any time.
-/
def checkAmericanOverpriced
    (optionSymbol : String)
    (spotPrice : Float)
    (strikePrice : Float)
    (marketPrice : Float)
    (isCall : Bool)
    (fees : Fees) :
    Option (String × Float) :=
  let upperBound := if isCall then spotPrice else strikePrice
  let overpricingAmount := marketPrice - upperBound

  if overpricingAmount > 0.0001 then
    let fee_cost := Fees.totalFee fees marketPrice (by sorry)
    let netProfit := overpricingAmount - fee_cost
    if netProfit > 0 then
      some (optionSymbol, netProfit)
    else
      none
  else
    none

-- ============================================================================
-- Early Exercise Analysis
-- ============================================================================

/-- Analyze whether early exercise is optimal at a given price.

    For calls: early exercise optimal when dividend yield is high
              and we're deep in-the-money.

    For puts: early exercise optimal when deeply in-the-money
             and rate is high (prefer cash now).
-/
def shouldExerciseEarly
    (spotPrice : Float)
    (strikePrice : Float)
    (timeToExpiry : Float)
    (params : BinomialParams)
    (isCall : Bool) :
    Bool :=
  if timeToExpiry ≤ 0.001 then
    -- Near expiry: always exercise if in-the-money
    if isCall then spotPrice > strikePrice else strikePrice > spotPrice
  else
    let intrinsic := if isCall then
      max 0 (spotPrice - strikePrice)
    else
      max 0 (strikePrice - spotPrice)

    if intrinsic ≤ 0 then
      false  -- Not in-the-money, don't exercise
    else
      -- For calls: early exercise if we can invest the strike at r for rest of time
      -- vs waiting for stock appreciation
      if isCall then
        let investmentValue := strikePrice * Float.exp (params.riskFreeRate * timeToExpiry)
        spotPrice > investmentValue * 0.95  -- Some margin for uncertainty
      else
        -- For puts: early exercise if intrinsic > European value
        let remainingTime := BinomialParams.mk params.volatility params.riskFreeRate
          params.dividendYield timeToExpiry
        let europeanVal := backwardInduction strikePrice spotPrice remainingTime false
        intrinsic > europeanVal * 0.95

-- ============================================================================
-- Dividend Impact on Early Exercise
-- ============================================================================

/-- Analyze dividend impact on early exercise decision.

    Dividends reduce call value (you miss them if you don't own stock).
    Dividends increase put value (company losing value to shareholders).

    For calls: early exercise might be optimal right before ex-dividend.
-/
def earlyExerciseBeforeDividend
    (spotPrice : Float)
    (strikePrice : Float)
    (exDividendDate : Float)  -- Time until ex-dividend
    (dividendAmount : Float)
    (params : BinomialParams) :
    Float :=
  -- Value of exercising now vs waiting for dividend
  let exerciseNow := spotPrice - strikePrice

  -- If we wait for dividend, we get dividendAmount but stock might fall
  -- Conservative estimate: future value = current value minus dividend risk
  let timeAfterDividend := params.timeToExpiry - exDividendDate
  if timeAfterDividend <= 0 then
    exerciseNow  -- Already passed ex-dividend, exercise if profitable
  else
    let futurePayoff := spotPrice - dividendAmount - strikePrice
    if exerciseNow > futurePayoff then exerciseNow else futurePayoff

-- ============================================================================
-- Result Structures
-- ============================================================================

/-- Result of American option analysis. -/
structure AmericanOptionAnalysis where
  callValue : Float
  putValue : Float
  callEarlyExerciseValue : Float
  putEarlyExerciseValue : Float
  callIsEarlyExerciseOptimal : Bool
  putIsEarlyExerciseOptimal : Bool
  callMispricing : Option (String × Float)
  putMispricing : Option (String × Float)

end Finance.Options
