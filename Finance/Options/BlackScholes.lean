-- Black-Scholes option pricing model and Greeks
-- Implements the Black-Scholes formula for European options
-- and computes risk sensitivities (delta, gamma, vega, theta, rho)

import Finance.Core
import Finance.Options.European

namespace Finance.Options

-- ============================================================================
-- Normal Distribution Approximation
-- ============================================================================

/-- Approximate cumulative normal distribution function using Abramowitz-Stegun.

    Accurate to about 10^-7 over the full range.
    Used in Black-Scholes formula.
-/
def normalCDF (x : Float) : Float :=
  -- Handle negative values via symmetry: Φ(-x) = 1 - Φ(x)
  let abs_x := x.abs
  -- Coefficients for rational approximation
  let a1 := 0.254829592
  let a2 := -0.284496736
  let a3 := 1.421413741
  let a4 := -1.453152027
  let a5 := 1.061405429
  let p := 0.3275911

  -- t = 1 / (1 + p * |x|)
  let t := 1.0 / (1.0 + p * abs_x)
  let t2 := t * t
  let t3 := t2 * t
  let t4 := t3 * t
  let t5 := t4 * t

  -- Polynomial approximation: exp(-x²/2) * (a1*t + a2*t² + a3*t³ + a4*t⁴ + a5*t⁵)
  let exp_neg_x2_2 := Float.exp (-(abs_x * abs_x) / 2.0)
  let poly := a1 * t + a2 * t2 + a3 * t3 + a4 * t4 + a5 * t5
  let approx := 1.0 - (exp_neg_x2_2 * poly)

  -- Apply symmetry for negative x
  if x < 0 then 1.0 - approx else approx

/-- Normal probability density function. -/
def normalPDF (x : Float) : Float :=
  let pi := 3.14159265358979323846
  let sqrt_2pi := Float.sqrt (2.0 * pi)
  Float.exp (-(x * x) / 2.0) / sqrt_2pi

-- ============================================================================
-- Black-Scholes Option Pricing
-- ============================================================================

/-- Black-Scholes formula inputs. -/
structure BlackScholesInput where
  spot : Float           -- Current stock price (S)
  strike : Float         -- Strike price (K)
  timeToExpiry : Float   -- Time to expiry in years (T)
  riskFreeRate : Float   -- Risk-free rate (r)
  volatility : Float     -- Volatility (σ, annualized)
  dividendYield : Float  -- Dividend yield (q)

/-- Black-Scholes pricing output with intermediate values. -/
structure BlackScholesPrice where
  callPrice : Float      -- European call price
  putPrice : Float       -- European put price
  d1 : Float            -- log(S/K) + (r-q+σ²/2)T / (σ√T)
  d2 : Float            -- d1 - σ√T
  ndOne : Float         -- N(d1)
  ndTwo : Float         -- N(d2)

/-- Compute d1 and d2 parameters for Black-Scholes.

    d1 = [ln(S/K) + (r - q + σ²/2)T] / (σ√T)
    d2 = d1 - σ√T
-/
def computeD1D2 (input : BlackScholesInput) : Float × Float :=
  if input.timeToExpiry ≤ 0 then
    -- At expiry, use intrinsic value
    (0, 0)
  else
    let sigma_sqrt_T := input.volatility * Float.sqrt input.timeToExpiry
    if sigma_sqrt_T.abs < 0.00001 then
      (0, 0)  -- No time/vol, use intrinsic
    else
      let forward := input.spot * Float.exp ((input.riskFreeRate - input.dividendYield) * input.timeToExpiry)
      let d1 := (Float.log (forward / input.strike) +
                 (input.volatility * input.volatility / 2.0) * input.timeToExpiry) / sigma_sqrt_T
      let d2 := d1 - sigma_sqrt_T
      (d1, d2)

/-- Black-Scholes pricing formula for European options.

    Call Price:  C = S·e^(-qT) · N(d1) - K·e^(-rT) · N(d2)
    Put Price:   P = K·e^(-rT) · N(-d2) - S·e^(-qT) · N(-d1)

    Where:
    - S = spot price
    - K = strike price
    - T = time to expiry (years)
    - r = risk-free rate
    - q = dividend yield
    - σ = volatility
    - N(x) = cumulative normal distribution
-/
def blackScholesPrice (input : BlackScholesInput) : BlackScholesPrice :=
  -- Handle boundary cases
  if input.timeToExpiry ≤ 0 then
    -- At expiry: use intrinsic value
    let call_payoff := max 0 (input.spot - input.strike)
    let put_payoff := max 0 (input.strike - input.spot)
    ⟨call_payoff, put_payoff, 0, 0, 0, 0⟩
  else if input.volatility ≤ 0 then
    -- Zero volatility: discounted forward payoff
    let df := Float.exp (-input.riskFreeRate * input.timeToExpiry)
    let div_df := Float.exp (-input.dividendYield * input.timeToExpiry)
    let forward := input.spot * div_df / df
    let call_payoff := max 0 (forward - input.strike)
    let put_payoff := max 0 (input.strike - forward)
    ⟨call_payoff * df, put_payoff * df, 0, 0, 0, 0⟩
  else
    -- Standard Black-Scholes calculation
    let (d1, d2) := computeD1D2 input
    let nd1 := normalCDF d1
    let nd2 := normalCDF d2
    let df := Float.exp (-input.riskFreeRate * input.timeToExpiry)
    let div_df := Float.exp (-input.dividendYield * input.timeToExpiry)

    let call := input.spot * div_df * nd1 - input.strike * df * nd2
    let put := input.strike * df * (1.0 - nd2) - input.spot * div_df * (1.0 - nd1)

    ⟨call, put, d1, d2, nd1, nd2⟩

-- ============================================================================
-- The Greeks: Risk Sensitivities
-- ============================================================================

/-- Greeks result: all five risk sensitivities. -/
structure GreeksResult where
  delta : Float    -- Rate of change w.r.t. spot price
  gamma : Float    -- Rate of change of delta w.r.t. spot price
  vega : Float     -- Rate of change w.r.t. volatility (per 1% change)
  theta : Float    -- Rate of change w.r.t. time (per day)
  rho : Float      -- Rate of change w.r.t. interest rate (per 1% change)

/-- Delta: sensitivity to spot price changes.

    Call Delta: Δ_C = e^(-qT) · N(d1)
    Put Delta:  Δ_P = -e^(-qT) · N(-d1) = e^(-qT) · (N(d1) - 1)

    Range: Call delta ∈ [0,1], Put delta ∈ [-1,0]
-/
def callDelta (input : BlackScholesInput) (pricing : BlackScholesPrice) : Float :=
  Float.exp (-input.dividendYield * input.timeToExpiry) * pricing.ndOne

def putDelta (input : BlackScholesInput) (pricing : BlackScholesPrice) : Float :=
  -Float.exp (-input.dividendYield * input.timeToExpiry) * (1.0 - pricing.ndOne)

/-- Gamma: rate of change of delta (convexity).

    Γ = e^(-qT) · n(d1) / (S · σ · √T)

    Where n(x) is the normal PDF.

    Range: Always positive for both calls and puts.
    Highest when option is at-the-money.
-/
def gamma (input : BlackScholesInput) (pricing : BlackScholesPrice) : Float :=
  if input.timeToExpiry ≤ 0 || input.volatility ≤ 0 then
    0
  else
    let div_df := Float.exp (-input.dividendYield * input.timeToExpiry)
    let npdf_d1 := normalPDF pricing.d1
    let denom := input.spot * input.volatility * Float.sqrt input.timeToExpiry
    if denom.abs < 0.00001 then 0 else div_df * npdf_d1 / denom

/-- Vega: sensitivity to volatility changes.

    ν = S · e^(-qT) · n(d1) · √T

    Typically quoted per 1% change in volatility (i.e., multiply by 0.01).

    Range: Always positive for both calls and puts.
    Highest when option is at-the-money.
-/
def vega (input : BlackScholesInput) (pricing : BlackScholesPrice) : Float :=
  if input.timeToExpiry ≤ 0 then
    0
  else
    let div_df := Float.exp (-input.dividendYield * input.timeToExpiry)
    let npdf_d1 := normalPDF pricing.d1
    let result := input.spot * div_df * npdf_d1 * Float.sqrt input.timeToExpiry
    if result < 0 then 0 else result / 100.0  -- Per 1%

/-- Theta: time decay sensitivity.

    Call Theta: Θ_C = -S·e^(-qT)·n(d1)·σ/(2√T) - r·K·e^(-rT)·N(d2) + q·S·e^(-qT)·N(d1)
    Put Theta:  Θ_P = -S·e^(-qT)·n(d1)·σ/(2√T) + r·K·e^(-rT)·N(-d2) - q·S·e^(-qT)·N(-d1)

    Typically quoted per day (divide by 365).

    Range: Usually negative for long calls/puts (time decay hurts you).
-/
def callTheta (input : BlackScholesInput) (pricing : BlackScholesPrice) : Float :=
  if input.timeToExpiry ≤ 0 || input.volatility ≤ 0 then
    0
  else
    let div_df := Float.exp (-input.dividendYield * input.timeToExpiry)
    let rf_df := Float.exp (-input.riskFreeRate * input.timeToExpiry)
    let npdf_d1 := normalPDF pricing.d1
    let sqrt_t := Float.sqrt input.timeToExpiry

    let decay := -input.spot * div_df * npdf_d1 * input.volatility / (2.0 * sqrt_t)
    let interest := -input.riskFreeRate * input.strike * rf_df * pricing.ndTwo
    let dividend := input.dividendYield * input.spot * div_df * pricing.ndOne

    (decay + interest + dividend) / 365.0  -- Per day

def putTheta (input : BlackScholesInput) (pricing : BlackScholesPrice) : Float :=
  if input.timeToExpiry ≤ 0 || input.volatility ≤ 0 then
    0
  else
    let div_df := Float.exp (-input.dividendYield * input.timeToExpiry)
    let rf_df := Float.exp (-input.riskFreeRate * input.timeToExpiry)
    let npdf_d1 := normalPDF pricing.d1
    let sqrt_t := Float.sqrt input.timeToExpiry

    let decay := -input.spot * div_df * npdf_d1 * input.volatility / (2.0 * sqrt_t)
    let interest := input.riskFreeRate * input.strike * rf_df * (1.0 - pricing.ndTwo)
    let dividend := -input.dividendYield * input.spot * div_df * (1.0 - pricing.ndOne)

    (decay + interest + dividend) / 365.0  -- Per day

/-- Rho: sensitivity to interest rate changes.

    Call Rho: ρ_C = K · T · e^(-rT) · N(d2) (per 1% change in rate)
    Put Rho:  ρ_P = -K · T · e^(-rT) · N(-d2) (per 1% change in rate)

    Range: Positive for calls, negative for puts.
-/
def callRho (input : BlackScholesInput) (pricing : BlackScholesPrice) : Float :=
  let rf_df := Float.exp (-input.riskFreeRate * input.timeToExpiry)
  input.strike * input.timeToExpiry * rf_df * pricing.ndTwo / 100.0  -- Per 1%

def putRho (input : BlackScholesInput) (pricing : BlackScholesPrice) : Float :=
  let rf_df := Float.exp (-input.riskFreeRate * input.timeToExpiry)
  let result := input.strike * input.timeToExpiry * rf_df * (1.0 - pricing.ndTwo) / 100.0
  let negativeResult := -result
  negativeResult

/-- Compute all Greeks at once. -/
def computeGreeks (input : BlackScholesInput) (isCall : Bool) : GreeksResult :=
  let pricing := blackScholesPrice input
  let d := if isCall then callDelta input pricing else putDelta input pricing
  let g := gamma input pricing
  let v := vega input pricing
  let t := if isCall then callTheta input pricing else putTheta input pricing
  let r := if isCall then callRho input pricing else putRho input pricing
  ⟨d, g, v, t, r⟩

-- ============================================================================
-- Black-Scholes Mispricing Detection
-- ============================================================================

/-- Detect if market price deviates significantly from Black-Scholes fair value.

    Used to identify potential mispricing opportunities in the options market.
-/
structure BSMispricingOpportunity where
  symbol : String
  isCall : Bool
  bsPrice : Float      -- Fair value from Black-Scholes
  marketPrice : Float  -- Actual market price
  deviation : Float    -- Market price - BS price (positive = overpriced)
  deviationPercent : Float  -- As percentage
  arbitrageType : String  -- "overpriced" or "underpriced"
  profitOpportunity : Float  -- After fees

/-- Check if call is mispriced relative to Black-Scholes. -/
def checkCallMispricing
    (callSymbol : String)
    (input : BlackScholesInput)
    (marketPrice : Float)
    (fees : Fees) :
    Option BSMispricingOpportunity :=
  let pricing := blackScholesPrice input
  let deviation := marketPrice - pricing.callPrice
  let devPercent := if pricing.callPrice > 0 then
    (deviation / pricing.callPrice) * 100.0 else 0

  -- Arbitrage if deviation exceeds fees
  let fee_cost := Fees.totalFee fees marketPrice (by sorry)
  let netProfit := deviation.abs - fee_cost

  if netProfit > 0.0001 then
    let arbType := if deviation > 0 then "overpriced" else "underpriced"
    some ⟨callSymbol, true, pricing.callPrice, marketPrice, deviation, devPercent, arbType, netProfit⟩
  else
    none

/-- Check if put is mispriced relative to Black-Scholes. -/
def checkPutMispricing
    (putSymbol : String)
    (input : BlackScholesInput)
    (marketPrice : Float)
    (fees : Fees) :
    Option BSMispricingOpportunity :=
  let pricing := blackScholesPrice input
  let deviation := marketPrice - pricing.putPrice
  let devPercent := if pricing.putPrice > 0 then
    (deviation / pricing.putPrice) * 100.0 else 0

  let fee_cost := Fees.totalFee fees marketPrice (by sorry)
  let netProfit := deviation.abs - fee_cost

  if netProfit > 0.0001 then
    let arbType := if deviation > 0 then "overpriced" else "underpriced"
    some ⟨putSymbol, false, pricing.putPrice, marketPrice, deviation, devPercent, arbType, netProfit⟩
  else
    none

-- ============================================================================
-- Implied Volatility Helpers
-- ============================================================================

/-- Compute implied volatility using Newton-Raphson iteration.

    Given a market price, finds the volatility that makes Black-Scholes price equal to it.

    Uses vega as the derivative: σ_new = σ_old - (BS_price - market_price) / vega

    Converges in 3-5 iterations typically.
-/
def impliedVolatility
    (input : BlackScholesInput)
    (targetPrice : Float)
    (isCall : Bool)
    (maxIterations : Nat := 10) :
    Float :=
  let rec iterate (vol : Float) (iteration : Nat) : Float :=
    if iteration ≥ maxIterations then vol
    else
      let current_input := { input with volatility := vol }
      let pricing := blackScholesPrice current_input
      let current_price := if isCall then pricing.callPrice else pricing.putPrice
      let price_error := current_price - targetPrice

      -- Stop if converged
      if price_error.abs < 0.0001 then vol
      else
        let v := vega current_input pricing
        if v.abs < 0.0001 then vol  -- Can't improve further
        else
          let vol_adjustment := price_error / v
          let new_vol := max (vol - vol_adjustment) 0.001  -- Keep vol positive
          iterate new_vol (iteration + 1)

  -- Start with reasonable initial guess
  let initial_vol := 0.2  -- 20% volatility
  iterate initial_vol 0

end Finance.Options
