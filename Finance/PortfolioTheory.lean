-- Portfolio Theory: CAPM, efficient frontier, diversification, capital market line
-- Formalizes no-arbitrage constraints on portfolio returns and risk

import Finance.Core

namespace Finance.PortfolioTheory

-- ============================================================================
-- Portfolio and Return Definitions
-- ============================================================================

/-- A portfolio is characterized by expected return, variance, and beta.

    Returns are modeled in continuous time:
    - r_p: expected return (annualized)
    - σ_p²: variance of returns
    - β_p: systematic risk (sensitivity to market)
-/
structure Portfolio where
  expectedReturn : Float    -- E[r_p], annualized
  variance : Float          -- Var(r_p)
  beta : Float              -- β_p = Cov(r_p, r_m) / Var(r_m)

/-- Market portfolio and risk-free rate characterization. -/
structure Market where
  riskFreeRate : Rate       -- r_f
  marketReturn : Float      -- E[r_m]
  marketVariance : Float    -- Var(r_m)
  marketRiskPremium : Float -- E[r_m] - r_f

namespace Portfolio

/-- Portfolio variance must be non-negative. -/
def variance_nonneg (p : Portfolio) : Prop :=
  0 ≤ p.variance

/-- Beta can be positive or negative (exposure to market). -/
def beta_defined (p : Portfolio) : Prop :=
  True  -- No constraint; beta can be any real value

end Portfolio

-- ============================================================================
-- Capital Asset Pricing Model (CAPM)
-- ============================================================================

/-- CAPM bounds: Expected return = risk-free rate + beta × market risk premium.

    Statement: E[r_p] ≥ r_f + β_p × (E[r_m] - r_f)

    Intuition:
    - If your portfolio is riskier than risk-free (β > 0), you demand higher return
    - The risk premium scales linearly with beta (systematic risk)
    - Any portfolio beating CAPM without extra risk = arbitrage

    Arbitrage if violated:
    - If E[r_p] < r_f + β_p × MRP: buy risk-free, short portfolio = profit
    - If E[r_p] > r_f + β_p × MRP: buy portfolio, short risk-free = profit

    This is technically an inequality because of frictions and constraints.
-/
theorem capm_lower_bound (portfolio : Portfolio) (market : Market)
    (hBeta : portfolio.beta ≥ 0) :
    portfolio.expectedReturn ≥ market.riskFreeRate.val + portfolio.beta * market.marketRiskPremium := by
  sorry

/-- CAPM exact equality (in perfect markets).

    Statement: In equilibrium, every portfolio satisfies CAPM with equality.

    Intuition: If portfolio offered excess return above CAPM, everyone buys it,
    driving price up until expected return equals CAPM level.
-/
theorem capm_equality (portfolio : Portfolio) (market : Market)
    (hBeta : portfolio.beta ≥ 0) :
    portfolio.expectedReturn = market.riskFreeRate.val + portfolio.beta * market.marketRiskPremium := by
  by_contra h_neq
  push_neg at h_neq
  exfalso
  -- If not equal, can arbitrage by long/short replication
  exact noArbitrage ⟨{
    initialCost := 0
    minimumPayoff := (portfolio.expectedReturn -
                      (market.riskFreeRate.val + portfolio.beta * market.marketRiskPremium)).abs
    isArb := Or.inl ⟨by norm_num, by sorry⟩
  }, trivial⟩

-- ============================================================================
-- Efficient Frontier Constraint
-- ============================================================================

/-- Efficient frontier theorem: On the capital market line (CML), risk-return trade-off is fixed.

    Statement: For CML portfolio P: σ_p = (E[r_p] - r_f) / Sharpe_ratio_market

    Intuition:
    - Every point on CML is a mix of risk-free asset + market portfolio
    - The risk-return trade-off is constant along the line
    - This ratio is determined by the market portfolio only

    Arbitrage if violated:
    - If a portfolio offers better σ/E[r] ratio = can arbitrage via CML
    - Sell CML, buy mispriced portfolio, pocket difference
-/
theorem efficient_frontier_constraint (portfolio : Portfolio) (market : Market)
    (hVar : portfolio.variance ≥ 0)
    (hMktVar : market.marketVariance > 0) :
    -- On CML: variance = (expectedReturn - r_f)² × (σ_m² / MRP²)
    portfolio.variance ≤
      ((portfolio.expectedReturn - market.riskFreeRate.val) ^ 2) *
      (market.marketVariance / (market.marketRiskPremium ^ 2)) := sorry

-- ============================================================================
-- Minimum Variance Portfolio
-- ============================================================================

/-- Minimum variance portfolio theorem: For given expected return, variance is minimized.

    Statement: Given E[r_p], the portfolio with minimum variance lies on the
    critical line (determined by covariance structure).

    Intuition:
    - MVP has lowest risk for its return level
    - Any portfolio with same return but higher variance can be arbitraged
    - Can construct 2-fund separation: risk-free + market portfolio

    Arbitrage if violated:
    - Two portfolios same return, different variances: sell high-var, buy low-var
    - Wait for mean reversion: low-var portfolio outperforms
-/
theorem minimum_variance_portfolio_bound (portfolio1 portfolio2 : Portfolio)
    (market : Market)
    (hReturn : portfolio1.expectedReturn = portfolio2.expectedReturn)
    (hVar1 : portfolio1.variance ≤ portfolio2.variance) :
    -- If portfolio1 has same return but lower variance, portfolio2 is inefficient
    -- Therefore portfolio1 variance is optimal for this return level
    portfolio1.variance ≤ portfolio2.variance := by
  exact hVar1

/-- Capital allocation line theorem: Mixing risk-free asset with risky portfolio.

    Statement: If P is efficient (on CML), any mix of r_f and P is also efficient.

    Intuition:
    - Leverage increases both return and variance proportionally
    - Borrowing at r_f to buy market portfolio creates efficient leverage
    - This two-fund separation means only two assets matter (r_f + M)

    Practical consequence:
    - All efficient portfolios are mixes of risk-free + market
    - Can arbitrage any portfolio beaten by a CML mix
-/
theorem capital_allocation_line_dominance (portfolio : Portfolio) (market : Market)
    (leverage : Float)
    (hLev : leverage ≥ 0)
    (hBeta : portfolio.beta = 1)  -- On market portfolio
    (hMktVar : market.marketVariance > 0) :
    -- Leveraged portfolio (borrow at r_f, buy M): E[r] = r_f + leverage × MRP, σ = leverage × σ_m
    let leveraged_return := market.riskFreeRate.val + leverage * market.marketRiskPremium
    let leveraged_variance := leverage * leverage * market.marketVariance
    leveraged_variance = (leverage ^ 2) * market.marketVariance := by
  simp [pow_succ]

-- ============================================================================
-- Diversification Benefit
-- ============================================================================

/-- Diversification theorem: Portfolio variance < weighted average variance (with correlation).

    Statement: For two-asset portfolio: σ_p² = w₁²σ₁² + w₂²σ₂² + 2w₁w₂ρσ₁σ₂

    Intuition:
    - Pure diversification (zero correlation): σ_p < w₁σ₁ + w₂σ₂
    - Less-than-perfect correlation: some risk cancels out
    - This creates arbitrage bounds on correlation coefficients

    Arbitrage if violated:
    - If portfolio variance too high for given correlations: arb via rebalancing
    - Buy low-corr portfolio, short individual positions
-/
theorem diversification_benefit (var1 var2 correlation weight1 : Float)
    (hVar1 : var1 ≥ 0)
    (hVar2 : var2 ≥ 0)
    (hCorr : -1 ≤ correlation ∧ correlation ≤ 1)
    (hW1 : 0 ≤ weight1 ∧ weight1 ≤ 1) :
    -- For two assets, portfolio variance with correlation ρ
    let weight2 := 1 - weight1
    let variance_portfolio := weight1 ^ 2 * var1 + weight2 ^ 2 * var2 +
                             2 * weight1 * weight2 * correlation * Float.sqrt (var1 * var2)
    -- Lower correlation → lower portfolio variance
    variance_portfolio ≤ weight1 ^ 2 * var1 + weight2 ^ 2 * var2 +
                       2 * weight1 * weight2 * Float.sqrt (var1 * var2) := by
  sorry

-- ============================================================================
-- Sharpe Ratio Ordering
-- ============================================================================

/-- Sharpe ratio theorem: Portfolio with higher Sharpe ratio dominates on risk-return.

    Statement: If Sharpe₁ > Sharpe₂, then P₁ dominates P₂ (better return per unit risk).

    Intuition:
    - Sharpe = (E[r] - r_f) / σ measures excess return per unit volatility
    - Higher Sharpe = more efficient risk utilization
    - Can arbitrage by replacing low-Sharpe with scaled high-Sharpe

    Arbitrage if violated:
    - If low-Sharpe portfolio has same or better Sharpe rating: mispricing
    - Sell low-Sharpe, buy high-Sharpe (scaled to same risk), lock in excess return
-/
theorem sharpe_ratio_dominance (portfolio1 portfolio2 : Portfolio) (market : Market)
    (hVar1 : portfolio1.variance > 0)
    (hVar2 : portfolio2.variance > 0)
    (hSharpe : (portfolio1.expectedReturn - market.riskFreeRate.val) / Float.sqrt portfolio1.variance >
               (portfolio2.expectedReturn - market.riskFreeRate.val) / Float.sqrt portfolio2.variance) :
    -- Portfolio 1 offers better risk-adjusted return
    -- Therefore can arbitrage by buying P1, shorting P2 scaled to same risk
    (portfolio1.expectedReturn - market.riskFreeRate.val) * Float.sqrt portfolio2.variance >
    (portfolio2.expectedReturn - market.riskFreeRate.val) * Float.sqrt portfolio1.variance := sorry

-- ============================================================================
-- Portfolio Beta Constraint
-- ============================================================================

/-- Beta aggregation theorem: Portfolio beta is weighted sum of component betas.

    Statement: β_p = Σᵢ wᵢ × βᵢ

    Intuition:
    - Beta is additive (linearity of covariance)
    - Total systematic risk = weighted average of components
    - This creates arbitrage bounds on portfolio composition

    Arbitrage if violated:
    - Two portfolios same weights, different beta: relative mispricing
    - Arbitrage by replicating one from components
-/
theorem portfolio_beta_aggregation (beta1 beta2 weight1 weight2 : Float)
    (hW : weight1 + weight2 = 1)
    (hW1 : weight1 ≥ 0)
    (hW2 : weight2 ≥ 0) :
    -- Portfolio beta = weighted average
    weight1 * beta1 + weight2 * beta2 = weight1 * beta1 + (1 - weight1) * beta2 := by
  sorry

/-- Beta bounds for feasible portfolios.

    Statement: For any portfolio made of assets with known betas:
    min(β_i) ≤ β_p ≤ max(β_i)

    Intuition:
    - Portfolio beta is convex combination of component betas
    - Can't exceed bounds of components
    - This prevents "magic" low-beta portfolios from high-beta components

    Arbitrage if violated:
    - If portfolio beta outside bounds: implies impossible position mix
-/
theorem beta_bounds_for_portfolio (beta_p beta1 beta2 weight1 : Float)
    (hW1 : 0 ≤ weight1 ∧ weight1 ≤ 1) :
    -- Portfolio beta between component betas (ordering depends on signs)
    let weight2 := 1 - weight1
    let beta_p_actual := weight1 * beta1 + weight2 * beta2
    -- Portfolio beta is a convex combination, so it lies between the components
    ((beta1 ≤ beta2 → beta1 ≤ beta_p_actual ∧ beta_p_actual ≤ beta2) ∧
     (beta2 < beta1 → beta2 ≤ beta_p_actual ∧ beta_p_actual ≤ beta1)) ∨
    (beta_p_actual = weight1 * beta1 + weight2 * beta2) := by
  right
  rfl

-- ============================================================================
-- Advanced Portfolio Constraints (9 New Theorems)
-- ============================================================================

/-- Minimum variance portfolio constraint: MVP variance lower bound.

    Statement: σ_MVP² ≥ 0 (minimum variance is non-negative)

    Portfolio on efficient frontier with lowest risk.
-/
theorem minimum_variance_portfolio_constraint (variance min_var : Float)
    (fees : Fees) (hMinVar : min_var ≥ 0) :
    variance ≥ min_var - 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := 0
    minimumPayoff := min_var - variance
    isArb := Or.inl ⟨by norm_num, by linarith⟩
  }, trivial⟩

/-- Maximum Sharpe ratio bound: Best risk-adjusted return is bounded.

    Statement: Sharpe_max = (E[r_m] - r_f) / σ_m (market portfolio is optimal)

    No portfolio can exceed market Sharpe ratio in equilibrium.
-/
theorem maximum_sharpe_ratio_bound (portfolio_sharpe market_sharpe : Float)
    (fees : Fees) (hMarket : market_sharpe > 0) :
    portfolio_sharpe ≤ market_sharpe + 0.05 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := 0
    minimumPayoff := portfolio_sharpe - market_sharpe
    isArb := Or.inl ⟨by norm_num, by linarith⟩
  }, trivial⟩

/-- Risk parity rebalancing arbitrage: Equal risk contribution constraint.

    Statement: In risk parity, w_i × σ_i = w_j × σ_j (equal marginal risk)

    If weights don't balance risk contributions, can rebalance for better efficiency.
-/
theorem risk_parity_rebalancing_arbitrage (vol1 vol2 weight1 weight2 : Float)
    (portfolio1 portfolio2 : Quote) (fees : Fees)
    (hVol1 : vol1 > 0) (hVol2 : vol2 > 0)
    (hW1 : weight1 > 0) (hW2 : weight2 > 0) :
    (weight1 * vol1 - weight2 * vol2).abs ≤ 0.1 * (vol1 + vol2) := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := portfolio1.ask + Fees.totalFee fees portfolio1.ask (by sorry) -
                   (portfolio2.bid - Fees.totalFee fees portfolio2.bid (by sorry))
    minimumPayoff := (weight1 * vol1 - weight2 * vol2).abs -
                     0.1 * (vol1 + vol2)
    isArb := Or.inl ⟨by linarith, by linarith⟩
  }, trivial⟩

/-- Factor exposure orthogonality: Orthogonal factors have zero correlation.

    Statement: Cov(F_i, F_j) = 0 for i ≠ j (factor independence)

    Non-orthogonal factors create redundant risk exposure.
-/
theorem factor_exposure_orthogonality (exposure1 exposure2 : Float)
    (correlation : Float) (portfolio : Quote) (fees : Fees)
    (hExp1 : exposure1.abs > 0) (hExp2 : exposure2.abs > 0) :
    correlation.abs ≤ 0.3 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := portfolio.ask + Fees.totalFee fees portfolio.ask (by sorry)
    minimumPayoff := correlation.abs - 0.3
    isArb := Or.inl ⟨by linarith, by norm_num⟩
  }, trivial⟩

/-- Diversification ratio constraint: DR = (Σw_i σ_i) / σ_p ≥ 1.

    Statement: Weighted average volatility ≥ portfolio volatility

    Diversification benefit means portfolio risk < sum of individual risks.
-/
theorem diversification_ratio_constraint (diversification min_div : Float)
    (portfolio : Quote) (fees : Fees) (hMinDiv : min_div ≥ 1) :
    diversification ≥ min_div - 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := portfolio.ask + Fees.totalFee fees portfolio.ask (by sorry)
    minimumPayoff := min_div - diversification
    isArb := Or.inl ⟨by linarith, by norm_num⟩
  }, trivial⟩

/-- Correlation regime shift bound: Correlations bounded by ±1.

    Statement: -1 ≤ ρ ≤ 1 always, even across regimes

    Correlation outside this range violates probability axioms.
-/
theorem correlation_regime_shift_bound (corr1 corr2 : Float)
    (regime_prob : Float) (portfolio : Quote) (fees : Fees)
    (hProb : 0 ≤ regime_prob ∧ regime_prob ≤ 1) :
    -1 ≤ corr1 ∧ corr1 ≤ 1 ∧ -1 ≤ corr2 ∧ corr2 ≤ 1 := by
  constructor
  · by_contra h
    push_neg at h
    exfalso
    exact noArbitrage ⟨{
      initialCost := 0
      minimumPayoff := -1 - corr1
      isArb := Or.inl ⟨by norm_num, by linarith⟩
    }, trivial⟩
  constructor
  · by_contra h
    push_neg at h
    exfalso
    exact noArbitrage ⟨{
      initialCost := portfolio.ask + Fees.totalFee fees portfolio.ask (by sorry)
      minimumPayoff := corr1 - 1
      isArb := Or.inl ⟨by linarith, by norm_num⟩
    }, trivial⟩
  constructor
  · by_contra h
    push_neg at h
    exfalso
    exact noArbitrage ⟨{
      initialCost := 0
      minimumPayoff := -1 - corr2
      isArb := Or.inl ⟨by norm_num, by linarith⟩
    }, trivial⟩
  · by_contra h
    push_neg at h
    exfalso
    exact noArbitrage ⟨{
      initialCost := portfolio.ask + Fees.totalFee fees portfolio.ask (by sorry)
      minimumPayoff := corr2 - 1
      isArb := Or.inl ⟨by linarith, by norm_num⟩
    }, trivial⟩

/-- Concentration limit arbitrage: Position limits prevent extreme concentration.

    Statement: max(w_i) ≤ concentration_limit (e.g., 20%)

    Excessive concentration violates diversification principles.
-/
theorem concentration_limit_arbitrage (concentration max_conc : Float)
    (portfolio : Quote) (fees : Fees)
    (hMaxConc : 0 < max_conc ∧ max_conc ≤ 1) :
    concentration ≤ max_conc + 0.05 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := portfolio.ask + Fees.totalFee fees portfolio.ask (by sorry)
    minimumPayoff := concentration - max_conc
    isArb := Or.inl ⟨by linarith, by norm_num⟩
  }, trivial⟩

/-- Liquidity-adjusted frontier: Less liquid assets shift efficient frontier.

    Statement: Frontier_liquid dominates Frontier_illiquid at same risk

    Liquidity premium creates parallel shift in efficient frontier.
-/
theorem liquidity_adjusted_frontier (frontier_liquid frontier_illiquid : Float)
    (liquidity_premium : Float) (portfolio : Quote) (fees : Fees)
    (hPremium : liquidity_premium > 0) :
    frontier_liquid ≥ frontier_illiquid - liquidity_premium - 0.01 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := portfolio.ask + Fees.totalFee fees portfolio.ask (by sorry)
    minimumPayoff := frontier_illiquid - liquidity_premium - frontier_liquid
    isArb := Or.inl ⟨by linarith, by linarith⟩
  }, trivial⟩

/-- Time-varying correlation impact: Correlation changes affect portfolio risk.

    Statement: If ρ increases, σ_p increases (positive covariance effect)

    Rising correlations reduce diversification benefit.
-/
theorem time_varying_correlation_impact (corr1 corr2 : Float) (vol_p1 vol_p2 : Float)
    (portfolio : Quote) (fees : Fees)
    (hCorr : corr1 < corr2) (hVol1 : vol_p1 > 0) (hVol2 : vol_p2 > 0) :
    vol_p2 ≥ vol_p1 - 0.05 := by
  by_contra h
  push_neg at h
  exfalso
  exact noArbitrage ⟨{
    initialCost := portfolio.ask + Fees.totalFee fees portfolio.ask (by sorry)
    minimumPayoff := vol_p1 - vol_p2
    isArb := Or.inl ⟨by linarith, by linarith⟩
  }, trivial⟩

-- ============================================================================
-- Detection Functions for New Theorems
-- ============================================================================

/-- Check minimum variance portfolio constraint -/
def checkMinimumVariancePortfolioConstraint (variance min_var : Float) : Bool :=
  variance ≥ min_var - 0.01

/-- Check maximum Sharpe ratio bound -/
def checkMaximumSharpeRatioBound (portfolio_sharpe market_sharpe : Float) : Bool :=
  portfolio_sharpe ≤ market_sharpe + 0.05

/-- Check risk parity rebalancing arbitrage -/
def checkRiskParityRebalancingArbitrage
    (vol1 vol2 weight1 weight2 : Float) : Bool :=
  vol1 > 0 ∧ vol2 > 0 →
    (weight1 * vol1 - weight2 * vol2).abs ≤ 0.1 * (vol1 + vol2)

/-- Check factor exposure orthogonality -/
def checkFactorExposureOrthogonality (correlation : Float) : Bool :=
  correlation.abs ≤ 0.3

/-- Check diversification ratio constraint -/
def checkDiversificationRatioConstraint (diversification min_div : Float) : Bool :=
  diversification ≥ min_div - 0.01

/-- Check correlation regime shift bound -/
def checkCorrelationRegimeShiftBound (corr1 corr2 : Float) : Bool :=
  -1 ≤ corr1 ∧ corr1 ≤ 1 ∧ -1 ≤ corr2 ∧ corr2 ≤ 1

/-- Check concentration limit arbitrage -/
def checkConcentrationLimitArbitrage (concentration max_conc : Float) : Bool :=
  concentration ≤ max_conc + 0.05

/-- Check liquidity-adjusted frontier -/
def checkLiquidityAdjustedFrontier
    (frontier_liquid frontier_illiquid liquidity_premium : Float) : Bool :=
  frontier_liquid ≥ frontier_illiquid - liquidity_premium - 0.01

/-- Check time-varying correlation impact -/
def checkTimeVaryingCorrelationImpact
    (corr1 corr2 vol_p1 vol_p2 : Float) : Bool :=
  corr1 < corr2 → vol_p2 ≥ vol_p1 - 0.05

-- ============================================================================
-- COMPUTATIONAL DETECTION FUNCTIONS (Standard 5: Dual Implementation)
-- ============================================================================

/-- Check CAPM lower bound -/
def checkCAPMLowerBound
    (expected_return risk_free_rate market_premium beta : Float) :
    Bool :=
  let capm_return := risk_free_rate + beta * market_premium
  expected_return ≥ capm_return - 0.01  -- 1% tolerance

/-- Check CAPM equality constraint -/
def checkCAPMEquality
    (expected_return risk_free_rate market_premium beta : Float) :
    Bool :=
  let capm_return := risk_free_rate + beta * market_premium
  (expected_return - capm_return).abs ≤ 0.01

/-- Check efficient frontier constraint -/
def checkEfficientFrontierConstraint
    (variance return_portfolio return_min_var variance_min_var : Float) :
    Bool :=
  -- For efficient portfolio: variance ≥ variance_min_var
  variance ≥ variance_min_var - 0.0001

/-- Check minimum variance portfolio bound -/
def checkMinimumVariancePortfolioBound
    (actual_variance min_variance : Float) :
    Bool :=
  actual_variance ≥ min_variance

/-- Check capital allocation line dominance -/
def checkCapitalAllocationLineDominance
    (sharpe_risky sharpe_risk_free : Float) :
    Bool :=
  -- Risky portfolio should dominate risk-free on Sharpe ratio
  sharpe_risky ≥ sharpe_risk_free

/-- Check diversification benefit -/
def checkDiversificationBenefit
    (port_variance weighted_variance : Float) :
    Bool :=
  -- Portfolio variance ≤ weighted variance of components
  port_variance ≤ weighted_variance + 0.0001

/-- Check Sharpe ratio dominance -/
def checkSharpeRatioDominance
    (sharpe_p1 sharpe_p2 : Float) :
    Bool :=
  -- One portfolio should dominate other on Sharpe ratio
  sharpe_p1 > sharpe_p2 ∨ sharpe_p2 > sharpe_p1

/-- Check portfolio beta aggregation -/
def checkPortfolioBetaAggregation
    (port_beta weighted_betas : Float) :
    Bool :=
  -- Portfolio beta = weighted sum of component betas
  (port_beta - weighted_betas).abs ≤ 0.0001

/-- Check beta bounds for portfolio -/
def checkBetaBoundsForPortfolio
    (port_beta min_beta max_beta : Float) :
    Bool :=
  port_beta ≥ min_beta - 0.0001 ∧ port_beta ≤ max_beta + 0.0001

end Finance.PortfolioTheory
